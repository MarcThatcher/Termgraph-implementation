module Trans where

import Data.Char (ord, chr, isAlpha)
import Data.List (nub, group, sort,isPrefixOf, partition, stripPrefix, intercalate, isSuffixOf)
import Parser
import Text.Parsec (ParseError)
import Debug.Trace
import qualified Data.Map.Strict as Map

-- ------------------------
-- Data structures for fully explicit INPLA nets
-- ------------------------
type Port   = String
type Symbol = String
type Agent  = (Symbol, Port, [Port]) -- (agent label, principal port, aux ports)
type Wire   = (Port,Port)
type Net    = ([Agent],[Wire])
type LUT    = [(String,Int)]         -- (func label, number outputs)

main :: [String] -> IO ()
--takes a list of inputs: flags plus file name (order doesn't matter); to change to being unix-style for final version
-- -imm = implicit memory management (adds erase & duplication on RHS of rules)
-- -npm = nested pattern matching (implements Interaction Nets with NPM by Hassan & Sato)
main args = do
    let imm      = "-imm" `elem` args
        npm      = "-npm" `elem` args
        mpp      = "-mpp" `elem` args
        hof      = "-hof" `elem` args
        filename = head (filter (`notElem` ["-imm", "-npm", "-mpp", "-hof"]) args)
    inputFile  <- readFile filename
    let inputLines  = lines inputFile
        ruleLines   = filter (not . ("--" `isPrefixOf`)) inputLines
        parsedRules = map parseRule ruleLines
        rules = (if imm then addAllErasers . addAllDuplicators else id)
                $ (if hof then expandFuncRefs else id)
                $ expandAllGenConstrs [r | Right r <- parsedRules]
        errors      = [e | Left e <- parsedRules]
    if not (null errors)
       then error ("Parse errors: " ++ show errors)
       else do
           let builtinLUT = [("succ", 1), ("pred", 1), ("!eraser", 0), ("!duplicator", 0), ("i_lam", 1), ("i_app", 1)]  -- needs to have special rules in transRuleList or elsewhere for each
               lut        = makeLUT rules builtinLUT
               transRules = dupToDup (transRuleList rules lut npm)
           putStrLn $ "LUT: " ++ show lut
           -- print FLIN rules
           putStrLn "FLIN rules:"
           putStrLn inputFile
           putStrLn "\nINPLA rules:"
           putStrLn transRules
           putStrLn ""
           putStr "Enter a FLIN term to translate, or :Q to quit"
           putStrLn ""
           -- start interactive loop to translate terms
           replLoop lut

replLoop :: LUT -> IO ()
replLoop lut = do
    putStr "> "
    line <- getLine
    if line == ":Q"
       then return ()
       else do
           let result = inpla lut line
           case result of
               Left err  -> putStrLn ("Parse error: " ++ show err)
               Right str -> putStrLn str
           replLoop lut

-- for when doing implicit memory management, replace internally generated !duplicator agents with INPLA's Dup 
dupToDup :: String -> String
dupToDup [] = []
dupToDup str = case stripPrefix "!duplicator" str of
    Just rest -> "Dup" ++ dupToDup rest
    Nothing   -> head str : dupToDup (tail str)


-- trans
trans :: Term -> VarName -> Net -> LUT -> Net
-- Variables
trans (Var v) root (agents, wires) _ =
    (agents, wires ++ [(v, root)])

-- Empty net vanishes
trans Empty _ (agents, wires) _ =
    (agents, wires)

-- Constructors
trans (Constr constr args) root (agents, wires) lut =
  let numIns = length args

      -- generate auxiliary ports from the root
      auxPorts = take numIns $ tail $ iterate fresh root

      -- argument roots: each aux port concatenated with its fresh increment
      argRoots = map (\x -> x ++ fresh x) auxPorts

      -- create the constructor agent
      newAgent = (constr, root, auxPorts)

      -- recursively translate each argument and connect its principal port
      (agents', wires') =
        foldl
          (\(as, ws) (arg, aroot, auxPort) ->
             let (as', ws') = trans arg aroot (as, ws) lut
                 newWire    = (aroot, auxPort)  -- principal first
             in (as', ws' ++ [newWire])
          )
          (agents ++ [newAgent], wires)
          (zip3 args argRoots auxPorts)
  in (agents', wires')

-- functions
-- special case !eraser is translated directly to INPLA's built-in Eraser agent
trans (Func "!eraser" [Var v]) root (agents, wires) _ =
    (agents ++ [("Eraser", v, [])], wires)
-- comment that need to always have () after function when 0-arity else INPLA cannot distinguish e()~1 (erase func) from e~1 (port e)
trans (Func fName args) root net lut =
  let numOuts = funcNumOuts fName lut
      pp       = fresh root

      -- output ports: first is root, rest are root ++ fresh iterated
      outPorts = 
        if numOuts == 0 then []
        else root : map (root ++) (take (numOuts - 1) $ tail $ iterate fresh root)

      -- input ports (excluding pp itself)
      numInPortsExPP = length args - 1
      inPortsExPP    = map (pp ++) (take numInPortsExPP $ tail $ iterate fresh pp)

      -- the function agent itself
      newAgent       = (fName, pp, outPorts ++ inPortsExPP)

      -- now handle arguments
      (allAgents, allWires) =
        foldr
          (\(arg, port) (as, ws) ->
             let freshP       = fresh port
                 (as', ws')  = trans arg freshP net lut
                 newWire      = (freshP, port)  -- connect arg result to function input
             in  (as' ++ as, newWire : (ws' ++ ws)))
          ([], [])
          (zip args (pp : inPortsExPP))
  in
      (newAgent : allAgents, allWires)

-- natural number variables
trans (NatVar v) root (agents, wires) _ =
    (agents ++ [("(int " ++ v ++ ")", root, [])], wires)

-- natural number literals: on LHS become (int n) agent for pattern matching
trans (Nat n) root (agents, wires) _ =
    (agents ++ [("(int " ++ show n ++ ")", root, [])], wires)

-- let
trans (Let t1 vars t2) root net lut =
  let
      -- 1. Translate t1
      (agents1, wires1) = trans t1 root net lut

      -- 2. Rename outputs of t1 to match 'vars'
      -- *** need to change this do deal with Par: need to do a case on shape of t1 e.g. x,y~A|B in x|y***
      (agents1',wires1') = 
        if null agents1 then (agents1, renameWire t1 (head wires1) (head vars)) -- only handles 1 wire
        else ((renameOutputs t1 (head agents1) vars lut) : tail agents1, wires1)  -- only handles 1 agent

      -- 3. Translate t2 with updated net
      -- (agents2,wires2) = 
      --   if null agents1' then (agents1',wires1')
      --   else trans t2 (root++"L"++(fresh root)) (agents1',wires1') lut
      (agents2,wires2) = 
        if null agents1' then (agents1',wires1')
        else 
          let (agents3,wires3) = trans t2 (root++"L"++(fresh root)) ([],[]) lut
          in (agents1'++agents3,wires1'++wires3)
  in
      -- Output ex duplications created
      (nub agents2, nub wires2)

-- ||
trans (Par t1 t2) root (agents,wires) lut =
  let (agents1, wires1) = trans t1 root (agents,wires) lut
      usedPorts = map (\(_,pp,aux) -> pp:aux) agents1 ++ [[a,b] | (a,b) <- wires1]
      usedSet   = concat usedPorts
      newRoot   = head (dropWhile (`elem` usedSet) (iterate fresh root))
      (agents2, wires2) = trans t2 newRoot (agents1,wires1) lut
  in (agents2, wires2)

-- [...] : handle list syntactic sugar
trans (ListTerm terms) root (agents, wires) _ =
    let listStr = "[" ++ intercalate "," (map termToINPLA terms) ++ "]"
    in (agents ++ [(listStr, root, [])], wires)

-- function reference: wire using f_hat port name
trans (FuncRef f) root (agents, wires) _ =
    (agents, wires ++ [(f, root)])

-- function application: becomes i_app agent
trans (FuncApp f x) root (agents, wires) lut =
    let freshP = fresh root
        (agents', wires') = trans x freshP (agents, wires) lut
    in (agents' ++ [("i_app", f, [root, freshP])], wires')



-- Convert a term to its INPLA string representation for use in list literals
termToINPLA :: Term -> String
termToINPLA (Var v)          = v
termToINPLA (Nat n)          = show n
termToINPLA (NatVar v)       = v
termToINPLA (Constr c [])    = c
termToINPLA (Constr c args)  = c ++ "(" ++ intercalate "," (map termToINPLA args) ++ ")"
termToINPLA _                = error "termToINPLA: unsupported term in list literal"

renameOutputs :: Term -> Agent -> [VarName] -> LUT -> Agent
-- need the Term to know whether is Constr or Func
renameOutputs (Var v) agent vars lut = 
  undefined
renameOutputs Empty agent vars lut = 
  undefined
renameOutputs (Constr _ _) (name,out,ins) vars lut = 
  let [newOut] = vars   -- should only be 1
  in (name,newOut,ins)
renameOutputs (Func fName inputs) (name,pp,auxs) vars lut = 
  let numOuts = funcNumOuts name lut
  in (name,pp,vars++(drop numOuts auxs))

renameWire :: Term -> Wire -> VarName -> [Wire]
renameWire (Var v) wire var = 
  let (p1,p2) = wire
  in
    if p1==v then [(p1,var)] else [(var,p2)]

netToINPLA :: Net -> String
netToINPLA (agents, wires)
  | null inplaAgents = inplaWires ++ ";"
  | null inplaWires  = inplaAgents ++ ";"
  | otherwise        = inplaAgents ++ "," ++ inplaWires ++ ";"
  where
    inplaAgents = agentsToINPLA agents
    inplaWires  = wiresToINPLA wires

agentsToINPLA :: [Agent] -> String
agentsToINPLA []     = ""
agentsToINPLA [(symbol, pp, auxPorts)]    = agentStr symbol auxPorts ++ "~" ++ pp
agentsToINPLA ((symbol, pp, auxPorts):as) = agentStr symbol auxPorts ++ "~" ++ pp ++ "," ++ agentsToINPLA as

agentStr symbol auxPorts
    | symbol == "!eraser"         = "Eraser"
    | symbol == "!Cons"           = "(" ++ head auxPorts ++ ":" ++ last auxPorts ++ ")"
    | "(int " `isPrefixOf` symbol = init (drop 5 symbol)
    | otherwise                   = symbol ++ "(" ++ listPorts auxPorts ++ ")"

listPorts :: [Port] -> String
listPorts []  = ""
listPorts [p] = p
listPorts (p:ps) = p++","++ listPorts ps

wiresToINPLA :: [Wire] -> String
wiresToINPLA []              = ""
wiresToINPLA [(p1,p2)]       = p1++"~"++p2
wiresToINPLA ((p1,p2):wires) = p1++"~"++p2++","++ wiresToINPLA wires

funcNumOuts :: String -> LUT -> Int
funcNumOuts symbol [] = error ("funcNumOuts reaches end of LUT for " ++ symbol)
funcNumOuts symbol ((name, num):rest) = 
    if symbol == name then num else funcNumOuts symbol rest

-- build the LUT
makeLUT :: [Rule] -> LUT -> LUT
makeLUT [] lut = lut
makeLUT (Rule t1 t2 : rs) lut =
    case t1 of
        Func fName _ ->
            if any (\(name, _) -> name == fName) lut
               then makeLUT rs lut  -- already in LUT, skip
               else
                   let numOuts = countOuts t2 lut
                       lut'    = lut ++ [(fName, numOuts)]
                   in makeLUT rs lut'
        _ -> error "First term of Rule must be Func"


countOuts :: Term -> LUT -> Int
-- count number non-empty terms
countOuts Empty _           = 0
countOuts (Var _) _         = 1
countOuts (Constr _ _) _    = 1
countOuts (Nat _) _         = 1
countOuts (NatVar _) _      = 1
countOuts (Func f _) lut    = funcNumOuts f lut
countOuts (Let t1 _ t2) lut = countOuts t2 lut
countOuts (Par t1 t2) lut   = (countOuts t1 lut) + (countOuts t2 lut)
countOuts (ListTerm _) _    = 1
countOuts (FuncRef _) _     = 1
countOuts (FuncApp _ _) _   = 1

-- fresh port names - appends _0 after alpha, increments digit after _, 9 -> _a
fresh :: String -> String
fresh s
  | isAlpha (last s) = s ++ "_0"
  | last s == '9'    = init s ++ "_a"
  | otherwise        = init s ++ [chr (ord (last s) + 1)]

-- clean up intermediate links e.g. a~b,b~c
cleanNet :: Net -> Net
cleanNet (agents, wires) = --(agents, wires)
    let intermediates     = nub $ intermediatePorts wires
        collapsedWires    = nub $ collapseChains wires intermediates
    in collapseWiresToPorts (updateAgentsWithWires agents collapsedWires)

intermediatePorts :: [Wire] -> [Port]
intermediatePorts ws =
    let ports = concatMap (\(a,b) -> [a,b]) ws
        counts = map (\g -> (head g, length g)) . group . sort $ ports
    in [p | (p,n) <- counts, n > 1, not ("_hat" `isSuffixOf` p)]

-- Collapse a single intermediate port
collapseIntermediate :: [Wire] -> Port -> [Wire]
collapseIntermediate wires ip =
    let -- select wires that contain the intermediate port
        relevant = filter (\(a,b) -> a == ip || b == ip) wires
        -- get the ports on the other side of ip
        endpoints = map (\(a,b) -> if a == ip then b else a) relevant
    in case endpoints of
         [p1,p2] -> [(p1,p2)]  -- connect them directly
         _        -> []         -- ignore other cases for now
         
-- Collapse all intermediate ports
collapseChains wires intermediates =
    let isIntermediate p = p `elem` intermediates

        -- map each port to its directly connected port(s)
        adj = Map.fromListWith (++) [(a,[b]) | (a,b) <- wires] `Map.union`
              Map.fromListWith (++) [(b,[a]) | (a,b) <- wires]

        -- find canonical port for a given port, skipping intermediates
        canonical p visited
          | isIntermediate p =
              case filter (`notElem` visited) (Map.findWithDefault [] p adj) of
                []    -> p
                (q:_) -> canonical q (p:visited)
          | otherwise = p

        ports = nub $ concatMap (\(a,b) -> [a,b]) wires

        -- build new wires for non-intermediate ports only
        newWires = nub [ (canonical a [], canonical b []) 
                       | (a,b) <- wires
                       , not (isIntermediate a && isIntermediate b)]
    in nub [(x,y) | (x,y) <- newWires, x /= y]

-- if a~b and a appears in port, replace a with b
collapseWiresToPorts :: Net -> Net
collapseWiresToPorts (agents, wires) = 
  let -- don't collapse wires involving _hat ports
      safeWires  = filter (\(a,b) -> not ("_hat" `isSuffixOf` a) && not ("_hat" `isSuffixOf` b)) wires
      (from,to)  = unzip safeWires
      newAgents  = map (updateAgent from to) agents
      freeWires  = makeFreeWires from to newAgents
  in (newAgents, freeWires)

makeFreeWires :: [Port] -> [Port] -> [Agent] -> [Wire]
makeFreeWires from to agents =
    [(f, t) | (f, t) <- zip from to, not (portInAgents t agents)]
  where
    portInAgents p ags = any (portInAgent p) ags

-- Check if a port occurs in an agent (principal or auxiliary)
portInAgent :: Port -> Agent -> Bool
portInAgent p (_, principal, auxPorts) =
    p == principal || p `elem` auxPorts

-- Check if either port from wire occurs in at least one agent
portOccurs :: Wire -> [Agent] -> Bool
portOccurs (p1, p2) agents =
    any (\agent -> portInAgent p1 agent || portInAgent p2 agent) agents

-- Get all ports that appear in the agents
agentPorts :: [Agent] -> [Port]
agentPorts agents = nub $ concatMap (\(_,pp,aux) -> pp:aux) agents

-- Update agents and wires based on collapsed wires
updateAgentsWithWires :: [Agent] -> [Wire] -> Net
updateAgentsWithWires agents wires =
    let aPorts = agentPorts agents
        processWire (as, ws) (a,b)
          | a `elem` aPorts && b `notElem` aPorts =
                let as' = map (replacePort a b) as
                in (as', ws)  -- drop wire
          | b `elem` aPorts && a `notElem` aPorts =
                let as' = map (replacePort b a) as
                in (as', ws)  -- drop wire
          | otherwise = (as, (a,b):ws)  -- keep wire
        (agents', wires') = foldl processWire (agents, []) wires
    in (nub agents', nub wires')

-- Replace port pOld with pNew in a single agent
replacePort :: Port -> Port -> Agent -> Agent
replacePort pOld pNew (label, pp, aux) =
    let pp' = if pp == pOld then pNew else pp
        aux' = map (\x -> if x == pOld then pNew else x) aux
    in (label, pp', aux')


-- Rules; needs LUT & npm flag allows for nesting
transRule :: Rule -> LUT -> Bool -> String
transRule rule lut npm =
    let 
        Rule t1 t2 = rule
        root       = "r"
        lhs        = cleanNet $ trans t1 root ([], []) lut
        numAgents  = length (fst lhs)
        rhs = case t2 of
                Par t1' t2' -> 
                    let flatRHS = flatPar (Par t1' t2')
                        numOuts  = length flatRHS
                        outsList = take numOuts $
                                   case lhs of
                                     (agents, _) -> concatMap (\(_,_,aux) -> aux) agents
                        -- translate each element of flatRHS with the corresponding port
                        combineNet (agentsAcc, wiresAcc) (term, port) =
                            let (a', w') = trans term port ([], []) lut
                            in (agentsAcc ++ a', wiresAcc ++ w')
                        rhsNet = foldl combineNet ([], []) (zip flatRHS outsList)
                    in rhsNet
                Let _ _ _ -> cleanUpLetOutputs lhs (cleanNet $ trans t2 "r" ([], []) lut) lut
                _         -> cleanNet $ trans t2 "r" ([], []) lut
    in if npm && numAgents > 2
       then applyT lhs t2 root lut npm
       else (transActivePair lhs) ++ (netToINPLA rhs)

applyT :: Net -> Term -> Port -> LUT -> Bool -> String
applyT lhs t2 root lut npm =
    case findNestedAgent lhs of
        Nothing ->
            -- no more nesting; translate RHS normally
            let rhs = cleanNet $ trans t2 root ([], []) lut
            in transActivePair lhs ++ netToINPLA rhs
        Just (alpha, beta, gamma, nestedPort, a) ->
            let (aName, aPP, aAux)  = alpha
                (bName, bPP, bAux)  = beta
                (gName, gPP, gAux)  = gamma
                -- new auxiliary agent name from concatenation of alpha and beta names (per paper but add "npm" to stop clashes in case alphabeta already used)
                abName  = "npm" ++ aName ++ bName
                -- aux ports of alphaB: beta's aux ports minus nestedPort, plus alpha's aux ports
                abAux   = filter (/= nestedPort) bAux ++ aAux
                -- Rule i) LHS: just alpha and beta
                lhsI    = ([alpha, beta], [])
                -- Rule i) RHS: new alphaB agent wired to nestedPort
                ruleI   = transActivePair lhsI ++
                          agentsToINPLA [(abName, nestedPort, abAux)] ++ ";"
                -- Rule ii) LHS: alphaB interacting with gamma, plus any further nested agents a
                abAgent    = (abName, gPP, abAux)
                gammaAgent = (gName, gPP, gAux)
                lhs2       = (abAgent : gammaAgent : a, [])
                -- Rule ii) is recursively translated in case of further nesting
                ruleII     = applyT lhs2 t2 root lut npm
            in ruleI ++ "\n" ++ ruleII

cleanUpLetOutputs :: Net -> Net -> LUT -> Net
-- take lhs and rhs of rule and ensure outputs are consistent
cleanUpLetOutputs lhs rhs lut = -- rhs
  let outputs     = uniqueOnly $ inLHSonly lhs rhs  -- outputs from LHS
      danglingRHS = unconnectedPorts rhs            -- anything not connected on RHS
      outputsRHS  = notInLHS lhs danglingRHS
  in updateOutputs rhs outputsRHS outputs 

updatePortName :: [Port] -> [Port] -> Port -> Port
updatePortName from to port =
    case lookup port (zip from to) of
        Just newPort -> newPort
        Nothing      -> port

-- Update ports in an agent
updateAgent :: [Port] -> [Port] -> Agent -> Agent
updateAgent from to (symbol, principal, auxPorts) =
    (symbol, updatePortName from to principal, map (updatePortName from to) auxPorts)

-- Update ports in a wire
updateWire :: [Port] -> [Port] -> Wire -> Wire
updateWire from to (p1, p2) =
    (updatePortName from to p1, updatePortName from to p2)

-- Main function: update all ports in a Net
updateOutputs :: Net -> [Port] -> [Port] -> Net
updateOutputs (agents, wires) from to =
    (map (updateAgent from to) agents, map (updateWire from to) wires)

transRuleList :: [Rule] -> LUT -> Bool -> String
transRuleList rules lut npm =
    builtins ++ guardedRules ++ dupToDup normalRules
    where
        -- built in INPLA rules : succ&pred to work with natural number consturctors and i_app and i_lam for lambda calculus for HOFs
        builtins = "succ(r) >< (int x) => r~(x+1);\npred(r)><(int x) => r~(x-1);\ni_lam(x1,x2) >< i_app(y1,y2) => y1~x2,y2~x1;\n---\n"
        -- find functions with nat literal rules
        natFuncs     = natLitFuncNames rules
        -- generate guarded rules for those functions
        guardedRules = concatMap (\f ->
            let (litRules, mVarRule) = groupNatRulesFor f rules
            in makeGuardedNatRule litRules mVarRule lut ++ "\n") natFuncs
        -- skip nat literal and nat var rules that have been handled above
        skipRules    = [r | f <- natFuncs, r <- fst (groupNatRulesFor f rules)]
                    ++ [r | f <- natFuncs, Just r <- [snd (groupNatRulesFor f rules)]]
        normalRules  = concatMap (\r -> transRule r lut npm ++ "\n")
                       (filter (`notElem` skipRules) rules)

transActivePair :: Net -> String
transActivePair (agents, wire) = 
  let [(a1name, a1pp, a1auxs) ,(a2name, a2pp, a2auxs)] = agents
      a1auxsList       = listPorts a1auxs
      a2auxsList       = listPorts a2auxs
      a1auxsListString = "(" ++ a1auxsList ++ ")"
      a2nameStr        = if a2name == "!Cons" then "" else a2name
      a2auxsListString = if null a2auxsList then ""
                            else if a2name == "!Cons" then "(" ++ head a2auxs ++ ":" ++ last a2auxs ++ ")"
                                 else "(" ++ a2auxsList ++ ")"
  in
    a1name ++ a1auxsListString ++ " >< " ++ a2nameStr ++ a2auxsListString ++ " => "

flatPar :: Term -> [Term]
flatPar (Par t1 t2) = flatPar t1 ++ flatPar t2
flatPar t           = [t]

--- **** 
tr :: LUT -> String -> Either ParseError Net
tr lut term =
  case parseTerm term of
    Left err -> Left err
    Right t  -> Right (cleanNet $ trans t "r" ([], []) lut) 

inpla :: LUT -> String -> Either ParseError String
inpla lut term =
  case tr lut term of
    Left err  -> Left err
    Right net -> Right (netToINPLA net)

inLHSonly :: Net -> Net -> [String]
inLHSonly (lhsAgents, lhsWires) (rhsAgents, rhsWires) =
  let lhsPorts = map (\(_,pp,aux) -> pp:aux) lhsAgents ++ [[a,b] | (a,b) <- lhsWires]
      rhsPorts = map (\(_,pp,aux) -> pp:aux) rhsAgents ++ [[a,b] | (a,b) <- rhsWires]
  in filter (`notElem` concat rhsPorts) (concat lhsPorts)

uniqueOnly :: Eq a => [a] -> [a]
-- if an element occurs more than once, remove it. So only unique elements remain.
uniqueOnly xs = [x | x <- nub xs, count x xs == 1]
  where
    count y = length . filter (== y)

unconnectedPorts :: Net -> [Port]
unconnectedPorts (agents, wires) =
  let agentPorts = concatMap (\(_,pp,aux) -> pp:aux) agents
      wirePorts  = concatMap (\(a,b) -> [a,b]) wires
      attempt1 =  filter (`notElem` wirePorts) agentPorts
      -- attempt2 = unconnectedPortsAgents (agents,wires)
  in uniqueOnly attempt1

unconnectedPortsAgents :: Net -> [Port]
unconnectedPortsAgents (agents, wires) = uniqueOnly $ concatMap portList agents

portList :: Agent -> [Port]
portList (symbol,pp,auxList) = pp:auxList

notInLHS :: Net -> [String] -> [String]
notInLHS (lhsAgents, lhsWires) ports =
  let lhsPorts = concatMap (\(_,pp,aux) -> pp:aux) lhsAgents ++ concatMap (\(a,b) -> [a,b]) lhsWires
  in filter (`notElem` lhsPorts) ports

-- replacePortAgent :: Agent -> Port -> Port -> [Agent]
-- replacePortAgent (symbol, pp, aux) new old =
--   let pp'  = if pp == old then new else pp
--       aux' = map (\p -> if p == old then new else p) aux
--   in (symbol, pp', aux')

replacePortAgents :: [Agent] -> [(Port,Port)] -> [Agent]
replacePortAgents []          _        = []
replacePortAgents (ag:agents) portList =
  (replacePortAgents1 ag portList) : (replacePortAgents agents portList) 

replacePortAgents1 :: Agent -> [(Port,Port)] -> Agent
replacePortAgents1 agent []       = agent
replacePortAgents1 agent portList =
  let ((new,old):rest) = portList 
  in replacePortAgents1 (replacePortAgent agent (new,old)) rest

replacePortAgent :: Agent -> (Port,Port) -> Agent
replacePortAgent (symbol, pp, aux) (new,old) =
  let pp'  = if pp == old then new else pp
      aux' = map (\p -> if p == old then new else p) aux
  in (symbol, pp', aux')




-- replacePortAgents :: [Agent] -> [Port] -> [Port] -> [Agent]
-- replacePortAgents []          _    _    = []
-- replacePortAgents (ag:agents) news olds = 
--   map (replacePortAgent 
  -- zip news olds
   


  -- | length olds /= length news = error "replacePortAgents: lists must have equal length"
  -- | otherwise = foldl (\ags o n -> map (\a -> replacePortAgent a n o) ags) agents olds news

replacePortsWires :: [Wire] -> [Port] -> [Port] -> [Wire]
replacePortsWires wires olds news
  | length olds /= length news = error "replacePortsWires: lists must have equal length"
  | otherwise = foldl (\ws (o,n) -> map (\(a,b) -> (if a==o then n else a, if b==o then n else b)) ws) wires (zip olds news)


-- generics
--1. collect constructors from list of rules & build list of pairs (constructor,arity)
collectConstrs :: [Rule] -> [(ConstrName, Int)]
collectConstrs rules = nub $ concatMap constrFromRule rules

constrFromRule :: Rule -> [(ConstrName, Int)]
constrFromRule (Rule t1 t2) = constrFromTerm t1 ++ constrFromTerm t2

constrFromTerm :: Term -> [(ConstrName, Int)]
constrFromTerm (Constr name args) = (name, length args) : concatMap constrFromTerm args
constrFromTerm (Func _ args)      = concatMap constrFromTerm args
constrFromTerm (Par t1 t2)        = constrFromTerm t1 ++ constrFromTerm t2
constrFromTerm (Let t1 _ t2)      = constrFromTerm t1 ++ constrFromTerm t2
constrFromTerm _                  = []

--2. check for functions with explicit constructors so do not overwrite these with generic version
specificConstrs :: FuncName -> [Rule] -> [ConstrName]
specificConstrs fName rules = concatMap (constrNamesFor fName) rules

-- Extract constructor names used as direct arguments to fName in a rule LHS
-- (only looks at LHS since that's where the active pair is defined)
constrNamesFor :: FuncName -> Rule -> [ConstrName]
constrNamesFor fName (Rule (Func f args) _)
    | f == fName = [name | Constr name _ <- args]
constrNamesFor _ _ = []

-- 3. Expand a single rule containing a GenConstr into a list of concrete rules
-- One rule is generated per constructor of matching arity in the constructor table
-- Constructors already having a specific rule for this function are skipped
expandGenConstr :: Rule -> [(ConstrName, Int)] -> [Rule] -> [Rule]
expandGenConstr rule@(Rule (Func fName args) rhs) constrTable allRules =
    case [i | (i, GenConstr vs) <- zip [0..] args] of
        -- no GenConstr found, return rule unchanged
        []    -> [rule]
        -- found a GenConstr at position pos with variables vs
        (pos:_) ->
            let GenConstr vs  = args !! pos
                arity         = length vs
                -- get all constructors of matching arity from the table
                matching      = [name | (name, a) <- constrTable, a == arity]
                -- skip constructors that already have a specific rule
                specific      = specificConstrs fName allRules
                toExpand      = filter (`notElem` specific) matching
                -- substitute GenConstr with a concrete Constr in the LHS
                mkRule name   = Rule (Func fName (take pos args
                                ++ [Constr name vs]
                                ++ drop (pos+1) args))
                              (substGenConstr name vs rhs)  -- also substitute in RHS
                concreteRules = map mkRule toExpand
                -- for arity 0, also generate a nat variable rule
                natRule       = [Rule (Func fName (take pos args
                                ++ [NatVar "x"]
                                ++ drop (pos+1) args))
                                (substNatVar rhs)
                              | arity == 0] 
            in concreteRules ++ natRule
-- non-Func rules are returned unchanged
expandGenConstr rule _ _ = [rule]

-- Substitute GenConstr [] with NatVar "x" throughout a term
substNatVar :: Term -> Term
substNatVar (GenConstr [])     = NatVar "x"
substNatVar (Func f args)      = Func f (map substNatVar args)
substNatVar (Constr c args)    = Constr c (map substNatVar args)
substNatVar (Par t1 t2)        = Par (substNatVar t1) (substNatVar t2)
substNatVar (Let t1 vs t2)     = Let (substNatVar t1) vs (substNatVar t2)
substNatVar t                  = t

-- Substitute GenConstr with a concrete constructor throughout a term
substGenConstr :: ConstrName -> [Term] -> Term -> Term
substGenConstr name vs (GenConstr args)  = Constr name (map (substGenConstr name vs) args)
substGenConstr name vs (Func f args)     = Func f (map (substGenConstr name vs) args)
substGenConstr name vs (Constr c args)   = Constr c (map (substGenConstr name vs) args)
substGenConstr name vs (Par t1 t2)       = Par (substGenConstr name vs t1) (substGenConstr name vs t2)
substGenConstr name vs (Let t1 vs' t2)   = Let (substGenConstr name vs t1) vs' (substGenConstr name vs t2)
substGenConstr _    _  t                 = t

-- 4. Top-level expansion pass: expand all generic constructor rules into
-- concrete rules, then combine with the specific rules
expandAllGenConstrs :: [Rule] -> [Rule]
expandAllGenConstrs rules =
    let -- build constructor table from all rules in the file
        constrTable   = collectConstrs rules
        -- separate generic rules (containing GenConstr) from specific ones
        (generic, specific) = partition hasGenConstr rules
        -- expand each generic rule into a list of concrete rules
        expanded      = concatMap (\r -> expandGenConstr r constrTable rules) generic
    in specific ++ expanded

-- Check if a rule contains a GenConstr anywhere in its LHS
hasGenConstr :: Rule -> Bool
hasGenConstr (Rule (Func _ args) _) = any isGenConstr args
hasGenConstr _                      = False

-- Check if a term is a GenConstr
isGenConstr :: Term -> Bool
isGenConstr (GenConstr _) = True
isGenConstr _             = False


-- Implicit memory management
-- 1. Erasure
-- Collect all variable names from a term
varsInTerm :: Term -> [VarName]
varsInTerm (Var v)          = [v]
varsInTerm (NatVar v)       = [v]
varsInTerm (Constr _ args)  = concatMap varsInTerm args
varsInTerm (Func _ args)    = concatMap varsInTerm args
varsInTerm (Par t1 t2)      = varsInTerm t1 ++ varsInTerm t2
varsInTerm (Let t1 _ t2)    = varsInTerm t1 ++ varsInTerm t2
varsInTerm _                = []

-- Add !eraser for any LHS variables missing from RHS
addErasers :: Rule -> Rule
addErasers rule@(Rule lhs rhs) =
    let lhsVars     = varsInTerm lhs
        rhsVars     = varsInTerm rhs
        missing     = filter (`notElem` rhsVars) lhsVars
        erasers     = map (\v -> Func "!eraser" [Var v]) missing
        newRhs      = foldl Par rhs erasers
    in if null missing then rule else Rule lhs newRhs

-- Apply addErasers to all rules (only called if -imm flag set)
addAllErasers :: [Rule] -> [Rule]
addAllErasers = map addErasers

-- 2. duplication
-- Find variables that appear more than once in a term
duplicatedVars :: Term -> [VarName]
duplicatedVars t = [v | v <- nub (varsInTerm t), count v (varsInTerm t) > 1]
  where count x xs = length (filter (== x) xs)

-- Replace all occurrences of a variable with a new name in a term
substVar :: VarName -> VarName -> Term -> Term
substVar old new (Var v)         = if v == old then Var new else Var v
substVar old new (NatVar v)      = if v == old then NatVar new else NatVar v
substVar old new (Constr c args) = Constr c (map (substVar old new) args)
substVar old new (Func f args)   = Func f (map (substVar old new) args)
substVar old new (Par t1 t2)     = Par (substVar old new t1) (substVar old new t2)
substVar old new (Let t1 vs t2)  = Let (substVar old new t1) vs (substVar old new t2)
substVar _   _   t               = t

-- Add !duplicator lets for any variable appearing more than once on RHS
-- Processes one variable at a time, nesting lets if needed
addDuplicators :: Rule -> Rule
addDuplicators (Rule lhs rhs) = Rule lhs (addDupsToTerm rhs)

addDupsToTerm :: Term -> Term
addDupsToTerm t =
    case duplicatedVars t of
        []    -> t
        (v:_) ->
            let v1   = v ++ "1"
                v2   = v ++ "2"
                -- replace all occurrences with v2, then replace first v2 with v1
                t'   = replaceFirst v2 v1 (substVar v v2 t)
                letT = Let (Func "!duplicator" [Var v]) [v1, v2] t'
            in addDupsToTerm letT

-- Replace only the first occurrence of a variable in a term
replaceFirst :: VarName -> VarName -> Term -> Term
replaceFirst old new t = fst (go t)
  where
    go (Var v) | v == old       = (Var new, True)
    go (Var v)                  = (Var v, False)
    go (Par t1 t2)              =
        let (t1', done) = go t1
        in if done then (Par t1' t2, True)
           else let (t2', done2) = go t2
                in (Par t1' t2', done2)
    go (Func f args)            = let (args', done) = goList args
                                  in (Func f args', done)
    go (Constr c args)          = let (args', done) = goList args
                                  in (Constr c args', done)
    go (Let t1 vs t2)           = let (t1', done) = go t1
                                  in if done then (Let t1' vs t2, True)
                                     else let (t2', done2) = go t2
                                          in (Let t1' vs t2', done2)
    go t                        = (t, False)
    goList []                   = ([], False)
    goList (x:xs)               = let (x', done) = go x
                                  in if done then (x':xs, True)
                                     else let (xs', done2) = goList xs
                                          in (x':xs', done2)

-- Apply addDuplicators to all rules
addAllDuplicators :: [Rule] -> [Rule]
addAllDuplicators = map addDuplicators


-- deal with issue that INPLA uses "anonymous" attributes and we treat nats as symbols
-- Check if a rule's LHS has a Nat literal as its constructor argument
hasNatLit :: Rule -> Bool
hasNatLit (Rule (Func _ args) _) = any isNatLit args
hasNatLit _                      = False

isNatLit :: Term -> Bool
isNatLit (Nat _) = True
isNatLit _       = False

-- Check if a rule's LHS has a NatVar as its constructor argument
hasNatVar :: Rule -> Bool
hasNatVar (Rule (Func _ args) _) = any isNatVarTerm args
hasNatVar _                      = False

isNatVarTerm :: Term -> Bool
isNatVarTerm (NatVar _) = True
isNatVarTerm _          = False

-- Get function name from a rule's LHS
ruleFuncName :: Rule -> Maybe FuncName
ruleFuncName (Rule (Func f _) _) = Just f
ruleFuncName _                   = Nothing

-- Get the Nat literal value from a rule's LHS
ruleNatLit :: Rule -> Maybe Int
ruleNatLit (Rule (Func _ args) _) = 
    case [n | Nat n <- args] of
        (n:_) -> Just n
        []    -> Nothing
ruleNatLit _ = Nothing

-- Get all function names that have at least one Nat literal rule
natLitFuncNames :: [Rule] -> [FuncName]
natLitFuncNames rules = nub [f | r@(Rule (Func f _) _) <- rules, hasNatLit r]

-- Group nat-related rules for a given function name
groupNatRulesFor :: FuncName -> [Rule] -> ([Rule], Maybe Rule)
groupNatRulesFor fName rules =
    let fRules   = [r | r@(Rule (Func f _) _) <- rules, f == fName]
        litRules = filter hasNatLit fRules
        varRule  = case filter hasNatVar fRules of
                       (r:_) -> Just r
                       []    -> Nothing
    in (litRules, varRule)

--- Generate a single guarded INPLA rule from Nat literal rules + optional catch-all
makeGuardedNatRule :: [Rule] -> Maybe Rule -> LUT -> String
makeGuardedNatRule litRules mVarRule lut =
    let -- get variable name from NatVar rule, default to "x"
        varName = case mVarRule of
                    Just (Rule (Func _ args) _) -> head [v | NatVar v <- args]
                    Nothing                      -> "x"
        -- translate each lit rule to get its RHS
        transLit (Rule (Func f args) rhs) =
            let n       = head [n | Nat n <- args]
                rhsNet  = cleanNet $ trans rhs "r" ([],[]) lut
                rhsStr' = init (netToINPLA rhsNet)
            in " | " ++ varName ++ "==" ++ show n ++ " => " ++ rhsStr'
        -- get header from first rule
        Rule (Func fName args) _ = head litRules
        -- get output ports from LHS translation
        lhs      = cleanNet $ trans (Func fName args) "r" ([],[]) lut
        (agents,_) = lhs
        (_, _, auxPorts) = head agents
        outPorts = listPorts auxPorts
        header   = fName ++ "(" ++ outPorts ++ ") >< (int " ++ varName ++ ")"
        guards   = concatMap transLit litRules
        catchAll = case mVarRule of
                     Just (Rule _ rhs) ->
                         let rhsNet  = cleanNet $ trans rhs "r" ([],[]) lut
                             rhsStr  = init (netToINPLA rhsNet)
                         in " | _ => " ++ rhsStr
                     Nothing -> " | _ => r~ERROR"
    in header ++ guards ++ catchAll ++ ";"


-- nested pattern matching
-- Check if a rule has nested constructors on the LHS
hasNestedPattern :: Rule -> Bool
hasNestedPattern (Rule (Func _ args) _) = any isNestedConstr args
hasNestedPattern _                      = False

-- Check if a constructor has any constructor arguments (i.e. is nested)
isNestedConstr :: Term -> Bool
isNestedConstr (Constr _ args) = any isConstr args
isNestedConstr _               = False

-- Check if a term is any constructor
isConstr :: Term -> Bool
isConstr (Constr _ _) = True
isConstr _            = False

testHasNestedPattern :: FilePath -> IO ()
testHasNestedPattern filename = do
    inputFile <- readFile filename
    let inputLines  = lines inputFile
        ruleLines   = filter (not . ("--" `isPrefixOf`)) inputLines
        parsedRules = map parseRule ruleLines
        rules       = expandAllGenConstrs [r | Right r <- parsedRules]
    putStrLn "Nested pattern rules:"
    mapM_ (putStrLn . show) (filter hasNestedPattern rules)
    putStrLn "\nNon-nested rules:"
    mapM_ (putStrLn . show) (filter (not . hasNestedPattern) rules)

-- Given a LHS net with >2 agents, identify:
-- (activePair1, activePair2, nestedAgent, nestedPort)
-- where nestedPort is the aux port of activePair2 that connects to nestedAgent
findNestedAgent :: Net -> Maybe (Agent, Agent, Agent, Port, [Agent])
findNestedAgent (agents, wires) =
    let alpha = head agents
        (aName, aPP, aAux) = alpha
        beta = head [a | a@(_, pp, _) <- tail agents, pp == aPP]
        (bName, bPP, bAux) = beta
        nested = [a | a@(_, pp, _) <- agents, pp `elem` bAux, a /= alpha, a /= beta]
    in case nested of
        []    -> Nothing
        (g:_) -> 
            let (gName, gPP, gAux) = g
                nestedPort = head [p | p <- bAux, p == gPP]
                -- a is any further agents connected to gamma's aux ports
                a = [ag | ag@(_, pp, _) <- agents, pp `elem` gAux, ag /= alpha, ag /= beta, ag /= g]
            in Just (alpha, beta, g, nestedPort, a)


-- multiple principal ports
-- Check if a rule has a constructor in non-first argument position (MPP rule)
hasMPP :: Rule -> Bool
hasMPP (Rule (Func _ args) _) = any isConstr (tail args)
hasMPP _                      = False

-- Get function name and first-position constructor name from an MPP rule
mppKey :: Rule -> Maybe (FuncName, ConstrName)
mppKey (Rule (Func f (Constr c _ : _)) _) = Just (f, c)
mppKey _                                   = Nothing

-- Group MPP rules by (function name, first-position constructor)
groupMPPRules :: [Rule] -> [((FuncName, ConstrName), [Rule])]
groupMPPRules rules =
    let mppRules = filter hasMPP rules
        keys     = nub [k | Just k <- map mppKey mppRules]
    in [(k, [r | r <- mppRules, mppKey r == Just k]) | k <- keys]

-- Generate dispatch rule and auxiliary rules for a group of MPP rules
-- e.g. max(S(x),Z)=S(x) and max(S(x),S(y))=S(max(x,y))
-- becomes:
-- dispatch: max(S(x),y) = mppMaxS(y,x)
-- aux:      mppMaxS(Z,x) = S(x)
--           mppMaxS(S(y),x) = S(max(x,y))
expandMPPGroup :: (FuncName, ConstrName) -> [Rule] -> [Rule]
expandMPPGroup (fName, cName) rules =
    let -- auxiliary function name
        auxName  = "mpp" ++ fName ++ cName
        -- get first constructor's args from first rule (they're all the same)
        Rule (Func _ (Constr _ cArgs : _)) _ = head rules
        -- fresh variable for the second argument in dispatch rule
        secVar   = "mppY"
        -- dispatch rule: fName(Constr(cArgs), secVar) = auxName(secVar, cArgs)
        dispatch = Rule (Func fName [Constr cName cArgs, Var secVar])
                        (Func auxName (Var secVar : cArgs))
        -- auxiliary rules: one per second-position pattern
        mkAux (Rule (Func _ (_ : rest)) rhs) =
            Rule (Func auxName (rest ++ cArgs)) rhs
        auxRules = map mkAux rules
    in dispatch : auxRules

expandAllMPP :: [Rule] -> [Rule]
expandAllMPP rules =
    let groups    = groupMPPRules rules
        mppRules  = filter hasMPP rules
        normalRules = filter (not . hasMPP) rules
        expanded  = concatMap (uncurry expandMPPGroup) groups
    in normalRules ++ expanded


-- HOFs
-- Rename FuncRef and FuncApp to use f_hat port names
renameFuncRefsRule :: Rule -> Rule
renameFuncRefsRule (Rule lhs rhs) = Rule (renameFuncRefs lhs) (renameFuncRefs rhs)

renameFuncRefs :: Term -> Term
renameFuncRefs (FuncRef f)       = Var (f ++ "_hat")
renameFuncRefs (FuncApp f x)     = Func "i_app" [Var (f ++ "_hat"), renameFuncRefs x]
renameFuncRefs (Constr c args)   = Constr c (map renameFuncRefs args)
renameFuncRefs (Func f args)     = Func f (map renameFuncRefs args)
renameFuncRefs (Par t1 t2)       = Par (renameFuncRefs t1) (renameFuncRefs t2)
renameFuncRefs (Let t1 vs t2)    = Let (renameFuncRefs t1) vs (renameFuncRefs t2)
renameFuncRefs t                 = t

-- Apply renameFuncRefsRule to all rules
expandFuncRefs :: [Rule] -> [Rule]
expandFuncRefs = map renameFuncRefsRule