module Trans where

import Data.Char (ord, chr, isAlpha, isAlphaNum, isLower, isDigit)
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


-- main takes a list of flags and a file name *.txt (order ignored)
-- if -bat is there, calls batch else calls interactive
-- both consider following flags:
-- -imm = implicit memory management (adds erase & duplication on RHS of rules)
-- -npm = nested pattern matching (implements Interaction Nets with NPM by Hassan & Sato)
-- -hof = deal with higher order functions
-- can have multiple flags
-- If -bat then file must have 0 or more rules followed by 1 or more blank lines and a term.
-- Comments are -- ; single line only
main :: [String] -> IO ()
main args =
    if "-bat" `elem` args
    then batch args
    else interactive args

-- flags recognised by main; anything else in args is the filename
allFlags :: [String]
allFlags = ["-imm", "-npm", "-mpp", "-hof", "-bat"]

-- shared by interactive and batch: parse and expand rules, build LUT, translate rules to INPLA
-- pipeline order: gen constrs -> mpp -> hofs -> imm
processRules :: [String] -> [String] -> (LUT, String)
processRules args ruleLines =
    let imm         = "-imm" `elem` args
        npm         = "-npm" `elem` args
        mpp         = "-mpp" `elem` args
        hof         = "-hof" `elem` args
        parsedRules = map parseRule ruleLines
        rules       = (if imm then addAllErasers . addAllDuplicators else id)
                      $ (if hof then expandAllFuncApps else id)
                      $ (if mpp then expandAllMPP else id)
                      $ expandAllGenConstrs
                      $ [r | Right r <- parsedRules]
        errors      = [e | Left e <- parsedRules]
        builtinLUT  = [("succ", 1), ("pred", 1), ("!eraser", 0), ("!duplicator", 2), ("i_lam", 1), ("i_app", 1)]
        lut         = makeLUT rules builtinLUT
        transRules  = dupToDup (transRuleList rules lut npm)
    in if not (null errors)
       then error ("Parse errors: " ++ show errors)
       else (lut, transRules)

interactive :: [String] -> IO ()
interactive args = do
    let filename = head (filter (`notElem` allFlags) args)
    inputFile <- readFile filename
    let ruleLines = filter (not . null . words) $ filter (not . ("--" `isPrefixOf`)) (lines inputFile)
        (lut, transRules) = processRules args ruleLines
    putStrLn "Input file:"
    putStrLn inputFile
    putStrLn "\nINPLA rules:"
    putStrLn transRules
    putStrLn ""
    putStr "Enter a FLIN term to translate, or :Q to quit"
    putStrLn ""
    replLoop lut

batch :: [String] -> IO ()
batch args = do
    let filename = head (filter (`notElem` allFlags) args)
    inputFile <- readFile filename
    let nonComment = filter (not . ("--" `isPrefixOf`)) (lines inputFile)
        cleaned    = filter (not . null) nonComment
        termLine   = last cleaned
        rs         = init cleaned
        (lut, transRules) = processRules args rs
        termResult  = case inpla lut termLine of
                          Left err  -> "Parse error: " ++ show err
                          Right str -> str
        Right pt    = parseTerm termLine
        netTerm     = trans pt "r" ([],[]) lut
        outPorts    = unconnectedPorts netTerm
        outFile     = reverse (dropWhile (/= '.') (reverse filename)) ++ "in"
        output      = transRules ++ "\n" ++ termResult ++ "\n" ++ (unwords outPorts) ++ ";\n"
    writeFile outFile output
    putStrLn $ "Written to " ++ outFile

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
-- special case for higher-order constructor "i_lam"
trans (Constr "i_lam" [port, Func fname _]) root (agents, wires) lut =
    (agents ++ [("i_lam", root, ["a1"++root++fname, "a2"++root++fname]),
                (fname, "a1"++root++fname, ["a2"++root++fname])],
     wires)

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
      pp      = fresh root

      -- output ports: first is root, rest are root ++ fresh iterated
      outPorts = 
        if numOuts == 0 then []
        else root : map (root ++) (take (numOuts - 1) $ tail $ iterate fresh root)

      -- input ports (excluding pp itself)
      numInPortsExPP = length args - 1
      inPortsExPP    = map (pp ++) (take numInPortsExPP $ tail $ iterate fresh pp)

      -- the function agent itself
      newAgent       = (fName, pp, outPorts ++ inPortsExPP)

      -- now handle arguments, threading the accumulated net through each
      -- translation (passing the same incoming net to every argument duplicates
      -- it once per Var argument, which corrupts cleanNet's collapsing)
      (netAgents, netWires) = net
      (allAgents, allWires) =
        foldl
          (\(as, ws) (arg, port) ->
             let freshP       = port ++ "_0"
                 (as', ws')   = trans arg freshP (as, ws) lut
                 newWire      = (freshP, port)  -- connect arg result to function input
             in  (as', newWire : ws'))
          (newAgent : netAgents, netWires)
          (zip args (pp : inPortsExPP))
  in
      (allAgents, allWires)

-- natural number variables
trans (NatVar v) root (agents, wires) _ =
    -- (agents ++ [("(int " ++ v ++ ")", root, [])], wires)
    -- (agents ++ [(v, root, [])], wires)
       (agents , wires++[(root,v)])

-- natural number literals: on RHS become n port for pattern matching
trans (Nat n) root (agents, wires) _ =
    -- (agents ++ [("(int " ++ show n ++ ")", root, [])], wires)
    (agents ++ [(show n, root, [])], wires)

-- let
trans (Let t1 vars t2) root net lut =
  let
      -- 1. Translate t1
      (agents1, wires1) = cleanNet $ trans t1 root net lut

      -- 2. Rename outputs of t1 to match 'vars'
      (agents1',wires1') = cleanNet $
        if null agents1 then (agents1, renameWire t1 (head wires1) (head vars))   -- only handles 1 wire
        else ((renameOutputs t1 (head agents1) vars lut) : tail agents1, wires1)  -- only handles 1 agent

      -- 3. Translate t2 with updated net
      (agents2,wires2) = 
        if null agents1' then (agents1',wires1')
        else 
          let (agents3,wires3) = cleanNet $ trans t2 root ([],[]) lut -- (root++"L"++(fresh root))
          in (agents1'++agents3,wires1'++wires3)
  in
      -- Output ex duplications created
      cleanNet (nub agents2, nub wires2)

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

-- function application: should not be called
trans (FuncApp f args) root (agents, wires) _ =
    error "FuncApp should have been expanded before translation"

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
  undefined -- because dealt with by renameWire
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
  | null inplaAgents = inplaWires  ++ ";"
  | null inplaWires  = inplaAgents ++ ";"
  | otherwise        = inplaAgents ++ "," ++ inplaWires ++ ";"
  where
    (cleanAgents, cleanWires) = cleanNet (agents, wires)
    (inplaAgents, inplaWires) = (agentsToINPLA cleanAgents, wiresToINPLA cleanWires)

agentsToINPLA :: [Agent] -> String
agentsToINPLA []     = ""
agentsToINPLA [(symbol, pp, auxPorts)]    = agentStr symbol auxPorts ++ "~" ++ pp
agentsToINPLA ((symbol, pp, auxPorts):as) = agentStr symbol auxPorts ++ "~" ++ pp ++ "," ++ agentsToINPLA as

agentStr :: Symbol -> [Port] -> String
agentStr symbol auxPorts
    | head symbol == '['          = symbol
    | symbol      == "!eraser"    = "Eraser"
    | symbol      == "!Cons"      = "(" ++ head auxPorts ++ ":" ++ last auxPorts ++ ")"
    | "(int " `isPrefixOf` symbol = init (drop 5 symbol)
    | all isDigit symbol          = symbol
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
-- multiple applications because if have npm'd rules need originals in first in case newly created refer to them
makeLUT rules lut = makeLUT' (npmTransRuleList rules) (makeLUT' rules lut)

makeLUT' :: [Rule] -> LUT -> LUT
makeLUT' [] lut = lut
makeLUT' (Rule t1 t2 : rs) lut =
    case t1 of
        Func fName _ ->
            if any (\(name, _) -> name == fName) lut
               then makeLUT' rs lut  -- already in LUT, skip
               else
                   let numOuts = countOuts t2 lut
                       lut'    = lut ++ [(fName, numOuts)]
                   in makeLUT' rs lut'
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
countOuts (FuncApp _ _) _   = 1

-- fresh port names - appends _0 after alpha, increments digit after _, 9 -> _a
fresh :: String -> String
fresh s
  | isAlpha (last s) = s ++ "_0"
  | last s == '9'    = init s ++ "_a"
  | otherwise        = init s ++ [chr (ord (last s) + 1)]

-- clean up intermediate links e.g. a~b,b~c
cleanNet :: Net -> Net
cleanNet (agents, wires) = 
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
        lhs        = transLHS t1 root lut -- cleanNet $ trans t1 root ([], []) lut
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
                Let _ _ _ -> cleanUpLetOutputs lhs (cleanNet $ trans t2 root ([], []) lut) lut
                _         -> let (agents,wires) = trans t2 root ([], []) lut
                             in cleanNet (nub agents,nub wires) 
       in let lhsStr = transActivePair lhs
          in lhsStr ++ netToINPLA (renameNetPorts lhsStr rhs)
    -- in if npm && numAgents > 2
    --    then applyT lhs t2 root lut npm
    --    else let lhsStr = transActivePair lhs
    --         in lhsStr ++ netToINPLA (renameNetPorts lhsStr rhs)

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
transRuleList ruleList lut npm =
    builtins ++ guardedRules ++ dupToDup normalRules
    where
        rules = if npm then npmTransRuleList ruleList else ruleList
        -- built in INPLA rules : succ&pred to work with natural number consturctors and i_app and i_lam for lambda calculus for HOFs
        -- note pred min is 0
        builtins = "succ(r) >< (int x) => r~(x+1);\npred(r)><(int x) | x>0 => r~x-1 | _ => r~0;\ni_app(r,v) >< i_lam(x,f) => r~f,v~x;\n"
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
    let parsedTerm = parseTerm term
    in
    case parsedTerm of
        Left err -> Left err
        Right t  -> Right (cleanNet $ trans (transHOFterm t) "r" ([], []) lut) 

inpla :: LUT -> String -> Either ParseError String
inpla lut term =
  case tr lut term of
    Left err  -> Left err
    Right net -> Right (netToINPLA net)

inLHSonly :: Net -> Net -> [String]
inLHSonly (lhsAgents, lhsWires) (rhsAgents, rhsWires) =
  let lhsPorts = map (\(_,pp,aux) -> aux) lhsAgents
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
  in uniqueOnly attempt1

unconnectedPortsAgents :: Net -> [Port]
unconnectedPortsAgents (agents, wires) = uniqueOnly $ concatMap portList agents

portList :: Agent -> [Port]
portList (symbol,pp,auxList) = pp:auxList

-- notInLHS :: Net -> [String] -> [String]
-- notInLHS (lhsAgents, lhsWires) ports =
--   let lhsPorts = concatMap (\(_,pp,aux) -> pp:aux) lhsAgents ++ concatMap (\(a,b) -> [a,b]) lhsWires
--   in filter (`notElem` lhsPorts) ports

notInLHS :: Net -> [String] -> [String]
notInLHS (lhsAgents, lhsWires) ports =
  let lhsAgents'   = map stripAgent lhsAgents
      lhsPorts     = concatMap (\(_,pp,aux) -> aux) lhsAgents' -- ++ concatMap (\(a,b) -> [a,b]) lhsWires
  in filter (`notElem` lhsPorts) ports

stripInts :: Net -> Net
stripInts ([agent1,agent2],wires) = (([stripAgent agent1] ++ [stripAgent agent2]), wires)

stripAgent :: Agent -> Agent
stripAgent (symbol, pp, auxPorts) =
    let stripInt s | "int " `isPrefixOf` s  = Just (drop 4 s)
                   | "(int " `isPrefixOf` s = Just (drop 5 (init s))
                   | otherwise              = Nothing
        auxPorts' = map (\s -> case stripInt s of Just v -> v; Nothing -> s) auxPorts
        newAux    = case stripInt symbol of
                        Just v  -> auxPorts' ++ [v]
                        Nothing -> auxPorts'
    in (symbol, pp, newAux)

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
    in expanded ++ specific

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
    go (NatVar v) | v == old    = (NatVar new, True)
    go (NatVar v)               = (NatVar v, False)
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

--- Generate a single guarded INPLA rule from Nat literal rules + catch-all
makeGuardedNatRule :: [Rule] -> Maybe Rule -> LUT -> String
makeGuardedNatRule litRules mVarRule lut =
    let -- get variable name from NatVar rule, default to "x_0"
        varName = case mVarRule of
                    Just (Rule (Func _ args) _) -> head [v | NatVar v <- args]
                    Nothing                     -> "x_0"
        -- get header from first rule
        Rule (Func fName args) _ = case mVarRule of
                                     Just r  -> r
                                     Nothing -> head litRules
        -- get output ports from LHS translation
        lhs        = transLHS (Func fName args) "r" lut
        (agents,_) = lhs
        (_, _, auxPorts) = head agents
        outPorts = listPorts auxPorts
        header   = fName ++ "(" ++ outPorts ++ ") >< (int " ++ varName ++ ")"
        -- translate a RHS, rooting Par components at the LHS output ports
        -- (otherwise trans's Par case invents its own roots, e.g. r_0 vs rr_0)
        numOuts  = funcNumOuts fName lut
        rhsRoots = take numOuts auxPorts
        transRHS rhs = case rhs of
            Par _ _ -> cleanNet $ foldl
                           (\(aAcc, wAcc) (t, p) ->
                                let (a', w') = trans t p ([], []) lut
                                in (aAcc ++ a', wAcc ++ w'))
                           ([], [])
                           (zip (flatPar rhs) rhsRoots)
            _       -> cleanNet $ trans rhs "r" ([], []) lut
        -- translate each lit rule to get its RHS
        transLit (Rule (Func f args) rhs) =
            let n       = head [n | Nat n <- args]
                rhsStr' = init (netToINPLA (transRHS rhs))
            in " | " ++ varName ++ "==" ++ show n ++ " => " ++ rhsStr'
        guards   = concatMap transLit litRules
        catchAll = case mVarRule of
                     Just (Rule (Func f ((NatVar var):vars)) rhs) ->
                         let rhsNet  = transRHS rhs
                             rhsNet' = if null (fst rhsNet)
                                       then let ports = snd rhsNet
                                            in ([], map (\(a, b) -> (a++"~"++var, b++"~"++var)) ports)
                                       else rhsNet
                             rhsStr  = if null (fst rhsNet)
                                       then intercalate "," (concatMap (\(a, b) -> [a, b]) (snd rhsNet'))
                                       else init (netToINPLA rhsNet)
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
isConstr (Constr _ _)  = True
isConstr (ListTerm []) = True
isConstr _             = False

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
mppKey (Rule (Func f (Constr c _ : _)) _)  = Just (f, c)
mppKey (Rule (Func f (ListTerm [] : _)) _) = Just (f, "Nil")
mppKey (Rule (Func f (NatVar _ : _)) _)    = Just (f, "Int")
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
    let -- auxiliary function name; '!' (from !Cons) replaced with '_' for INPLA
        auxName  = "mpp" ++ fName ++ map (\ch -> if ch == '!' then '_' else ch) cName
        -- first-position pattern: args to carry to aux, and the LHS pattern itself
        (cArgs, cPat) = case head rules of
            Rule (Func _ (Constr c args : _)) _ -> (args, Constr c args)
            Rule (Func _ (ListTerm [] : _)) _   -> ([], ListTerm [])
            Rule (Func _ (NatVar v : _)) _      -> ([Var v], NatVar v)
            _ -> error "expandMPPGroup: unexpected pattern"
        -- fresh variable for the second argument in dispatch rule
        secVar   = "mppY"
        -- dispatch rule: fName(cPat, secVar) = auxName(secVar, cArgs)
        dispatch = Rule (Func fName [cPat, Var secVar])
                        (Func auxName (Var secVar : cArgs))
        -- auxiliary rules: one per second-position pattern
        mkAux (Rule (Func _ (_ : rest)) rhs) =
            Rule (Func auxName (rest ++ cArgs)) rhs
        auxRules = map mkAux rules
    in auxRules ++ [dispatch]

expandAllMPP :: [Rule] -> [Rule]
expandAllMPP rules =
    let groups    = groupMPPRules rules
        mppRules  = filter hasMPP rules
        badRules  = [r | r <- mppRules, mppKey r == Nothing]
        normalRules = filter (not . hasMPP) rules
        expanded  = concatMap (uncurry expandMPPGroup) groups
    in if not (null badRules)
       then error ("MPP rule needs a constructor pattern in the first argument: " ++ show (head badRules))
       else normalRules ++ expanded


-- HoFs
expandFuncApp :: Term -> Term
expandFuncApp (FuncApp f args)   = Func "i_app" (Var f : map expandFuncApp args)
expandFuncApp (Constr c args)    = Constr c (map expandFuncApp args)
expandFuncApp (Func f args)      = Func f (map expandFuncApp args)
expandFuncApp (Par t1 t2)        = Par (expandFuncApp t1) (expandFuncApp t2)
expandFuncApp (Let t1 vs t2)     = Let (expandFuncApp t1) vs (expandFuncApp t2)
expandFuncApp t                  = t

expandFuncAppRule :: Rule -> Rule
expandFuncAppRule (Rule lhs rhs) = Rule (expandFuncApp lhs) (expandFuncApp rhs)

expandAllFuncApps :: [Rule] -> [Rule]
expandAllFuncApps = map expandFuncAppRule

extractLHSPorts :: String -> [String]
extractLHSPorts [] = []
extractLHSPorts s =
    case dropWhile (/= '(') s of
        [] -> []
        (_:rest) ->
            let ports = filter (/= "int") $ splitOnNonIdent (takeWhile (/= ')') rest)
            in ports ++ extractLHSPorts (dropWhile (/= ')') rest)

renameNetPorts :: String -> Net -> Net
renameNetPorts str net = net

splitOnNonIdent :: String -> [String]
splitOnNonIdent [] = []
splitOnNonIdent s@(c:cs)
    | isIdentChar c = let (word, rest) = span isIdentChar s
                      in word : splitOnNonIdent rest
    | otherwise     = splitOnNonIdent cs

isIdentChar :: Char -> Bool
isIdentChar c = isAlphaNum c || c == '_'

transLHS :: Term -> Port -> LUT -> Net
transLHS term root lut =
    let (Func fName (c:auxs1))  = term
        numOuts1                = funcNumOuts fName lut
        outPorts1               = if numOuts1 == 0 then []
                                  else
                                  root : map (root ++) (take (numOuts1 - 1) $ tail $ iterate fresh root)
        agent1                  = (fName, "p1", outPorts1 ++ (map transAux auxs1))
        agent2                  = case c of
                                    ListTerm []        -> ("[]", "p2", [])
                                    Constr cName auxs2 -> (cName, "p2", map (\(Var s) -> s) auxs2)
                                    Nat n              -> ("(int " ++ show n ++ ")", "p2", [])
                                    NatVar v           -> ("(int " ++ v ++ ")", "p2", [])
                                    _                  -> error "transLHS: unsupported constructor pattern"
        in ([agent1]++[agent2],[("p1","p2")])

-- Translate an aux port term to a port name
transAux :: Term -> String
transAux (Var s)    = s
transAux (NatVar v) = "int " ++ v
transAux _          = error "transAux: unsupported aux pattern"

-- translate HOF term
transHOFterm :: Term -> Term
transHOFterm (Func name [])    = Constr "i_lam" [Var (name ++ "_pp"), Func name []]
transHOFterm (Func name args)  = Func name (map transHOFterm args)
transHOFterm (Constr c args)   = Constr c (map transHOFterm args)
transHOFterm (Par t1 t2)       = Par (transHOFterm t1) (transHOFterm t2)
transHOFterm (Let t1 vs t2)    = Let (transHOFterm t1) vs (transHOFterm t2)
transHOFterm t                 = t


-- npm
-- Scan a rule's LHS for constructors, Nats, or ListTerms in non-first positions
-- (including nested within the first argument's arguments)
-- Scan a Term for constructors, Nats, or ListTerms in non-first positions
-- (including nested within the first argument's arguments)
npmTransRuleList :: [Rule] -> [Rule]
npmTransRuleList = concatMap npmTrans

npmTrans :: Rule -> [Rule]
npmTrans rule =
    let Rule (Func fName args) rhs = rule
        listArgs = [arg | arg@(Constr c _) <- args, c == "!Cons" || c == "Cons"]
        allVars (Constr c cArgs) = all isVar cArgs
        isVar (Var _) = True
        isVar _       = False
        -- replaceNonVars (Constr _ cArgs) n =
        --     let replace arg i = case arg of
        --             Var _ -> arg
        --             _     -> Var ("var_" ++ show i)
        --     in Constr "!Cons" (zipWith replace cArgs [n..])
        replaceNonVars (Constr c cArgs) n =
            let replace arg i = case arg of
                    Var _ -> arg
                    _     -> Var ("var_" ++ show i)
            in Constr c (zipWith replace cArgs [n..])
        replaceNonVars t _ = t
        (newArgs, _) = foldl
            (\(as, n) arg -> case arg of
                Constr c _ | c == "!Cons" || c == "Cons" -> (as ++ [replaceNonVars arg n], n + 1)
                _                -> (as ++ [arg], n))
            ([], 0) args
        extractVars (Var v)          = [Var v]
        extractVars (Constr _ cArgs) = concatMap extractVars cArgs
        extractVars _                = []
        varsInArgs = concatMap extractVars newArgs
        newLHS  = Func fName newArgs
        newRHS  = Func (fName ++ "_1") (reverse varsInArgs)
        Constr _ [origA, origB] = head listArgs
        (replaced, other) = if isVar origA then (origB, origA) else (origA, origB)
        auxLHS  = Func (fName ++ "_1") [replaced, other]
        auxRule = Rule auxLHS rhs
    in if null listArgs || all allVars listArgs
       then [rule]
       else [Rule newLHS newRHS, auxRule]