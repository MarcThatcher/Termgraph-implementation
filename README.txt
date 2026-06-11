README -- FLIN to INPLA translator

Please note this implementation is for demonstration purposes only.
In particular, not all errors are caught and those that are have messages designed for the author not the user.

Sections below follow the abstract's sections.

4. Base FLIN
Do not use _ in variable names.

4.1 Generic constructors

4.2 Implicit memory management

4.3 Nested pattern matching

4.4 Natural numbers
The INPLA rules:
succ(r) >< (int x) => r~(x+1);
pred(r) >< (int x) => r~(x-1);

are built in as INPLA has arithmetic included but FLIN does not.

Example:
add(0,  n) = n
add(_m,_n) = succ(add(pred(m),n))

The base case must not flag 'n' as an integer.

4.5 Multiple principal ports
First argument still must be a constructor (or *) as cannot handle parallel definitions.
(e.g. por(x,False) - if x never resolves.)

4.6 Higher-order functions
***are ports right way round on lam,app?