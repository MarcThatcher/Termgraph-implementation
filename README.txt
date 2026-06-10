README -- FLIN to INPLA translator

Sections below follow the abstract's sections.

4. Base FLIN

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

Note that the base case must not flag 'n' as an integer.
