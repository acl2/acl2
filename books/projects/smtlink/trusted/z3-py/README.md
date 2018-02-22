---------------------------------------------------------------

                  z3_interface README

---------------------------------------------------------------

Subdirectory z3_interface is for storing interface files to
SMT solvers.

The default z3 interface file provided is ACL2_to_Z3.py.

---------------------------------------------------------------

                  NECESSARY METHODS

Smtlink's built-in translator requires several premitive
functions to be implemented. Below is the list of functions
needed:

  __SMT__.plus       : binary addition
  __SMT__.times      : binary multiplication
  __SMT__.reciprocal : reciprocal
  __SMT__.negate     : numerical negation
  __SMT__.equal      : equality
  __SMT__.lt         : less than
  __SMT__.ifx        : if statement
  __SMT__.not        : logic negation
  __SMT__.lambda     : lambda expression
  __SMT__.implies    : logic implication
  __SMT__.integerp   : integer type check
  __SMT__.rationalp  : rational type check
  __SMT__.booleanp   : boolean type check

Check details in ACL2_to_Z3.py.

--------------------------------------------------------------

                  INHERIT FROM ACL22SMT

Check RewriteExpt.py for how to inherit from class ACL22SMT
and extend the interface capabilities.

--------------------------------------------------------------