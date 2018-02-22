z3_interface
=====================

Subdirectory z3_interface is for storing interface files to
SMT solvers.

The default z3 interface file provided is ACL2_to_Z3.py.

### Basic functions

Smtlink's built-in translator requires several premitive
functions to be implemented. Below is the list of functions
needed:

  Option                 | Explanation
  ---------------------- | ---------------------------------
  \_\_SMT\_\_.plus       | binary addition
  \_\_SMT\_\_.times      | binary multiplication
  \_\_SMT\_\_.reciprocal | reciprocal
  \_\_SMT\_\_.negate     | numerical negation
  \_\_SMT\_\_.equal      | equality
  \_\_SMT\_\_.lt         | less than
  \_\_SMT\_\_.ifx        | if statement
  \_\_SMT\_\_.not        | logic negation
  lambda                 | lambda expression
  \_\_SMT\_\_.implies    | logic implication
  \_\_SMT\_\_.hint_okay  | function that always return false
  \_\_SMT\_\_.isInt      | integer type
  \_\_SMT\_\_.isReal     | real type
  \_\_SMT\_\_.isBool     | boolean type

Check details in ACL2_to_Z3.py.

### Customized module

Check details in RewriteExpt.py for extended module with customized abilities.
