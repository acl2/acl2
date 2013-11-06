# Avoid provisional certification because of directory circularities,
# as explained below:
override ACL2_PCERT =

DIRS = generic-modules instantiations

include ../../../../Makefile-subdirs

# Each of the following two directories depends on the other:
# instantiations/genoc/simple-ct-global/
# instantiations/scheduling/circuit-switching-global/
# To see this notice the following two forms.
# In instantiations/genoc/simple-ct-global/simple.lisp:
#   (include-book "../../scheduling/circuit-switching-global/circuit")
# In instantiations/scheduling/circuit-switching-global/circuit.lisp:
# (include-book "../../genoc/simple-ct-global/trlst-equal")
