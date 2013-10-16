DIRS = ordinals dag-unification reflexive defpun-exec find-path/graph find-path other-apps
include ../Makefile-psubdirs

# Because find-path/Makefile has the dependency
# fpst.cert: graph/linear-find-path.cert
# we add the following:
find-path: find-path/graph
