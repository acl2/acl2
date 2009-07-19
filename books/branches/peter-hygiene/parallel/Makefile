include ../Makefile-generic
-include Makefile-deps

# Additional dependencies to force serialization when set-compile-fns is set
# (causes a problem for GCL 2.6.*).

matrix-multiplication-parallel.cert: matrix-multiplication-serial.cert
fibonacci.cert: matrix-multiplication-parallel.cert
