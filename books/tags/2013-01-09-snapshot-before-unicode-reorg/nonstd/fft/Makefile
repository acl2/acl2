include ../Makefile-generic

#  Put dependencies (from `make -s dependencies', or other sources) below.

eval-poly.cert: eval-poly.lisp
eval-poly.cert: ../arithmetic/top.cert
eval-poly.cert: ../powerlists/algebra.cert

fft-omega.cert: fft-omega.lisp
fft-omega.cert: eval-poly.cert

fft-trig.cert: fft-trig.lisp
fft-trig.cert: fft-omega.cert
fft-trig.cert: ../nsa/trig.cert

fft-trig-with-axioms.cert: fft-trig-with-axioms.lisp
fft-trig-with-axioms.cert: fft-omega.cert
