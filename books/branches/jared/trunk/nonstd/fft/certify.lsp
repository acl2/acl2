(value :q)
(setq si::*multiply-stacks* 2)

(in-package "ACL2")

; We load the definition of the packages we need.

(ld "../powerlists/defpkg.lisp")

; We start out with polynomial evaluation.

(certify-book "eval-poly" 4)
:u

; Next is the abstract FFT proof

(certify-book "fft-omega" 4)
:u

; And here is the concrete FFT proof, using trigonometric axioms

(certify-book "fft-trig-with-axioms" 4)
:u

; And this is the same proof, using NSA sine/cosine instead of axioms

(certify-book "fft-trig" 4)
:u

; Finally, we retract even the definition of the POWERLISTS package

:u :u :u :u
