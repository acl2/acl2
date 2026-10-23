; 07-inductance-note.lisp
;
; NOTE, with no executable content: Section III.F of the paper
; (equations 29-31, self and mutual inductance calculation) requires
; evaluating trigonometric definite integrals over [0, 2*pi] (the
; "winding function" method). ACL2 has no symbolic calculus and no
; theory of integration: it cannot evaluate those integrals, and
; faking a mechanical proof of that step would be misleading.
;
; This is deliberately left unmechanized here (omitting is preferred
; over simulating a proof that is not one). The only part of that
; section that IS mechanizable in plain ACL2 -- the product-to-sum
; trigonometric identity cos(A)cos(B) = 1/2[cos(A-B)+cos(A+B)] -- is a
; direct consequence of the angle-difference formulas already verified
; in 01-euler-identities.lisp (cosine-difference), and is not repeated
; here since it adds nothing beyond what is already proved there.
;
; A follow-up ACL2(r)-only attempt, 08-inductance-integral.lisp, goes
; further: it certifies the same product-to-sum identity in ACL2(r)'s
; acl2-cosine/acl2-sine, confirms it matches the antiderivative's
; algebraic shape, and machine-derives (via an automatic differentiator)
; the raw derivative fact for the antiderivative's oscillating term --
; but does not complete the integral itself. See that book's header
; for exactly how far it got and where it stopped.
;
; The manual (non-mechanical) verification of this section, including
; the cross-check L_k/M = (1+sigma_k) N_k/N_{k+1} against Leonhard's
; classical scalar result, is not reported here.

(in-package "ACL2")
