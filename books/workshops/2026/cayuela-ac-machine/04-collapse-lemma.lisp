; 04-collapse-lemma.lisp
;
; Verifies the "three-phase collapse lemma" of Section III.H
; (equations 33-35), the most substantial proof the paper adds
; relative to the original: for any vector A constant in n,
; sum_{n=0}^{2} (2/3)(A . e^{jn gamma}) e^{jn gamma} = A.
; Also verifies the phase-shift identity (image 62) used to apply the
; lemma to the MUTUAL term of the flux linkage.

(in-package "ACL2")
(include-book "02-roots-of-unity")
(include-book "01-euler-identities")

; --- Collapse lemma (images 56-60), general version for A=(ra,ia).
;     REAL/RATIONALP (not RATIONALP) so that the hypotheses are satisfiable in
;     ACL2(r) by s3 = sqrt(3); in plain ACL2 REAL/RATIONALP = RATIONALP. ---
(defthm eq33-35-three-phase-collapse-lemma
  (implies (and (real/rationalp ra) (real/rationalp ia) (real/rationalp s3)
                (equal (* s3 s3) 3))
           (equal (cadd (cscale (* 2/3 (dotp (cplx ra ia) (e0))) (e0))
                  (cadd (cscale (* 2/3 (dotp (cplx ra ia) (e1 s3))) (e1 s3))
                        (cscale (* 2/3 (dotp (cplx ra ia) (e2 s3))) (e2 s3))))
                  (cplx ra ia)))
  :hints (("Goal" :nonlinearp t)))

; --- Phase-shift identity (image 62), applied to the mutual term
;     with B=i_{k+1}(t), phi=(-1)^k eps(t):
;     B . e^{j(n gamma - phi)} = (B e^{j phi}) . e^{j n gamma}.
;     Does not require the Pythagorean identity for cos/sin: it is
;     pure algebra from the angle-difference formulas (verified
;     explicitly: both sides reduce, without using cos^2+sin^2=1, to
;     the same combination cos(n gamma)[p cos(phi)-q sin(phi)] +
;     sin(n gamma)[p sin(phi)+q cos(phi)]). ---
(defthm eq-mutual-phase-shift
  (implies (and (real/rationalp p) (real/rationalp q)
                (acl2-numberp x) (acl2-numberp phi))
           (equal (dotp (cplx p q) (eiz (- x phi)))
                  (dotp (cmul (cplx p q) (eiz phi)) (eiz x))))
  :hints (("Goal" :use ((:instance cosine-difference (x x) (y phi))
                        (:instance sine-difference (x x) (y phi))))))
