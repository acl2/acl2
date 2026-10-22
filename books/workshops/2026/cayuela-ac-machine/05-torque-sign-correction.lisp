; 05-torque-sign-correction.lisp
;
; Verifies the derivation chain of Section III.K (equations 40-46):
; the sign correction of the exponent in the motor torque equation.
; This is the highest-risk part of the paper: it claims the original
; text carried e^{-j eps(t)} and that the correct derivation from
; Leonhard's own starting equation (40) gives e^{+j eps(t)}.
;
; Here W(t) := i_S(t) i_R*(t) e^{-j eps(t)} is fixed EXACTLY as in
; (41)-(42) of the paper (that is the "given input" taken from
; Leonhard, not something derived here), and the rest of the chain --
; up to obtaining the + sign in the argument of the cross product --
; is verified to be a correct algebraic consequence. This does NOT
; verify that (40)/(41) are faithful to Leonhard's book (no access to
; the book is available here); it only verifies that everything
; derived FROM (41) in the paper is correct.

(in-package "ACL2")
(include-book "00-complex-vectors")
(include-book "01-euler-identities")
(include-book "02-roots-of-unity")

; W = i_S * conj(i_R * E),  E = e^{j eps}  =>  W = i_S i_R* e^{-j eps}
(defun torque-W (i-s i-r eps)
  (declare (xargs :guard (and (cplxp i-s) (cplxp i-r))))
  (cmul i-s (cconj (cmul i-r (eiz eps)))))

; --- W* = i_S* i_R e^{+j eps}  (given explicitly in the paper) ---
(defthm eq-W-conjugate
  (equal (cconj (torque-W i-s i-r eps))
         (cmul (cconj i-s) (cmul i-r (eiz eps)))))

; --- (W - W*)/(2j) = Im(W), general identity reused from (8)-(9) ---
(defthm eq-w-minus-wconj-is-2j-im
  (and (equal (re (csub w (cconj w))) 0)
       (equal (imz (csub w (cconj w))) (* 2 (imz w)))))

; --- Definitional check AB* = W (image 74, with the "checkmark") ---
(defthm eq-ab-star-is-w
  (equal (cmul i-s (cconj (cmul i-r (eiz eps))))
         (torque-W i-s i-r eps)))

; --- Applying (9): Im(W) = Im(AB*) = A x B, with A=i_S, B=i_R e^{j eps} ---
(defthm eq-im-w-is-crossp
  (equal (imz (torque-W i-s i-r eps))
         (crossp i-s (cmul i-r (eiz eps))))
  :hints (("Goal" :in-theory (e/d (torque-w) (eq-ab-star-is-w)))))

; --- Final result: the argument that survives inside the cross
;     product is i_R(t) rotated by +eps(t), i.e. the correct exponent
;     is +eps(t), not -eps(t) as in the original text. This
;     reproduces exactly (43)/(46) of the paper. ---
(defthm torque-exponent-sign-is-plus
  (equal (imz (torque-W i-s i-r eps))
         (crossp i-s (cmul i-r (eiz eps))))
  :hints (("Goal" :use eq-im-w-is-crossp :in-theory nil))
  :rule-classes nil)

; --- The sign correction is not vacuous: for concrete values, using
;     the exponent -eps instead of +eps changes the result. e1(s3) =
;     e^{j gamma} stands in for "+eps" and its conjugate e2(s3) =
;     e^{-j gamma} for the alternative "-eps", with i_S=(1,1),
;     i_R=(1,0).
;     REAL/RATIONALP (not RATIONALP): satisfiable in ACL2(r) by s3 = sqrt(3). ---
(defthm sign-matters-nonvacuous
  (implies (and (real/rationalp s3) (equal (* s3 s3) 3))
           (not (equal (crossp (cplx 1 1) (cmul (cplx 1 0) (e1 s3)))
                       (crossp (cplx 1 1) (cmul (cplx 1 0) (e2 s3))))))
  :hints (("Goal" :nonlinearp t)))
