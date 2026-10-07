; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  It illustrates a soundness bug fixed before ACL2
; Version 8.8.  Here is what Claude said about this file in 9/2026:

; "axioms.lisp:13342: (length (cdr l)) should be (length l) — latent since 8.4"
;   [and:]
; "compress1 in-order path miscounts num → aset1 skips a mandated recompression"

(in-package "ACL2")

(defconst *h* '((:header :dimensions (1) :maximum-length 2 :default 0)))
(defconst *a0* (compress1 'a *h*))
(defconst *a1* (aset1 'a *a0* 0 1))

(defthm aset1-car-lemma
  (implies (and (equal (array-order (header name (cons (cons n val) l))) '<)
                (> (length (cons (cons n val) l))
                   (maximum-length name (cons (cons n val) l))))
           (equal (car (aset1 name l n val))
                  (header name (cons (cons n val) l))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable aset1 compress1))))

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(defthm nil-proved
  nil
  :rule-classes nil
  :hints (("Goal" :use (:instance aset1-car-lemma
                                  (name 'a) (l *a1*) (n 0) (val 5)))))
)
