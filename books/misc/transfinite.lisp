(in-package "ACL2")

;; Transfinite induction (a.k.a. ordinal induction) in ACL2.
;; See http://www.mtnmath.com/whatrh/node52.html for a discussion of ordinal induction.

;; Thanks to Matt Kaufmann and Pete Manolios for enlightening discussions.
;; The proof below was sketched out by Matt; I basically just typed it
;; up. --Eric Smith

;; Should this be added to the ordinals books?
(defun o-fix (x)
  (if (o-p x)
      x
    0))

(encapsulate
 (((transfinite-induction-predicate *) => *))
 (local (defun transfinite-induction-predicate (x) (declare (ignore x)) t))

 ;;We don't need a base case [e.g., one asserting
 ;;(transfinite-induction-predicate 0)], since it would be subsumed by
 ;;pred-when-pred-for-smaller below.

 ;; It's gross that this is in the encapsulate, but I need it to express the constraint:
 (defun-sk pred-for-all-ordinals-smaller-than (alpha)
   (forall (x) (implies (and (o-p x)
                             (o< x alpha))
                        (transfinite-induction-predicate x))))

 ;; The constraint on pred:
 (defthm pred-when-pred-for-smaller
   (implies (and (o-p alpha)
                 (pred-for-all-ordinals-smaller-than alpha))
            (transfinite-induction-predicate alpha))))

;; This function suggests the induction scheme. The clever idea of recurring
;; on the witness of the defun-sk is due to Matt Kaufmann. It turns out that
;; we can show the witness is smaller than x if we're not in the base case.

(local
 (defun transfinite-induction-scheme (x)
   (declare (xargs :measure (o-fix x)))
   (if (or (not (o-p x))
           (transfinite-induction-predicate x) ;putting this in the base case seems clever
           )
       x
     (transfinite-induction-scheme (pred-for-all-ordinals-smaller-than-witness x)))))

;; The main theorem:
(defthm pred-for-all-ordinals
  (implies (o-p y)
           (transfinite-induction-predicate y))
  :hints (("Goal" :induct (transfinite-induction-scheme y))))





;; Now try it out...
(local
 (encapsulate
  ()

  (defun foo (x) (declare (ignore x)) t)

  ;;We'll keep foo shut off to keep the proof from being trivial.
  (in-theory (disable foo (:type-prescription foo) (:executable-counterpart foo)))

  (defun-sk foo-for-all-ordinals-smaller-than (alpha)
    (forall (x) (implies (and (o-p x)
                              (o< x alpha))
                         (foo x))))

  (defthm foo-when-foo-for-smaller
    (implies (and (o-p alpha)
                  (foo-for-all-ordinals-smaller-than alpha))
             (foo alpha))
    :hints (("Goal" :in-theory (enable foo)))) ;this is the only place where we open up foo

  ;; Is sure would be nice if the defun-sk would just phrase
  ;; foo-for-all-ordinals-smaller-than-necc this way...  The way it currently
  ;; gets phrased is with the hypothesis as an implies, and it fails to fire
  ;; due to free variables.
  (defthm foo-for-all-ordinals-smaller-than-necc-better
    (implies (and (o-p x)
                  (o< x alpha)
                  (not (foo x)))
             (not (foo-for-all-ordinals-smaller-than alpha)))
    :hints (("Goal" :in-theory (disable FOO-FOR-ALL-ORDINALS-SMALLER-THAN-NECC)
             :use (:instance FOO-FOR-ALL-ORDINALS-SMALLER-THAN-NECC))))

  ;; Yep, it works!
  (defthm foo-for-all-ordinals
    (implies (o-p y)
             (foo y))
    :hints (("Goal" :do-not '(generalize eliminate-destructors)
             :use (:instance (:functional-instance pred-for-all-ordinals
                                                   (transfinite-induction-predicate foo)
                                                   (pred-for-all-ordinals-smaller-than-witness foo-for-all-ordinals-smaller-than-witness)
                                                   (pred-for-all-ordinals-smaller-than foo-for-all-ordinals-smaller-than)
                                                   )))))))

