; Number Theory Library
; Quadratic Residue
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)
;
; NOTE: DRAFT

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PRIMES")

(include-book "arithmetic-3/floor-mod/mod-expt-fast" :dir :system)
(include-book "kestrel/prime-fields/top" :dir :system)

(include-book "euler2-support")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate ()
  (local (include-book "arithmetic-3/top" :dir :system))

  (defun has-square-root? (a p)
    (declare (xargs :guard (and (natp a) (natp p) (< 2 p) (< a p) (oddp p))))
    (if (not (and (natp a) (natp p) (< 2 p) (< a p) (oddp p)))
        nil
      (equal (acl2::mod-expt-fast a (/ (- p 1) 2) p)
             1)))
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Show that if (has-square-root? x) is NIL,
;; there is no y such that (mul y y p) equals x.


;; ----------------
;; 1. note that
;; (acl2::mod-expt-fast m (/ (- p 1) 2) p)
;; = (mod (expt m (/ (1- p) 2)) p)
;; in :logic mode.

#||
(defthm mod-expt-fast-instance-meaning
  (implies (and (rtl::primep p)
                (fep m p))
           (equal (acl2::mod-expt-fast m (/ (- p 1) 2) p)
                  (mod (expt m (/ (1- p) 2)) p)))
  :hints (("Goal" :in-theory (enable acl2::mod-expt-fast))))
||#

;; ----------------
;; 2. prove that (not (has-square-root? m p)) implies (not (rtl::residue m p))
;; See rtl::euler-criterion
;; [NOTE: what I really want in the consequent is a more general
;;   (equal (rtl::residue m p) (has-square-root? m p))
;;  so that I can use this to rewrite rtl::residue into has-square-root? which
;;  is faster.]

(defthm residue-meaning
  (implies (and (rtl::primep p)
                (not (= p 2))
                (oddp p)
                (fep m p)
                (not (equal 0 m))
                ;(not (rtl::divides p m))
                ) ; I would like a thm that fep implies this
           (equal (rtl::residue m p)
                  (has-square-root? m p)))
  :hints (("Goal" :in-theory (enable has-square-root? acl2::mod-expt-fast)
                  :use ((:instance rtl::euler-criterion-2a (acl2::p p) (acl2::m m))
                        (:instance rtl::euler-criterion-2b (acl2::p p) (acl2::m
                                                                       m))))))

(defthmd residue-meaning-backwards
  (implies (and (rtl::primep p)
                (not (= p 2))
                (oddp p)
                (fep m p)
                (not (equal 0 m))
                ;(not (rtl::divides p m))
                ) ; I would like a thm that fep implies this
           (equal (has-square-root? m p)
                  (rtl::residue m p))))

(theory-invariant (incompatible (:rewrite residue-meaning) (:rewrite residue-meaning-backwards)))


;; (has-square-root? ..) is defined to be (equal (acl2::mod-expt-fast ..) 1)
;; We can use something like rtl::euler-criterion-2a


#||
;; Something like this should be adequate for proving no-square-root-forall
(defthm residue-meaning
  (implies (and (rtl::primep p)
                (> p 2)
                (fep m p)
                (not (has-square-root? m p)))
           (not (rtl::residue m p)))
  :hints (("Goal" :in-theory (enable rtl::euler-criterion-2a has-square-root?)))
  )
||#


;; 3. Prove if some x doesn't have a square root, it means y*y is never
;; equal to x.
;; See rtl::not-res-no-root

#||
(defthm no-square-root-forall
  (implies (and (primep p)
                (fep x p) (fep y p)
                (not (has-square-root? x p)))
           (equal (equal x (mul y y p)) nil)))
||#


(defthm no-square-root-forall
  (implies (and (not (has-square-root? x p)) ; conjunct ordering
                (natp p)
                (not (equal p 2))
                (oddp p)
                (fep x p)
                (fep y p)
                (rtl::primep p))
           (equal (equal x (mul y y p))
                  (if (equal x 0) ; it is good we negated and moved (not (= x 0)) into the conclusion since it made the rule more general
                      (equal 0 (mul y y p))
                    nil))
   ;        (not (equal x (mul y y p)))
           )
  :hints (("Goal" :in-theory (e/d (residue-meaning-backwards mul) (residue-meaning
                                                               has-square-root?))
                  :use ((:instance rtl::not-res-no-root (acl2::p p) (acl2::m x)
  (acl2::j y)))))
  )
