;;  
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")
(include-book "coi/types/types" :dir :system)
(include-book "coi/util/linear" :dir :system)
(include-book "coi/pattern-hint/pattern-hint" :dir :system)
(include-book "coi/util/defun" :dir :system)
(include-book "coi/util/good-rewrite-order" :dir :system)
(include-book "coi/util/pseudo-translate" :dir :system)
(include-book "coi/util/skip-rewrite" :dir :system)
(include-book "tools/without-subsumption" :dir :system)
(include-book "coi/util/in-conclusion" :dir :system)
(include-book "coi/quantification/quantified-congruence" :dir :system)
(include-book "misc/priorities" :dir :system)

(in-theory (disable DEFAULT-+-2 DEFAULT-+-1 DEFAULT-<-1 DEFAULT-<-2 DEFAULT-*-1 DEFAULT-*-2))

(defmacro phased-rewrite-hint ()
  `(PRIORITY-PHASED-SIMPLIFICATION WORLD STABLE-UNDER-SIMPLIFICATIONP 0))

(defmacro include-arithmetic ()
  `(progn
     (include-book "arithmetic-5/top" :dir :system)
     (in-theory (disable DEFAULT-PLUS-2
                         |(* -1 x)|
                         NOT-INTEGERP-4A
                         SIMPLIFY-SUMS-<))
     ))

(defmacro with-arithmetic (&rest args)
  `(encapsulate
       ()
     (local (include-book "arithmetic-5/top" :dir :system))
     (local (in-theory (disable DEFAULT-PLUS-2
                                |(* -1 x)|
                                NOT-INTEGERP-4A
                                SIMPLIFY-SUMS-<)))
     ,@args
     ))

(defthm stengthen-integer-linear-lower
  (implies
   (and
    (syntaxp (quotep c))
    (in-conclusion-check (< c a) :top t)
    (integerp c)
    (integerp a)
    (equal z (+ c 1)))
   (iff (< c a)
        (<= z a))))

(defthm stengthen-integer-linear-lower-N
  (implies
   (and
    (syntaxp (equal a '(N)))
    (in-conclusion-check (< c a) :top t)
    (integerp c)
    (integerp a)
    (equal z (+ c 1)))
   (iff (< c a)
        (<= z a))))

(defthm stengthen-integer-linear-upper
  (implies
   (and
    (syntaxp (quotep c))
    (in-conclusion-check (< a c) :top t)
    (integerp c)
    (integerp a)
    (equal z (1- c)))
   (iff (< a c)
        (<= a z))))

;; This is just a little trick we use to help hang on to
;; variable instances that might otherwise get rewritten
;; away during ACL2 proofs.
(defun always-true (x)
  (declare (ignore x))
  t)

(defun expand-lte-match-domain (x y)
  (declare (xargs :guard t))
  (list (list x y)
        (list `(quote 0) x)
        (list `(quote 0) y)
        (list x '(N))
        (list y '(N))))

(defun default-lte-match-domain ()
  (declare (xargs :guard t))
  (list (list `(quote 0) '(N))))

(def::signature default-lte-match-domain () true-listp)
(def::signature expand-lte-match-domain (t t) true-listp)

(in-theory (disable expand-lte-match-domain))
(in-theory (disable default-lte-match-domain (default-lte-match-domain)))

(def::type rat (x)
  :type-witness (rfix x)
  :and (rational))

(def::type nnrat (x)
  :body (and (rationalp x) (<= 0 x))
  :type-witness 0)

(def::type sign (x)
  :body (or (equal x 1) (equal x -1))
  :refines (int)
  :type-witness 1)

(defthm sign-p-negation
  (implies
   (sign-p x)
   (sign-p (- x)))
  :hints (("Goal" :in-theory (enable sign-p))))

(def::un snot (x)
  (declare (xargs :signature ((sign-p) sign-p)))
  (- x))

;; -------------------------------------------------------------------
;;
;; Here we introduce an encapsulated function that represents the
;; total number of UAVs in the ensemble.
;;
;; -------------------------------------------------------------------

(encapsulate
    (
     ((N) => *)
     )
  
  (local (defun N () 1))
  
  (defthm positive-count
    (posp (N))
    :rule-classes ((:type-prescription)))

  )

(defthm force-rewrite-N-constant-1
  (implies
   (and
    (syntaxp (and (quotep c1) (quotep c2)))
    (in-conclusion-check (equal (+ c1 (N)) c2) :top t)
    (integerp c1)
    (integerp c2)
    (equal c3 (- c2 c1)))
   (iff (equal (+ c1 (N)) c2)
        (hide (rewrite-equiv (equal (N) c3)))))
  :hints ('(:expand (:free (x) (hide x)))))

(defthm force-rewrite-N-constant-2
  (implies
   (and
    (syntaxp (and (quotep c1) (quotep c2)))
    (in-conclusion-check (equal c2 (+ c1 (N))) :top t)
    (integerp c1)
    (integerp c2)
    (equal c3 (- c2 c1)))
   (iff (equal c2 (+ c1 (N)))
        (hide (rewrite-equiv (equal (N) c3)))))
  :hints ('(:expand (:free (x) (hide x)))))

(defthm equal-double-containment-1
  (implies
   (and
    (syntaxp (and (quotep c1) (quotep c2)))
    (in-conclusion-check (EQUAL (+ c1 (N)) c2) :top :negated)
    (integerp c1)
    (integerp c2)
    (equal c3 (- c2 c1)))
   (iff (EQUAL (+ c1 (N)) c2)
        (and (<= (N) c3)
             (<= c3 (N))))))

(defthm equal-double-containment-2
  (implies
   (and
    (syntaxp (and (quotep c1) (quotep c2)))
    (in-conclusion-check (EQUAL c2 (+ c1 (N))) :top :negated)
    (integerp c1)
    (integerp c2)
    (equal c3 (- c2 c1)))
   (iff (EQUAL c2 (+ c1 (N)))
        (and (<= (N) c3)
             (<= c3 (N))))))

(defthm posp-N
  (<= 1 (N))
  :rule-classes (:linear))

(defun N-exec ()
  (declare (xargs :guard t))
  100)

(defattach N N-exec)

;; -------------------------------------------------------------------
;;
;; A UAV identifier (UAV-ID) is a natural number between 0 and the
;; total number of UAVs in the ensemble, (N).
;;
;; -------------------------------------------------------------------

(def::type UAV-ID (id)
  :body (and (natp id) (< id (N)))
  :non-executable t
  :type-witness 0
  :open-fix-default t
  )

(defthm weak-UAV-ID-FIX-UAV-ID-P
  (implies
   (uav-id-p x)
   (equal (uav-id-fix x) x))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm natp-uav-id-fix
  (natp (uav-id-fix x))
  :rule-classes :type-prescription)

(defthm fix-max-index
  (equal (uav-id-fix (+ -1 (N)))
         (+ -1 (N))))

(defthm open-uav-id-p-sum
  (implies
   (and
    (integerp c)
    (integerp x))
   (iff (uav-id-p (+ c x))
        (and (<= 0 (+ c x))
             (< (+ c x) (N))))))

(defthm uav-id-fix-constant
  (implies
   (syntaxp (quotep x))
   (equal (uav-id-fix x)
          (if (and (natp x)
                   (< x (N)))
              x
            0))))

(defthm uav-id-p-constant
  (implies
   (syntaxp (quotep x))
   (equal (uav-id-p x)
          (and (natp x)
               (< x (N)))))
  :hints (("Goal" :in-theory (enable uav-id-p))))

(encapsulate
    ()

  ;;(local (in-theory (disable EQUAL-UAV-ID-FIX-1-TO-UAV-ID-EQUIV)))

  (defthm denerate-equal-n-n-1
    (iff (uav-id-equiv (N) (+ -1 (N)))
         (equal (N) 1))
    :hints (("goal" :in-theory (enable uav-id-equiv
                                       uav-id-fix
                                       uav-id-p))))
  
  (defthm degenerate-fix-N
    (equal (uav-id-fix (N)) 0)
    :hints (("Goal" :in-theory (enable uav-id-fix))))
  
  (defthm degenerate-equiv--3--1
    (iff (UAV-ID-EQUIV (+ -3 (N)) (+ -1 (N)))
         (equal (N) 1))
    :hints (("GOal" :do-not '(preprocess)
             :in-theory (e/d (UAV-ID-FIX uav-id-equiv)
                             #+joe
                             (PLUS-EQUAL-N-TO-EQUIV-N-MINUS-1)))))
  
  (defthm degenerate-equal-n-to-uav-id-equiv
    (iff (equal (+ 2 (uav-id-fix i)) (N))
         (if (equal (n) 1) nil
           (uav-id-equiv i (+ (N) (- 2)))))
    :hints (("Goal" :do-not '(preprocess)
             :in-theory (enable uav-id-equiv
                                uav-id-fix
                                uav-id-p))))
  
  (defthm degenerate-equiv-plus-1-zero
    (implies
     (uav-id-p i)
     (iff (UAV-ID-EQUIV (+ 1 I) 0)
          (uav-id-equiv I (+ -1 (n)))))
    :hints (("Goal" :do-not '(preprocess)
             :in-theory (enable uav-id-equiv
                                uav-id-fix
                                uav-id-p))))
  
  (defthm degenerate-equiv-4-0
    (iff (uav-id-equiv 4 0)
         (or (equal (N) 1)
             (equal (N) 2)
             (equal (N) 3)
             (equal (N) 4)))
    :hints (("Goal" :do-not '(preprocess)
             :in-theory (enable uav-id-equiv
                                uav-id-fix
                                uav-id-p))))
  
  (defthm degenerate-equiv-3-0
    (iff (uav-id-equiv 3 0)
         (or (equal (N) 1)
             (equal (N) 2)
             (equal (N) 3)))
    :hints (("Goal" :do-not '(preprocess)
             :in-theory (enable uav-id-equiv
                                uav-id-fix
                                uav-id-p))))
  
  (defthm degenerate-equiv-2-0
    (iff (uav-id-equiv 2 0)
         (or (equal (N) 1)
             (equal (N) 2)))
    :hints (("Goal" :do-not '(preprocess)
             :in-theory (enable uav-id-equiv
                                uav-id-fix
                                uav-id-p))))
  
  (defthm degenerate-equiv-1-0
    (iff (uav-id-equiv 1 0)
         (equal (N) 1))
    :hints (("Goal" :do-not '(preprocess)
             :in-theory (enable uav-id-equiv
                                uav-id-fix
                                uav-id-p))))
  
  (defthm degenerate-equiv-0-1
    (iff (uav-id-equiv 0 1)
         (equal (N) 1))
    :hints (("Goal" :do-not '(preprocess)
             :in-theory (enable uav-id-equiv
                                uav-id-fix
                                uav-id-p))))
  
  (defthm degenerate-equiv-1-N-1
    (iff (uav-id-equiv 1 (+ -1 (N)))
         (or (equal (N) 1)
             (equal (N) 2)))
    :hints (("Goal" :do-not '(preprocess)
             :in-theory (enable uav-id-equiv
                                uav-id-fix
                                uav-id-p))))
  
  (defthm degenerate-equiv-n-1-0
    (iff (UAV-ID-EQUIV (+ -1 (N)) 0)
         (equal (N) 1))
    :hints (("Goal" :do-not '(preprocess)
             :in-theory (enable uav-id-equiv
                                uav-id-fix
                                uav-id-p))))
  
  (defthm degenerate-add-to-uav-id-fix
    (implies
     (<= 3 (N))
     (uav-id-equiv (+ 1 (UAV-ID-FIX (+ -2 (N))))
                   (+ -1 (N))))
    :hints (("Goal" :do-not '(preprocess)
             :in-theory (enable natp
                                uav-id-fix
                                uav-id-equiv
                                uav-id-p))))
  
  (defthm degenerate-gamme-1
    (implies
     (<= 2 (N))
     (iff (UAV-ID-EQUIV (+ -2 (N)) 0)
          (equal (N) 2)))
    :hints (("Goal" :do-not '(preprocess)
             :in-theory (enable uav-id-equiv
                                uav-id-p
                                uav-id-fix))))

  )
  
(defthm equal-to-uav-id-equiv-1
  (iff (equal (+ -1 (uav-id-fix x)) 0)
       (if (equal (N) 1) nil
         (uav-id-equiv x 1)))
  :hints (("Goal" :in-theory (e/d (uav-id-equiv
                                   uav-id-fix
                                   uav-id-p)
                                  nil))))

(defthmd force-UAV-ID-EQUIV-rewrite-symbol
  (implies
   (and
    (syntaxp (symbolp j))
    (in-conclusion-check (UAV-ID-EQUIV J k) :top t))
   (iff (UAV-ID-EQUIV J k)
        (hide (rewrite-equiv (UAV-ID-EQUIV J k)))))
  :hints (("Goal" :expand (:free (x) (hide x)))))

(defthm not-uav-id-p-from-not-acl2-numberp
  (implies
   (not (acl2-numberp i))
   (not (uav-id-p i)))
  :rule-classes (:type-prescription))

(defthm uav-id-equiv-to-double-containment
  (implies
   (in-conclusion-check (uav-id-equiv j i) :top :negated)
   (iff (uav-id-equiv j i)
        (and (<= (uav-id-fix i) (uav-id-fix j))
             (<= (uav-id-fix j) (uav-id-fix i)))))
  :hints (("Goal" :in-theory (e/d (uav-id-equiv)
                                  ))))

(defthm acl2-numberp-uav-id-fix
  (acl2-numberp (uav-id-fix x))
  :rule-classes (:type-prescription))

(defthm linear-bounds-on-uav-id-fix
  (and (<= 0 (uav-id-fix x))
       (< (uav-id-fix x) (N)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable uav-id-fix
                                     uav-id-p))))

(defthm <-c-uav-id-fix-rewrite-0
  (implies
   (and
    (integerp c)
    (< c 0))
   (< c (uav-id-fix x))))

(defthm <-uav-id-fix-N-rewrite-1
  (implies
   (and
    (integerp c)
    (<= c 0))
   (< (+ c (uav-id-fix x)) (N))))

(defthm <-uav-id-fix-N-rewrite-2
  (implies
   (and
    (integerp c)
    (<= 0 c))
   (< (uav-id-fix x) (+ c (N)))))

;; DAG -- I don't like this rule ..
(defthm not-equal-into-inequality-1
  (implies
   (and
    (in-conclusion-check (equal (+ -1 (uav-id-fix x)) 0) :top :negated)
    (< 0 (uav-id-fix x)))
   (iff (equal (+ -1 (uav-id-fix x)) 0)
        (not (<= 2 (uav-id-fix x)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable uav-id-equiv
                              uav-id-fix
                              uav-id-p))))


(in-theory (disable (UAV-ID-EQUIV)))

(defthmd equal-uav-id-fix-constant
  (implies
   (and
    (in-conclusion)
    (syntaxp (quotep a))
    (uav-id-p a))
   (equal (equal (uav-id-fix x) a)
          (uav-id-equiv x a))))

(defthm not-uav-id-p-n
  (not (uav-id-p (N))))

(defthmd equal-uav-id-fix-1-to-uav-id-equiv
  (implies
   (in-conclusion)
   (equal (equal (uav-id-fix x) y)
          (and (uav-id-p y)
               (uav-id-equiv x y))))
  :hints (("GOal" :do-not '(preprocess)
           :in-theory (enable uav-id-equiv
                              uav-id-fix))))

(theory-invariant (incompatible (:definition uav-id-equiv)
                                (:rewrite equal-uav-id-fix-1-to-uav-id-equiv)))

(defthmd single-uav-perimeter-id-equiv-0
  (implies
   (equal 1 (N))
   (iff (uav-id-equiv x 0) t))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints (("GOal" :do-not '(preprocess)
           :in-theory (enable uav-id-equiv uav-id-fix uav-id-p))))

(add-priority 1 single-uav-perimeter-id-equiv-0)

(defthmd force-uav-id-equiv-rewrite
  (implies
   (in-conclusion-check (uav-id-equiv id1 id2) :top t)
   (iff (uav-id-equiv id1 id2)
        (hide (rewrite-equiv (uav-id-equiv id1 id2)))))
  :hints (("Goal" :expand (:free (x) (hide x)))))

(defthm equal-plus-1-implication
  (and (iff (uav-id-equiv x (+ 1 (uav-id-fix x)))
            (equal (N) 1))
       (iff (uav-id-equiv (+ 1 (uav-id-fix x)) x)
            (equal (N) 1)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable uav-id-equiv uav-id-fix uav-id-p))))

(defthm plus-equal-n-to-equiv-n-minus-1
  (implies
   (in-conclusion)
   (iff (equal (+ 1 (uav-id-fix x)) (n))
        (uav-id-equiv x (- (n) 1))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable uav-id-fix uav-id-equiv uav-id-p))))

(defthm reduce-uav-id-equiv
  (iff (uav-id-equiv x (+ -1 (uav-id-fix x)))
       (uav-id-equiv x 0))
  ;; (<= (N) 1))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable uav-id-equiv
                              uav-id-fix
                              uav-id-p))))

(defthm reduce-uav-id-equiv-2
  (iff (uav-id-equiv x (+ 1 (uav-id-fix x)))
       (and (equal (N) 1)
            (uav-id-equiv x 0)))
  ;; (<= (N) 1))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable uav-id-equiv
                              uav-id-fix
                              uav-id-p))))

(defthm reduce-uav-id-equiv-3
  (iff (uav-id-equiv 0 (+ 1 (uav-id-fix x)))
       (equal (+ 1 (uav-id-fix x)) (N)))
  ;; (<= (N) 1))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable uav-id-equiv
                              uav-id-fix
                              uav-id-p))))

(defthm uav-id-p-1
  (iff (uav-id-p 1)
       (< 1 (N)))
  :hints (("GOal" :in-theory (enable uav-id-p))))

(defthm uav-id-p-plus-c
  (implies
   (and (uav-id-p id) (natp c))
   (iff (uav-id-p (+ c id))
        (< (+ c id) (N))))
  :hints (("GOal" :in-theory (enable uav-id-p))))

(defthm not-uav-id-p-is-zero
  (implies
   (NOT (UAV-ID-P x))
   (uav-id-equiv x 0))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable uav-id-equiv
                              uav-id-fix)))
  :rule-classes (:forward-chaining))

(defthm uav-id-fix-plus
  (implies (and (syntaxp (quotep c))
                (integerp c)
                (integerp id))
           (equal (uav-id-fix (+ c id))
                  (if (< (+ c id) 0)
                      0 (if (<= (n) (+ c id)) 0 (+ c id)))))
  :hints (("goal" :in-theory (enable uav-id-p uav-id-fix))))

(defthm iff-uav-id-equiv-zero
  (iff (uav-id-equiv 0 (+ -1 (N)))
       (equal (N) 1))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable uav-id-equiv uav-id-fix uav-id-p))))

(defthm normalize-uav-id-equiv-plus-fix
  (implies
   (and (integerp c)
        (case-split
         (and (uav-id-p y)
              (uav-id-p (+ c (uav-id-fix x)))
              (uav-id-p (+ (- c) y)))))
   (iff (uav-id-equiv (+ c (uav-id-fix x)) y)
        (uav-id-equiv x (+ (- c) y))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable uav-id-equiv uav-id-fix uav-id-p))))

(defthm impossible-scenario
  (iff (UAV-ID-EQUIV (+ -1 (UAV-ID-FIX I))
                     (+ -1 (N)))
       (and (equal (N) 1)
            (uav-id-equiv i 0)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable uav-id-equiv uav-id-fix uav-id-p))))

(defthm helper-rule
  (implies
   (< (UAV-ID-FIX i)
      (UAV-ID-FIX j))
   (and (< (1+ (uav-id-fix i)) (N))
        (< 0 (uav-id-fix j))))
  :hints (("GOal" :in-theory (enable uav-id-fix))))

(defthm not-1-n-3
  (implies
   (NOT (UAV-ID-EQUIV I 0))
   (< 1 (n)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable uav-id-equiv
                              uav-id-fix)))
  :rule-classes (:forward-chaining))

(defthm uav-id-equiv-different-offsets
  (implies
   (integerp x)
   (iff (uav-id-equiv (+ -2 x) (+ -1 x))
        (or (equal (n) 1)
            (<= (N) (+ -2 x))
            (<= x 1))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable uav-id-p
                              uav-id-equiv
                              uav-id-fix))))

(defthm less-than-zero-to-uav-id-equiv
  (implies
   (in-conclusion-check (< (+ -1 (UAV-ID-FIX I)) 0) :top t)
   (iff (< (+ -1 (UAV-ID-FIX I)) 0)
        (uav-id-equiv i 0)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable uav-id-equiv
                              uav-id-fix
                              uav-id-p))))

(in-theory (disable BODY-IMPLIES-UAV-ID-P
                    UAV-ID-FIX-UAV-ID-P))

(in-theory (enable equal-uav-id-fix-1-to-uav-id-equiv))

;; -------------------------------------------------------------------
;;
;; A UAV identifier (UAV-ID) is a natural number between 0 and the
;; total number of UAVs in the ensemble, (N).
;;
;; -------------------------------------------------------------------

(encapsulate
    (
     ((P) => *)
     )
  
  (local (defun P () 1))
  
  (defthm positive-rational-peremeter
    (and (rationalp (P))
         (< 0 (P)))
    :rule-classes ((:forward-chaining :trigger-terms ((P)))))

  )

(defun P-exec ()
  (declare (xargs :guard t))
  1000)

(defattach P P-exec)

;; -------------------------------------------------------------------
;;
;; We now introduce functions that describe the perimeter boundaries.
;;
;; -------------------------------------------------------------------

(def::und left-perimeter-boundary ()
  (declare (xargs :signature (() rationalp)))
  0)

(defthm left-perimeter-boundary-lower-bound
  (<= 0 (left-perimeter-boundary))
  :rule-classes (:linear))

(in-theory (disable (:type-prescription left-perimeter-boundary)))

(defthm left-perimeter-boundary-upper-bound
  (< (left-perimeter-boundary) (P))
  :hints (("Goal" :in-theory (enable left-perimeter-boundary)))
  :rule-classes (:linear))

(def::und right-perimeter-boundary ()
  (declare (xargs :signature (() rationalp)))
  (P))

(defthm right-perimeter-bound
  (<= (right-perimeter-boundary) (p))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable right-perimeter-boundary))))

(defthm right-perimeter-boundary-lower-bound
  (< 0 (right-perimeter-boundary))
  :hints (("Goal" :in-theory (enable right-perimeter-boundary)))
  :rule-classes (:linear))

(defthm perimeter-boundaries-are-distinct
  (< (left-perimeter-boundary)
     (right-perimeter-boundary))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable left-perimeter-boundary
                                     right-perimeter-boundary))))


;; -------------------------------------------------------------------
;;
;; The location of a UAV is rational number that is between the left
;; and the right boundaries of the perimeter.
;;
;; -------------------------------------------------------------------

(def::type-predicate uav-location-p (loc)
  :type-name uav-location
  :non-executable t
  :body (and (rationalp loc) (<= (left-perimeter-boundary) loc) (<= loc (right-perimeter-boundary)))
  )

(def::und uav-location-fix (loc)
  (declare (xargs :signature ((t) uav-location-p)))
  (let ((loc (rfix loc)))
    (if (< loc (left-perimeter-boundary))
        (left-perimeter-boundary)
      (if (< (right-perimeter-boundary) loc)
          (right-perimeter-boundary)
        loc))))

(def::type UAV-LOCATION (loc)
  :type-p uav-location-p
  :fix! uav-location-fix
  :fix-signature nil
  :prove-properties nil
  :fix-in-theory (enable uav-location-fix)
  :non-executable t
  )

;; I'm not sure where location-p is important (?)
;; DAG -> this illustrates the fighting between :forward-chaining and :type-prescription (!)
(in-theory (disable body-implies-uav-location-p))

;; DAG .. confounded again by :normalize t This is why I had trouble
;; getting rid of certain constants in the proof .. ACL2 was
;; simplifying some functions when they were admitted (!)


;; -------------------------------------------------------------------
;;
;; We now have the vocabulary necessary to describe a UAV instance.
;;
;; -------------------------------------------------------------------

(def::type-str UAV
 ((id        UAV-ID)
  (location  UAV-LOCATION)
  (direction sign)))

(defthm rationalp-location
  (rationalp (uav->location ens))
  :rule-classes (:type-prescription))

;;
;; I would really like to get rid of this.
;;
(in-theory (disable (UAV-fix) (uav)))
;;(in-theory (disable UAV->ID-OF-UAV-FIX-UAV-INSTANCE-NORMALIZE-CONST))
;;(in-theory (disable UAV->LOCATION-OF-UAV-FIX-UAV-INSTANCE-NORMALIZE-CONST))

(defthm acl2-numberp-uav->location
  (acl2-numberp (UAV->LOCATION uav))
  :rule-classes (:type-prescription))

(defthm acl2-numberp-uav->direction
  (acl2-numberp (UAV->direction uav))
  :rule-classes (:type-prescription))

(defthm negative-direction-to-not-one
  (equal (< (UAV->DIRECTION uav) 0)
         (equal (UAV->DIRECTION uav) -1)))

(defthm positive-to-one
  (equal (< 0 (UAV->DIRECTION uav))
         (equal (UAV->DIRECTION uav) 1)))

(defthm normalize-negation
  (implies
   (syntaxp (quotep c))
   (iff (equal (- (UAV->DIRECTION uav)) c)
        (equal (UAV->DIRECTION uav) (- c)))))

(defthm normalize-direction-direction
  (implies
   (and
    (in-conclusion)
    (syntaxp (quotep c)))
   (iff (equal c (UAV->DIRECTION uav))
        (skip-rewrite (equal (UAV->DIRECTION uav) c)))))

(defthmd negate-direction-equality
  (implies
   (syntaxp (any-p uav))
   (and (iff (equal (UAV->DIRECTION uav) 1)
             (not (equal (UAV->DIRECTION uav) -1)))
        (iff (equal 1 (UAV->DIRECTION uav))
             (not (equal (UAV->DIRECTION uav) -1))))))

(defthm negate-direction-equality-rewrite-0
  (implies
   (in-conclusion-check (equal (UAV->DIRECTION uav) -1) :top :negated)
   (iff (equal (UAV->DIRECTION uav) -1)
        (not (equal (UAV->DIRECTION uav) 1)))))

(defthm negate-direction-equality-rewrite-1
  (implies
   (in-conclusion-check (equal (UAV->DIRECTION uav) 1) :top :negated)
   (iff (equal (UAV->DIRECTION uav) 1)
        (not (equal (UAV->DIRECTION uav) -1)))))

(defthm less-than-direction
  (iff (< (uav->direction uavi)
          (uav->direction uavj))
       (and (equal (uav->direction uavi) -1)
            (equal (uav->direction uavj)  1))))

(defmacro update-uav (uav &key (id 'nil) (location 'nil) (direction 'nil))
  `(let ((id        ,(or id `(uav->id ,uav)))
         (location  ,(or location `(uav->location ,uav)))
         (direction ,(or direction `(uav->direction ,uav))))
     (uav id location direction)))

;; -------------------------------------------------------------------
;;
;; Each UAV is assigned a specific segment of the perimeter.  Here we
;; introduce the concepts of the left and right boundaries of each
;; UAVs segment.
;;
;; -------------------------------------------------------------------

(def::und segment-length ()
  (declare (xargs :signature (() rationalp)))
  (/ (P) (N)))

(defthm positive-segment-length
  (< 0 (segment-length))
  :rule-classes (:linear)
  :hints (("Goal" :in-theory (enable segment-length))))

(with-arithmetic
 (defthmd alt-right-perimeter
   (equal (RIGHT-PERIMETER-BOUNDARY)
          (* (N) (SEGMENT-LENGTH)))
   :hints (("Goal" :in-theory (enable RIGHT-PERIMETER-BOUNDARY
                                      SEGMENT-LENGTH)))))
 
(def::und UAV-left-boundary (x)
  (declare (xargs :signature ((t) uav-location-p)
                  :signature-hints (("Goal"
                                     :nonlinearp t
                                     :in-theory (enable 
                                                 LEFT-PERIMETER-BOUNDARY
                                                 alt-right-perimeter
                                                 uav-location-p)))
                  :congruence ((UAV-equiv) equal)
                  :guard (UAV-p x)))
  (* (UAV->id x) (segment-length)))

(def::und UAV-right-boundary (x)
  (declare (xargs :signature ((t) uav-location-p)
                  :signature-hints (("Goal" :cases ((< (UAV->ID X) (N)))
                                     :nonlinearp t
                                     :in-theory (enable UAV-LEFT-BOUNDARY
                                                        alt-right-perimeter
                                                        LEFT-PERIMETER-BOUNDARY
                                                        uav-location-p)))
                  :congruence ((UAV-equiv) equal)
                  :guard (UAV-p x)))
  (+ (UAV-left-boundary x) (segment-length)))

(defthm left-perimeter-boundary-lt-uav-right-boundary
  (< (LEFT-PERIMETER-BOUNDARY) (UAV-RIGHT-BOUNDARY uav))
  :hints (("GOal" :in-theory (enable UAV-RIGHT-BOUNDARY )))
  :rule-classes :linear)
  
(encapsulate
    ()

  (local (include-arithmetic))

  (defthm uav-0-right-perimeter-boundary-implication
    (implies
     (equal (uav->id uav) 0)
     (iff (EQUAL (RIGHT-PERIMETER-BOUNDARY)
                 (UAV-RIGHT-BOUNDARY uav))
          (equal (N) 1)))
    :hints (("Goal" :in-theory (enable alt-right-perimeter
                                       RIGHT-PERIMETER-BOUNDARY
                                       UAV-LEFT-BOUNDARY
                                       UAV-RIGHT-BOUNDARY
                                       ))))
          
  
  )

(encapsulate
    ()

  (local (include-arithmetic))

  (defthmd shared-boundary
    (iff (equal (UAV-right-boundary x)
                (UAV-left-boundary y))
         (equal (UAV->id y) (+ (UAV->id x) 1)))
    :hints (("Goal" :in-theory (enable SEGMENT-LENGTH UAV-left-boundary
                                       UAV-right-boundary))))
  (defthm equal-right-boundaries
    (iff (equal (UAV-right-boundary x)
                (UAV-right-boundary y))
         (equal (UAV->id y) (UAV->id x)))
    :hints (("Goal" :in-theory (enable SEGMENT-LENGTH UAV-left-boundary
                                       UAV-right-boundary))))

  )

(encapsulate
    ()

  (local (include-arithmetic))

  (defthm positive-boundaries
    (and ;;(<= 0 (UAV-LEFT-BOUNDARY uav))
         (< 0 (UAV-RIGHT-BOUNDARY uav)))
    :hints (("Goal" :in-theory (enable SEGMENT-LENGTH
                                       UAV-LEFT-BOUNDARY
                                       UAV-RIGHT-BOUNDARY)))
    :rule-classes (:linear))
  
  (defthm left-boundary-is-smaller
    (< (UAV-LEFT-BOUNDARY uav)
       (UAV-RIGHT-BOUNDARY uav))
    :hints (("Goal" :in-theory (enable SEGMENT-LENGTH
                                       UAV-LEFT-BOUNDARY
                                       UAV-RIGHT-BOUNDARY)))
    :rule-classes ((:linear :trigger-terms ((UAV-LEFT-BOUNDARY uav)))))
  
  (defthmd left-boundary-is-ordered
    (implies
     (< (uav->id uav1) (uav->id uav2))
     (< (UAV-LEFT-BOUNDARY uav1)
        (UAV-LEFT-BOUNDARY uav2)))
    :hints (("Goal" :in-theory (enable SEGMENT-LENGTH
                                       UAV-LEFT-BOUNDARY)))
    :rule-classes (:linear))

  (local (in-theory (enable left-boundary-is-ordered)))
  
  (defthm right-boundary-is-ordered
    (implies
     (< (uav->id uav1) (uav->id uav2))
     (< (UAV-RIGHT-BOUNDARY uav1)
        (UAV-RIGHT-BOUNDARY uav2)))
    :hints (("Goal" :in-theory (enable SEGMENT-LENGTH
                                       UAV-RIGHT-BOUNDARY))))
  
  (in-theory (disable (:rewrite right-boundary-is-ordered)))

  )
  
(encapsulate
    ()

  (local (include-arithmetic))

  (defthm even-right-boundary-is-lte-right-perimeter-boundary
    (<= (uav-right-boundary uav) (RIGHT-PERIMETER-BOUNDARY))
    :rule-classes (:linear :rewrite (:forward-chaining :trigger-terms ((uav-right-boundary uav))))
    :hints (("GOal" :nonlinearp t
             :in-theory 
             (enable uav-right-boundary
                     uav-left-boundary
                     RIGHT-PERIMETER-BOUNDARY
                     SEGMENT-LENGTH
                     ))))

  (defthm right-boundary-is-aways-greater-than-zero
    (< 0 (uav-right-boundary uav))
    :rule-classes ((:forward-chaining :trigger-terms ((uav-right-boundary uav))))
    :hints (("GOal" :in-theory (enable uav-left-boundary
                                       RIGHT-PERIMETER-BOUNDARY
                                       SEGMENT-LENGTH
                                       ))))

  )

(defun len-len-induction (x y)
  (if (not (consp x)) y
    (if (not (consp y)) x
      (len-len-induction (cdr x) (cdr y)))))

;; -------------------------------------------------------------------
;;
;; Our model employs a list of UAVs
;;
;; -------------------------------------------------------------------

(def::type-list UAV
  :listp uav-list-p)

(defthmd equal-to-uav-list-equiv
  (implies
   (and (uav-list-p x) (uav-list-p y))
   (iff (equal x y)
        (uav-list-equiv x y)))
  :hints (("Goal" :in-theory (enable uav-list-equiv))))

;; -------------------------------------------------------------------
;;
;; The locations of the UAVs in the list are ordered.
;;
;; -------------------------------------------------------------------

(defun <=location-all (x list)
  (declare (type t list))
  (if (not (consp list)) t
    (and (<= (UAV->location (UAV-fix! x)) (UAV->location (UAV-fix! (car list))))
         (<=location-all x (cdr list)))))

(defcong uav-equiv equal (<=location-all x list) 1)
(defcong uav-list-equiv equal (<=location-all x list) 2)

(defthm <=location-all-implies-<=-nth
  (implies
   (and
    (< (nfix j) (len list))
    (<=LOCATION-ALL A list))
   (<= (uav->location A)
       (uav->location (nth j list)))))

(def::un <=location-all-witness (x list)
  (declare (xargs :signature ((t t) integerp)))
  (if (not (consp list)) -1
    (if (not (<= (UAV->location (UAV-fix! x)) (UAV->location (UAV-fix! (car list))))) 0
      (1+ (<=location-all-witness x (cdr list))))))

(defthm <=location-all-witness-upper-bound
  (< (<=location-all-witness x list) (len list))
  :rule-classes (:rewrite :linear))

(defthm <=location-all-witness-upper-bound-rule
  (implies
   (<= (len list) n)
   (< (<=location-all-witness x list) n))
  :hints (("Goal" :in-theory (disable <=location-all-witness-upper-bound)
           :use <=location-all-witness-upper-bound)))

(defthm natp-implies
  (implies
   (natp x)
   (and (integerp x)
        (<= 0 x)))
  :rule-classes (:forward-chaining))

(defthm natp-<=location-all-witness
  (implies
   (consp list)
   (natp (<=location-all-witness x list)))
  :rule-classes (:rewrite :type-prescription))

(defthm natp-<=location-all-witness-linear
  (implies
   (consp list)
   (<= 0 (<=location-all-witness x list)))
  :rule-classes (:linear))

(defthm <=location-all-implies-consp
  (implies
   (not (<=location-all x list))
   (consp list))
  :rule-classes (:forward-chaining))

(defthm <=location-all-witness-property
  (implies
   (not (<=location-all x list))
   (< (uav->location (nth (<=location-all-witness x list) list))
      (uav->location x))))

(defthmd <=location-all-skolemization
  (iff (<=location-all x list)
       (if (not (consp list)) t
         (<= (uav->location x)
             (uav->location (nth (<=location-all-witness x list) list)))))
  :hints (("Goal" :in-theory (disable nfix))))

;; -------------------------------------------------------------------
;;
;; The primitive function for extracting UAVs from the list.
;;
;; -------------------------------------------------------------------

(defun ith (i list)
  (declare (type t i list))
  (if (not (consp list)) nil
    (let ((i (nfix i)))
      (if (zp i) (car list)
        (ith (1- i) (cdr list))))))

(defthm ith-to-nth
  (equal (ith i list) (nth i list)))

;;(defcong uav-list-equiv uav-equiv (nth i x) 2)

(def::un ith-uav (i list)
  (declare (xargs :signature  ((t t) uav-p)
                  :congruence ((uav-id-equiv uav-list-equiv) equal)))
  (UAV-fix! (ith (uav-id-fix i) (uav-list-fix! list))))

(defcong uav-list-equiv uav-equiv (ith-uav i x) 2
  :hints (("Goal" :in-theory (enable ith-uav))))

(defthm alt-location-bounds
  (and
   (<= 0 (uav->location (ith-uav i ens)))
   (<= (uav->location (ith-uav i ens)) (P)))
  :rule-classes (:linear))

(defthmd unfied-reduction
  (implies
   (and
    (syntaxp (quotep i))
    (integerp i)
    (< i 0))
   (equal (ith-uav i ens)
          (ith-uav 0 ens)))
  :hints (("Goal" :in-theory (enable uav-id-fix ith-uav))))

;; I don't think we ended up having any success with prioritized
;; rewriting.
(add-priority 1 unfied-reduction)

(defthmd degenerate-ith-uav
  (implies
   (not (uav-id-p x))
   (equal (ith-uav x ens)
          (ith-uav 0 ens)))
  :hints (("Goal" :in-theory (enable uav-id-fix ith-uav))))

(add-priority 1 degenerate-ith-uav)

(defthmd single-uav-perimeter-ith-index
  (implies
   (and
    (equal 1 (N))
    (syntaxp (not (quotep x))))
   (equal (ITH-UAV x ENS)
          (ith-uav 0 ens)))
  :hints (("Goal" :in-theory (enable UAV-ID-P uav-id-fix ith-uav))))

(add-priority 1 single-uav-perimeter-ith-index)

(defthm not-1-n
  (implies
   (not (equal (uav->location (ith-uav 0 ens))
               (uav->location (ith-uav 1 ens))))
   (< 1 (n)))
  :hints (("Goal" :in-theory (enable uav-id-fix ith-uav)))
  :rule-classes (:forward-chaining))


(defun <=location-all-quant (a list)
  (<= (uav->location a) (uav->location (ith-uav (<=location-all-witness a list) list))))

(defthm what-we-want-to-say-about-<=location-all
  (implies
   (and
    (<=location-all-quant x list)
    (equal (len list) (N)))
   (<= (uav->location x)
       (uav->location (ith-uav i list))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable UAV-ID-P uav-id-fix)
           :cases ((<=location-all x list)))))

(in-theory (disable <=location-all))
(in-theory (disable <=location-all-quant))

;; -------------------------------------------------------------------
;;
;; The list of UAVs is ordered by location.
;;
;; -------------------------------------------------------------------

(defun ordered-location-list-p (list)
  (declare (type t list))
  (if (not (consp list)) t
    (let ((uav (UAV-fix! (car list))))
      (and (<=location-all uav (cdr list))
           (ordered-location-list-p (cdr list))))))

(defthm ordered-location-list-p-implies-<=-nth
  (implies
   (and
    (ordered-location-list-p list)
    (<= (nfix i) (nfix j))
    (< (nfix j) (len list)))
   (<= (uav->location (nth i list))
       (uav->location (nth j list)))))

(defun ordered-location-list-p-witness (list)
  (if (not (consp list)) -1
    (let ((uav (UAV-fix! (car list))))
      (if (not (<=location-all uav (cdr list))) 0
        (1+ (ordered-location-list-p-witness (cdr list)))))))

(defthm ordered-location-list-p-witness-upper-bound
  (< (ordered-location-list-p-witness list) (len list))
  :rule-classes (:rewrite :linear))

(defthm ordered-location-list-p-witness-upper-bound-rule
  (implies
   (<= (len list) n)
   (< (ordered-location-list-p-witness list) n))
  :hints (("Goal" :in-theory (disable ordered-location-list-p-witness-upper-bound)
           :use ordered-location-list-p-witness-upper-bound)))

(defthm natp-ordered-location-list-p-witness
  (implies
   (consp list)
   (natp (ordered-location-list-p-witness list)))
  :rule-classes (:rewrite :type-prescription))

(in-theory (disable ordered-location-list-p-witness))

(encapsulate
    ()

  (local
   (defthm n-len-implies-consp
     (implies
      (equal (len list) (N))
      (consp list))
     :rule-classes (:forward-chaining :rewrite)))

  (local
   (defthm natp-implies-positive
     (implies
      (natp x)
      (<= 0 x))))
  
  (defthm uav-id-p-ordered-location-list-p-witness
    (implies
     (equal (len ens) (N))
     (uav-id-p (ordered-location-list-p-witness ens)))
    :hints (("Goal" :do-not-induct t
             :in-theory (enable uav-id-p))))

  )

(in-theory (disable ORDERED-LOCATION-LIST-P-WITNESS-UPPER-BOUND))

(defthm ordered-location-list-p-witness-property
  (implies
   (not (ordered-location-list-p list))
   (not (<=location-all (nth (ordered-location-list-p-witness list) list)
                        (nthcdr (ordered-location-list-p-witness list) list))))
  :hints (("Goal" :induct (ordered-location-list-p-witness list)
           :do-not-induct t
           :do-not '(eliminate-destructors)
           :in-theory (enable ordered-location-list-p-witness
                                     <=location-all)))
  :rule-classes (:rewrite :forward-chaining))

(defthmd ordered-location-list-p-partial-skolemization
  (iff (ordered-location-list-p list)
       (if (not (consp list)) t
         (<=location-all (nth (ordered-location-list-p-witness list) list)
                         (nthcdr (ordered-location-list-p-witness list) list))))
  :hints (("Goal" :induct (ordered-location-list-p-witness list)
           :in-theory (enable ordered-location-list-p-witness
                              <=location-all))))

(defthm not-consp-nthcdr
  (implies
   (not (consp list))
   (not (consp (nthcdr i list)))))

(defthm consp-nthcdr
  (iff (consp (nthcdr i list))
       (< (nfix i) (len list))))

(encapsulate
    ()

  (local (include-arithmetic))
  
  (defthm nth-nthcdr
    (equal (nth i (nthcdr j list))
           (if (<= (len list) (+ (nfix j) (nfix i))) nil
             (nth (+ (nfix i) (nfix j)) list)))
    :hints (("Goal" :induct (nthcdr j list))))

  )

(defthm len-nthcdr-x
  (implies
   (< (nfix i) (len list))
   (equal (len (nthcdr i list))
          (- (len list) (nfix i))))
  :rule-classes (:rewrite :linear))

(defthm nfix-definition
  (equal (nfix x)
         (if (natp x) x 0)))

(encapsulate
    ()

  (local
   (defthm ordered-location-list-p-skolemization-helper
     (iff (ordered-location-list-p list)
          (if (not (consp list)) t
            (let* ((n    (ordered-location-list-p-witness list))
                   (x    (nth n list))
                   (list (nthcdr (ordered-location-list-p-witness list) list)))
              (<= (uav->location x)
                  (uav->location (nth (<=location-all-witness x list) list))))))
     :hints (("Goal" :do-not-induct t
              :in-theory '(ordered-location-list-p-witness-upper-bound
                           ordered-location-list-p-partial-skolemization
                           consp-nthcdr
                           nth-nthcdr
                           natp-ordered-location-list-p-witness
                           nfix-definition
                           <=location-all-skolemization
                           )))))

  (defthmd ordered-location-list-p-skolemization
    (iff (ordered-location-list-p list)
         (if (not (consp list)) t
           (let* ((n    (ordered-location-list-p-witness list))
                  (x    (nth n list))
                  (rst  (nthcdr n list)))
             (<= (uav->location x)
                 (uav->location (nth (+ n (<=location-all-witness x rst)) list))))))
    :hints (("Goal" :do-not-induct t)))

  )

(defun ordered-location-list-p-first-witness (list)
  (uav-id-fix (ordered-location-list-p-witness list)))

(defun ordered-location-list-p-second-witness (list)
  (let* ((i    (uav-id-fix (ordered-location-list-p-witness list)))
         (x    (nth     i list))
         (rst  (nthcdr  i list))
         (k    (<=location-all-witness x rst)))
    (uav-id-fix (+ i k))))

(def::signature ordered-location-list-p-first-witness (t)
  uav-id-p)

(def::signature ordered-location-list-p-second-witness (t)
  uav-id-p)

;; -------------------------------------------------------------------
;;
;; Here we "quantify" the ordering property to enable pick-a-point
;; style proofs.
;;
;; -------------------------------------------------------------------

(defun ordered-location-list-quant-p (list)
  (let* ((i    (ordered-location-list-p-first-witness list))
         (j    (ordered-location-list-p-second-witness list)))
    (<= (uav->location (ith-uav i list))
        (uav->location (ith-uav j list)))))

(defthm positive-sum
  (implies
   (and
    (natp x)
    (natp y))
   (<= 0 (+ x y))))

(encapsulate
    ()

  (local
   (defthm sign-sign
     (implies
      (natp x)
      (<= 0 x))))

  (local
   (defthm zeip
     (implies
      (equal (len list) (N))
      (consp list))
     :rule-classes (:rewrite :forward-chaining)))

  (local (include-arithmetic))
  
  (defthm ordered-location-list-p-witness-ordering
    (implies
     (equal (len list) (N))
     (<= (ordered-location-list-p-first-witness list)
         (ordered-location-list-p-second-witness list)))
    :rule-classes (:linear :rewrite)
    :hints (("Goal" :do-not-induct t
             :in-theory (e/d (;;SIMPLIFY-SUMS-<
                              UAV-ID-FIX-UAV-ID-P
                              BODY-IMPLIES-UAV-ID-P)
                             (ordered-location-list-p-witness-upper-bound
                              <=location-all-witness-upper-bound
                              ORDERED-LOCATION-LIST-P-WITNESS-UPPER-BOUND-RULE
                              <=LOCATION-ALL-WITNESS-UPPER-BOUND-RULE
                              ))
             :cases ((<= (+ -1 (N)) (ORDERED-LOCATION-LIST-P-WITNESS LIST)))
             :use (ordered-location-list-p-witness-upper-bound
                   (:instance <=location-all-witness-upper-bound
                              (x (NTH (ORDERED-LOCATION-LIST-P-WITNESS LIST) LIST))
                              (list (NTHCDR (ORDERED-LOCATION-LIST-P-WITNESS LIST)
                                            LIST)))))))

  )

(defthmd ordered-location-list-p-to-ordered-location-list-quant-p
  (implies
   (equal (len list) (N))
   (iff (ordered-location-list-p list)
        (ordered-location-list-quant-p list)))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable uav-id-fix
                              uav-id-p
                              ordered-location-list-p-skolemization))))

(defthm ordered-location-list-p-implies-ordered-location-list-quant-p
  (implies
   (and
    (ordered-location-list-p list)
    (equal (len list) (N)))
   (ordered-location-list-quant-p list))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable ordered-location-list-p-to-ordered-location-list-quant-p))))

(defthmd what-we-want-to-say-about-ordered-location-list-p
  (implies
   (and
    (ordered-location-list-quant-p list)
    (equal (len list) (N))
    (<= (uav-id-fix i) (uav-id-fix j)))
   (<= (uav->location (ith-uav i list))
       (uav->location (ith-uav j list))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable UAV-ID-P uav-id-fix)
           :cases ((ordered-location-list-p list)))
          (and stable-under-simplificationp
               '(:in-theory (enable ORDERED-LOCATION-LIST-P-WITNESS
                                    ordered-location-list-p-skolemization)))
          ))

(in-theory (disable ordered-location-list-p-first-witness
                    ordered-location-list-p-second-witness))
                    
(in-theory (disable ith-uav ordered-location-list-quant-p))

;;
;; I think we could move this back much earlier
;;
(encapsulate
    ()

  (local
   (encapsulate
       ()

     (defthm nth-out-of-bounds
       (implies
        (<= (len list) (nfix i))
        (equal (nth i list)
               nil)))
     
     (defthm nth-to-ith-uav
       (implies
        (and
         (<= (len list) (N))
         (integerp i)
         (< i (len list)))
        (equal (uav-fix (nth i list))
               (ith-uav i list)))
       :hints (("GOal" :do-not-induct t
                :in-theory (enable uav-id-fix
                                   UAV-ID-P
                                   ith-uav))))
     
     (defthm equal-uav-fix-nth-to-equal-ith-uav
       (implies
        (and
         (integerp i)
         (< i (len x))
         (< i (len y))
         (force
          (and
           (<= (len x) (N))
           (<= (len y) (N)))))
        (iff (equal (uav-fix (nth i x))
                    (uav-fix (nth i y)))
             (equal (ith-uav i x)
                    (ith-uav i y))))
       :hints (("GOal" :do-not-induct t
                :in-theory '(uav-id-fix uav-id-p nfix nth-to-ith-uav))))

     ))
     
  (defthmd uav-list-equiv-pick-a-point-alt
    (implies
     (force
      (and
       (equal (len x) (N))
       (equal (len y) (N))))
     (iff (uav-list-equiv x y)
          (and (equal (len x) (len y))
               (equal (ith-uav (pick-a-point::uav-list-equiv-point x y) x)
                      (ith-uav (pick-a-point::uav-list-equiv-point x y) y)))))
    :hints (("Goal" :in-theory (enable uav-list-equiv-pick-a-point))))

  )

(defthm right-perimeter-pinching
  (implies
   (and
    (EQUAL (UAV->LOCATION (ith-uav i ens)) (RIGHT-PERIMETER-BOUNDARY))
    (<= (uav-id-fix i) (uav-id-fix j))
    (ordered-location-list-quant-p ens)
    (equal (len ens) (N)))
   (equal (uav->location (ith-uav j ens))
          (RIGHT-PERIMETER-BOUNDARY)))
  :hints (("Goal" :use (:instance what-we-want-to-say-about-ordered-location-list-p
                                  (list ens)))))

(defthmd location-pinching-lemma
  (implies
   (and
    (equal (UAV->location (ith-uav i list))
           (UAV->location (ith-uav j list)))
    (implies
     (<= (UAV-id-fix i) (UAV-id-fix j))
     (and (<= (UAV-id-fix i) (UAV-id-fix k))
          (<= (UAV-id-fix k) (UAV-id-fix j))))
    (implies
     (<= (UAV-id-fix j) (UAV-id-fix i))
     (and (<= (UAV-id-fix j) (UAV-id-fix k))
          (<= (UAV-id-fix k) (UAV-id-fix i))))
    (ordered-location-list-quant-p list)
    (equal (len list) (N))
    )
   (equal (UAV->location (ith-uav k list))
          (UAV->location (ith-uav i list))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance what-we-want-to-say-about-ordered-location-list-p (i k) (j i))
                 (:instance what-we-want-to-say-about-ordered-location-list-p (i j) (j k))
                 (:instance what-we-want-to-say-about-ordered-location-list-p (i k) (j j))
                 (:instance what-we-want-to-say-about-ordered-location-list-p (i i) (j k)))
           )))

(defthmd location-pinching-lemma-instance
  (implies
   (and
    (equal (UAV->location (ith-uav i list))
           (UAV->location (ith-uav j list)))
    (<= (UAV-id-fix i) (UAV-id-fix k))
    (<= (UAV-id-fix k) (UAV-id-fix j))
    (ordered-location-list-quant-p list)
    (equal (len list) (N))
    )
   (equal (UAV->location (ith-uav k list))
          (UAV->location (ith-uav i list))))
  :hints (("Goal"
           :do-not-induct t
           :use location-pinching-lemma
           )))

(defthm far-left-location-forcing
  (implies
   (and
    (ordered-location-list-quant-p ens)
    (equal (len ens) (N))
    (equal (uav->location (ith-uav j ens)) 0)
    (<= (uav-id-fix i) (uav-id-fix j)))
   (equal (uav->location (ith-uav i ens)) 0))
  :hints (("Goal" :use (:instance what-we-want-to-say-about-ordered-location-list-p
                                  (list ens)))))

;; -------------------------------------------------------------------
;;
;; The UAV ID's within the list are sequential
;;
;; -------------------------------------------------------------------

(defun sequential-id-list-aux-p (id list)
  (declare (type t list)
           (xargs :measure (len list)))
  (if (not (consp list)) (<= (nfix id) (N))
    (let ((id (nfix id)))
      (and (equal (UAV->id (UAV-fix! (car list))) id)
           (sequential-id-list-aux-p (1+ id) (cdr list))))))

(defun sequential-id-list-aux-p-witness (id list)
  (declare (xargs :measure (len list)))
  (if (not (consp list)) 0
    (let ((id (nfix id)))
      (if (not (equal (UAV->id (UAV-fix! (car list))) id)) 0
        (1+ (sequential-id-list-aux-p-witness (1+ id) (cdr list)))))))

(defthm sequential-id-list-aux-p-witness-bound
  (implies
   (and
    (not (sequential-id-list-aux-p id list))
    (<= (+ (nfix id) (len list)) (N)))
   (< (sequential-id-list-aux-p-witness id list) (len list)))
  :hints (("Goal" :do-not-induct t
           :induct (sequential-id-list-aux-p-witness id list))))

(defthmd sequential-id-list-aux-p-witness-property
  (implies
   (and
    (not (sequential-id-list-aux-p id list))
    (<= (+ (nfix id) (len list)) (N)))
   (not (equal (UAV->id (nth (sequential-id-list-aux-p-witness id list) list))
               (+ (sequential-id-list-aux-p-witness id list) (nfix id))))))

(defthm sequential-id-list-aux-p-witness-when-sequential
  (implies
   (sequential-id-list-aux-p id list)
   (equal (sequential-id-list-aux-p-witness id list)
          (len list))))

(defthmd sequential-id-list-aux-p-reduction
  (implies
   (equal (len list) (N))
   (iff (sequential-id-list-aux-p 0 list)
        (equal (UAV->id (ith-uav (sequential-id-list-aux-p-witness 0 list) list))
               (uav-id-fix (sequential-id-list-aux-p-witness 0 list)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable ith-uav uav-id-p
                              uav-id-fix))
          (and stable-under-simplificationp
               '(:use ((:instance sequential-id-list-aux-p-witness-bound
                                  (id 0))
                       (:instance sequential-id-list-aux-p-witness-property
                                  (id 0)))))))

(defcong uav-list-equiv equal (sequential-id-list-aux-p id list) 2)
;;(defcong nfix-equiv equal (sequential-id-list-aux-p id list) 1)

(defthm sequential-id-list-aux-p-bound
  (implies
   (and
    (sequential-id-list-aux-p id list)
    (natp id)
    (uav-list-p list))
   (<= (+ id (len list)) (N)))
  :rule-classes (:forward-chaining :linear))

(defthm UAV-id-sequential-id-list-aux-p
  (implies
   (and
    (sequential-id-list-aux-p n per)
    (< (nfix k) (len per)))
   (equal (UAV->id (nth k per))
          (+ (nfix n) (nfix k)))))

;; -------------------------------------------------------------------
;;
;; The UAV ID's within the list are sequential, starting at zero
;;
;; -------------------------------------------------------------------

(defun sequential-id-list-p (list)
  (declare (type t list))
  (sequential-id-list-aux-p 0 list))

(defthmd sequential-id-list-p-reduction
  (implies
   (equal (len list) (N))
   (iff (sequential-id-list-p list)
        (equal (UAV->id (ith-uav (sequential-id-list-aux-p-witness 0 list) list))
               (uav-id-fix (sequential-id-list-aux-p-witness 0 list)))))
  :hints (("Goal" :do-not-induct t
           :in-theory '(sequential-id-list-p
                        sequential-id-list-aux-p-reduction))))

(defthm ith-uav-id-is-i
  (implies
   (and
    (sequential-id-list-p list)
    (equal (len list) (N)))
   (equal (UAV->id (ith-uav i list))
          (uav-id-fix i)))
  :hints (("Goal" :in-theory (enable ith-uav))))

(defthm rewrite-left-boundary-to-right-boundary
  (implies
   (and
    (sequential-id-list-p ens)
    (equal (len ens) (N)))
   (equal (UAV-left-boundary (ith-uav i ens))
          (if (equal (uav-id-fix i) 0) (left-perimeter-boundary)
            (UAV-right-boundary (ith-uav (+ -1 (uav-id-fix i)) ens)))))
  :hints (("Goal" :in-theory (enable left-perimeter-boundary
                                     UAV-left-boundary
                                     UAV-right-boundary))))


(defthm sequential-id-list-p-implies-sequential-id-list-aux-p
  (implies
   (sequential-id-list-p list)
   (sequential-id-list-aux-p 0 list))
  :rule-classes (:forward-chaining))

(in-theory (disable sequential-id-list-p))

(encapsulate
    ()

  (local (include-arithmetic))
  
  (defthmd UAV-right-boundary-is-right-perimeter-boundary-strong
    (implies
     (equal (+ (UAV->id x) 1) (N))
     (equal (UAV-right-boundary x)
            (right-perimeter-boundary)))
    :hints (("Goal" :in-theory (enable right-perimeter-boundary
                                       SEGMENT-LENGTH
                                       UAV-left-boundary
                                       UAV-right-boundary))))
  
  (defthm UAV-right-boundary-is-right-perimeter-boundary
    (implies
     (and
      (sequential-id-list-p ens)
      (equal (len ens) (N)))
     (equal (UAV-right-boundary (ITH-UAV (+ -1 (N)) ENS))
            (right-perimeter-boundary)))
    :hints (("Goal" :in-theory (enable UAV-right-boundary-is-right-perimeter-boundary-strong))))

  )



;; -------------------------------------------------------------------
;;
;; wf-ensemble is a predicate that recognizes ensembles of
;; UAVs that satisfy our model constraints.
;;
;; -------------------------------------------------------------------

(def::type-predicate wf-ensemble (ens)
  :type-name wf-ensemble
  :non-executable t
  :rewrite t
  :forward-chain-cases nil
  :body (and (uav-list-p ens)
             (sequential-id-list-p ens)
             (equal (len ens) (N))
             (ordered-location-list-p ens)
             ))

(defthm UAV-RIGHT-BOUNDARY-of-uav
  (implies
   (and
    (wf-ensemble ens)
    (syntaxp (symbolp ens)))
   (equal (UAV-RIGHT-BOUNDARY (UAV I L D))
          (uav-right-boundary (ith-uav i ens))))
  :hints (("Goal" :in-theory (enable uav-left-boundary
                                     uav-right-boundary))))

(defthm UAV-LEFT-BOUNDARY-of-uav
  (implies
   (and
    (wf-ensemble ens)
    (syntaxp (symbolp ens)))
   (equal (UAV-LEFT-BOUNDARY (UAV I L D))
          (uav-left-boundary (ith-uav i ens))))
  :hints (("Goal" :in-theory (enable uav-left-boundary
                                     uav-right-boundary))))


;; DAG .. I originally wanted to just use linear rules like God
;; intended.  def::linear allows me to do that now.
(def::linear location-linear
  (implies
   (and
    (syntaxp (not (equal i j)))
    (<= (uav-id-fix i) (uav-id-fix j))
    (wf-ensemble ens))
   (<= (uav->location (ith-uav i ens))
       (uav->location (ith-uav j ens))))
  :hints (("Goal" :in-theory (enable what-we-want-to-say-about-ordered-location-list-p))))

(def::linear right-boundary-is-ordered-linear
  (implies
   (and
    (< (uav-id-fix i) (uav-id-fix j))
    (wf-ensemble ens))
   (< (UAV-RIGHT-BOUNDARY (ith-uav i ens))
      (UAV-RIGHT-BOUNDARY (ith-uav j ens))))
  :hints (("Goal" :in-theory (enable right-boundary-is-ordered))))

(with-arithmetic

 (defthm evenly-spaced-boundaries
   (implies
    (and
     (<= (uav-id-fix i) (+ -3 (N)))
     (wf-ensemble ens)
     ;;
     ;; DAG - If we don't double-rewrite, we ended up with 'ifs'
     ;; in our linear result (!)
     ;;
     (uav-id-equiv ip1 (double-rewrite (+ 1 (uav-id-fix i))))
     (uav-id-equiv ip2 (double-rewrite (+ 2 (uav-id-fix i))))
     )
    (equal (* 2 (UAV-RIGHT-BOUNDARY (ITH-UAV ip1 ENS)))
           (+ (UAV-RIGHT-BOUNDARY (ITH-UAV I ENS))
              (UAV-RIGHT-BOUNDARY (ITH-UAV ip2 ENS)))))
   :hints (("Goal" :in-theory (enable UAV-RIGHT-BOUNDARY
                                      UAV-LEFT-BOUNDARY)))
   :rule-classes ((:linear :trigger-terms ((UAV-RIGHT-BOUNDARY (ITH-UAV I ENS))))))

 (local
  (defthm P-defn
    (equal (P) (* (N) (segment-length)))
    :hints (("Goal" :in-theory (enable segment-length)))))
 
 (defthm evenly-spaced-boundaries-constant
   (implies
    (and
     (syntaxp (quotep c))
     (integerp c)
     (<= 0 c)
     (< (+ 2 c) (N))
     (wf-ensemble ens))
    (equal (* 2 (UAV-RIGHT-BOUNDARY (ITH-UAV (+ 1 c) ENS)))
           (+ (UAV-RIGHT-BOUNDARY (ITH-UAV c ENS))
              (UAV-RIGHT-BOUNDARY (ITH-UAV (+ 2 c) ENS)))))
   :hints (("Goal" :in-theory (enable uav-id-p
                                      UAV-RIGHT-BOUNDARY
                                      UAV-LEFT-BOUNDARY)))
   :rule-classes ((:linear :trigger-terms ((UAV-RIGHT-BOUNDARY (ITH-UAV c ENS))))))
 
 (defthm evenly-spaced-left-perimeter
   (implies
    (and
     (< 1 (N))
     (wf-ensemble ens))
    (equal (* 2 (UAV-RIGHT-BOUNDARY (ITH-UAV 0 ENS)))
           (+ (LEFT-PERIMETER-BOUNDARY)
              (UAV-RIGHT-BOUNDARY (ITH-UAV 1 ENS)))))
   :hints (("Goal" :in-theory (enable uav-id-p
                                      LEFT-PERIMETER-BOUNDARY
                                      UAV-RIGHT-BOUNDARY
                                      UAV-LEFT-BOUNDARY)))
   :rule-classes ((:linear :trigger-terms ((UAV-RIGHT-BOUNDARY (ITH-UAV 1 ENS))))))

 (defthm evenly-spaced-betwee-perimeter-boundaries
   (implies
    (and
     (equal (N) 2)
     (wf-ensemble ens))
    (equal (* 2 (UAV-RIGHT-BOUNDARY (ITH-UAV 0 ENS)))
           (+ (LEFT-PERIMETER-BOUNDARY)
              (RIGHT-PERIMETER-BOUNDARY))))
   :hints (("Goal" :in-theory (enable uav-id-p
                                      LEFT-PERIMETER-BOUNDARY
                                      RIGHT-PERIMETER-BOUNDARY
                                      UAV-RIGHT-BOUNDARY
                                      UAV-LEFT-BOUNDARY)))
   :rule-classes ((:linear :trigger-terms ((UAV-RIGHT-BOUNDARY (ITH-UAV 0 ENS))))))
 
 )

(in-theory (disable ALT-LOCATION-BOUNDS
                    RIGHT-PERIMETER-BOUND
                    LEFT-PERIMETER-BOUNDARY-UPPER-BOUND))

(encapsulate
    (
     ((ensemble-witness) => *)
     )
  

  (local (include-arithmetic))
     
  (local
   (encapsulate
       ()

     (def::un ensemble-witness-rec (i)
       (declare (xargs :fty ((nat) uav-list)
                       :guard-hints (("Goal" :in-theory (enable natp
                                                                uav-id-p
                                                                UAV-LOCATION-P
                                                                SEGMENT-LENGTH
                                                                LEFT-PERIMETER-BOUNDARY
                                                                RIGHT-PERIMETER-BOUNDARY)
                                      :nonlinearp t))))
       (if (zp i) nil
         (if (< (N) i) nil
           (let* ((id  (- (N) i))
                  (loc (* id (segment-length))))
             (let ((uav (uav id loc 1))) 
               (cons uav (ensemble-witness-rec (1- i))))))))

     (defthm len-ensemble-witness-rec
       (equal (len (ensemble-witness-rec i))
              (if (<= (nfix i) (N))
                  (nfix i)
                0)))

     (defthm len-ENSEMBLE-WITNESS-REC-N
       (equal (len (ENSEMBLE-WITNESS-REC (N)))
              (N))
       :rule-classes (:rewrite
                      :linear
                      (:forward-chaining :trigger-terms ((ENSEMBLE-WITNESS-REC (N))))))

     (defun nth-nth-induction (i j)
       (if (zp i) j
         (if (zp j) i
           (nth-nth-induction (1- i) (1- j)))))

     (defthm nth-ensemble-witness-rec
       (equal (nth j (ensemble-witness-rec i))
              (let ((i (nfix i)))
                (if (< (N) i) nil
                  (let ((n (- (N) i))
                        (j (nfix j)))
                    (if (< j i)
                        (let* ((id (+ n j))
                               (loc (* id (segment-length))))
                          (uav id loc 1))
                      nil)))))
       :hints (("Goal" :induct (nth-nth-induction i j)
                :expand ((ENSEMBLE-WITNESS-REC I)
                         (:free (i a x) (nth i (cons a x)))))))

     (def::un ensemble-witness ()
       (declare (xargs :signature (() uav-list-p)))
       (ensemble-witness-rec (N)))

     (defthm len-ensemble-witness
       (equal (len (ensemble-witness)) (N)))

     (defthm ith-uav-ensemble-witness
       (equal (ith-uav i (ensemble-witness))
              (uav i (* (uav-id-fix i) (segment-length)) 1))
       :hints (("Goal" :in-theory (enable ith-uav))))

     (defthm <-right-perimeter-boundary-reduction
       (implies
        (and (integerp x) (integerp y))
        (iff (< (right-perimeter-boundary)
                (+ (* (segment-length) x)
                   (* (segment-length) y)))
             (< (n) (+ x y))))
       :hints (("Goal" :in-theory (enable segment-length right-perimeter-boundary)
                :nonlinearp t)))

     (defthm <=-right-perimeter-boundary-reduction
       (implies
        (and (integerp x) (integerp y))
        (iff (< (+ (* (segment-length) x)
                   (* (segment-length) y))
                (right-perimeter-boundary))
             (< (+ x y) (n))))
       :hints (("Goal" :in-theory (enable segment-length right-perimeter-boundary)
                :nonlinearp t)))

     (defthm <-right-perimeter-boundary-alt
       (implies
        (integerp x)
        (iff (< (RIGHT-PERIMETER-BOUNDARY) (* (SEGMENT-LENGTH) x))
             (< (n) x)))
       :hints (("Goal" :in-theory (enable segment-length right-perimeter-boundary)
                :nonlinearp t)))

     (encapsulate
         ()

       (local
        (encapsulate
            ()
          
          (in-theory (enable UAV-LOCATION-FIX))

          (defthm ORDERED-LOCATION-LIST-P-WITNESS-ENSEMBLE-WITNESS-REC-bound
            (< (ORDERED-LOCATION-LIST-P-WITNESS (ENSEMBLE-WITNESS-REC (N))) (N)))
          
          (defthm really?
            (implies
             (and
              (not (equal x 0))
              (integerp x)
              (force (<= 0 x)))
             (< 0 x)))
          
          (defthm sigh
            (implies
             (force (consp y))
             (< -1 (<=location-all-witness x y))))
          
          (DEFTHM LEN-NTHCDR-again?
            (IMPLIES (< (NFIX I) (LEN LIST))
                     (EQUAL (LEN (NTHCDR I LIST))
                            (- (LEN LIST) (NFIX I))))
            :rule-classes (:rewrite));; :linear))
          ))

       (in-theory (disable (UAV->LOCATION)))
       
       (defthm ordered-location-list-p-ensemble-witness
         (ordered-location-list-p (ensemble-witness))
         :hints (("Goal" ;;:nonlinearp t
                  :in-theory (enable natp
                                     LEFT-PERIMETER-BOUNDARY
                                     ordered-location-list-p-skolemization))))
       
       )

     (in-theory (disable ensemble-witness (ensemble-witness)))

     (defthm sequential-id-list-p-ensemble-witness
       (sequential-id-list-p (ensemble-witness))
       :hints (("Goal" :in-theory (enable sequential-id-list-p-reduction))))

     (defthm segment-length-times-uav-id-bounded-by-right-perimeter
       (implies
        (uav-id-p id)
        (<= (* (SEGMENT-LENGTH) id)
            (RIGHT-PERIMETER-BOUNDARY)))
       :rule-classes (:rewrite :linear)
       :hints (("GOal" :in-theory (enable RIGHT-PERIMETER-BOUNDARY
                                          segment-length
                                          uav-id-p)
                :nonlinearp t)))

     ))
  
  ;; This is all we should need for escort-condition ..
  (defthm all-uav-locations-differ
    (iff (equal (uav->location (ith-uav i (ensemble-witness)))
                (uav->location (ith-uav j (ensemble-witness))))
         (uav-id-equiv i j))
    :hints (("Goal" :in-theory (enable LEFT-PERIMETER-BOUNDARY
                                       UAV-LOCATION-FIX))))

  (def::signature ensemble-witness ()
    wf-ensemble)
    
  )

(def::type sequential-ensemble (list)
  :type-witness (ensemble-witness)
  :body (and (sequential-id-list-p list)
             (equal (len list) (N))))

(def::type ordered-ensemble (list)
  :type-witness (ensemble-witness)
  :body (and (ordered-location-list-p list)
             (equal (len list) (N))))

(def::type wf-ensemble (list)
  :type-p wf-ensemble
  :prove-properties nil
  :type-witness (ensemble-witness)
  :non-executable t
  :refines (ordered-ensemble
            sequential-ensemble)
  :refines-equiv-in-theory (enable wf-ensemble-fix
                                   sequential-ensemble-fix
                                   ordered-ensemble-fix)
  )

(encapsulate
    (
     ((perimeter) => *)
     )

  (local
   (encapsulate
       ()

     (in-theory (enable BODY-IMPLIES-UAV-ID-P
                        UAV-ID-FIX-UAV-ID-P))
     
     (encapsulate
         ()

       (local (include-arithmetic))

       (local (in-theory (enable RIGHT-PERIMETER-BOUNDARY LEFT-PERIMETER-BOUNDARY UAV-LOCATION-P)))
       
       (def::un UAV-witness (n)
         (declare (xargs :signature ((t) UAV-p)))
         (let ((n (UAV-id-fix n)))
           (UAV n (- (P) (/ (P) (1+ n))) -1)))
       
       (defthm UAV-witness->id
         (equal (UAV->id (UAV-witness n))
                (UAV-id-fix n)))

       (defthm <=UAV-LOCATION-UAV-WITNESS
         (implies
          (<= (UAV-ID-fix n) (uav-id-fix m))
          (<= (UAV->LOCATION (UAV-WITNESS N))
              (UAV->LOCATION (UAV-WITNESS M))))
         :rule-classes (:rewrite :linear))
       
       (in-theory (disable UAV-witness (UAV-witness)))
       
       )
     
     (defun perimeter-witness (n)
       (declare (type t n)
                (xargs :measure (nfix (- (N) (nfix n)))))
       (let ((n (nfix n)))
         (if (<= (N) n) nil
           (cons (UAV-witness n)
                 (perimeter-witness (1+ n))))))
     
     (in-theory (disable (perimeter-witness)))

     (local (in-theory (enable <=LOCATION-ALL)))
     
     (defthm <=LOCATION-ALL-PERIMETER-WITNESS
       (implies
        (<= (uav-id-fix n) (uav-id-fix m))
        (<=LOCATION-ALL (UAV-WITNESS N) (PERIMETER-WITNESS m)))
       :hints (("Subgoal *1/2" :cases ((uav-id-p (+ 1 m))))))
     
     (defthm ORDERED-LOCATION-LIST-P-PERIMETER-WITNESS
       (ORDERED-LOCATION-LIST-P (PERIMETER-WITNESS n))
       :hints (("Subgoal *1/2" :cases ((< (+ 1 n) (N))))))

     (in-theory (disable (perimeter-witness)))
     
     (def::signature perimeter-witness (t) UAV-list-p)
     
     (defthm len-perimeter-witness
       (equal (len (perimeter-witness n))
              (nfix (- (N) (nfix n)))))
     
     (defthm sequential-id-list-aux-p-perimeter-witness
       (implies
        (< (nfix n) (N))
        (sequential-id-list-aux-p n (perimeter-witness n)))
       :hints (("Goal" :in-theory (disable (sequential-id-list-aux-p)
                                           (perimeter-witness)))))
     
     (defthm wf-ensemble-witness
       (wf-ensemble (perimeter-witness 0))
       :hints (("Goal" :in-theory (enable sequential-id-list-p))))

     ))

  (local
   (defun perimeter ()
     (perimeter-witness 0)))

  ;; But we are looking for a map from the real numbers to wf-ensembles ..
  
  (defthm wf-ensemble-perimeter
    (wf-ensemble (perimeter))
    :rule-classes (:rewrite (:forward-chaining :trigger-terms ((perimeter)))))
  
  )

(in-theory (disable sequential-id-list-aux-p-bound))

;;
;; pattern-hints definitions
;;

(def::pattern-function lte-index-filter (x y)
  (:first (:match x 0)
          (:and (:match x 1)
                (:not (:match y 0)))
          (:match y (n))
          (:match y (+ -1 (n)))
          (:and (:match y (+ -2 (n)))
                (:not (:match x (+ -1 (n)))))
          (:call (lte-filter x y) nil)))

(def::pattern-function lt-N-filter (x)
  (:first (:match x (uav-id-fix y))
          (:syntaxp (quotep x))
          (:and (:call (base-offset x) (xo xb))
                (:syntaxp (quotep xo))
                (:or (:syntaxp (<= (cadr xo) 0))
                     (:and
                      (:bind-free `(((c . (quote ,(- (cadr xo)))))) (c))
                      (:call (lte-filter xb (+ c (N))) nil))))
          (:call (lte-filter x (+ -1 (N))) nil)
          ))
                        
(def::pattern-function gte-0-filter (x)
  (:first (:match x (uav-id-fix y))
          (:and (:call (base-offset x) (xo xb))
                (:syntaxp (or (equal xb '(N))
                              (and (quotep xo)
                                   (<= 0 (cadr xo))))))
          (:call (lte-filter 0 x) nil)))

(def::pattern-function uav-fix (x)
  (:match x (:if (+ c b) (:bind (res x))
                 (:if (:syntaxp (quotep x)) (:bind (res x))
                      (:if (uav-id-fix y) (:bind (res x))
                           (:bind (res (uav-id-fix x)))))))
  :returns (res))

(def::pattern-function unfix (x)
  (:match x (:if (uav-id-fix y) (:bind (res y))
                 (:bind (res x))))
  :returns (res))

(def::pattern-hint ordering-rule
  (:and
   (:replicate (:or (:term (uav->location (ith-uav i ens)))
                    (:term (uav-right-boundary (ith-uav i ens))))
               (j i))
   (:not (:equal i j))
   (:call (uav-fix i) (ifix))
   (:call (uav-fix j) (jfix))
   ;;(:syntaxp (not (cw "consider: ~x0 and ~x1 ~%" ifix jfix)))
   (:call (lte-index-filter ifix jfix) nil)
   ;;(:syntaxp (not (cw "lte-in-filtr: ~x0 <= ~x1 ~%" ifix jfix)))
   (:call (gte-0-filter ifix) nil)
   ;;(:syntaxp (not (cw "gte-0-filter: 0 <= ~x0 ~%" ifix)))
   (:call (lt-N-filter jfix) nil)
   ;;(:syntaxp (not (cw "lt-N-filter : ~x0 < (N) ~%" jfix)))
   (:first (:not (< (uav->location (ith-uav i ens))
                    (uav->location (ith-uav j ens))))
           (:not (<= (uav-right-boundary (ith-uav i ens))
                     (uav-right-boundary (ith-uav j ens)))))
   (:keep ens i j)
   )
  ;;:stable nil
  :use ((:instance what-we-want-to-say-about-ordered-location-list-p
                   (list ens)
                   (i i)
                   (j j))
        (:instance right-boundary-is-ordered-linear
                   (ens ens)
                   (i i)
                   (j j))))

(defthm lt-chaining-rule
  (implies
   (and
    (< (UAV-ID-FIX I)
       (UAV-ID-FIX K))
    (< (UAV-ID-FIX K)
       (UAV-ID-FIX J)))
   (< (UAV-ID-FIX I) (UAV-ID-FIX J)))
  :rule-classes (:forward-chaining))

;; ------------------------------------------------------------------
;;
;; escort-condition: essentially, a first UAV is not allowed to
;; escort a second UAV *away* from the first UAV's segment.  Once
;; this property has been established, it is invariant.
;; 
;; ------------------------------------------------------------------

(defun escort-condition-p (i j ens)
  (declare (type t i ens))
  (let* ((i   (uav-id-fix i))
         (j   (uav-id-fix j)))
    (implies
     (and
      (< i j)
      (equal (UAV->location (ith-uav i ens))
             (UAV->location (ith-uav j ens))))
     (and
      (implies
       ;;      I        J
       ;; |--------|--------|
       ;;      >>  |
       ;;      ij
       (and
        (< 0 (UAV->direction (ith-uav i ens)))
        (< 0 (UAV->direction (ith-uav j ens))))
       (<= (UAV->location (ith-uav i ens))
           (UAV-right-boundary (ith-uav i ens))))
      ;;
      (implies
       ;;      I        J
       ;; |--------|--------|
       ;;          |  <<
       ;;             ij
       (and
        (< (UAV->direction (ith-uav i ens)) 0)
        (< (UAV->direction (ith-uav j ens)) 0))
       (<= (UAV-left-boundary (ith-uav j ens))
           (UAV->location (ith-uav j ens))))
      ))))

;; (defthmd cellularize-escort-condition-p
;;   (implies
;;    (wf-ensemble ens)
;;    (equal (escort-condition-p i j ens)
;;           (cellular-escort-condition-p (ith-uav i ens) (ith-uav j ens)))))

(defthm escort-condition-p-ensemble-witness
  (escort-condition-p i j (ensemble-witness)))

(defun-sk escort-condition (ens)
  (declare (type t ens))
  (forall (i j) (escort-condition-p i j ens)))

(defthmd escort-condition-implies
  (implies
   (escort-condition ens)
   (escort-condition-p i j ens))
  :hints (("Goal" :use (:instance escort-condition-necc))))

(defthm escort-condition-ensemble-witness
  (escort-condition (ensemble-witness))
  :hints (("Goal" :in-theory (disable escort-condition-p))))

(in-theory (disable escort-condition))

(def::type escort-condition (x)
  :type-witness (ensemble-witness)
  :type-p escort-condition
  :prove-properties nil
  )

;; ------------------------------------------------------------------
;;
;; a wf-escort is just the conjunction of escort-condition and
;; wf-ensemble.
;;
;; ------------------------------------------------------------------

(def::type wf-escort (ens)
  :type-witness (ensemble-witness)
  :and (escort-condition
        wf-ensemble))

(defthm equal-negative-sign-fix
  (iff (equal (UAV->DIRECTION uav) (- (sign-fix s)))
       (not (equal (UAV->DIRECTION uav) (sign-fix s))))
  :hints (("Goal" :in-theory (enable sign-fix sign-p))))

(in-theory (disable escort-condition))

(in-theory (disable FAR-LEFT-LOCATION-FORCING))

(defthm combine-constants-linear
  (implies
   (and
    (syntaxp (and (quotep c) (quotep d)))
    (integerp x)
    (integerp y))
   (iff (< (+ c x) (+ d y))
        (< x (+ (- d c) y)))))


(def::pattern-function same-location-match ()
  (:and (:replicate
         (:and (:commutes (EQUAL A z) (A z))
               (:match z (UAV->LOCATION (ITH-UAV i ENS))))
         (B A) (j i))
        (:or (:and (:equal A B)
                   (:not (:equal i j)))
             (:and (:match A (UAV->LOCATION (ITH-UAV j ENS)))
                   (:bind (A B)))))
  :returns (i j A ens))

(def::pattern-function same-location-filter (ens i j)
  (:and (:replicate (:commutes (equal P Q) (P Q)) (R P) (S Q))
        (:first (:and (:match P (UAV->LOCATION (ITH-UAV i ENS)))
                      (:match Q (UAV->LOCATION (ITH-UAV j ENS))))
                (:and (:equal Q R)
                      (:match P (UAV->LOCATION (ITH-UAV i ENS)))
                      (:match S (UAV->LOCATION (ITH-UAV j ENS)))))))

(def::pattern-function constant-distance-filter (i j)
  (:and
   (:call (base-offset i) (ci bi))
   (:call (base-offset j) (cj bj))
   (:equal bi bj)))

(def::pattern-function strong-intermediate-value (i k j)
  (:first
   ;;(:syntaxp (not (cw "strong:(~x0 <= ~x1 <= ~x2)~%" i k j)))
   (:and
    (:call (lte-index-filter i k) nil)
    (:first (:and (:call (constant-distance-filter i k) nil)
                  (:not (:call (constant-distance-filter i j) nil))
                  (:call (lte-index-filter i j) nil)
                  )
            (:call (lte-index-filter k j) nil))
    ;;(:syntaxp (not (cw "1:(~x0 <= ~x1 <= ~x2)~%" i k j)))
    )
   (:and
    (:call (lte-index-filter k j) nil)
    (:first (:and (:call (constant-distance-filter k j) nil)
                  (:not (:call (constant-distance-filter i j) nil))
                  (:call (lte-index-filter i j) nil)
                  )
            (:call (lte-index-filter i k) nil))
    ;;(:syntaxp (not (cw "2:(~x0 <= ~x1 <= ~x2)~%" i k j)))
    )
   ))

(def::pattern-hint location-pinching-rule
  (:and
   (:call (same-location-match) (iindex jindex A ens))
   (:call (uav-fix iindex) (i))
   (:call (uav-fix jindex) (j))
   (:term (uav->location (ith-uav kindex ens)))
   (:not (:equal iindex kindex))
   (:not (:equal jindex kindex))
   (:call (uav-fix kindex) (k))
   (:call (strong-intermediate-value i k j) nil)
   (:keep ens iindex kindex jindex)
   )
  ;;:stable nil
  :use ((:instance location-pinching-lemma-instance
                   (list ens)
                   (i iindex)
                   (k kindex)
                   (j jindex))
        ))


(def::pattern-hint escort-condition-implies
  (:and
   (:call (same-location-match) (i j A ens))
   ;;(:syntaxp (not (cw "same location : ~x0 ~x1~%" i j)))
   ;;(:either (< (UAV-right-boundary (ith-uav i ens)) (UAV->location (ith-uav j ens))))
   ;;(:either (< (UAV->location (ith-uav j ens)) (UAV-right-boundary (ith-uav i ens))))
   ;;(:commutes (equal (UAV-right-boundary (ith-uav i ens)) (UAV->location (ith-uav j ens)))))
   (:call (uav-fix i) (ifix))
   (:call (uav-fix j) (jfix))
   (:or (:match A (:or 0 (LEFT-PERIMETER-BOUNDARY) (RIGHT-PERIMETER-BOUNDARY)))
        (:and (:call (lte-index-filter ifix jfix) nil)
              (:call (lt-N-filter jfix) nil)
              (:call (gte-0-filter ifix) nil)))
   (:keep ens i j))
  ;;:stable nil
  :use ((:instance escort-condition-implies
                   (ens ens)
                   (i i)
                   (j j))))

(def::pattern-hint right-perimeter-escort-condition-implies
  (:and (equal (UAV->location (ith-uav i ens))
               (right-perimeter-boundary))
        (EQUAL (UAV->DIRECTION (ITH-UAV j ENS)) b)
        (:call (uav-fix i) (ifix))
        (:call (uav-fix j) (jfix))
        (:call (lte-index-filter ifix jfix) nil)
        (:keep ens i j)
        )
  ;;:stable nil
  :use ((:instance escort-condition-implies
                   (ens ens)
                   (i i)
                   (j j))))

(def::pattern-hint left-perimeter-escort-condition-implies
  (:and (equal (UAV->location (ith-uav j ens))
               (left-perimeter-boundary))
        (EQUAL (UAV->DIRECTION (ITH-UAV i ENS)) b)
        (:call (uav-fix i) (ifix))
        (:call (uav-fix j) (jfix))
        (:call (lte-index-filter ifix jfix) nil)
        (:keep ens i j)
        )
  ;;:stable nil
  :use ((:instance escort-condition-implies
                   (ens ens)
                   (i i)
                   (j j))))

(def::pattern-hint shared-boundary
  (:and
   (:replicate (:commutes (equal A R) (A R)) (L R) (B A))
   ;; (equal A R)
   ;; (equal L B)
   (:equal L R)
   (:match A (UAV-right-boundary x))
   (:match B (UAV-right-boundary y))
   (:not (:equal x y))
   (:keep x y)
   )
  ;;:stable nil
  :use ((:instance shared-boundary
                   (x x)
                   (y y))))

;;
;;
;;

(defthm clean-up-equality
  (implies
   (and
    (integerp x)
    (integerp y))
   (iff (equal (- x) (- y))
        (equal x y))))

(defthm equal-common-addend
  (implies
   (and (rationalp x) (rationalp y) (rationalp z))
   (iff (equal (+ x y)
               (+ x z))
        (equal y z))))
 
(defthm equal-direction-reduction
  (iff (equal (UAV->DIRECTION x)
              (UAV->DIRECTION y))
       (or
        (and (equal (UAV->DIRECTION x) 1)
             (equal (UAV->DIRECTION y) 1))
        (and (equal (UAV->DIRECTION x) -1)
             (equal (UAV->DIRECTION y) -1)))))

(encapsulate
    ()

  (local (include-arithmetic))

  (defthm equal-right-perimeter-boundary-reduction
    (implies
     (and
      (sequential-id-list-p ens)
      (equal (len ens) (N)))
     (iff (equal (UAV-RIGHT-BOUNDARY (ITH-UAV I ENS)) (RIGHT-PERIMETER-BOUNDARY))
          (uav-id-equiv I (+ -1 (N)))))
    :hints (("Goal" :do-not-induct t
             :do-not '(preprocess)
             :nonlinearp t
             :in-theory (e/d (UAV-ID-P
                              RIGHT-PERIMETER-BOUNDARY
                              UAV-LEFT-BOUNDARY
                              segment-length
                              uav-id-equiv
                              uav-id-fix
                              UAV-right-boundary)
                             (EQUAL-UAV-ID-FIX-1-TO-UAV-ID-EQUIV)))))

  )

(in-theory (disable location-linear right-boundary-is-ordered-linear))
