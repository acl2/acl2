;;  
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")

(include-book "level-4-phase-abstraction")

;; ==================================================================
;;
;; phase count abstraction
;;
;; ==================================================================

;; -------------------------------------------------------------------
;; phase count (pcount)
;; -------------------------------------------------------------------

(defun weak-pcount-p (x)
  (declare (type t x))
  (and (consp x)
       (consp (cdr x))))

(defun pcount-p (x)
  (declare (type t x))
  (and (weak-pcount-p x)
       (phase-p (car x))
       (posp (cadr x))
       (null (cddr x))))

(defthm pcount-p-implies-weak-pcount-p
  (implies
   (pcount-p x)
   (weak-pcount-p x))
  :rule-classes (:forward-chaining))

(def::un pcount (phase count)
  (declare (xargs :signature ((t t) pcount-p)
                  :congruence ((phase-equiv pfix-equiv) equal)))
  (let ((phase (phase-fix phase))
        (count (pfix count)))
    (list phase count)))

(def::un pcount-fix (x)
  (declare (xargs :signature ((t) pcount-p)))
  (if (consp x)
      (let ((phase (phase-fix (car x))))
        (if (consp (cdr x))
            (list phase (pfix (cadr x)))
          (list phase 1)))
    (list :X 1)))

(defthm pcount-p-pcount-fix
  (implies
   (pcount-p x)
   (equal (pcount-fix x) x)))

(defun pcount-equiv (x y)
  (declare (type t x y))
  (equal (pcount-fix x)
         (pcount-fix y)))

(defthmd equal-pcount-fix
  (equal (equal (pcount-fix x) y)
         (and (pcount-p y)
              (pcount-equiv x y))))

(defequiv pcount-equiv)

(defcong pcount-equiv equal (pcount-fix x) 1)

(defthm pcount-equiv-pcount-fix
  (pcount-equiv (pcount-fix x) x))

(def::un pcount-phase (x)
  (declare (xargs :signature ((t) phase-p)
                  :congruence ((pcount-equiv) equal)))
  (if (consp x) (phase-fix (car x)) :X))

(defthm pcount-phase-pcount
  (equal (pcount-phase (pcount phase pcount))
         (phase-fix phase)))

(def::un pcount-count (x)
  (declare (xargs :signature ((t) posp)
                  :congruence ((pcount-equiv) equal)))
  (if (consp x)
      (if (consp (cdr x))
          (pfix (cadr x))
        1)
    1))

(defthm pcount-count-pcount
  (equal (pcount-count (pcount phase count))
         (pfix count)))

(defthmd pcount-equiv-reduction
  (iff (pcount-equiv x y)
       (and (phase-equiv (pcount-phase x)
                         (pcount-phase y))
            (pfix-equiv  (pcount-count x)
                         (pcount-count y))))
  :hints (("Goal" :in-theory (enable equal-phase-fix
                                     equal-pfix))))

(def-pattern-match-constructor pcount weak-pcount-p (pcount-phase pcount-count))

(def-pattern-match-constructor pos any-p (pfix))
(def-pattern-match-constructor nat any-p (nfix))

(in-theory (disable pcount (pcount) pcount-phase pcount-count))
(in-theory (disable weak-pcount-p pcount-p pcount-fix pcount-equiv))

;; -------------------------------------------------------------------
;; pcount-parity-p
;; -------------------------------------------------------------------

(defun pcount-parity-p (x)
  (declare (type t x))
  (and (pcount-p x)
       (implies
        (memberp (pcount-phase x) '(:X :W))
        (odd-p (pcount-count x)))
       (implies
        (memberp (pcount-phase x) '(:Y :Z))
        (even-p (pcount-count x)))
       (implies
        (equal (pcount-phase x) :O)
        (equal (pcount-count x) 1))
       (implies
        (equal (pcount-phase x) :W)
        (<= 3 (pcount-count x)))
       (implies
        (memberp (pcount-phase x) '(:Z :Y))
        (<= 2 (pcount-count x)))))

(defthm pcount-parity-p-implies
  (implies
   (pcount-parity-p x)
   (pcount-p x))
  :rule-classes (:forward-chaining))

(defthm pcount-parity-p-implies-2<=count
  (implies
   (and
    (memberp (pcount-phase x) '(:Z :Y))
    (pcount-parity-p x))
   (<= 2 (pcount-count x)))
  :rule-classes ((:linear :backchain-limit-lst nil) 
                 (:rewrite :backchain-limit-lst nil)
                 ))

(defthm pcount-parity-p-implies-3<=count
  (implies
   (and
    (equal (pcount-phase x) :W)
    (pcount-parity-p x))
   (<= 3 (pcount-count x)))
  :rule-classes ((:linear :backchain-limit-lst nil)
                 (:rewrite :backchain-limit-lst nil)
                 ))

(defthm pcount-parity-p-implies-oddp
  (implies
   (and
    (memberp (pcount-phase x) '(:X :W))
    (pcount-parity-p x))
   (not (even-p (pcount-count x))))
  :rule-classes ((:rewrite :backchain-limit-lst nil)))

(defthm pcount-parity-p-implies-evenp
  (implies
   (and
    (memberp (pcount-phase x) '(:Y :Z))
    (pcount-parity-p x))
   (even-p (pcount-count x)))
  :rule-classes ((:rewrite :backchain-limit-lst nil)
                 ))

(defthm even-p-pcount-count-rewrite
  (implies
   (and
    (memberp (pcount-phase x) '(:O :X :W :Y :Z))
    (pcount-parity-p x))
   (equal (even-p (pcount-count x))
          (not (memberp (pcount-phase x) '(:O :X :W)))))
  :rule-classes ((:rewrite :backchain-limit-lst nil)
                 ))

(defthm pcount-parity-p-implies-1
  (implies
   (and
    (equal (pcount-phase x) :O)
    (pcount-parity-p x))
   (equal (pcount-count x) 1))
  :rule-classes ((:rewrite :backchain-limit-lst nil)
                 ))

(defthm implies-pcount-parity-p
  (implies
   (and (pcount-p x)
        (implies
         (memberp (pcount-phase x) '(:X :W))
         (not (even-p (double-rewrite (pcount-count x)))))
        (implies
         (memberp (pcount-phase x) '(:Y :Z))
         (even-p (double-rewrite (pcount-count x))))
        (implies
         (equal (pcount-phase x) :O)
         (equal (pcount-count x) 1))
        (implies
         (equal (pcount-phase x) :W)
         (<= 3 (pcount-count x)))
        (implies
         (memberp (pcount-phase x) '(:Z :Y))
         (<= 2 (pcount-count x))))
   (pcount-parity-p x))
  :rule-classes (:rewrite))

(in-theory (disable pcount-parity-p))

(defthm pos-odd-not-3-pcount-count
  (implies
   (and
    (not (equal (pcount-count x) 3))
    (<= 3 (pcount-count x))
    (not (even-p (double-rewrite (pcount-count x)))))
   (<= 5 (pcount-count x)))
  :rule-classes (:linear :rewrite)
  :hints (("Goal" :use (:instance pos-odd-not-3-implication
                                  (x (pcount-count x))))))
  
(defthm pos-even-not-2-pcount-count
  (implies
   (and
    (not (equal (pcount-count x) 2))
    (even-p (double-rewrite (pcount-count x))))
   (<= 4 (pcount-count x)))
  :rule-classes (:linear :rewrite)
  :hints (("Goal" :use (:instance pos-even-not-2-implication
                                  (x (pcount-count x))))))

(defthm non-zero-even-is-gte-pcount-count
  (implies
   (and
    (not (equal (pcount-count x) 0))
    (even-p (double-rewrite (pcount-count x))))
   (<= 2 (pcount-count x)))
  :rule-classes (:linear :rewrite)
  :hints (("Goal" :use (:instance non-zero-even-is-gte
                                  (x (pcount-count x))))))

(defthm pos-odd-not-1-pcount-count
  (implies
   (and
    (not (equal (pcount-count x) 1))
    (odd-p (pcount-count x)))
   (<= 3 (pcount-count x)))
  :rule-classes (:linear :rewrite)
  :hints (("Goal" :use (:instance pos-odd-not-1-implication
                                  (x (pcount-count x))))))

;; -------------------------------------------------------------------
;; nzpcount-p
;; -------------------------------------------------------------------

(defun nzpcount-p (x)
  (declare (type t x))
  (pcount-parity-p x))

(defthm nzpcount-implies
  (implies
   (nzpcount-p x)
   (pcount-parity-p x))
  :rule-classes (:forward-chaining))

(defthm implies-nzpcount
  (implies
   (pcount-parity-p x)
   (nzpcount-p x))
  :rule-classes (:rewrite :forward-chaining))

(in-theory (disable nzpcount-p))

;; -------------------------------------------------------------------
;; pcount-listp
;; -------------------------------------------------------------------

(defun pcount-listp (x)
  (declare (type t x))
  (if (not (consp x)) (null x)
    (and (pcount-p (car x))
         (pcount-listp (cdr x)))))

(def::signature tcons (pcount-listp pcount-p) pcount-listp)

(defthm pcount-listp-append
  (implies
   (pcount-listp x)
   (iff (pcount-listp (append x y))
        (pcount-listp y))))

(defun pcount-len (x)
  (if (not (consp x)) 0
    (let ((entry (car x)))
      (+ (pcount-count entry)
         (pcount-len (cdr x))))))

(defthm pcount-listp-implies-true-listp
  (implies
   (pcount-listp x)
   (true-listp x))
  :rule-classes (:forward-chaining))

(def::un fix-pcount-list (list)
  (declare (xargs :signature ((t) pcount-listp)))
  (if (not (consp list)) nil
    (cons (pcount-fix (car list))
          (fix-pcount-list (cdr list)))))

(defthm fix-pcount-list-pcount-listp
  (implies
   (pcount-listp list)
   (equal (fix-pcount-list list) list)))

(defun pcount-list-equiv (x y)
  (equal (fix-pcount-list x)
         (fix-pcount-list y)))

(defequiv pcount-list-equiv)

(defcong pcount-list-equiv equal (fix-pcount-list x) 1)
  
(defthm pcount-list-equiv-fix-pcount-list
  (pcount-list-equiv (fix-pcount-list x) x))
 
(defthmd open-pcount-list-equiv
  (and
   (implies
    (or (consp x) (consp y))
    (equal (pcount-list-equiv x y)
           (and (iff (consp x) (consp y))
                (pcount-equiv (car x) (car y))
                (pcount-list-equiv (cdr x) (cdr y)))))
   (implies
    (or (not (consp x)) (not (consp y)))
    (equal (pcount-list-equiv x y)
           (and (not (consp x)) (not (consp y))))))
  :hints (("Goal" :expand (fix-pcount-list y)
           :in-theory (enable equal-pcount-fix))))

(in-theory (disable pcount-list-equiv))

(defthm weak-open-pcount-list-equiv
  (and
   (equal (pcount-list-equiv y (cons a x))
          (and (consp y)
               (pcount-equiv a (car y))
               (pcount-list-equiv x (cdr y))))
   (equal (pcount-list-equiv (cons a x) y)
          (and (consp y)
               (pcount-equiv a (car y))
               (pcount-list-equiv x (cdr y))))
   (implies
    (or (not (consp x)) (not (consp y)))
    (equal (pcount-list-equiv x y)
           (and (not (consp x)) (not (consp y))))))
  :hints (("Goal" :in-theory (enable open-pcount-list-equiv equal-boolean))))

(defthm pcount-list-equiv-induction t
  :rule-classes ((:induction :pattern (pcount-list-equiv x y)
                             :scheme (list-equiv-induction x y))))

(defcong pcount-list-equiv equal (consp x) 1
  :hints (("Goal" :in-theory (enable equal-boolean open-pcount-list-equiv))))

(defcong pcount-list-equiv pcount-equiv (car x) 1)
(defcong pcount-list-equiv pcount-list-equiv (cdr x) 1)
(defcong pcount-list-equiv pcount-list-equiv (cons a x) 2)
(defcong pcount-equiv      pcount-list-equiv (cons a x) 1)
(defcong pcount-list-equiv pcount-list-equiv (append x y) 1)
(defcong pcount-list-equiv pcount-list-equiv (append x y) 2)

(defcong pcount-list-equiv pcount-equiv (tcar x) 1)
(defcong pcount-list-equiv pcount-list-equiv (tcdr x) 1)
(defcong pcount-list-equiv pcount-list-equiv (tcons x a) 1)
(defcong pcount-equiv pcount-list-equiv (tcons x a) 2)

(defcong pcount-list-equiv equal (len x) 1)

(def::und nth-pcount-entry (x entry)
  (declare (xargs :signature ((t t) concrete-phase-p)
                  :signature-hints (("Goal" :in-theory (enable phase-bit concrete-phase-p)))
                  :congruence ((nfix-equiv pcount-equiv) equal)))
  (let ((x (nfix x)))
    (if (not (< x (pcount-count entry))) (phase-bit)
      (let ((phase (pcount-phase entry)))
        (case phase
          (:W (if (even-p x) :O :X))
          (:X (if (even-p x) :X :O))
          (:Y (if (even-p x) :O :X))
          (:Z (if (even-p x) :X :O))
          (t phase))))))

(defthm nth-pcount-entry-fix-zp-count
  (implies
   (and (syntaxp (not (quotep x)))
        (zp x))
   (equal (nth-pcount-entry x entry)
          (nth-pcount-entry 0 entry)))
  :hints (("Goal" :in-theory (enable zp nfix nth-pcount-entry))))

(def::un nth-pcount (x list)
  (declare (xargs :signature ((t t) concrete-phase-p)
                  :measure (len list)
                  :congruence ((nfix-equiv pcount-list-equiv) equal)))
  (if (not (consp list)) (phase-bit)
    (let ((entry (pcount-fix (car list))))
      (let ((x (nfix x)))
        (if (equal (pcount-count entry) 0)
            (nth-pcount x (cdr list))
          (if (zp x) (leading-phase (pcount-phase entry))
            (if (< x (pcount-count entry)) (nth-pcount-entry x entry) 
              (nth-pcount (- x (pcount-count entry)) (cdr list)))))))))

(defthm LEADING-PHASE-PCOUNT-PHASE
  (implies
   (< 0 (PCOUNT-COUNT A))
   (EQUAL (LEADING-PHASE (PCOUNT-PHASE A))
          (NTH-PCOUNT-ENTRY 0 A)))
  :hints (("Goal" :in-theory (enable LEADING-PHASE NTH-PCOUNT-ENTRY))))

(defthm nth-pcount-tcons
  (equal (nth-pcount i (tcons x a))
         (let ((i (nfix i)))
           (if (< i (pcount-len x))
               (nth-pcount i x)
             (if (< i (+ (pcount-len x) (pcount-count a)))
                 (nth-pcount-entry (- i (pcount-len x)) a)
               (phase-bit)))))
  :hints (("GOal" :induct (list (tcons x a)
                                (nth-pcount i x)))))

(defthm nth-pcount-out-of-range
  (implies
   (<= (pcount-len x) (nfix i))
   (equal (nth-pcount i x) (phase-bit))))

(defthm nth-pcount-zero
  (implies
   (and (syntaxp (not (quotep x)))
        (zp x))
   (equal (nth-pcount x z)
          (nth-pcount 0 z)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable zp nfix)
           :expand (nth-pcount x z))))

(defthm open-nth-pcount
  (and
   (implies
    (and
     (not (zp x))
     (syntaxp (implies (consp list) (or (equal (car list) 'cdr) (equal (car list) 'cons))))
     (not (equal (pcount-count (car list)) 0)))
    (equal (nth-pcount x list)
           (if (not (consp list)) (phase-bit)
             (let ((entry (pcount-fix (car list))))
               (let ((x (nfix x)))
                 (if (< x (pcount-count entry)) (nth-pcount-entry x entry) 
                   (nth-pcount (- x (pcount-count entry)) (cdr list))))))))
   (implies
    (and
     (zp x)
     (syntaxp (implies (consp list) (or (equal (car list) 'cdr) (equal (car list) 'cons))))
     (not (equal (pcount-count (car list)) 0)))
    (equal (nth-pcount x list)
           (if (not (consp list)) (phase-bit)
             (let ((entry (pcount-fix (car list))))
               (leading-phase (pcount-phase entry))))))))

(defthmd open-nth-pcount-consp
  (implies
   (consp list)
   (equal (nth-pcount x list)
          (let ((entry (pcount-fix (car list))))
            (let ((x (nfix x)))
              (if (equal (pcount-count entry) 0)
                  (nth-pcount x (cdr list))
                (if (zp x) (leading-phase (pcount-phase entry))
                  (if (< x (pcount-count entry)) (nth-pcount-entry x entry) 
                    (nth-pcount (- x (pcount-count entry)) (cdr list)))))))))
  :hints (("Goal" :in-theory (enable nth-pcount))))

(defthm open-nth-pcount-safe
  (and
   (implies
    (not (consp list))
    (equal (nth-pcount x list)
           (phase-bit)))
   (equal (nth-pcount x (cons a z))
          (let ((entry (pcount-fix a)))
            (let ((x (nfix x)))
              (if (equal (pcount-count entry) 0)
                  (nth-pcount x z)
                (if (zp x) (leading-phase (pcount-phase entry))
                  (if (< x (pcount-count entry)) (nth-pcount-entry x entry) 
                    (nth-pcount (- x (pcount-count entry)) z)))))))))
  
(in-theory (disable (:definition nth-pcount)))

;; ----------------------------------------
;;
;; pcount-list-equiv reduction
;;
;; ----------------------------------------

(include-book "centaur/misc/universal-equiv" :dir :system)

;; (def-universal-equiv nth-pcount-entry-equiv
;;   :qvars (i)
;;   :equiv-terms ((equal (nth-pcount-entry i x))))

;; (defrefinement pcount-equiv nth-pcount-entry-equiv
;;   :hints (("Goal" :expand (NTH-PCOUNT-ENTRY-EQUIV X Y))))

;; (defun pcount-phase-equiv (x y)
;;   (and (equal (pcount-count x)
;;               (pcount-count y))
;;        (nth-pcount-entry-equiv x y)))

;; (defequiv pcount-phase-equiv)

;; (defrefinement pcount-equiv pcount-phase-equiv)

(def-universal-equiv nth-pcount-list-equiv
  :qvars (i)
  :equiv-terms ((equal (nth-pcount i x))))

;; (defun nth-pcount-bad-guy (x y)
;;   (declare (xargs :measure (max (len x) (len y))))
;;   (if (or (not (consp x)) (not (consp y))) 0
;;     (if (not (pcount-phase-equiv (car x) (car y))) (nth-pcount-entry-equiv-witness (car x) (car y))
;;       (+ (pcount-count (car x)) (nth-pcount-bad-guy (cdr x) (cdr y))))))

;; (defthm nth-pcount-bad-guy-property
;;   (implies
;;    (and
;;     (equal (pcount-len x)
;;            (pcount-len y))
;;     (equal (nth-pcount (nth-pcount-bad-guy x y) x)
;;            (nth-pcount (nth-pcount-bad-guy x y) y)))
;;    (pcount-phase-list-equiv x y))
;;   :hints (("GOal" :induct (nth-pcount-bad-guy x y))))

;; (defthm natp-nth-pcount-bad-guy
;;   (natp (nth-pcount-bad-guy x y)))

(defcong pcount-list-equiv equal (pcount-len x) 1)

;; (defthm nth-pcount-bad-guy-equiv
;;   (implies
;;    (pcount-list-equiv x y)
;;    (equal (nth-pcount-bad-guy x y)
;;           (min (pcount-len x)
;;                (pcount-len y))))
;;   :hints (("Goal" :induct (pcount-list-equiv x y)
;;            :in-theory (enable pcount-equiv-implies-all-NTH-PCOUNT-ENTRY-EQUIV
;;                               OPEN-PCOUNT-LIST-EQUIV))))

(defthm nth-pcount-len-x
  (equal (nth-pcount (pcount-len x) x)
         (phase-bit)))

;; (include-book "arithmetic-5/top" :dir :system)
;; (defthm pcount-equiv-nth-pcount-bad-guy
;;   (implies
;;    (and
;;     (not (pcount-list-equiv x y))
;;     (equal (len x) (len y))
;;     (equal (pcount-len x) (pcount-len y)))
;;    (not (equal (nth-pcount (nth-pcount-bad-guy x y) x)
;;                (nth-pcount (nth-pcount-bad-guy x y) y))))
;;   :hints (("Goal" :in-theory (enable equal-pcount-fix OPEN-PCOUNT-LIST-EQUIV)
;;            :induct (nth-pcount-bad-guy x y))))

;; (defthmd pcount-list-equiv-reduction
;;   (iff (pcount-list-equiv x y)
;;        (and (equal (len x) (len y))
;;             (equal (pcount-len x) (pcount-len y))
;;             (equal (nth-pcount (nth-pcount-bad-guy x y) x)
;;                    (nth-pcount (nth-pcount-bad-guy x y) y))))
;;   :hints (("Goal" :do-not-induct t)))

;; -------------------------------------------------------------------
;; nzpcount-listp
;; -------------------------------------------------------------------

(defun pcount-parity-listp (x)
  (declare (type t x))
  (if (not (consp x)) (null x)
    (and (pcount-parity-p (car x))
         (pcount-parity-listp (cdr x)))))

(defun nzpcount-listp (x)
  (declare (type t x))
  (if (not (consp x)) (null x)
    (and (nzpcount-p (car x))
         (nzpcount-listp (cdr x)))))

(defthm nzpcount-listp-implication
  (implies
   (nzpcount-listp x)
   (pcount-parity-listp x))
  :rule-classes (:forward-chaining))

(defthm pcount-parity-listp-implication
  (implies
   (pcount-parity-listp x)
   (pcount-listp x))
  :rule-classes (:forward-chaining))

;; -------------------------------------------------------------------
;; well-formed p-count sequence
;; -------------------------------------------------------------------

;; (def::un strip-phase (x)
;;   (declare (xargs :signature ((t) phase-listp)
;;                   :congruence ((pcount-list-equiv) equal)))
;;   (if (not (consp x)) nil
;;     (cons (pcount-phase (car x))
;;           (strip-phase (cdr x)))))

(def::und wf-pcount-final (R)
  (declare (type t R)
           (xargs :congruence ((phase-equiv) equal)))
  (memberp (phase-fix R) '(:O :W :X :Y :Z)))

(defcong trailing-phase-equiv equal (wf-pcount-final r) 1
  :hints (("Goal" :in-theory (enable trailing-phase-equiv
                                     trailing-phase
                                     wf-pcount-final))))

(def::und wf-pcount-initial (L)
  (declare (type t L)
           (xargs :congruence ((phase-equiv) equal)))
  (memberp (phase-fix L) '(:O :W :X :Y :Z)))

(def::und wf-pcount-only (v)
  (declare (type t v)
           (xargs :congruence ((phase-equiv) equal)))
  (memberp (phase-fix v) '(:W :X :Y :Z)))

;; :X = [P] X (O X)* [N]
;; :W = [N] O (X O)+ [P]
;; :Y = [N] O X (O X)* [N]
;; :Z = [P] X O (X O)* [P]
;; :O = [N] O [P]

(def::und wf-pcount-sequence-step (L R)
  (declare (type t L R)
           (xargs :congruence ((phase-equiv phase-equiv) equal))
           )
  (let ((L (phase-fix L))
        (R (phase-fix R)))
    (or
     (and (memberp L '(:X :Y)) (equal R :N))
     (and (memberp L '(:W :Z)) (equal R :P))
     (and (equal L :O)         (equal R :P))
     (and (equal L :P)         (memberp R '(:X :Z)))
     (and (equal L :N)         (memberp R '(:O :Y :W)))
     )))

(defcong trailing-phase-equiv equal (wf-pcount-sequence-step v x) 1
  :hints (("GOal" :in-theory (enable trailing-phase-equiv
                                     trailing-phase
                                     wf-pcount-sequence-step))))

(def::und wf-pcount-sequence-body (list)
  (declare (type t list)
           (xargs :congruence ((pcount-list-equiv) equal)
                  :congruence-hints (("Goal" :in-theory (enable open-PCOUNT-LIST-EQUIV)))))
  (if (not (consp list)) t
    (if (not (consp (cdr list))) t
      (let ((L (pcount-phase (car list)))
            (R (pcount-phase (cadr list))))
        (and (wf-pcount-sequence-step L R)
             (wf-pcount-sequence-body (cdr list)))))))

(def::und wf-pcount-sequence-suffix (x list)
  (declare (type t list x)
           (xargs :congruence ((phase-equiv pcount-list-equiv) equal)))
  (and (wf-pcount-sequence-body list)
       (if (consp list)
           (and (wf-pcount-sequence-step x (pcount-phase (car list)))
                (wf-pcount-final (pcount-phase (tcar list))))
         (wf-pcount-final x))))

(def::un wf-pcount-sequence-rec (L list)
  (declare (type t list)
           (xargs :congruence ((phase-equiv pcount-list-equiv) equal)))
  (if (not (consp list)) t
    (let ((R (pcount-phase (car list))))
      (and (wf-pcount-sequence-step L R)
           (wf-pcount-sequence-rec R (cdr list))))))

(defcong trailing-phase-equiv equal (wf-pcount-sequence-rec L list) 1
  :hints (("Goal" :expand (:free (L) (wf-pcount-sequence-rec L list)))))

(defthmd wf-pcount-sequence-body-reduction
  (equal (wf-pcount-sequence-body list)
         (if (consp list)
             (wf-pcount-sequence-rec (pcount-phase (car list)) (cdr list))
           t))
  :hints (("Goal" :in-theory (enable wf-pcount-sequence-body))))

(defcong trailing-phase-equiv equal (wf-pcount-sequence-suffix x list) 1
  :hints (("Goal" :in-theory (enable wf-pcount-sequence-suffix))))

(defthm wf-pcount-sequence-suffix-cons
  (equal (wf-pcount-sequence-suffix a (cons x list))
         (and (wf-pcount-sequence-suffix (pcount-phase x) list)
              (wf-pcount-sequence-step a (pcount-phase x))))
  :hints (("Goal" :in-theory (enable wf-pcount-sequence-body wf-pcount-sequence-suffix))))

(defthm wf-pcount-sequence-suffix-consp
  (implies
   (consp list)
   (equal (wf-pcount-sequence-suffix a list)
          (and (wf-pcount-sequence-suffix (pcount-phase (car list)) (cdr list))
               (wf-pcount-sequence-step a (pcount-phase (car list))))))
  :hints (("Goal" :in-theory (enable wf-pcount-sequence-body wf-pcount-sequence-suffix))))

(defthm wf-pcount-sequence-suffix-not-consp
  (implies
   (not (consp list))
   (equal (wf-pcount-sequence-suffix x list)
          (wf-pcount-final x)))
  :hints (("Goal" :in-theory (enable wf-pcount-sequence-body  wf-pcount-sequence-suffix))))

(defthmd wf-pcount-sequence-suffix-reduction
  (equal (wf-pcount-sequence-suffix a list)
         (if (consp list)
             (and (wf-pcount-sequence-rec a list)
                  (wf-pcount-final (pcount-phase (tcar list))))
           (wf-pcount-final a)))
  :hints (("GOal" :in-theory (disable WF-PCOUNT-SEQUENCE-SUFFIX-CONSP))))

(def::und wf-pcount-sequence (list)
  (declare (type t list)
           (xargs :congruence ((pcount-list-equiv) equal)))
  (if (not (consp list)) nil
    (let ((L (pcount-phase (car list))))
      (if (not (consp (cdr list))) (wf-pcount-only L)
        (and (wf-pcount-initial L)
             (wf-pcount-sequence-suffix L (cdr list)))))))

;; -------------------------------------------------------------------
;; weak p-count sequence
;; -------------------------------------------------------------------

(def::und weak-pcount-final (R)
  (declare (type t R)
           (xargs :congruence ((phase-equiv) equal)))
  (memberp (phase-fix R) '(:O :W :X :Y :Z)))

(defcong trailing-phase-equiv equal (weak-pcount-final x) 1
  :hints (("Goal" :in-theory (enable trailing-phase-equiv
                                     trailing-phase
                                     weak-pcount-final))))

(defthm wf-pcount-final-implies-weak-pcount-final
  (implies
   (wf-pcount-final r)
   (weak-pcount-final r))
  :hints (("Goal" :in-theory (enable wf-pcount-final weak-pcount-final)))
  :rule-classes (:forward-chaining))

(defthm weak-pcount-final-implies-wf-pcount-final
  (implies
   (weak-pcount-final r)
   (wf-pcount-final r))
  :hints (("Goal" :in-theory (enable wf-pcount-final weak-pcount-final)))
  :rule-classes (:forward-chaining))

(def::und weak-pcount-initial (L)
  (declare (type t L)
           (xargs :congruence ((phase-equiv) equal)))
  (memberp (phase-fix L) '(:O :W :X :Y :Z)))

(defthm wf-pcount-initial-implies-weak-pcount-initial
  (implies
   (wf-pcount-initial r)
   (weak-pcount-initial r))
  :hints (("Goal" :in-theory (enable wf-pcount-initial weak-pcount-initial)))
  :rule-classes (:forward-chaining))

(defthm weak-pcount-initial-implies-wf-pcount-initial
  (implies
   (weak-pcount-initial r)
   (wf-pcount-initial r))
  :hints (("Goal" :in-theory (enable wf-pcount-initial weak-pcount-initial)))
  :rule-classes (:forward-chaining))

(def::und weak-pcount-only (v)
  (declare (type t v)
           (xargs :congruence ((phase-equiv) equal)))
  (memberp (phase-fix v) '(:W :X :Y :Z)))

(defthm wf-pcount-only-implies-weak-pcount-only
  (implies
   (wf-pcount-only r)
   (weak-pcount-only r))
  :hints (("Goal" :in-theory (enable wf-pcount-only weak-pcount-only)))
  :rule-classes (:forward-chaining))

(defthm weak-pcount-only-implies-wf-pcount-only
  (implies
   (weak-pcount-only r)
   (wf-pcount-only r))
  :hints (("Goal" :in-theory (enable wf-pcount-only weak-pcount-only)))
  :rule-classes (:forward-chaining))

(def::und weak-pcount-sequence-step (L R)
  (declare (type t L R)
           (xargs :congruence ((phase-equiv phase-equiv) equal))
           )
  (let ((L (phase-fix L))
        (R (phase-fix R)))
    (or
     (and (memberp L '(:N :X :Y))    (memberp R '(:N :O :Y :W)))
     (and (memberp L '(:P :O :W :Z)) (memberp R '(:X :P :Z)))
     )))

(defthm wf-pcount-sequence-step-implies-weak-pcount-sequence-step
  (implies
   (wf-pcount-sequence-step L R)
   (weak-pcount-sequence-step L R))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable wf-pcount-sequence-step
                                     weak-pcount-sequence-step))))

(defcong trailing-phase-equiv equal (weak-pcount-sequence-step L R) 1
  :hints (("Goal" :in-theory (enable trailing-phase-equiv
                                     trailing-phase
                                     weak-pcount-sequence-step))))

(def::und weak-pcount-sequence-body (list)
  (declare (type t list)
           (xargs :congruence ((pcount-list-equiv) equal)))
  (if (not (consp list)) t
    (if (not (consp (cdr list))) t
      (let ((L (pcount-phase (car list)))
            (R (pcount-phase (cadr list))))
        (and (weak-pcount-sequence-step L R)
             (weak-pcount-sequence-body (cdr list)))))))

(def::und weak-pcount-sequence-suffix (x list)
  (declare (type t list x)
           (xargs :congruence ((phase-equiv pcount-list-equiv) equal)))
  (and (weak-pcount-sequence-body list)
       (if (consp list)
           (and (weak-pcount-sequence-step x (pcount-phase (car list)))
                (weak-pcount-final (pcount-phase (tcar list))))
         (weak-pcount-final x))))

(defcong trailing-phase-equiv equal (weak-pcount-sequence-suffix x list) 1
  :hints (("Goal" :in-theory (enable weak-pcount-sequence-suffix))))

(defthm weak-pcount-sequence-suffix-cons
  (equal (weak-pcount-sequence-suffix a (cons x list))
         (and (weak-pcount-sequence-suffix (pcount-phase x) list)
              (weak-pcount-sequence-step a (pcount-phase x))))
  :hints (("Goal" :in-theory (enable weak-pcount-sequence-body weak-pcount-sequence-suffix))))

(defthm weak-pcount-sequence-suffix-consp
  (implies
   (consp list)
   (equal (weak-pcount-sequence-suffix a list)
          (and (weak-pcount-sequence-suffix (pcount-phase (car list)) (cdr list))
               (weak-pcount-sequence-step a (pcount-phase (car list))))))
  :hints (("Goal" :in-theory (enable weak-pcount-sequence-body weak-pcount-sequence-suffix))))

(defthm weak-pcount-sequence-suffix-not-consp
  (implies
   (not (consp list))
   (equal (weak-pcount-sequence-suffix x list)
          (weak-pcount-final x)))
  :hints (("Goal" :in-theory (enable weak-pcount-sequence-body  weak-pcount-sequence-suffix))))

(def::un weak-pcount-sequence-rec (L list)
  (declare (type t list)
           (xargs :congruence ((phase-equiv pcount-list-equiv) equal)))
  (if (not (consp list)) t
    (let ((R (pcount-phase (car list))))
      (and (weak-pcount-sequence-step L R)
           (weak-pcount-sequence-rec R (cdr list))))))

(defcong trailing-phase-equiv equal (weak-pcount-sequence-rec L list) 1
  :hints (("Goal" :expand (:free (L) (weak-pcount-sequence-rec L list)))))

(defthmd weak-pcount-sequence-body-reduction
  (equal (weak-pcount-sequence-body list)
         (if (consp list)
             (weak-pcount-sequence-rec (pcount-phase (car list)) (cdr list))
           t))
  :hints (("Goal" :in-theory (enable weak-pcount-sequence-body))))

;; (def::und weak-pcount-sequence-suffix (x list)
;;   (declare (type t list x)
;;            (xargs :congruence ((phase-equiv pcount-list-equiv) equal)))
;;   (if (consp list)
;;       (and (weak-pcount-sequence-rec x list)
;;            (weak-pcount-final (pcount-phase (tcar list))))
;;     (weak-pcount-final x)))

;; (defthm weak-pcount-sequence-rec-append
;;   (equal (weak-pcount-sequence-rec a (append x y))
;;          (if (consp x)
;;              (and (weak-pcount-sequence-rec a x)
;;                   (if (consp y)
;;                       (and (weak-pcount-sequence-step (pcount-phase (tcar x)) (pcount-phase (car y)))
;;                            (weak-pcount-sequence-rec (pcount-phase (car y)) (cdr y)))
;;                     t))
;;            (weak-pcount-sequence-rec a y))))
  
;; (def::und weak-pcount-sequence-append (x y)
;;   (declare (type t x y)
;;            (xargs :congruence ((pcount-list-equiv pcount-list-equiv) equal)))
;;   (if (consp x)
;;       (and (weak-pcount-sequence-rec (pcount-phase (car x)) (cdr x))
;;            (if (consp y)
;;                (and (weak-pcount-sequence-step (pcount-phase (tcar x)) (pcount-phase (car y)))
;;                     (weak-pcount-sequence-rec (pcount-phase (car y)) (cdr y)))
;;              t))
;;     (weak-pcount-sequence-body y)))

(defthmd consp-append
  (iff (consp (append x y))
       (or (consp x)
           (consp y))))

(defthmd car-append
  (equal (car (append x y))
         (if (consp x)
             (car x)
           (car y))))

(defthmd cdr-append
  (equal (cdr (append x y))
         (if (consp x)
             (append (cdr x) y)
           (cdr y))))

;; (defthm weak-pcount-sequence-body-append-to-weak-pcount-sequence-append
;;   (equal (weak-pcount-sequence-body (append x y))
;;          (weak-pcount-sequence-append x y))
;;   :hints (("Goal" :do-not-induct t
;;            :in-theory (enable
;;                        consp-append
;;                        car-append
;;                        weak-pcount-sequence-body-reduction
;;                        weak-pcount-sequence-append))))

;; (defthm weak-pcount-sequence-append-reduction
;;   (equal (weak-pcount-sequence-append x y)
;;          (if (consp x)
;;              (and (weak-pcount-sequence-body x)
;;                   (weak-pcount-sequence-rec (pcount-phase (tcar x)) y))
;;            (weak-pcount-sequence-body y)))
;;   :hints (("Goal" :in-theory (enable weak-pcount-sequence-append
;;                                      weak-pcount-sequence-body-reduction)
;;            :do-not-induct t)))

(defthm weak-pcount-sequence-rec-append
  (iff (weak-pcount-sequence-rec a (append x y))
       (if (consp x)
           (and (weak-pcount-sequence-rec a x)
                (weak-pcount-sequence-rec (pcount-phase (tcar x)) y))
         (weak-pcount-sequence-rec a y))))

(defthmd weak-pcount-sequence-suffix-reduction
  (equal (weak-pcount-sequence-suffix a list)
         (if (consp list)
             (and (weak-pcount-sequence-rec a list)
                  (weak-pcount-final (pcount-phase (tcar list))))
           (weak-pcount-final a)))
  :hints (("GOal" :in-theory (disable WEAK-PCOUNT-SEQUENCE-SUFFIX-CONSP))))

(def::und weak-pcount-sequence (list)
  (declare (type t list)
           (xargs :congruence ((pcount-list-equiv) equal)))
  (if (not (consp list)) nil
    (let ((L (pcount-phase (car list))))
      (if (not (consp (cdr list))) (weak-pcount-only L)
        (and (weak-pcount-initial L)
             (weak-pcount-sequence-suffix L (cdr list)))))))

;; -------------------------------------------------------------------
;; p-count
;; -------------------------------------------------------------------

(def::un p-count (x)
  (declare (xargs :signature ((t) integerp phase-p t)))
  (if (not (consp x)) (mv -1 :X nil)
    (let ((entry (phase-fix (car x))))
      (if (not (equal entry :P)) (mv 0 entry (cdr x))
        (mv-let (n a x) (p-count (cdr x))
          (mv (1+ n) a x))))))

(defthm p-count-lower-bound
  (<= -1 (val 0 (p-count x)))
  :rule-classes :linear)

(def::signature p-count (phase-listp) t t phase-listp)
(def::signature p-count (concrete-phase-listp) t concrete-phase-p concrete-phase-listp)

(defthm len-p-count
  (equal (len (val 2 (p-count x)))
         (+ (len x) -1 (- (val 0 (p-count x))))))

(defthm p-count-bounds
  (and
   (< (val 0 (p-count x)) (len x))
   (<= (len (val 2 (p-count x))) (len x))
   (implies
    (< 0 (val 0 (p-count x)))
    (< (len (val 2 (p-count x))) (len x))))
  :rule-classes :linear)

;; Unnecessarily painful.
(defthmd val1-p-count-as-nth-phase
  (implies
   (and
    (wf-phase-sequence-suffix :P x)    
    (<= 0 (val 0 (p-count x))))
   (equal (val 1 (p-count x))
          (nth-phase (val 0 (p-count x)) x)))
  :hints ((and stable-under-simplificationp
               '(:expand (P-COUNT (CDR X))))))

(defthm nth-phase-of-p-pcount
  (implies
   (< (nfix i) (val 0 (p-count x)))
   (equal (nth-phase i x) :P)))

(defthm nth-phase-over-p-count
  (implies
   (<= 0 (val 0 (p-count x)))
   (phase-equiv (nth-phase i (val 2 (p-count x)))
                (nth-phase (+ (nfix i) 1 (val 0 (p-count x))) x)))
  :hints (("Goal" :in-theory (disable (:definition p-count)))
          (and stable-under-simplificationp
               '(:expand ((p-count x))))
          (and stable-under-simplificationp
               '(:expand ((p-count (cdr x)))))
          ))

(defthm natp-p-count
  (implies
   (consp x)
   (natp (val 0 (p-count x))))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((p-count x)))))
   
(defthm val1-p-count-as-phase
  (implies
   (wf-phase-sequence-suffix :P x)
   (phase-equiv (val 1 (p-count x)) :X))
  :hints (("Goal" :in-theory (enable WF-PHASE-SEQUENCE-STEP))))

(theory-invariant
 (incompatible
  (:rewrite val1-p-count-as-phase)
  (:rewrite val1-p-count-as-nth-phase)))                              

(defthm wf-phase-sequence-p-count
  (implies
   (wf-phase-sequence-suffix :P x)
   (and (natp (val 0 (p-count x)))
        (wf-phase-sequence-step :P (val 1 (p-count x)))
        (wf-pcount-sequence-step :P (val 1 (p-count x)))
        (implies
         (phase-equiv phase (val 1 (p-count x)))
         (wf-phase-sequence-suffix phase (val 2 (p-count x))))))
  :hints (("Goal" :in-theory (enable WF-PHASE-SEQUENCE-STEP
                                     equal-phase-fix))))

(in-theory (disable p-count))

;; -------------------------------------------------------------------
;; n-count
;; -------------------------------------------------------------------

(def::un n-count (x)
  (declare (xargs :signature ((t) integerp phase-p t)))
  (if (not (consp x)) (mv -1 :X nil)
    (let ((entry (phase-fix (car x))))
      (if (not (equal entry :N)) (mv 0 entry (cdr x))
        (mv-let (n a x) (n-count (cdr x))
          (mv (1+ n) a x))))))

(defthm n-count-lower-bound
  (<= -1 (val 0 (n-count x)))
  :rule-classes :linear)

(def::signature n-count (phase-listp) t t phase-listp)
(def::signature n-count (concrete-phase-listp) t concrete-phase-p concrete-phase-listp)

(defthm len-n-count
  (equal (len (val 2 (n-count x)))
         (+ (len x) -1 (- (val 0 (n-count x))))))

(defthm n-count-bounds
  (and
   (< (val 0 (n-count x)) (len x))
   (<= (len (val 2 (n-count x))) (len x))
   (implies
    (< 0 (val 0 (n-count x)))
    (< (len (val 2 (n-count x))) (len x))))
  :rule-classes :linear)

;; Unnecessarily painful.
(defthmd val1-n-count-as-nth-phase
  (implies
   (and
    (wf-phase-sequence-suffix :N x)    
    (<= 0 (val 0 (n-count x))))
   (equal (val 1 (n-count x))
          (nth-phase (val 0 (n-count x)) x)))
  :hints ((and stable-under-simplificationp
               '(:expand (N-COUNT (CDR X))))))

(defthm nth-phase-n-count
  (implies
   (< (nfix i) (val 0 (n-count x)))
   (equal (nth-phase i x) :N)))

(defthm nth-phase-over-n-count
  (implies
   (<= 0 (val 0 (n-count x)))
   (phase-equiv (nth-phase i (val 2 (n-count x)))
                (nth-phase (+ (nfix i) 1 (val 0 (n-count x))) x)))
  :hints (("Goal" :in-theory (disable (:definition n-count)))
          (and stable-under-simplificationp
               '(:expand ((n-count x))))
          (and stable-under-simplificationp
               '(:expand ((n-count (cdr x)))))
          ))

(defthm natp-n-count
  (implies
   (consp x)
   (natp (val 0 (n-count x))))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((n-count x)))))
   
(defthm val1-n-count-as-phase
  (implies
   (wf-phase-sequence-suffix :N x)
   (phase-equiv (val 1 (n-count x)) :O))
  :hints (("Goal" :in-theory (enable WF-PHASE-SEQUENCE-STEP))))

(theory-invariant
 (incompatible
  (:rewrite val1-n-count-as-phase)
  (:rewrite val1-n-count-as-nth-phase)))                              

(defthm wf-phase-sequence-n-count
  (implies
   (wf-phase-sequence-suffix :N x)
   (and (natp (val 0 (n-count x)))
        (wf-phase-sequence-step :N (val 1 (n-count x)))
        (wf-pcount-sequence-step :N (val 1 (n-count x)))
        (implies
         (phase-equiv phase (val 1 (n-count x)))
         (wf-phase-sequence-suffix phase (val 2 (n-count x))))))
  :hints (("Goal" :in-theory (enable WF-PHASE-SEQUENCE-STEP
                                     equal-phase-fix))))

(in-theory (disable n-count))

;; -------------------------------------------------------------------
;; ox-count/xo-count
;; -------------------------------------------------------------------

(defines xo-ox-count
  :flag-local nil
  (define ox-count (x)
    :measure (len x)
    :returns (mv (count natp)
                 (flag  booleanp)
                 (a     phase-p)
                 (nxt   any-p)
                 )
    (if (not (consp x)) (mv 0 nil :X nil)
      (let ((L (phase-fix (car x))))
        (if (equal L :O)
            (mv-let (n flg phase x) (xo-count (cdr x))
              (mv (1+ (nfix n)) flg phase x))
          (mv 0 t L (cdr x))))))
  (define xo-count (x)
    :measure (len x)
    :returns (mv (count natp)
                 (flag  booleanp)
                 (a     phase-p)
                 (nxt   any-p)
                 )
    (if (not (consp x)) (mv 0 nil :X nil)
      (let ((L (phase-fix (car x))))
        (if (equal L :X)
            (mv-let (n flg phase x) (ox-count (cdr x))
              (mv (1+ (nfix n)) flg phase x))
          (mv 0 t L (cdr x))))))
  )

(def::signature ox-count (t) natp t phase-p t)
(def::signature xo-count (t) natp t phase-p t)

(defthm-xo-ox-count-flag
    (defthm phase-listp-xo-count
      (implies
       (phase-listp x)
       (phase-listp (val 3 (xo-count x))))
      :flag xo-count)
    (defthm phase-listp-ox-count
      (implies
       (phase-listp x)
       (phase-listp (val 3 (ox-count x))))
      :flag ox-count)
    :hints ('(:expand ((ox-count x)
                       (xo-count x)))))

(def::signature ox-count (phase-listp) t t t phase-listp)
(def::signature ox-count (phase-listp) t t t phase-listp)

(defthm-xo-ox-count-flag
    (defthm concrete-phase-listp-xo-count
      (implies
       (concrete-phase-listp x)
       (and (concrete-phase-listp (val 3 (xo-count x)))
            (concrete-phase-p (val 2 (xo-count x)))))
      :flag xo-count)
    (defthm concrete-phase-listp-ox-count
      (implies
       (concrete-phase-listp x)
       (and (concrete-phase-listp (val 3 (ox-count x)))
            (concrete-phase-p (val 2 (ox-count x)))))
      :flag ox-count)
    :hints ('(:expand ((ox-count x)
                       (xo-count x)))))

(def::signature ox-count (concrete-phase-listp) t t concrete-phase-p concrete-phase-listp)
(def::signature xo-count (concrete-phase-listp) t t concrete-phase-p concrete-phase-listp)

(defthm-xo-ox-count-flag
  (defthmd phase-list-equiv-v0-xo-count
    (implies
     (syntaxp (symbolp x))
     (equal (val 0 (xo-count x))
            (val 0 (xo-count (fix-phase-list x)))))
    :flag xo-count)
  (defthmd phase-list-equiv-v0-ox-count
    (implies
     (syntaxp (symbolp x))
     (equal (val 0 (ox-count x))
            (val 0 (ox-count (fix-phase-list x)))))
    :flag ox-count)
  :hints ('(:in-theory (enable xo-count ox-count))))

(defthm phase-list-equiv-congruence-v0-xo-count
  (implies
   (phase-list-equiv x y)
   (equal (val 0 (xo-count x))
          (val 0 (xo-count y))))
  :rule-classes :congruence
  :hints (("Goal" :in-theory (enable phase-list-equiv
                                     phase-list-equiv-v0-xo-count))))

(defthm phase-list-equiv-congruence-v0-ox-count
  (implies
   (phase-list-equiv x y)
   (equal (val 0 (ox-count x))
          (val 0 (ox-count y))))
  :rule-classes :congruence
  :hints (("Goal" :in-theory (enable phase-list-equiv
                                     phase-list-equiv-v0-ox-count))))

(defthm-xo-ox-count-flag
  (defthm phase-list-equiv-v1-xo-count
    (equal (val 1 (xo-count (fix-phase-list x)))
           (val 1 (xo-count x)))
    :flag xo-count)
  (defthm phase-list-equiv-v1-ox-count
    (equal (val 1 (ox-count (fix-phase-list x)))
           (val 1 (ox-count x)))
    :flag ox-count)
  :hints ('(:in-theory (enable xo-count ox-count))))

(defthm-xo-ox-count-flag
  (defthm phase-list-equiv-v2-xo-count
    (equal (val 2 (xo-count (fix-phase-list x)))
           (val 2 (xo-count x)))
    :flag xo-count)
  (defthm phase-list-equiv-v2-ox-count
    (equal (val 2 (ox-count (fix-phase-list x)))
           (val 2 (ox-count x)))
    :flag ox-count)
  :hints ('(:in-theory (enable xo-count ox-count))))

(defthm-xo-ox-count-flag
  (defthm phase-list-equiv-v3-xo-count
    (phase-list-equiv (val 3 (xo-count (fix-phase-list x)))
                      (val 3 (xo-count x)))
    :flag xo-count)
  (defthm phase-list-equiv-v3-ox-count
    (phase-list-equiv (val 3 (ox-count (fix-phase-list x)))
                      (val 3 (ox-count x)))
    :flag ox-count)
  :hints ('(:in-theory (enable xo-count ox-count))))

(defthm-xo-ox-count-flag
  (defthm not-flag-implies-end-ox-count
    (implies
     (not (val 1 (ox-count x)))
     (equal (val 0 (ox-count x))
            (len x)))
    :flag ox-count)
  (defthm not-flag-implies-end-xo-count
    (implies
     (not (val 1 (xo-count x)))
     (equal (val 0 (xo-count x))
            (len x)))
    :flag xo-count)
  :hints ('(:in-theory (enable xo-count ox-count))))

(defthm-xo-ox-count-flag
  (defthm len-ox-count
    (equal (len (val 3 (ox-count x)))
           (if (val 1 (ox-count x))
               (+ (len x) -1 (- (val 0 (ox-count x))))
             (+ (len x) (- (val 0 (ox-count x))))))
    :flag ox-count)
  (defthm len-xo-count
    (equal (len (val 3 (xo-count x)))
           (if (val 1 (xo-count x))
               (+ (len x) -1 (- (val 0 (xo-count x))))
             (+ (len x) (- (val 0 (xo-count x))))))
    :flag xo-count)
  :hints ('(:in-theory (enable xo-count ox-count)))
  )
  
(defthm-xo-ox-count-flag
  (defthm wf-phase-sequence-suffix-v2-v3-ox-count
    (implies
     (and
      (val 1 (ox-count x))
      (wf-phase-sequence-suffix :X x)
      (phase-equiv phase (val 2 (ox-count x))))
     (wf-phase-sequence-suffix phase
                               (val 3 (ox-count x))))
    :flag ox-count)
  (defthm wf-phase-sequence-suffix-v2-v3-xo-count
    (implies
     (and
      (val 1 (xo-count x))
      (wf-phase-sequence-suffix :O x)
      (phase-equiv phase (val 2 (xo-count x))))
     (wf-phase-sequence-suffix phase
                               (val 3 (xo-count x))))
    :flag xo-count)
  :hints ('(:in-theory (enable equal-phase-fix
                               xo-count
                               ox-count)))
  )

(defthm-xo-ox-count-flag
  (defthm wf-phase-sequence-step-v2-ox-count
    (implies
     (and
      (val 1 (ox-count x))
      (wf-phase-sequence-suffix :X x))
     (and
      (implies
       (even-p (val 0 (ox-count x)))
       (phase-equiv (val 2 (ox-count x)) :N))
      (implies
       (not (even-p (val 0 (ox-count x))))
       (phase-equiv (val 2 (ox-count x)) :P))))
    :flag ox-count)
  (defthm wf-phase-sequence-step-v2-xo-count
    (implies
     (and
      (val 1 (xo-count x))
      (wf-phase-sequence-suffix :O x))
     (and
      (implies
       (not (even-p (val 0 (xo-count x))))
       (phase-equiv (val 2 (xo-count x)) :N))
      (implies
       (even-p (val 0 (xo-count x)))
       (phase-equiv (val 2 (xo-count x)) :P))))
    :flag xo-count)
  :hints ('(:in-theory (enable WF-PHASE-SEQUENCE-STEP
                               equal-phase-fix
                               xo-count
                               ox-count)))
  )

(defines xo-ox-replicate
  :flag-local nil
  (define replicate-ox (count)
    :measure (nfix count)
    :returns (res concrete-phase-listp)
    ;:signature ((t) concrete-phase-listp)
    ;:congruence ((nfix-equiv) equal)))
    (let ((count (nfix count)))
      (if (zp count) nil
        (cons :O (replicate-xo (1- count))))))
  (define replicate-xo (count)
    :measure (nfix count)
    :returns (res concrete-phase-listp)
    ;:signature ((t) concrete-phase-listp)
    ;:congruence ((nfix-equiv) equal)))
    (let ((count (nfix count)))
      (if (zp count) nil
        (cons :X (replicate-ox (1- count))))))
  )

(def::signature replicate-ox (t) concrete-phase-listp)
(def::signature replicate-xo (t) concrete-phase-listp)

(defthm step-replicate-ox
  (implies
   (natp c)
   (equal (replicate-ox (+ 1 c))
          (cons :O (replicate-xo c))))
  :hints (("Goal" :in-theory (enable replicate-ox))))

(defthm step-replicate-xo
  (implies
   (natp c)
   (equal (replicate-xo (+ 1 c))
          (cons :X (replicate-ox c))))
  :hints (("Goal" :in-theory (enable replicate-xo))))

(defthm-xo-ox-replicate-flag
  (defthm len-replicate-ox
    (equal (len (replicate-ox count))
           (nfix count))
    :flag replicate-ox)
  (defthm len-replicate-xo
    (equal (len (replicate-xo count))
           (nfix count))
    :flag replicate-xo)
  :hints ('(:in-theory (enable replicate-ox
                               replicate-xo)))
  )

(in-theory (disable phase-fix-phase-p))

(defthm-xo-ox-count-flag
  (defthm replicate-ox-ox-count
    (implies
     (and
      (concrete-phase-listp x)
      (not (val 1 (ox-count x))))
     (phase-list-equiv (replicate-ox (len x))
                       x))
    :flag ox-count)
  (defthm replicate-xo-xo-count
    (implies
     (and
      (concrete-phase-listp x)
      (not (val 1 (xo-count x))))
     (phase-list-equiv (replicate-xo (len x))
                       x))
    :flag xo-count)
  :hints ('(:in-theory (enable xo-count
                               ox-count
                               equal-phase-fix
                               replicate-ox
                               replicate-xo)))
  )

(defthm-xo-ox-count-flag
  (defthm replicate-ox-ox-count-bind
    (implies
     (and
      (concrete-phase-listp x)
      (val 1 (ox-count x))
      (phase-equiv phase (val 2 (ox-count x))))
     (phase-list-equiv (append (replicate-ox (val 0 (ox-count x)))
                               (cons phase (val 3 (ox-count x))))
                       x))
    :flag ox-count)
  (defthm replicate-xo-xo-count-bind
    (implies
     (and
      (concrete-phase-listp x)
      (val 1 (xo-count x))
      (phase-equiv phase (val 2 (xo-count x))))
     (phase-list-equiv (append (replicate-xo (val 0 (xo-count x)))
                               (cons phase (val 3 (xo-count x))))
                       x))
    :flag xo-count)
  :hints ('(:in-theory (enable xo-count
                               ox-count
                               equal-phase-fix
                               replicate-ox
                               replicate-xo)))
  )

;; -------------------------------------------------------------------
;; phase count abstraction
;; -------------------------------------------------------------------

(defthmd len-cdr
  (implies
   (syntaxp (not (symbolp x)))
   (equal (len (cdr x))
          (if (consp x) (1- (len x))
            0))))

;; We could have a left accumulator?

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))
  
  (defthm <-constants
    (implies
     (and
      (syntaxp (and (quotep c) (quotep d)))
      (integerp c)
      (integerp d)
      (integerp x))
     (and
      (equal (< (+ c x) d)
             (< x (- d c)))
      (equal (<  d (+ c x))
             (< (- d c) x)))))

  )

(def::un abstract-phase-rec (R a x)
  (declare (ignorable R)
           (xargs :measure (len x)
                  :hints (("Goal" :in-theory (enable len-cdr)))
                  :signature ((t t t) pcount-listp)))
  (if (not (consp x)) (list (pcount a 1))
    (let ((entry (phase-fix a)))
      (cond
       ((equal entry :N)
        (mv-let (c a x) (n-count x)
          (let ((p (pcount :N (1+ c))))
            (cons p (abstract-phase-rec :N a x)))))
       ((equal entry :P)
        (mv-let (c a x) (p-count x)
          (let ((p (pcount :P (1+ c))))
            (cons p (abstract-phase-rec :P a x)))))
       ((equal entry :O)
        (mv-let (c flg a x) (xo-count x)
          (if (not flg)
              (if (even-p c) (list (pcount :W (+ 1 c)))
                (list (pcount :Y (+ 1 c))))
            (cond
             ((equal c 0)
              (let ((p (pcount :O 1)))
                (cons p (abstract-phase-rec :O a x))))
             ((not (even-p c))
              (let ((p (pcount :Y (+ 1 c))))
                (cons p (abstract-phase-rec :Y a x))))
             (t
              (cons (pcount :W (+ 1 c))
                    (abstract-phase-rec :W a x)))))))
       (t
        (mv-let (c flg a x) (ox-count x)
          (if (not flg)
              (if (even-p c) (list (pcount :X (1+ c)))
                (list (pcount :Z (1+ c))))
            (cond
             ((even-p c)
              (let ((p (pcount :X (1+ c))))
                (cons p (abstract-phase-rec :X a x))))
             (t
              (cons (pcount :Z (1+ c))
                    (abstract-phase-rec :Z a x)))))))))))

(def::signature abstract-phase-rec (t concrete-phase-p concrete-phase-listp) nzpcount-listp
  :hints (`(:in-theory (enable non-zero-even-is-gte CONCRETE-PHASE-P))))

(defcong phase-equiv equal (abstract-phase-rec p a x) 2
  :hints (("Goal" :expand (:free (a) (abstract-phase-rec p a x)))))

#+joe
(defthm count-relation-fix-1
  (implies
   (concrete-phase-p a)
   (equal (count-relation-fix a 1) 1))
  :hints (("goal" :in-theory (enable concrete-phase-p count-relation-fix))))

(defthm pcount-len-abstract-phase-rec
  (implies
   (and
    (concrete-phase-p a)
    (concrete-phase-listp x)
    (wf-phase-sequence-suffix a x))
   (equal (pcount-len (abstract-phase-rec pre a x))
          (+ 1 (len x))))
  :hints (("Goal" :in-theory (e/d (equal-phase-fix)
                                  (WF-PHASE-SEQUENCE-SUFFIX-CONSP)))))

(defthm NTH-PCOUNT-ENTRY-out-of-bounds
  (implies
   (<= (pcount-count x) (nfix i))
   (EQUAL (NTH-PCOUNT-ENTRY I x)
          (PHASE-BIT)))
  :hints (("Goal" :in-theory (enable NTH-PCOUNT-ENTRY))))

(in-theory (disable NTH-PCOUNT-ENTRY-OUT-OF-BOUNDS))

(defthm-xo-ox-count-flag
  (defthm val0-ox-count-bound
    (and (<= (val 0 (ox-count x)) (len x))
         (implies
          (val 1 (ox-count x))
          (< (val 0 (ox-count x)) (len x))))
    :rule-classes (:linear)
    :flag ox-count)
  (defthm val0-xo-count-bound
    (and (<= (val 0 (xo-count x)) (len x))
         (implies
          (val 1 (xo-count x))
          (< (val 0 (xo-count x)) (len x))))
    :rule-classes (:linear)
    :flag xo-count)
  :hints ('(:in-theory (enable ox-count xo-count)))
  )
  
(defthm-xo-ox-count-flag
  (defthm nth-phase-val0-ox-count
    (implies
     (< (nfix i) (val 0 (ox-count x)))
     (equal (nth-phase i x)
            (if (even-p (nfix i)) :O :X)))
    :flag ox-count)
  (defthm nth-phase-val0-xo-count
    (implies
     (< (nfix i) (val 0 (xo-count x)))
     (equal (nth-phase i x)
            (if (even-p (nfix i)) :X :O)))
    :flag xo-count)
  :hints (("Goal" :induct (list (XO-OX-COUNT-FLAG FLAG X)
                                (nth-phase i x)))
          '(:in-theory (enable ox-count xo-count)))
  )

(defthm-xo-ox-count-flag
  (defthm nth-phase-val2-ox-count
    (implies
     (val 1 (ox-count x))
     (and (equal (val 2 (ox-count x))
                 (nth-phase (val 0 (ox-count x)) x))
          (equal (nth-phase i (val 3 (ox-count x)))
                 (nth-phase (+ (nfix i) 1 (val 0 (ox-count x))) x))))
    :flag ox-count)
  (defthm nth-phase-val2-xo-count
    (implies
     (val 1 (xo-count x))
     (and (equal (val 2 (xo-count x))
                 (nth-phase (val 0 (xo-count x)) x))
          (equal (nth-phase i (val 3 (xo-count x)))
                 (nth-phase (+ (nfix i) 1 (val 0 (xo-count x))) x))))
    :flag xo-count)
  :hints ('(:in-theory (enable nfix-equiv-nfix)
                       :expand ((xo-count x)
                                (ox-count x))))
  )

(in-theory (disable nth-phase-val2-ox-count nth-phase-val2-xo-count))

(defun nth-pcount-abstract-phase-rec-induction (R i a x)
  (declare (ignorable r i)
           (xargs :measure (len x)))
  (if (not (consp x)) (list (pcount a 1))
    (let ((entry (phase-fix a))
          (i     (nfix i)))
      (cond
       ((equal entry :N)
        (mv-let (c a x) (n-count x)
          (let ((p (pcount :N (1+ c))))
            (cons p (nth-pcount-abstract-phase-rec-induction :N (- i (1+ c)) a x)))))
       ((equal entry :P)
        (mv-let (c a x) (p-count x)
          (let ((p (pcount :P (1+ c))))
            (cons p (nth-pcount-abstract-phase-rec-induction :P (- i (1+ c)) a x)))))
       ((equal entry :O)
        (mv-let (c flg a x) (xo-count x)
          (if (not flg)
              (if (even-p c) (list (pcount :W (+ 1 c)))
                (list (pcount :Y (+ 1 c))))
            (cond
             ((equal c 0)
              (let ((p (pcount :O 1)))
                (cons p (nth-pcount-abstract-phase-rec-induction :O (- i (1+ c)) a x))))
             ((not (even-p c))
              (let ((p (pcount :Y (+ 1 c))))
                (cons p (nth-pcount-abstract-phase-rec-induction :Y (- i (1+ c)) a x))))
             (t
              (cons (pcount :W (+ 1 c))
                    (nth-pcount-abstract-phase-rec-induction :W (- i (1+ c)) a x)))))))
       (t
        (mv-let (c flg a x) (ox-count x)
          (if (not flg)
              (if (even-p c) (list (pcount :X (1+ c)))
                (list (pcount :Z (1+ c))))
            (cond
             ((even-p c)
              (let ((p (pcount :X (1+ c))))
                (cons p (nth-pcount-abstract-phase-rec-induction :X (- i (1+ c)) a x))))
             (t
              (cons (pcount :Z (1+ c))
                    (nth-pcount-abstract-phase-rec-induction :Z (- i (1+ c)) a x)))))))))))

(def::signature phase-fix (CONCRETE-PHASE-P) CONCRETE-PHASE-P
  :hints (("Goal" :in-theory (enable CONCRETE-PHASE-P))))

(encapsulate
   ()

  (local (include-book "arithmetic-5/top" :dir :system))
  (in-theory (disable abstract-phase-rec))

  (local (in-theory (disable open-nth-phase-consp DEFAULT-LESS-THAN-2 ZP-OPEN NTH-PCOUNT-ZERO)))

  (local (in-theory (e/d
                     (nfix
                      val1-p-count-as-nth-phase
                      val1-n-count-as-nth-phase
                      nth-phase-val2-ox-count
                      nth-phase-val2-xo-count
                      )
                     (NTH-PCOUNT-OUT-OF-RANGE
                      val1-n-count-as-phase
                      val1-p-count-as-phase
                      wf-phase-sequence-step-v2-ox-count
                      wf-phase-sequence-step-v2-xo-count
                      ))))
  
  ;; Clearly a messy,inefficient proof .. compared to the inductive
  ;; version.  Provides a nice counterpoint.  I suspect, however, that
  ;; in this case the messiness is due to the complexity of the "nth"
  ;; function.
  
  ;; OK .. part of the problem is that we are eliminating destructors.
  ;; That isn't good.
  
  (defthm nth-pcount-abstract-phase-rec
    (implies
     (and
      (concrete-phase-p a)
      (concrete-phase-listp x)
      (wf-phase-sequence-suffix a x))
     (phase-equiv (nth-pcount i (abstract-phase-rec pre a x))
                  (nth-phase i (cons a x))
                  #+joe
                  (let ((i (nfix i)))
                    (if (and (<= 0 i) (<= i (len x)))
                        (nth-phase i (cons a x))
                      (phase-bit)))))
    :otf-flg t
    :hints (("Goal" :do-not-induct t
             :in-theory (enable nth-pcount-entry)
             :induct (nth-pcount-abstract-phase-rec-induction pre i a x))
            '(:expand (:free (a) (ABSTRACT-PHASE-REC PRE a x)))
            (and stable-under-simplificationp
                 '(:expand ((ABSTRACT-PHASE-REC PRE A NIL)
                            (ABSTRACT-PHASE-REC PRE :O X))
                           :in-theory (enable nth-pcount-entry)))))

  )
  
(defthm x-or-z
  (iff (wf-pcount-sequence-step a :z)
       (wf-pcount-sequence-step a :x))
  :hints (("goal" :in-theory (enable wf-pcount-sequence-step))))

(defthm wf-phase-final-implies-wf-pcount-final
  (implies
   (wf-phase-final a)
   (wf-pcount-final a))
  :hints (("goal" :in-theory (enable wf-phase-final wf-pcount-final))))

;; (defthm WF-PCOUNT-TRIPLE-STEP-z-reduction
;;   (iff (WF-PCOUNT-TRIPLE-STEP L P :Z)
;;        (WF-PCOUNT-TRIPLE-STEP L P :X))
;;   :hints (("Goal" :in-theory (enable WF-PCOUNT-TRIPLE-STEP))))

;; (defthm triple-step-secret
;;   (implies
;;    (not (phase-equiv v :O))
;;    (WF-PCOUNT-TRIPLE-STEP L v R))
;;   :hints (("Goal" :in-theory (enable equal-phase-fix
;;                                      WF-PCOUNT-TRIPLE-STEP))))

;; (defthm triple-step-secret-2
;;   (implies
;;    (EQUAL (PHASE-FIX P) :N)
;;    (WF-PCOUNT-TRIPLE-STEP P v N))
;;   :hints (("Goal" :in-theory (enable equal-phase-fix
;;                                      WF-PCOUNT-TRIPLE-STEP))))

(defthm wf-pcount-sequence-suffix-abstract-phase-rec
  (implies
   (and
    (implies
     (phase-equiv a :O)
     (equal (phase-fix P) :N))
    (wf-pcount-sequence-step P a)
    (wf-phase-sequence-suffix a nxt))
   (wf-pcount-sequence-suffix P (abstract-phase-rec P a nxt)))
  :hints (("Goal" :do-not-induct t
           :induct (abstract-phase-rec P a nxt)
           :in-theory (e/d (abstract-phase-rec)
                           (wf-pcount-sequence-suffix-consp
                            wf-phase-sequence-suffix-consp)))
          (and stable-under-simplificationp
               '(:in-theory (enable WF-PHASE-SEQUENCE-STEP)))))

(defthm x-or-y
  (iff (wf-pcount-sequence-step :y a)
       (wf-pcount-sequence-step :x a))
  :hints (("goal" :in-theory (enable wf-pcount-sequence-step))))

(in-theory (disable abstract-phase-rec))

;; X | X O X   ;; even from X
;; W | O X O   ;; odd from O X
;; Y | O X O X ;; even from O X
;; Z | X O X O ;; odd from X

(defthm zero-step-phase-when-not-x
  (implies
   (not (equal (phase-fix x) :x))
   (iff (wf-phase-sequence-step :o x)
        (phase-equiv x :p)))
  :hints (("goal" :in-theory (enable equal-phase-fix
                                     wf-phase-sequence-step))))

(def::un abstract-phase (x)
  (declare (xargs :signature ((t) pcount-listp)))
  (if (not (consp x)) nil
    (let ((L (phase-fix (car x))))
      (if (not (consp (cdr x))) (list (pcount :X 1))
        (cond
         ((equal L :O)
          (mv-let (c flg a x) (xo-count (cdr x))
            (if (not flg)
                (if (even-p c) (list (pcount :W (+ 1 c)))
                  (list (pcount :Y (+ 1 c))))
              (cond
               ((equal c 0)
                (let ((p (pcount :O 1)))
                  (cons p (abstract-phase-rec :O a x))))
               ((not (even-p c))
                (let ((p (pcount :Y (+ 1 c))))
                  (cons p (abstract-phase-rec :Y a x))))
               (t
                (let ((p (pcount :W (+ 1 c))))
                  (cons p (abstract-phase-rec :W a x))))))))
         (t
          (mv-let (c flg a x) (ox-count (cdr x))
            (if (not flg)
                (if (even-p c) (list (pcount :X (1+ c)))
                  (list (pcount :Z (1+ c))))
              (cond
               ((even-p c)
                (let ((p (pcount :X (1+ c))))
                  (cons p (abstract-phase-rec :X a x))))
               (t
                (cons (pcount :Z (1+ c))
                      (abstract-phase-rec :Z a x))))))))))))

(defthm nzpcount-listp-abstract-phase
  (implies
   (and
    (concrete-phase-listp x)
    (wf-phase-sequence x))
   (nzpcount-listp (abstract-phase x)))
  :hints (("Goal" :in-theory (enable WF-PHASE-INITIAL
                                     non-zero-even-is-gte
                                     equal-phase-fix
                                     wf-phase-sequence)))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((abstract-phase x)))))
   
(defthm even-p-to-odd-p-len
  (implies
   (and
    (even-p (len x))
    (consp x))
   (not (even-p (len (cdr x)))))
  :rule-classes (:forward-chaining))

(defthm odd-p-to-even-p-len
  (implies
   (and
    (not (even-p (len x)))
    (consp x))
   (even-p (len (cdr x))))
  :rule-classes (:forward-chaining))

(defthm pcount-len-abstract-phase
  (implies
   (and
    (wf-phase-sequence x)
    (concrete-phase-listp x))
   (equal (pcount-len (abstract-phase x))
          (len x)))
  :hints (("Goal" :in-theory (e/d (WF-PHASE-INITIAL
                                   WF-PHASE-SEQUENCE)
                                  nil)
           :do-not-induct t)))

(defthm wf-phase-sequence-listp-wf-pcount-sequence-listp-abstract-phase
  (implies
   (wf-phase-sequence x)
   (wf-pcount-sequence (abstract-phase x)))
  :otf-flg t
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (wf-pcount-sequence
                            WF-PHASE-SEQUENCE
                            equal-phase-fix
                            WF-PHASE-INITIAL)
                           (WF-PCOUNT-SEQUENCE-SUFFIX-CONSP
                            WF-PHASE-SEQUENCE-SUFFIX-CONSP)))))


(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (local (in-theory (e/d
                     (nfix
                      val1-p-count-as-nth-phase
                      val1-n-count-as-nth-phase
                      nth-phase-val2-ox-count
                      nth-phase-val2-xo-count
                      )
                     (val1-n-count-as-phase
                      val1-p-count-as-phase
                      wf-phase-sequence-step-v2-ox-count
                      wf-phase-sequence-step-v2-xo-count
                      ))))

  (defthm nth-pcount-abstract-phase
    (implies
     (and
      (wf-phase-sequence x)
      (concrete-phase-listp x))
     (phase-equiv (nth-pcount i (abstract-phase x))
                  (nth-phase i x)))
    :hints (("Goal" :do-not-induct t
             :in-theory (enable NTH-PCOUNT-ENTRY
                                WF-PHASE-INITIAL
                                WF-PHASE-ONLY wf-phase-sequence))))
  
  )
  
;; -------------------------------------------------------------------
;; phase decoder
;; -------------------------------------------------------------------

(in-theory (disable nfix-equiv))


(def::un replicate-phase (phase count)
  (declare (xargs :signature ((t t) phase-listp)
                  :measure (nfix count)
                  ))
  (let ((count (nfix count))
        (phase (phase-fix phase)))
    (if (zp count) nil
      (cons phase (replicate-phase phase (1- count))))))

(defcong phase-equiv equal (replicate-phase phase count) 1)
(defcong nfix-equiv equal (replicate-phase phase count) 2
  :hints (("Goal" :in-theory (enable nfix nfix-equiv))))

(defthm concrete-phase-listp-replicate-phase
  (implies
   (memberp (phase-fix phase) '(:O :N :P))
   (concrete-phase-listp (replicate-phase phase count))))
    
(defthm len-replicate-phase
  (equal (len (replicate-phase phase count))
         (nfix count)))

(defthm open-replicate-phase
  (implies
   (natp c)
   (equal (replicate-phase p (+ 1 c))
          (cons (phase-fix p) (replicate-phase p c)))))

(defthm replicate-phase-p-count
  (implies
   (and
    (wf-phase-sequence-suffix :p x)
    (phase-equiv phase (val 1 (p-count x))))
   (phase-list-equiv (append (replicate-phase :p (val 0 (p-count x)))
                             (cons phase (val 2 (p-count x))))
                     x))
  :hints (("goal" :induct (p-count x)
           :in-theory (enable equal-phase-fix p-count))))

(defthm replicate-phase-n-count
  (implies
   (and
    (wf-phase-sequence-suffix :n x)
    (phase-equiv phase (val 1 (n-count x))))
   (phase-list-equiv (append (replicate-phase :n (val 0 (n-count x)))
                             (cons phase (val 2 (n-count x))))
                     x))
  :hints (("goal" :induct (n-count x)
           :in-theory (enable equal-phase-fix n-count))))

;; And a special case for :O ..

(defthm replicate-phase-xo-count
  (implies
   (and
    (wf-phase-sequence-suffix :O x)
    (val 1 (xo-count x))
    (equal (val 0 (xo-count x)) 0)
    (phase-equiv phase (val 2 (xo-count x))))
   (phase-list-equiv (append (replicate-phase :O 0)
                             (cons phase (val 3 (xo-count x))))
                     x))
  :hints (("goal" :expand (xo-count x))))

(in-theory (disable replicate-phase (replicate-phase)))

(def::und decode-pcount (x)
  (declare (xargs :signature ((t) concrete-phase-listp)
                  :signature-hints ('(:cases ((equal (pcount-phase x) :n)))
                                    '(:cases ((equal (pcount-phase x) :o))))
                  :congruence ((pcount-equiv) equal)))
  (let ((phase (pcount-phase x))
        (count (pcount-count x)))
    (cond
     ((equal phase :W)
      (replicate-ox count))
     ((equal phase :X)
      (replicate-xo count))
     ((equal phase :Y)
      (replicate-ox count))
     ((equal phase :Z)
      (replicate-xo count))
     (t (replicate-phase phase count)))))

(defthm len-decode-pcount
  (equal (len (decode-pcount x))
         (pcount-count x))
  :hints (("Goal" :in-theory (enable decode-pcount))))

;; (def::signature decode-pcount (empty-pcount-p) concrete-phase-listp
;;   :hints (("Goal" :cases ((EQUAL (PCOUNT-PHASE X1) :N))
;;            :in-theory (enable decode-pcount))))

(def::un decode-pcount-list (list)
  (declare (xargs :signature ((t) concrete-phase-listp)
                  :congruence ((pcount-list-equiv) equal)))
  (if (not (consp list)) nil
    (let ((entry (pcount-fix (car list))))
      (append (decode-pcount entry)
              (decode-pcount-list (cdr list))))))

(defthm append-x-nil
  (implies
   (true-listp x)
   (equal (append x nil)
          x)))

;; DAG: So .. a weaker variant of this would follow from
;; our nth-theorms.  I think our primary objective is
;; to preserve pcount-len and nth-pcount.
(defthm decode-pcount-list-abstract-phase-rec
  (implies
   (and
    (concrete-phase-p a)
    (concrete-phase-listp x)
    (wf-pcount-sequence-step p a)
    (wf-phase-sequence-suffix a x))
   (phase-list-equiv (decode-pcount-list (abstract-phase-rec p a x))
                     (cons a x)))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (abstract-phase-rec
                                   DECODE-PCOUNT
                                   equal-phase-fix
                                  )
                                  (phase-fix-phase-p
                                   wf-phase-sequence-suffix-consp
                                   open-phase-list-equiv-cons
                                   open-phase-list-equiv-consp
                                   ))
           :do-not-induct t
           :induct (abstract-phase-rec p a x))
          (and stable-under-simplificationp
               '(:in-theory (enable REPLICATE-PHASE)))
          ))

(defthm nth-phase-append
  (equal (nth-phase i (append x y))
         (if (< (nfix i) (len x))
             (nth-phase i x)
           (nth-phase (- (nfix i) (len x)) y)))
  :hints (("Goal" :in-theory (enable zp nfix)
           :induct (nth-phase i x))))

(defun nat-induction (n)
  (if (zp n) n
    (nat-induction (1- n))))

(defun sigh-induction (flg i n)
  (if (or (zp i) (zp n)) (list i n)
    (if (equal flg 'replicate-ox)
        (sigh-induction 'replicate-xo (1- i) (1- n))
      (sigh-induction 'replicate-ox (1- i) (1- n)))))

(defthm-xo-ox-replicate-flag
  (defthm nth-phase-replicate-ox
    (EQUAL (NTH-PHASE I (replicate-ox n))
           (if (< (nfix i) (nfix n))
               (if (even-p (nfix i)) :O :X)
             (phase-bit)))
    :flag replicate-ox)
  (defthm nth-phase-replicate-xo
    (EQUAL (NTH-PHASE I (replicate-xo n))
           (if (< (nfix i) (nfix n))
               (if (even-p (nfix i)) :X :O)
             (phase-bit)))
    :flag replicate-xo)
  :hints (("Goal" :in-theory (enable nfix zp)
           :induct (sigh-induction flag n i))
          '(:expand ((replicate-xo n)
                     (replicate-ox n))))
  )

(defun nat-nat-induction (x y)
  (if (or (zp x) (zp y)) nil
    (nat-nat-induction (1- x) (1- y))))

(defthm nth-phase-replicate-phase
  (equal (nth-phase i (replicate-phase phase count))
         (if (< (nfix i) (nfix count))
             (phase-fix phase)
           (phase-bit)))
  :hints (("Goal" :in-theory (enable zp nfix replicate-phase)
           :expand (replicate-phase phase count)
           :induct (nat-nat-induction i count))))

(defthm nth-phase-decode-pcount
  (EQUAL (NTH-PHASE I (DECODE-PCOUNT x))
         (NTH-PCOUNT-entry I X))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable decode-pcount
                              nth-pcount-entry))))

(defthm nth-phase-decode-pcount-list
  (equal (nth-phase i (decode-pcount-list x))
         (nth-pcount i x))
  :hints (("Goal" :induct (nth-pcount i x)
           :in-theory (e/d (NTH-PCOUNT-ENTRY-OUT-OF-BOUNDS nfix)
                           (OPEN-NTH-PCOUNT)))
          '(:expand ((DECODE-PCOUNT-LIST (CDR X))
                     (decode-pcount-list x)
                     (NTH-PCOUNT I X)))))

(defthm nth-phase-decode-pcount-list-abstract-phase
  (implies
   (and
    (concrete-phase-listp x)
    (wf-phase-sequence x))
   (phase-equiv (nth-phase i (decode-pcount-list (abstract-phase x)))
                (nth-phase i x)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable abstract-phase))))

(defthm decode-pcount-list-abstract-phase
  (implies
   (and
    (concrete-phase-listp x)
    (wf-phase-sequence x))
   (phase-list-equiv (decode-pcount-list (abstract-phase x))
                     x))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (WF-PHASE-INITIAL
                                   WF-PHASE-ONLY
                                   WF-PHASE-SEQUENCE
                                   equal-phase-fix
                                   DECODE-PCOUNT)
                                  (len))
           :do-not-induct t)
          ))

;; ----------------------------------------
;; step pcount
;; ----------------------------------------

(def::un 3-tuple-test (L M R)
  (pattern-match-list (L M R)
    ;; -----------------------------------------------------------
    ;; passive middle
    ;; -----------------------------------------------------------
    (((phase ':W) (phase ':P) (phase ':X))
     t)
    (((phase ':W) (phase ':P) (phase ':Z))
     t)           
    (((phase ':X) (phase ':N) (phase ':Y))
     t)           
    (((phase ':X) (phase ':N) (phase ':O))
     t)           
    (((phase ':X) (phase ':N) (phase ':W))
     t)
    (((phase ':Y) (phase ':N) (phase ':W))
     t)
    (((phase ':Y) (phase ':N) (phase ':O))
     t)
    (((phase ':Y) (phase ':N) (phase ':Y))
     t)
    (((phase ':Z) (phase ':P) (phase ':X))
     t)
    (((phase ':Z) (phase ':P) (phase ':Z))
     t)           
    (((phase ':O) (phase ':P) (phase ':X))
     t)
    (((phase ':O) (phase ':P) (phase ':Z))
     t)
    ;; -----------------------------------------------------------
    ;; active middle
    ;; -----------------------------------------------------------
    (((phase ':N) (phase ':W) (phase ':P))
     t)
    (((phase ':P) (phase ':X) (phase ':N))
     t)
    (((phase ':N) (phase ':Y) (phase ':N))
     t)
    (((phase ':P) (phase ':Z) (phase ':P))
     t)
    (((phase ':N) (phase ':O) (phase ':P))
     t)
    ;; -----------------------------------------------------------
    (& nil)))

;; This is a nice test
(defthm 3-tuple-is-complete
  (implies
   (and
    (phase-p L)
    (phase-p M)
    (phase-p R))
   (iff (and 
         (wf-pcount-sequence-step L M)
         (wf-pcount-sequence-step M R))
        (3-tuple-test L M R)))
  :hints (("GOal" :in-theory (enable equal-phase-fix
                                     wf-pcount-sequence-step
                                     ))))

;; :X :N(n) :O | :X :N(n-1)|:E :O 
;; :Y :N(n) :O | :Y :N(n-1)|:E :O 
;; :W :P(n) :O | :X :N(n+1) :O 
;; :Z :N(n) :O | :Y :N(n+1) :O 

;; :O :P(n) :X | :O :P(n-1)|E :X
;; :O :P(n) :Z | :O :P(n-1)|E :Z
;; :O :P(n) :W | :O :P(n+1) :O 
;; :O :P(n) :Y | :O :P(n+1) :O 

;; :N :Y(n) :N | :N :Y(n)      :N  ;; Y moves right (or :Z or exapnds from wall)
;; :N :W(n) :P | :N :W(n-2)|:O :P  ;; W shrinks (or :X if alone)
;; :P :X(n) :N | :P :X(n+2)    :N  ;; X grows   (or :W if alone)
;; :P :Z(n) :P | :P :Z(n)      :P  ;; Z moves left (or :Y or expands from wall)

(defthm equal-pcount-phase
  (iff (equal (pcount-phase a) x)
       (and
        (phase-p x)
        (phase-equiv (pcount-phase a) x)))
  :hints (("Goal" :in-theory (e/d (phase-equiv
                                   phase-fix)
                                  (equal-phase-fix)))))

(encapsulate
    ()

  (defthmd helper-1
    (implies
     (and
      (PHASE-EQUIV (PCOUNT-PHASE M) :X)
      (not (EVEN-P I))
      (NZPCOUNT-P M)
      (integerp i))
     (not (equal (PCOUNT-COUNT M) (+ 1 I))))
    :hints (("Goal" :cases ((equal I (- (PCOUNT-COUNT M) 1))))))
  
  (defthmd helper-2
    (implies
     (and
      (PHASE-EQUIV (PCOUNT-PHASE M) :Z)
      (EVEN-P I)
      (NZPCOUNT-P M)
      (integerp i))
     (not (equal (PCOUNT-COUNT M) (+ 1 I))))
    :hints (("Goal" :cases ((equal I (- (PCOUNT-COUNT M) 1))))))
  
  (defthmd helper-3
    (implies
     (and
      (PHASE-EQUIV (PCOUNT-PHASE M) :Y)
      (EVEN-P I)
      (NZPCOUNT-P M)
      (integerp i))
     (not (equal (PCOUNT-COUNT M) (+ 1 I))))
    :hints (("Goal" :cases ((equal I (- (PCOUNT-COUNT M) 1))))))

  (defthmd helper-4
    (implies
     (and
      (PHASE-EQUIV (PCOUNT-PHASE M) :W)
      (not (EVEN-P I))
      (NZPCOUNT-P M)
      (integerp i))
     (not (equal (PCOUNT-COUNT M) (+ 1 I))))
    :hints (("Goal" :cases ((equal I (- (PCOUNT-COUNT M) 1))))))

  )
  
(def::un step-pcount-only (M)
  (declare (xargs :signature ((t) pcount-p)
                  :congruence ((pcount-equiv) equal)))
  (let ((M (pcount-fix M)))
    (pattern-match M
      ((pcount ':W c)
       (pcount :X c))
      ((pcount ':X (nat c))
       (if (<= 3 c)
           (pcount :W c)
         (pcount ':X c)))
      ((pcount ':Y c)
       (pcount :Z c))
      ((pcount ':Z c)
       (pcount :Y c))
      (& M))))

(defthm pcount-count-step-pcount-only
  (equal (pcount-count (step-pcount-only M))
         (pcount-count M)))

(encapsulate
    ()

  (local (in-theory (enable helper-1 helper-2 helper-3 helper-4)))
  
  (defthm nth-pcount-entry-step-pcount-only
    (implies
     (and
      (nzpcount-p x)
      (wf-pcount-only (pcount-phase x)))
     (equal (nth-pcount-entry i (step-pcount-only x))
            (let ((i (nfix i)))
              (let ((L (nth-pcount-entry (- i 1) x))
                    (M (nth-pcount-entry    i    x))
                    (R (nth-pcount-entry (+ i 1) x)))
                (if (equal i 0)
                    (if (equal (pcount-count x) 1)
                        :X
                      (first-two-step-phase M R))
                  (if (< (1+ i) (pcount-count x))
                      (step-phase L M R)
                    (if (equal (1+ i) (pcount-count x))
                        (last-two-step-phase L M)
                      (phase-bit))))))))
    :hints (("Goal" :in-theory (enable FIRST-TWO-STEP-PHASE
                                       NTH-PCOUNT-ENTRY))
            (and stable-under-simplificationp
                 '(:in-theory (enable WF-PCOUNT-ONLY)))
            ))
                                       
  )
  
(def::signature step-pcount-only (nzpcount-p) nzpcount-p)

(in-theory (disable step-pcount-only))

(defthm step-phase-list-replicate-xo
  (phase-list-equiv (step-phase-list (replicate-xo count))
                    (let ((count (nfix count)))
                      (if (zp count) nil
                        (if (<= count 1)
                            (list :x)
                          (cons (first-two-step-phase :x :o)
                                (step-phase-list-suffix (alt-phase :x :o) :x :o (replicate-xo (- count 2))))))))
  :hints (("goal" :expand ((replicate-xo count)
                           (replicate-ox (+ -1 (nfix count)))))))

(defthm step-phase-list-replicate-ox
  (phase-list-equiv (step-phase-list (replicate-ox count))
                    (let ((count (nfix count)))
                      (if (zp count) nil
                        (if (<= count 1)
                            (list :O)
                          (cons (first-two-step-phase :O :X)
                                (step-phase-list-suffix (alt-phase :o :x) :O :X (replicate-ox (- count 2))))))))
  :hints (("goal" :expand ((replicate-ox count)
                           (replicate-xo (+ -1 (nfix count)))))))

(defthm-xo-ox-replicate-flag
  (defthm v3-step-phase-rec-REPLICATE-XO
    (phase-list-equiv (val 3 (step-phase-list-rec LL :X :O (REPLICATE-XO count)))
                      (if (zp count) nil
                        (cons :X (REPLICATE-OX (1- (nfix count))))))
    :flag REPLICATE-XO)
  (defthm v3-step-phase-rec-REPLICATE-OX
    (phase-list-equiv (val 3 (step-phase-list-rec LL :O :X (REPLICATE-OX count)))
                      (if (zp count) nil
                        (cons :O (REPLICATE-XO (1- (nfix count))))))
    :flag REPLICATE-OX)
  :hints ('(:in-theory (enable nfix
                               REPLICATE-XO
                               REPLICATE-OX))))

(defthm reduce-phase-list-equiv-cons
  (iff (phase-list-equiv (cons a x) (cons a y))
       (phase-list-equiv x y)))

(encapsulate
    ()

  (local
   (defthm-xo-ox-replicate-flag
     (defthmd replicate-ox-tcons
       (equal (replicate-ox count)
              (if (zp count) nil
                (if (even-p count)
                    (tcons (replicate-ox (1- count)) :X)
                  (tcons (replicate-ox (1- count)) :O))))
       :rule-classes :definition
       :flag replicate-ox)
     (defthmd replicate-xo-tcons
       (equal (replicate-xo count)
              (if (zp count) nil
                (if (even-p count)
                    (tcons (replicate-xo (1- count)) :O)
                  (tcons (replicate-xo (1- count)) :X))))
       :rule-classes :definition
       :flag replicate-xo)
     :hints ('(:in-theory (enable nfix
                                  replicate-ox
                                  replicate-xo))))
   )
  
  
  (defthmd phase-list-equiv-as-tcar-tcdr
    (iff (phase-list-equiv x y)
         (if (and (consp x) (consp y))
             (and (phase-list-equiv (tcdr x) (tcdr y))
                  (phase-equiv (tcar x) (tcar y)))
           (and (not (consp x)) (not (consp y))))))
  
  (defthmd phase-list-equiv-replicate-xo
    (iff (phase-list-equiv (replicate-xo count) (tcons x a))
         (and (not (zp count))
              (phase-list-equiv (replicate-xo (1- count)) x)
              (if (even-p count)
                  (phase-equiv :O a)
                (phase-equiv :X a))))
    :hints (("Goal" :do-not-induct t
             :in-theory (enable replicate-ox-tcons
                                replicate-xo-tcons)
             :use (:instance phase-list-equiv-as-tcar-tcdr
                             (x (replicate-xo count))
                             (y (tcons x a))))))

  (defthmd phase-list-equiv-replicate-ox
    (iff (phase-list-equiv (replicate-ox count) (tcons x a))
         (and (not (zp count))
              (phase-list-equiv (replicate-ox (1- count)) x)
              (if (not (even-p count))
                  (phase-equiv :O a)
                (phase-equiv :X a))))
    :hints (("Goal" :do-not-induct t
             :in-theory (enable replicate-ox-tcons
                                replicate-xo-tcons)
             :use (:instance phase-list-equiv-as-tcar-tcdr
                             (x (replicate-ox count))
                             (y (tcons x a))))))

  )
  
(defthmd VAL0-STEP-PHASE-LIST-REC-irrelevant
  (implies
   (syntaxp (implies (quotep LL) (not (equal (cadr LL) :X))))
   (and (equal (VAL 1 (STEP-PHASE-LIST-REC LL L v list))
               (VAL 1 (STEP-PHASE-LIST-REC :X L v list)))
        (equal (VAL 2 (STEP-PHASE-LIST-REC LL L v list))
               (VAL 2 (STEP-PHASE-LIST-REC :X L v list))))))

(defthm-xo-ox-replicate-flag
  (defthm V1-V2-STEP-PHASE-LIST-REC-REPLICATE-XO
    (and (phase-equiv (VAL 1 (STEP-PHASE-LIST-REC LL :X :O (REPLICATE-XO count)))
                      (if (even-p (nfix count)) :X :O))
         (phase-equiv (VAL 2 (STEP-PHASE-LIST-REC LL :X :O (REPLICATE-XO count)))
                      (if (not (even-p (nfix count))) :X :O)))
    :flag REPLICATE-XO)
  (defthm V0-V1-STEP-PHASE-LIST-REC-REPLICATE-OX
    (and (phase-equiv (VAL 1 (STEP-PHASE-LIST-REC LL :O :X (REPLICATE-OX count)))
                      (if (even-p (nfix count)) :O :X))
         (phase-equiv (VAL 2 (STEP-PHASE-LIST-REC LL :O :X (REPLICATE-OX count)))
                      (if (not (even-p (nfix count))) :O :X)))
    :flag REPLICATE-OX)
  :hints ('(:in-theory (enable REPLICATE-XO REPLICATE-OX
                               VAL0-STEP-PHASE-LIST-REC-irrelevant)))
  )

(defthm phase-list-equiv-replicate-xo-cons
  (iff (phase-list-equiv (replicate-xo count)
                         (cons a x))
       (if (zp count) nil
         (and (phase-equiv a :X)
              (phase-list-equiv (replicate-ox (1- (nfix count)))
                                x))))
  :hints (("Goal" :in-theory (enable nfix)
           :expand (replicate-xo count))))

(defthm phase-list-equiv-replicate-ox-cons
  (iff (phase-list-equiv (replicate-ox count)
                         (cons a x))
       (if (zp count) nil
         (and (phase-equiv a :O)
              (phase-list-equiv (replicate-xo (1- (nfix count)))
                                x))))
  :hints (("Goal" :in-theory (enable nfix)
           :expand (replicate-ox count))))

(in-theory (disable REPLICATE-OX))

(defthm pcount-only-commutes
  (implies
   (and
    (wf-pcount-only (pcount-phase a))
    (nzpcount-p a))
   (phase-list-equiv (decode-pcount (step-pcount-only a))
                     (step-phase-list (decode-pcount a))))
  :otf-flg t
  :hints (("Goal" ;;:expand ((REPLICATE-OX (PCOUNT-COUNT A))
                  ;;         (REPLICATE-XO (+ -1 (PCOUNT-COUNT A))))
           :in-theory (e/d (nzpcount-p
                            step-pcount-only
                            phase-list-equiv-replicate-xo
                            phase-list-equiv-replicate-ox
                            WF-PCOUNT-ONLY
                            PCOUNT-PARITY-P
                            equal-phase-fix
                            decode-pcount)
                           (;STEP-PHASE-LIST
                            OPEN-PHASE-LIST-EQUIV-CONS)))
          (and stable-under-simplificationp
               '(:expand ((REPLICATE-XO (PCOUNT-COUNT A))
                          (REPLICATE-OX (PCOUNT-COUNT A))
                          (REPLICATE-OX (+ -1 (PCOUNT-COUNT A)))
                          (REPLICATE-XO (+ -1 (PCOUNT-COUNT A))))))))


;; :X . :N . z            :O . :X
;; :X . :O :P . z         :O . :P :P
;; :X . :O :X :N . z      :O . :X :O :X
;; :X . :O :X :O :P . z   :O . :X :O :P :P

;;    :W
;; --------
;; :N :W :P
;; :N :O :P

(def::un step-pcount-initial (L R)
  (declare (xargs :signature ((t t) pcount-listp)
                  :congruence ((pcount-equiv phase-equiv) equal)))
  (let ((L (pcount-fix L))
        (R (leading-phase R)))
    (pattern-match-list (L R)
      ;; O X O
      ;; X O P
      (((pcount ':W c) (phase ':P))
       (if (< 1 c) (list (pcount :Z (1- c)) (pcount :P 1))
         (list (pcount :X c))))
      (((pcount ':W c) (phase ':X))
       (list (pcount :X c)))
      ;; X O X
      (((pcount ':X c) &)
       (if (equal c 1) (list (pcount :O 1))
         (list (pcount :W c))))
      ;; O X O X
      (((pcount ':Y c) &)
       (list (pcount :Z c)))
      ;; X O (X O)
      ;; O X  O| . .
      (((pcount ':Z c) (phase ':P))
       (if (< 3 c) (list (pcount :W (1- c)) (pcount :P 1))
         (if (equal 2 c) (list (pcount :O 1) (pcount :P 1))
           (list (pcount :Y c)))))
      (((pcount ':Z c) (phase ':X))
       (list (pcount :Y c)))
      ;;
      (((pcount ':O c) (phase ':X))
       (list (pcount :X c)))
      (& ;; (pcount ':O &)
       (list L)))))

(in-theory (disable (:type-prescription step-pcount-initial)))

(def::signature step-pcount-initial (nzpcount-p t) nzpcount-listp)

(defthm pcount-len-step-pcount-initial
  (equal (pcount-len (STEP-PCOUNT-initial L x))
         (pcount-count L))
  :hints (("Goal" :in-theory (enable step-pcount-initial))))

(encapsulate
    ()

  (local (in-theory (enable helper-1 helper-2 helper-3 helper-4)))

  (defthm nth-pcount-entry-step-pcount-initial
    (implies
     (and (nzpcount-p L)
          (wf-pcount-sequence-step (pcount-phase L) v)
          (wf-pcount-initial (pcount-phase L)))
     (equal (nth-pcount i (step-pcount-initial L v))
            (let ((i (nfix i))
                  (L0 L))
              (let ((L (nth-pcount (- i 1) (list L (pcount v 1))))   ; -1 0
                    (M (nth-pcount    i    (list L (pcount v 1))))   ;  0 1
                    (R (nth-pcount (+ i 1) (list L (pcount v 1)))))  ;  1 2
                (if (equal i 0)
                    (first-two-step-phase M R)
                  (if (< i (pcount-count L0))
                      (step-phase l m r)
                    (phase-bit)))))))
    :hints (("goal" :in-theory (enable nth-pcount-entry
                                       first-two-step-phase
                                       step-pcount-initial
                                       ))
            (and stable-under-simplificationp
                 '(:in-theory (enable WF-PCOUNT-SEQUENCE-STEP
                                      )))
            (and stable-under-simplificationp
                 '(:in-theory (enable (phase-bit) nfix)))
            ))

  )

(def::und step-pcount-final (L R)
  (declare (xargs :signature ((t t) pcount-listp)
                  :congruence ((phase-equiv pcount-equiv) equal)))
  (let ((L (trailing-phase L))
        (R (pcount-fix R)))
    (pattern-match-list (L R)
      ;; O X O
      ;; N O X
      (((phase ':N) (pcount ':W c))
       (if (< 1 c)
           (list (pcount :N 1) (pcount :Y (1- c)))
         (list (pcount :X c))))
      (((phase ':X) (pcount ':W c))
       (list (pcount ':X c)))
      ;; X O X
      ((& (pcount ':X c))
       (if (equal c 1) (list (pcount :O 1))
         (list (pcount :W c))))
      ;; O X O X
      ;; N O X O
      (((phase ':N) (pcount ':Y c))
       (if (<= c 1) (list (pcount :X c))
         (if (equal c 2) (list (pcount :N 1) (pcount :O (1- c)))
           (list (pcount :N 1) (pcount :W (1- c))))))
      (((phase ':X) (pcount ':Y c))
       (list (pcount :Z c)))
      ;; P X O X O
      ;; X O X O X
      ((& (pcount ':Z c))
       (list (pcount :Y c)))
      (((phase ':X) (pcount ':O c))
       (list (pcount ':X c)))
      ((& &)
       (list R)))))
      
(in-theory (disable (:type-prescription step-pcount-final)))

(def::signature step-pcount-final (t nzpcount-p) nzpcount-listp
  :hints (("Goal" :in-theory (enable step-pcount-final))))

(defcong trailing-phase-equiv equal (step-pcount-final l r) 1
  :hints (("Goal" :in-theory (enable step-pcount-final))))

(defthm pcount-len-step-pcount-final
  (equal (pcount-len (STEP-PCOUNT-FINAL L x))
         (pcount-count x))
  :hints (("Goal" :in-theory (enable step-pcount-final))))

(encapsulate
    ()

  (local (in-theory (enable helper-1 helper-2 helper-3 helper-4)))

  (defthm nth-pcount-entry-step-pcount-final
    (implies
     (and (nzpcount-p v)
          (weak-pcount-sequence-step l (pcount-phase v))
          (weak-pcount-final (pcount-phase v)))
     (equal (nth-pcount i (step-pcount-final l v))
            (let ((i (nfix i)))  ;; i = 1
              (let ((i (1+ i))   ;; i = 2
                    (l (trailing-phase l))) 
                (let ((l (nth-pcount (- i 1) (list (pcount l 1) v)))  ; 1
                      (m (nth-pcount    i    (list (pcount l 1) v)))  ; 2
                      (r (nth-pcount (+ i 1) (list (pcount l 1) v)))) ; 3
                  (if (< i (pcount-count v))
                      (step-phase l m r)
                    (if (equal i (pcount-count v))
                        (last-two-step-phase l m)
                      (phase-bit))))))))
    :hints (("goal" :in-theory (enable nth-pcount-entry
                                       last-two-step-phase
                                       step-pcount-final))
            (and stable-under-simplificationp
                 '(:in-theory (enable Weak-PCOUNT-SEQUENCE-STEP
                                      )))
            (and stable-under-simplificationp
                 '(:in-theory (enable (phase-bit) nfix)))
            ))

  )

(def::und step-3-tuple (L M R)
  (declare (xargs :signature ((t t t) pcount-listp)
                  :congruence ((phase-equiv pcount-equiv pcount-equiv) equal)))
  (let ((L (trailing-phase L))
        (M (pcount-fix M))
        (R (leading-phase (pcount-phase R))))
    (pattern-match-list (L M R)
      ;; 
      ;; :X
      ;;
      ;; :O :X :O | (:W c) | (:o 1)
      ;; :P :X :O | (:w c) | (:o 1) ;; :p | :x :o :x :o :x | :o
      ;; :O :X :N | (:w c) | (:o 1) 
      ;; :P :X :N | (:w c) | (:o 1) 
      ;;
      ((& (pcount ':X c) &)
       (if (equal c 1) (list (pcount :O 1))
         (list (pcount :W c))))
      ;;
      ;; :N
      ;;
      ;; :X :N :O | (:X 1) (:N c-1)
      ;; :X :N :N | (:X 1) (:N c-1)
      ;; :N :N :O | (:N c)
      ;; :N :N :N | (:N c)
      ;;
      ;; else default case
      (((phase ':X) (pcount ':N c) &)
       (if (equal c 1) (list (pcount :X 1))
         (list (pcount :X 1) (pcount :N (1- c)))))
      ;;
      ;; :P
      ;;
      ;; :O :P :X | (:p c-1) (:x 1)
      ;; :P :P :X | (:p c-1) (:x 1)
      ;; :O :P :P | (:P c)
      ;; :P :P :P | (:p c
      ;;
      ;; else default case
      ((& (pcount ':P c) (phase ':X))
       (if (equal c 1) (list (pcount :X 1))
         (list (pcount :P (1- c)) (pcount :X 1))))
      ;;
      ;; :O
      ;;
      ;; :X :O :X | (:X 1)
      ;; :N :O :X | (:N 1)
      ;; :X :O :P | (:P 1)
      ;; :N :O :P | (:O 1)
      ;;
      (((phase ':X) (pcount ':O c) (phase ':X))
       (list (pcount :X c)))
      (((phase ':N) (pcount ':O c) (phase ':X))
       (list (pcount :N c)))
      (((phase ':X) (pcount ':O c) (phase ':P))
       (list (pcount :P c)))
      (((phase ':N) (pcount ':O c) (phase ':P))
       (list (pcount :O c)))
      ;;
      ;; :W
      ;;
      ;; :N :W :P | (:N 1) (:W c-2) (:P 1)
      ;; :N :W :X | (:N 1) (:Y c-1)        ;; :N o x o :x | :N :N o x :x 
      ;; :X :W :P | (:z c-1) (:P 1) ;; (:x | o x o x o | :p) (:x | x o x o p | P)
      ;; :X :W :X | (:x c)
      ;;
      (((phase ':N) (pcount ':W c) (phase ':P))
       (let ((w (if (equal c 3) (pcount :O 1) (pcount :W (- c 2)))))
         (list (pcount :N 1) w (pcount :P 1))))
      (((phase ':N) (pcount ':W c) (phase ':X))
       (list (pcount :N 1) (pcount :y (1- c))))
      (((phase ':X) (pcount ':W c) (phase ':P))
       (list (pcount :z (1- c)) (pcount :P 1)))
      (((phase ':X) (pcount ':W c) (phase ':X))
       (list (pcount :x c)))
      ;;
      ;; :Y
      ;;
      ;; :X :Y :O | (:Z c)                          ;; (:x | :o :x :o :x | :o)
      ;; :X :Y :N | (:Z c)                          ;; (:x | :o :x :o :x | :n)
      ;; :N :Y :O | (:N 1) (:w c-1) | (:N 1) (:O 1) ;; (:n | :o :x :o :x | :o) (:n | :n :o :x :o | :x) 
      ;; :N :Y :N | (:N 1) (:w c-1) | (:N 1) (:O 1) ;; (:n | :o :x :o :x | :n)
      ;;
      (((phase ':X) (pcount ':Y c) &)
       (list (pcount :Z c)))
      (((phase ':N) (pcount ':Y c) &)
       (let ((y (if (equal c 2) (pcount :O 1) (pcount :w (1- c)))))
         (list (pcount :N 1) y)))
      ;;
      ;; :Z
      ;;
      ;; :O :Z :X | (:Y c)                          ;; (:p | :x :o :x :o | :x) (:n | :o :x | :o)
      ;; :P :Z :X | (:Y c)                          ;; (:p | :x :o :x :o | :x) (:n | :o :x | :o)
      ;; :O :Z :P | (:y c-1) (:P 1) | (:O 1) (:P 1) ;; 
      ;; :P :Z :P | (:y c-1) (:P 1) | (:O 1) (:P 1) ;; (:p | :x :o :x :o | :P) (:x | :o :x :o :p | :P)
      ;;
      ((& (pcount ':Z c) (phase ':X))
       (list (pcount :Y c)))
      ((& (pcount ':Z c) (phase ':P))
       (let ((z (if (equal c 2) (pcount :O 1) (pcount :w (1- c)))))
         (list z (pcount :P 1))))
      ;;
      ((& & &)
       (list M))
      )))

(def::und step-3-tuple-old (L M R)
  (declare (xargs :signature ((t t t) pcount-listp)
                  :congruence ((phase-equiv pcount-equiv pcount-equiv) equal)))
  (let ((L (phase-fix L))
        (M (pcount-fix M))
        (R (pcount-fix R)))
    (pattern-match-list (L M R)
      ;; -----------------------------------------------------------
      ;; passive middle
      ;; -----------------------------------------------------------
      (((phase ':W) (pcount ':P c) (pcount ':X &))
       (if (equal c 1) (list (pcount :X 1))
         (list (pcount :P (1- c)) (pcount :X 1))))
      (((phase ':W) (pcount ':P c) (pcount ':Z &))
       (if (equal c 1) (list (pcount :X 1))
         (list (pcount :P (1- c)) (pcount :X 1))))
      (((phase ':X) (pcount ':N c) (pcount ':Y &))
       (if (equal c 1) (list (pcount :X 1))
         (list (pcount :X 1) (pcount :N (1- c)))))
      (((phase ':X) (pcount ':N c) (pcount ':O &))
       (if (equal c 1) (list (pcount :X 1))
         (list (pcount :X 1) (pcount :N (1- c)))))
      (((phase ':X) (pcount ':N c) (pcount ':W &))
       (if (equal c 1) (list (pcount :X 1))
         (list (pcount :X 1) (pcount :N (1- c)))))
      (((phase ':Y) (pcount ':N c) (pcount ':W &))
       (if (equal c 1) (list (pcount :X 1))
         (list (pcount :X 1) (pcount :N (1- c)))))
      (((phase ':Y) (pcount ':N c) (pcount ':O &))
       (if (equal c 1) (list (pcount :X 1))
         (list (pcount :X 1) (pcount :N (1- c)))))
      (((phase ':Y) (pcount ':N c) (pcount ':Y &))
       (if (equal c 1) (list (pcount :X 1))
         (list (pcount :X 1) (pcount :N (1- c)))))
      (((phase ':Z) (pcount ':P c) (pcount ':X &))
       (if (equal c 1) (list (pcount :X 1))
         (list (pcount :P (1- c)) (pcount :X 1))))
      (((phase ':Z) (pcount ':P c) (pcount ':Z &))
       (if (equal c 1) (list (pcount :X 1))
         (list (pcount :P (1- c)) (pcount :X 1))))
      (((phase ':O) (pcount ':P c) (pcount ':X &))
       (if (equal c 1) (list (pcount :X 1))
         (list (pcount :P (1- c)) (pcount :X 1))))
      (((phase ':O) (pcount ':P c) (pcount ':Z &))
       (if (equal c 1) (list (pcount :X 1))
         (list (pcount :P (1- c)) (pcount :X 1))))
      ;; -----------------------------------------------------------
      ;; active middle
      ;; -----------------------------------------------------------
      (((phase ':N) (pcount ':W c) (pcount ':P &))
       (let ((w (if (equal c 3) (pcount :O 1) (pcount :W (- c 2)))))
         (list (pcount :N 1) w (pcount :P 1))))
      (((phase ':P) (pcount ':X c) (pcount ':N &))
       (if (equal c 1) (list (pcount :O 1))
         (list (pcount :W c))))
      (((phase ':N) (pcount ':Y c) (pcount ':N &))
       (if (equal c 2) (list (pcount :N 1) (pcount :O 1))
         (list (pcount :N 1) (pcount :W (1- c)))))
      (((phase ':P) (pcount ':Z c) (pcount ':P &))
       ;; P | X O X O | P
       ;; X | O X O P | P
       ;;
       ;; P | X O | P
       ;; X | O P | ..
       (if (equal c 2) (list (pcount :O 1) (pcount :P 1))
         (list (pcount :W (1- c)) (pcount :P 1))))
      ((& & &)
       ;; ((phase ':N) (pcount ':O) (pcount ':P))
       (list M))
      )))

(defthm equal-pcount-reduction
  (equal (equal M (pcount p c))
         (and (pcount-p M)
              (equal (pcount-phase M) (phase-fix p))
              (equal (pcount-count M) (pfix c))))
  :hints (("Goal" :in-theory (enable weak-pcount-p
                                     PCOUNT-P
                                     pcount
                                     pcount-phase
                                     pcount-count))))
                                     
(defthm reduction-ad-absurdium
  (implies
   (and
    (nzpcount-p M)
    (wf-pcount-sequence-step L (pcount-phase M))
    (wf-pcount-sequence-step (pcount-phase M) (pcount-phase R)))
   (equal (step-3-tuple-old L M R)
          (step-3-tuple L M R)))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable wf-pcount-sequence-step
                              leading-phase
                              trailing-phase
                              STEP-3-TUPLE-OLD
                              STEP-3-TUPLE))))

(defcong trailing-phase-equiv equal (step-3-tuple L M R) 1
  :hints (("Goal" :in-theory (enable trailing-phase-equiv
                                     trailing-phase
                                     step-3-tuple))))

(defthm weak-pcount-sequence-step-3-tuple
  (implies
   (and
    (nzpcount-p M)
    (weak-pcount-sequence-step Lp (pcount-phase M))
    (weak-pcount-sequence-step (pcount-phase M) (pcount-phase R)))
   (and
    (weak-pcount-sequence-body (step-3-tuple Lp M R))
    (implies
     (weak-pcount-sequence-step (pcount-phase R)
                                (pcount-phase X))
     (weak-pcount-sequence-step (pcount-phase (tcar (step-3-tuple Lp M R)))
                                (pcount-phase (car (step-3-tuple (pcount-phase M) R X)))))))
  :hints (("GOal" :in-theory (e/d (weak-PCOUNT-SEQUENCE-STEP
                                   weak-pcount-sequence-body
                                   step-3-tuple)
                                  (LEADING-PHASE-PCOUNT-PHASE)
                                  ))))
  
(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))
  (local (in-theory (enable step-3-tuple)))

  (local (in-theory (enable helper-1 helper-2 helper-3 helper-4)))

  (def::signature step-3-tuple (t nzpcount-p t) pcount-parity-listp)
  
  (defthm pcount-len-step-3-tuple
    (implies
     (nzpcount-p m)
     (equal (pcount-len (step-3-tuple L M R))
            (pcount-count M))))
  
  (defthm nth-pcount-step-3-tuple
    (implies
     (and (nzpcount-p m)
          (nzpcount-p r)
          (weak-pcount-sequence-step l (pcount-phase m))
          (weak-pcount-sequence-step (pcount-phase m) (pcount-phase r))
          )
     (equal (nth-pcount i (step-3-tuple l m r))
            (let ((i (nfix i)))
              (let ((l (trailing-phase l)))
                (if (and (<= 0 i) (< i (pcount-count m)))
                    (let ((i (1+ i)))
                      (let ((L (nth-pcount (- i 1)   (list (pcount L 1) m r)))
                            (M (nth-pcount    i      (list (pcount L 1) m r)))
                            (R (nth-pcount (+ i 1)   (list (pcount L 1) m r))))
                        (step-phase L M R)))
                  (phase-bit))))))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable weak-pcount-sequence-step
                                      ;;wf-pcount-sequence-step
                                      NTH-PCOUNT-ENTRY
                                      step-phase)))))
      
  )

(defun trailing-pcount-phase-equiv (x y)
  (trailing-phase-equiv (pcount-phase x)
                        (pcount-phase y)))

(defequiv trailing-pcount-phase-equiv)

(defrefinement pcount-equiv trailing-pcount-phase-equiv)

(in-theory (disable trailing-pcount-phase-equiv))

(def::un step-pcount-list-rec (LL L v list)
  (declare (xargs :signature ((t t t t) pcount-p pcount-p pcount-p pcount-listp)
                  :congruence ((pcount-equiv pcount-equiv pcount-equiv pcount-list-equiv) equal)))
  (if (not (consp list)) (list (pcount-fix LL) (pcount-fix L) (pcount-fix v) nil)
    (let ((R (pcount-fix (car list))))
      (let ((plist (step-3-tuple (trailing-phase (pcount-phase L)) v R)))
        (metlist ((LL L v res) (step-pcount-list-rec L v R (cdr list)))
          (list LL L v (append plist res)))))))

(encapsulate
    ()

  (local
   (defthm val3-step-pcount-list-rec-irrelevant
     (implies
      (syntaxp (not (quotep LL)))
      (equal (val 3 (step-pcount-list-rec LL L v list))
             (val 3 (step-pcount-list-rec nil L v list))))))

  ;; Meh .. I don't think this matters ..
  (defthm trailing-pcount-phase-equiv-2-implies-equal-val3-step-pcount-list-rec
    (implies
     (trailing-pcount-phase-equiv L1 L2)
     (equal (val 3 (step-pcount-list-rec LL L1 v list))
            (val 3 (step-pcount-list-rec LL L2 v list))))
    :rule-classes :congruence
    :hints (("Goal" :do-not-induct t
             :expand (:free (L) (step-pcount-list-rec LL L v list))
             :in-theory (enable trailing-pcount-phase-equiv))))

  )

(def::signature step-pcount-list-rec (nzpcount-p nzpcount-p nzpcount-p nzpcount-listp)
  nzpcount-p nzpcount-p nzpcount-p pcount-parity-listp)

(defthm weak-pcount-sequence-rec-step-3-tuple
  (implies (and (nzpcount-p l)
                (nzpcount-p v)
                (nzpcount-p r)
                (weak-pcount-sequence-step (pcount-phase ll)
                                           (pcount-phase l))
                (weak-pcount-sequence-step (pcount-phase l)
                                           (pcount-phase v))
                (weak-pcount-sequence-step (pcount-phase v)
                                           (pcount-phase r)))
           (weak-pcount-sequence-rec (pcount-phase (tcar (step-3-tuple (pcount-phase ll) l v)))
                                     (step-3-tuple (pcount-phase l) v r)))
  :hints (("goal" :in-theory (enable weak-pcount-sequence-step
                                     step-3-tuple))))

(encapsulate
    ()

  (local
   (defthm weak-pcount-sequence-body-val3-step-pcount-list-rec-helper
     (implies
      (and
       (nzpcount-p L)
       (nzpcount-p v)
       (nzpcount-listp list)
       (weak-pcount-sequence-step (pcount-phase LL) (pcount-phase L))
       (weak-pcount-sequence-step (pcount-phase L) (pcount-phase v))
       (weak-pcount-sequence-suffix (pcount-phase v) list))
      (weak-pcount-sequence-rec (pcount-phase (tcar (step-3-tuple (pcount-phase LL) L v)))
                                (val 3 (step-pcount-list-rec LL L v list))))))


  (defthm weak-pcount-sequence-body-val3-step-pcount-list-rec
    (implies
     (and
      (trailing-phase-equiv p (pcount-phase (tcar (step-3-tuple (pcount-phase LL) L v))))
      (nzpcount-p L)
      (nzpcount-p v)
      (nzpcount-listp list)
      (weak-pcount-sequence-step (pcount-phase LL) (pcount-phase L))
      (weak-pcount-sequence-step (pcount-phase L) (pcount-phase v))
      (weak-pcount-sequence-suffix (pcount-phase v) list))
     (weak-pcount-sequence-rec p (val 3 (step-pcount-list-rec LL L v list)))))
  
  
  )

(defthm wf-pcount-sequence-step-step-pcount-list-rec
  (implies
   (and
    (wf-pcount-sequence-step (pcount-phase LL) (pcount-phase L))
    (wf-pcount-sequence-step (pcount-phase L) (pcount-phase v))
    (wf-pcount-sequence-suffix (pcount-phase v) list))
   (and
    (wf-pcount-sequence-step (pcount-phase (val 0 (step-pcount-list-rec LL L v list)))
                             (pcount-phase (val 1 (step-pcount-list-rec LL L v list))))
    (wf-pcount-sequence-step (pcount-phase (val 1 (step-pcount-list-rec LL L v list)))
                             (pcount-phase (val 2 (step-pcount-list-rec LL L v list))))
    (wf-pcount-final (pcount-phase (val 2 (step-pcount-list-rec LL L v list))))))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((step-pcount-list-rec LL L v list)))))

(defthm weak-pcount-sequence-step-step-pcount-list-rec
  (implies
   (and
    (weak-pcount-sequence-step (pcount-phase LL) (pcount-phase L))
    (weak-pcount-sequence-step (pcount-phase L) (pcount-phase v))
    (weak-pcount-sequence-suffix (pcount-phase v) list))
   (and
    (weak-pcount-sequence-step (pcount-phase (val 0 (step-pcount-list-rec LL L v list)))
                             (pcount-phase (val 1 (step-pcount-list-rec LL L v list))))
    (weak-pcount-sequence-step (pcount-phase (val 1 (step-pcount-list-rec LL L v list)))
                             (pcount-phase (val 2 (step-pcount-list-rec LL L v list))))
    (weak-pcount-final (pcount-phase (val 2 (step-pcount-list-rec LL L v list))))))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((step-pcount-list-rec LL L v list)))))

(defthm pcount-len-append
  (equal (pcount-len (append x y))
         (+ (pcount-len x)
            (pcount-len y))))

(defthm pcount-len-val2-step-pcount-list-rec
  (implies
   (and (nzpcount-listp list)
        (nzpcount-p v))
   (equal (pcount-len (val 3 (step-pcount-list-rec LL L v list)))
          (+ (pcount-len list)
             (pcount-count v)
             (- (pcount-count (val 2 (step-pcount-list-rec LL L v list))))))))

(defthm pcount-count-val1-step-pcount-list-rec-bound
  (<= (pcount-count (val 2 (step-pcount-list-rec LL L v list)))
      (+ (pcount-len list)
         (pcount-count v)))
  :rule-classes :linear)

(defthm pcount-count-val1-step-pcount-list-rec-equality-reduction
  (iff (equal (pcount-count (val 2 (step-pcount-list-rec LL L v list)))
              (+ (pcount-count v)
                 (pcount-len list)))
       (not (consp list))))

(defun step-pcount-list-rec-induction-2 (i LL L v list)
  (declare (ignore LL)
           (xargs :measure (len list)))
  (if (not (consp list)) (list i L v list)
    (let ((i (nfix i)))
      (let ((R (pcount-fix (car list))))
        (if (< (+ i 1) (pcount-count v)) (list i L v list)
          (step-pcount-list-rec-induction-2 (- i (pcount-count v)) L v R (cdr list)))))))

(defthm nth-pcount-append
  (equal (nth-pcount i (append x y))
         (if (< (nfix i) (pcount-len x))
             (nth-pcount i x)
           (nth-pcount (+ (nfix i) (- (pcount-len x))) y)))
  :hints (("Goal" :induct (nth-pcount i x))))
  
(defthm equal-nfix-implication
  (implies
   (equal (nfix x) y)
   (nfix-equiv x y))
  :rule-classes (:forward-chaining))

(defthm zero-pcount-len
  (implies
   (nzpcount-listp list)
   (iff (equal (pcount-len list) 0)
        (not (consp list)))))

;; (defthm nfix-plus
;;   (implies
;;    (and (integerp x) (integerp y))
;;    (equal (nfix (+ x y))
;;           (if (< (+ x y) 0) 0
;;             (+ x y)))))
           
(defthm nth-pcount-entry-to-trailing-phase
  (implies
   (and
    (nzpcount-p v)
    (EQUAL (nfix i) (1- (PCOUNT-COUNT V))))
   (equal (NTH-PCOUNT-ENTRY i v)
          (TRAILING-PHASE (PCOUNT-PHASE V))))
  :hints (("Goal" :in-theory (enable NTH-PCOUNT-ENTRY TRAILING-PHASE))))

;;(in-theory (disable open-nth-pcount))

(defthm nth-pcount-step-pcount-list-rec
  (implies
   (and
    (nzpcount-p v)
    (nzpcount-listp list)
    (weak-pcount-sequence-step (pcount-phase l) (pcount-phase v))
    (weak-pcount-sequence-suffix (pcount-phase v) list)
    )
   (equal (nth-pcount i (val 3 (step-pcount-list-rec LL L v list)))
          (let ((i (nfix i)))
            (if (< i (+ (pcount-len list)
                        (pcount-count v)
                        (- (pcount-count (val 2 (step-pcount-list-rec LL L v list))))))
                (let ((i (1+ i))
                      (l (trailing-phase (pcount-phase L))))
                  (let ((L (nth-pcount (- i 1)   (list* (pcount L 1) v list)))
                        (M (nth-pcount    i      (list* (pcount L 1) v list)))
                        (R (nth-pcount (+ i 1)   (list* (pcount L 1) v (tcons list
                                                                              (val 2 (step-pcount-list-rec LL L v list)))))))
                    (step-phase L M R)))
              (phase-bit)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable nfix)
           :do-not '(eliminate-destructors)
           :expand ((STEP-PCOUNT-LIST-REC LL L V LIST)
                    )
           :induct (step-pcount-list-rec-induction-2 i LL L v list))
          ))

;;
;; On to better things ..
;;

(def::und step-pcount-list-suffix (LL L v list)
  (declare (xargs :signature ((t t t t) pcount-listp)
                  :congruence ((pcount-equiv pcount-equiv pcount-equiv pcount-list-equiv) equal)))
  (metlist ((LL L v res) (step-pcount-list-rec LL L v list))
    (declare (ignore LL))
    (append res (step-pcount-final (pcount-phase L) v))))


(defthm WEAK-PCOUNT-FINAL-TCAR-STEP-PCOUNT-FINAL
  (implies
   (weak-pcount-final (pcount-phase R))
   (WEAK-PCOUNT-FINAL (PCOUNT-PHASE (TCAR (STEP-PCOUNT-FINAL L R)))))
  :hints (("Goal" :in-theory (enable weak-pcount-final
                                     STEP-PCOUNT-FINAL))))
  
(defthmd tcar-append
  (equal (tcar (append x y))
         (if (not (consp y))
             (tcar x)
           (tcar y))))

(defthm weak-pcount-final-tcar-step-pcount-list-suffix
  (implies
   (and
    (weak-pcount-sequence-step (pcount-phase LL) (pcount-phase L))
    (weak-pcount-sequence-step (pcount-phase L) (pcount-phase v))
    (weak-pcount-sequence-suffix (pcount-phase v) list))
   (weak-pcount-final (pcount-phase (tcar (step-pcount-list-suffix LL L v list)))))
  :hints (("Goal" :in-theory (enable tcar-append
                                     step-pcount-list-suffix)
           :do-not-induct t)))

(defthm weak-pcount-sequence-rec-step-pcount-final
  (implies
   (and
    (nzpcount-p m)
    (nzpcount-p r)
    (weak-pcount-final (pcount-phase r))
    (weak-pcount-sequence-step lp (pcount-phase m))
    (weak-pcount-sequence-step (pcount-phase m) (pcount-phase r)))
   (weak-pcount-sequence-rec
    (pcount-phase
     (tcar
      (step-3-tuple lp m r)))
    (step-pcount-final (pcount-phase m) r)))
  :hints (("goal" :in-theory (enable step-3-tuple
                                     step-pcount-final
                                     weak-pcount-sequence-step
                                     weak-pcount-final))))

(encapsulate
    ()
  
  (defthm consp-val3-STEP-PCOUNT-LIST-REC
    (iff (consp (VAL 3 (STEP-PCOUNT-LIST-REC LL L V list)))
         (consp list)))
  
  (local (in-theory (enable tcar-append)))
  
  (defthm tcar-val3-STEP-PCOUNT-LIST-REC
    (implies
     (consp list)
     (equal (tcar (VAL 3 (STEP-PCOUNT-LIST-REC LL L V LIST)))
            (tcar (step-3-tuple (pcount-phase (VAL 0 (STEP-PCOUNT-LIST-REC LL L V LIST)))
                                (VAL 1 (STEP-PCOUNT-LIST-REC LL L V LIST))
                                (val 2 (STEP-PCOUNT-LIST-REC LL L V LIST)))))))

  (local
   (defthm weak-pcount-sequence-rec-step-pcount-list-suffix-helper
     (implies
      (and
       (nzpcount-p L)
       (nzpcount-p v)
       (nzpcount-listp list)
       (weak-pcount-sequence-step (pcount-phase LL) (pcount-phase L))
       (weak-pcount-sequence-step (pcount-phase L) (pcount-phase v))
       (weak-pcount-sequence-suffix (pcount-phase v) list))
      (weak-pcount-sequence-rec (pcount-phase (tcar (step-3-tuple (pcount-phase LL) L v)))
                                (step-pcount-list-suffix LL L v list)))
     :hints (("Goal" :in-theory (enable step-pcount-list-suffix)
              :do-not-induct t))))

  (defthm weak-pcount-sequence-rec-step-pcount-list-suffix
    (implies
     (and
      (trailing-phase-equiv p (pcount-phase (tcar (step-3-tuple (pcount-phase LL) L v))))
      (nzpcount-p L)
      (nzpcount-p v)
      (nzpcount-listp list)
      (weak-pcount-sequence-step (pcount-phase LL) (pcount-phase L))
      (weak-pcount-sequence-step (pcount-phase L) (pcount-phase v))
      (weak-pcount-sequence-suffix (pcount-phase v) list))
     (weak-pcount-sequence-rec p (step-pcount-list-suffix LL L v list))))
  
  )

(defthm pcount-len-tcons
  (equal (pcount-len (tcons x a))
         (+ (pcount-len x)
            (pcount-count a))))

(defthm pcount-len-step-pcount-list-suffix
  (implies
   (and
    (nzpcount-p v)
    (nzpcount-listp list))
   (equal (pcount-len (step-pcount-list-suffix LL L v list))
          (+ (pcount-len list)
             (pcount-count v))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (step-pcount-list-suffix)
                           (STEP-PCOUNT-FINAL)))))

(defthm last-phase-bit
  (implies
   (and (nzpcount-p v) (nzpcount-listp list))
   (equal (trailing-phase (pcount-phase (val 2 (step-pcount-list-rec LL l v list))))
          (nth-pcount (+ (pcount-count v) (pcount-len list) -1) (list* v list)))))

(defthm nth-pcount-entry-val1-step-pcount-list-rec-reduction
  (implies
   (and
    (nzpcount-p v)
    (nzpcount-listp list))
   (equal (nth-pcount-entry i (val 2 (step-pcount-list-rec LL l v list)))
          (if (not (consp list))
              (nth-pcount-entry i v)
            (if (< (nfix i) (pcount-count (val 2 (step-pcount-list-rec LL l v list))))
                (nth-pcount (+ (nfix i) (pcount-len list)
                               (- (pcount-count (val 2 (step-pcount-list-rec LL l v list)))))
                            list)
              (phase-bit)))))
  :hints (("goal" :induct (step-pcount-list-rec LL l v list)
           :do-not-induct t
           :expand (:free (i) (nth-pcount i list))
           :in-theory (e/d (;;open-nth-pcount-consp
                            NTH-PCOUNT-ENTRY-out-of-bounds)
                           ()
                           )))
  )

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))
  
  (defthm val0-step-pcount-list-rec-reduction
    (implies
     (and
      (nzpcount-p v)
      (nzpcount-listp list))
     (equal (trailing-phase (pcount-phase (val 1 (step-pcount-list-rec LL l v list))))
            (if (not (consp list))
                (trailing-phase (pcount-phase L))
              (if (not (consp (cdr list)))
                  (trailing-phase (pcount-phase v))
                (nth-pcount (+ (pcount-len list)
                               (- (pcount-count (val 2 (step-pcount-list-rec LL l v list))))
                               -1)
                            list)))))
    :hints (("goal" :induct (step-pcount-list-rec LL l v list)
             :do-not-induct t
             :expand (:free (i) (nth-pcount i list))
             )))

  )

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (encapsulate
       ()

     (defthm not-consp-1
       (implies
        (and
         (<= (+ (pcount-count v)
                (pcount-len list)
                (- (pcount-count (val 2 (step-pcount-list-rec LL l v list)))))
             (nfix i))
         (< (nfix i) (pcount-count v)))
        (not (consp list)))
       :rule-classes (:forward-chaining))

     (defthm not-consp-2
       (implies
        (and
         (< (+ 1 (pcount-count v) (pcount-len list))
            (+ (nfix i)
               (pcount-count (val 2 (step-pcount-list-rec LL l v list)))))
         (< (+ 1 (nfix i)) (pcount-count v))
         )
        (not (consp list)))
       :rule-classes (:forward-chaining))

     (defthm not-consp-3
       (implies
        (and
         (equal (+ (nfix i)
                   (pcount-count (val 2 (step-pcount-list-rec LL l v list))))
                (+ 1 (pcount-count v)
                   (pcount-len list)))
         (< (+ 1 (nfix i)) (pcount-count v))
         )
        (not (consp list)))
       :rule-classes (:forward-chaining))

     (defthm not-consp-4
       (implies
        (and (equal (+ (nfix i)
                       (pcount-count (val 2 (step-pcount-list-rec LL l v list))))
                    (+ (pcount-count v) (pcount-len list)))
             (< (+ 1 (nfix i)) (pcount-count v))
             
             )
        (not (consp list)))
       :rule-classes (:forward-chaining))

     (defthm open-step-pcount-list-rec-consp-cdr
       (implies
        (and (consp list)
             (not (consp (cdr list))))
        (equal (step-pcount-list-rec LL L v list)
               (let ((r (pcount-fix (car list))))
                 (let ((plist (step-3-tuple (trailing-phase (pcount-phase L)) v r)))
                   (metlist ((LL l v res) (step-pcount-list-rec L v r (cdr list)))
                     (list LL l v (append plist res))))))))
     
     (defthm pinch
       (implies
        (and
         (nzpcount-p v)
         (nzpcount-listp list)
         (consp list))
        (iff (equal (+ (pcount-count v)
                       (pcount-count (car list))
                       (pcount-len (cdr list)))
                    (+ 1 (pcount-count (val 2 (step-pcount-list-rec LL l v list)))))
             (and (not (consp (cdr list)))
                  (equal (pcount-count v) 1))))
       :hints (("goal" :do-not-induct t
                :expand (step-pcount-list-rec LL l v list)
                :use pcount-len-val2-step-pcount-list-rec
                :in-theory (disable pcount-len-val2-step-pcount-list-rec))))

     (defthm if-val1-is-greater-than-list-then-list-is-not-consp
       (implies
        (and
         (pcount-p (val 2 (step-pcount-list-rec LL L v list)))
         (< (pcount-len list)
            (pcount-count (val 2 (step-pcount-list-rec LL L v list)))))
        (not (consp list))))

     (defthm lte-val1-step-pcount-list-rec-reduction
       (implies
        (nzpcount-p v)
        (iff (< (pcount-count (val 2 (step-pcount-list-rec LL L v list)))
                (pcount-len list))
             (not (or (not (consp list))
                      (not (consp (cdr list))))))))

     (defthm open-STEP-PCOUNT-LIST-REC-not-consp
       (implies
        (not (consp list))
        (equal (STEP-PCOUNT-LIST-REC LL L V list)
               (LIST (pcount-fix LL) (PCOUNT-FIX L) (PCOUNT-FIX V) NIL))))     
     
     (defthm nth-pcount-existentionality
       (implies
        (equal x y)
        (iff (phase-equiv (NTH-PCOUNT x LIST)
                          (nth-pcount y list)) t)))
     
     (defthm nth-pcount-entry-exentionality
       (implies
        (equal x y)
        (iff (phase-equiv (NTH-PCOUNT-entry x LIST)
                          (nth-pcount-entry y list)) t)))
     
     (defthm strong-arm-last-two-step-phase
       (implies
        ;;(case-split
        (and (phase-equiv x a)
             (phase-equiv y b))
        ;;)
        (iff (equal (last-two-step-phase x y)
                    (last-two-step-phase a b)) t)))
     
     (defthm strong-arm-step-phase
       (implies
        ;;(case-split
         (and (phase-equiv x a)
              (phase-equiv y b)
              (phase-equiv z c))
         ;;)
        (iff (equal (step-phase x y z)
                    (step-phase a b c)) t)))

     ))

  (skip-proofs
   (defthm nth-pcount-step-pcount-list-suffix
    (implies
     (and
      (nzpcount-p v)
      (nzpcount-listp list)
      (weak-pcount-sequence-step (pcount-phase l) (pcount-phase v))
      (weak-pcount-sequence-suffix (pcount-phase v) list)
      )
     (equal (nth-pcount i (step-pcount-list-suffix LL L v list))
            (let ((i (nfix i)))
              (let ((i (1+ i))) 
                (let ((L (trailing-phase (pcount-phase L))))
                  (let ((L (nth-pcount (- i 1)   (list* (pcount L 1) v list)))  ;; 1
                        (M (nth-pcount    i      (list* (pcount L 1) v list)))  ;; 2
                        (R (nth-pcount (+ i 1)   (list* (pcount L 1) v list)))) ;; 3
                    (if (< i (+ (pcount-len list) (pcount-count v)))
                        (step-phase L M R)
                      (if (equal i (+ (pcount-len list) (pcount-count v)))
                          (last-two-step-phase L M)
                        (phase-bit)))))))))
    :hints (("Goal" :in-theory (e/d (STEP-PCOUNT-LIST-SUFFIX)
                                    (open-nth-pcount))
             :do-not '(eliminate-destructors fertilize)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:in-theory (e/d (nfix
                                    strong-arm-step-phase
                                    strong-arm-last-two-step-phase)
                                   (open-nth-pcount))))
            (and stable-under-simplificationp
                 '(:expand ((:free (i) (NTH-PCOUNT i LIST)))))
            (and stable-under-simplificationp
                 '(:expand ((:free (i) (NTH-PCOUNT i (cdr list))))))
            (and stable-under-simplificationp
                 '(:expand ((:free (i) (NTH-PCOUNT i (cddr list))))))
            ))
   )
  )

(in-theory (disable step-pcount-initial))

(def::und alt-pcount (L R)
  (declare (xargs :signature ((t t) nzpcount-p)
                  :congruence ((pcount-equiv pcount-equiv) equal)))
  (let ((L (pcount-phase L))
        (R (leading-phase (pcount-phase R))))
    (pattern-match-list (L R)
      (((phase ':Y) &) ;; :N :O
       (pcount :X 1))
      (((phase ':O) (phase ':X))
       (pcount :X 1))
      (((phase ':O) (phase ':P))
       (pcount :N 1))
      (((phase ':W) &)
       (pcount :N 1))
      (((phase ':N) &)
       (pcount :N 1))
      ((& &)
       (pcount :P 1)))))

(def::un step-pcount-list (list)
  (declare (xargs :signature ((t) pcount-listp)
                  :congruence ((pcount-list-equiv) equal)))
  (if (not (consp list)) nil
    (let ((L (pcount-fix (car list))))
      (if (not (consp (cdr list))) (list (step-pcount-only L))
        (let ((v (pcount-fix (cadr list))))
          (let ((p (step-pcount-initial L (leading-phase (pcount-phase v)))))
            (append p (step-pcount-list-suffix (alt-pcount L v) L v (cddr list)))))))))

(defthm weak-pcount-initial-step-pcount-initial
  (implies
   (weak-pcount-initial (pcount-phase l))
   (weak-pcount-initial
    (pcount-phase (car (step-pcount-initial l r)))))
  :hints (("goal" :in-theory (enable weak-pcount-initial
                                     step-pcount-initial))))

(defthm weak-pcount-only-step-pcount-only
  (implies (weak-pcount-only (pcount-phase x))
           (weak-pcount-only (pcount-phase (step-pcount-only x))))
  :hints (("goal" :in-theory (enable step-pcount-only wf-pcount-only))))

(defthm weak-pcount-sequence-rec-step-pcount-initial
  (implies
   (weak-pcount-initial (pcount-phase l))
   (weak-pcount-sequence-rec
    (pcount-phase (car (step-pcount-initial l r)))
    (cdr (step-pcount-initial l r))))
  :hints (("goal" :in-theory (enable step-pcount-initial
                                     weak-pcount-initial))))

(defthm wf-pcount-sequence-step-alt-pcount
  (implies
   (and
    (weak-pcount-initial (pcount-phase l))
    (weak-pcount-sequence-step (pcount-phase l) (pcount-phase r)))
   (weak-pcount-sequence-step (pcount-phase (alt-pcount l r))
                              (pcount-phase l)))
  :hints (("goal" :in-theory (e/d (alt-pcount
                                   WEAK-PCOUNT-SEQUENCE-STEP
                                   leading-phase
                                   weak-pcount-initial)
                                  (LEADING-PHASE-PCOUNT-PHASE)))))

(encapsulate
    ()

  (local
   (defthm what-are-the-odds
     (implies
      (and
       (nzpcount-p l)
       (weak-pcount-sequence-step (pcount-phase l) (pcount-phase r))
       (weak-pcount-initial (pcount-phase l))
       )
      (trailing-phase-equiv (pcount-phase
                             (tcar (step-3-tuple (pcount-phase (alt-pcount l r)) l r)))
                            (if (consp (cdr (step-pcount-initial l (nth-pcount-entry 0 r))))
                                (pcount-phase
                                 (tcar (cdr (step-pcount-initial l (nth-pcount-entry 0 r)))))
                              (pcount-phase (car (step-pcount-initial l (nth-pcount-entry 0 r)))))))
     :hints (("goal" :in-theory (e/d (trailing-phase-equiv
                                      trailing-phase
                                      alt-pcount
                                      weak-pcount-sequence-step
                                      nth-pcount-entry
                                      step-pcount-initial
                                      step-3-tuple)
                                     ())))))
     
  (local
   (defthm consp-STEP-PCOUNT-LIST-SUFFIX 
     (consp (STEP-PCOUNT-LIST-SUFFIX LL L V list))
     :hints (("Goal" :in-theory (enable STEP-PCOUNT-LIST-SUFFIX)))))

  (defthm weak-pcount-sequence-step-pcount-list
    (implies
     (and
      (nzpcount-listp list)
      (weak-pcount-sequence list))
     (weak-pcount-sequence (step-pcount-list list)))
    :hints (("Goal" :in-theory (e/d (weak-pcount-sequence-suffix-reduction
                                     Weak-PCOUNT-SEQUENCE
                                     consp-append
                                     tcar-append
                                     car-append
                                     cdr-append
                                     weak-pcount-sequence-body-reduction
                                     weak-pcount-sequence)
                                    (WEAK-PCOUNT-SEQUENCE-SUFFIX-CONSP))
             :do-not-induct t)))

  )
  
(defthm weak-pcount-sequence-step-leading-phase
  (iff (weak-pcount-sequence-step x (leading-phase y))
       (weak-pcount-sequence-step x y))
  :hints (("Goal" :in-theory (enable weak-pcount-sequence-step
                                     leading-phase))))

(defthm wf-pcount-sequence-step-leading-phase
  (iff (wf-pcount-sequence-step x (leading-phase y))
       (wf-pcount-sequence-step x y))
  :hints (("Goal" :in-theory (enable wf-pcount-sequence-step
                                     leading-phase))))

(defthm nth-pcount-entry-as-LEADING-PHASE-pcount-phase
  (EQUAL (NTH-PCOUNT-ENTRY 0 A)
         (LEADING-PHASE (PCOUNT-PHASE A)))
  :hints (("Goal" :in-theory (enable NTH-PCOUNT-ENTRY LEADING-PHASE))))

(in-theory (disable LEADING-PHASE-PCOUNT-PHASE))

(defthm initial-unit-phase
  (implies
   (and
    (equal (pcount-count x) 1)
    (nzpcount-p x)
    (Weak-PCOUNT-INITIAL (PCOUNT-PHASE x)))
   (concrete-phase-p (pcount-phase x)))
  :hints (("Goal" :in-theory (enable concrete-phase-p
                                     PCOUNT-PARITY-P
                                     nzpcount-p
                                     Weak-PCOUNT-INITIAL))))

(defthmd only-unit-phase
  (implies
   (and
    (equal (pcount-count x) 1)
    (nzpcount-p x)
    (Weak-PCOUNT-ONLY (PCOUNT-PHASE x)))
   (equal (pcount-phase x) :X))
  :hints (("Goal" :in-theory (enable concrete-phase-p
                                     Weak-PCOUNT-ONLY
                                     PCOUNT-PARITY-P
                                     nzpcount-p
                                     WF-PCOUNT-INITIAL))))

(skip-proofs
 (defthm nth-pcount-step-pcount-list
  (implies
   (and
    (nzpcount-listp x)
    (case-split (weak-pcount-sequence x)))
   (equal (nth-pcount i (step-pcount-list x))
          (let ((i (nfix i)))
            (let ((L (nth-pcount (- i 1) x))
                  (M (nth-pcount    i    x))
                  (R (nth-pcount (+ i 1) x)))
              (if (<= (pcount-len x) i) (phase-bit)
                (if (equal i 0)
                    (if (equal (pcount-len x) 1)
                        :X
                      (first-two-step-phase M R))
                  (if (< (1+ i) (pcount-len x))
                      (step-phase L M R)
                    (last-two-step-phase L M))))))))
  ;;:otf-flg t
  :hints (("Goal" :in-theory (e/d (nth-pcount
                                   weak-pcount-sequence)
                                  ())
           :do-not-induct t)
          (and stable-under-simplificationp
               '(:in-theory (enable weak-pcount-only
                                    step-pcount-only
                                    step-pcount-initial)))
          (and stable-under-simplificationp
               '(:in-theory (enable leading-phase
                                    only-unit-phase
                                    leading-phase
                                    trailing-phase
                                    nzpcount-p
                                    pcount-parity-p
                                    nth-pcount-entry
                                    WEAK-PCOUNT-SEQUENCE-STEP
                                    )))))
 )

(def::un alternate (phase count)
  (declare (xargs :signature ((t t) pcount-p)))
  (let ((phase (phase-fix phase))
        (count (pfix count)))
    (if (memberp phase '(:X :Z))
        (if (even-p count)
            (pcount :Z count)
          (pcount :X count))
      (if (memberp phase '(:O :W :Y))
          (if (even-p count) (pcount :Y count)
            (if (equal count 1) (pcount :O count)
              (pcount :W count)))
        (pcount phase count)))))

(defthm nzcount-p-alternate
  (nzpcount-p (alternate phase count))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((alternate phase count))))
  :hints (("Goal" :in-theory (enable pos-odd-not-1-implication
                                     non-zero-even-is-gte))))

(defthm pcount-alternate
  (equal (pcount-count (alternate phase count))
         (pfix count)))

(defthm nth-pcount-entry-alternate
  (equal (nth-pcount-entry i (alternate phase count))
         (let ((i     (nfix i))
               (phase (phase-fix phase))
               (count (pfix count)))
           (if (<= count i) (phase-bit)
             (if (memberp phase '(:X :Z))
                 (if (even-p i) :X :O)
               (if (memberp phase '(:O :W :Y))
                   (if (even-p i) :O :X)
                 phase)))))
  :hints (("Goal" :in-theory (enable nth-pcount-entry))))

(in-theory (disable alternate))

(defthm equal-trailing-phase-n
  (iff (equal (trailing-phase x) :N)
       (phase-equiv x :N))
  :hints (("Goal" :in-theory (enable trailing-phase))))

(defthm equal-trailing-phase-p
  (iff (equal (trailing-phase x) :P)
       (phase-equiv x :P))
  :hints (("Goal" :in-theory (enable trailing-phase))))

(def::un compress-rec (L pre list)
  (declare (ignorable L)
           (xargs :signature ((t nzpcount-p nzpcount-listp) nzpcount-listp)))
  (if (not (consp list)) (list pre)
    (let ((entry (pcount-fix (car list)))
          (phase (pcount-phase pre)))
      (let ((last  (trailing-phase phase))
            (count (pcount-count pre)))
        (pattern-match-list (last entry)
          ((':N (pcount ':N c))
           (compress-rec L (pcount phase (+ count c)) (cdr list)))
          ((':P (pcount ':P c))
           (compress-rec L (pcount phase (+ count c)) (cdr list)))
          ((':O (pcount ':X c))
           (compress-rec L (alternate phase (+ count c)) (cdr list)))
          ((':O (pcount ':Z c))
           (compress-rec L (alternate phase (+ count c)) (cdr list)))
          ((':X (pcount ':W c))
           (compress-rec L (alternate phase (+ count c)) (cdr list)))
          ((':X (pcount ':Y c))
           (compress-rec L (alternate phase (+ count c)) (cdr list)))
          ((':X (pcount ':O c))
           (compress-rec L (alternate phase (+ count c)) (cdr list)))
          (&
           (cons pre (compress-rec (trailing-phase (pcount-phase pre)) entry (cdr list))))
          )))))

(defthm TRAILING-PHASE-choices
  (or (PHASE-EQUIV (PCOUNT-PHASE PRE) :N)
      (PHASE-EQUIV (PCOUNT-PHASE PRE) :P)
      (EQUAL (TRAILING-PHASE (PCOUNT-PHASE PRE)) :O)
      (EQUAL (TRAILING-PHASE (PCOUNT-PHASE PRE)) :X))
  :rule-classes ((:forward-chaining :trigger-terms ((TRAILING-PHASE (PCOUNT-PHASE PRE)))))
  :hints (("Goal" :in-theory (enable TRAILING-PHASE))))

(defthm normalize-trailing-phase-constant-WEAK-PCOUNT-SEQUENCE-REC
  (implies
   (and
    (syntaxp (quotep p1))
    (equal p2 (trailing-phase p1))
    (syntaxp (not (equal p2 p1))))
   (iff (WEAK-PCOUNT-SEQUENCE-REC p1 list)
        (WEAK-PCOUNT-SEQUENCE-REC p2 list))))

(defthm normalize-trailing-phase-constant-WEAK-PCOUNT-SEQUENCE-suffix
  (implies
   (and
    (syntaxp (quotep p1))
    (equal p2 (trailing-phase p1))
    (syntaxp (not (equal p2 p1))))
   (iff (WEAK-PCOUNT-SEQUENCE-suffix p1 list)
        (WEAK-PCOUNT-SEQUENCE-suffix p2 list))))

(defun leading-phase-equiv (x y)
  (equal (leading-phase x)
         (leading-phase y)))

(defequiv leading-phase-equiv)

(defrefinement phase-equiv leading-phase-equiv)

(defcong leading-phase-equiv equal (leading-phase x) 1)

(defthm leading-phase-equiv-leading-phase
  (leading-phase-equiv (leading-phase x) x)
  :hints (("Goal" :in-theory (enable leading-phase))))

(in-theory (disable leading-phase-equiv))

(defthm leading-phase-alternate
  (leading-phase-equiv (pcount-phase (alternate phase c))
                       phase)
  :hints (("Goal" :in-theory (enable leading-phase-equiv alternate))))

(defthm leading-phase-compress-rec
  (leading-phase-equiv (pcount-phase (car (compress-rec L pre list)))
                       (pcount-phase pre)))

(defcong leading-phase-equiv equal (wf-pcount-initial x) 1
  :hints (("Goal" :in-theory (enable leading-phase-equiv
                                     leading-phase
                                     wf-pcount-initial))))

(defthm wf-pcount-sequence-suffix-compress-rec
  (implies
   (and
    (nzpcount-p pre)
    (nzpcount-listp list)
    (wf-pcount-sequence-step L (pcount-phase pre))
    (weak-pcount-sequence-rec (trailing-phase (pcount-phase pre)) list))
   (wf-pcount-sequence-rec L (compress-rec L pre list)))
  :hints (("Goal" :induct (compress-rec L pre list)
           :do-not-induct t)
          (and stable-under-simplificationp
               '(:in-theory (enable
                             ALTERNATE
                             WEAK-PCOUNT-SEQUENCE-STEP
                             WF-PCOUNT-SEQUENCE-STEP)))))

(defun nth-pcount-compress-rec-induction (i L pre list)
  (declare (ignorable L)
           (xargs :measure (len list)))
  (if (not (consp list)) (list i pre)
    (let ((entry (pcount-fix (car list)))
          (phase (pcount-phase pre)))
      (let ((i     (nfix i))
            (last  (trailing-phase phase))
            (count (pcount-count pre)))
        (pattern-match-list (last entry)
          ((':N (pcount ':N c))
           (nth-pcount-compress-rec-induction i L (pcount phase (+ count c)) (cdr list)))
          ((':P (pcount ':P c))
           (nth-pcount-compress-rec-induction i L (pcount phase (+ count c)) (cdr list)))
          ((':O (pcount ':X c))
           (nth-pcount-compress-rec-induction i L (alternate phase (+ count c)) (cdr list)))
          ((':O (pcount ':Z c))
           (nth-pcount-compress-rec-induction i L (alternate phase (+ count c)) (cdr list)))
          ((':X (pcount ':W c))
           (nth-pcount-compress-rec-induction i L (alternate phase (+ count c)) (cdr list)))
          ((':X (pcount ':Y c))
           (nth-pcount-compress-rec-induction i L (alternate phase (+ count c)) (cdr list)))
          ((':X (pcount ':O c))
           (nth-pcount-compress-rec-induction i L (alternate phase (+ count c)) (cdr list)))
          (&
           (nth-pcount-compress-rec-induction (- i (pcount-count pre)) (trailing-phase (pcount-phase pre)) entry (cdr list)))
          )))))

(defthm pcount-len-compress-rec
  (equal (pcount-len (compress-rec L pre list))
         (+ (pcount-count pre)
            (pcount-len list))))

(defthm one-of-four
  (or (PHASE-EQUIV (PCOUNT-PHASE PRE) :N)
      (PHASE-EQUIV (PCOUNT-PHASE PRE) :P)
      (EQUAL (TRAILING-PHASE (PCOUNT-PHASE PRE)) :O)
      (EQUAL (TRAILING-PHASE (PCOUNT-PHASE PRE)) :X))
  :rule-classes ((:forward-chaining :trigger-terms ((TRAILING-PHASE (PCOUNT-PHASE PRE)))))
  :hints (("Goal" :in-theory (enable trailing-phase))))

;;(in-theory (disable PCOUNT-PARITY-P-IMPLIES-1))

(encapsulate
    ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm even-p-negation
    (implies
     (integerp x)
     (equal (even-p (- x))
            (even-p x)))
    :hints (("Goal" :in-theory (e/d (even-p) (mod)))))
  )


(skip-proofs
 (defthm nth-pcount-compress-rec
  (implies
   (and
    (nzpcount-p pre)
    (nzpcount-listp list))
   (equal (nth-pcount i (compress-rec L pre list))
          (let ((i (nfix i)))
            (if (< i (pcount-count pre))
                (nth-pcount-entry i pre)
              (nth-pcount (- i (pcount-count pre)) list)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d ()
                           (pcount-parity-p-implies-1))
           :expand ((compress-rec L pre list))
           :do-not '(generalize eliminate-destructors)
           :induct (nth-pcount-compress-rec-induction i L pre list))
          (and stable-under-simplificationp
               '(:in-theory (e/d (leading-phase
                                  NTH-PCOUNT-ENTRY
                                  open-nth-pcount-consp
                                  TRAILING-PHASE)
                                 ())))))
 )

(def::und wf-pcount-pre (x)
  (declare (xargs :signature ((t) concrete-phase-p)))
  (let ((phase (pcount-phase x)))
    (if (memberp phase '(:W :Y :O))
        :N
      (if (memberp phase '(:X :Z))
          :P
        (if (equal phase :N)
            :X
          :O)))))

(defthm wf-pcount-sequence-step-wf-pcount-pre
  (wf-pcount-sequence-step (wf-pcount-pre x) (pcount-phase x))
  :hints (("Goal" :in-theory (enable wf-pcount-sequence-step
                                     wf-pcount-pre))))

(def::un compress (list)
  (declare (xargs :signature ((nzpcount-listp) nzpcount-listp)))
  (if (not (consp list)) nil
    (compress-rec (wf-pcount-pre (car list)) (car list) (cdr list))))

(defthm wf-pcount-only-COMPRESS-REC 
  (implies
   (and
    (not (consp (cdr (COMPRESS-REC L pre list))))
    (nzpcount-p pre)
    (nzpcount-listp list)
    (case-split (weak-pcount-sequence-suffix (pcount-phase pre) list))
    (case-split (< 1 (+ (pcount-count pre) (pcount-len list)))))
   (wf-pcount-only (PCOUNT-PHASE (CAR (COMPRESS-REC L pre list)))))
  :hints (("Goal" :induct (COMPRESS-REC L pre list)
           :do-not-induct t
           :expand (COMPRESS-REC L pre list))
          (and stable-under-simplificationp
               '(:in-theory (enable weak-pcount-initial
                                    weak-pcount-final
                                    trailing-phase
                                    ALTERNATE)))))

(defthm wf-pcount-final-COMPRESS-REC
  (IMPLIES
   (and
    (consp list)
    (WEAK-PCOUNT-FINAL (PCOUNT-PHASE (TCAR list))))
   (WF-PCOUNT-FINAL (PCOUNT-PHASE (TCAR (COMPRESS-REC L PRE LIST)))))
  :hints (("Goal" :induct (COMPRESS-REC L PRE LIST))
          (and stable-under-simplificationp
               '(:in-theory (enable TRAILING-PHASE
                                    ALTERNATE)))))

(encapsulate
    ()

  (local
   (defthm sigh-helper
     (implies
      (and
       (NZPCOUNT-LISTP (COMPRESS-REC L pre zed))
       (consp list)
       (wf-pcount-sequence-rec L list))
      (wf-pcount-sequence-rec (pcount-phase (car list))
                              (cdr list)))))

  (local
   (defthm dont-do-this
     (implies
      (and (consp list) (consp (cdr list)))
      (equal (tcar (cdr list))
             (tcar list)))))

  (defthm wf-pcount-sequence-compress
    (implies
     (and
      (nzpcount-listp list)
      (weak-pcount-sequence list))
     (wf-pcount-sequence (compress list)))
    :otf-flg t
    :hints (("Goal" :do-not-induct t
             :in-theory (enable weak-pcount-sequence
                                wf-pcount-sequence
                                weak-pcount-sequence-suffix-reduction
                                wf-pcount-sequence-suffix-reduction))))
  
  )

(defthm pcount-len-compress
  (equal (pcount-len (compress list))
         (pcount-len list)))

(defthm nth-pcount-compress
  (implies
   (nzpcount-listp list)
   (equal (nth-pcount i (compress list))
          (nth-pcount i list))))

(def::un pcount-bad ()
  (declare (xargs :signature (() nzpcount-listp)))
  (list
   (pcount :O 1)
   (pcount :P 27)
   (pcount :X 1)))

(defthm wf-pcount-sequence-pcount-pcount-bad
  (wf-pcount-sequence (pcount-bad)))

(def::un pcount-seq ()
  (declare (xargs :signature (() nzpcount-listp)))
  (list
   (pcount :W 3)
   (pcount :P 3)
   (pcount :X 1)
   (pcount :N 4)
   (pcount :Y 2)
   (pcount :N 4)
   (pcount :O 1)
   (pcount :P 4)
   (pcount :Z 2)
   (pcount :P 4)
   (pcount :X 1)))

(defthm wf-pcount-sequence-pcount-pcount-seq
  (wf-pcount-sequence (pcount-seq)))

(def::un pcount-eqv1 ()
  (declare (xargs :signature (() nzpcount-listp)))
  (list
   (pcount :W 3)
   (pcount :P 3)
   (pcount :X 1)
   (pcount :N 10)
   (pcount :O 1)
   (pcount :P 10)
   (pcount :X 1)))

(defthm wf-pcount-sequence-pcount-pcount-eqv1
  (wf-pcount-sequence (pcount-eqv1)))

(def::un pcount-eqv2 ()
  (declare (xargs :signature (() nzpcount-listp)))
  (list
   (pcount :W 3)
   (pcount :P 3)
   (pcount :X 23)))

(defthm wf-pcount-sequence-pcount-pcount-eqv2
  (wf-pcount-sequence (pcount-eqv2)))

(def::un pcount-eqv3 ()
  (declare (xargs :signature (() nzpcount-listp)))
  (list
   (pcount :O 1)
   (pcount :P 5)
   (pcount :X 23)))

(defthm wf-pcount-sequence-pcount-pcount-eqv3
  (wf-pcount-sequence (pcount-eqv3)))

(def::un pcount-eqv4 ()
  (declare (xargs :signature (() nzpcount-listp)))
  (list
   (pcount :X 29)))

(defthm wf-pcount-sequence-pcount-pcount-eqv4
  (wf-pcount-sequence (pcount-eqv4)))

;; --------------------------------------------------
;; --------------------------------------------------

(def::un phase-seq ()
  (declare (xargs :signature (() phase-listp)))
  (decode-pcount-list (pcount-seq)))

(defthm wf-phase-sequence-pcount-phase-seq
  (wf-phase-sequence (phase-seq)))

(def::un phase-eqv1 ()
  (declare (xargs :signature (() phase-listp)))
  (decode-pcount-list (pcount-eqv1)))

(defthm wf-phase-sequence-pcount-phase-eqv1
  (wf-phase-sequence (phase-eqv1)))

(def::un phase-eqv2 ()
  (declare (xargs :signature (() phase-listp)))
  (decode-pcount-list (pcount-eqv2)))

(defthm wf-phase-sequence-pcount-phase-eqv2
  (wf-phase-sequence (phase-eqv2)))

(def::un phase-eqv3 ()
  (declare (xargs :signature (() phase-listp)))
  (decode-pcount-list (pcount-eqv3)))

(defthm wf-phase-sequence-pcount-phase-eqv3
  (wf-phase-sequence (phase-eqv3)))

(def::un phase-eqv4 ()
  (declare (xargs :signature (() phase-listp)))
  (decode-pcount-list (pcount-eqv4)))

(defthm wf-phase-sequence-pcount-phase-eqv4
  (wf-phase-sequence (phase-eqv4)))

(def::un phase-bad ()
  (declare (xargs :signature (() phase-listp)))
  (decode-pcount-list (pcount-bad)))

(defthm wf-phase-baduence-pcount-phase-bad
  (wf-phase-sequence (phase-bad)))

(def::un nz-seq ()
  (declare (xargs :signature (() nz-listp)))
  (decode-phase-list (phase-seq)))

(def::un nz-bad ()
  (declare (xargs :signature (() nz-listp)))
  (decode-phase-list (phase-bad)))

(make-event
 (pprogn
  (set-fmt-soft-right-margin 10000 state)
  (set-fmt-hard-right-margin 10000 state)
  (value '(value-triple :done)))
 :check-expansion t)

(defun print-line (x)
  (cw "~f0~%" x))

(defun nz-to-sign (x)
  (if (< x 0) '- '+))

(defun map-sign (list)
  (if (not (consp list)) nil
    (cons (nz-to-sign (car list))
          (map-sign (cdr list)))))

(defun print-step-nz (n time st)
  (if (zp n) (print-line (list time (map-sign st)))
    (prog2$
     (print-line (list time (map-sign st)))
     (let ((st (step-nz-list st)))
       (print-step-nz (1- n) (1+ time) st)))))

;;
;; ACL2 !>(print-step-nz 11 0 (nz-seq))
;;
;; (0  ( + - + + + + - - - - - + - - - - - + + + + + - + + + + + ))
;; (1  ( - + + + + - + - - - - - + - - - - + + + + - + + + + + - ))
;; (2  ( + + + + - + - + - - - - - + - - - + + + - + + + + + - + ))
;; (3  ( + + + - + - + - + - - - - - + - - + + - + + + + + - + - ))
;; (4  ( + + - + - + - + - + - - - - - + - + - + + + + + - + - + ))
;; (5  ( + - + - + - + - + - + - - - - - + - + + + + + - + - + - ))
;; (6  ( - + - + - + - + - + - + - - - - - + + + + + - + - + - + ))
;; (7  ( + - + - + - + - + - + - + - - - - + + + + - + - + - + - ))
;; (8  ( - + - + - + - + - + - + - + - - - + + + - + - + - + - + ))
;; (9  ( + - + - + - + - + - + - + - + - - + + - + - + - + - + - ))
;; (10 ( - + - + - + - + - + - + - + - + - + - + - + - + - + - + ))
;; (11 ( + - + - + - + - + - + - + - + - + - + - + - + - + - + - ))
;;

;;  o o o o
;; L R L R
;;   L R L R

;; With N drones there are N+1 "locations".
;; So it would take N+1 steps to traverse the whole perimeter.
;; 

;;
;; ACL2 !>(print-step-nz 28 0 (nz-bad))
;;
;; (0  (+ + + + + + + + + + + + + + + + + + + + + + + + + + + +))
;; (1  (+ + + + + + + + + + + + + + + + + + + + + + + + + + + -))
;; (2  (+ + + + + + + + + + + + + + + + + + + + + + + + + + - +))
;; (3  (+ + + + + + + + + + + + + + + + + + + + + + + + + - + -))
;; (4  (+ + + + + + + + + + + + + + + + + + + + + + + + - + - +))
;; (5  (+ + + + + + + + + + + + + + + + + + + + + + + - + - + -))
;; (6  (+ + + + + + + + + + + + + + + + + + + + + + - + - + - +))
;; (7  (+ + + + + + + + + + + + + + + + + + + + + - + - + - + -))
;; (8  (+ + + + + + + + + + + + + + + + + + + + - + - + - + - +))
;; (9  (+ + + + + + + + + + + + + + + + + + + - + - + - + - + -))
;; (10 (+ + + + + + + + + + + + + + + + + + - + - + - + - + - +))
;; (11 (+ + + + + + + + + + + + + + + + + - + - + - + - + - + -))
;; (12 (+ + + + + + + + + + + + + + + + - + - + - + - + - + - +))
;; (13 (+ + + + + + + + + + + + + + + - + - + - + - + - + - + -))
;; (14 (+ + + + + + + + + + + + + + - + - + - + - + - + - + - +))
;; (15 (+ + + + + + + + + + + + + - + - + - + - + - + - + - + -))
;; (16 (+ + + + + + + + + + + + - + - + - + - + - + - + - + - +))
;; (17 (+ + + + + + + + + + + - + - + - + - + - + - + - + - + -))
;; (18 (+ + + + + + + + + + - + - + - + - + - + - + - + - + - +))
;; (19 (+ + + + + + + + + - + - + - + - + - + - + - + - + - + -))
;; (20 (+ + + + + + + + - + - + - + - + - + - + - + - + - + - +))
;; (21 (+ + + + + + + - + - + - + - + - + - + - + - + - + - + -))
;; (22 (+ + + + + + - + - + - + - + - + - + - + - + - + - + - +))
;; (23 (+ + + + + - + - + - + - + - + - + - + - + - + - + - + -))
;; (24 (+ + + + - + - + - + - + - + - + - + - + - + - + - + - +))
;; (25 (+ + + - + - + - + - + - + - + - + - + - + - + - + - + -))
;; (26 (+ + - + - + - + - + - + - + - + - + - + - + - + - + - +))
;; (27 (+ - + - + - + - + - + - + - + - + - + - + - + - + - + -))
;; (28 (- + - + - + - + - + - + - + - + - + - + - + - + - + - +))
;;

(defun print-step-phase (n time st)
  (if (zp n) (print-line (list time st))
    (prog2$
     (print-line (list time st))
     (let ((st (step-phase-list st)))
       (print-step-phase (1- n) (1+ time) st)))))

;;
;; ACL2 !> (print-step-phase 11 0 (phase-seq))
;;
;; (0  (:O :X :O :P :P :P :X :N :N :N :N :O :X :N :N :N :N :O :P :P :P :P :X :O :P :P :P :P :X))
;; (1  (:X :O :P :P :P :X :O :X :N :N :N :N :O :X :N :N :N :O :P :P :P :X :O :P :P :P :P :X :O))
;; (2  (:O :P :P :P :X :O :X :O :X :N :N :N :N :O :X :N :N :O :P :P :X :O :P :P :P :P :X :O :X))
;; (3  (:O :P :P :X :O :X :O :X :O :X :N :N :N :N :O :X :N :O :P :X :O :P :P :P :P :X :O :X :O))
;; (4  (:O :P :X :O :X :O :X :O :X :O :X :N :N :N :N :O :X :O :X :O :P :P :P :P :X :O :X :O :X))
;; (5  (:O :X :O :X :O :X :O :X :O :X :O :X :N :N :N :N :O :X :O :P :P :P :P :X :O :X :O :X :O))
;; (6  (:X :O :X :O :X :O :X :O :X :O :X :O :X :N :N :N :N :O :P :P :P :P :X :O :X :O :X :O :X))
;; (7  (:O :X :O :X :O :X :O :X :O :X :O :X :O :X :N :N :N :O :P :P :P :X :O :X :O :X :O :X :O))
;; (8  (:X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :N :N :O :P :P :X :O :X :O :X :O :X :O :X))
;; (9  (:O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :N :O :P :X :O :X :O :X :O :X :O :X :O))
;; (10 (:X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (11 (:O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;;

;;
;; ACL2 !> (print-step-phase 11 0 (phase-eqv1))
;;
;; (0  (:O :X :O :P :P :P :X :N :N :N :N :N :N :N :N :N :N :O :P :P :P :P :P :P :P :P :P :P :X))
;; (1  (:X :O :P :P :P :X :O :X :N :N :N :N :N :N :N :N :N :O :P :P :P :P :P :P :P :P :P :X :O))
;; (2  (:O :P :P :P :X :O :X :O :X :N :N :N :N :N :N :N :N :O :P :P :P :P :P :P :P :P :X :O :X))
;; (3  (:O :P :P :X :O :X :O :X :O :X :N :N :N :N :N :N :N :O :P :P :P :P :P :P :P :X :O :X :O))
;; (4  (:O :P :X :O :X :O :X :O :X :O :X :N :N :N :N :N :N :O :P :P :P :P :P :P :X :O :X :O :X))
;; (5  (:O :X :O :X :O :X :O :X :O :X :O :X :N :N :N :N :N :O :P :P :P :P :P :X :O :X :O :X :O))
;; (6  (:X :O :X :O :X :O :X :O :X :O :X :O :X :N :N :N :N :O :P :P :P :P :X :O :X :O :X :O :X))
;; (7  (:O :X :O :X :O :X :O :X :O :X :O :X :O :X :N :N :N :O :P :P :P :X :O :X :O :X :O :X :O))
;; (8  (:X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :N :N :O :P :P :X :O :X :O :X :O :X :O :X))
;; (9  (:O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :N :O :P :X :O :X :O :X :O :X :O :X :O))
;; (10 (:X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (11 (:O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;;

;;
;; ACL2 !> (print-step-phase 11 0 (phase-eqv2))
;;
;; (0  (:O :X :O :P :P :P :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (1  (:X :O :P :P :P :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;; (2  (:O :P :P :P :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (3  (:O :P :P :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;; (4  (:O :P :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (5  (:O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;; (6  (:X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (7  (:O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;; (8  (:X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (9  (:O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;; (10 (:X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (11 (:O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;;


;;
;; ACL2 !> (print-step-phase 11 0 (phase-eqv3))
;;
;; (0  (:O :P :P :P :P :P :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (1  (:O :P :P :P :P :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;; (2  (:O :P :P :P :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (3  (:O :P :P :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;; (4  (:O :P :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (5  (:O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;; (6  (:X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (7  (:O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;; (8  (:X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (9  (:O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;; (10 (:X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (11 (:O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;;

;;
;; ACL2 !> (print-step-phase 11 0 (phase-eqv4))
;;
;; (0  (:X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (1  (:O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;; (2  (:X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (3  (:O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;; (4  (:X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (5  (:O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;; (6  (:X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (7  (:O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;; (8  (:X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (9  (:O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;; (10 (:X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (11 (:O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;;

;; ACL2 !> (print-step-phase 28 0 (phase-bad))
;;
;; (0  (:O :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :X))
;; (1  (:O :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :X :O))
;; (2  (:O :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :X :O :X))
;; (3  (:O :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :X :O :X :O))
;; (4  (:O :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :X :O :X :O :X))
;; (5  (:O :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :X :O :X :O :X :O))
;; (6  (:O :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :X :O :X :O :X :O :X))
;; (7  (:O :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :X :O :X :O :X :O :X :O))
;; (8  (:O :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :X :O :X :O :X :O :X :O :X))
;; (9  (:O :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :X :O :X :O :X :O :X :O :X :O))
;; (10 (:O :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :X :O :X :O :X :O :X :O :X :O :X))
;; (11 (:O :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :X :O :X :O :X :O :X :O :X :O :X :O))
;; (12 (:O :P :P :P :P :P :P :P :P :P :P :P :P :P :P :P :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (13 (:O :P :P :P :P :P :P :P :P :P :P :P :P :P :P :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;; (14 (:O :P :P :P :P :P :P :P :P :P :P :P :P :P :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (15 (:O :P :P :P :P :P :P :P :P :P :P :P :P :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;; (16 (:O :P :P :P :P :P :P :P :P :P :P :P :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (17 (:O :P :P :P :P :P :P :P :P :P :P :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;; (18 (:O :P :P :P :P :P :P :P :P :P :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (19 (:O :P :P :P :P :P :P :P :P :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;; (20 (:O :P :P :P :P :P :P :P :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (21 (:O :P :P :P :P :P :P :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;; (22 (:O :P :P :P :P :P :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (23 (:O :P :P :P :P :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;; (24 (:O :P :P :P :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (25 (:O :P :P :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;; (26 (:O :P :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;; (27 (:O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O))
;; (28 (:X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X :O :X))
;;

(defun print-step-pcount (n time st)
  (if (zp n) (print-line (list time st))
    (prog2$
     (print-line (list time st))
     (let ((st (step-pcount-list st)))
       (let ((st (compress st)))
         (print-step-pcount (1- n) (1+ time) st))))))

;;
;; ACL2 !> (print-step-pcount 11 0 (pcount-seq))
;;
;; (0  ((:W 3) (:P 3) (:X 1) (:N 4) (:Y 2) (:N 4) (:O 1) (:P 4) (:Z 2) (:P 4) (:X 1)))
;; (1  ((:Z 2) (:P 3) (:X 3) (:N 4) (:Y 2) (:N 3) (:O 1) (:P 3) (:Z 2) (:P 4) (:Z 2)))
;; (2  ((:O 1) (:P 3) (:X 5) (:N 4) (:Y 2) (:N 2) (:O 1) (:P 2) (:Z 2) (:P 4) (:X 3)))
;; (3  ((:O 1) (:P 2) (:X 7) (:N 4) (:Y 2) (:N 1) (:O 1) (:P 1) (:Z 2) (:P 4) (:Z 4)))
;; (4  ((:O 1) (:P 1) (:X 9) (:N 4)               (:W 5)               (:P 4) (:X 5)))
;; (5  ((:Y 12)              (:N 4)               (:W 3)               (:P 4) (:Z 6)))
;; (6  ((:X 13)              (:N 4)               (:O 1)               (:P 4) (:X 7)))
;; (7  ((:Y 14)              (:N 3)               (:O 1)               (:P 3) (:Z 8)))
;; (8  ((:X 15)              (:N 2)               (:O 1)               (:P 2) (:X 9)))
;; (9  ((:Y 16)              (:N 1)               (:O 1)               (:P 1) (:Z 10)))
;; (10 (                                          (:X 29)                            ))
;; (11 (                                          (:W 29)                            ))
;;
;;
;; ACL2 !> (print-step-pcount 28 0 (pcount-bad))
;;
;; (0  ((:O 1) (:P 27) (:X 1) ))
;; (1  ((:O 1) (:P 26) (:Z 2) ))
;; (2  ((:O 1) (:P 25) (:X 3) ))
;; (3  ((:O 1) (:P 24) (:Z 4) ))
;; (4  ((:O 1) (:P 23) (:X 5) ))
;; (5  ((:O 1) (:P 22) (:Z 6) ))
;; (6  ((:O 1) (:P 21) (:X 7) ))
;; (7  ((:O 1) (:P 20) (:Z 8) ))
;; (8  ((:O 1) (:P 19) (:X 9) ))
;; (9  ((:O 1) (:P 18) (:Z 10)))
;; (10 ((:O 1) (:P 17) (:X 11)))
;; (11 ((:O 1) (:P 16) (:Z 12)))
;; (12 ((:O 1) (:P 15) (:X 13)))
;; (13 ((:O 1) (:P 14) (:Z 14)))
;; (14 ((:O 1) (:P 13) (:X 15)))
;; (15 ((:O 1) (:P 12) (:Z 16)))
;; (16 ((:O 1) (:P 11) (:X 17)))
;; (17 ((:O 1) (:P 10) (:Z 18)))
;; (18 ((:O 1) (:P 9)  (:X 19)))
;; (19 ((:O 1) (:P 8)  (:Z 20)))
;; (20 ((:O 1) (:P 7)  (:X 21)))
;; (21 ((:O 1) (:P 6)  (:Z 22)))
;; (22 ((:O 1) (:P 5)  (:X 23)))
;; (23 ((:O 1) (:P 4)  (:Z 24)))
;; (24 ((:O 1) (:P 3)  (:X 25)))
;; (25 ((:O 1) (:P 2)  (:Z 26)))
;; (26 ((:O 1) (:P 1)  (:X 27)))
;; (27 (               (:W 29)))
;; (28 (               (:X 29)))
;;

(def::un squash (x)
  (declare (xargs :signature ((pcount-listp) pcount-listp)))
  (case-match x
    ((a . z)
     (pattern-match a
       ((pcount ':X l)
        (pattern-match z
          ((list* (pcount ':N b) (pcount ':O 1) (pcount ':P b) (pcount ':X r) z)
           (cons (pcount :X (+ (nfix l) (nfix b) 1 (nfix b) (nfix r)))
                 (squash z)))
          ((list* (pcount ':O 1) (pcount ':X r) z)
           (cons (pcount :X (+ (nfix l) 1 (nfix r)))
                 (squash z)))
          (& (cons a (squash z)))))
       ((pcount ':Y l)
        (pattern-match z
          ((list* (pcount ':N b) (pcount ':O 1) (pcount ':P b) (pcount ':X r) z)
           (cons (pcount :Y (+ (nfix l) (nfix b) 1 (nfix b) (nfix r)))
                 (squash z)))
          ((list* (pcount ':O 1) (pcount ':X r) z)
           (cons (pcount :Y (+ (nfix l) 1 (nfix r)))
                 (squash z)))
          (& (cons a (squash z)))))
       (&
        (cons a (squash z)))))
    (& nil)))

(def::un s1 (pre list)
  (declare (xargs :signature ((pcount-listp pcount-listp) pcount-listp)))
  (pattern-match list
    ((cons (pcount ':w (pos c)) rst)
     (if (not (consp rst)) (append pre list)
       (let ((m (if (equal c 3) (pcount :O 1) (pcount :w (- c 2)))))
         (s1 (append pre (list (pcount :n 1) m (pcount :P 1))) rst))))
    ((cons a rst)
     (s1 (tcons pre a) rst))
    (& (append pre list))))

(defthm nzpcount-listp-append
  (implies
   (nzpcount-listp x)
   (iff (nzpcount-listp (append x y))
        (nzpcount-listp y))))

(defthm nzpcount-listp-tcons
  (implies
   (nzpcount-listp x2)
   (iff (nzpcount-listp (tcons x2 a))
        (nzpcount-p a))))

(def::signature s1 (nzpcount-listp nzpcount-listp) nzpcount-listp)

(defthm weak-pcount-sequence-append
  (iff (weak-pcount-sequence (append x y))
       (if (not (consp x)) (weak-pcount-sequence y)
         (if (equal (+ (len x) (len y)) 1) (weak-pcount-only (pcount-phase (car x)))
           (and (weak-pcount-initial (pcount-phase (car x)))
                (weak-pcount-sequence-rec (pcount-phase (car x)) (cdr x))
                (if (not (consp y)) (weak-pcount-final (pcount-phase (tcar x)))
                  (weak-pcount-sequence-suffix (pcount-phase (tcar x)) y))))))
  :hints (("Goal" :in-theory (enable WEAK-PCOUNT-SEQUENCE-SUFFIX-REDUCTION
                                     consp-append
                                     car-append
                                     tcar-append
                                     weak-pcount-sequence))))
                  
(defthm weak-pcount-sequence-rec-tcons
  (iff (weak-pcount-sequence-rec p (tcons res a))
       (if (consp res)
           (and (weak-pcount-sequence-rec p res)
                (weak-pcount-sequence-step (pcount-phase (tcar res)) (pcount-phase a)))
         (weak-pcount-sequence-step p (pcount-phase a)))))

(encapsulate
    ()

  (local
   (encapsulate
       ()

     (defthm joe
       (equal (tcons (append x y) z)
              (append x (tcons y z))))
     
     (defthm zoo
       (equal (append (append x y) z)
              (append x y z)))
     
     (defthmd s1-pre-reduction-helper
       (equal (s1 (append x pre) list)
              (append x (s1 pre list)))
       :hints (("Goal" :induct (s1 pre list)
                :expand (S1 (APPEND X PRE) LIST))))
     
     ))
  
  (defthmd s1-pre-reduction
    (implies
     (and
      (syntaxp (not (equal pre *nil*)))
      (true-listp pre))
     (equal (s1 pre list)
            (append pre (s1 nil list))))
    :hints (("Goal" :do-not-induct t
             :use (:instance s1-pre-reduction-helper
                             (x pre)
                             (pre nil)))))

  )

(defun weak-pcount-sequence-prefix (pre)
  (and (consp pre)
       (weak-pcount-initial (pcount-phase (car pre)))
       (weak-pcount-sequence-rec (pcount-phase (car pre)) (cdr pre))))

(defun weak-pcount-sequence-step-r-fix (r)
  (let ((r (phase-fix r)))
    (if (MEMBERP R '(:N :O :Y :W)) :O :X)))

(defun weak-pcount-sequence-step-r-equiv (x y)
  (equal (weak-pcount-sequence-step-r-fix x)
         (weak-pcount-sequence-step-r-fix y)))

(defequiv weak-pcount-sequence-step-r-equiv)

(defthm weak-pcount-sequence-step-r-equiv-weak-pcount-sequence-step-r-fix
  (weak-pcount-sequence-step-r-equiv (weak-pcount-sequence-step-r-fix x) x))

(defrefinement phase-equiv weak-pcount-sequence-step-r-equiv)

(defun weak-pcount-sequence-step-l-fix (l)
  (let ((l (phase-fix l)))
    (if (MEMBERP L '(:N :X :Y)) :X :O)))

(defun weak-pcount-sequence-step-l-equiv (x y)
  (equal (weak-pcount-sequence-step-l-fix x)
         (weak-pcount-sequence-step-l-fix y)))

(defequiv weak-pcount-sequence-step-l-equiv)

(defthm weak-pcount-sequence-step-l-equiv-weak-pcount-sequence-step-l-fix
  (weak-pcount-sequence-step-l-equiv (weak-pcount-sequence-step-l-fix x) x))

(defrefinement phase-equiv weak-pcount-sequence-step-l-equiv)

(defcong weak-pcount-sequence-step-l-equiv equal (weak-pcount-sequence-step l r) 1
  :hints (("Goal" :in-theory (enable weak-pcount-sequence-step))))

(defcong weak-pcount-sequence-step-r-equiv equal (weak-pcount-sequence-step l r) 2
  :hints (("Goal" :in-theory (enable weak-pcount-sequence-step))))

(in-theory (disable weak-pcount-sequence-step-l-fix weak-pcount-sequence-step-r-fix))

(defthm normalize-constant-weak-pcount-sequence-step-l
  (implies
   (and
    (syntaxp (quotep l1))
    (equal l2 (weak-pcount-sequence-step-l-fix l1))
    (syntaxp (not (equal l1 l2))))
   (equal (weak-pcount-sequence-step l1 r)
          (weak-pcount-sequence-step l2 r))))

(defthm normalize-constant-weak-pcount-sequence-step-r
  (implies
   (and
    (syntaxp (quotep r1))
    (equal r2 (weak-pcount-sequence-step-r-fix r1))
    (syntaxp (not (equal r1 r2))))
   (equal (weak-pcount-sequence-step l r1)
          (weak-pcount-sequence-step l r2))))

(defthm weak-pcount-sequence-s1
  (implies
   (and
    (nzpcount-listp pre)
    (nzpcount-listp list)
    (consp list)
    (weak-pcount-sequence-prefix pre)
    (weak-pcount-sequence-suffix (pcount-phase (tcar pre)) list))
   (weak-pcount-sequence (s1 pre list)))
  :hints (("goal" :induct (s1 pre list)
           :in-theory (enable tcar-append)
           :expand (weak-pcount-sequence list))
          (and stable-under-simplificationp
               '(:in-theory (e/d (tcar-append
                                  weak-pcount-sequence-suffix-reduction
                                  weak-pcount-sequence)
                                 (weak-pcount-sequence-suffix-consp))))))

(defthm pcount-len-s1
  (implies
   (nzpcount-listp list)
   (equal (pcount-len (s1 pre list))
          (+ (pcount-len pre)
             (pcount-len list)))))

;; . . . . (W c) . . .
;; . . . . + (w (- 2 c)) 
;; (def::un s1-domain (pre list)
;;   (declare (xargs :signature ((pcount-listp pcount-listp) pcount-listp)))
;;   (pattern-match list
;;     ((cons (pcount ':w c) rst)
;;      (append (enumerate (pcount-len pre) c)
;;              (le
;;              (s1 (append pre (list (pcount :n 1) (pcount :w (- c 2)) (pcount :P 1))) rst)))
;;     ((cons a rst)
;;      (s1 (tcons pre a) rst))
;;     (& nil)))

;; (defthm consp-s1
;;   (equal (consp (s1 pre list))
;;          (or (consp pre)
;;              (consp list))))

;; (defthm car-s1-consp
;;   (implies
;;    (consp pre)
;;    (equal (car (s1 pre list))
;;           (car pre))))

;; (defthm cadr-s1-consp
;;   (implies
;;    (consp (cdr pre))
;;    (equal (cadr (s1 pre list))
;;           (cadr pre))))

;; - They are equivalent outside of the updated domains
;; - The updated domains get smaller with each step
;; - 

#+dag
(defthm nth-pcount-step-pcount-list-s1
  (implies
   (and
    (nzpcount-listp list)
    (nzpcount-listp pre)
    (consp list)
    (weak-pcount-sequence-prefix pre)
    (weak-pcount-sequence-suffix (pcount-phase (tcar pre)) list))
   (equal (nth-pcount i (step-pcount-list (s1 pre list)))
          (nth-pcount i (step-pcount-list (append pre list)))))
  :hints (("Goal" :in-theory (e/d (CAR-APPEND
                                   tcar-append
                                   CDR-APPEND
                                   CONSP-APPEND
                                   weak-pcount-sequence-suffix-reduction
                                   weak-pcount-sequence)
                                  (step-pcount-list
                                   weak-pcount-sequence-suffix-consp))
           :do-not-induct t)))
         

(in-theory (disable pcount-p))

(defun enumerate (k n)
  (if (zp k) nil
    (if (even-p n)
        (cons 1 (enumerate (1- k) (/ n 2)))
      (cons -1 (enumerate (1- k) (/ (- n 1) 2))))))

(defun enum-all-rec (k n)
  (let ((x (enumerate k n)))
    (if (zp n) (list x)
      (cons x (enum-all-rec k (1- n))))))

(defun enum-all (k)
  (enum-all-rec k (1- (expt 2 k))))


;; Can you write a simulator without "compressing"?
;;
;; :X expands
;; :W contracts
;; :Y moves right
;; :Z moves left

;; (:P ) (:X ) (:N )
;; 
;; (:W ) ..
;; 
