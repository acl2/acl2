;;  
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")

(include-book "level-3-signed-abstraction")

;; ==================================================================
;; phase abstraction
;; ==================================================================

;; ----------------------------------------
;; phase
;; ----------------------------------------

;;
;;   (R)
;;    ^
;;   O|P 
;;  --+-- > (L)
;;   N|X 
;;

(defun phase-p (x)
  (declare (type t x))
  (memberp x '(:N :O :P :W :X :Y :Z)))

(defthm phase-p-implication
  (implies
   (phase-p x)
   (or (equal x :N)
       (equal x :O)
       (equal x :P)
       (equal x :W)
       (equal x :X)
       (equal x :Y)
       (equal x :Z)))
  :rule-classes (:forward-chaining))

(def::un phase-fix (x)
  (declare (xargs :signature ((t) phase-p)))
  (if (phase-p x) x :X))

(defthm phase-fix-phase-p
  (implies
   (phase-p x)
   (equal (phase-fix x) x)))

(defun phase-equiv (x y)
  (declare (type t x y))
  (equal (phase-fix x)
         (phase-fix y)))

(defequiv phase-equiv)

(defthm phase-equiv-phase-fix
  (phase-equiv (phase-fix x) x))

(defcong phase-equiv equal (phase-fix x) 1)

(defthm phase-equiv-choices
  (or (phase-equiv x :N)
      (phase-equiv x :O)
      (phase-equiv x :P)
      (phase-equiv x :W)
      (phase-equiv x :X)
      (phase-equiv x :Y)
      (phase-equiv x :Z))
  :rule-classes ((:forward-chaining :trigger-terms ((phase-equiv x :N)
                                                    (phase-equiv x :X)
                                                    (phase-equiv x :O)))))

(defthm equal-phase-fix
  (equal (equal (phase-fix x) y)
         (and (phase-p y)
              (phase-equiv x y))))

(in-theory (disable phase-p phase-fix phase-equiv))

(theory-invariant (incompatible (:rewrite equal-phase-fix)
                                (:definition phase-equiv)))

(defun any-p (x)
  (declare (type t x)
           (ignore x))
  t)

(def-pattern-match-constructor phase any-p (phase-fix))

;; ----------------------------------------

(defun concrete-phase-p (x)
  (declare (type t x))
  (memberp x '(:N :O :P :X)))

(defthm concrete-phase-implies-phase
  (implies
   (concrete-phase-p x)
   (phase-p x))
  :rule-classes (:rewrite :forward-chaining))

(defthm concrete-phase-p-implication
  (implies
   (concrete-phase-p x)
   (and (not (equal x :W))
        (not (equal x :Y))
        (not (equal x :Z))
        (or (equal x :N)
            (equal x :O)
            (equal x :P)
            (equal x :X))))
  :rule-classes (:forward-chaining))

(defthm concrete-phase-p-implication-2
  (implies
   (concrete-phase-p x)
   (and (not (phase-equiv x :W))
        (not (phase-equiv x :Y))
        (not (phase-equiv x :Z))
        (or (phase-equiv x :N)
            (phase-equiv x :O)
            (phase-equiv x :P)
            (phase-equiv x :X))))
  :rule-classes ((:forward-chaining :trigger-terms ((concrete-phase-p x)
                                                    (phase-equiv x :N)
                                                    (phase-equiv x :O)
                                                    (phase-equiv x :X)))))

(def::un concrete-phase-fix (x)
  (declare (xargs :signature ((t) concrete-phase-p)))
  (if (concrete-phase-p x) x :X))

(defthm concrete-phase-fix-concrete-phase-p
  (implies
   (concrete-phase-p x)
   (equal (concrete-phase-fix x) x)))

(defun concrete-phase-equiv (x y)
  (declare (type t x y))
  (equal (concrete-phase-fix x)
         (concrete-phase-fix y)))

(defequiv concrete-phase-equiv)

(defrefinement phase-equiv concrete-phase-equiv 
  :hints (("Goal" :in-theory (e/d (phase-fix
                                   phase-equiv)
                                  (equal-phase-fix)))))

(defthm concrete-phase-equiv-concrete-phase-fix
  (concrete-phase-equiv (concrete-phase-fix x) x))

(defcong concrete-phase-equiv equal (concrete-phase-fix x) 1)

(defthmd equal-concrete-phase-fix
  (equal (equal (concrete-phase-fix x) y)
         (and (concrete-phase-p y)
              (concrete-phase-equiv x y))))

(defthm concrete-phase-equiv-choices
  (or (concrete-phase-equiv x :N)
      (concrete-phase-equiv x :O)
      (concrete-phase-equiv x :P)
      (concrete-phase-equiv x :X))
  :rule-classes ((:forward-chaining :trigger-terms ((concrete-phase-equiv x :X)))))

(def::und leading-phase (phase)
  (declare (xargs :signature ((t) concrete-phase-p)
                  :congruence ((phase-equiv) equal)))
  (let ((phase (phase-fix phase)))
    (if (memberp phase (list :Y :W))
        :O
      (if (memberp phase (list :X :Z))
          :X
        phase))))

(def::und trailing-phase (phase)
  (declare (xargs :signature ((t) concrete-phase-p)
                  :congruence ((phase-equiv) equal)))
  (let ((phase (phase-fix phase)))
    (if (memberp phase (list :Z :W))
        :O
      (if (memberp phase (list :X :Y))
          :X
        phase))))

(defthm TRAILING-PHASE-trailing-phase
  (equal (TRAILING-PHASE (TRAILING-PHASE v))
         (TRAILING-PHASE v))
  :hints (("Goal" :in-theory (enable TRAILING-PHASE))))

(defun trailing-phase-equiv (x y)
  (equal (trailing-phase x)
         (trailing-phase y)))

(defequiv trailing-phase-equiv)

(defrefinement phase-equiv trailing-phase-equiv)

(defthm trailing-phase-equiv-trailing-phase
  (trailing-phase-equiv (trailing-phase x) x))

(defcong trailing-phase-equiv equal (trailing-phase x) 1)

(in-theory (disable trailing-phase-equiv))

(defthm concrete-phase-p-leading-phase
  (implies
   (concrete-phase-p x)
   (phase-equiv (leading-phase x) x)))

(defthm concrete-phase-p-trailing-phase
  (implies
   (concrete-phase-p x)
   (phase-equiv (trailing-phase x) x)))

(in-theory (disable concrete-phase-p concrete-phase-fix concrete-phase-equiv))


;; ----------------------------------------

(defun phase-listp (list)
  (declare (type t list))
  (if (not (consp list)) (null list)
    (and (phase-p (car list))
         (phase-listp (cdr list)))))

(defthm phase-listp-implies-true-listp
  (implies
   (phase-listp list)
   (true-listp list))
  :rule-classes (:forward-chaining))

(def::signature tcons (phase-listp phase-p) phase-listp)

(def::un fix-phase-list (list)
  (declare (xargs :signature ((t) phase-listp)))
  (if (not (consp list)) nil
    (cons (phase-fix (car list))
          (fix-phase-list (cdr list)))))

(defthm fix-phase-list-phase-listp
  (implies
   (phase-listp list)
   (equal (fix-phase-list list) list)))

(defun phase-list-equiv (x y)
  (equal (fix-phase-list x)
         (fix-phase-list y)))

(defequiv phase-list-equiv)

(defcong phase-list-equiv equal (fix-phase-list x) 1)
  
(defthm phase-list-equiv-fix-phase-list
  (phase-list-equiv (fix-phase-list x) x))
 
(defthmd open-phase-list-equiv-consp
  (and
   (implies
    (or (consp x) (consp y))
    (equal (phase-list-equiv x y)
           (and (iff (consp x) (consp y))
                (phase-equiv (car x) (car y))
                (phase-list-equiv (cdr x) (cdr y)))))
   (implies
    (or (not (consp x)) (not (consp y)))
    (equal (phase-list-equiv x y)
           (and (not (consp x)) (not (consp y))))))
  :hints (("Goal" :expand (fix-phase-list y)
           :in-theory (enable equal-phase-fix))))

(in-theory (disable phase-list-equiv))

(defthm open-phase-list-equiv-cons
  (and
   (equal (phase-list-equiv y (cons a x))
          (and (consp y)
               (phase-equiv a (car y))
               (phase-list-equiv x (cdr y))))
   (equal (phase-list-equiv (cons a x) y)
          (and (consp y)
               (phase-equiv a (car y))
               (phase-list-equiv x (cdr y))))
   (implies
    (or (not (consp x)) (not (consp y)))
    (equal (phase-list-equiv x y)
           (and (not (consp x)) (not (consp y))))))
  :hints (("Goal" :in-theory (enable open-phase-list-equiv-consp equal-boolean))))

(defthm phase-list-equiv-induction t
  :rule-classes ((:induction :pattern (phase-list-equiv x y)
                             :scheme (list-equiv-induction x y))))

(defcong phase-list-equiv equal (consp x) 1
  :hints (("Goal" :in-theory (enable equal-boolean open-phase-list-equiv-consp))))

(def::signature append (phase-listp phase-listp) phase-listp)

(defcong phase-list-equiv phase-equiv (car x) 1)
(defcong phase-list-equiv phase-list-equiv (cdr x) 1)
(defcong phase-list-equiv phase-list-equiv (cons a x) 2)
(defcong phase-equiv      phase-list-equiv (cons a x) 1)
(defcong phase-list-equiv phase-list-equiv (append x y) 1)
(defcong phase-list-equiv phase-list-equiv (append x y) 2)

(defcong phase-list-equiv phase-equiv (tcar x) 1)
(defcong phase-list-equiv phase-list-equiv (tcdr x) 1)
(defcong phase-list-equiv phase-list-equiv (tcons x a) 1)
(defcong phase-equiv phase-list-equiv (tcons x a) 2)

(defcong phase-list-equiv equal (len x) 1)

(defrefinement list-equiv phase-list-equiv
  :hints (("Goal" :in-theory (enable open-list-equiv-on-consp))))

(def::und phase-bit ()
  (declare (xargs :signature (() concrete-phase-p)))
  :X)

(def::un nth-phase (x list)
  (declare (xargs :signature ((t t) phase-p)
                  :congruence ((nfix-equiv phase-list-equiv) equal)))
  (if (or (not (consp list)) (zp (nfix x)))
      (if (not (consp list)) (phase-bit) (phase-fix (car list)))
    (nth-phase (1- (nfix x)) (cdr list))))

(defthm open-nth-phase
  (and
   (implies
    (not (zp i))
    (equal (nth-phase i x)
           (if (not (consp x)) (phase-bit)
             (nth-phase (1- (nfix i)) (cdr x)))))
   (implies
    (zp i)
    (equal (nth-phase i x)
           (if (not (consp x)) (phase-bit) (phase-fix (car x)))))))

(defthm open-nth-phase-consp
  (implies
   (consp list)
   (equal (nth-phase x list)
          (if (or (not (consp list)) (zp (nfix x)))
              (if (not (consp list)) (phase-bit) (phase-fix (car list)))
            (nth-phase (1- (nfix x)) (cdr list)))))
  :rule-classes (:definition))

(defthm nth-phase-out-of-range
  (implies
   (<= (len x) (nfix i))
   (equal (nth-phase i x) (phase-bit))))

(defthm open-nth-phase-cons
  (equal (nth-phase i (cons a x))
         (if (zp i) (phase-fix a)
           (nth-phase (1- i) x))))

(defthm nth-phase-tcons
  (equal (nth-phase i (tcons x a))
         (let ((i (nfix i)))
           (if (< i (len x))
               (nth-phase i x)
             (if (equal i (len x))
                 (phase-fix a)
               (phase-bit)))))
  :hints (("GOal" :induct (list (tcons x a)
                                (nth-phase i x)))))

(in-theory (disable (:definition nth-phase)))

;; ----------------------------------------
;;
;; phase-list-equiv reduction
;;
;; ----------------------------------------

(defun nth-phase-bad-guy (x y)
  (declare (xargs :measure (max (len x) (len y))))
  (if (or (not (consp x)) (not (consp y))) 0
    (if (not (phase-equiv (car x) (car y))) 0
      (1+ (nth-phase-bad-guy (cdr x) (cdr y))))))

(defthm natp-nth-phase-bad-guy
  (natp (nth-phase-bad-guy x y)))

(defthm nth-phase-bad-guy-equiv
  (implies
   (phase-list-equiv x y)
   (equal (nth-phase-bad-guy x y)
          (min (len x) (len y)))))

(defthm nth-phase-len-x
  (equal (nth-phase (len x) x)
         (phase-bit)))

(defthm phase-equiv-nth-phase-bad-guy
  (implies
   (and
    (not (phase-list-equiv x y))
    (equal (len x) (len y)))
   (not (equal (nth-phase (nth-phase-bad-guy x y) x)
               (nth-phase (nth-phase-bad-guy x y) y))))
  :hints (("Goal" :in-theory (enable equal-phase-fix)
           :induct (nth-phase-bad-guy x y))))

(defthmd phase-list-equiv-reduction
  (iff (phase-list-equiv x y)
       (and (equal (len x) (len y))
            (equal (nth-phase (nth-phase-bad-guy x y) x)
                   (nth-phase (nth-phase-bad-guy x y) y))))
  :hints (("Goal" :do-not-induct t)))

;; ----------------------------------------

(defun concrete-phase-listp (list)
  (declare (type t list))
  (if (not (consp list)) (null list)
    (and (concrete-phase-p (car list))
         (concrete-phase-listp (cdr list)))))

(defthm concrete-phase-listp-implies-phase-listp
  (implies
   (concrete-phase-listp list)
   (phase-listp list))
  :rule-classes :forward-chaining)
 
(def::un fix-concrete-phase-list (list)
  (declare (xargs :signature ((t) concrete-phase-listp)))
  (if (not (consp list)) nil
    (cons (concrete-phase-fix (car list))
          (fix-concrete-phase-list (cdr list)))))

(defthm fix-concrete-phase-list-concrete-phase-listp
  (implies
   (concrete-phase-listp list)
   (equal (fix-concrete-phase-list list) list)))

(defun concrete-phase-list-equiv (x y)
  (equal (fix-concrete-phase-list x)
         (fix-concrete-phase-list y)))

(defequiv concrete-phase-list-equiv)

(defcong concrete-phase-list-equiv equal (fix-concrete-phase-list x) 1)
  
(defthm concrete-phase-list-equiv-fix-concrete-phase-list
  (concrete-phase-list-equiv (fix-concrete-phase-list x) x))
 
(defthmd open-concrete-phase-list-equiv
  (and
   (implies
    (or (consp x) (consp y))
    (equal (concrete-phase-list-equiv x y)
           (and (iff (consp x) (consp y))
                (concrete-phase-equiv (car x) (car y))
                (concrete-phase-list-equiv (cdr x) (cdr y)))))
   (implies
    (or (not (consp x)) (not (consp y)))
    (equal (concrete-phase-list-equiv x y)
           (and (not (consp x)) (not (consp y))))))
  :hints (("Goal" :expand (fix-concrete-phase-list y)
           :in-theory (enable equal-concrete-phase-fix))))

(in-theory (disable concrete-phase-list-equiv))

(defthm weak-open-concrete-phase-list-equiv
  (and
   (equal (concrete-phase-list-equiv y (cons a x))
          (and (consp y)
               (concrete-phase-equiv a (car y))
               (concrete-phase-list-equiv x (cdr y))))
   (equal (concrete-phase-list-equiv (cons a x) y)
          (and (consp y)
               (concrete-phase-equiv a (car y))
               (concrete-phase-list-equiv x (cdr y))))
   (implies
    (or (not (consp x)) (not (consp y)))
    (equal (concrete-phase-list-equiv x y)
           (and (not (consp x)) (not (consp y))))))
  :hints (("Goal" :in-theory (enable open-concrete-phase-list-equiv equal-boolean))))

(def::signature append (concrete-phase-listp concrete-phase-listp) concrete-phase-listp)

(defcong concrete-phase-list-equiv concrete-phase-equiv (car x) 1)
(defcong concrete-phase-list-equiv concrete-phase-list-equiv (cdr x) 1)

;; ----------------------------------------
;; well-formed phase sequence
;; ----------------------------------------

;; :X -> (:O,:N)
;; :N -> (:O,:N)
;; :O -> (:X,:P)
;; :P -> (:X,:P)
;; :W
;; :Z
;; :Y

(def::und wf-phase-final (R)
  (declare (type t R)
           (xargs :congruence ((phase-equiv) equal)))
  (memberp (phase-fix R) '(:O :X)))

(def::und wf-phase-initial (L)
  (declare (type t L)
           (xargs :congruence ((phase-equiv) equal)))
  (memberp (phase-fix L) '(:O :X)))

(def::und wf-phase-only (v)
  (declare (type t v)
           (xargs :congruence ((phase-equiv) equal)))
  (memberp (phase-fix v) '(:X)))

;; (defun left-sequence-fix (L)
;;   (let ((L (phase-fix L)))
;;     (if (memberp L '(:Y :X :N)) :X
;;       (if (member L '(:O :P)) :O
;;         :Z))))

;; (defun left-sequence-equiv (L1 L2)
;;   (equal (left-sequence-fix L1)
;;          (left-sequence-fix L2)))

;; (defequiv left-sequence-equiv)

(def::und wf-phase-sequence-step (L R)
  (declare (type t L R)
           (xargs :congruence ((phase-equiv phase-equiv) equal)
                  ;;:congruence ((left-sequence-equiv nil) equal)
                  ))
  (let ((L (phase-fix L))
        (R (phase-fix R)))
    (or
     (and (memberp L '(:X :N)) (memberp R '(:O :N)))
     (and (memberp L '(:O :P)) (memberp R '(:X :P))))))

(def::und wf-phase-sequence-body (list)
  (declare (type t list)
           (xargs :congruence ((phase-list-equiv) equal)))
  (if (not (consp list)) t
    (if (not (consp (cdr list))) t
      (let ((L (phase-fix (car list)))
            (R (phase-fix (cadr list))))
        (and (wf-phase-sequence-step L R)
             (wf-phase-sequence-body (cdr list)))))))

(def::un wf-phase-sequence-rec (L list)
  (declare (type t list)
           (xargs :congruence ((phase-equiv phase-list-equiv) equal)))
  (if (not (consp list)) t
    (let ((R (phase-fix (car list))))
      (and (wf-phase-sequence-step L R)
           (wf-phase-sequence-rec R (cdr list))))))

(defthm wf-phase-sequence-body-cons
  (equal (wf-phase-sequence-body (cons x list))
         (or (not (consp list))
             (and (wf-phase-sequence-step x (car list))
                  (wf-phase-sequence-body list))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable wf-phase-sequence-body))))

(defthm wf-phase-sequence-body-tcons
  (equal (wf-phase-sequence-body (tcons list x))
         (or (not (consp list))
             (and (wf-phase-sequence-step (tcar list) x)
                  (wf-phase-sequence-body list))))
  :hints (("Goal" :in-theory (enable wf-phase-sequence-body))))

(def::und wf-phase-sequence-prefix (list x)
  (declare (type t list x)
           (xargs :congruence ((phase-list-equiv phase-equiv) equal)))
  (and (wf-phase-sequence-body list)
       (if (consp list) (and (wf-phase-initial (car list)) (wf-phase-sequence-step (tcar list) x))
         (wf-phase-initial x))))

(defthm wf-phase-sequence-prefix-not-consp
  (implies
   (not (consp list))
   (equal (wf-phase-sequence-prefix list x)
          (wf-phase-initial x)))
  :hints (("Goal" :in-theory (enable wf-phase-sequence-body wf-phase-sequence-prefix))))

(defthm wf-phase-sequence-prefix-tcons
  (equal (wf-phase-sequence-prefix (tcons list x) a)
         (and (wf-phase-sequence-prefix list x)
              (wf-phase-sequence-step x a)))
  :hints (("Goal" :in-theory (enable wf-phase-sequence-body  wf-phase-sequence-prefix))))

(def::und wf-phase-sequence-suffix (x list)
  (declare (type t list x)
           (xargs :congruence ((phase-equiv phase-list-equiv) equal)))
  (and (wf-phase-sequence-body list)
       (if (consp list) (and (wf-phase-sequence-step x (car list)) (wf-phase-final (tcar list)))
         (wf-phase-final x))))

(defthm wf-phase-sequence-suffix-cons
  (equal (wf-phase-sequence-suffix a (cons x list))
         (and (wf-phase-sequence-suffix x list)
              (wf-phase-sequence-step a x)))
  :hints (("Goal" :in-theory (enable wf-phase-sequence-body wf-phase-sequence-suffix))))


(defthmd wf-phase-sequence-suffix-reduction
  (equal (wf-phase-sequence-suffix a list)
         (if (consp list)
             (and (wf-phase-sequence-rec a list)
                  (wf-phase-final (tcar list)))
           (wf-phase-final a)))
  :hints (("Goal" :induct (wf-phase-sequence-rec a list))
          ("Subgoal *1/1" :expand ((WF-PHASE-SEQUENCE-BODY LIST)
                                   (WF-PHASE-SEQUENCE-SUFFIX A LIST)))))

(defthm wf-phase-sequence-suffix-consp
  (implies
   (consp list)
   (equal (wf-phase-sequence-suffix a list)
          (and (wf-phase-sequence-suffix (car list) (cdr list))
               (wf-phase-sequence-step a (car list)))))
  :hints (("Goal" :in-theory (enable wf-phase-sequence-body wf-phase-sequence-suffix))))

(defthm wf-phase-sequence-suffix-not-consp
  (implies
   (not (consp list))
   (equal (wf-phase-sequence-suffix x list)
          (wf-phase-final x)))
  :hints (("Goal" :in-theory (enable wf-phase-sequence-body  wf-phase-sequence-suffix))))

(def::un wf-phase-sequence-split-1 (pre L nxt)
  (declare (type t pre L nxt)
           (xargs :congruence ((phase-list-equiv phase-equiv phase-list-equiv) equal)))
  (and (wf-phase-sequence-prefix pre L)
       (wf-phase-sequence-suffix L nxt)))

(defun wf-phase-sequence-split-1-induction (pre L nxt)
  (if (consp nxt)
      (wf-phase-sequence-split-1-induction (tcons pre L) (car nxt) (cdr nxt))
    (list pre L nxt)))

(defthm wf-phase-sequence-split-1-induction-rule t
  :rule-classes ((:induction :pattern (wf-phase-sequence-split-1 pre L nxt)
                             :scheme (wf-phase-sequence-split-1-induction pre L nxt))))

(def::und wf-phase-sequence (list)
  (declare (type t list)
           (xargs :congruence ((phase-list-equiv) equal)))
  (if (not (consp list)) nil
    (let ((L (phase-fix (car list))))
      (if (not (consp (cdr list))) (wf-phase-only L)
        (wf-phase-sequence-split-1 nil L (cdr list))))))

(def::und wf-phase-sequence-split (pre nxt)
  (declare (type t pre nxt)
           (xargs :congruence ((phase-list-equiv phase-list-equiv) equal)))
  (if (consp nxt)
      (wf-phase-sequence-split-1 pre (car nxt) (cdr nxt))
    (if (consp pre)
        (wf-phase-sequence-split-1 (tcdr pre) (tcar pre) nxt)
      nil)))

(defthm wf-phase-sequence-split-consp
  (implies
   (consp nxt)
   (equal (wf-phase-sequence-split pre nxt)
          (and (wf-phase-sequence-prefix pre (car nxt))
               (wf-phase-sequence-suffix (car nxt) (cdr nxt)))))
  :hints (("Goal" :in-theory (enable wf-phase-sequence-split))))

;; :Y is  <|>< (ie: :O :X)

;; ----------------------------------------
;; phase abstraction
;; ----------------------------------------

(def::und phaze (L R)
  (declare (xargs :signature ((t t) concrete-phase-p)
                  :congruence ((nz-equiv nz-equiv) equal)))
  (let ((L (nz-fix L))
        (R (nz-fix R)))
    (if (< L 0)
        (if (< R 0) :N :O)
      (if (< R 0) :X :P))))

(defthm wf-phase-final-phaze
  (implies
   (nz-equiv x (double-rewrite (- (nz-fix y))))
   (wf-phase-final (phaze x y)))
  :hints (("Goal" :in-theory (enable phaze wf-phase-final))))

(defthm wf-phase-initial-phaze
  (implies
   (nz-equiv y (double-rewrite (- (nz-fix x))))
   (wf-phase-initial (phaze x y)))
  :hints (("Goal" :in-theory (enable phaze wf-phase-initial))))

(defthm wf-phase-sequence-step-phaze
  (wf-phase-sequence-step (phaze p l) (phaze l n))
  :hints (("Goal" :in-theory (enable phaze wf-phase-sequence-step))))

(def::un phase-list-rec (P L x)
  (declare (ignorable P)
           (xargs :signature ((t t t) concrete-phase-listp)
                  :congruence ((nz-equiv nz-equiv nz-list-equiv) equal)))
  (let ((L (nz-fix L)))
    (if (not (consp x)) (list (phaze L (- L)))
      (let ((R (nz-fix (car x))))
        (cons (phaze L R)
              (phase-list-rec L R (cdr x)))))))

(defthm len-phase-list-rec
  (equal (len (phase-list-rec p l x))
         (1+ (len x))))

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))
  
  (defthm nth-phase-phase-list-rec
    (equal (nth-phase i (phase-list-rec P L x))
           (let ((i (nfix i)))
             (let ((L (nth-nz i      (list* L x)))
                   (R (nth-nz (1+ i) (list* L X))))
               (if (and (<= 0 i) (< i (len x)))
                   (phaze L R)
                 (if (equal i (len x))
                     (phaze L (- L))
                   (phase-bit))))))
    :hints (("Goal" :induct (list (phase-list-rec P L x)
                                  (nth-phase i x)))))

  )

(def::un phase-list (x)
  (declare (xargs :signature ((t) concrete-phase-listp)
                  :congruence ((nz-list-equiv) equal)))
  (if (not (consp x)) (list :X)
    (let ((L (nz-fix (car x))))
      (let ((p (phaze (- L) L)))
        (cons p (phase-list-rec (- L) L (cdr x)))))))

(defthm len-phase-list
  (equal (len (phase-list x))
         (1+ (len x))))

(defthm nth-phase-phase-list
  (equal (nth-phase i (phase-list x))
         (let ((i (nfix i)))           
           (if (not (consp x))
               (if (equal i 0) :X
                 (phase-bit))
             (let ((L (nth-nz  (1- i) x))
                   (R (nth-nz      i  x)))
               (if (equal i 0)
                   (phaze (- R) R)
                 (if (and (< 0 i) (< i (len x)))
                     (phaze L R)
                   (if (equal i (len x))
                       (phaze L (- L))
                     (phase-bit))))))))
  :hints (("Goal" :do-not-induct t)))

(defthm wf-phase-sequence-list-recp-phase-list-rec
  (wf-phase-sequence-suffix (phaze P L) (phase-list-rec P L x)))

(defthm wf-phase-sequence-list-phase-list
  (wf-phase-sequence (phase-list x))
  :hints (("goal" :in-theory (enable wf-phase-sequence
                                     ))))

;; ----------------------------------------
;; phase decoder
;; ----------------------------------------

(def::und decode-phase (P)
  (declare (xargs :signature ((t) nzp)
                  :congruence ((phase-equiv) equal)))
  (let ((P (phase-fix P)))
    (case P
      (:X +1)
      (:O -1)
      (:N -1)
      (:P +1)
      (t  +1))))

(defthm decode-phaze
  (nz-equiv (decode-phase (phaze x y))
            x)
  :hints (("Goal" :in-theory (enable phaze decode-phase
                                     rewrite-negated-nz-equality
                                     nzp-lt-0
                                     equal-nz-fix))))

(def::un decode-phase-list-rec (x)
  (declare (xargs :signature ((t) nz-listp)
                  :congruence ((phase-list-equiv) equal)))
  (if (not (consp x)) nil
    (cons (decode-phase (car x))
          (decode-phase-list-rec (cdr x)))))

(defthm len-decode-phase-list-rec
  (equal (len (decode-phase-list-rec x))
         (len x))
  :hints (("Goal" :induct (decode-phase-list-rec x))))

(defthm nth-nz-decode-phase-list-rec
  (equal (nth-nz i (decode-phase-list-rec x))
         (let ((i (nfix i)))
           (if (and (<= 0 i) (< i (len x)))
               (decode-phase (nth-phase i x))
             (nz-bit))))
  :hints (("Goal" :induct (list (decode-phase-list-rec x)
                                (nth-nz i x)))))

(defthm decode-phase-list-rec-phase-list-rec
  (nz-list-equiv (decode-phase-list-rec (phase-list-rec P L x))
                 (cons L x)))

(def::un decode-phase-list (list)
  (declare (type t list)
           (xargs :congruence ((phase-list-equiv) equal)))
  (if (not (consp list)) nil
    (decode-phase-list-rec (cdr list))))

(defthm nth-nz-decode-phase-list
  (equal (nth-nz i (decode-phase-list x))
         (let ((i (nfix i)))
           (if (not (consp x))
               (nz-bit)
             (if (and (<= 0 i) (< i (1- (len x))))
                 (decode-phase (nth-phase (1+ i) x))
               (nz-bit)))))
  :hints (("Goal" :do-not-induct t)))

(defthm nth-nz-decode-phase-list-phase-list
  (equal (nth-nz i (decode-phase-list (phase-list x)))
         (nth-nz i x))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable decode-phase-list
                               phase-list))
          (and stable-under-simplificationp
               '(:in-theory (enable decode-phase phaze)))))

(defthm decode-phase-list-phase-list
  (nz-list-equiv (decode-phase-list (phase-list x))
                 x))

;; ----------------------------------------
;; step phase
;; ----------------------------------------

(def::und last-two-step-phase (L v)
  (declare (xargs :signature ((t t) concrete-phase-p)
                  :congruence ((phase-equiv phase-equiv) equal)))
  (let ((L (phase-fix L))
        (v (phase-fix v)))
    (if (equal v :X) :O
      (if (equal L :N) :O
        :X))))

(def::und step-phase (L v R)
  (declare (xargs :signature ((t t t) phase-p)
                  :congruence ((phase-equiv phase-equiv phase-equiv) equal)))
  (let ((L (phase-fix L))
        (v (phase-fix v))
        (R (phase-fix R)))
    ;; :X :O :X * :X ;; 
    ;; :X :O :P * :P ;; 
    ;; :X :N :O * :X ;; A
    ;; :X :N :N * :X ;; A
    ;; :O :X :O * :O ;; O
    ;; :O :X :N * :O ;; O
    ;; :O :P :X *
    ;; :O :P :P
    ;; :N :O :X * :N
    ;; :N :O :P
    ;; :N :N :O 
    ;; :N :N :N
    ;; :P :P :P
    ;; :P :P :X * :X ;; A
    ;; :P :X :O * :O ;; O
    ;; :P :X :N * :O ;; O
    (cond
     ((equal v :X)                                            :O) ;; O
     ((and (not (equal v :O)) (or (equal L :X) (equal R :X))) :X) ;; A
     ((and (equal L :X) (equal v :O) (equal R :X))            :X)
     ((and (equal L :X) (equal v :O) (equal R :P))            :P)
     ((and (equal L :N) (equal v :O) (equal R :X))            :N)
     (t                                                        v))))
    
(def::signature step-phase (t concrete-phase-p t) concrete-phase-p
  :hints (("Goal" :in-theory (enable step-phase))))

(in-theory (disable concrete-phase-p))

(def::un step-phase-list-rec (LL L v list)
  (declare (xargs :signature ((t t t t) phase-p phase-p phase-p phase-listp)
                  :congruence ((phase-equiv phase-equiv phase-equiv phase-list-equiv) equal)))
  (if (not (consp list)) (list (phase-fix LL) (phase-fix L) (phase-fix V) nil)
    (let ((R (phase-fix (car list))))
      (let ((p (step-phase L v R)))
        (metlist ((LL L V res) (step-phase-list-rec L v R (cdr list)))
          (list LL L V (cons p res)))))))

;; (defun step-phase-list-rec-wf-induction (LL L v list)
;;   (declare (ignorable LL L v list))
;;   (if (not (consp list)) nil
;;     (let ((R (phase-fix (car list))))
;;       (step-phase-list-rec-wf-induction L v R (cdr list)))))

(defthm wf-phase-sequence-step-step-phase
  (implies
   (and
    (wf-phase-sequence-step ll l)
    (wf-phase-sequence-step l v)
    (wf-phase-sequence-step v r))
   (wf-phase-sequence-step (step-phase ll l v)
                           (step-phase l v r)))
  :hints (("goal" :in-theory (enable
                              step-phase
                              wf-phase-sequence-step))))

(encapsulate
    ()

  (local
   (defthm wf-phase-sequence-suffix-val3-step-phase-list-rec-helper
     (implies
      (and
       (wf-phase-sequence-step LL L)
       (wf-phase-sequence-step L v)
       (wf-phase-sequence-rec v list))
      (wf-phase-sequence-rec (step-phase LL L v) (val 3 (step-phase-list-rec LL L v list))))
     :hints (("Goal" :do-not-induct t
              :expand ((wf-phase-sequence-rec v list)
                       (STEP-PHASE-LIST-REC LL L V LIST))
              :induct (STEP-PHASE-LIST-REC LL L V LIST)))))

  (defthm wf-phase-sequence-suffix-val3-step-phase-list-rec
    (implies
     (and
      (phase-equiv p (step-phase LL L v))
      (wf-phase-sequence-step LL L)
      (wf-phase-sequence-step L v)
      (wf-phase-sequence-rec v list))
     (wf-phase-sequence-rec P (val 3 (step-phase-list-rec LL L v list)))))

  )
  
(def::signature step-phase-list-rec (concrete-phase-p concrete-phase-p concrete-phase-p concrete-phase-listp)
  concrete-phase-p concrete-phase-p concrete-phase-p concrete-phase-listp)

(defthm len-step-phase-list-rec
  (equal (len (val 3 (step-phase-list-rec LL L v list)))
         (len list)))

(defthm nth-step-phase-phase-list-rec
  (equal (nth-phase i (val 3 (step-phase-list-rec LL L v x)))
         (let ((i (nfix i)))
           (if (and (<= 0 i) (< i (len x)))
               (let ((L (nth-phase    i    (list* L v x)))
                     (M (nth-phase (+ i 1) (list* L v x)))
                     (R (nth-phase (+ i 2) (list* L v x))))
                 (step-phase L M R))
             (phase-bit))))
  :hints (("Goal" :induct (list (nth-phase i x)
                                (step-phase-list-rec LL L v x)))))

(def::un step-phase-list-suffix (LL L v list)
  (declare (xargs :signature ((t t t t) phase-listp)
                  :congruence ((phase-equiv phase-equiv phase-equiv phase-list-equiv) equal)))
  (metlist ((LL L V res) (step-phase-list-rec LL L v list))
    (declare (ignore LL))
    (tcons res (last-two-step-phase L V))))

(defthm wf-phase-v0-v1-v2-STEP-PHASE-LIST-REC
  (implies
   (AND (WF-PHASE-SEQUENCE-STEP LL L)
        (WF-PHASE-SEQUENCE-STEP L V)
        (WF-PHASE-SEQUENCE-SUFFIX V LIST))
   (and (wf-phase-final (VAL 2 (STEP-PHASE-LIST-REC LL L V LIST)))
        (wf-phase-sequence-step (VAL 0 (STEP-PHASE-LIST-REC LL L V LIST))
                                (VAL 1 (STEP-PHASE-LIST-REC LL L V LIST)))
        (wf-phase-sequence-step (VAL 1 (STEP-PHASE-LIST-REC LL L V LIST))
                                (VAL 2 (STEP-PHASE-LIST-REC LL L V LIST))))))

(defthm wf-phase-final-last-two-step-phsae
  (wf-phase-final (LAST-TWO-STEP-PHASE L R))
  :hints (("Goal" :in-theory (enable LAST-TWO-STEP-PHASE))))

(defthm wf-phase-sequence-rec-tcons
  (equal (wf-phase-sequence-rec p (tcons a x))
         (if (consp a)
             (and (wf-phase-sequence-rec p a)
                  (wf-phase-sequence-step (tcar a) x))
           (wf-phase-sequence-step p x))))

(defthm consp-val3-STEP-PHASE-LIST-REC
  (iff (consp (VAL 3 (STEP-PHASE-LIST-REC LL L V LIST)))
       (consp list)))

(defthm tcar-val3-STEP-PHASE-LIST-REC
  (implies
   (consp list)
   (equal (TCAR (VAL 3 (STEP-PHASE-LIST-REC LL L V LIST)))
          (step-phase (VAL 0 (STEP-PHASE-LIST-REC LL L V LIST))
                      (VAL 1 (STEP-PHASE-LIST-REC LL L V LIST))
                      (VAL 2 (STEP-PHASE-LIST-REC LL L V LIST))))))

(defthm WF-PHASE-SEQUENCE-STEP-LAST-TWO-STEP-PHASE
  (IMPLIES (AND (WF-PHASE-SEQUENCE-STEP LL L)
                (WF-PHASE-SEQUENCE-STEP L V)
                (WF-PHASE-FINAL V))
           (WF-PHASE-SEQUENCE-STEP (STEP-PHASE LL L V)
                                   (LAST-TWO-STEP-PHASE L V)))
  :hints (("GOal" :in-theory (enable step-phase
                                     last-two-step-phase
                                     WF-PHASE-SEQUENCE-STEP
                                     wf-phase-final))))

(defthm wf-phase-sequence-rec-step-phase-list-suffix
  (implies
   (and
    (wf-phase-sequence-step LL L)
    (wf-phase-sequence-step L v)
    (wf-phase-sequence-suffix v list))
   (and (wf-phase-sequence-rec (step-phase LL L v)
                               (step-phase-list-suffix LL L v list))
        (wf-phase-final (tcar (step-phase-list-suffix LL L v list)))))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (wf-phase-sequence-suffix-reduction)
                                  (WF-PHASE-SEQUENCE-SUFFIX-CONSP))
           :do-not-induct t)))

(defthm val1-STEP-PHASE-LIST-REC
  (equal (VAL 1 (STEP-PHASE-LIST-REC LL L V X))
         (nth-phase (len x) (list* L V X))))

(defthm val2-STEP-PHASE-LIST-REC
  (equal (VAL 2 (STEP-PHASE-LIST-REC LL L V X))
         (nth-phase (len x) (list* V X))))

(defthm nth-phase-step-phase-list-suffix
  (equal (nth-phase i (step-phase-list-suffix LL L v x))
         (let ((i (nfix i)))
           (let ((L (nth-phase    i    (list* L v x)))
                 (M (nth-phase (+ i 1) (list* L v x)))
                 (R (nth-phase (+ i 2) (list* L v x))))
             (if (and (<= 0 i) (< i (len x)))
                 (step-phase L M R)
               (if (equal i (len x))
                   (last-two-step-phase L M)
                 (phase-bit))))))
  :hints (("Goal" :do-not-induct t)))

(defthm decode-step-phase-phase
  (implies
   (and (concrete-phase-p q)
        (concrete-phase-p p)
        (concrete-phase-p a)
        (wf-phase-sequence-step q p)
        (wf-phase-sequence-step p a))
   (nz-equiv (decode-phase (step-phase q p a))
             (step-nz (decode-phase q)
                      (decode-phase p)
                      (decode-phase a))))
  :hints (("goal" :in-theory (enable wf-phase-sequence-step
                                     last-two-step-phase
                                     step-phase
                                     decode-phase
                                     step-nz))))

(defthm decode-phase-last-two-step-phase
  (implies
   (and (concrete-phase-p p)
        (wf-phase-final p)
        (wf-phase-sequence-step q p))
   (nz-equiv (decode-phase (last-two-step-phase q p))
             (step-nz (decode-phase q)
                      (decode-phase p)
                      (- (decode-phase p)))))
  :hints (("goal" :in-theory (enable wf-phase-final
                                     wf-phase-sequence-step
                                     last-two-step-phase
                                     decode-phase
                                     step-nz))))
      
    
(defthm step-phase-list-rec-step-nz-list-rec-commute
  (implies
   (and
    (concrete-phase-p p)
    (concrete-phase-p q)
    (concrete-phase-listp rst)
    (wf-phase-sequence-suffix P rst)
    (wf-phase-sequence-step Q P))
   (nz-list-equiv (decode-phase-list-rec (val 3 (step-phase-list-rec LL Q P rst)))
                  (val 2 (step-nz-list-rec (decode-phase Q) (decode-phase P) (decode-phase-list-rec rst)))))
  :hints (("Goal" :induct (step-phase-list-rec LL Q P rst))))
  
(defthm last-step
  (implies
   (and
    (wf-phase-sequence-step Q P)
    (wf-phase-sequence-suffix P rst))
   (nz-equiv (decode-phase (last-two-step-phase (val 1 (step-phase-list-rec LL q p rst))
                                                (val 2 (step-phase-list-rec LL q p rst))))
             (let ((q (decode-phase Q))
                   (p (decode-phase p)))
               (mv-let (q p) (step-nz-list-rec q p (decode-phase-list-rec rst))
                 (step-nz q p (- p))))))
  :hints (("Goal" :induct (step-phase-list-rec LL q p rst))
          (and stable-under-simplificationp
               '(:in-theory (enable wf-phase-final
                                    equal-phase-fix
                                    LAST-TWO-STEP-PHASE
                                    WF-PHASE-SEQUENCE-STEP
                                    step-nz
                                    decode-phase)))))


(def::und first-two-step-phase (L R)
  (declare (xargs :signature ((t t) concrete-phase-p)
                  :congruence ((phase-equiv phase-equiv) equal)))
  (let ((L (phase-fix L))
        (R (phase-fix R)))
    (if (equal L :X) :O
      (if (equal R :X) :X
        :O))))

(def::und alt-phase (L R)
  (declare (xargs :signature ((t t) concrete-phase-p)
                  :congruence ((phase-equiv phase-equiv) equal)))
  (let ((L (phase-fix L))
        (R (phase-fix R)))
    (if (equal L :O)
        (if (equal R :X) :X
          :N)
      :O)))

(defthm alt-phase-x
  (implies
   (phase-equiv L :O)
   (iff (phase-equiv (alt-phase L R) :X)
        (PHASE-EQUIV R :X)))
  :hints (("Goal" :in-theory (enable alt-phase))))

(defthmd first-two-step-phase-to-step-phase
  (implies
   (and
    (wf-phase-initial L)
    (wf-phase-sequence-step L R))
   (equal (first-two-step-phase L R)
          (step-phase (alt-phase L R) L R)))
  :otf-flg t
  :hints (("Goal" :in-theory (enable wf-phase-initial
                                     wf-phase-sequence-step
                                     first-two-step-phase
                                     step-phase))))

(def::un step-phase-list (list)
  (declare (xargs :signature ((t) phase-listp)
                  :congruence ((phase-list-equiv) equal)))
  (if (not (consp list)) nil
    (let ((L (phase-fix (car list))))
      (if (not (consp (cdr list))) (list L)
        (let ((R (phase-fix (cadr list))))
          (cons (first-two-step-phase L R)
                (step-phase-list-suffix (alt-phase L R) L R (cddr list))))))))

(def::signature step-phase-list (concrete-phase-listp) concrete-phase-listp)

(defthm wf-phase-initial-first-two-step-phase
  (wf-phase-initial (first-two-step-phase x y))
  :hints (("GOal" :in-theory (enable first-two-step-phase))))

(defthm WF-PHASE-SEQUENCE-STEP-first-last
  (implies
   (and
    (WF-PHASE-INITIAL L)
    (WF-PHASE-FINAL R)
    (WF-PHASE-SEQUENCE-STEP L R))
   (WF-PHASE-SEQUENCE-STEP (FIRST-TWO-STEP-PHASE L R)
                           (LAST-TWO-STEP-PHASE L R)))
  :hints (("GOal" :in-theory (enable WF-PHASE-SEQUENCE-STEP
                                     LAST-TWO-STEP-PHASE
                                     first-two-step-phase))))

(defthm wf-phase-sequence-step-alt-phase
  (implies
   (and
    (wf-phase-initial L)
    (wf-phase-sequence-step L R))
   (wf-phase-sequence-step (alt-phase L R) L))
  :hints (("Goal" :in-theory (enable WF-PHASE-SEQUENCE-STEP
                                     wf-phase-initial alt-phase))))

(defthm wf-phase-sequence-step-phase-list
  (implies
   (wf-phase-sequence list)
   (wf-phase-sequence (step-phase-list list)))
  :hints (("Goal" :in-theory (e/d (wf-phase-sequence
                                   FIRST-TWO-STEP-PHASE-TO-STEP-PHASE
                                   wf-phase-sequence-suffix-reduction
                                   )
                                  (VAL1-STEP-PHASE-LIST-REC
                                   VAL2-STEP-PHASE-LIST-REC
                                   WF-PHASE-SEQUENCE-SUFFIX-CONSP))
           :do-not-induct t)))

(defthm len-step-phase-list
  (equal (len (step-phase-list x))
         (len x)))

(defthm nth-phase-step-phase-list
  (equal (nth-phase i (step-phase-list list))
         (let ((i (nfix i)))
           (let ((L (nth-phase (- i 1) list))
                 (M (nth-phase (+ i 0) list))
                 (R (nth-phase (+ i 1) list)))
             (if (equal (len list) 0)
                 (phase-bit)
               (if (equal (len list) 1)
                   (if (equal i 0)
                       M
                     (phase-bit))
                 (if (and (<= 0 i) (< i (1- (len list))))
                     (if (equal i 0)
                         (first-two-step-phase M R)
                       (step-phase L M R))
                   (if (equal i (1- (len list)))
                       (last-two-step-phase L M)
                     (phase-bit))))))))
  :hints (("Goal" :do-not-induct t)))

;; Hmm .. who'da guessed?
(defthmd initial-sequence-phase-relation
  (implies
   (and (wf-phase-initial a)
        (wf-phase-sequence-step a b)
        (concrete-phase-p a)
        (concrete-phase-p b))
   (nz-equiv (decode-phase a)
             (- (decode-phase b))))
  :hints (("goal" :in-theory (enable decode-phase
                                     concrete-phase-p
                                     wf-phase-initial
                                     wf-phase-sequence-step))))

(defthm decode-phase-list-rec-tcons
  (equal (decode-phase-list-rec (tcons list a))
         (tcons (decode-phase-list-rec list)
                (decode-phase a))))

(defcong nz-list-equiv nz-list-equiv (tcons x a) 1)
(defcong nz-equiv nz-list-equiv (tcons x a) 2)

(defthm nz-list-equiv-tcons-reduction
  (iff (nz-list-equiv (tcons x a) (tcons x b))
       (nz-equiv a b)))

(defthm concrete-phase-p-nth-phase
  (implies
   (and
    (concrete-phase-listp list)
    (< (nfix i) (len list)))
   (concrete-phase-p (nth-phase i list))))

(defthm reconstruct-WF-PHASE-SEQUENCE-SUFFIX
  (implies
   (and
    (WF-PHASE-SEQUENCE-SUFFIX (car x) (cdr X))
    (wf-phase-sequence-step B (car x))
    (consp x))
   (WF-PHASE-SEQUENCE-SUFFIX B X))
  :rule-classes (:forward-chaining))

(defun nth-phase-suffix-induction (i a x)
  (if (or (zp i) (not (consp x))) (list i a x)
    (nth-phase-suffix-induction (1- i) (car x) (cdr x))))

(defthm WF-PHASE-SEQUENCE-STEP-NTH-PHASE
  (implies
   (and
    (WF-PHASE-SEQUENCE-SUFFIX A x)
    (< (nfix i) (len (cdr x))))
   (WF-PHASE-SEQUENCE-STEP (NTH-PHASE I x) (NTH-PHASE I (cdr x))))
  :hints (("Goal" :induct (nth-phase-suffix-induction i a x))))

(defthm WF-PHASE-FINAL-NTH-PHASE
  (implies
   (and
    (WF-PHASE-SEQUENCE-SUFFIX A x)
    (<= 1 (len x))
    (equal (nfix i) (1- (len x))))
   (WF-PHASE-FINAL (nth-phase i x)))
  :hints (("Goal" :induct (nth-phase-suffix-induction i a x))))

(defthm why-now
  (implies
   (and
    (WF-PHASE-INITIAL L)
    ;;(WF-PHASE-FINAL M)
    (WF-PHASE-SEQUENCE-STEP L M))
   (NZ-EQUIV (STEP-NZ (DECODE-PHASE L)
                      (DECODE-PHASE M)
                      Z)
             (STEP-NZ (- (DECODE-PHASE M))
                      (DECODE-PHASE M)
                      Z)))
  :hints (("Goal" :in-theory (enable WF-PHASE-INITIAL
                                     WF-PHASE-FINAL
                                     WF-PHASE-SEQUENCE-STEP))))

(in-theory (disable step-nz-list))

(encapsulate
    ()

  ;; I don't think we need this, but it helped debug
  ;; and it changes the subgoals below ..
  ;;(local (include-book "arithmetic-5/top" :dir :system))
  
  (defthm nth-nz-decode-phase-list-step-phase-list
    (implies
     (and
      (concrete-phase-listp res)
      (wf-phase-sequence res))
     (nz-equiv (nth-nz i (decode-phase-list (step-phase-list res)))
               (nth-nz i (step-nz-list (decode-phase-list res)))))
    :hints (("Goal" :do-not-induct t
             :in-theory (enable WF-PHASE-SEQUENCE))
            ;;
            ;; There are one or more rules that would automate these proofs
            ;;
            ;;#+joe
            (and STABLE-UNDER-SIMPLIFICATIONP
                 '(:in-theory (enable equal-phase-fix WF-PHASE-SEQUENCE-STEP)))
            ;; ("Subgoal 13" :in-theory (enable equal-phase-fix WF-PHASE-SEQUENCE-STEP))
            ;; ("Subgoal 12" :in-theory (enable equal-phase-fix WF-PHASE-SEQUENCE-STEP))
            ;; ("Subgoal 11" :in-theory (enable equal-phase-fix WF-PHASE-SEQUENCE-STEP))
            ;; ("Subgoal 9.15" :in-theory (enable equal-phase-fix WF-PHASE-SEQUENCE-STEP))
            ;; ("Subgoal 7" :in-theory (enable equal-phase-fix WF-PHASE-SEQUENCE-STEP))
            ;; ("Subgoal 3" :in-theory (enable equal-phase-fix WF-PHASE-SEQUENCE-STEP))
            ;; ("Subgoal 2" :in-theory (enable equal-phase-fix WF-PHASE-SEQUENCE-STEP))
            ))

  )

(in-theory (disable val1-STEP-PHASE-LIST-REC
                    val2-STEP-PHASE-LIST-REC))

(defthm step-phase-list-step-nz-list-commute
  (implies
   (and
    (concrete-phase-listp res)
    (wf-phase-sequence res))
   (nz-list-equiv (decode-phase-list (step-phase-list res))
                  (step-nz-list (decode-phase-list res))))
  :hints (("Goal" :in-theory (enable
                              STEP-NZ-LIST
                              val0-STEP-NZ-LIST-REC
                              val1-STEP-NZ-LIST-REC
                              wf-phase-sequence
                              initial-sequence-phase-relation
                              )
           :do-not-induct t)
          (and stable-under-simplificationp
               '(:in-theory (enable WF-PHASE-INITIAL
                                    WF-PHASE-SEQUENCE-STEP
                                    )))))

;; -------------------------------------------------------------------
;; even-p/odd-p
;; -------------------------------------------------------------------

(encapsulate
    ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defun even-p (x)
    (declare (type t x))
    (equal (mod (ifix x) 2) 0))
  
  (defun odd-p (x)
    (declare (type t x))
    (not (even-p x)))
  
  (def::und half (x)
    (declare (xargs :signature ((natp) natp)))
    (let ((x (nfix x)))
      (if (even-p x)
          (/ x 2)
        (/ (1- x) 2))))

  (defthm half-property
    (equal (* 2 (half x))
           (if (even-p (nfix x)) (nfix x) (- (nfix x) 1)))
    :hints (("GOal" :in-theory (enable half))))
    
  (defun parity-fix (x)
    (declare (type t x))
    (mod (ifix x) 2))
  
  (defun parity-equiv (x y)
    (equal (parity-fix x)
           (parity-fix y)))
  
  (defequiv parity-equiv)
  
  (defcong parity-equiv equal (parity-fix x) 1)
  
  (defcong parity-equiv equal (even-p x) 1)

  (defthm parity-equiv-parity-fix
    (parity-equiv (parity-fix x) x))

  (defthm parity-equiv-plus
    (implies
     (and
      (integerp x)
      (integerp y)
      (parity-equiv a (double-rewrite x))
      (parity-equiv b (double-rewrite y)))
     (parity-equiv (+ x y)
                   (if (even-p a)
                       (if (even-p b)
                           0
                         1)
                     (if (even-p b)
                         1
                       0))))
    :hints (("Goal" :in-theory (disable parity-equiv even-p))
            (and stable-under-simplificationp
                 '(:in-theory (disable |(mod x 2)|)))))
  
  (defthm parity-equiv-times
    (implies
     (and
      (integerp x)
      (integerp y)
      (parity-equiv a (double-rewrite x))
      (parity-equiv b (double-rewrite y)))
     (parity-equiv (* x y)
                   (if (or (even-p a) (even-p b)) 0
                     1)))
    :hints (("Goal" :in-theory (disable parity-equiv even-p))
            (and stable-under-simplificationp
                 '(:in-theory (disable |(mod x 2)|)))))
  
  (defthm posp-subtraction
    (implies
     (and (posp x) (even-p (double-rewrite x)))
     (posp (+ -1 x))))

  (defthmd non-zero-even-is-gte
    (implies
     (and
      (not (equal x 0))
      (natp x)
      (even-p x))
     (<= 2 x))
    :hints (("Goal" :in-theory (disable |(mod x 2)|))))

  (defthmd pos-odd-not-1-implication
    (implies
     (and
      (not (equal x 1))
      (posp x)
      (odd-p x))
     (<= 3 x))
    :hints (("Goal" :in-theory (disable |(mod x 2)|))))

  (defthmd pos-even-not-2-implication
    (implies
     (and
      (not (equal x 2))
      (posp x)
      (even-p x))
     (<= 4 x))
    :hints (("Goal" :in-theory (disable |(mod x 2)|))))

  (defthmd pos-odd-not-3-implication
    (implies
     (and
      (not (equal x 3))
      (<= 3 x)
      (posp x)
      (not (even-p x)))
     (<= 5 x))
    :hints (("Goal" :in-theory (disable |(mod x 2)|))
            (and stable-under-simplificationp
                 '(:cases ((<= x 1))))
            (and stable-under-simplificationp
                 '(:cases ((<= x 2))))
            (and stable-under-simplificationp
                 '(:cases ((<= x 3))))
            (and stable-under-simplificationp
                 '(:cases ((<= x 4))))
            ))
            
  
  )
  
(defthm odd-naturals-are-positive
  (implies
   (and (not (even-p x)) (natp x))
   (posp x))
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((even-p x)))))

(in-theory (disable even-p parity-fix parity-equiv))

;; ----------------------------------------
;; positive
;; ----------------------------------------

(def::un pfix (x)
  (declare (xargs :signature ((t) posp)))
  (if (posp x) x 1))

(defthm pfix-posp
  (implies
   (posp x)
   (equal (pfix x) x)))

(defun pfix-equiv (x y)
  (declare (type t x y))
  (equal (pfix x)
         (pfix y)))

(defequiv pfix-equiv)

(defcong pfix-equiv equal (pfix x) 1)

(defthm pfix-equiv-pfix
  (pfix-equiv (pfix x) x))

(defthmd equal-pfix
  (equal (equal (pfix x) y)
         (and (posp y)
              (pfix-equiv x y))))

(defrefinement nfix-equiv pfix-equiv)

(defthm posp-deduction
  (implies
   (and (integerp x) (< 0 x))
   (posp x)))

(defthm natp-deduction
  (implies
   (and (integerp x) (<= 0 x))
   (natp x)))

(defthm natp-implies
  (implies
   (natp x)
   (and (integerp x) (<= 0 x)))
  :rule-classes (:forward-chaining))   

(defthm posp-implies
  (implies
   (posp x)
   (and (integerp x) (< 0 x)))
  :rule-classes (:forward-chaining))   

(defthm posp-plus-1
  (implies
   (natp x)
   (posp (+ 1 x))))

(defthm nfix-natp
  (implies
   (natp x)
   (equal (nfix x) x)))

(in-theory (disable natp nfix posp pfix pfix-equiv))
