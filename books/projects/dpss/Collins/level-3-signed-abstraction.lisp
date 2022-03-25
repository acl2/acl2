;;  
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")

(include-book "coi/util/defun" :dir :system)
(include-book "tools/pattern-match" :dir :system)
(include-book "coi/util/in-conclusion" :dir :system)
(include-book "std/lists/equiv" :dir :system)
(include-book "coi/util/deffix" :dir :system)
(include-book "std/util/defines" :dir :system)

(defun memberp (a x)
  (declare (type (satisfies true-listp) x))
  (if (member-equal a x) t nil))

(defthmd equal-boolean
  (implies
   (booleanp x)
   (equal (equal x y)
          (and (booleanp y)
               (iff x y)))))

(defthm equal-cons-reduction
  (equal (equal (cons a x) y)
         (and (consp y)
              (equal a (car y))
              (equal x (cdr y)))))

(defthm equal-plus-len
  (implies
   (and
    (syntaxp (and (quotep c) (quotep d)))
    (integerp c)
    (integerp d)
    (equal e (- d c)))
   (equal (equal (+ c (len x)) d)
          (equal (len x) e))))

(defthm equal-len-into-consp
  (implies
   (and (syntaxp (quotep c))
        (integerp c))
   (equal (equal (len x) c)
          (if (equal c 0) (not (consp x))
            (and (consp x)
                 (equal (len (cdr x)) (1- c)))))))

(defun list-equiv-induction (x y)
  (if (and (consp x) (consp y))
      (list-equiv-induction (cdr x) (cdr y))
    (list x y)))

(def::un tcons (list x)
  (declare (xargs :signature ((t t) true-listp)))
  (if (not (consp list)) (list x)
    (cons (car list) (tcons (cdr list) x))))

(in-theory (disable (:type-prescription tcons)))

(defthmd open-list-equiv-on-consp
  (implies
   (consp x)
   (iff (list-equiv x y)
        (and (consp y)
             (equal (car x) (car y))
             (list-equiv (cdr x) (cdr y)))))
  :hints (("Goal" :in-theory (enable true-list-fix list-equiv))))

(defthm list-equiv-induction-rule t
  :rule-classes ((:induction :pattern (list-equiv x y)
                             :scheme (list-equiv-induction x y))))

(defcong list-equiv equal (tcons list x) 1
  :hints (("Goal" :in-theory (enable open-list-equiv-on-consp))))

(defthm len-tcons
  (equal (len (tcons list x))
         (+ 1 (len list))))

(defun tcar (list)
  (declare (type t list))
  (if (not (consp list)) nil
    (if (not (consp (cdr list))) (car list)
      (tcar (cdr list)))))

(def::un tcdr (list)
  (declare (xargs :signature ((t) true-listp)))
  (if (not (consp list)) nil
    (if (not (consp (cdr list))) nil
      (cons (car list) (tcdr (cdr list))))))

(defthm len-tcdr
  (equal (len (tcdr list))
         (nfix (1- (len list)))))

(defthm tcar-tcons
  (equal (tcar (tcons list x))
         x))

(defthm tcdr-tcons
  (equal (tcdr (tcons list x))
         (list-fix list)))

(defthm tcons-tcdr-tcar
  (implies
   (consp x)
   (equal (tcons (tcdr x) (tcar x))
          (list-fix x))))

(def::un tnth (i list)
  (declare (type t i list))
  (if (not (consp list)) nil
    (let ((i (nfix i)))
      (if (zp i) (tcar list)
        (tnth (1- i) (tcdr list))))))

(encapsulate
    ()

  (local
   (defthm nth-tcdr
     (equal (nth i (tcdr list))
            (if (< (nfix i) (len (tcdr list)))
                (nth i list)
              nil))))
     
   (local
    (defthm nth-to-tcar
      (equal (nth (+ -1 (len list)) list)
             (tcar list))))
   
   (defthmd tnth-as-nth
     (equal (tnth i list)
            (if (< (nfix i) (len list))
                (nth (+ (len list) -1 (- (nfix i))) list)
              nil)))

   )

;; ==================================================================
;; nz-list abstraction
;; ==================================================================

;; ----------------------------------------
;; nfix-equiv
;; ----------------------------------------

(defun nfix-equiv (x y)
  (declare (type t x y))
  (equal (nfix x)
         (nfix y)))

(defequiv nfix-equiv)

(defthm nfix-equiv-nfix
  (nfix-equiv (nfix x) x))

(defthm equal-nfix-0
  (equal (equal (nfix i) 0)
         (zp i)))

(defthm zp-implies-not-positive
  (implies
   (zp x)
   (not (< 0 (nfix x))))
  :rule-classes (:rewrite :linear))

(defthm zp-implies-equal-zero
  (implies
   (zp x)
   (equal (nfix x) 0))
  :rule-classes (:forward-chaining))

(defthm not-zp-implication
  (implies
   (not (zp x))
   (and (natp x) (< 0 (nfix x)) (< 0 x)))
  :rule-classes (:forward-chaining))

;; ----------------------------------------
;; non-zero (+/-)1
;; ----------------------------------------

(defun nzp (x)
  (declare (type t x))
  (or (equal x 1)
      (equal x -1)))

(defthm nzp-implies
  (implies
   (nzp x)
   (and (integerp x)
        (or (equal x 1)
            (equal x -1))))
  :rule-classes (:forward-chaining))

(defthmd nzp-lt-0
  (implies
   (nzp x)
   (iff (< x 0)
        (equal x -1))))

(def::un nz-fix (x)
  (declare (xargs :signature ((t) nzp)))
  (if (not (nzp x)) 1
    x))

(defthm nzp-negation
  (implies
   (nzp x)
   (equal (nz-fix (- x))
          (- x))))

(defthm nzp-nz-fix-identity
  (implies
   (nzp x)
   (equal (nz-fix x) x)))

(defun nz-equiv (x y)
  (declare (type t x y))
  (equal (nz-fix x)
         (nz-fix y)))

(defequiv nz-equiv)

(defcong nz-equiv equal (nz-fix x) 1)

(defthm nz-equiv-nz-fix
  (nz-equiv (nz-fix x) x))

(defthmd equal-nz-fix
  (equal (equal (nz-fix x) y)
         (and (nzp y)
              (nz-equiv x y))))

(defthm nzp--
  (implies
   (nzp x)
   (nzp (- x))))

(defthm nz-equiv-negation
  (implies
   (and
    (syntaxp (quotep c))
    (nzp x)
    (nzp c))
   (equal (nz-equiv (- x) c)
          (nz-equiv x (- c)))))

(defthm integer--
  (implies
   (integerp x)
   (equal (- (- x)) x)))

(defthm nzp-*
  (implies
   (and (nzp x) (nzp y))
   (nzp (* x y))))

(defthmd rewrite-negated-nz-equality
  (implies
   (and
    (syntaxp (quotep a))
    (in-conclusion-check (nz-equiv x a) :top :negated)
    (nzp a))
   (equal (nz-equiv x a)
          (not (nz-equiv x (- a))))))

(in-theory (disable nzp nz-fix nz-equiv))

;; ----------------------------------------

(defun nz-listp (list)
  (if (not (consp list)) (null list)
    (and (nzp (car list))
         (nz-listp (cdr list)))))

(def::signature tcons (nz-listp nzp) nz-listp)

(defthm nz-listp-cons
  (equal (nz-listp (cons a x))
         (and (nzp a)
              (nz-listp x))))

(def::un fix-nz-list (list)
  (declare (xargs :signature ((t) nz-listp)))
  (if (not (consp list)) nil
    (cons (nz-fix (car list))
          (fix-nz-list (cdr list)))))

(defthm fix-nz-list-nz-listp
  (implies
   (nz-listp list)
   (equal (fix-nz-list list) list)))

(defun nz-list-equiv (x y)
  (equal (fix-nz-list x)
         (fix-nz-list y)))

(defequiv nz-list-equiv)

(defcong nz-list-equiv equal (fix-nz-list x) 1)
  
(defthm nz-list-equiv-fix-nz-list
  (nz-list-equiv (fix-nz-list x) x))

(defthmd open-nz-list-equiv
  (and
   (implies
    (or (consp x) (consp y))
    (equal (nz-list-equiv x y)
           (and (iff (consp x) (consp y))
                (nz-equiv (car x) (car y))
                (nz-list-equiv (cdr x) (cdr y)))))
   (implies
    (or (not (consp x)) (not (consp y)))
    (equal (nz-list-equiv x y)
           (and (not (consp x)) (not (consp y))))))
  :hints (("Goal" :expand (fix-nz-list y)
           :in-theory (enable equal-nz-fix))))

(in-theory (disable nz-list-equiv))

(defthm weak-open-nz-list-equiv
  (and
   (equal (nz-list-equiv (cons a z) y)
          (and (consp y)
               (nz-equiv a (car y))
               (nz-list-equiv z (cdr y))))
   (equal (nz-list-equiv y (cons a z))
          (and (consp y)
               (nz-equiv a (car y))
               (nz-list-equiv z (cdr y))))
   (implies
    (or (not (consp x)) (not (consp y)))
    (equal (nz-list-equiv x y)
           (and (not (consp x)) (not (consp y))))))
  :hints (("Goal" :in-theory (enable open-nz-list-equiv
                                     equal-boolean))))

(defthm nz-list-equiv-induction t
  :rule-classes ((:induction :pattern (nz-list-equiv x y)
                             :scheme (list-equiv-induction x y))))

(defcong nz-list-equiv equal (consp x) 1
  :hints (("Goal" :in-theory (enable equal-boolean open-nz-list-equiv))))

(defcong nz-list-equiv nz-equiv (car x) 1)
(defcong nz-list-equiv nz-list-equiv (cdr x) 1)
(defcong nz-list-equiv nz-list-equiv (cons a x) 2)
(defcong nz-equiv      nz-list-equiv (cons a x) 1)
(defcong nz-list-equiv nz-list-equiv (append x y) 1)
(defcong nz-list-equiv nz-list-equiv (append x y) 2)

(defcong nz-list-equiv equal (len x) 1)

(defrefinement list-equiv nz-list-equiv
  :hints (("Goal" :in-theory (enable open-list-equiv-on-consp))))

(def::und nz-bit ()
  (declare (xargs :signature (() nzp)))
  1)

(def::un nth-nz (x list)
  (declare (xargs :signature ((t t) nzp)
                  :congruence ((nfix-equiv nz-list-equiv) equal)))
  (if (not (consp list)) (nz-bit)
    (if (zp (nfix x)) (nz-fix (car list))
      (nth-nz (1- (nfix x)) (cdr list)))))

(defthm open-nth-nz
  (implies
   (not (zp i))
   (equal (nth-nz i x)
          (if (not (consp x)) (nz-bit)
            (nth-nz (1- (nfix i)) (cdr x))))))

(defthm nth-nz-out-of-range
  (implies
   (<= (len x) (nfix i))
   (equal (nth-nz i x) (nz-bit))))

(defthm open-nth-nz-cons
  (equal (nth-nz i (cons a x))
         (if (zp i) (nz-fix a)
           (nth-nz (1- i) x))))

(defthm nth-nz-tcons
  (equal (nth-nz i (tcons x a))
         (let ((i (nfix i)))
           (if (< i (len x))
               (nth-nz i x)
             (if (equal i (len x))
                 (nz-fix a)
               (nz-bit)))))
  :hints (("GOal" :induct (list (tcons x a)
                                (nth-nz i x)))))

;; ----------------------------------------
;;
;; nz-list-equiv reduction
;;
;; ----------------------------------------

(defun nth-nz-bad-guy (x y)
  (declare (xargs :measure (max (len x) (len y))))
  (if (or (not (consp x)) (not (consp y))) 0
    (if (not (nz-equiv (car x) (car y))) 0
      (1+ (nth-nz-bad-guy (cdr x) (cdr y))))))

(defthm natp-nth-nz-bad-guy
  (natp (nth-nz-bad-guy x y)))

(defthm nth-nz-bad-guy-equiv
  (implies
   (nz-list-equiv x y)
   (equal (nth-nz-bad-guy x y)
          (min (len x) (len y)))))

(defthm nth-nz-len-x
  (equal (nth-nz (len x) x)
         (nz-bit)))

(defthm nz-equiv-nth-nz-bad-guy
  (implies
   (and
    (not (nz-list-equiv x y))
    (equal (len x) (len y)))
   (not (equal (nth-nz (nth-nz-bad-guy x y) x)
               (nth-nz (nth-nz-bad-guy x y) y))))
  :hints (("Goal" :in-theory (enable equal-nz-fix)
           :induct (nth-nz-bad-guy x y))))

(defthmd nz-list-equiv-reduction
  (iff (nz-list-equiv x y)
       (and (equal (len x) (len y))
            (equal (nth-nz (nth-nz-bad-guy x y) x)
                   (nth-nz (nth-nz-bad-guy x y) y))))
  :hints (("Goal" :do-not-induct t)))

;; ----------------------------------------
;; step nz-list
;; ----------------------------------------

(def::und step-nz (L v R)
  (declare (xargs :signature ((t t t) nzp)))
  (let ((L (nz-fix L))
        (v (nz-fix v))
        (R (nz-fix R)))
    (if (< v 0)
        (if (not (< L 0)) (- v) v)
      (if (< R 0) (- v) v))))

(def::un step-nz-list-rec (L v x)
  (declare (xargs :signature ((t t t) nzp nzp nz-listp)
                  ;;:congruence ((nz-equiv nz-equiv nz-list-equiv) equal equal equal)
                  ))
  (let ((L   (nz-fix L))
        (v   (nz-fix v)))
    (if (not (consp x)) (mv L v nil)
      (let ((R (nz-fix (car x))))
        (let ((z (step-nz L v R)))
          (mv-let (L v res) (step-nz-list-rec v R (cdr x))
            (mv L v (cons z res))))))))

(defthm nz-equiv-1-equal-step-nz-list-rec
  (implies
   (nz-equiv L1 L2)
   (equal (step-nz-list-rec L1 v x)
          (step-nz-list-rec L2 v x)))
  :rule-classes :congruence)

(defthm nz-equiv-2-equal-step-nz-list-rec
  (implies
   (nz-equiv v1 v2)
   (equal (step-nz-list-rec L v1 x)
          (step-nz-list-rec L v2 x)))
  :rule-classes :congruence)

(defthm nz-equiv-3-equal-step-nz-list-rec
  (implies
   (nz-list-equiv x1 x2)
   (equal (step-nz-list-rec L v x1)
          (step-nz-list-rec L v x2)))
  :rule-classes :congruence)

(defthm len-step-nz-list-rec
  (equal (len (val 2 (step-nz-list-rec L v x)))
         (len x)))

(defthm nth-nz-step-nz-list-rec
  (equal (nth-nz i (val 2 (step-nz-list-rec L v x)))
         (let ((i (nfix i)))
           (if (and (<= 0 i) (< i (len x)))
               (let ((L (nth-nz    i    (list* L v x)))
                     (M (nth-nz (+ i 1) (list* L v x)))
                     (R (nth-nz (+ i 2) (list* L v x))))
                 (step-nz L M R))
             (nz-bit))))
  :hints (("Goal" :induct (list (nth-nz i x)
                                (step-nz-list-rec L v x)))))

(def::un step-nz-list-suffix (L v list)
  (declare (xargs :signature ((t t t) nz-listp)
                  :congruence ((nz-equiv nz-equiv nz-list-equiv) equal)))
  (let ((L (nz-fix L))
        (v (nz-fix v)))
    (mv-let (L v res) (step-nz-list-rec L v list)
      (tcons res (step-nz L v (- v))))))

(defthm len-step-nz-list-suffix
  (equal (len (step-nz-list-suffix L v list))
         (1+ (len list))))

(defthm val0-STEP-NZ-LIST-REC
  (equal (VAL 0 (STEP-NZ-LIST-REC L V X))
         (nth-nz (len x) (list* L V X))))

(defthm val1-STEP-NZ-LIST-REC
  (equal (VAL 1 (STEP-NZ-LIST-REC L V X))
         (nth-nz (len x) (list* V X))))

(defthm nth-nz-step-nz-list-suffix
  (equal (nth-nz i (step-nz-list-suffix L v x))
         (let ((i (nfix i)))
           (let ((L (nth-nz    i    (list* L v x)))
                 (M (nth-nz (+ i 1) (list* L v x)))
                 (R (nth-nz (+ i 2) (list* L v x))))
             (if (and (<= 0 i) (< i (len x)))
                 (step-nz L M R)
               (if (equal i (len x))
                   (step-nz L M (- M))
                 (nz-bit))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable open-nth-nz
                               nth-nz))
          (and stable-under-simplificationp
               '(:in-theory (current-theory :here)))))

(def::un step-nz-list (list)
  (declare (xargs :signature ((t) nz-listp)
                  :congruence ((nz-list-equiv) equal)))
  (if (not (consp list)) nil
    (let ((v (nz-fix (car list))))
      (if (not (consp (cdr list))) (list (step-nz (- v) v (- v)))
        (step-nz-list-suffix (- v) v (cdr list))))))

(defthm len-step-nz-list
  (equal (len (step-nz-list x))
         (len x)))

(defthm nth-nz-step-nz-list
  (equal (nth-nz i (step-nz-list list))
         (let ((i (nfix i)))
           (let ((L (nth-nz (- i 1) list))
                 (M (nth-nz (+ i 0) list))
                 (R (nth-nz (+ i 1) list)))
             (if (equal (len list) 0)
                 (nz-bit)
               (if (equal (len list) 1)
                   (if (equal i 0)
                       (step-nz (- M) M (- M))
                     (nz-bit))
                 (if (and (<= 0 i) (< i (1- (len list))))
                     (if (equal i 0)
                         (step-nz (- M) M R)
                       (step-nz L M R))
                   (if (equal i (1- (len list)))
                       (step-nz L M (- M))
                     (nz-bit))))))))
  :hints (("Goal" :do-not-induct t)))

(in-theory (disable val0-STEP-NZ-LIST-REC
                    val1-STEP-NZ-LIST-REC))
