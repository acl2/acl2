; A function to test whether a list is a prefix of another
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Clean up this book

(local (include-book "true-list-fix"))
(local (include-book "len"))

;dup in books/std/lists/list-defuns.lisp
(defund prefixp (x y)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp y)
           (equal (car x) (car y))
           (prefixp (cdr x) (cdr y)))
    t))

(defthm prefixp-of-nil-arg1
  (prefixp nil y)
  :hints (("Goal" :in-theory (enable prefixp))))

(defthm prefixp-of-nil-arg2
  (equal (prefixp x nil)
         (atom x))
  :hints (("Goal" :in-theory (enable prefixp))))

(defthm prefixp-of-true-list-fix-arg2
  (equal (prefixp x (true-list-fix y))
         (prefixp x y))
  :hints (("Goal" :in-theory (enable prefixp))))

(defthm prefixp-of-true-list-fix-arg1
  (equal (prefixp (true-list-fix x) y)
         (prefixp x y))
  :hints (("Goal" :in-theory (enable prefixp))))

;rename?
(defthmd prefixp-when-lens-equal
  (implies (equal (len x) (len y))
           (equal (prefixp x y)
                  (equal (true-list-fix x) (true-list-fix y))))
  :hints (("Goal" :in-theory (enable prefixp true-list-fix))))

(defthm equal-of-prefixp-and-equal
  (implies (and (equal (len x) (len y))
                (true-listp x)
                (true-listp y))
           (equal (equal (prefixp x y) (equal x y))
                  t))
  :hints (("Goal" :in-theory (enable prefixp))))

(defthmd equal-of-equal-and-prefixp
  (implies (and (equal (len x) (len y))
                (true-listp x)
                (true-listp y))
           (equal (equal (equal x y) (prefixp x y))
                  t))
  :hints (("Goal" :in-theory (enable prefixp))))

;drop? only used by axe?
(defthm booleanp-of-prefixp
  (booleanp (prefixp x y)))

(defthm prefixp-when-not-shorter
  (implies (<= (len x) (len y))
           (equal (prefixp y x)
                  (equal (true-list-fix x) (true-list-fix y))))
  :hints (("Goal" :in-theory (enable prefixp true-list-fix))))

(defthm <-of-len-and-len-when-prefixp
  (implies (and (prefixp x free)
                (equal free y) ;poor man's limit
                )
           (equal (< (len x) (len y))
                  (not (equal (true-list-fix x) (true-list-fix y)))))
    :hints (("Goal" :in-theory (e/d (prefixp len true-list-fix) (len-of-cdr)))))

(defthm equal-of-len-and-len-when-prefixp
  (implies (and (prefixp x free) ;poor man's backchain limit
                (equal free y))
           (equal (equal (len x) (len y))
                  (equal (true-list-fix x) (true-list-fix y))))
  :hints (("Goal" :in-theory (e/d (prefixp true-list-fix) ()))))

(defthm equal-of-len-and-len-when-prefixp-alt
  (implies (and (prefixp x free) ;poor man's backchain limit
                (equal free y))
           (equal (equal (len y) (len x))
                  (equal (true-list-fix x) (true-list-fix y))))
  :hints (("Goal" :in-theory (e/d (prefixp true-list-fix) ()))))

(defthm prefixp-same
  (prefixp x x)
  :hints (("Goal" :in-theory (enable prefixp))))

;gross proof?
(defthm prefixp-of-cdr-rule
  (implies (and (prefixp y x)
                (prefixp z (cdr y)))
           (equal (prefixp z (cdr x))
                  t))
  :hints (("Goal" :in-theory (enable prefixp true-list-fix))))

(defthm prefixp-when-len-0
  (implies (and (equal free (len x))
                (EQUAl 0 free) ;poor man's backchain limit
;                (true-listp y)
                )
           (equal (prefixp y x)
                  (equal 0 (len y))))
  :hints (("Goal" :in-theory (enable prefixp true-list-fix))))

(local
 (defun double-cdr-induct (x y)
  (if (endp x)
      (list x y)
    (double-cdr-induct (cdr x) (cdr y)))))

;; The phrasing here is to avoid loops.
(defthm len-when-equal-of-true-list-fix-and-true-list-fix
  (implies (and (equal (true-list-fix x)
                       (true-list-fix y)))
           (equal (equal (len x) (len y))
                  t))
  :hints (("Goal" :induct (double-cdr-induct x y)
           :in-theory (enable true-list-fix (:i len)))))

(defthm prefixp-when-longer
  (implies (< (len x) (len y))
           (equal (prefixp y x)
                  nil))
  :hints (("Goal" :in-theory (e/d (prefixp true-list-fix)
                                  (len-when-equal-of-true-list-fix-and-true-list-fix))
           :use (:instance len-when-equal-of-true-list-fix-and-true-list-fix))))

(defthmd not-prefixp-when-not-equal-of-nth-and-nth
  (implies (and (not (equal (nth n x) (nth n y)))
                (< n (len x))
                ;; (< n (len y))
                (natp n))
           (not (prefixp x y)))
  :hints (("Goal" :in-theory (enable prefixp nth))))

(defthm prefixp-of-take-arg1-same
  (implies (and (<= n (len x))
                (natp n))
           (prefixp (take n x) x))
  :hints (("Goal" :in-theory (enable prefixp take))))

;; todo: use a congruence on append instead
(defthm prefix-of-append-when-not-consp-cheap
  (implies (not (consp y))
           (equal (prefixp (append x y) z)
                  (prefixp x z)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable prefixp append))))

(defthm prefixp-of-append-same
  (prefixp x (append x y))
  :hints (("Goal" :in-theory (enable prefixp))))

(defthm prefixp-of-append-and-append-same
  (equal (prefixp (append x y1)
                  (append x y2))
         (prefixp y1 y2))
  :hints (("Goal" :in-theory (enable prefixp append))))

;move
(defthm equal-of-append-and-true-list-fix-same
  (equal (equal (append x y) (true-list-fix x))
         (equal y nil))
  :hints (("Goal" :in-theory (enable append true-list-fix))))

(defthm prefix-when-not-consp-arg1-cheap
  (implies (not (consp x))
           (prefixp x y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable prefixp))))

(encapsulate ()
  (local (include-book "nthcdr"))
  (local (include-book "take"))
  (local (include-book "true-list-fix"))
  (local (include-book "append"))
  (local (include-book "len"))
  (local (include-book "nth"))
  (local (include-book "cons"))

  ;; (defthm append-when-not-consp-arg2-cheap
  ;;   (implies (not (consp y))
  ;;            (equal (append x y)
  ;;                   (true-list-fix x)))
  ;;   :rule-classes ((:rewrite :backchain-limit-lst (0)))
  ;;   :hints (("Goal" :in-theory (enable append true-list-fix))))

  (local
   (defthmd prefixp-of-append-arg1-fw-1
    (implies (prefixp (append x y) z)
             (<= (+ (len x) (len y)) (len z)))
    :hints (("goal" :do-not '(generalize eliminate-destructors)
             :in-theory (enable prefixp append)))))

  (local
   (defthmd prefixp-of-append-arg1-fw-2
    (implies (prefixp (append x y) z)
             (equal (true-list-fix x)
                    (take (len x) z)))
    :hints (("goal" :do-not '(generalize eliminate-destructors)
             :induct (prefixp x z)
             :in-theory (enable prefixp append TRUE-LIST-FIX)))))

  (local
   (defthmd prefixp-of-append-arg1-fw-3
    (implies (prefixp (append x y) z)
             (prefixp (true-list-fix y)
                      (nthcdr (len x) z)))
    :hints (("goal" :do-not '(generalize eliminate-destructors)
             :induct (prefixp x z)
             :in-theory (enable prefixp append)))))

  (local
   (defthmd prefixp-of-append-arg1-back
     (implies (and (<= (+ (len x) (len y)) (len z))
                   (equal (true-list-fix x)
                          (take (len x) z))
                   (prefixp (true-list-fix y)
                            (nthcdr (len x) z)))
              (prefixp (append x y) z))
     :hints (("Goal" :use (:instance APPEND-OF-TAKE-AND-NTHCDR-2
                                     (n (len x))
                                     (l z))
              :in-theory (disable APPEND-OF-TAKE-AND-NTHCDR-2)))))

  (defthm prefixp-of-append-arg1
    (equal (prefixp (append x y) z)
           (and (<= (+ (len x) (len y)) (len z))
                (equal (true-list-fix x)
                       (take (len x) z))
                (prefixp y (nthcdr (len x) z))))
    :hints (("Goal" :use (prefixp-of-append-arg1-back
                          prefixp-of-append-arg1-fw-3
                          prefixp-of-append-arg1-fw-2
                          prefixp-of-append-arg1-fw-1))))
  )
