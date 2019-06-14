; A lightweight book about the built-in function nth.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable nth))

(defthm nth-of-nil
  (equal (nth n nil)
         nil)
  :hints (("Goal" :in-theory (enable nth))))

(defthm nth-when-<=-len-cheap
  (implies (and (<= (len x) n)
                (natp n))
           (equal (nth n x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))
  :hints (("Goal" :in-theory (enable nth))))

(defthm nth-when-not-consp-cheap
  (implies (not (consp x))
           (equal (nth n x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable nth))))

(defthm nth-when-zp-cheap
  (implies (and (syntaxp (not (equal n ''0))) ;prevents loops
                (zp n))
           (equal (nth n x)
                  (nth 0 x)))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 0)))
  :hints (("Goal" :in-theory (enable nth))))

(defthmd nth-when-<=-len
  (implies (<= (len x) (nfix n))
           (equal (nth n x)
                  nil)))

(defthmd nth-of-cons
  (equal (nth n (cons x y))
         (if (zp n)
             x
           (nth (+ -1 n) y)))
  :hints (("Goal" :in-theory (enable nth))))

(defthm nth-of-cons-safe
  (implies (syntaxp (not (and (quotep x)
                              (quotep y))))
           (equal (nth n (cons x y))
                  (if (zp n)
                      x
                    (nth (+ -1 n) y))))
  :hints (("Goal" :in-theory (enable nth))))

;prevents case splits??
(defthm nth-of-cons-constant-version
  (implies (syntaxp (quotep n))
           (equal (nth n (cons x y))
                  (if (zp n) x (nth (+ -1 n) y))))
  :hints (("Goal" :in-theory (enable nth))))

;; In case we don't want to commit to either normal form.
(defthm nth-1-cadr-hack
  (equal (equal (nth 1 x) (car (cdr x)))
         t)
  :hints (("Goal" :in-theory (enable nth))))

(defthmd car-becomes-nth-of-0
  (equal (car x)
         (nth 0 x))
  :hints (("Goal" :in-theory (enable nth))))

(defthmd nth-of-0
  (equal (nth 0 lst)
         (car lst))
  :hints (("Goal" :in-theory (enable nth))))

(theory-invariant (incompatible (:rewrite car-becomes-nth-of-0) (:rewrite nth-o-0 )))

;; There is also a copy of this in books/centaur/misc/defapply.lisp
(defthm nth-of-cdr
  (equal (nth n (cdr x))
         (nth (+ 1 (nfix n)) x))
  :hints (("Goal" :in-theory (enable nth))))

(theory-invariant (incompatible (:definition nth) (:rewrite nth-of-cdr)))

(defthm equal-of-nth-forward-to-consp
  (implies (and (equal free (nth n x))
                (syntaxp (quotep free))
                free)
           (consp x))
  :rule-classes :forward-chaining)

;compromise.  we can leave car but turn cadr etc into nth.
(defthmd cadr-becomes-nth-of-1
  (equal (cadr x)
         (nth 1 x)))

(defthm nth-of-append
  (equal (nth n (append x y))
         (if (< (nfix n) (len x))
             (nth n x)
           (nth (- n (len x)) y)))
  :hints (("Goal" :in-theory (e/d (nth) (nth-of-cdr)))))

(defthm nth-of-true-list-fix
  (equal (nth n (true-list-fix x))
         (nth n x))
  :hints (("Goal" :in-theory (e/d (nth) (nth-of-cdr)))))

;in case we don't want to commit to either form
(defthm equal-of-car-and-nth-of-0
  (equal (equal (car x) (nth 0 x))
         t))

;in case we don't want to commit to either form
(defthm equal-of-cadr-and-nth-of-1
  (equal (equal (cadr x) (nth 1 x))
         t))

;;in case we are not rewriting either to the other
(defthm equal-of-nth-2-and-caddr
  (equal (equal (nth 2 x) (caddr x))
         t))
