; A lightweight book about the built-in function pairlis$
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))

(in-theory (disable pairlis$))

(defthm alistp-of-pairlis$
  (alistp (pairlis$ x y))
  :hints (("Goal" :in-theory (enable pairlis$))))

(defthm symbol-alistp-of-pairlis$
  (equal (symbol-alistp (pairlis$ x y))
         (symbol-listp (true-list-fix x)))
  :hints (("Goal" :in-theory (enable pairlis$))))

;; Also in strip-cars.lisp.
(defthm strip-cars-of-pairlis$
  (equal (strip-cars (pairlis$ x y))
         (true-list-fix x))
  :hints (("Goal" :in-theory (enable pairlis$))))

;see also a version in books/std/alists/strip-cdrs.lisp
(defthm strip-cdrs-of-pairlis$2
  (implies (and (true-listp y)
                (equal (len x) (len y)))
           (equal (strip-cdrs (pairlis$ x y))
                  y))
  :hints (("Goal" :in-theory (enable pairlis$))))

;; Also in strip-cdrs.lisp.
;; this introduces take, which may not always be desirable
(defthm strip-cdrs-of-pairlis$
  (equal (strip-cdrs (pairlis$ x y))
         (take (len x) y))
  :hints (("Goal" :in-theory (enable pairlis$ take))))

(defthmd pairlis$-opener
  (implies (consp keys)
           (equal (pairlis$ keys vals)
                  (acons (car keys)
                         (car vals)
                         (pairlis$ (cdr keys) (cdr vals)))))
  :hints (("Goal" :in-theory (enable pairlis$))))

(defthmd pairlis$-when-not-consp
  (implies (not (consp keys))
           (equal (pairlis$ keys vals)
                  nil))
  :hints (("Goal" :in-theory (enable pairlis$))))

(local
 (defun double-cdr-induct (x y)
   (if (endp x)
       (list x y)
     (double-cdr-induct (cdr x) (cdr y)))))

(defthm pairlis$-of-cons-arg1
  (equal (pairlis$ (cons x xs) y)
         (cons (cons x (car y))
               (pairlis$ xs (cdr y))))
  :hints (("Goal" :in-theory (enable pairlis$)
           :induct (double-cdr-induct x y)
           )))

(defthm pairlis$-of-append-arg1
  (equal (pairlis$ (append x y) z)
         (append (pairlis$ x (take (len x) z))
                 (pairlis$ y (nthcdr (len x) z))))
  :hints (("Goal" :in-theory (enable pairlis$)
           :induct (double-cdr-induct x z)
           )))

;; less aggressive
(defthm pairlis$-of-append-and-append
  (implies (equal (len x1) (len x2))
           (equal (pairlis$ (append x1 y1) (append x2 y2))
                  (append (pairlis$ x1 x2)
                          (pairlis$ y1 y2)))))

(defthm assoc-equal-of-pairlis$-iff
  (iff (assoc-equal key (pairlis$ keys vals))
       (member-equal key keys))
  :hints (("Goal" :in-theory (enable pairlis$))))

;; limit?
(defthm assoc-equal-of-pairlis$-when-not-member-equal
  (implies (not (member-equal key keys))
           (equal (assoc-equal key (pairlis$ keys vals))
                  nil)))

(defthm pairlis$-of-true-list-fix-arg1
  (equal (pairlis$ (true-list-fix x) y)
         (pairlis$ x y))
  :hints (("Goal" :in-theory (enable pairlis$))))

;; The identical rule PAIRLIS$-TRUE-LIST-FIX is built in to ACL2
;; (defthm pairlis$-of-true-list-fix-arg2
;;   (equal (pairlis$ x (true-list-fix y))
;;          (pairlis$ x y))
;;   :hints (("Goal" :in-theory (enable pairlis$))))

(defthm len-of-pairlis$
  (equal (len (pairlis$ x y))
         (len x))
  :hints (("Goal" :in-theory (enable pairlis$))))
