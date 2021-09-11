; A lightweight book about the built-in function pairlis$
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))

(in-theory (disable pairlis$))

(defthm alistp-of-pairlis$
  (alistp (pairlis$ x y))
  :hints (("Goal" :in-theory (enable pairlis$))))

(defthm symbol-alistp-of-pairlis$
  (equal (symbol-alistp (pairlis$ x y))
         (symbol-listp (true-list-fix x)))
  :hints (("Goal" :in-theory (enable pairlis$))))

;see also a version in books/std/alists/strip-cdrs.lisp
(defthm strip-cdrs-of-pairlis$2
  (implies (and (true-listp y)
                (equal (len x) (len y)))
           (equal (strip-cdrs (pairlis$ x y))
                  y))
  :hints (("Goal" :in-theory (enable pairlis$))))

;; this introduces take, which may not always be desirable
(defthm strip-cdrs-of-pairlis$-gen
  (equal (strip-cdrs (pairlis$ x y))
         (take (len x) y))
  :hints (("Goal" :in-theory (enable pairlis$ take))))

(defthmd pairlis$-opener
  (implies (not (atom keys))
           (equal (pairlis$ keys vals)
                  (acons (car keys)
                         (car vals)
                         (pairlis$ (cdr keys) (cdr vals)))))
  :hints (("Goal" :in-theory (enable pairlis$))))

(defthmd pairlis$-base
  (implies (atom keys)
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

(defthm assoc-equal-of-pairlis$-iff
  (iff (assoc-equal key (pairlis$ keys vals))
       (member-equal key keys))
  :hints (("Goal" :in-theory (enable pairlis$))))

(defthm pairlis$-of-true-list-fix-arg1
  (equal (pairlis$ (true-list-fix x) y)
         (pairlis$ x y))
  :hints (("Goal" :in-theory (enable pairlis$))))

(defthm pairlis$-of-true-list-fix-arg2
  (equal (pairlis$ x (true-list-fix y))
         (pairlis$ x y))
  :hints (("Goal" :in-theory (enable pairlis$))))
