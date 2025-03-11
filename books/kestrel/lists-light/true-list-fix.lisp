; A lightweight book about the built-in function true-list-fix.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable true-list-fix))

(defthm true-list-fix-when-true-listp
  (implies (true-listp x)
           (equal (true-list-fix x)
                  x))
  :hints (("Goal" :in-theory (enable true-list-fix))))

(defthm true-list-fix-when-not-consp-cheap
  (implies (not (consp x))
           (equal (true-list-fix x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable true-list-fix))))

(defthm len-of-true-list-fix
  (equal (len (true-list-fix x))
         (len x))
  :hints (("Goal" :in-theory (enable true-list-fix))))

(defthm consp-of-true-list-fix
  (equal (consp (true-list-fix x))
         (consp x))
  :hints (("Goal" :in-theory (enable true-list-fix))))

(defthm true-list-fix-iff
  (iff (true-list-fix x)
       (consp x))
  :hints (("Goal" :in-theory (enable true-list-fix))))

(defthm car-of-true-list-fix
  (equal (car (true-list-fix x))
         (car x))
  :hints (("Goal" :in-theory (enable true-list-fix))))

(defthm cdr-of-true-list-fix
  (equal (cdr (true-list-fix x))
         (true-list-fix (cdr x)))
  :hints (("Goal" :in-theory (enable true-list-fix))))

(defthm true-list-fix-of-cons
  (equal (true-list-fix (cons x y))
         (cons x (true-list-fix y)))
  :hints (("Goal" :in-theory (enable true-list-fix))))

(local
 (defun double-cdr-induct (x y)
   (if (endp x)
       (list x y)
     (double-cdr-induct (cdr x) (cdr y)))))

(defthmd equal-of-true-list-fix-and-true-list-fix-forward
  (implies (equal (true-list-fix x) (true-list-fix y))
           (equal (len x) (len y)))
  :rule-classes :forward-chaining
  :hints (("Goal" :induct (double-cdr-induct x y)
           :in-theory (enable true-list-fix len))))
