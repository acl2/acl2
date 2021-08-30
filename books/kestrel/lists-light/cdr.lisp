; A lightweight book about the built-in function cdr.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defthm equal-of-cdr-same
  (equal (equal (cdr x) x)
         (equal x nil)))

(defthm cdr-iff
  (iff (cdr x)
       (if (< 1 (len x))
           t
         (if (equal 1 (len x))
             (not (true-listp x))
           nil)))
  :hints (("Goal" :expand (true-listp (cdr x))
           :in-theory (enable len true-listp))))

;simpler but might loop?
(defthmd cdr-iff-2
  (iff (cdr x)
       (if (consp x)
           (if (consp (cdr x))
               t
             (not (true-listp x)))
         nil))
  :hints (("Goal" :expand (true-listp (cdr x))
           :in-theory (enable len true-listp))))

(defthmd true-listp-of-cdr
  (implies (true-listp x)
           (true-listp (cdr x))))

(theory-invariant (incompatible (:rewrite true-listp-of-cdr) (:definition true-listp)))

(defthmd true-listp-of-cdr-strong
  (equal (true-listp (cdr x))
         (if (consp x)
             (true-listp x)
           t)))

(theory-invariant (incompatible (:rewrite true-listp-of-cdr-strong) (:definition true-listp)))

(defthmd equal-when-equal-of-cdrs
  (implies (and (equal (cdr x) (cdr y))
                (consp x)
                (consp y))
           (equal (equal x y)
                  (equal (car x) (car y)))))
