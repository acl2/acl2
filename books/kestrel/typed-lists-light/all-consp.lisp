; A recognizer for lists of conses
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Note that any atom satisfies this!
;; Matches what defmergsort generates
(defund all-consp (x)
  (declare (xargs :guard t))
  (if (atom x)
      t
    (and (consp (first x))
         (all-consp (rest x)))))

;; Disabled since it may be expensive
(defthmd consp-of-car-when-all-consp
  (implies (all-consp x)
           (equal (consp (car x))
                  (consp x)))
  :hints (("Goal" :in-theory (enable all-consp))))

;; Since consp-of-car-when-all-consp is disabled by default
(defthm all-consp-forward-to-consp-of-car
  (implies (and (all-consp x)
                (consp x))
           (consp (car x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable all-consp))))

(defthm all-consp-of-cdr
  (implies (all-consp x)
           (all-consp (cdr x)))
  :hints (("Goal" :in-theory (enable all-consp))))

(defthm all-consp-of-cons
  (equal (all-consp (cons x y))
         (and (consp x)
              (all-consp y)))
  :hints (("Goal" :in-theory (enable all-consp ))))

(defthm all-consp-of-intersection-equal
  (implies (or (all-consp x)
               (all-consp y))
           (all-consp (intersection-equal x y)))
  :hints (("Goal" :in-theory (enable all-consp
                                     intersection-equal
                                     consp-of-car-when-all-consp))))
