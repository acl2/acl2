; A lightweight utility to recognize a list of function symbols
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Checks whether all of the FNS are function-symbols in WRLD.
;; We could call this function-symbol-listp, but that name is taken.
(defund function-symbolsp (fns wrld)
  (declare (xargs :guard (and (symbol-listp fns)
                              (plist-worldp wrld))))
  (if (atom fns)
      (null fns)
    (and (function-symbolp (first fns) wrld)
         (function-symbolsp (rest fns) wrld))))

(defthm function-symbolsp-of-append
  (equal (function-symbolsp (append fns1 fns2) wrld)
         (and (function-symbolsp (true-list-fix fns1) wrld)
              (function-symbolsp fns2 wrld)))
  :hints (("Goal" :in-theory (enable function-symbolsp append))))

(defthm function-symbolsp-of-cons
  (equal (function-symbolsp (cons fn fns) wrld)
         (and (function-symbolp fn wrld)
              (function-symbolsp fns wrld)))
  :hints (("Goal" :in-theory (enable function-symbolsp))))

(defthm function-symbolsp-of-cdr
  (implies (function-symbolsp fns wrld)
           (function-symbolsp (cdr fns) wrld))
  :hints (("Goal" :in-theory (enable function-symbolsp))))

(defthm function-symbolp-of-car-when-function-symbolsp
  (implies (and (function-symbolsp fns wrld)
                (consp fns))
           (function-symbolp (car fns) wrld))
  :hints (("Goal" :in-theory (enable function-symbolsp))))

(defthm function-symbolsp-of-true-list-fix
  (implies (function-symbolsp fns wrld)
           (function-symbolsp (true-list-fix fns) wrld))
  :hints (("Goal" :in-theory (enable function-symbolsp))))

(defthm function-symbolsp-when-not-consp
  (implies (not (consp fns))
           (equal (function-symbolsp fns wrld)
                  (equal fns nil)))
  :hints (("Goal" :in-theory (enable function-symbolsp))))
