; A utility to make a list of doublets
;
; Copyright (C) 2016-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defund make-doublets (xs ys)
  (declare (xargs :guard (and (true-listp xs)
                              (true-listp ys))))
  (if (endp xs)
      nil
    (cons (list (first xs) (first ys))
          (make-doublets (rest xs) (rest ys)))))

;; no case split on empty
(defthm car-of-make-doublets
  (equal (car (car (make-doublets xs ys)))
         (car xs))
  :hints (("Goal" :in-theory (enable make-doublets))))

(defthm strip-cars-of-make-doublets
  (equal (strip-cars (make-doublets xs ys))
         (true-list-fix xs))
  :hints (("Goal" :in-theory (enable make-doublets))))

(defthm strip-cadrs-of-make-doublets
  (equal (strip-cadrs (make-doublets xs ys))
         (take (len xs) ys))
  :hints (("Goal" :in-theory (enable make-doublets))))

(defthm cdr-of-make-doublets
  (equal (cdr (make-doublets x y))
         (make-doublets (cdr x) (cdr y)))
  :hints (("Goal" :in-theory (enable make-doublets))))

(defthm len-of-make-doublets
  (equal (len (make-doublets xs ys))
         (len xs))
  :hints (("Goal" :in-theory (enable make-doublets))))
