; A variant of update-subrange
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "update-subrange")
(local (include-book "take"))

;not sure exactly how to define this in the nicest way
;i want to make sure the length is always len, even if start, end, etc. are bad
(defun update-subrange2 (len start end vals lst)
  (declare (type (integer 0 *) start end)
           (type (integer 1 *) len)
           (xargs :guard (and (true-listp vals)
                              (true-listp lst)
                              (<= (+ -1 start) end) ;relax?  think about what to do if start and end are out of order...
                              )))
  ;this could just call take of update-subrange?
;;   (take len
;;             (append (take start lst)
;;                     (take (+ 1 end (- start)) vals)
;;                     (subrange (+ 1 end) (+ -1 len) lst)))
  (take len (update-subrange start end vals lst))
  )

(defthm len-of-update-subrange2
  (equal (len (update-subrange2 len start end vals lst))
         (nfix len)))

;drop some hyps?
(defthm nth-of-update-subrange2
  (implies (and (natp n)
                (natp len)
                (natp start)
                (integerp end))
           (equal (nth n (update-subrange2 len start end vals lst))
                  (if (< n len)
                      (if (< n start)
                          (nth n lst)
                        (if (< end n)
                            (nth n lst)
                          (nth (- n start) vals)))
                    nil)))
  :hints (("Goal" :in-theory (enable natp))))

(defthm update-subrange2-iff
  (iff (update-subrange2 len start end vals lst)
       (not (zp len))))

(defthm equal-of-nil-and-update-subrange2
  (equal (equal nil (update-subrange2 len start end vals lst))
         (zp len)))

(defthm true-listp-of-update-subrange2
  (true-listp (update-subrange2 len start end vals lst)))
