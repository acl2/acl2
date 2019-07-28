; BV Library: bvcat2
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; bvcat2 is a utility to conveniently concatenate several bit-vectors.

(include-book "bvcat-def")

;; Build a term representing the sum of SIZE1 and SIZE2.
(defun symbolic-sum (size1 size2)
  (declare (xargs :guard t))
  (if (and (natp size1)
           (natp size2))
      ;;optimization: actually compute the sum of constants:
      (+ size1 size2)
    `(binary-+ ,size1 ,size2)))

;; Build a term representing the sum of the sizes in SIZES-AND-VALS.
(defun bvcat-size (sizes-and-vals)
  (declare (xargs :guard (and (true-listp sizes-and-vals)
                              (evenp (length sizes-and-vals))
                              sizes-and-vals)))
  (if (endp (cddr sizes-and-vals)) ;; only one size and val
      (car sizes-and-vals)
    (symbolic-sum (car sizes-and-vals)
                  (bvcat-size (cddr sizes-and-vals)))))

;; Concatenate several values together.  Takes a non-empty list of alternating sizes and values.
;; TODO: Pull out the macro body into a function.
;; TODO: Perhaps rename
(defmacro bvcat2 (&rest sizes-and-vals)
  (declare (xargs :guard (and (true-listp sizes-and-vals)
                              (evenp (len sizes-and-vals))
                              sizes-and-vals)))
  (cond ((endp (cddr sizes-and-vals)) ;; only one size and value left
         `(bvchop ,@sizes-and-vals))
        ((endp (cddddr sizes-and-vals)) ;; only two sizes and values left
         `(bvcat ,@sizes-and-vals))
        (t
         `(bvcat ,(car sizes-and-vals)
                 ,(cadr sizes-and-vals)
                 ,(bvcat-size (cddr sizes-and-vals))
                 (bvcat2 ,@(cddr sizes-and-vals))))))
