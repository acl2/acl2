; Printing arrays
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "alen1")
(local (include-book "array1p"))

(defun print-array-vals (high-index low-index array-name array)
  (declare (xargs :measure (+ 1 (nfix (- (+ 1 high-index) low-index)))
                  :guard (and (symbolp array-name)
                              (integerp high-index)
                              (array1p array-name array)
                              (< high-index (alen1 array-name array)))
                  :guard-hints (("Goal" :in-theory (enable array1p-rewrite)))
                  )
           (type (integer 0 *) low-index))
  (if (or (< high-index low-index)
          (not (natp low-index))
          (not (natp high-index)))
      nil
    (print-array-vals (prog2$ (cw " ~y0"
                                  (cons high-index (aref1 array-name array high-index)) ;save this cons?
                                  )
                              (+ -1 high-index))
                      low-index
                      array-name
                      array)))


;fixme whitespace before and/or after isn't quite right
;does this do the right thing for very small arrays?
;prints the low elems-to-print elements
(defun print-array (array-name array elem-count-to-print)
  (declare (type (integer 0 *) elem-count-to-print)
           (xargs :guard (implies (not (eql 0 elem-count-to-print))
                                  (and (symbolp array-name)
                                       (array1p array-name array)
                                       (<= elem-count-to-print (alen1 array-name array))))
                  :guard-hints (("Goal" :in-theory (enable ARRAY1P-rewrite)))))
  (prog2$
   ;;print the open paren:
   (cw "(")
   (prog2$
    ;;print the elements
    (if (eql 0 elem-count-to-print)
        nil
      (if (equal 1 elem-count-to-print)
          (cw "~x0" (cons 0 (aref1 array-name array 0)))
        (prog2$ (cw "~y0" (cons (+ -1 elem-count-to-print) (aref1 array-name array (+ -1 elem-count-to-print)))) ;can we skip the conses?
                (prog2$ (print-array-vals (+ -2 elem-count-to-print) 1 array-name array)
                        (cw " ~x0" (cons 0 (aref1 array-name array 0))) ;no newline
                        ))))
    ;;print the close paren:
    (cw ")~%"))))
