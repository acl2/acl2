; Helper functions for manipulating calls of COND
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The CLAUSES can have length 1 or 2.  All we have to do is flatten.
;; Doesn't require the lists to be true-lists -- todo: why not?
;; TODO: Better guard
(defun extract-terms-from-cond-clauses (clauses)
  (declare (xargs :guard (true-listp clauses)))
  (if (endp clauses)
      nil
    (append (true-list-fix (first clauses))
            (extract-terms-from-cond-clauses (rest clauses)))))

;; Replace the terms in the CLAUSES with the corresponding NEW-TERMS, which
;; come in order and correspond to the terms in the existing CLAUSES.  Note
;; that each element of CLAUSES may have length 1 or 2.
(defun recreate-cond-clauses (clauses new-terms)
  (if (endp clauses)
      nil
    (let* ((clause (first clauses))
           (clause-len (len clause)) ;can be 1 or 2
           )
      (cons (take clause-len new-terms) ; the new clause
            (recreate-cond-clauses (rest clauses)
                                   (nthcdr clause-len new-terms))))))
