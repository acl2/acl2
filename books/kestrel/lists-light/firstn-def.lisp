(in-package "ACL2")

;; This function is taken from the coi library.  See the copyright there.

(DEFUN FIRSTN (N L)
  "The sublist of L consisting of its first N elements."
  (DECLARE (XARGS :GUARD (AND (TRUE-LISTP L)
                              (INTEGERP N)
                              (<= 0 N))))
  (COND ((ENDP L) NIL)
        ((ZP N) NIL)
        (T (CONS (CAR L)
                 (FIRSTN (1- N) (CDR L))))))
