(in-package "DJVM")

;----------------------------------------------------------------------

(include-book "base")
(include-book "base-consistent-state")

;----------------------------------------------------------------------


(defmacro BRANCHIF (cond) 
  `(if ,cond 
       (state-set-pc (arg inst) 
                     (popStack s))
     (ADVANCE-PC (popStack s))))

;----------------------------------------------------------------------

(acl2::set-verify-guards-eagerness  2)


(defun branch-target-exists (pc code)
  (declare (xargs :guard (wff-insts code)))
  (if (not (consp code)) nil
      (or (equal (inst-offset (car code)) pc)
          (branch-target-exists pc (cdr code)))))



             

