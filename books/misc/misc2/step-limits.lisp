; This book provides a test for the correct implementation of step-limits.

(in-package "ACL2")

(include-book "make-event/eval-check" :dir :system)

(must-succeed
 (thm 
  (equal (append x (append y z)) 
         (append (append x y) z))))

(must-succeed
; 380 steps exactly in a version between ACL2 4.2 and 4.3
 (with-prover-step-limit 
  380
  (thm
   (equal (append x (append y z)) 
          (append (append x y) z)))))

(must-fail
; 380 steps exactly in a version between ACL2 4.2 and 4.3
 (with-prover-step-limit 
  379
  (thm
   (equal (append x (append y z)) 
          (append (append x y) z)))))
