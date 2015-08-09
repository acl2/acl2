(in-package "ACL2")

(include-book "model") ; ACL2 model

(defun input-assumptions (n)
  (and (not (zp n))

; "Long op" is initiated at n and asserted at n+2.

       (equal (longop n) 1)
       (equal (longop (+ 1 n)) 1)))
