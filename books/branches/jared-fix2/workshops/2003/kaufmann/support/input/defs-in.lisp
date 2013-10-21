(in-package "ACL2")

(defun %g1 (x y)
  (cond
   ((zp x) x)
   ((< 0 (f1 x)) y)
   (t 23)))

(in-theory (disable %g1))

(defun %g2 (x y)
  (if (atom x)
      (%g1 x y)
    (%g2 (cdr x) y)))

(in-theory (disable %g2))

(mutual-recursion
 (defun %reg1 (n)
   (declare (xargs :measure (make-ord 1 (1+ (nfix n)) 0)))
   (if (zp n)
       0
     (logxor (%wire1 (1- n))
             (input1 (1- n)))))
 (defun %reg2 (n)
   (declare (xargs :measure (make-ord 1 (1+ (nfix n)) 1)))
   (if (zp n)
       (%reg1 n)
     (logand (%wire1 (1- n))
             (%wire2 (1- n)))))
 (defun %wire1 (n)
   (declare (xargs :measure (make-ord 1 (1+ (nfix n)) 2)))
   (logior (%reg1 n) (input2 n)))
 (defun %wire2 (n)
   (declare (xargs :measure (make-ord 1 (1+ (nfix n)) 3)))
   (lognot (%wire1 n))))

(in-theory (disable %g1 %g2 %reg1 %reg2 %wire1 %wire2
                    logand logior logxor
                    ; Not disabled:  f1 lognot
                    ))
