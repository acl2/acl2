; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; The examples just below come from :doc irrelevant-formals-info.  Then later
; below, as noted, are examples that are based on ones in :doc
; chk-irrelevant-formals-ok.

; This returns the list (X1 X3 X4 X5) of irrelevant formals.
(irrelevant-formals-info
 '(defun f (x0 x1 x2 x3 x4 x5)
    (declare (xargs :guard (natp x2)))
    (if (consp x0) (f (cdr x0) x1 x2 x5 x4 x3) nil)))

; This returns (X1 X3 X4 X5) as in the ``Simple Example Form'' above,
; thus illustrating that by default, `irrelevant' declarations are
; ignored (as explained earlier above).
(irrelevant-formals-info
 '(defun f (x0 x1 x2 x3 x4 x5)
    (declare (irrelevant x1 x3 x5 x4)
             (xargs :guard (natp x2)))
    (if (consp x0) (f (cdr x0) x1 x2 x5 x4 x3) nil)))

; Same as above.
(irrelevant-formals-info
 '((defun f (x0 x1 x2 x3 x4 x5)
     (declare (xargs :guard (natp x2)))
     (if (consp x0) (f (cdr x0) x1 x2 x5 x4 x3) nil))))

; Unlike the examples above, this time X2 is included in the result,
; because :guard is not in the list specified by :dcls.
(irrelevant-formals-info
 '((defun f (x0 x1 x2 x3 x4 x5)
     (declare (xargs :guard (natp x2)))
     (if (consp x0) (f (cdr x0) x1 x2 x5 x4 x3) nil)))
 :dcls nil)

; This returns ((F1 Y) (F2 Y)) because y is an irrelevant formal
; for both f1 and f2.
(irrelevant-formals-info
 '((defun f1 (x y)
     (if (consp x) (f2 (cdr x) y) t))
   (defun f2 (x y)
     (if (consp x) (f1 (cdr x) y) nil))))

; This is handled exactly as just above.
(irrelevant-formals-info
 '(mutual-recursion
   (defun f1 (x y)
     (if (consp x) (f2 (cdr x) y) t))
   (defun f2 (x y)
     (if (consp x) (f1 (cdr x) y) nil))))

 ; This is as just above, except that the missing argument in the call
 ; of f2 in the body of f1, a hard ACL2 error occurs:
(irrelevant-formals-info
 '(mutual-recursion
   (defun f1 (x y)
     (if (consp x) (f2 (cdr x)) t))
   (defun f2 (x y)
     (if (consp x) (f1 (cdr x) y) nil))))

; Because of the :result argument below, we get a msgp from the
; irrelevance check.  Try running (fmx \"~@0\" x) where x is bound
; to this result.
(irrelevant-formals-info
 '(mutual-recursion
   (defun f1 (x y)
     (if (consp x) (f2 (cdr x) y) t))
   (defun f2 (x y)
     (if (consp x) (f1 (cdr x) y) nil)))
 :result :msg)

; As above, but this time we print the message.
(fms "~@0"
     (list (cons #\0 (irrelevant-formals-info
                      '(mutual-recursion
                        (defun f1 (x y)
                          (if (consp x) (f2 (cdr x) y) t))
                        (defun f2 (x y)
                          (if (consp x) (f1 (cdr x) y) nil)))
                      :result :msg)))
     (standard-co state) state nil)

(irrelevant-formals-info
 '(mutual-recursion
   (defund f1 (x y z)
     (declare (irrelevant z))
     (if (consp x) (f2 (cdr x) y z) z))
   (defund f2 (x y z)
     (if (consp x) (f1 (cdr x) y z) nil)))
 :result :raw)

; These are adapted from :doc chk-irrelevant-formals-ok.

; Success: Returns (value t).
(chk-irrelevant-formals-ok
 '(defun f (x0 x1 x2 x3 x4 x5)
    (declare (irrelevant x1 x3 x5 x4)
             (xargs :guard (natp x2)))
    (if (consp x0) (f (cdr x0) x1 x2 x5 x4 x3) nil)))

; Failure: x2 is falsely declared irrelevant.
(chk-irrelevant-formals-ok
 '(defun f (x0 x1 x2 x3 x4 x5)
    (declare (irrelevant x1 x2 x3 x5 x4)
             (xargs :guard (natp x2)))
    (if (consp x0) (f (cdr x0) x1 x2 x5 x4 x3) nil)))

; Failure: x4 and x5 are also irrelevant.
(chk-irrelevant-formals-ok
 '(defun f (x0 x1 x2 x3 x4 x5)
    (declare (irrelevant x1 x3)
             (xargs :guard (natp x2)))
    (if (consp x0) (f (cdr x0) x1 x2 x5 x4 x3) nil)))

; Failure: x1, x4, and x5 are also irrelevant, and x0 is n ot.
(chk-irrelevant-formals-ok
 '(defun f (x0 x1 x2 x3 x4 x5)
    (declare (irrelevant x0 x3)
             (xargs :guard (natp x2)))
    (if (consp x0) (f (cdr x0) x1 x2 x5 x4 x3) nil)))

; Success: Returns (value t)
(chk-irrelevant-formals-ok
 '(mutual-recursion
   (defun f1 (x y)
     (declare (xargs :guard (consp y)))
     (if (consp x) (f2 (cdr x) y) t))
   (defun f2 (x y)
     (if (consp x) (f1 (cdr x) y) nil))))

; Failure: Error message reports y irrelevant for both definitions.
(chk-irrelevant-formals-ok
 '(mutual-recursion
   (defun f1 (x y)
     (if (consp x) (f2 (cdr x) y) t))
   (defun f2 (x y)
     (if (consp x) (f1 (cdr x) y) nil))))

;; Mutual-recursion example with more than one irrelevant formal
(irrelevant-formals-info
 '(mutual-recursion
   (defun even-natp (x irrelevant1 irrelevant2)
     (if (zp x)
         t
       (not (odd-natp (+ -1 x) irrelevant1 irrelevant2))))
   (defun odd-natp (x irrelevant3 irrelevant4)
     (if (zp x)
         nil
       (not (even-natp (+ -1 x) irrelevant3 irrelevant4))))))
