; proof-builder macrsos -- Tests
;
; Copyright (C) 2018, Regents of the University of Texas
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author:
;   Matt Kaufmann (kaufmann@cs.utexas.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "proof-builder-macros")
(include-book "misc/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Here are some trivial tests of prove-guard.  They do not stress it, but they
; test several aspects of its functionality.

(defun my-consp (x)
  (declare (xargs :guard t))
  (consp x))

(defun f1 (x)
  (declare (xargs :guard (my-consp x)))
  (cdr x))

(in-theory (disable my-consp (:e tau-system)))

(defun f2 (x)
  (declare (xargs :guard (my-consp x)
                  :guard-hints
                  (("Goal"
                    :instructions
                    ((prove-guard f1))))))
  (cdr x))

(defund my-consp-2 (x)
  (declare (xargs :guard t))
  (consp x))

(must-fail
 (defun f3 (x)
   (declare (xargs :guard (my-consp-2 x)
                   :guard-hints
                   (("Goal"
                     :instructions
                     ((prove-guard f1))))))
   (cdr x)))

(defun f3 (x)
   (declare (xargs :guard (my-consp-2 x)
                   :guard-hints
                   (("Goal"
                     :instructions ; verbose this time
                     ((prove-guard f1 (enable my-consp-2) nil t))))))
   (cdr x))

(must-fail
 (defun f4 (x)
   (declare (xargs :guard (my-consp-2 x)
                   :guard-hints
                   (("Goal"
                     :instructions
                     ((prove-guard f1
                                   (enable my-consp) ; insufficent
                                   ))))))
   (cdr x)))

(defun f4 (x)
   (declare (xargs :guard (my-consp-2 x)
                   :guard-hints
                   (("Goal"
                     :instructions
                     ((prove-guard f1
                                   (enable my-consp) ; insufficent
                                   (enable my-consp-2)
; Partially verbose:
                                   some))))))
   (cdr x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Here are some trivial tests of prove-termination.  They do not stress it, but they
; test several aspects of its functionality.

(defun f5 (x)
  (declare (xargs :hints (("Goal" :in-theory (enable my-consp)))))
  (if (my-consp x)
      (f5 (cdr x))
    x))

(must-fail
 (defun f6 (x)
   (if (my-consp x)
       (f6 (cdr x))
     x)))

(defun f6 (x)
  (declare (xargs :hints
                  (("Goal"
                    :instructions
                    ((prove-termination f5))))))
  (if (my-consp x)
      (f6 (cdr x))
    x))

(defund my-consp-3 (x)
  (my-consp x))

(must-fail
 (defun f7 (x)
   (declare (xargs :hints
                   (("Goal"
                     :instructions
                     ((prove-termination f5))))))
  (if (my-consp-3 x)
      (f7 (cdr x))
    x)))

(defun f7 (x)
  (declare (xargs :hints
                  (("Goal"
                    :instructions
                    ((prove-termination f5 (enable my-consp-3)))))))
  (if (my-consp-3 x)
      (f7 (cdr x))
    x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Here are some trivial tests of fancy-use.  They do not stress it, but they
; test several aspects of its functionality.

(must-fail
 (defun f8 (x)
   (if (my-consp x)
       (f8 (cdr x))
     x)))

(defun f8 (x)
  (declare (xargs :hints
                  (("Goal"
                    :instructions
                    ((fancy-use (:termination-theorem f5)))))))
  (if (my-consp x)
      (f8 (cdr x))
    x))

(defun f9 (x)
  (declare (xargs :hints
                  (("Goal"
                    :instructions
                    ((fancy-use (nth ; just to test syntax
                                 (:termination-theorem f5))))))))
  (if (my-consp x)
      (f9 (cdr x))
    x))

(must-fail
 (defthm my-consp-is-consp
   (equal (my-consp a)
          (consp a))
   :rule-classes nil))

(defthm my-consp-is-consp
  (equal (my-consp a)
         (consp a))
  :hints (("Goal"
           :instructions
           ((fancy-use (:instance my-consp (x a))))))
  :rule-classes nil)
