; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Error: Body of a MACROLET binding calls FLET-bound function.
(defun f1-bad1 (x)
  (flet ((g (x) x))
    (macrolet ((mac (a) (list 'quote (g a))))
      (cons x (mac x)))))

; Error: Body of a MACROLET binding calls MACROLET-bound function.
(defun f1-bad2 (x)
  (macrolet ((g (x) x))
    (macrolet ((mac (a) (list 'quote (g a))))
      (cons x (mac x)))))

(defun f1 (x)
  (flet ((g (x) x))
    (macrolet ((mac (a) (list 'quote a)))
      (cons (g x) (mac x)))))

(assert-event (equal (f1 3) '(3 . X)))

(verify-guards f1)

(assert-event (equal (f1 3) '(3 . X)))

(defun binds-and-calls-f1 ()
  (macrolet ((f1 (x) x)
             (f2 () (list 'quote
; The following reference is to the global f1, not to the identity macro just
; above.
                          (f1 3))))
    (f2)))

(assert-event (equal (binds-and-calls-f1) '(3 . X)))

(defun f2 (x)

; This is like f1-bad1, except flet replaces macrolet hence the call of g is OK
; in the body of the local definition of mac.  For good measure we also call g
; in the body of the inner flet call, and we add declare forms.

  (flet ((g (x)
            (declare (type cons x))
            x))
    (declare (inline g))
    (flet ((mac (a)
                (declare (type (satisfies true-listp) a))
                (list 'quote (g a))))
      (cons x (mac x)))))

;;; The following should be fixed!  (It's on my list....)
; (f2 nil) ; violates first declare form
; (f2 '(3 . 3)) ; violates second declare form
; (f2 3) ; violates both declare forms

(assert-event (equal (f2 '(a b c))
                     '((A B C) QUOTE (A B C))))

; Fails:
(verify-guards f2)

(defun mac-fn (x)
  (declare (xargs :guard (true-listp x)))
  (cons (cadr x) (car x)))

(defun f3 (y z)
  (macrolet ((mac (x) (mac-fn x)))
    (mac (((ifix y) (ifix z))
          expt))))

(assert-event (equal (f3 2 3)
                     8))

; Macroexpansion fails:
(defun f3-bad (y z)
  (macrolet ((mac (x) (mac-fn x)))
    (mac (((ifix y) (ifix z))
          . expt))))

(include-book "projects/apply/top" :dir :system)

(defun$ my-id (x) x)

; Macroexpansion can't depend on apply$ on non-primitives:
(defun f3-bad2 (y z)
  (macrolet ((mac (x) (mac-fn (apply$ 'my-id (list x)))))
    (mac (((ifix y) (ifix z))
          expt))))

; Error
(defun dups-disallowed (x z)
  (flet ((f1 (y) (list 'quote (list y x)))
         (f1 (y) (list 'quote (list x y))))
    (f1 z)))

; Error
(defun cannot-bind-predefined ()
  (flet ((nth (n x) (cons n x)))
    (nth 3 nil)))

; Error
(defun cannot-bind-built-ins-not-predefined ()
  (flet ((throw-raw-ev-fncall (n x) (cons n x)))
    (throw-raw-ev-fncall 3 nil)))

; Error
(defun cannot-bind-in-main-lisp-package ()
  (flet ((let (n x) (cons n x)))
    (let 3 nil)))

; Error
(defun cannot-bind-return-last-table ()
  (macrolet ((time$1-RAW (n x) (cons n x)))
    (time$1-RAW 3 nil)))

; Error
(defun unused-var ()
  (flet ((foo (n x) x))
    (foo 3 4)))

(encapsulate
  ()
  (set-ignore-ok t)
  (defun unused-var ()
    (flet ((foo (n x) x))
      (foo 3 4)))
  (assert-event (equal (unused-var) 4)))

; Test &rest
(defun f4 (x)
  (macrolet ((mac (&rest a) (list 'quote a)))
    (cons x (mac x y z))))
(assert-event (equal (f4 7)
                     '(7 X Y Z)))

; Use local macro definition, overriding global one..
(defmacro mac (&key k)
  k)
(defun f5 (x)
  (macrolet ((mac (&key k) (list 'quote (list k k k))))
    (cons x (mac :k y))))
(assert-event (equal (f5 7)
                     '(7 Y Y Y)))
