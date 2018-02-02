; Event-Level Assertions -- Tests
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors:
;   Matt Kaufmann (kaufmann@cs.utexas.edu)
;   Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "assert")
(include-book "eval")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (progn
   (assert! (equal 3 3)
            (defun assert-test1 (x) x))

; Check that above defun was evaluated.
   (value-triple (or (equal (assert-test1 3) 3)
                     (er hard 'top-level
                         "Failed to evaluate (assert-test1 3) to 3.")))))

(local
 (progn
   (must-fail
    (assert! (equal 3 4)
             (defun assert-test2 (x) x)))

; Check that above defun was not evaluated.
   (defun assert-test2 (x)
     (cons x x))))

; Simple test with no second argument:
(assert! (equal (append '(a b c) '(d e f))
                '(a b c d e f)))

; Check failure of assertion when condition is false:
(local
 (must-fail
  (assert! (equal (append '(a b c) '(d e f))
                  '(a b)))))

; The following requires that this book be certified in the initial
; certification world, unless an acl2-customization file has been supplied.  It
; also succeeds at include-book time even if we include the book after
; executing another command, because assert! uses make-event with
; :check-expansion nil.  See assert-include.lisp.
; HOWEVER....
; This book is no longer certified in the initial certification world during
; regressions, because cert.pl causes LD of books/xdoc/top.port and also, in
; the current directory, eval.port.  So we comment out the following form.
;   (local (make-event
;           (er-let* ((c (getenv$ "ACL2_CUSTOMIZATION" state)))
;             (value
;              (if (and c (not (equal c "NONE")))
;                  `(value-triple
;                    (cw "SKIPPING due to ACL2_CUSTOMIZATION=~x0~%" ,c))
;                '(assert! (equal (access-command-tuple-form
;                                  (cddr (car (scan-to-command (w state)))))
;                                 '(exit-boot-strap-mode))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test-stobj example from David Rager.
(local
 (encapsulate
  ()

  (defstobj foo field1 field2)

  (defun test-stobj (x foo)
    (declare (xargs :stobjs foo))
    (let ((foo (update-field1 17 foo)))
      (update-field2 x foo)))

; Passes.
  (assert!-stobj (let* ((foo (test-stobj 14 foo)))
                   (mv (equal (field1 foo)
                              17)
                       foo))
                 foo)

  (must-fail
   (assert!-stobj (let* ((foo (test-stobj 14 foo)))
                    (mv (equal (field1 foo)
                               14)
                        foo))
                  foo))
  ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defun f (x) (cons x x))
 (assert-equal (f 3) '(3 . 3)))

(must-fail
 (assert-equal 1 2))
