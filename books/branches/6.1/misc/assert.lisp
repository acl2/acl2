; The macro assert!, defined and illustrated below, allows for assertions
; within an ACL2 book, as requested by David Rager.

; 2012-03-12: David Rager made the calls to assert! that fail local, so that
; break-on-error wouldn't break when including this book.  Also, it's nice to
; have less clutter when including the book.

(in-package "ACL2")

(defun assert!-body (assertion form)

; Note that assertion should evaluate to a single non-stobj value.  See also
; assert!-stobj-body.

  `(let ((assertion ,assertion))
     (er-progn
      (if assertion
          (value nil)
        (er soft 'assert!
            "Assertion failed:~%~x0"
            ',assertion))
      (value ',(or form '(value-triple :success))))))

(defmacro assert! (&whole whole-form
                          assertion &optional form)

; Note that assertion should evaluate to a single non-stobj value.  See also
; assert!-stobj.

  (list 'make-event (assert!-body assertion form)
        :on-behalf-of whole-form))

(assert! (equal 3 3)
         (defun assert-test1 (x) x))

; Check that above defun was evaluated.
(value-triple (or (equal (assert-test1 3) 3)
                  (er hard 'top-level
                      "Failed to evaluate (assert-test1 3) to 3.")))

(include-book "eval")

(local
 (must-fail
  (assert! (equal 3 4)
           (defun assert-test2 (x) x))))

; Check that above defun was not evaluated.
(defun assert-test2 (x)
  (cons x x))

; Simple test with no second argument:
(assert! (equal (append '(a b c) '(d e f))
                '(a b c d e f)))

; Check failure of assertion when condition is false:
(local
 (must-fail
  (assert! (equal (append '(a b c) '(d e f))
                  '(a b)))))

; The following requires that this book be certified in the initial
; certification world.  It also succeeds at include-book time even if we
; include the book after executing another command, because assert! uses
; make-event with :check-expansion nil.  See assert-include.lisp.
(local (assert! (equal (access-command-tuple-form
                        (cddr (car (scan-to-command (w state)))))
                       '(exit-boot-strap-mode))))

; We turn now to developing an extension of assert! that works with stobjs, in
; this case for assertions that return (mv val st) where val is an ordinary
; value and st is a stobj.  Our intention is to illustrate how to write other
; versions of assert!.  If you understand this extension, you can then write
; your own extensions that can similarly handle other signatures for the
; assertion.

(defun assert!-stobj-body (assertion st form)

; Assertion should evaluate to (mv val st), where val is an ordinary value and
; st is a stobj.  See also assert!-body.

  `(mv-let (result ,st)
           ,assertion
           (if result
               (mv nil ',(or form '(value-triple :success)) state ,st)
             (mv-let (erp val state)
                     (er soft 'assert!
                         "Assertion failed:~%~x0"
                         ',assertion)
                     (declare (ignore erp val))
                     (mv t nil state ,st)))))

(defmacro assert!-stobj (&whole whole-form
                                assertion st &optional form)

; Assertion should evaluate to (mv val st), where val is an ordinary value and
; st is a stobj.  See also assert!.

  (list 'make-event (assert!-stobj-body assertion st form)
        :on-behalf-of whole-form))

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
