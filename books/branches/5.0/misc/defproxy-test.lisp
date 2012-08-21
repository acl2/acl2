; The following little book shows how to use defproxy.  See :DOC defproxy for
; more information.  Most users probably will have no need for defproxy, but
; for those who use attachments, it provides a convenient way to experiment
; with them.

; This book can be certified as suggested in file defproxy-test.acl2:

; (certify-book "defproxy-test" 0 t :ttags (:defproxy-test))

(in-package "ACL2")

(set-state-ok t)

; We imagine a function foo whose guard implies that the first argument is a
; non-nil symbol.  But we hold off on specifying the guard (simple in this
; case, but perhaps very complicated in general), by using defproxy.

(defproxy foo (* state *) => (mv * state))

; Here is an implementation of foo.  We illustrate that its guard can be weaker
; than the one that will be specified for foo.
(defun foo-impl (x state y)
  (declare (xargs :guard (symbolp x)))
  (mv (cons x y) state))

; We need a ttag in order to use :skip-checks.
(defttag :defproxy-test)

; Do the attachment.
(defattach (foo foo-impl) :skip-checks t)

; Here is a little test, showing that the attachment is working.
(make-event
 (mv-let (def state)
         (foo-impl 'defun state '(bar (x) (cons x x)))
         (value def)))

; Yep, bar did indeed get defined by the above make-event.
(assert-event (equal (bar 3) '(3 . 3)))

; Things still work after verifying guards on the implementation.  Note that we
; need to do this at some point anyhow, if we are going to attach foo-impl to
; foo without using skip-checks.
(verify-guards foo-impl)

; Assertion still holds.
(assert-event (equal (bar 3) '(3 . 3)))

; Remove the attachment.
(defattach (foo nil) :skip-checks t)

; It is optional to remove the active ttag, but we do so in order to stress
; that we don't need it any longer.
(defttag nil)

; If the guard on foo were to be T (perhaps implicitly), then we could use this
; defstub, which has the same syntax as the defproxy above:
; (defstub foo (* state *) => (mv * state))
; But we need a guard that implies the guard of foo-impl, so we stick to our
; original plan.
(encapsulate
 ((foo (x state y) (mv t state)
       :guard (and (symbolp x)
                   x)))
 (local (defun foo (x state y)
          (declare (ignore x y))
          (mv nil state))))

; Now that foo is encapsulated rather than a proxy, and foo-impl is
; guard-verified, we can attach without :skip-checks t.
(defattach foo foo-impl)

; Let's repeat the make-event experiment above, but defining function bar2 this
; time.
(make-event
 (mv-let (def state)
         (foo-impl 'defun state '(bar2 (x) (cons x x)))
         (value def)))

; As before, bar2 was indeed defined by the make-event.
(assert-event (equal (bar2 3) '(3 . 3)))
