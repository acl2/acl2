
(in-package "ACL2")


;; This defines a simple make-event which submits a redundant copy of
;; a defthm/defun/defmacro event.  The practical use of this is for
;; cases where in a book or encapsulate context, an encapsulate
;; exports some events that should be book-local and some that should
;; not.  For example, the following illustrates how to keep FOO but
;; not BAR local, even though they are both originally produced
;; inside the same encapsulate:
#||

(encapsulate
    nil
  (local (encapsulate
             nil
           (defun foo (x y) (declare (ignore x)) y)
           (defun bar (x y) (declare (ignore y)) x)))
  (make-redundant bar))

||#

(defun make-redundant-fn (name state)
  (declare (xargs :stobjs state
                  :mode :program))
  (er-let* ((ev-wrld (er-decode-logical-name
                      name (w state) 'make-redundant-fn state)))
           (value (access-event-tuple-form (cddar ev-wrld)))))

(defmacro make-redundant (name)
  `(make-event (make-redundant-fn ',name state)))


