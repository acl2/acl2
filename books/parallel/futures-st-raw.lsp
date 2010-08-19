(in-package "ACL2")

; Futures are a raw-Lisp only feature.

(defstruct st-future
  (value nil)
  (valid nil) ; whether the value is valid
  (closure nil)
  (aborted nil))

(defmacro st-future (x)

; Speculatively creating a single-threaded future will not cause the future's
; value to be computed.  Only reading the future causes such evaluation.

  `(let ((st-future (make-st-future)))
     (setf (st-future-closure st-future) (lambda () ,x))
     (setf (st-future-valid st-future) nil) ; set to T once the value is known
     st-future))

(defun st-future-read (st-future)

; Speculatively reading from a single-threaded future will consume unnecessary
; CPU cycles (and could even lead to infinite recursion), so make sure all
; reading is necessary.

  (assert (st-future-p st-future))
  (if (st-future-valid st-future)
      (values-list (st-future-value st-future))
    (progn (setf (st-future-value st-future) 
                 (multiple-value-list (funcall (st-future-closure st-future))))
           (setf (st-future-valid st-future) t)
           (values-list (st-future-value st-future)))))

(defun st-future-abort (st-future)

; We could do nothing in this function and it would be fine.  However, we mark
; it as aborted for book keeping and clear the closure for (earlier) garbage
; collection.

  (assert (st-future-p st-future))
  (setf (st-future-closure st-future) nil)
  (setf (st-future-aborted st-future) t)
  st-future)
