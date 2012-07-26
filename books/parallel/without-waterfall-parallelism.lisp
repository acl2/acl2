; Defines a macro that temporarily disables waterfall parallelism and then
; restores it to its previous value.  The calls of set-waterfall-parallelism
; are local, because they can change the memoization status of functions, and
; not all functions are defined non-locally (so they may exist in one pass of
; the certification but not in the next).

(in-package "ACL2")

(defun without-waterfall-parallelism-fn (events state)
  ;(declare (xargs :guard (state-p state) :stobjs state))
  (declare (xargs :mode :program :stobjs state))
  (let ((curr-waterfall-parallelism-val
         (f-get-global 'waterfall-parallelism state)))
    `(progn (local (set-waterfall-parallelism nil))
            ,@events
            (local (set-waterfall-parallelism 
                    ,curr-waterfall-parallelism-val)))))

(defmacro without-waterfall-parallelism (&rest events)
  `(make-event (without-waterfall-parallelism-fn ',events state)))
