; Defines a macro that temporarily disables waterfall parallelism and then
; restores it to its previous value.  Perhaps the calls of
; set-waterfall-parallelism need not be local, but be careful about removing
; the LOCALs: perhaps that would cause problems for how
; set-waterfall-parallelism changes the memoization status of functions, in the
; case of locally defined functions.  Another reason to keep the LOCALs is that
; the user of this macro will be unhappy if it messes with
; waterfall-parallelism settings when including a book.

(in-package "ACL2")

(defun without-waterfall-parallelism-fn (events state)
; (declare (xargs :guard (state-p state) :stobjs state))
  (declare (xargs :mode :program :stobjs state))
  (let ((curr-waterfall-parallelism-val
         (f-get-global 'waterfall-parallelism state)))
    `(progn (local (make-event
                    (er-progn (set-waterfall-parallelism nil)
                              (value '(value-triple nil)))
                    :check-expansion t))
            ,@events
            (local (make-event
                    (er-progn (set-waterfall-parallelism
                               ',curr-waterfall-parallelism-val)
                              (value '(value-triple t)))
                    :check-expansion t)))))

(defmacro without-waterfall-parallelism (&rest events)
  `(make-event (without-waterfall-parallelism-fn ',events state)))
