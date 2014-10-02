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

; Matt K. mode, 10/1/2014: I removed LOCAL from each MAKE-EVENT below so that
; this utility works when including uncertified books, for example when
; certifying a book after (set-write-acl2x '(t) state).  Then I also removed
; :CHECK-EXPANSION from each, because now that the make-event forms are
; non-local, the second one could cause waterfall-parallelism to be
; inadvertently turned on when including a book.

    `(progn (make-event
             (er-progn (set-waterfall-parallelism nil)
                       (value '(value-triple nil))))
            ,@events
            (make-event
             (er-progn (set-waterfall-parallelism
                        ',curr-waterfall-parallelism-val)
                       (value '(value-triple t)))))))

(defmacro without-waterfall-parallelism (&rest events)
  `(make-event (without-waterfall-parallelism-fn ',events state)))
