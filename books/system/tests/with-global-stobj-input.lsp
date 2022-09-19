; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Basic with-global-stobj tests, based somewhat on examples from the
;;; Essay on the Design of With-global-stobj
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstobj st fld)
(defstobj st2 fld2 :congruent-to st)

; Illegal at top level:
(with-global-stobj st (fld st))

; nil
(top-level (with-global-stobj st (fld st)))

; Illegal at top level:
(with-global-stobj
 st
 (st)
 (update-fld 0 st))

; <state>
(top-level (with-global-stobj
            st
            (st)
            (update-fld 1 st)))

; 1
(top-level (with-global-stobj st (fld st)))

(defun rd0 (state)
  (declare (xargs :stobjs state))
  (with-global-stobj st (fld st)))

(assert-event (equal (rd0 state) 1))

(defun wr0 (x state)
  (declare (xargs :stobjs state))
  (with-global-stobj st (st) (update-fld x st)))

; <state>
(wr0 2 state)

(assert-event (equal (rd0 state) 2))

; error: body of read-only form returns the bound stobj
(defun bad (x state)
  (declare (xargs :stobjs state))
  (with-global-stobj st (update-fld x st)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Basic aliasing tests, based somewhat on examples from the
;;; Essay on the Design of With-global-stobj
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; ok
(defun foo (val st state)
  (declare (xargs :stobjs (st state)))
  (let ((state (with-global-stobj st
                                  (st)
                                  (update-fld val st))))
    (mv (fld st) state)))

; error: free, yet bound by updating with-global-stobj form
(foo nil st state)

; (nil state)
(foo 3 st2 state)

; 3
(fld st)

(defun foo2-sub (val state)
  (declare (xargs :stobjs state))
  (with-global-stobj st
                     (st)
                     (update-fld val st)))

(defun foo2 (val st state)
  (declare (xargs :stobjs (st state)))
  (let ((state (foo2-sub val state)))
    (mv (fld st) state val)))

; Low-level test:
(assert-event (and (equal (getpropc 'foo 'global-stobjs)
                          '(NIL . (ST)))
                   (equal (getpropc 'foo2-sub 'global-stobjs)
                          '(NIL . (ST)))
                   (equal (getpropc 'foo2 'global-stobjs)
                          '(NIL . (ST)))))

; error: free, yet bound by updating with-global-stobj form
(foo2 nil st state)

(defun foo2-caller (val st state)
  (declare (xargs :stobjs (st state)))
  (foo2 val st state))

; error, as above
(foo2-caller nil st state)

; (NIL <state> 4)
(foo2 4 st2 state)

(assert-event (and (equal (fld st) 4)
                   (equal (fld st2) nil)))

; Bury the with-global-stobj call one deeper, testing error message for the
; next form after this defun.

; ok
(defun g1 (st state)
  (declare (xargs :stobjs (st state)))
  (let ((f (with-global-stobj st (fld st))))
    (mv f state (fld st))))

; (4 <state> 4)
(g1 st state)

; ok
(defun g2 (val st state)
  (declare (xargs :stobjs (st state)))
  (let ((st (update-fld val st)))
    (let ((f (with-global-stobj st (fld st))))
      (mv f (fld st) st state))))

; bad: st is returned yet bound by with-global-stobj
(g2 nil st state)

; (4 5 <st2> <state>)
(g2 5 st2 state)

(defun g3-sub (state)
  (declare (xargs :stobjs state))
  (with-global-stobj st (fld st)))

(defun g3 (state)
  (declare (xargs :stobjs state))
  (let ((f (with-global-stobj st (fld st))))
    (mv f state (g3-sub state))))

; (4 <state> 4)
(g3 state)

; error (subsidiary updating with-global-stobj form)
(defun foo3 (state)
  (declare (xargs :stobjs (state)))
  (with-global-stobj st ; st is "known" below
    (let ((state (with-global-stobj st ; illegal: st is "known" here
                   (st)
                   (update-fld 3 st))))
      (mv (fld st) state))))

; error
; (as just above but with the subsidiary with-global-stobj buried in a
; subfunction)
(defun foo3 (state)
  (declare (xargs :stobjs (state)))
  (with-global-stobj st ; st is "known" below
    (let ((state (foo2-sub val state)))
      (mv (fld st) state))))

; error (read within write this time):
(defun foo4 (state)
  (declare (xargs :stobjs (state)))
  (with-global-stobj st ; st is "known" below
    (nil nil st)
    (let ((x (with-global-stobj st ; illegal: st is "known" here
               (fld st))))
      (mv (fld st) x st))))

; error (as just above, but with the subsidiary with-global-stobj buried in a
; subfunction)
(defun foo4 (state)
  (declare (xargs :stobjs (state)))
  (with-global-stobj st ; st is "known" below
    (nil nil st)
    (let ((x (rd0 state)))
      (mv (fld st) x st))))

; error (st is free but wr0 causes updating with-global-stobj call binding st)
(let ((state (wr0 2 state)))
  (mv st state))

(defun wr1 (x state)
  (declare (xargs :stobjs state))
  (wr0 x state))

(defun wr2 (x state)
  (declare (xargs :stobjs state))
  (wr1 x state))

; error (st is free but wr2 causes updating with-global-stobj call binding st;
; path from wr2 to wr0 is shown)
(let ((state (wr2 2 state)))
  (mv st state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Adjust signature of updating with-global-stobj form
;;; by removing stobj and adding state.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; sig contains st and, at the end, state
(defun f0 (st2 state)
  (declare (xargs :stobjs (st2 state)))
  (with-global-stobj
    st
    (st st2 nil state)
    (mv st st2 nil state)))

(assert-event (and (equal (stobjs-in 'f0 (w state))
                          '(st2 state))
                   (equal (stobjs-out 'f0 (w state))
                          '(st2 nil state))))

; error: st must be in [output] signature of with-globa-stobj
(defun f1-bad (st2 state)
  (declare (xargs :stobjs (st2 state)))
  (with-global-stobj
    st
    (st2 nil state)
    (mv st2 nil state)))

; ok; sig contains st and, not at the end, state
(defun f1 (st2 state)
  (declare (xargs :stobjs (st2 state)))
  (with-global-stobj
    st
    (st2 st state nil)
    (mv st2 st state 17)))

(assert-event (and (equal (stobjs-in 'f1 (w state))
                          '(st2 state))
                   (equal (stobjs-out 'f1 (w state))
                          '(st2 state nil))))

; ok; sig does not contain state, which is added at the end
(defun f2 (st2 state)
  (declare (xargs :stobjs (st2 state)))
  (with-global-stobj
    st
    (st2 st nil)
    (mv st2 st 17)))

(assert-event (and (equal (stobjs-in 'f2 (w state))
                          '(st2 state))
                   (equal (stobjs-out 'f2 (w state))
                          '(st2 nil state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Swap-stobjs and with-local-stobj
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun f3 (st2 state)
  (declare (xargs :stobjs (st2 state)))
  (with-global-stobj
    st
    (st2 st)
    (swap-stobjs st2 st)))

(assert-event (and (equal (stobjs-in 'f3 (w state))
                          '(st2 state))
                   (equal (stobjs-out 'f3 (w state))
                          '(st2 state))))

(update-fld 1 st)
(update-fld 2 st2)
(f3 st2 state)

(assert-event (and (equal (fld st) 2)
                   (equal (fld st2) 1)
                   (equal (rd0 state) 2)))

(defun f4 (state)
  (declare (xargs :stobjs state))
  (with-global-stobj
    st
    (st)
    (with-local-stobj
      st2
      (mv-let (st st2)
        (let ((st2 (update-fld 3 st2)))
          (swap-stobjs st st2))
        st))))

(update-fld 1 st)
(update-fld 2 st2)
(f4 state)

(assert-event (and (equal (fld st) 3)
                   (equal (fld st2) 2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Nested reads are ok
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun f5 (state)
  (declare (xargs :stobjs state))
  (with-global-stobj st
    (list (fld st)
          (with-global-stobj st
            (fld st)))))

(wr0 'f5 state)
(assert-event (equal (f5 state) '(f5 f5)))

; '(F5 (F5 F5))
; -- no error, since we don't return st and hence read-only with-global-stobj
; binding st is ok
(list (fld st) (f5 state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; A few more tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Error: (st) should be (st state)
(defun write-global-st-st2 (fld fld2 state)
  (declare (xargs :stobjs state))
  (with-global-stobj st
    (st) ; should be (st state) for what's returned below
    (let ((st (update-fld fld st)))
      (with-global-stobj st2
        (st st2)
        (let ((st2 (update-fld fld2 st2)))
          (mv st st2))))))

(defun write-global-st-st2 (fld fld2 state)
  (declare (xargs :stobjs state))
  (with-global-stobj st
    (st state)
    (let ((st (update-fld fld st)))
      (with-global-stobj st2
        (st st2)
        (let ((st2 (update-fld fld2 st2)))
          (mv st st2))))))

(write-global-st-st2 'a 'b state)

(assert-event (and (equal (fld st) 'a)
                   (equal (fld st2) 'b)))

(write-global-st-st2 'c 'd state)

(assert-event (and (equal (fld st) 'c)
                   (equal (fld st2) 'd)))

(defun read-global-st-st2 (state)
  (declare (xargs :stobjs state))
  (with-global-stobj st
    (with-global-stobj st2
      (list (fld st) (fld st2)))))

(assert-event (equal (read-global-st-st2 state)
                     '(c d)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Program mode and non-guard-verified logic mode
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun f3-alt (st2 state)
  (declare (xargs :stobjs (st2 state) :mode :program))
  (with-global-stobj
    st
    (st2 st)
    (swap-stobjs st2 st)))

(assert-event (and (equal (stobjs-in 'f3-alt (w state))
                          '(st2 state))
                   (equal (stobjs-out 'f3-alt (w state))
                          '(st2 state))))

(update-fld -1 st)
(update-fld -2 st2)
(f3-alt st2 state)

(assert-event (and (equal (fld st) -2)
                   (equal (fld st2) -1)
                   (equal (rd0 state) -2)))

(verify-termination f3-alt (declare (xargs :verify-guards nil)))

(assert-event (and (equal (stobjs-in 'f3-alt (w state))
                          '(st2 state))
                   (equal (stobjs-out 'f3-alt (w state))
                          '(st2 state))))

(update-fld 1 st)
(update-fld 2 st2)
(f3-alt st2 state)

(assert-event (and (equal (fld st) 2)
                   (equal (fld st2) 1)
                   (equal (rd0 state) 2)))

(verify-guards f3-alt)

(update-fld -1 st)
(update-fld -2 st2)
(f3-alt st2 state)

(assert-event (and (equal (fld st) -2)
                   (equal (fld st2) -1)
                   (equal (rd0 state) -2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Reasoning
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm assoc-equal-put-assoc-equal
  (equal (assoc-equal key (put-assoc-equal key val alist))
         (cons key val)))

(defthm rd0-of-wr0
  (equal (rd0 (wr0 val state))
         val))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Global stobj-table
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstobj global-stobj-table (gtbl :type (stobj-table)))

; First, let's program up reading and writing the ST entry in the above
; stobj-table's global value in state.

(defun read-gtbl-st (state)
  (declare (xargs :stobjs state))
  (with-global-stobj global-stobj-table
    (stobj-let ((st (gtbl-get 'st global-stobj-table (create-st)))) ; bindings
               (val)    ; producer variable
               (fld st) ; producer
               val)))

(defun write-gtbl-st (val state)
  (declare (xargs :stobjs state))
  (with-global-stobj global-stobj-table
    (global-stobj-table)
    (stobj-let ((st (gtbl-get 'st global-stobj-table (create-st)))) ; bindings
               (st)                ; producer variable
               (update-fld val st) ; producer
               global-stobj-table)))

; Let's check that the reader above gives us the value we expected to write.

(write-gtbl-st 10 state)
(assert-event (equal (read-gtbl-st state) 10))

; Now let's repeat the experiment above by using general macros instead.

(defmacro read-gtbl (name field &optional creator)
  `(with-global-stobj global-stobj-table
     (stobj-let ((,name ; bindings
                  (gtbl-get ',name
                            global-stobj-table
                            (,(or creator
                                  (defstobj-fnname name :CREATOR :TOP nil))))))
                (,field)        ; producer variable
                (,field ,name)  ; producer
                ,field)))

(defmacro write-gtbl (val name updater &optional creator)
  `(with-global-stobj global-stobj-table
     (global-stobj-table)
     (stobj-let ((,name ; bindings
                  (gtbl-get ',name
                            global-stobj-table
                            (,(or creator
                                  (defstobj-fnname name :CREATOR :TOP nil))))))
                (,name)               ; producer variable
                (,updater ,val ,name) ; producer
                global-stobj-table)))

(defun read-gtbl-st2 (state)
  (declare (xargs :stobjs state))
  (read-gtbl st fld))

(defun write-gtbl-st2 (val state)
  (declare (xargs :stobjs state))
  (write-gtbl val st update-fld))

(write-gtbl-st 20 state)
(assert-event (equal (read-gtbl-st state) 20))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Constrained functions and defattach
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
  (((crn0 state) => *))
  (local (defun crn0 (state)
           (declare (xargs :stobjs state))
           (state-p state))))

; error: need global-stobjs of rd0 to be contained in those of crn0
(defattach crn0 rd0)

(defun rd0-in-guard (state)
  (declare (xargs :stobjs state
                  :guard (rd0 state))
           (ignore state))
  17)

; error: as above, but this time a :guard is involved
(defattach crn0 rd0-in-guard)

; error: :global-stobjs requires state as a formal
(encapsulate
  (((crn1 *) => * :global-stobjs ((st) . nil)))
  (local (defun crn1 (x) x)))

; same error as just above
(encapsulate
  (((crn1 *) => * :formals (x) :guard (consp x) :global-stobjs ((st) . nil)))
  (local (defun crn1 (x) x)))

; ok
(encapsulate
  (((crn1 state) => * :global-stobjs ((st) . nil)))
  (local (defun crn1 (state)
           (declare (xargs :stobjs state))
           (state-p state))))

; error: the :global-stobjs writes must be nil unless state is returned
(encapsulate
  (((crn2 * state) => * :global-stobjs (nil . (st))))
  (local (defun crn2 (x state)
           (declare (xargs :stobjs state))
           (cons x (state-p state)))))

; ok
(encapsulate
  (((crn2 * state) => state :global-stobjs (nil . (st))))
  (local (defun crn2 (x state)
           (declare (xargs :stobjs state))
           (f-put-global 'abc x state))))

; ok
(defattach crn1 rd0)

(update-fld 'e st)

(assert-event (equal (rd0 state) 'e))

; error: signatures don't match
(defattach crn1 wr0)

; error: signatures don't match
(defattach crn2 rd0)

; ok
(defattach crn2 wr0)

; error: duplicate :global-stobjs
(encapsulate
  (((crn3 * state) => state :global-stobjs ((st st st2 st2) . nil)))
  (local (defun crn3 (x state)
           (declare (xargs :stobjs state))
           (f-put-global 'abc x state))))

; error: duplicate :global-stobjs
(encapsulate
  (((crn3 * state) => state :global-stobjs ((st) . (st))))
  (local (defun crn3 (x state)
           (declare (xargs :stobjs state))
           (f-put-global 'abc x state))))
; ok
(encapsulate
  (((crn3 * state) => state :global-stobjs ((st) . nil)))
  (local (defun crn3 (x state)
           (declare (xargs :stobjs state))
           (f-put-global 'abc x state))))

; error (containment for writes fails)
(defattach crn3 wr0)

; error (containment for writes fails; should show path from wr2 to wr0)
(defattach crn3 wr2)

(defun rd0+ (state)
  (declare (xargs :stobjs state))
  (mv (with-global-stobj st (fld st)) state))

(encapsulate
  (((crn4 state) => (mv * state) :global-stobjs (nil . (st))))
  (local (defun crn4 (state)
           (declare (xargs :stobjs state))
           (mv 3 state))))

; ok (crn4 allows update of bound st, hence also read of bound st)
(defattach crn4 rd0+)

(defun h1 (state)
  (declare (xargs :stobjs state))
  (crn1 state))

(defun h2 (state)
  (declare (xargs :stobjs state))
  (h1 state))

; error (h2 leads to with-global-stobj binding of st)
(mv st (h2 state))
