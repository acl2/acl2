(in-package "ACL2")

(redef+)

(defun translate11-lst (lst ilks stobjs-out bindings known-stobjs
                            msg flet-alist cform ctx wrld state-vars)

; WARNING: This function's treatment of stobjs-out is unusual:
; (1) stobjs-out must be either t, nil, or list of stobj flags.
;     It CANNOT be a function name (``an unknown'').
; (2) If stobjs-out is nil, it is treated as though it were a list of
;     nils as long as lst.

; If stobjs-out is t, we translate each element of lst (with stobjs-out t)
; and return the resulting list.

; If stobjs-out is not t, it is a list of stobj flags as long as lst.
; We consider each element, x, of list in correspondence with each
; flag, flg.  If flg is nil, we insist that the translation of x
; return one non-stobj result.  If flg is a stobj, we insist that x BE
; flg -- except that x ``is'' a stobj, flg, only if x is flg and x is
; among known-stobjs (with proper treatment of known-stobjs = t).

; Msg is used to describe the form that contains the list, lst, of
; forms being translated.  It is only used if an error is caused when
; some element of lst violates the stobj restrictions of stobjs-out.
; If msg is nil, no allusion to the containing form is made.  If msg
; is a symbol, we describe the containing form as though it were a
; call of that function symbol.  Otherwise, we print msg with ~@ in
; ``the form x is being used, @msg, where a stobj...''.

; The cform argument is a form that provides context -- it is the one to be
; printed by trans-er+ when there isn't another obvious contextual form to
; print.  (Often x carries enough context.)

  (cond ((atom lst) (trans-value nil))
        ((eq stobjs-out t)
         (trans-er-let*
          ((x (translate11 (car lst) (car ilks) t bindings known-stobjs
                           flet-alist
                           (car lst) ctx wrld state-vars))
           (y (translate11-lst (cdr lst) (cdr ilks) t bindings known-stobjs msg
                               flet-alist cform ctx wrld state-vars)))
          (trans-value (cons x y))))
        ((car stobjs-out)
         (trans-er-let*
          ((x (cond
               (t #+skip(eq (if (or (eq known-stobjs t)
                            (member-eq (car lst) known-stobjs))
                        (car lst)
                      nil)
                    (car stobjs-out))
                (trans-value (car lst)))
               ((eq (car lst) (car stobjs-out))

; In this case, we failed because (car lst) is not considered a stobj even
; though it has the right name.

                (let ((known-stobjs (collect-non-x nil known-stobjs)))
                  (trans-er+ cform ctx
                             "The form ~x0 is being used~#1~[ ~/, as an ~
                              argument to a call of ~x2,~/, ~@2,~] where the ~
                              single-threaded object of that name is ~
                              required.  But in the current context, ~
                              ~#3~[there are no declared stobj names~/the ~
                              only declared stobj name is ~&4~/the only ~
                              declared stobj names are ~&4~]."
                             (car lst)
                             (if (null msg) 0 (if (symbolp msg) 1 2))
                             msg
                             (cond ((null known-stobjs) 0)
                                   ((null (cdr known-stobjs)) 1)
                                   (t 2))
                             known-stobjs)))
               ((and (symbolp (car lst))
                     (congruent-stobjsp (car lst)
                                        (car stobjs-out)
                                        wrld))
                (trans-er+ cform ctx
                             "The form ~x0 is being used~#1~[ ~/, as an ~
                              argument to a call of ~x2,~/, ~@2,~] where the ~
                              single-threaded object ~x3 was expected, even ~
                              though these are congruent stobjs.  See :DOC ~
                              defstobj, in particular the discussion of ~
                              congruent stobjs."
                             (car lst)
                             (if (null msg) 0 (if (symbolp msg) 1 2))
                             msg
                             (car stobjs-out)))
               (t (trans-er+ cform ctx
                             "The form ~x0 is being used~#1~[ ~/, as an ~
                              argument to a call of ~x2,~/, ~@2,~] where the ~
                              single-threaded object ~x3 is required.  Note ~
                              that the variable ~x3 is required, not merely a ~
                              term that returns such a single-threaded ~
                              object, so you may need to bind ~x3 with LET; ~
                              see :DOC stobj."
                             (car lst)
                             (if (null msg) 0 (if (symbolp msg) 1 2))
                             msg
                             (car stobjs-out)))))
           (y (translate11-lst (cdr lst) (cdr ilks) (cdr stobjs-out)
                               bindings known-stobjs msg flet-alist cform ctx
                               wrld state-vars)))
          (trans-value (cons x y))))
        (t (trans-er-let*
            ((x (translate11 (car lst) (car ilks) '(nil) bindings known-stobjs flet-alist

; At one time we passed in (car lst) here for cform (to represent the
; surrounding context).  But it makes more sense to preserve cform.  To see
; why, first note that translate11-call passes the call down to
; translate11-lst.  Now suppose we have an error, for example from the
; following where st is a stobj and the call should be (foo x st), not (foo st
; x).
;   (defun bar (x st) (declare (xargs :stobjs st)) (foo st x))
; We want to see the call of foo when told that st is being used where an
; ordinary object is expected.

                             cform ctx wrld state-vars))
             (y (translate11-lst (cdr lst) (cdr ilks) (cdr stobjs-out)
                                 bindings known-stobjs msg flet-alist cform ctx
                                 wrld state-vars)))
            (trans-value (cons x y))))))

(redef-)
