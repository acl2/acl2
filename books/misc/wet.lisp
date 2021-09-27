; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Replacement for WET, from before Version 3.4.

; WARNING: Keep the functionality of this book in sync with :doc wet,
; i.e. with (defdoc wet ...) in the ACL2 source code.

(in-package "ACL2")

(set-state-ok t)
(program)

(defun wet-trace-specs1 (fns tail acc)
  (cond ((endp fns) acc)
        (t (wet-trace-specs1
            (cdr fns)
            tail
            (cons `(,(car fns)
                    :entry
                    (let ((state *the-live-state*))
                      (f-put-global 'wet-stack
                                    (cons (cons traced-fn arglist)
                                          (f-get-global 'wet-stack state))
                                    state))
                    ,@tail)
                  acc)))))

(defun executable-ancestors (flg fn wrld acc)

; Here flg is nil if fn is a single function, else fn is a list of functions.

  (cond
   (flg (if (null fn)
            acc
          (executable-ancestors
           flg (cdr fn) wrld
           (executable-ancestors nil (car fn) wrld acc))))
   ((or (member-eq fn acc)
        (getprop fn 'predefined nil 'current-acl2-world wrld))
    acc)
   (t
    (mv-let (name x)
            (constraint-info fn wrld)
            (declare (ignore x))
            (cond
             (name acc)
             (t (let ((body (getprop fn 'unnormalized-body nil
                                     'current-acl2-world wrld)))
                  (cond
                   (body (executable-ancestors t (all-fnnames body) wrld
                                               (cons fn acc)))
                   (t acc)))))))))

(defun executable-user-fns (wrld-tail wrld acc)
  (cond ((or (null wrld-tail)
             (and (eq (caar wrld-tail) 'command-landmark)
                  (eq (cadar wrld-tail) 'global-value)
                  (equal (access-command-tuple-form (cddar wrld-tail))
                         '(exit-boot-strap-mode))))
         acc)
        (t
         (executable-user-fns
          (cdr wrld-tail)
          wrld
          (cond ((and (eq (cadar wrld-tail) 'formals)
                      (mv-let (name x)
                              (constraint-info (caar wrld-tail) wrld)
                              (declare (ignore x))
                              (not name)))
                 (cons (caar wrld-tail) acc))
                (t acc))))))

(defun wet-trace-specs (form fns compile state)
  (let ((tail `(:exit
                (let ((state *the-live-state*))
                  (f-put-global 'wet-stack
                                (cdr (f-get-global 'wet-stack state))
                                state))
                ,@(and (not (eq compile :same)) ; else already the default
                       `(:compile ,compile))
                :evisc-tuple :no-print))
        (wrld (w state))
        (ctx 'wet))
    (cond
     ((eq fns :all)
      (value (wet-trace-specs1 (executable-user-fns wrld wrld nil) tail nil)))
     ((eq fns t)

; We call translate just as we do in in trans-eval:

      (mv-let
       (erp trans bindings state)
       (translate1 form
                   :stobjs-out '((:stobjs-out . :stobjs-out))
                   t
                   ctx wrld state)
       (declare (ignore bindings))
       (cond
        (erp (mv t nil state))
        (t (let ((fns (executable-ancestors t (all-fnnames trans) wrld
                                            nil)))
             (value (wet-trace-specs1 fns tail nil)))))))
     ((true-listp fns)
      (value (wet-trace-specs1 fns tail nil)))
     (t (er soft ctx
            "Illegal value for :fns (must be t, :all, or a true list of ~
             symbols):~|~x0"
            fns)))))

(defmacro with-trace-saved (form &optional need-ttag)
  (let ((cleanup-form `(mv-let (erp val state)
                               (er-progn
                                (untrace$)
                                (trans-eval (cons ',(if need-ttag
                                                        'trace!
                                                      'trace$)
                                                  saved-specs)
                                            'with-trace-saved
                                            state
                                            t))
                               (declare (ignore erp val))
                               state)))
    `(er-let* ((saved-specs (trace$)))
              (acl2-unwind-protect "with-trace-saved"
                                   ,form
                                   ,cleanup-form
                                   ,cleanup-form))))

(defun natp-digits-base-10 (i)

; This definition is based on that of integer-length.

  (declare (xargs :guard (natp i)))
  (if (zp i)
      0
    (+ 1 (natp-digits-base-10 (floor i 10)))))

(defun print-numbered-list1 (lst index integer-width chan evisc-tuple state)
  (if (endp lst)
      (newline chan state)
    (mv-let (col state)
            (fmt1 "~c0. ~x1~|"
                  (list (cons #\0 (cons index integer-width))
                        (cons #\1 (car lst)))
                  0 chan state evisc-tuple)
            (declare (ignore col))
            (print-numbered-list1 (cdr lst) (1+ index) integer-width chan
                                  evisc-tuple state))))

(defun print-numbered-list (lst chan evisc-tuple state)
  (print-numbered-list1 lst 1 (natp-digits-base-10 (length lst))
                        chan evisc-tuple state))

(defconst *see-doc-set-iprint* ; redundant with ACL2 sources.
  "~|(See :DOC set-iprint to be able to see elided values in this message.)")

(defmacro wet! (form
                &key
                (fullp 'nil)
                (evisc-tuple 'nil evisc-tuple-p)
                (fns 't)
                (compile ':same compile-p))
  `(with-output
     :off summary
     (make-event
      (progn
        (defttag :trace!)
        (remove-untouchable trace-evisceration-alist t)
        (progn!
         (pprogn
          (f-put-global 'wet-stack nil state)
          (mv-let
            (erp val state)
            (er-let* ((specs (wet-trace-specs ',form
                                              ,fns
                                              ,(if compile-p
                                                   compile
                                                 `(if (eq ,fns :all)
                                                      nil
                                                    ,compile))
                                              state)))
              (with-trace-saved
               (er-progn (untrace$)
                         (trans-eval (cons 'trace$ specs)
                                     'wet
                                     state
                                     t)
                         (mv-let
                           (erp val state)
                           ,(if fullp
                                `(with-guard-checking-error-triple
                                  :all
                                  (trans-eval ',form 'wet state t))
                              `(trans-eval ',form 'wet state t))
                           (cond
                            (erp
                             (let ((evisc-tuple
                                    ,(if evisc-tuple-p
                                         evisc-tuple
                                       '(evisc-tuple 3
                                                     4
                                                     (trace-evisceration-alist
                                                      state)
                                                     nil)))
                                   (val (f-get-global 'wet-stack state)))
                               (pprogn
                                (fms "Backtrace stack:"
                                     nil *standard-co* state nil)
                                (fms "----------------~|"
                                     nil *standard-co* state nil)

; We use 'evisc-hitp-without-iprint as it is used by ACL2 source function,
; fmt-abbrev1.  We can't get the effect we want by calling fmt-abbrev1 directly
; because we don't want to print the extra message until all printing calls
; under the print-numbered-list call have completed.

                                (f-put-global 'evisc-hitp-without-iprint nil state)
                                (print-numbered-list val
                                                     *standard-co*
                                                     evisc-tuple
                                                     state)
                                (cond ((f-get-global 'evisc-hitp-without-iprint
                                                     state)
                                       (assert$
                                        (not (iprint-enabledp state))
                                        (mv-let
                                          (col state)
                                          (fmx "~@0~|" *see-doc-set-iprint*)
                                          (declare (ignore col))
                                          state)))
                                      (t state))
                                (value (list 'value-triple
                                             :invisible)))))
                            (t (value (list 'value-triple
                                            (kwote (cdr val))))))))))
            (cond (erp (mv "WET! failed." nil state))
                  (t (mv nil val state))))))))))
