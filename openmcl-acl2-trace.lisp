; ACL2 Version 8.4 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2021, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; This file originally written by:  Robert Krug
; email:       rkrug@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

; We don't intend this file to be compiled.

;                            TRACE stuff

; This file is allegro-acl2-trace, with modifications.

; CCL's trace facilities are somewhat limited.  However it does have a
; function, advise, which is sufficiently general to allow it to imitate GCL's
; trace facilities as provided within ACL2.  This function seems to have
; limited documentation, but see the file ccl/lib/encapsulate.lisp in the
; CCL sources.

; We put over into old-trace the macro for trace that comes with CCL.
; Thus one can type (old-trace foo) and get the effect that (trace
; foo) would have previously provided.  We do not guarantee that using
; old-trace works well with trace$, however.

(cond ((null (macro-function 'old-trace))
       (setf (macro-function 'old-trace) (macro-function 'trace))))

(cond ((null (macro-function 'old-untrace))
       (setf (macro-function 'old-untrace) (macro-function 'untrace))))


; The variables *trace-arglist* and *trace-values* will contain the
; cleaned up arglist and values of a traced function.  The alist
; *trace-sublis* allows one to refer to these variables by more
; common names.

(defvar *trace-arglist*)

(defvar *trace-values*)

(defparameter *trace-sublis* '((values . *trace-values*)
                               (ccl::values . *trace-values*)
                               (arglist . *trace-arglist*)
                               (ccl::arglist . *trace-arglist*)
                               ))

(defun trace-pre-process (lst &aux (state *the-live-state*))

; The user has provided arguments lst to trace.  Here we return the result of
; converting lst to a list of entries (fn orig-fn . rst).  Each fn in lst is
; treated as (fn), and then each (fn . rst) is replaced with (fn fn . rst) and,
; if fn is known to ACL2, also (*1*fn fn . rst).

  (let ((new-lst nil))
    (dolist (x lst new-lst)
      (let ((sym (cond ((symbolp x) x)
                       ((and (consp x) (symbolp (car x)))
                        (car x))
                       (t (interface-er
                           "Not a symbol or a cons of a symbol: ~x0"
                           x)))))
        (if (function-symbolp sym (w state))

; We have an ACL2 function.

            (cond ((symbolp x)
                   (push (list (*1*-symbol x) x) new-lst)
                   (push (list x x) new-lst))
                  (t
                   (push (list* (*1*-symbol (car x)) (car x) (cdr x))
                         new-lst)
                   (push (list* (car x) (car x) (cdr x)) new-lst)))

; We do not have an ACL2 function.

          (if (fboundp sym)
              (if (symbolp x)
                  (push (list x x) new-lst)
                (push (list* (car x) (car x) (cdr x)) new-lst))
            (interface-er "~s0 is not a bound function symbol." sym)))))))

(defun trace-entry-rec (name l entry evisc-tuple)

; We construct the (ccl:advise <fn-name> ... :when :before) form that performs the
; tracing on entry.

  (cond ((null l)
         `(ccl:advise ,name
                      (progn (setq *trace-arglist* ccl::arglist)
                             (custom-trace-ppr
                              :in
                              (cons ',name
                                    (trace-hide-world-and-state
                                     ,(if entry
                                          (sublis *trace-sublis* entry)
                                        '*trace-arglist*)))
                              ,@(and evisc-tuple
                                     (list evisc-tuple))))
                      :when :before))
        ((eq (car l) :entry)
         (trace-entry-rec name (cdr l) (cadr l) evisc-tuple))
        ((eq (car l) :evisc-tuple)
         (trace-entry-rec name (cdr l) entry (cadr l)))
        (t
         (trace-entry-rec name (cdr l) entry evisc-tuple))))

(defun trace-entry (name l)
  (trace-entry-rec name l nil nil))

(defun trace-values (name)
  (declare (ignore name))
  'values)

(defun trace-exit-rec (name original-name l exit evisc-tuple)

; We construct the (ccl:advise <fn-name> ... :when :after) form that performs
; the tracing on exit.

  (cond ((null l)
         (cond
          (exit
           `(ccl:advise ,name
                        (progn (setq *trace-values*
                                     ,(trace-values original-name))
                               (setq *trace-arglist*
                                     ccl::arglist)
                               (custom-trace-ppr :out
                                                 (cons ',name
                                                       (trace-hide-world-and-state
                                                        ,(sublis *trace-sublis*
                                                                 exit)))
                                                 ,@(and evisc-tuple
                                                        (list evisc-tuple))))
                        :when :after))
          (t
           `(ccl:advise ,name
                        (progn (setq *trace-values*
                                     ,(trace-values original-name))
                               (custom-trace-ppr :out
                                                 (cons ',name
                                                       (trace-hide-world-and-state
                                                        *trace-values*))
                                                 ,@(and evisc-tuple
                                                        (list evisc-tuple))))
                        :when :after))))
        ((eq (car l) :exit)
         (trace-exit-rec name original-name (cdr l) (cadr l) evisc-tuple))
        ((eq (car l) :evisc-tuple)
         (trace-exit-rec name original-name (cdr l) exit (cadr l)))
        (t
         (trace-exit-rec name original-name (cdr l) exit evisc-tuple))))

(defun trace-exit (name original-name l)
  (trace-exit-rec name original-name l nil nil))

(defun traced-fns-lst (lst)
  (list 'QUOTE (mapcar #'car lst)))

(defun trace-process (lst)

; We perform a little error checking, and gather together all the (ccl:advise
; ...) calls.

  (let ((new-lst (list (traced-fns-lst lst)))) ; for the returned value
    (dolist (x lst new-lst)
      (cond ((member :cond (cddr x))
             (interface-er "The use of :cond is not supported in CCL."))
            ((member :break (cddr x))
             (interface-er "The use of :break is not supported in CCL.  ~
                            However, you can use either (~s0 :entry (break)) ~
                            or (~s0 :exit (break)). See any Lisp ~
                            documentation for more on break and its options."
                           (car x)))
            (t
             (push (trace-exit (car x) (cadr x) (cddr x)) new-lst)
             (push (trace-entry (car x) (cddr x)) new-lst)
             (push `(ccl:unadvise ,(car x)) new-lst))))))

(defun acl2-traced-fns ()
  (sort (delete-duplicates (strip-cars (ccl:advisedp t)))
        #'symbol<))

(let ((temp ccl::*warn-if-redefine-kernel*))
  (setf ccl::*warn-if-redefine-kernel* nil)
  (defmacro trace (&rest fns)
    (if fns
        (cons 'progn
              (trace-process (trace-pre-process fns)))
      '(acl2-traced-fns)))
  (setf ccl::*warn-if-redefine-kernel* temp))

(let ((temp ccl::*warn-if-redefine-kernel*))
  (setf ccl::*warn-if-redefine-kernel* nil)
  (defmacro untrace (&rest fns)
    (if (null fns)
        '(prog1 (acl2-traced-fns)
           (ccl:unadvise t))
      (cons 'progn
            (let ((ans nil))
              (dolist (fn fns ans)
                (push `(when (fboundp ',fn)
                         (ccl:unadvise ,fn))
                      ans)
                (push `(when (fboundp ',(*1*-symbol fn))
                         (ccl:unadvise ,(*1*-symbol fn)))
                      ans))))))
  (setf ccl::*warn-if-redefine-kernel* temp))
