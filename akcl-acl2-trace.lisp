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

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

; We don't intend this file to be compiled.

;                            TRACE stuff

; We put over into old-trace the macro for trace that comes with ACKL.
; Thus one can type (old-trace foo) and get the effect that (trace
; foo) would have previously provided.  We do not guarantee that using
; old-trace works well with trace$, however.

(cond ((null (macro-function 'old-trace))
       (setf (macro-function 'old-trace) (macro-function 'trace))))

(cond ((null (macro-function 'old-untrace))
       (setf (macro-function 'old-untrace) (macro-function 'untrace))))

(defmacro trace (&rest fns)
  (let (acl2-fns non-acl2-fns all-fns)
    (loop for fn in fns
          do (if (function-symbolp
                  (cond
                   ((symbolp fn) fn)
                   ((and (consp fn) (symbolp (car fn)))
                    (car fn))
                   (t (error "Not a symbol or a cons of a symbol: ~s" fn)))
                  (w *the-live-state*))
                 (push fn acl2-fns)
               (push fn non-acl2-fns)))
    (cons
     'old-trace
     (progn

; Turn every element of acl2-fns into (list* fn fn ...).

       (setq acl2-fns
             (loop for x in acl2-fns
                   collect
                   (cond ((symbolp x) (list x x))
                         (t (list* (car x) (car x) (cdr x))))))

; Trace the *1* functions too.  Then every element of acl2-fns will have the
; form (list* fn original-fn ...).

       (dolist (x acl2-fns)
         (push (cons (*1*-symbol (car x))
                     (cdr x))
               acl2-fns))
       (dolist (fn acl2-fns)
         (push (progn (cond ((member :break (cdr fn))
                             (interface-er "Use of :break is not permitted in ~
                                            TRACE.  Consider :entry (progn ~
                                            (break$) arglist) instead.")))
                      (cons (car fn)
                            (trace-fix-cond
                             (trace-fix-entry
                              (car fn)
                              (trace-fix-exit (car fn)
                                              (cadr fn)
                                              (cddr fn))))))
               all-fns))
       (dolist (fn non-acl2-fns)
         (let* ((spec (if (symbolp fn) (list fn) fn))
                (fn (car spec)))
           (push (cons fn
                       (trace-fix-entry-raw
                        fn
                        (trace-fix-exit-raw
                         fn
                         (cdr spec))))
                 all-fns)))
       all-fns))))

(defmacro untrace (&rest fns)
  (cons
   'old-untrace
   (let ((ans fns))
     (dolist (fn fns)
       (push (*1*-symbol fn) ans))
     ans)))

(defun trace-ppr-gcl (direction x &aux (state *the-live-state*))

; Unfortunately, in native GCL trace :entry and :exit cause a return
; value to be printed in addition to the side-effect printing.  The > character
; is a pretty innocuous value to print.

  (let ((*inside-trace$* t))
    (declare (special *inside-trace$* *trace-level*))
    (cond ((eq direction :in)
           (incf *trace-level*)))
    (let ((trace-evisc-tuple (trace-evisc-tuple))
          (x (trace-hide-world-and-state x)))
      (ppr (eviscerate-top x
                           (cadr trace-evisc-tuple)  ;;; print-level
                           (caddr trace-evisc-tuple) ;;; print-length
                           (car trace-evisc-tuple)   ;;; alist
                           (table-alist 'evisc-table (w state))
                           (car (cddddr trace-evisc-tuple)) ;;; hiding-cars
                           state)
           (+ 2 ; GCL starts "1>" in column 2
              (first-trace-printing-column))
           (f-get-global 'trace-co state)
           state
           t))
    (cond ((eq direction :out)
           (decf *trace-level*)))
    '>))

(defun trace-fix-entry-raw (name l)
  (cond ((null l)
         (list :entry `(cons ',name (trace-hide-world-and-state si::arglist))))
        ((or (atom l)
             (and (cdr l)
                  (atom (cdr l))))
         (error "A trace spec must be a true-list, but yours ends in ~s."
                l))
        ((eq (car l) :entry)
         (list* :entry
                `(cons ',name (trace-hide-world-and-state
                               (let ((arglist si::arglist))
                                 ,(cadr l))))
                (cddr l)))
        (t (list* (car l) (cadr l) (trace-fix-entry-raw name (cddr l))))))

(defun trace-fix-entry (name l)
  (cond ((endp l)
         (list :entry
               `(trace-ppr-gcl :in
                               (cons ',name si::arglist))))
        ((eq (car l) :entry)
         (list* :entry
                `(trace-ppr-gcl :in
                                (cons ',name
                                      (let ((arglist si::arglist))
                                        ,(cadr l))))
                (cddr l)))
        (t (list* (car l) (cadr l) (trace-fix-entry name (cddr l))))))

(defun trace-values (name)
  (declare (ignore name))
  'values)

(defun trace-fix-exit-raw (name l)
  (cond ((endp l)
         (list :exit
               `(cons ',name (trace-hide-world-and-state
                              ,(trace-values name)))))
        ((eq (car l) :exit)
         (list* :exit
                `(cons ',name
                       (trace-hide-world-and-state
                        (let ((arglist si::arglist))
                          (declare (ignorable arglist))
                          ,(cadr l))))
                (cddr l)))
        (t (list* (car l) (cadr l) (trace-fix-exit-raw name (cddr l))))))

(defun trace-fix-exit (name original-name l &aux (state *the-live-state*))
  (cond ((endp l)
         (list :exit
               (protect-mv
                `(trace-ppr-gcl :out
                                (cons ',name
                                      ,(trace-values original-name)))
                (trace-multiplicity original-name state))))
        ((eq (car l) :exit)
         (list* :exit
                (protect-mv
                 `(trace-ppr-gcl :out
                                 (cons ',name
                                       (let* ((values ,(trace-values original-name))
                                              (arglist si::arglist))
                                         (declare (ignorable values arglist))
                                         ,(cadr l))))
                 (trace-multiplicity original-name state))
                (cddr l)))
        (t (list* (car l) (cadr l) (trace-fix-exit name original-name (cddr l))))))

(defun trace-fix-cond (trace-spec)
  (if (member-eq :cond trace-spec) ; optimization
      (loop for tail on trace-spec
            append
            (if (eq (car tail) :cond)
                (prog1 (list :cond
                             `(let ((arglist si::arglist))
                                ,(cadr tail)))
                  (setq tail (cdr tail)))
              (list (car tail))))
    trace-spec))
