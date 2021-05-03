; ACL2 Version 8.3 -- A Computational Logic for Applicative Common Lisp
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

; Allegro's trace facilities are somewhat limited.  However it does have a
; function, advise, which is sufficiently general to allow it to imitate GCL's
; trace facilities as provided within ACL2.  See Franz's documentation for
; information on advise and unadvise.

; We put over into old-trace the macro for trace that comes with Allegro.
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

(defconst *trace-sublis* '((values . *trace-values*)
                           (si::values . *trace-values*)
                           (arglist . *trace-arglist*)
                           (si::arglist . *trace-arglist*)))

; What I am trying to do:
; Trace is called with a list of functions to be traced.  Each element of
; this list can be;
; (Let foo be defined in common lisp but not in ACL2, and
;  bar be defined within ACL2.)
; 1. the name of a non-acl2 function --- foo,
; 2. the name of an acl2 function --- bar,
; 3. a list whose only element is the name of a non-acl2 function --- (foo),
; 4. a list whose only element is the name of an acl2 function --- (bar),
; 5. a list whose car is the name of a non-acl2 function and whose
;    cdr may contain the keywords :entry and :exit, each of which
;    are followed by a function whose value will be printed upon
;    entry and exit respectively of the function being traced ---
;    (foo :entry (list (list 'arg-one (car si::arglist))
;                      (list 'arg-two (nth 1 si::arglist))))),
; 6. a list whose car is the name of an acl2 function and whose
;    cdr may contain the keywords :entry and :exit, each of which
;    are followed by a function whose value will be printed upon
;    entry and exit respectively of the function being traced ---
;    (bar :entry si::arglist
;         :exit (if (eql (nth 1 si::arglist)
;                        (nth 0 values))
;                   'FAILED
;                 (pretty-print-arg (nth 1 values))))
;
; In trace-pre-process we generate a new list as follows, where *1*bar denotes
; (*1*-symbol bar).
; 1. replacing foo with (foo foo),
; 2. replacing bar with (bar bar) & adding (*1*bar bar),
; 3, replacing (foo ...) with (foo foo ...)
; 4. replacing (bar ...) with (bar bar ...) & adding ((*1*bar ...) (bar ...)).
;
; In trace-process we generate suitable calls of advise and unadvise.
;
; Unless explicitly overridden by the :entry or :exit keywords,
; <entry trace-instructions> and <exit trace-instructions> print the
; arguments and returned values respectively.  A minor amount of
; cleaning up is done, such as printing |*STATE*| instead of the
; entire state if it is one of the arguments or values.

(defun trace-pre-process (lst)
  (let ((new-lst nil))
    (dolist (x lst new-lst)
      (let ((sym (cond
                  ((symbolp x) x)
                  ((and (consp x) (symbolp (car x)))
                   (car x))
                  (t (interface-er "Not a symbol or a cons of a symbol: ~s0" x)))))
        (if (function-symbolp sym (w *the-live-state*))

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

; We construct the (excl:advise <fn-name> :before ...) form that performs the
; tracing on entry.

  (cond ((null l)
         `(excl:advise ,name :before nil nil
                       (progn (setq *trace-arglist* si::arglist)
                              (custom-trace-ppr
                               :in
                               (cons ',name
                                     (trace-hide-world-and-state
                                      ,(if entry
                                           (sublis *trace-sublis*
                                                   entry)
                                         '*trace-arglist*)))
                               ,@(and evisc-tuple
                                      (list evisc-tuple))))))
        ((eq (car l) :entry)
         (trace-entry-rec name (cdr l) (cadr l) evisc-tuple))
        ((eq (car l) :evisc-tuple)
         (trace-entry-rec name (cdr l) entry (cadr l)))
        (t
         (trace-entry-rec name (cdr l) entry evisc-tuple))))

(defun trace-entry (name l)
  (trace-entry-rec name l nil nil))

; These next two functions were blindly copied from akcl-acl2-trace.lisp

#-acl2-mv-as-values
(defun trace-values (name)
  (list* 'list
         '(car values)
         (let ((mul (trace-multiplicity name *the-live-state*)))
           (cond ((or (null mul)
                      (eql mul 1))
                  nil)
                 (t (mv-refs-fn (1- mul)))))))

#+acl2-mv-as-values
(defun trace-values (name)
  (declare (ignore name))
  'values)

#-acl2-mv-as-values
(defun make-nths (i n var)
  (if (zerop n)
      nil
    (cons `(nth ,i ,var)
          (make-nths (1+ i) (1- n) var))))

(defun trace-exit-rec (name original-name l state exit evisc-tuple)

; We construct the (excl:advise <fn-name> :after ...) form that performs the
; tracing on entry.

  (cond ((null l)
         (cond
          ((null exit)
           `(excl:advise
             ,name :after nil nil
             (progn (setq *trace-values*
                          (trace-hide-world-and-state
                           ,(trace-values original-name)))
                    ,(protect-mv
                      `(custom-trace-ppr
                        :out
                        (cons ',name *trace-values*)
                        ,@(and evisc-tuple
                               (list evisc-tuple)))
                      (trace-multiplicity original-name state)))))
          (t
           (let ((multiplicity (trace-multiplicity original-name state)))
             `(excl:advise
               ,name :after nil nil
               (progn ,(protect-mv
                        `(progn (setq *trace-values*
                                      (trace-hide-world-and-state
                                       ,(trace-values original-name)))
                                (setq *trace-arglist* (trace-hide-world-and-state
                                                       si::arglist)))
                        multiplicity)
                      ,(protect-mv
                        `(custom-trace-ppr
                          :out
                          (cons ',name
                                ,(sublis *trace-sublis* exit))
                          ,@(and evisc-tuple
                                 (list evisc-tuple)))
                        multiplicity)))))))
        ((eq (car l) :exit)
         (trace-exit-rec name original-name (cdr l) state (cadr l) evisc-tuple))
        ((eq (car l) :evisc-tuple)
         (trace-exit-rec name original-name (cdr l) state exit (cadr l)))
        (t
         (trace-exit-rec name original-name (cdr l) state exit evisc-tuple))))

(defun trace-exit (name original-name l)
  (trace-exit-rec name original-name l *the-live-state* nil nil))

(defun traced-fns-lst (lst)
  (list 'QUOTE (mapcar #'car lst)))

(defun trace-process (lst)

; We perform a little error checking, and gather together all the (excl:advise
; ...) functions.

  (let ((new-lst (list (traced-fns-lst lst)))) ; for the returned value
    (dolist (x lst new-lst)
      (cond ((member :cond (cddr x))
             (interface-er "The use of :cond is not supported in ~
                            Allegro."))
            ((member :break (cddr x))
             (interface-er "The use of :break is not supported in ~
                            Allegro.  However, you can use either ~
                            (~s0 :entry (break$)) or (~s0 :exit (break$)). ~
                            See any Lisp documentation for more on ~
                            break and its options." (car x)))
            (t
             (push (trace-exit (car x) (cadr x) (cddr x)) new-lst)
             (push (trace-entry (car x) (cddr x)) new-lst)
             (push `(excl:unadvise ,(car x)) new-lst))))))

(excl:without-package-locks
 (defmacro trace (&rest fns)
   (if fns
       (cons 'progn
             (trace-process (trace-pre-process fns)))
     '(excl::advised-functions))))

(excl:without-package-locks
 (defmacro untrace (&rest fns)
   (if (null fns)
       '(prog1 (excl::advised-functions)
          (excl:unadvise))
     (cons
      'progn
      (let ((ans nil))
        (dolist (fn fns ans)
                (push `(excl:unadvise ,fn) ans)
                (push `(excl:unadvise ,(*1*-symbol fn)) ans)))))))
