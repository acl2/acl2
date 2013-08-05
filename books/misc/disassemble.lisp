; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann, April, 2012
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; WARNING: Keep the functionality of this book in sync with disassemble$ (and
; its documentation) in the ACL2 source code.

(in-package "ACL2")

(defun disassemble$-fn (sym recompile args)
  (declare (ignore sym recompile args)
           (xargs :guard t))
  nil)

(defttag :disassemble$)

(defmacro defun-raw (&rest args)

; Avoid warnings in (at least) CMUCL about "Unable to compute number of values
; returned by this evaluation".

  `(progn (defun ,@args)
          nil))

(defmacro defmacro-raw (&rest args)

; Avoid warnings in (at least) CMUCL about "Unable to compute number of values
; returned by this evaluation".

  `(progn (defmacro ,@args)
          nil))

(defconst *host-lisps-that-recompile-by-default*
  '(:ccl))

(progn!

 (set-raw-mode-on state)

 (defmacro-raw with-source-info (&rest forms)
   (case (f-get-global 'host-lisp *the-live-state*)
     (:ccl
      `(let ((,(intern "*SAVE-INTERACTIVE-SOURCE-LOCATIONS*" "CCL") t)
             (,(intern "*SAVE-SOURCE-LOCATIONS*" "CCL") t))
         ,@forms))
     (otherwise `(progn ,@forms))))

 (defun-raw disassemble$-fn (sym recompile args)
   (let* ((state *the-live-state*)
          (wrld (w state))
          (ctx 'disassemble$))
     (when (and args
                (not (and (eq (car args) :recompile)
                          (null (cddr args)))))
       (observation ctx
                    "Ignoring unimplemented keyword argument~#0~[~/s~] ~
                     ~&0.~|~%"
                    (remove1 :recompile (evens args))))
     (cond ((not (symbolp sym))
            (observation ctx
                         "Error: ~x0 is not a symbol.~|~%"
                         sym))
           ((not (and (fboundp sym)
                      (function-symbolp sym wrld)))
            (observation ctx
                         "Error: Symbol ~x0 is not defined as a function.~|~%"
                         sym))
           ((if (eq recompile :default)
                (member-eq (f-get-global 'host-lisp state)
                           *host-lisps-that-recompile-by-default*)
              recompile)
            (let* ((stobj-function (getprop sym 'stobj-function nil
                                            'current-acl2-world wrld))
                   (form (cltl-def-from-name1 sym stobj-function nil wrld)))
              (cond (form
                     (let ((old-fn (symbol-function sym))
                           (temp-file "temp-disassemble.lsp"))
                       (assert old-fn)
                       (unwind-protect
                           (with-source-info
                            (with-open-file
                             (str temp-file :direction :output)
                             (print form str))
                            (load temp-file)
                            (disassemble sym))
                         (delete-file temp-file)
                         (setf (symbol-function sym)
                               old-fn)))
                     (return-from disassemble$-fn nil))
                    ((and stobj-function
                          (cltl-def-from-name1 sym stobj-function t wrld))
                     (progn (observation ctx
                                         "Not dissassembling ~x0, because it ~
                                          is a macro in raw Lisp: the ~
                                          defstobj event for ~x1 specified ~
                                          :inline t.~|~%"
                                         sym
                                         stobj-function)
                            (return-from disassemble$-fn nil)))
                    (t (observation ctx
                                    "Unable to find an ACL2 definition for ~
                                     ~x0.  Disassembling the existing ~
                                     definition.~|~%"
                                    sym)))
              (disassemble sym)))
           (t (disassemble sym))))))
