; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:  Matt Kaufmann
; email:       Kaufmann@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78701 U.S.A.

; April, 2012

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
                      (function-symbolp 'mem-tablei wrld)))
            (observation ctx
                         "Error: Symbol ~x0 is not defined as a function.~|~%"
                         sym))
           ((if (eq recompile :default)
                (member-eq (f-get-global 'host-lisp state)
                           *host-lisps-that-recompile-by-default*)
              recompile)
            (let* ((stobj-function (getprop sym 'stobj-function nil
                                            'current-acl2-world wrld))
                   (form (cltl-def-from-name sym stobj-function wrld)))
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
