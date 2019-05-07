; ACL2 Version 8.2 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2019, Regents of the University of Texas

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

(in-package "ACL2")

; We compute information below to help in the reporting of ACL2 code size.

; We assume that the commands in file create-acl2-code-size have already been
; run that create the infile argument for write-acl2-code-size, which in this
; case is acl2-wc.txt.  That file records output from the wc (Linux) command.
; Why not just use our Lisp approach for everything, instead of only for
; counting lines and characters in :doc strings as we do below?  We could, by
; first reading each source file into a string (say, by reading a character and
; then writing it with princ$ into a channel to a string, finally calling
; get-output-stream-string$).  But we started with the wc command, so we simply
; proceeded by taking advantage of that.  If it becomes critical somehow to do
; this task entirely within ACL2, say because of problems with grep, then we
; may reconsider.

(program)
(set-state-ok t)

(defun write-acl2-code-size-fn (infile outfile ctx state)
  (mv-let
   (channel state)
   (open-input-channel infile :object state)
   (cond
    ((null channel)
     (pprogn (warning$ ctx nil
                       "Unable to open file ~x0 for input.  Skipping ~
                        computation of code size."
                       infile)
             (value nil)))
    (t
     (er-let* ((lines-code  (read-object channel state))
               (chars-code  (read-object channel state))
               (lines-comm  (read-object channel state))
               (chars-comm  (read-object channel state))
               (lines-blank (read-object channel state))
               (chars-blank (read-object channel state))
               (lines-total (read-object channel state))
               (chars-total (read-object channel state))
               (lines-doc (read-object channel state))
               (chars-doc (read-object channel state)))
       (let ((state (close-input-channel channel state)))
         (mv-let
          (ch state)
          (open-output-channel outfile :character state)
          (cond
           ((null ch)
            (er soft ctx
                "Unable to open file ~x0 for output."
                outfile))
           (t (pprogn
               (princ$ "Source files (not including doc.lisp):" ch state)
               (newline ch state)
               (princ$ "------------------------------------" ch state)
               (fms "  CODE LINES:~| ~c0 lines, ~c1 characters"
                    (list (cons #\0 (cons lines-code 7))
                          (cons #\1 (cons chars-code 9)))
                    ch state nil)
               (fms "  COMMENT LINES:~| ~c0 lines, ~c1 characters"
                    (list (cons #\0 (cons lines-comm 7))
                          (cons #\1 (cons chars-comm 9)))
                    ch state nil)
               (fms "  BLANK LINES:~| ~c0 lines, ~c1 characters"
                    (list (cons #\0 (cons lines-blank 7))
                          (cons #\1 (cons chars-blank 9)))
                    ch state nil)
               (fms "  TOTAL:~| ~c0 lines, ~c1 characters"
                    (list (cons #\0 (cons lines-total 7))
                          (cons #\1 (cons chars-total 9)))
                    ch state nil)
               (newline ch state)
               (princ$ "------------------------------------" ch state)
               (fms "Documentation (file books/system/doc/acl2-doc.lisp):~| ~
                     ~c0 lines, ~c1 characters~|"
                    (list (cons #\0 (cons lines-doc 7))
                          (cons #\1 (cons chars-doc 9)))
                    ch state nil)
               (princ$ "------------------------------------" ch state)
               (newline ch state)
               (close-output-channel ch state)
               (value t)))))))))))

(defmacro write-acl2-code-size (infile outfile)

; See comments at the top of the file.  This macro is called in shell script
; create-acl2-code-size.

  `(time$ (write-acl2-code-size-fn ,infile ,outfile 'write-acl2-code-size
                                   state)
          :msg "~%The execution of WRITE-ACL2-CODE-SIZE took ~st seconds of ~
                real time and ~sc seconds of run time (cpu time), and ~
                allocated ~sa bytes.~%"))
