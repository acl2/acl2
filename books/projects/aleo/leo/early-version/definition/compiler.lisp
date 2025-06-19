; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "parser-interface")
(include-book "input-parser")
(include-book "syntax-abstraction")
(include-book "input-syntax-abstraction")
(include-book "program-and-input-checking")
(include-book "program-execution")
(include-book "output-pretty-printer")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ compiler
  :parents (compilation)
  :short "Executable compiler of Leo."
  :long
  (xdoc::topstring
   (xdoc::p
    "By putting together our formalization of Leo
     with the executable parser code and input parser,
     we can run the Leo compilation process in ACL2,
     as declaratively formalized in @(see compilation).
     This does not yet generate any bytecode,
     but it does the parsing (and abstraction),
     the enforcement of the static semantic requirements,
     and the execution that generates outputs from inputs.")
   (xdoc::p
    "This compiler takes as input three paths:
     one for the code file;
     one for the input file;
     and one for the output file.
     The first two files must exist;
     they are read,
     parsed,
     abstracted,
     subjected to static checks,
     and executed.
     If there are no errors,
     an output file is created, and written at the third path mentioned above;
     if the file does not exist, it is created;
     if it exists, it is overwritten."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define compile-to-lines ((code stringp)
                          (input-file stringp)
                          (curve curvep))
  :returns (mv erp outlines)
  :short "Compile and execute a Leo program,
          returning the lines of the Leo output file."
  :long
  (xdoc::topstring
   (xdoc::p
    "The Leo source and the input file source are in the form of strings.
     This interface function may be preferred when
     interaction with a file system is not desired.")
   (xdoc::p
    "This is as described in @(see compiler).")
   (xdoc::p
    "We pass a very large limit that should never run out in practice.
     In the future, we should be able to calculate an appropriate value,
     given that the Leo program must terminate.")
   (xdoc::p
    "Since actually writing to the output file requires program mode,
     here, in logic mode, we just return the lines that form the output file.
     The function @(tsee compile) finishes the job."))
  (b* ((file-cst (parse-from-string code))
       ((when (reserrp file-cst)) (mv file-cst nil))

       ;; input-file parsing
       (input-lexemes (lexemize-leo-from-string input-file))
       ((when (reserrp input-lexemes)) (mv input-lexemes nil))
       (input-tokens (filter-and-lower-tokens input-lexemes))
       ((when (reserrp input-tokens)) (mv input-tokens nil))
       ((mv input-cst & &) (parse-input-file input-tokens))
       ((when (reserrp input-cst)) (mv input-cst nil))

       ;; abstracting
       (file-ast (abs-file file-cst))
       ((when (reserrp file-ast)) (mv file-ast nil))
       (input-ast (abs-input-file input-cst))
       ((when (reserrp input-ast)) (mv input-ast nil))

       (prg (make-program :package (make-package :file file-ast)))
       (env (check-program-and-input prg input-ast))
       ((when (reserrp env)) (mv nil nil))
       (outval (exec-program prg input-ast curve 100000000000000000000))
       ((when (reserrp outval)) (mv outval nil))
       (outexpr (value-to-value-expr outval))
       ((when (reserrp outexpr)) (mv (list :out-expr-fail outexpr) nil))
       (outfile (output-file
                 (output-section
                  (output-item
                   (output-expression outexpr)))))
       (outlines (pprint-output-file outfile)))
    (mv nil outlines)))

(define compile-file-and-input-file-to-lines ((code-path stringp)
                                              (input-path stringp)
                                              (curve curvep)
                                              state)
  :returns (mv erp outlines state)
  :short "Compile a Leo program with a Leo input file,
          generating the lines of the Leo output file."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is as described in @(see compiler).")
   (xdoc::p
    "We pass a very large limit that should never run out in practice.
     In the future, we should be able to calculate an appropriate value,
     given that the Leo program must terminate.")
   (xdoc::p
    "Since actually writing to the output file requires program mode,
     here, in logic mode, we just return the lines that form the output file.
     The function @(tsee compile) finishes the job."))
  (b* ((code (acl2::read-file-into-string code-path))
       ;; acl2::read-file-into-string is documented to potentially
       ;; "cause an error".  Possibly that is only when using the keyword args.
       ;; However, if it does signal any errors in our use cases,
       ;; then we ought to write a version that returns an error object
       ;; instead.
       ((unless (stringp code))
        (mv (list :cannot-read-code-from-path code-path) nil state))
       (input-file (acl2::read-file-into-string input-path))
       ((unless (stringp input-file))
        (mv (list :cannot-read-input-file-from-path input-path) nil state))
       ((mv erp outlines) (compile-to-lines code
                                            input-file
                                            curve)))
    (mv erp outlines state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Note, you can also use *standard-co* to output to stdout.
(define pprinted-lines-to-channel ((lines msg-listp) (channel symbolp) state)
  :returns state
  :mode :program
  :short "Write pretty-printed lines to a channel."
  (b* (((when (endp lines)) state)
       ((mv & state)
        (fmt1! "~@0" (list (cons #\0 (car lines))) 0 channel state nil)))
    (pprinted-lines-to-channel (cdr lines) channel state)))

(define pprinted-lines-to-string ((lines msg-listp) (append-to stringp))
  :returns ret
  :mode :program
  :short "Append pretty-printed lines to a string."
  (b* (((when (endp lines)) append-to)
       ((mv ?col string)
        (fmt1!-to-string "~@0" (list (cons #\0 (car lines))) 0)))
    (pprinted-lines-to-string (cdr lines) (string-append append-to string))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define compile-program-and-input-strings-to-standard-co ((code stringp)
                                                          (input stringp)
                                                          (curve curvep)
                                                          state)
   ;; The only purpose of dummy is so that the return value is an error triple
   ;; which makes it easy to elide the return value so the output looks nicer.
  :returns (mv erp dummy state)
  :mode :program
  :short "Compile a Leo program string with a Leo input file string,
          generating an output file that is written to *standard-co*."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there is no error, the output file (what would be a @('.out') file
     is written to @(see *standard-co*), and the uninteresting return value
     is suppressed.")
   (xdoc::p
    "If there is an error, the error is returned as the value part of the
     <see topic=\"ACL2____ERROR-TRIPLE\">error triple</see>,
     to instruct the REPL to output it."))
  (mv-let (erp outlines)
      (compile-to-lines code input curve)
    (if erp
        (mv nil (list :error erp) state)
      (let ((state (pprinted-lines-to-channel outlines *standard-co* state)))
        (mv nil :invisible state)))))

(define compile-program-and-input-strings-to-string ((code stringp)
                                                     (input stringp)
                                                     (curve curvep))
  :returns (mv erp outstring)
  :mode :program
  :short "Compile a Leo program string with a Leo input file string,
          generating an output file string."
  (mv-let (erp outlines)
      (compile-to-lines code input curve)
    (if erp
        (mv erp "")
      (mv nil (pprinted-lines-to-string outlines "")))))
