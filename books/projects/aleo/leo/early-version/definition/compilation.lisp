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

(include-book "lexing-and-parsing")
(include-book "syntax-abstraction")
(include-book "input-syntax-abstraction")
(include-book "output-syntax-abstraction")
(include-book "program-and-input-checking")
(include-book "output-checking")
(include-book "program-execution")
(include-book "output-execution")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ compilation
  :parents (language)
  :short "Compilation of Leo."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize the notion of correct compilation of Leo.
     In the current version of Leo,
     this involves relating three files (from the file system):
     the code file, the input file, and the output file.
     Each is represented as a finite sequence of Unicode characters,
     which is the content of each file after UTF-8 decoding.")
   (xdoc::p
    "Leo compilation produces the output file from the code and input files.
     There will be more files in future versions of Leo,
     but this is all that we capture for the current version.
     We capture that as a relation between the code, input, and output file.")
   (xdoc::p
    "The relation is that:")
   (xdoc::ul
    (xdoc::li
     "Code, input, and output files (i.e. lists of Unicode characters)
      are correctly lexed and parsed to CSTs.")
    (xdoc::li
     "Code, input, and output CSTs are correctly abstracted to ASTs.")
    (xdoc::li
     "Code, input, and output ASTs satisfy
      all their static semsantic requirements.")
    (xdoc::li
     "Executing the code AST on the input AST
      completes without error and returns a value;
      executing the output AST yields the same value."))
   (xdoc::p
    "This is an initial formalization of correct compilation.
     As the Leo langauge and its formalization are extended,
     we will extend the notion of correct compilation accordingly.
     In particular, at some point we may formulate it on
     a (suitably abstract) model of (a portion of) the file system;
     this will be importnt when
     a Leo program will consist of multiple files,
     and will also involve configuration files."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk compilep ((code unicode-listp)
                     (input unicode-listp)
                     (output unicode-listp)
                     (curve curvep))
  :returns (yes/no booleanp)
  :short "Check correct compilation."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(see compilation),
     this is a relation among the code, input, and output files,
     each of which is represented as a list of Unicode characters.
     This is a non-executable predicate,
     which makes use of an existential quantifier
     to introduce the code, input, and output CSTs,
     the code, input, and output ASTs,
     the static environment for the program
     a limit that suffuces to execute the program,
     the type of the output, and the value of the output."))
  (exists (code-cst
           input-cst
           output-cst
           code-ast
           input-ast
           output-ast
           env
           limit
           output-type
           output-value)
          (and (abnf::treep code-cst)
               (abnf::treep input-cst)
               (abnf::treep output-cst)
               (filep code-ast)
               (input-filep input-ast)
               (output-filep output-ast)
               (senvp env)
               (natp limit)
               (typep output-type)
               (valuep output-value)
               (b* ((pkg (make-package :file code-ast))
                    (prg (make-program :package pkg)))
                 (and (file-lex-parse-p code code-cst)
                      (input-file-lex-parse-p input input-cst)
                      (output-file-lex-parse-p output output-cst)
                      (equal code-ast (abs-file code-cst))
                      (equal input-ast (abs-input-file input-cst))
                      (equal output-ast (abs-output-file output-cst))
                      (equal (check-program-and-input prg input-ast)
                             env)
                      (equal (check-output-file output-ast env)
                             output-type)
                      (equal (exec-program prg input-ast curve limit)
                             (value-result-ok output-value))
                      (equal (eval-output-file output-ast curve)
                             (value-result-ok output-value))
                      (equal (type-of-value output-value)
                             output-type))))))
