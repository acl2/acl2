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

(include-book "type-checking")
(include-book "function-recursion")
(include-book "struct-recursion")
(include-book "programs")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ program-checking
  :parents (static-semantics)
  :short "Static checks on Leo programs."
  :long
  (xdoc::topstring
   (xdoc::p
    "These check the static semantic requirements on Leo programs.
     They include type checking,
     function (non-)recursion, and
     struct type (non-)recursion.
     They also ensure that the program has a main function."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod api
  :short "Fixtype of program APIs"
  :long
  (xdoc::topstring
   (xdoc::p
    "The API of a Leo program is its main function.
     Since there is just one main function with a known name (i.e. @('main')),
     the relevant information about it, which may vary across programs,
     consists of:")
   (xdoc::ul
    (xdoc::li
     "The list of parameters of the main function.
      Each consists of a name, type, and sort.")
    (xdoc::li
     "The output type of the main function."))
   (xdoc::p
    "We capture this information into a data structure of this fixtype.
     Note that this data structure is a ``subset'' of @(tsee fundecl),
     in the sense that it includes two of its components.")
   (xdoc::p
    "This will be extended to consist of multiple
     externally callable functions."))
  ((inputs funparam-list)
   (output type))
  :tag :api
  :pred apip)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult api-result
  :short "Fixtype of errors and program APIs"
  :ok api
  :pred api-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod api+senv
  :short "Fixtype of pairs consisting of
          a program API and a static environment."
  ((api api)
   (senv senv))
  :tag :api+senv
  :pred api+senv-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defresult api+senv-result
  :short "Fixtype of error and
          pairs consisting of a program API and a static environment."
  :ok api+senv
  :pred api+senv-resultp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: redesign or extend this for transition function entry points.

(define lookup-main-function ((file filep))
  :returns (fundecl? fundecl-optionp)
  :short "Look up the main function in a file."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through the file and return
     the declaration of the first function named @('main'),
     which is also the only one if the file is type-checked.
     We return @('nil') if no function named @('main') is found."))
  (lookup-main-function-aux (programdecl->items (file->program file)))
  :hooks (:fix)

  :prepwork
  ((define lookup-main-function-aux ((decls topdecl-listp))
     :returns (fundecl? fundecl-optionp)
     :parents nil
     (b* (((when (endp decls)) nil)
          (decl (car decls))
          ((unless (topdecl-case decl :function))
           (lookup-main-function-aux (cdr decls)))
          (fundecl (topdecl-function->get decl))
          ((when (equal (fundecl->name fundecl)
                        (identifier "main")))
           fundecl))
       (lookup-main-function-aux (cdr decls)))
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-program ((prg programp))
  :returns (api+senv api+senv-resultp)
  :short "Check a program."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently a program consists of a single file in a single file.
     We type-check the file
     and we ensure it has no function or struct type recursion.
     Then we ensure that it has a main function,
     returning the corresponding API if it does.
     We also return the static environment for the program."))
  (b* ((pkg (program->package prg))
       (file (package->file pkg))
       ((okf senv) (typecheck-file file))
       (ok (file-function-recursion-okp file))
       ((unless ok) (reserrf :function-recursion))
       (ok (file-struct-recursion-okp file))
       ((unless ok) (reserrf :struct-reccursion))
       (decl (lookup-main-function file))
       ((unless decl) (reserrf :no-main))
       (api (make-api :inputs (fundecl->inputs decl)
                      :output (fundecl->output decl))))
    (make-api+senv :api api :senv senv))
  :hooks (:fix))
