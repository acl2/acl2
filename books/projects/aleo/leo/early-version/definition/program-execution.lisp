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

(include-book "execution")
(include-book "input-execution")
(include-book "program-checking")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ program-execution
  :parents (dynamic-semantics)
  :short "Execution of programs."
  :long
  (xdoc::topstring
   (xdoc::p
    "A program is executed together with an input file.
     First we execute the input file,
     which results in a list of function arguments.
     Then we check the function arguments
     against the main function parameters,
     ensuring that they match up to reordering:
     there must arguments for all and only the parameters,
     with values matching types and with sorts matching.
     The matching process results in
     a list of argument values for the main function,
     which is used to execute the main function and obtain a result."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lookup-funarg ((name identifierp) (args funarg-listp))
  :returns (arg funarg-optionp)
  :short "Look up a function argument with a given name
          in a list of function arguments."
  :long
  (xdoc::topstring
   (xdoc::p
    "Return the first match, if any.
     Return @('nil') if there is no match."))
  (b* (((when (endp args)) nil)
       (arg (car args))
       ((when (identifier-equiv name (funarg->name arg)))
        (funarg-fix arg)))
    (lookup-funarg name (cdr args)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define funparams-match-funargs ((params funparam-listp) (args funarg-listp))
  :returns (vals value-list-resultp)
  :short "Match function arguments to function parameters."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through the parameters in order.
     For each parameter, we try and find an argument with the same name;
     if none is found, matching fails.
     If one is found, we ensure that it has the same sort as the parameter,
     and also that the value has the type of the parameter.
     When we run out of parameters,
     for now we ignore any remaining arguments,
     but eventually we will want to fail if there are remaining arguments.
     If we reach the end of parameters without arguments left,
     parameters and arguments match up to permutation.")
   (xdoc::p
    "As we go through the parameters and find matching arguments,
     we collect the values of the arguments,
     in the same order as the parameters.
     We return the resulting list of values if successful,
     which forms the list of values to pass to the main function."))
  (b* (((when (endp params))
        ;; (if (endp args)
        ;;     nil
        ;;   (reserrf (list :extra-args (funarg-list-fix args))))
        nil)
       ((funparam param) (car params))
       (arg (lookup-funarg param.name args))
       ((unless arg) (reserrf (list :no-param param.name)))
       ((unless (equal param.sort (funarg->sort arg)))
        (reserrf (list :mismatched-sorts
                   :param param.sort
                   :arg (funarg->sort arg))))
       (val (funarg->value arg))
       (args (remove1-equal arg (funarg-list-fix args)))
       ((okf vals) (funparams-match-funargs (cdr params) args)))
    (cons val vals))
  :verify-guards :after-returns
  :prepwork
  ((local
    (in-theory
     (enable valuep-when-value-resultp-and-not-reserrp
             value-listp-when-value-list-resultp-and-not-reserrp))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec-program ((prg programp)
                      (input input-filep)
                      (curve curvep)
                      (limit natp))
  :returns (result value-resultp)
  :short "Execute a program."
  :long
  (xdoc::topstring
   (xdoc::p
    "We execute the input file, obtaining arguments.
     We find the main function, and match the arguments to its parameters.
     We call he main function with the resulting values."))
  (b* (((okf args) (eval-input-file input curve))
       (pkg (program->package prg))
       (file (package->file pkg))
       (main (lookup-main-function file))
       ((unless main) (reserrf :no-main-function))
       (params (fundecl->inputs main))
       ((okf vals) (funparams-match-funargs params args)))
    (exec-file-main file vals curve limit))
  :prepwork ((local (in-theory (disable nfix))))
  :hooks (:fix))
