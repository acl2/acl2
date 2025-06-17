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

(include-book "program-checking")
(include-book "input-checking")

(include-book "kestrel/lists-light/perm-def" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ program-and-input-checking
  :parents (static-semantics)
  :short "Static checks on Leo programs and inputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "In order to execute and compile Leo,
     the static semantics requirements must hold on
     both the program and the input file.
     These requirements include
     not only the individual ones on the program and the input file,
     but also a consistency requirement between program and input file,
     namely that the function parameters obtained from the input file
     match the ones of the main function.
     The matching is modulo permutation,
     because an input file may list its sections and items in any order."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-program-and-input ((prg programp) (infile input-filep))
  :returns (env senv-resultp)
  :short "Check a program and an input file together."
  :long
  (xdoc::topstring
   (xdoc::p
    "We first check the program, obtaining an API and a static environment.
     We use the static environment to check the input file.
     We match the program API to the result of checking the input file.")
   (xdoc::p
    "We temporarily allow the parameters of the main function
     to be a subset, as opposed to a permutation,
     of the input items in the input file.
     We plan to tighten this check to be a permutation instead.")
   (xdoc::p
    "If all the checks are successful,
     we return the static environment of the program."))
  (b* (((okf api+senv) (check-program prg))
       (api (api+senv->api api+senv))
       (env (api+senv->senv api+senv))
       ((okf params) (check-input-file infile env))
       (;(unless (acl2::perm params (program-interface->inputs interface)))
        (unless (subsetp-equal (api->inputs api) params))
        (reserrf (list :mismatched-inputs
                       :main (api->inputs api)
                       :file params))))
    env)
  :hooks (:fix))
