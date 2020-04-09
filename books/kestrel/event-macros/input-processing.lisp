; Event Macros Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "evmac-input-hints-p")
(include-book "evmac-input-print-p")

(include-book "kestrel/utilities/error-checking/top" :dir :system)
(include-book "kestrel/utilities/keyword-value-lists" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ event-macro-input-processors
  :parents (event-macros)
  :short "Utilities to process inputs
          that are common to multiple event macros."
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define evmac-process-input-hints (hints ctx state)
  :returns (mv erp (hints$ evmac-input-hints-p) state)
  :short "Process the @(':hints') input of an event macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a replacement for @(tsee evmac-process-input-hints).
     When that utility is no longer used, it will be removed,
     and this new utility will be renamed to @('evmac-process-input-hints').")
   (xdoc::p
    "This is for event macros that have a @(':hints') input
     for user-supplied hints to prove applicability conditions.")
   (xdoc::p
    "See the discussion in @(tsee evmac-input-hints-p)
     about the possible forms of the @(':hints') input of an event macro.
     This utility validates the @(':hints') input
     and returns it in processed form.")
   (xdoc::p
    "If the @(':hints') input is a keyword-value list,
     we check that the keywords are all distinct,
     and return it in alist form.
     We do not check that the keywords identify
     applicability conditions that are actually present,
     as this would complicate this input processing function.
     Instead, as discussed in @(tsee evmac-appcond-theorem),
     we let the event macro handle the situation.")
   (xdoc::p
    "If the @(':hints') input is not a keyword-value list,
     we ensure that it is at least a true list,
     and return it unchanged.")
   (xdoc::p
    "Note that if the input is (perhaps by default) @('nil'),
     it is recognized as a keyword-value list with unique (no) keywords,
     and returned unchanged as an alist, i.e. @('nil')."))
  (if (keyword-value-listp hints)
      (b* ((hints$ (keyword-value-list-to-alist hints))
           (kwds (strip-cars hints$))
           ((er &)
            (ensure-list-no-duplicates$ kwds
                                        (msg "The list of keywords ~x0 ~
                                              in the keyword-value list ~
                                              that forms the :HINTS input"
                                             kwds)
                                        t nil)))
        (value hints$))
    (if (true-listp hints)
        (value hints)
      (er-soft+ ctx t nil
                "The :HINTS input must be ~
                 either a keyword-value list or a true list, ~
                 but it is ~x0 instead, which is neither."
                hints))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define evmac-process-input-print (print ctx state)
  :returns (mv erp (print$ evmac-input-print-p) state)
  :short "Process the @(':print') input of an event macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is for event macros that have a @(':print') input
     to specify what is printed on the screen when the even macro is run.")
   (xdoc::p
    "If the @(':print') input, is valid,
     it is returned unchanged.
     This facilitates guard/type proofs involving this function,
     by obviating the need to enable this function in such proofs
     to establish that, if the @(':print') input passes validation,
     then it satisfies @(tsee evmac-input-print-p)."))
  (if (evmac-input-print-p print)
      (value print)
    (er-soft+ ctx t nil
              "The :PRINT input must be ~
               NIL, :ERROR, :RESULT, :INFO, or :ALL; ~
               but it is ~x0 instead."
              print)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define evmac-process-input-show-only (show-only ctx state)
  :returns (mv erp (show-only$ booleanp) state)
  :short "Process the @(':show-only') input of an event macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is for event macros that have a @(':show-only') input
     to specify whether the event expansion should be
     submitted to ACL2 or just shown on the screen.")
   (xdoc::p
    "If the @(':show-only') input, is valid,
     it is returned unchanged.
     This facilitates guard/type proofs involving this function,
     by obviating the need to enable this function in such proofs
     to establish that, if the @(':show-only') input passes validation,
     then it satisfies @(tsee booleanp)."))
  (if (booleanp show-only)
      (value show-only)
    (er-soft+ ctx t nil
              "The :SHOW-ONLY input must be T or NIL; ~
               but it is ~x0 instead."
              show-only)))
