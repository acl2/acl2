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

(include-book "kestrel/error-checking/ensure-list-has-no-duplicates" :dir :system)
(include-book "kestrel/error-checking/ensure-symbol-is-fresh-event-name" :dir :system)
(include-book "kestrel/std/util/defmacro-plus" :dir :system)
(include-book "kestrel/utilities/error-checking/top" :dir :system)
(include-book "kestrel/utilities/keyword-value-lists" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc event-macro-input-processing
  :parents (event-macros)
  :short "Input processing in event macros."
  :long
  (xdoc::topstring
   (xdoc::p
    "Event macros normally take inputs from the user.
     Thus, it is generally necessary to validate these inputs,
     and often transform them slightly
     (e.g. supply a default value, or translate a term),
     derive additional information from them
     (e.g. retrieve the formals and guard of a function symbol),
     etc.
     We call all of this `input processing'.")
   (xdoc::p
    "Input processing is normally the first thing
     that an event macro implementation does,
     before using the result of input processing
     to generate event, possibly files, etc.")
   (xdoc::p
    "Event macro "
    (xdoc::seetopic "event-macro-applicability-conditions"
                    "applicability conditions")
    " are a form of input validation,
     but we do not consider them part of input processing,
     for the purpose of this event macro library.
     Applicability conditions are ``deep'', undecidable checks,
     while the input validation that is part of input processing
     is normally decidable, and often relatively simple.
     There are also cases in which the inputs cannot completely validated
     until they are subjected to the more core processing
     performed by the event macro,
     e.g. if the event macro is a code generator for ACL2,
     it may be more natural to perform certain validation checks on ACL2 terms
     while they are being translated to constructs of the target language.
     These examples show that input processing does not necessarily perform
     a complete validation of the inputs of the event macro;
     it only makes those that can be conveniently done
     as a first phase in the macro,
     before the phase(s) to generate events, files, etc.")
   (xdoc::p
    "An event macros should throw "
    (xdoc::seetopic "er" "soft errors")
    " when some input validation fails.
     This allows the soft errors to be potentially caught programmatically,
     when an event macro is used that way.
     Hard errors should be used only for internal implementation errors,
     e.g. some expected condition that fails to hold.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ event-macro-input-processors
  :parents (event-macro-input-processing)
  :short (xdoc::topstring
          "Utilities for"
          (xdoc::seetopic "event-macro-input-processing"
                          "input processing")
          ".")
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define evmac-process-input-hints (hints ctx state)
  :returns (mv erp (hints$ evmac-input-hints-p) state)
  :short "Process the @(':hints') input of an event macro."
  :long
  (xdoc::topstring
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
            (ensure-list-has-no-duplicates$ kwds
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ def-process-input-fresh-function-name (input
                                                  &key
                                                  macro
                                                  other-args
                                                  auto-code
                                                  prepwork)
  (declare (xargs :guard (and (symbolp input)
                              (symbolp macro)
                              (true-listp other-args))))
  :short "Generate an input processor for
          an input that specifies a fresh function name."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some event macros have inputs
     to specify names of generated functions.
     An input of this kind must be
     either a symbol to use as the function name,
     or the keyword @(':auto') (which cannot be a function name).
     In the latter case, the function name to use
     is generated according to some method
     described in the user documentation of the event macro.
     In either case, the name must be valid for a function
     and must be fresh, i.e.
     (1) not already in the ACL2 world and
     (2) distinct from the names of other event
     being generated by the event macro.")
   (xdoc::p
    "This macro generates an input processor for this kind of inputs.
     See the implementation for details,
     which uses a readable backquote notation.
     The @('input') argument of this macro is
     the name of the input being processed.
     The @(':macro') argument is the name of the event macro.
     The @(':other-args') argument is a list of
     zero or more additional @(tsee define)-style parameters
     for the input processor,
     needed to construct the function name when the input is @(':auto').
     The @(':auto-code') argument is the code to use
     to construct the function name when the input is @(':auto');
     this must refer to the additional parameters just described.
     The @(':prepwork') argument consists of zero or more preparatory events,
     as in @(tsee define)."))
  (b* ((input-processor-name (packn-pos (list macro '-process- input) macro))
       (keyword (intern (symbol-name input) "KEYWORD"))
       (short (concatenate 'string
                           "Process the @(':"
                           (acl2::string-downcase (symbol-name input))
                           "') input.")))
    `(define ,input-processor-name (,input
                                    ,@other-args
                                    (names-to-avoid symbol-listp)
                                    ctx
                                    state)
       :returns (mv erp
                    (result
                     "A @('(tuple (fn symbolp)
                                  (updated-names-to-avoid symbol-listp)
                                  result)').")
                    state)
       :mode :program
       :short ,short
       (b* (((er &) (ensure-value-is-symbol$ ,input
                                             (msg "The ~x0 input" ,keyword)
                                             t
                                             nil))
            (fn (if (eq ,input :auto)
                    ,auto-code
                  ,input))
            ((er names-to-avoid)
             (ensure-symbol-is-fresh-event-name$
              fn
              (msg
               "The name ~x0 specified (perhaps by default) by the ~x1 input"
               fn ,keyword)
              'function
              names-to-avoid
              t
              nil)))
         (value (list fn names-to-avoid)))
       ,@(and prepwork (list :prepwork prepwork)))))
