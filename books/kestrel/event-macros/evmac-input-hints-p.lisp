; Event Macros Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/typed-alists/keyword-truelist-alistp" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define evmac-input-hints-p (x)
  :returns (yes/no booleanp)
  :parents (event-macros event-macro-applicability-conditions)
  :short "Recognize processed hints inputs of event macros."
  :long
  (xdoc::topstring
   (xdoc::p
    "Event macros may accept, among their inputs,
     hints to prove applicability conditions.
     These hints may be given by the user
     either in the same form that follows @(':hints') in @(tsee defthm),
     in which case the supplied hints are used
     for all the applicability conditions,
     or as a "
    (xdoc::seetopic "keyword-value-listp" "keyword-value list")
    " where each keyword identifies an applicability conditions
     and the corresponding value consists of hints
     (in the same form that follows @(':hints') in @(tsee defthm))
     that are used for the identified applicability condition.")
   (xdoc::p
    "In the first case, the hints should be always a true list,
     based on the general form shown in the "
    (xdoc::seetopic "computed-hints" "topic about computed hints")
    ", which further says that each element of the list may be
     either a common hint (see the "
    (xdoc::seetopic "hints" "topic about hints")
    ") or a computed hints.
     However, for now we do capture any constraints on these elements,
     and allow, in the definition of this recognizer,
     any true list for this first case of event macro hints.")
   (xdoc::p
    "In the second case of event macro hints,
     the values of the keyword-value list should be always true lists,
     as reasoned above for the first case.
     Similarly, we do not capture further constraints on the values.
     A keyword-value list is a bit like an alist from keywords to values,
     but it is more convenient to have an event macros's input processing
     turn that into an actual alist.
     Thus, this recognizer, which is for processed hints,
     recognizes alists from keywords to true lists
     for the second case of event macro hints.")
   (xdoc::p
    "So we would like to define this recognizer as the disjunction of
     @(tsee true-listp) for the first case and
     @(tsee keyword-truelist-alistp) for the second case.
     However, since the latter implies the form
     (i.e. an alist is a true list, as stated by the local theorem below),
     the disjunction can be simplified to just @(tsee true-listp).
     Code that operates on values recognized by this predicate
     can still do different things based on whether the values
     satisfy @(tsee keyword-truelist-alistp) or just @(tsee true-listp).")
   (xdoc::p
    "We prefer to introduce this explicit recognizer,
     instead of using its current definiens @(tsee true-listp) directly,
     so that (i) the intent is more clear
     (i.e. it is not any true list; it is processed event macro hints)
     and (ii) we may add further constraints in the future."))
  (true-listp x)
  ///

  (local
   (defthm validation
     (implies (keyword-truelist-alistp x)
              (true-listp x))))

  (defthm evmac-input-hints-p-when-keyword-truelist-alistp
    (implies (keyword-truelist-alistp x)
             (evmac-input-hints-p x)))

  (defthm evmac-input-hints-p-when-true-listp
    (implies (true-listp x)
             (evmac-input-hints-p x))))
