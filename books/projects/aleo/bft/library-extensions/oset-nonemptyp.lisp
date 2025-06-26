; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT")

(include-book "std/osets/top" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk set-nonemptyp ((set set::setp))
  :returns (yes/no booleanp)
  :parents (library-extensions)
  :short "Check if an oset is not empty, using an existential quantifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "When this predicate is true,
     it provides an under-specified witness member of the set,
     which is useful for certain kinds of reasoning."))
  (exists (elem) (set::in elem set))
  :skolem-name set-nonempty-witness

  ///

  (in-theory (disable set-nonemptyp set-nonemptyp-suff))

  (defruled set-nonemptyp-when-not-emptyp
    (implies (not (set::emptyp set))
             (set-nonemptyp set))
    :use (:instance set-nonemptyp-suff (elem (set::head set))))

  (defruled set-not-emptyp-when-nonemptyp
    (implies (set-nonemptyp set)
             (not (set::emptyp set)))
    :enable set-nonemptyp)

  (defruled set-not-emptyp-to-nonemptyp
    (equal (not (set::emptyp set))
           (set-nonemptyp set))
    :use (set-nonemptyp-when-not-emptyp
          set-not-emptyp-when-nonemptyp))

  (defruled set-emptyp-to-not-nonemptyp
    (equal (set::emptyp set)
           (not (set-nonemptyp set)))
    :use (:instance set-not-emptyp-to-nonemptyp (set set))
    :enable not)

  (theory-invariant (incompatible (:rewrite set-not-emptyp-to-nonemptyp)
                                  (:rewrite set-emptyp-to-not-nonemptyp)))

  (defruled set-nonempty-witness-from-not-emptyp
    (implies (not (set::emptyp set))
             (set::in (set-nonempty-witness set) set))
    :rule-classes ((:forward-chaining :trigger-terms ((set::emptyp set))))
    :use set-nonemptyp-when-not-emptyp
    :enable set-nonemptyp))
