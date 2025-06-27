; Ordered Sets (Osets) Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SET")

(include-book "top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection nonemptyp
  :parents (std/osets)
  :short "Oset non-emptiness predicate defined with an existential quantifier."
  :long
  "<p>When this predicate holds,
      it provides an under-specified witness member of the set,
      which is useful in certain proofs,
      via the rules provided here.</p>
   <p>The rule @('emptyp-to-not-nonemptyp') resp. @('not-emptyp-to-nonemptyp')
      is useful to rewrite the emptiness resp. non-emptiness of a set
      to the non-membership resp. membership of a witness in the set
      (by also enabling @('nonemptyp')).
      Although @(tsee head) could be such a witness,
      it seems to require a @(':use') hint to be brought to ACL2's attention,
      and its (non-)membership gets quickly rewritten away
      by the @('in-head') rule, which must be thus disabled for this purpose
      (even though it may still be useful for other @(tsee head)s in the proof).
      Furthermore, @(tsee head) may interact with other rules,
      depending on the form of the term that denotes the set.
      In contrast, @('nonempty-witness') is abstract.
      Thus this approach should provide more proof control.</p>
   <p>The rule @('not-emptyp-to-nonemptyp')
      has more restricted applicability than @('emptyp-to-not-nonempty'),
      in case one wants to leave alone
      @(tsee emptyp) not preceded by @(tsee not).</p>
   <p>The forward chaining rule @('nonemptyp-witness-from-not-emptyp')
      is useful to inject a witness member into a proof,
      when a set is known to be non-empty in a hypothesis.</p>
   <p>The implication rules
      @('nonemptyp-when-not-emptyp') and @('not-emptyp-when-nonemptyp')
      are mainly used to prove @('not-emptyp-to-nonemptyp'),
      but they could be useful when they provide the desired backchaining.</p>
   <p>All these rules are disabled by default.</p>
   <p>This file is not included in @('[books]/std/osets/top.lisp').
      It must be included explicitly when needed.</p>"

  (defun-sk nonemptyp (set)
    (exists (elem) (in elem set))
    :skolem-name nonemptyp-witness)

  (in-theory (disable nonemptyp nonemptyp-suff))

  (defthmd nonemptyp-when-not-emptyp
    (implies (not (emptyp set))
             (nonemptyp set))
    :hints (("Goal" :use (:instance nonemptyp-suff (elem (head set))))))

  (defthmd not-emptyp-when-nonemptyp
    (implies (nonemptyp set)
             (not (emptyp set)))
    :hints (("Goal" :in-theory (enable nonemptyp))))

  (defthmd not-emptyp-to-nonemptyp
    (equal (not (emptyp set))
           (nonemptyp set))
    :hints (("Goal" :use (nonemptyp-when-not-emptyp
                          not-emptyp-when-nonemptyp))))

  (defthmd emptyp-to-not-nonemptyp
    (equal (emptyp set)
           (not (nonemptyp set)))
    :hints (("Goal" :use not-emptyp-to-nonemptyp)))

  (theory-invariant (incompatible (:rewrite not-emptyp-to-nonemptyp)
                                  (:rewrite emptyp-to-not-nonemptyp)))

  (defthmd nonemptyp-witness-from-not-emptyp
    (implies (not (emptyp set))
             (in (nonemptyp-witness set) set))
    :rule-classes ((:forward-chaining :trigger-terms ((emptyp set))))
    :hints (("Goal"
             :use nonemptyp-when-not-emptyp
             :in-theory (enable nonemptyp)))))
