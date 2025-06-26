; Ordered Sets (Osets) Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SET")

(include-book "membership")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection nonemptyp
  :parents (std/osets)
  :short "Oset non-emptiness predicate defined with an existential quantifier."
  :long
  "<p>When this predicate holds,
      it provides an under-specified witness member of the set,
      which is useful in certain proofs,
      via the rules provided here.</p>
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
