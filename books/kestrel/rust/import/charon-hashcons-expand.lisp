; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST")

(include-book "kestrel/json/top" :dir :system)
(include-book "kestrel/fty/defomap" :dir :system)

; These allow the definitions below to prove their internal theorems
; under the controlled configuration, as in the ../mir/ books.
(local (include-book "kestrel/arithmetic-light/fix" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/utilities/acl2-count" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))

; The ordinals book supplies the o-p facts for the -count measures
; under the controlled configuration, as in ../mir/values.lisp.
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ hashcons-expansion
  :parents (mir-import)
  :short "Expansion of hashcons sharing in JSON coming from Charon."
  :long
  (xdoc::topstring
   (xdoc::p
    "Charon, the extractor that produces our JSON input, deduplicates
     hashcons nodes (types and trait references):
     the first occurrence of a shared node, in document order,
     is serialized as the object
     @('{\"HashConsedValue\": [id, value]}'),
     and every later occurrence as @('{\"Deduplicated\": id}'),
     where the ids are drawn from
     a single counter for all nodes.")
   (xdoc::p
    "This pass rewrites a JSON value into an equivalent one
     with the sharing expanded away:
     it walks the value in document order,
     recording each @('\"HashConsedValue\"') node's
     (fully expanded) payload under its id
     and replacing the node by that payload,
     and replacing each @('\"Deduplicated\"') node by
     the payload recorded under its id.
     The result contains neither marker,
     so the rest of the importer never sees the sharing.
     A @('\"Deduplicated\"') id with no earlier definition
     is an error:
     the serializer emits definitions before uses,
     so this indicates a malformed or truncated input.")
   (xdoc::p
    "Following the deserializer precedents in the community books,
     each function returns @('(mv erp ...)'),
     where a non-@('nil') @('erp') describes the failure."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap hc-table
  :short "Fixtype of maps from hashcons ids to JSON values."
  :long
  (xdoc::topstring
   (xdoc::p
    "The values stored are already expanded:
     a @('\"Deduplicated\"') node is replaced by
     a straight lookup, with no further work."))
  :key-type acl2::nat
  :val-type json::value
  :pred hc-tablep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hc-single-member ((x json::valuep) (name acl2::stringp))
  :returns (value? json::value-optionp)
  :short "The value of a JSON object's single member of a given name,
          if the object has exactly one member and it has that name."
  (b* (((unless (json::value-case x :object)) nil)
       (members (json::value-object->members x))
       ((unless (and (consp members)
                     (not (consp (cdr members)))))
        nil)
       ((json::member member) (car members))
       ((unless (equal member.name (acl2::str-fix name))) nil))
    member.value))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; In the empty-object case of the measure proofs below,
;; the count of the member list computes to its base value,
;; erasing the trigger term of the library's linear lemma
;; relating an object's count to its members' count;
;; this lower bound is keyed to the count of the object itself,
;; which does survive.
(local
 (defthm value-count-lower-bound-when-object
   (implies (equal (json::value-kind x) :object)
            (<= 2 (json::value-count x)))
   :rule-classes :linear
   :hints
   (("Goal"
     :use (:instance json::member-list-count-of-value-object->members
                     (json::x x))))))

(defines hc-expand-value

  (define hc-expand-value ((x json::valuep) (table hc-tablep))
    :returns (mv erp
                 (new json::valuep)
                 (new-table hc-tablep))
    :parents (hashcons-expansion)
    :short "Expand the sharing in a JSON value."
    :measure (json::value-count x)
    :hooks nil
    (b* ((table (hc-table-fix table))
         ;; {"Deduplicated": id}
         (dedup-id (hc-single-member x "Deduplicated"))
         ((when dedup-id)
          (b* (((unless (json::value-case dedup-id :number))
                (mv (list :non-number-dedup-id) (json::value-null) table))
               (id (json::value-number->get dedup-id))
               ((unless (natp id))
                (mv (list :non-nat-dedup-id id) (json::value-null) table))
               ((unless (omap::assoc id table))
                (mv (list :dedup-id-not-defined id)
                    (json::value-null)
                    table)))
            (mv nil (omap::lookup id table) table))))
      (json::value-case
       x
       :object
       (b* (;; {"HashConsedValue": [id, value]}
            (members x.members)
            ((when (and (consp members)
                        (not (consp (cdr members)))
                        (equal (json::member->name (car members))
                               "HashConsedValue")))
             (b* ((pair (json::member->value (car members)))
                  ((unless (json::value-case pair :array))
                   (mv (list :non-array-hashconsed-node)
                       (json::value-null)
                       table))
                  (elems (json::value-array->elements pair))
                  ((unless (and (consp elems)
                                (consp (cdr elems))
                                (not (consp (cddr elems)))))
                   (mv (list :bad-hashconsed-arity)
                       (json::value-null)
                       table))
                  (id-value (car elems))
                  ((unless (json::value-case id-value :number))
                   (mv (list :non-number-hashcons-id)
                       (json::value-null)
                       table))
                  (id (json::value-number->get id-value))
                  ((unless (natp id))
                   (mv (list :non-nat-hashcons-id id)
                       (json::value-null)
                       table))
                  ((mv erp payload table)
                   (hc-expand-value (car (cdr elems)) table))
                  ((when erp) (mv erp (json::value-null) table)))
               (mv nil payload (omap::update id payload table))))
            ((mv erp new-members table)
             (hc-expand-member-list members table))
            ((when erp) (mv erp (json::value-null) table)))
         (mv nil (json::make-value-object :members new-members) table))
       :array
       (b* (((mv erp new-elems table)
             (hc-expand-value-list x.elements table))
            ((when erp) (mv erp (json::value-null) table)))
         (mv nil (json::make-value-array :elements new-elems) table))
       :otherwise (mv nil (json::value-fix x) table))))

  (define hc-expand-value-list ((xs json::value-listp) (table hc-tablep))
    :returns (mv erp
                 (new json::value-listp)
                 (new-table hc-tablep))
    :parents (hashcons-expansion)
    :short "Expand the sharing in a list of JSON values, in order."
    :measure (json::value-list-count xs)
    :hooks nil
    (b* ((table (hc-table-fix table))
         ((when (endp xs)) (mv nil nil table))
         ((mv erp new-first table) (hc-expand-value (car xs) table))
         ((when erp) (mv erp nil table))
         ((mv erp new-rest table) (hc-expand-value-list (cdr xs) table))
         ((when erp) (mv erp nil table)))
      (mv nil (cons new-first new-rest) table)))

  (define hc-expand-member-list ((members json::member-listp)
                                 (table hc-tablep))
    :returns (mv erp
                 (new json::member-listp)
                 (new-table hc-tablep))
    :parents (hashcons-expansion)
    :short "Expand the sharing in
            a list of JSON object members, in order."
    :measure (json::member-list-count members)
    :hooks nil
    (b* ((table (hc-table-fix table))
         ((when (endp members)) (mv nil nil table))
         ((json::member member) (car members))
         ((mv erp new-value table) (hc-expand-value member.value table))
         ((when erp) (mv erp nil table))
         ((mv erp new-rest table)
          (hc-expand-member-list (cdr members) table))
         ((when erp) (mv erp nil table)))
      (mv nil
          (cons (json::make-member :name member.name :value new-value)
                new-rest)
          table)))

  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hc-expand ((x json::valuep))
  :returns (mv erp (new json::valuep))
  :short "Expand the hashcons sharing in a JSON value,
          starting from an empty table."
  (b* (((mv erp new -) (hc-expand-value x nil)))
    (mv erp new))
  :hooks nil)
