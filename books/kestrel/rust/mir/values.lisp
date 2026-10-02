; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST")

(include-book "abstract-syntax")

; These allow the fixtype definitions below to prove
; their internal theorems under the controlled configuration,
; as in ../syntax/token-trees.lisp.
(local (include-book "kestrel/arithmetic-light/fix" :dir :system))
(local (include-book "kestrel/arithmetic-light/ifix" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/utilities/acl2-count" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ mir-values
  :parents (mir)
  :short "Runtime values of the MIR interpreter."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are typed, structured values:
     integers carry their integer type,
     and compound values (tuples, arrays, enum values)
     contain their component values directly.
     This is the natural value model for code that
     never observes byte-level representations &mdash;
     no transmutes, no unions, no raw-pointer arithmetic &mdash;
     which is the case for the currently modeled subset.
     On such code this typed-value machine coincides with
     a byte-level machine in the style of "
    (xdoc::ahref "https://github.com/minirust/minirust" "MiniRust")
    " (values encoded to abstract bytes with provenance);
     the byte layer will be added underneath
     when the modeled subset grows to observe it,
     with the value fixtypes here becoming
     the decoded view of byte-level places,
     connected by a refinement theorem.")
   (xdoc::p
    "An enum value (@(':variant')) records
     the index of the active variant and the field values.
     A struct value is a @(':variant') with index 0,
     matching the representation of structs as
     single-variant ADTs in the abstract syntax.
     A function item value (@(':fn')) is
     the zero-sized value of a function item type;
     it is what a call terminator's function operand
     evaluates to in the monomorphic core.")
   (xdoc::p
    "A reference value (@(':ref')) denotes a location:
     an @(see address) &mdash; a frame in the stack,
     a local of that frame, and a concrete path into
     the structured value of that local.
     A slice reference (@(':slice-ref')) is a fat pointer:
     an address (of an array) together with
     the start and length of the referenced window.
     Frames are numbered from the bottom of the stack,
     so an address stays meaningful while
     frames are pushed and popped above its frame;
     a reference into a frame that has been popped is dangling,
     and using one is flagged as undefined behavior
     (the borrow checker rules this out
     for the programs we ultimately care about)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum path-elem
  :short "Fixtype of concrete path elements."
  :long
  (xdoc::topstring
   (xdoc::p
    "The concrete counterpart of @(tsee proj-elem),
     used in addresses:
     place evaluation resolves each index projection's local
     to the number it holds,
     and dereferences to the address they reach,
     so an address path has only
     field selections, concrete indices, and downcasts."))
  (:field ((index acl2::nat)))
  (:index ((index acl2::nat)))
  (:downcast ((variant acl2::nat)))
  :pred path-elemp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist path-elem-list
  :short "Fixtype of lists of concrete path elements."
  :elt-type path-elem
  :true-listp t
  :elementp-of-nil nil
  :pred path-elem-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod address
  :short "Fixtype of addresses."
  :long
  (xdoc::topstring
   (xdoc::p
    "The location that a reference value denotes:
     a frame (numbered from the bottom of the stack),
     a local of that frame,
     and a concrete path into that local's value.
     See @(see mir-values)."))
  ((frame acl2::nat)
   (local acl2::nat)
   (path path-elem-list))
  :pred addressp)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-address
  :short "An address witness."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see irr-edition) for
     the purpose of these witnesses."))
  :type addressp
  :body (make-address :frame 0 :local 0 :path nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes values
  :short "Fixtypes of MIR runtime values."

  (fty::deftagsum value
    :short "Fixtype of runtime values."
    :long
    (xdoc::topstring
     (xdoc::p
      "See @(see mir-values) for
       the value model these fixtypes realize.
       The integer variants do not constrain
       their value to the range of their type;
       the interpreter maintains that invariant dynamically
       (constructing arithmetic results with
       the wrapping operations of the limits book),
       and a static well-formedness predicate will come
       with the typed-machine invariants."))
    (:bool ((val acl2::bool)))
    (:char ((val acl2::nat)))
    (:int ((val acl2::int)
           (type int-type)))
    (:uint ((val acl2::nat)
            (type uint-type)))
    (:unit ())
    (:tuple ((elems value-list)))
    (:array ((elems value-list)))
    (:variant ((index acl2::nat)
               (fields value-list)))
    (:fn ((name acl2::string)))
    (:ref ((address address)))
    (:slice-ref ((address address)
                 (start acl2::nat)
                 (len acl2::nat)))
    :pred valuep
    :measure (two-nats-measure (acl2-count x) 0))

  (fty::deflist value-list
    :short "Fixtype of lists of runtime values."
    :elt-type value
    :true-listp t
    :elementp-of-nil nil
    :pred value-listp
    :measure (two-nats-measure (acl2-count x) 1)))

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-value
  :short "A value witness."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see irr-edition) for
     the purpose of these witnesses."))
  :type valuep
  :body (value-unit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption value-option
  value
  :short "Fixtype of optional runtime values."
  :long
  (xdoc::topstring
   (xdoc::p
    "The value of a local that may be uninitialized:
     @('nil') is the uninitialized state
     (a local before its first assignment,
     or after a storage marker resets it)."))
  :pred value-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist value-option-list
  :short "Fixtype of lists of optional runtime values."
  :long
  (xdoc::topstring
   (xdoc::p
    "The locals of a frame:
     position @('i') holds the value of local @('i'),
     or @('nil') if that local is uninitialized."))
  :elt-type value-option
  :true-listp t
  :elementp-of-nil t
  :pred value-option-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The ordinals book supplies the o-p facts for the -count measures
; below; it is included here, after the deftypes cliques above,
; because it disturbs deftypes' internal proofs if loaded before them
; (which is also why ../syntax/token-tree-operations.lisp is
; a separate book from ../syntax/token-trees.lisp).
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(defines const-to-value
  :short "Turn a constant operand into a runtime value."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a direct re-tagging:
     each constant maps to the value variant of the same shape,
     recursively for constant arrays."))
  :verify-guards :after-returns

  (define const-to-value ((const constp))
    :returns (value valuep)
    :measure (const-count const)
    (const-case const
                :bool (value-bool const.value)
                :char (value-char const.value)
                :int (value-int const.value const.type)
                :uint (value-uint const.value const.type)
                :unit (value-unit)
                :fn (value-fn const.name)
                :array (value-array (const-list-to-values const.elems))))

  (define const-list-to-values ((consts const-listp))
    :returns (values value-listp)
    :measure (const-list-count consts)
    (if (endp consts)
        nil
      (cons (const-to-value (car consts))
            (const-list-to-values (cdr consts))))))
