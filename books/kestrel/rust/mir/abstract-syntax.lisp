; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST")

(include-book "types")

(include-book "kestrel/fty/defomap" :dir :system)

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

(defxdoc+ mir-abstract-syntax
  :parents (mir)
  :short "Abstract syntax of MIR."
  :long
  (xdoc::topstring
   (xdoc::p
    "A MIR body is a control-flow graph:
     typed locals and a list of basic blocks,
     each consisting of statements followed by one terminator.
     Locals and basic blocks are referred to by their indices
     (rustc's @('Local') and @('BasicBlock') index types);
     local 0 is the return place,
     locals 1 through the argument count are the arguments,
     and the rest are temporaries and user variables.")
   (xdoc::p
    "Per the plan's panic=abort decision (D3),
     terminators have no unwind targets:
     a failed assertion or an explicit panic aborts the machine.
     This deletes rustc's @('unwind') edges from
     call, assert, and drop terminators.")
   (xdoc::p
    "This draft covers the statement and terminator kinds
     needed for the R0 subset
     (and produced by rustc for it, with overflow checks on):
     more rvalue and cast kinds, and the unwinding forms,
     will be added as the subset ladder climbs."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum proj-elem
  :short "Fixtype of place projection elements."
  :long
  (xdoc::topstring
   (xdoc::p
    "Mirrors the core cases of rustc's @('ProjectionElem'):
     dereferencing,
     field selection (by field index),
     array indexing (by a local holding the index),
     and enum variant downcasting (by variant index).
     Constant indexing and subslicing will come with slices."))
  (:deref ())
  (:field ((index acl2::nat)))
  (:index ((local acl2::nat)))
  (:downcast ((variant acl2::nat)))
  :pred proj-elemp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist proj-elem-list
  :short "Fixtype of lists of place projection elements."
  :elt-type proj-elem
  :true-listp t
  :elementp-of-nil nil
  :pred proj-elem-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod place
  :short "Fixtype of places."
  :long
  (xdoc::topstring
   (xdoc::p
    "A place is a local with a (possibly empty) list of projections,
     mirroring rustc's @('Place'):
     e.g. @('(*_1).3') is local 1 with
     a dereference and then a field projection."))
  ((local acl2::nat)
   (projection proj-elem-list))
  :pred placep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-place
  :short "A place witness."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see irr-edition) for
     the purpose of these witnesses."))
  :type placep
  :body (make-place :local 0 :projection nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum const
  :short "Fixtype of constants."
  :long
  (xdoc::topstring
   (xdoc::p
    "The constant operands of the monomorphic scalar core:
     booleans, characters (by code point),
     integers of the signed and unsigned types
     (with mathematical-integer values;
     the well-formedness predicate, to come,
     requires the value to fit the type),
     the unit value,
     and function items
     (zero-sized values of @('ty-fn-def') type,
     which is how call terminators name their callees).
     Aggregate and by-reference constants
     will come with later subsets."))
  (:bool ((value acl2::bool)))
  (:char ((value acl2::nat)))
  (:int ((value acl2::int)
         (type int-type)))
  (:uint ((value acl2::nat)
          (type uint-type)))
  (:unit ())
  (:fn ((name acl2::string)))
  :pred constp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum operand
  :short "Fixtype of operands."
  :long
  (xdoc::topstring
   (xdoc::p
    "Mirrors rustc's @('Operand'):
     copy from a place, move from a place, or constant."))
  (:copy ((place place)))
  (:move ((place place)))
  (:constant ((const const)))
  :pred operandp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist operand-list
  :short "Fixtype of lists of operands."
  :elt-type operand
  :true-listp t
  :elementp-of-nil nil
  :pred operand-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum bin-op
  :short "Fixtype of binary operators."
  :long
  (xdoc::topstring
   (xdoc::p
    "Mirrors the core of rustc's @('BinOp').
     The @('...-with-overflow') operators return
     a pair of the wrapped result and an overflow flag;
     they are what overflow-checked arithmetic lowers to
     (an @('assert') terminator then checks the flag).
     The shift operators' right operand may have
     a different integer type than the left."))
  (:add ())
  (:sub ())
  (:mul ())
  (:div ())
  (:rem ())
  (:add-with-overflow ())
  (:sub-with-overflow ())
  (:mul-with-overflow ())
  (:bit-xor ())
  (:bit-and ())
  (:bit-or ())
  (:shl ())
  (:shr ())
  (:eq ())
  (:lt ())
  (:le ())
  (:ne ())
  (:ge ())
  (:gt ())
  :pred bin-opp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum un-op
  :short "Fixtype of unary operators."
  :long
  (xdoc::topstring
   (xdoc::p
    "Mirrors rustc's @('UnOp')
     (except @('PtrMetadata'), which comes with slices):
     logical/bitwise not, and arithmetic negation."))
  (:not ())
  (:neg ())
  :pred un-opp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum agg-kind
  :short "Fixtype of aggregate kinds."
  :long
  (xdoc::topstring
   (xdoc::p
    "Mirrors the core cases of rustc's @('AggregateKind'):
     tuples, arrays (with element type),
     and ADT values (by ADT name and variant index)."))
  (:tuple ())
  (:array ((elem ty)))
  (:adt ((name acl2::string)
         (variant acl2::nat)))
  :pred agg-kindp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum rvalue
  :short "Fixtype of rvalues."
  :long
  (xdoc::topstring
   (xdoc::p
    "Mirrors the core cases of rustc's @('Rvalue'):
     operand use, references to places,
     unary and binary operations,
     aggregate construction,
     and enum discriminant reads.
     Casts, pointer operations, and length reads
     will come with later subsets."))
  (:use ((operand operand)))
  (:ref ((mut mutability)
         (place place)))
  (:binary-op ((op bin-op)
               (left operand)
               (right operand)))
  (:unary-op ((op un-op)
              (operand operand)))
  (:aggregate ((kind agg-kind)
               (operands operand-list)))
  (:discriminant ((place place)))
  :pred rvaluep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum statement
  :short "Fixtype of statements."
  :long
  (xdoc::topstring
   (xdoc::p
    "Mirrors the core cases of rustc's @('StatementKind'):
     assignment of an rvalue to a place,
     storage liveness markers for locals,
     enum discriminant setting,
     and no-ops."))
  (:assign ((place place)
            (rvalue rvalue)))
  (:storage-live ((local acl2::nat)))
  (:storage-dead ((local acl2::nat)))
  (:set-discriminant ((place place)
                      (variant acl2::nat)))
  (:nop ())
  :pred statementp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist statement-list
  :short "Fixtype of lists of statements."
  :elt-type statement
  :true-listp t
  :elementp-of-nil nil
  :pred statement-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod switch-targets
  :short "Fixtype of switch targets."
  :long
  (xdoc::topstring
   (xdoc::p
    "Mirrors rustc's @('SwitchTargets'):
     a list of values with corresponding target blocks
     (the two lists have equal length;
     the well-formedness predicate, to come, requires that),
     and an otherwise block for all other values."))
  ((values acl2::integer-list)
   (targets acl2::nat-list)
   (otherwise acl2::nat))
  :pred switch-targetsp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum terminator
  :short "Fixtype of terminators."
  :long
  (xdoc::topstring
   (xdoc::p
    "Mirrors the core cases of rustc's @('TerminatorKind'),
     in panic=abort form (no unwind targets; see @(see mir-abstract-syntax)):")
   (xdoc::ul
    (xdoc::li
     "@(':goto'): jump to a block.")
    (xdoc::li
     "@(':switch-int'): multi-way branch on
      an integer/boolean/character operand.")
    (xdoc::li
     "@(':return'): return from the function;
      the return value is in local 0.")
    (xdoc::li
     "@(':call'): call the function that
      the @('func') operand evaluates to
      (a constant function item in the monomorphic core),
      with argument operands,
      writing the result to the destination place
      and continuing at the target block.")
    (xdoc::li
     "@(':assert'): evaluate the boolean condition;
      if it is not the expected value, abort (panic);
      otherwise continue at the target block.
      The structured panic messages of rustc's @('AssertKind')
      are elided in this draft.")
    (xdoc::li
     "@(':drop'): drop the value in the place
      (a no-op for the types of the current subset)
      and continue at the target block.")
    (xdoc::li
     "@(':unreachable'): undefined behavior if reached.")))
  (:goto ((target acl2::nat)))
  (:switch-int ((discr operand)
                (targets switch-targets)))
  (:return ())
  (:call ((func operand)
          (args operand-list)
          (dest place)
          (target acl2::nat)))
  (:assert ((cond operand)
            (expected acl2::bool)
            (target acl2::nat)))
  (:drop ((place place)
          (target acl2::nat)))
  (:unreachable ())
  :pred terminatorp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod basic-block
  :short "Fixtype of basic blocks."
  :long
  (xdoc::topstring
   (xdoc::p
    "Statements followed by a terminator,
     mirroring rustc's @('BasicBlockData')."))
  ((statements statement-list)
   (terminator terminator))
  :pred basic-blockp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist basic-block-list
  :short "Fixtype of lists of basic blocks."
  :elt-type basic-block
  :true-listp t
  :elementp-of-nil nil
  :pred basic-block-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod body
  :short "Fixtype of function bodies."
  :long
  (xdoc::topstring
   (xdoc::p
    "Mirrors rustc's @('Body'):
     the types of the locals
     (local 0 is the return place,
     locals 1 through @('arg-count') are the arguments,
     the rest are temporaries and user variables),
     the argument count,
     and the basic blocks
     (block 0 is the entry;
     blocks are referred to by index in terminators)."))
  ((locals ty-list)
   (arg-count acl2::nat)
   (blocks basic-block-list))
  :pred bodyp)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-body
  :short "A body witness."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see irr-edition) for
     the purpose of these witnesses."))
  :type bodyp
  :body (make-body :locals nil :arg-count 0 :blocks nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap fn-map
  :short "Fixtype of maps from function names to bodies."
  :key-type acl2::string
  :val-type body
  :pred fn-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap adt-map
  :short "Fixtype of maps from ADT names to ADT definitions."
  :key-type acl2::string
  :val-type adt-def
  :pred adt-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod mir-program
  :short "Fixtype of MIR programs."
  :long
  (xdoc::topstring
   (xdoc::p
    "A monomorphic MIR program:
     a table of function bodies and a table of ADT definitions,
     both keyed by name.
     (In rustc these are keyed by @('DefId');
     in the monomorphic core, fully qualified names suffice
     and are what the importer will produce.)"))
  ((funs fn-map)
   (adts adt-map))
  :pred mir-programp)
