; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST")

(include-book "../mir/abstract-syntax")
(include-book "charon-hashcons-expand")
(include-book "std/strings/decimal" :dir :system)

; These allow the definitions below to prove their internal theorems
; under the controlled configuration, as in the ../mir/ books.
(local (include-book "kestrel/arithmetic-light/fix" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/utilities/acl2-count" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))

; The ordinals book supplies the o-p facts for the -count measures
; under the controlled configuration, as in ../mir/values.lisp.
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

; These two rules loop with fty's equal-of-len reasoning
; (incrementing the constant forever), as in ../mir/interp.lisp;
; nothing in this book needs them.
(local (in-theory (disable acl2::equal-of-+-when-negative-constant
                           acl2::len-of-cdr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ullbc-to-mir-mapping
  :parents (mir-import)
  :short "Mapping from Charon's ULLBC JSON to the MIR abstract syntax."
  :long
  (xdoc::topstring
   (xdoc::p
    "The JSON input is produced by "
    (xdoc::ahref "https://github.com/AeneasVerif/charon" "Charon")
    ", a tool that runs a Rust crate through rustc and re-emits
     the result in its own intermediate representation.
     Charon has two such forms:
     LLBC (Low-Level Borrow Calculus),
     a structured form in which high-level control flow
     &mdash; loops and conditionals &mdash; has been reconstructed;
     and ULLBC (Unstructured LLBC),
     a control-flow-graph form of basic blocks and terminators
     that stays close to rustc's own MIR.
     We import the unstructured form &mdash; hence the name of this
     mapping &mdash; because its shape corresponds almost directly to
     our @(see mir-abstract-syntax)
     (which also fixes the modeled MIR dialect).
     Charon serializes ULLBC to JSON,
     and that JSON is the input here.")
   (xdoc::p
    "This mapping consumes that JSON,
     with the hashcons sharing already expanded
     (see @(see hashcons-expansion)),
     and produces a @(tsee mir-program):
     a table of function bodies keyed by name.")
   (xdoc::p
    "Names are normalized as the program is mapped.
     Functions local to the crate are keyed by their final identifier.
     Calls to standard library functions
     (whose bodies are not part of the input)
     are mapped onto the names of
     the interpreter's standard library shims:
     the input names callees by their declaration ids,
     and the declaration tables classify each id &mdash;
     by its defining impl's self type and trait &mdash;
     onto a shim name.
     Because the input is not monomorphized,
     a single generic declaration
     (such as the slice indexing operation)
     serves several shims;
     those are finalized at each call site
     from the call's generic arguments.
     Calls to functions that are neither in the program
     nor recognized shims are mapped with
     their full path as the name,
     so that reaching one stops the interpreter
     with that name visible.")
   (xdoc::p
    "Three input constructs are normalized to
     equivalent forms of the abstract syntax:
     a read whose place ends with a pointer-metadata projection
     becomes the pointer-metadata unary operation
     (which reads a slice reference's length);
     a reference or raw-pointer rvalue that reborrows
     a whole slice becomes a copy of the fat pointer itself;
     and a field projection that names an enum variant
     becomes a downcast projection followed by
     a field projection.")
   (xdoc::p
    "Following the deserializer precedents in the community books,
     each function returns @('(mv erp ...)'),
     where a non-@('nil') @('erp') describes the failure
     and the other results are irrelevant values."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-const
  :short "A constant witness."
  :type constp
  :body (const-unit))

(defirrelevant irr-operand
  :short "An operand witness."
  :type operandp
  :body (operand-constant (const-unit)))

(defirrelevant irr-rvalue
  :short "An rvalue witness."
  :type rvaluep
  :body (rvalue-use (operand-constant (const-unit))))

(defirrelevant irr-mir-program
  :short "A MIR program witness."
  :type mir-programp
  :body (make-mir-program :funs nil :adts nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; JSON navigation helpers.

(define jget ((x json::value-optionp) (name acl2::stringp))
  :returns (value? json::value-optionp)
  :short "The value of an object's member of a given name,
          or @('nil') if absent or not an object."
  :long
  (xdoc::topstring
   (xdoc::p
    "The navigation functions accept and return optional values,
     so that failed lookups compose without checks;
     the mappers check for @('nil') only where
     an absence changes what to do."))
  (b* ((x (json::value-option-fix x))
       ((unless x) nil)
       ((unless (json::value-case x :object)) nil))
    (jget-members (json::value-object->members x) name))
  :prepwork
  ((define jget-members ((members json::member-listp) (name acl2::stringp))
     :returns (value? json::value-optionp)
     (b* (((when (endp members)) nil)
          ((json::member member) (car members))
          ((when (equal member.name (acl2::str-fix name)))
           member.value))
       (jget-members (cdr members) name)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jelems ((x json::value-optionp))
  :returns (elems json::value-listp)
  :short "The elements of an array, or @('nil') if not an array."
  (b* ((x (json::value-option-fix x))
       ((unless x) nil))
    (if (json::value-case x :array)
        (json::value-array->elements x)
      nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm valuep-of-nth-when-value-listp
   (implies (and (json::value-listp l)
                 (< (acl2::nfix n) (len l)))
            (json::valuep (nth n l)))
   :hints (("Goal"
            :induct (nth n l)
            :in-theory (e/d (nth acl2::nfix) (acl2::nth-of-cdr))))))

(define jidx ((x json::value-optionp) (n acl2::natp))
  :returns (value? json::value-optionp)
  :short "The nth element of an array,
          or @('nil') if absent or not an array."
  (b* ((elems (jelems x))
       ((unless (< (acl2::nfix n) (len elems))) nil))
    (json::value-fix (nth n elems)))
  :hooks nil
  :guard-hints (("Goal" :in-theory (enable acl2::nfix jelems))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jstr ((x json::value-optionp))
  :returns (str? acl2::maybe-stringp)
  :short "The string of a string value, or @('nil')."
  (b* ((x (json::value-option-fix x))
       ((unless x) nil)
       ((unless (json::value-case x :string)) nil))
    (json::value-string->get x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jnat ((x json::value-optionp))
  :returns (nat? acl2::maybe-natp)
  :short "The natural number of a number value, or @('nil')."
  (b* ((x (json::value-option-fix x))
       ((unless x) nil)
       ((unless (json::value-case x :number)) nil)
       (n (json::value-number->get x))
       ((unless (natp n)) nil))
    n))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jtruep ((x json::value-optionp))
  :returns (yes/no booleanp)
  :short "Check if an optional value is the true value."
  (b* ((x (json::value-option-fix x)))
    (and x (json::value-case x :true))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define jkey1 ((x json::value-optionp))
  :returns (key? acl2::maybe-stringp)
  :short "The name of an object's single member, or @('nil')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The serializer encodes an enum variant with a payload as
     an object with the variant's name as its only member;
     this retrieves that name (mainly for error messages)."))
  (b* ((x (json::value-option-fix x))
       ((unless x) nil)
       ((unless (json::value-case x :object)) nil)
       (members (json::value-object->members x))
       ((unless (and (consp members)
                     (not (consp (cdr members)))))
        nil))
    (json::member->name (car members))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; The recursive mappers below recurse through jget/jidx/jelems,
; measuring by json::value-count; these lemmas make the navigation
; functions transparent to the measure proofs.

(local
 (defthm value-count-of-jget-members
   (implies (jget-members members name)
            (< (json::value-count (jget-members members name))
               (json::member-list-count members)))
   :rule-classes :linear
   :hints (("Goal"
            :induct (jget-members members name)
            :in-theory (enable jget-members)))))

(local
 (defthm value-count-of-jget
   (implies (jget x name)
            (< (json::value-count (jget x name))
               (json::value-count x)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable jget
                                      json::value-option-fix)))))

;; In branches that recurse on an empty list because
;; a member is absent, the count of the empty list computes away,
;; leaving no trigger for the lemma above;
;; this lower bound is keyed to the count of the object itself.
(local
 (defthm value-count-lower-bound-when-jget
   (implies (jget x name)
            (<= 2 (json::value-count x)))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance value-count-of-jget))))))

(local
 (defthm value-count-of-nth
   (<= (json::value-count (nth n l))
       (json::value-list-count l))
   :rule-classes :linear
   :hints (("Goal"
            :induct (nth n l)
            :in-theory (e/d (nth
                             json::value-list-count
                             json::value-count)
                            (acl2::nth-of-cdr))))))

(local
 (defthm value-list-count-of-jelems
   (<= (json::value-list-count (jelems x))
       (json::value-count x))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable jelems
                                      json::value-option-fix
                                      json::value-list-count)))))

(local
 (defthm value-count-of-jidx
   (implies (jidx x n)
            (< (json::value-count (jidx x n))
               (json::value-count x)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable jidx jelems)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Scalars and literal types.

(define json-to-uint-type ((s acl2::maybe-stringp))
  :returns (mv erp (type uint-typep))
  :short "Map a serialized unsigned integer type name."
  (b* ()
    (cond ((equal s "U8") (mv nil (uint-type-u8)))
          ((equal s "U16") (mv nil (uint-type-u16)))
          ((equal s "U32") (mv nil (uint-type-u32)))
          ((equal s "U64") (mv nil (uint-type-u64)))
          ((equal s "U128") (mv nil (uint-type-u128)))
          ((equal s "Usize") (mv nil (uint-type-usize)))
          (t (mv (list :bad-uint-type s) (uint-type-u8))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-to-int-type ((s acl2::maybe-stringp))
  :returns (mv erp (type int-typep))
  :short "Map a serialized signed integer type name."
  (b* ()
    (cond ((equal s "I8") (mv nil (int-type-i8)))
          ((equal s "I16") (mv nil (int-type-i16)))
          ((equal s "I32") (mv nil (int-type-i32)))
          ((equal s "I64") (mv nil (int-type-i64)))
          ((equal s "I128") (mv nil (int-type-i128)))
          ((equal s "Isize") (mv nil (int-type-isize)))
          (t (mv (list :bad-int-type s) (int-type-i8))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm character-listp-of-cdr-of-explode
   (character-listp (cdr (acl2::explode s)))
   :hints
   (("Goal"
     :use ((:instance acl2::character-listp-of-explode (acl2::x s)))
     :expand ((character-listp (acl2::explode s)))
     :in-theory (acl2::disable acl2::character-listp-of-explode)))))

(define decimal-string-to-int ((s acl2::stringp))
  :returns (mv erp (int acl2::integerp))
  :short "Parse a decimal integer string, possibly negative."
  :long
  (xdoc::topstring
   (xdoc::p
    "Scalar values are serialized as decimal strings,
     since they can exceed the range of JSON numbers."))
  (b* ((s (acl2::str-fix s))
       (chars (acl2::explode s))
       ((when (endp chars)) (mv (list :empty-scalar-string) 0))
       (negp (eql (car chars) #\-))
       (digits (if negp (acl2::implode (cdr chars)) s))
       (val (str::strval digits))
       ((unless val) (mv (list :bad-scalar-string s) 0)))
    (mv nil (if negp (- val) val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-scalar-to-const ((x json::value-optionp))
  :returns (mv erp (const constp))
  :short "Map a serialized integer scalar to an integer constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "A scalar is @('{\"Unsigned\": [width, value]}') or
     @('{\"Signed\": [width, value]}'),
     with the value as a decimal string."))
  (b* ((x (json::value-option-fix x))
       ((unless x) (mv (list :missing-scalar) (irr-const)))
       (unsigned (jget x "Unsigned"))
       ((when unsigned)
        (b* (((mv erp type) (json-to-uint-type (jstr (jidx unsigned 0))))
             ((when erp) (mv erp (irr-const)))
             (valstr (jstr (jidx unsigned 1)))
             ((unless valstr) (mv (list :bad-scalar-value) (irr-const)))
             ((mv erp val) (decimal-string-to-int valstr))
             ((when erp) (mv erp (irr-const)))
             ((unless (natp val))
              (mv (list :negative-unsigned-scalar val) (irr-const))))
          (mv nil (const-uint val type))))
       (signed (jget x "Signed"))
       ((when signed)
        (b* (((mv erp type) (json-to-int-type (jstr (jidx signed 0))))
             ((when erp) (mv erp (irr-const)))
             (valstr (jstr (jidx signed 1)))
             ((unless valstr) (mv (list :bad-scalar-value) (irr-const)))
             ((mv erp val) (decimal-string-to-int valstr))
             ((when erp) (mv erp (irr-const))))
          (mv nil (const-int val type)))))
    (mv (list :unsupported-scalar (jkey1 x)) (irr-const))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-const-to-nat ((x json::value-optionp))
  :returns (mv erp (nat acl2::natp))
  :short "Map a serialized constant known to be
          a nonnegative machine integer (e.g. an array length)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Accepts a full constant expression
     (an object with a @('\"kind\"') member),
     a constant-generic value (@('{\"Value\": literal}')),
     or a bare literal kind."))
  (b* ((x (json::value-option-fix x))
       ((unless x) (mv (list :missing-length-const) 0))
       (kind (or (jget x "kind")
                 (jget x "Value")
                 x))
       (lit (jget kind "Literal"))
       ((unless lit) (mv (list :non-literal-length) 0))
       (scalar (jget lit "Scalar"))
       ((mv erp const) (json-scalar-to-const scalar))
       ((when erp) (mv erp 0))
       ((unless (const-case const :uint))
        (mv (list :non-uint-length) 0)))
    (mv nil (const-uint->value const))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Names and declaration tables.

(define json-name-last-ident ((name json::value-optionp))
  :returns (mv erp (ident acl2::stringp))
  :short "The final identifier of a serialized item name."
  :long
  (xdoc::topstring
   (xdoc::p
    "An item name is an array of path elements;
     an identifier element is
     @('{\"Ident\": [string, disambiguator]}')."))
  (b* ((name (json::value-option-fix name))
       ((unless name) (mv (list :missing-name) ""))
       (elems (jelems name))
       ((unless (consp elems)) (mv (list :empty-name) ""))
       (last-elem (jidx name (1- (len elems))))
       ((unless last-elem) (mv (list :empty-name) ""))
       (ident (jget last-elem "Ident"))
       ((unless ident) (mv (list :non-ident-final-elem) ""))
       (s (jstr (jidx ident 0)))
       ((unless s) (mv (list :bad-ident) "")))
    (mv nil s))
  :guard-hints (("Goal" :in-theory (enable natp jelems))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-name-idents ((name json::value-optionp))
  :returns (idents acl2::string-listp)
  :short "The identifier strings of a serialized item name, in order,
          skipping non-identifier elements."
  (b* ((name (json::value-option-fix name))
       ((unless name) nil))
    (json-name-idents-elems (jelems name)))
  :prepwork
  ((define json-name-idents-elems ((elems json::value-listp))
     :returns (idents acl2::string-listp
                      :hints (("Goal"
                               :induct (json-name-idents-elems elems)
                               :in-theory (enable acl2::string-listp
                                                  jstr))))
     (b* (((when (endp elems)) nil)
          (ident (jget (json::value-fix (car elems)) "Ident"))
          (s (and ident (jstr (jidx ident 0))))
          (rest (json-name-idents-elems (cdr elems))))
       (if s (cons s rest) rest)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define join-idents ((idents acl2::string-listp))
  :returns (joined acl2::stringp)
  :short "Join identifiers with @('::') separators."
  (cond ((endp idents) "")
        ((endp (cdr idents)) (acl2::str-fix (car idents)))
        (t (acl2::string-append
            (acl2::str-fix (car idents))
            (acl2::string-append "::" (join-idents (cdr idents))))))
  :guard-hints (("Goal" :in-theory (enable acl2::string-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define qualify ((self acl2::stringp) (method acl2::stringp))
  :returns (name acl2::stringp)
  :short "Join a self-type name and a method name with @('::')."
  (acl2::string-append (acl2::str-fix self)
                       (acl2::string-append "::"
                                            (acl2::str-fix method))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap nat-string-map
  :short "Fixtype of maps from ids to strings."
  :key-type acl2::nat
  :val-type acl2::string
  :pred nat-string-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap nat-ty-map
  :short "Fixtype of maps from ids to types."
  :key-type acl2::nat
  :val-type ty
  :pred nat-ty-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum fun-class
  :short "Fixtype of function-declaration classifications."
  :long
  (xdoc::topstring
   (xdoc::p
    "Most declarations classify to a fixed name
     (a crate-local function's own identifier
     or a shim name).
     The generic declarations that serve several shims
     classify to a family,
     finalized at each call site from
     the call's generic arguments:
     slice/array indexing (by the index type),
     iterator conversion,
     and slice-to-array conversion."))
  (:name ((name acl2::string)))
  (:slice-index ((mutp acl2::bool)))
  (:into-iter ())
  (:try-into ())
  :pred fun-classp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap fun-class-map
  :short "Fixtype of maps from function ids to classifications."
  :key-type acl2::nat
  :val-type fun-class
  :pred fun-class-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod ictx
  :short "Fixtype of importer contexts."
  :long
  (xdoc::topstring
   (xdoc::p
    "The tables extracted from the declaration sections,
     consulted while mapping function bodies:
     ADT ids to their names,
     type-alias ids to their (already mapped) definitions,
     and function ids to their classifications."))
  ((adt-names nat-string-map)
   (alias-tys nat-ty-map)
   (fun-classes fun-class-map))
  :pred ictxp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Types.

(defines json-to-ty
  :ruler-extenders :all

  (define json-to-ty ((x json::valuep) (ictx ictxp))
    :returns (mv erp (ty ty-p))
    :parents (ullbc-to-mir-mapping)
    :short "Map a serialized type."
    :long
    (xdoc::topstring
     (xdoc::p
      "References to type aliases are resolved to
       their (already mapped) definitions,
       since the interpreter's value model is structural.
       Regions and trait references are erased."))
    :measure (json::value-count x)
    :hooks nil
    (b* ((lit (jget x "Literal"))
         ((when lit)
          (b* (((when (equal (jstr lit) "Bool")) (mv nil (ty-bool)))
               ((when (equal (jstr lit) "Char")) (mv nil (ty-char)))
               (uint (jget lit "UInt"))
               ((when uint)
                (b* (((mv erp type) (json-to-uint-type (jstr uint)))
                     ((when erp) (mv erp (irr-ty))))
                  (mv nil (ty-uint type))))
               (int (jget lit "Int"))
               ((when int)
                (b* (((mv erp type) (json-to-int-type (jstr int)))
                     ((when erp) (mv erp (irr-ty))))
                  (mv nil (ty-int type)))))
            (mv (list :unsupported-literal-ty (jkey1 lit)) (irr-ty))))
         (slice (jget x "Slice"))
         ((when slice)
          (b* (((mv erp elem) (json-to-ty slice ictx))
               ((when erp) (mv erp (irr-ty))))
            (mv nil (ty-slice elem))))
         (array (jget x "Array"))
         ((when array)
          (b* ((elem-json (jidx array 0))
               ((unless elem-json)
                (mv (list :missing-array-elem-ty) (irr-ty)))
               ((mv erp elem) (json-to-ty elem-json ictx))
               ((when erp) (mv erp (irr-ty)))
               ((mv erp len) (json-const-to-nat (jidx array 1)))
               ((when erp) (mv erp (irr-ty))))
            (mv nil (ty-array elem len))))
         (ref (jget x "Ref"))
         ((when ref)
          (b* ((ty-json (jidx ref 1))
               ((unless ty-json) (mv (list :missing-ref-ty) (irr-ty)))
               ((mv erp ty) (json-to-ty ty-json ictx))
               ((when erp) (mv erp (irr-ty)))
               (mut (if (equal (jstr (jidx ref 2)) "Mut")
                        (mutability-mut)
                      (mutability-not))))
            (mv nil (ty-ref mut ty))))
         (rawptr (jget x "RawPtr"))
         ((when rawptr)
          (b* ((ty-json (jidx rawptr 0))
               ((unless ty-json) (mv (list :missing-raw-ptr-ty) (irr-ty)))
               ((mv erp ty) (json-to-ty ty-json ictx))
               ((when erp) (mv erp (irr-ty)))
               (mut (if (equal (jstr (jidx rawptr 1)) "Mut")
                        (mutability-mut)
                      (mutability-not))))
            (mv nil (ty-raw-ptr mut ty))))
         (adt (jget x "Adt"))
         ((when adt)
          (b* ((id (jget adt "id"))
               (generics (jget adt "generics"))
               (gen-tys (and generics (jget generics "types")))
               ((when (equal (jstr id) "Tuple"))
                (b* (((mv erp tys)
                      (json-to-ty-list (if gen-tys (jelems gen-tys) nil)
                                       ictx))
                     ((when erp) (mv erp (irr-ty))))
                  (mv nil (ty-tuple tys))))
               (adt-id (and id (jnat (jget id "Adt"))))
               ((when adt-id)
                (b* ((alias (omap::assoc adt-id
                                         (ictx->alias-tys ictx)))
                     ((when alias) (mv nil (cdr alias)))
                     (name (omap::assoc adt-id
                                        (ictx->adt-names ictx)))
                     ((unless name)
                      (mv (list :unknown-adt-id adt-id) (irr-ty))))
                  (mv nil (ty-adt (cdr name)))))
               (builtin (and id (jstr (jget id "Builtin"))))
               (elem-json (and gen-tys (jidx gen-tys 0)))
               ((when (equal builtin "Slice"))
                (b* (((unless elem-json)
                      (mv (list :missing-slice-elem-ty) (irr-ty)))
                     ((mv erp elem) (json-to-ty elem-json ictx))
                     ((when erp) (mv erp (irr-ty))))
                  (mv nil (ty-slice elem))))
               ((when (equal builtin "Array"))
                (b* (((unless elem-json)
                      (mv (list :missing-array-elem-ty) (irr-ty)))
                     ((mv erp elem) (json-to-ty elem-json ictx))
                     ((when erp) (mv erp (irr-ty)))
                     ((mv erp len)
                      (json-const-to-nat
                       (jidx (jget generics "const_generics") 0)))
                     ((when erp) (mv erp (irr-ty))))
                  (mv nil (ty-array elem len)))))
            (mv (list :unsupported-adt-ty) (irr-ty)))))
      (mv (list :unsupported-ty (jkey1 (json::value-fix x))) (irr-ty))))

  (define json-to-ty-list ((xs json::value-listp) (ictx ictxp))
    :returns (mv erp (tys ty-listp))
    :parents (ullbc-to-mir-mapping)
    :short "Map a list of serialized types."
    :measure (json::value-list-count xs)
    :hooks nil
    (b* (((when (endp xs)) (mv nil nil))
         ((mv erp first) (json-to-ty (car xs) ictx))
         ((when erp) (mv erp nil))
         ((mv erp rest) (json-to-ty-list (cdr xs) ictx))
         ((when erp) (mv erp nil)))
      (mv nil (cons first rest))))

  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-literal-ty-to-ty ((x json::value-optionp))
  :returns (mv erp (ty ty-p))
  :short "Map a serialized literal (scalar) type."
  :long
  (xdoc::topstring
   (xdoc::p
    "Scalar cast kinds carry bare literal types
     (not wrapped in a full type)."))
  (b* ((x (json::value-option-fix x))
       ((unless x) (mv (list :missing-literal-ty) (irr-ty)))
       ((when (equal (jstr x) "Bool")) (mv nil (ty-bool)))
       ((when (equal (jstr x) "Char")) (mv nil (ty-char)))
       (uint (jget x "UInt"))
       ((when uint)
        (b* (((mv erp type) (json-to-uint-type (jstr uint)))
             ((when erp) (mv erp (irr-ty))))
          (mv nil (ty-uint type))))
       (int (jget x "Int"))
       ((when int)
        (b* (((mv erp type) (json-to-int-type (jstr int)))
             ((when erp) (mv erp (irr-ty))))
          (mv nil (ty-int type)))))
    (mv (list :unsupported-literal-ty (jkey1 x)) (irr-ty))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-ty-head ((x json::value-optionp) (ictx ictxp))
  :returns (head acl2::stringp)
  :short "A short name for a serialized type's head constructor,
          for classifying declarations and call sites."
  :long
  (xdoc::topstring
   (xdoc::p
    "Integer types map to their Rust names,
     slices and arrays to @('\"slice\"')
     (the shims view arrays through slice windows),
     named ADTs to their names,
     and anything else to @('\"*\"')."))
  (b* ((x (json::value-option-fix x))
       ((unless x) "*")
       (lit (jget x "Literal"))
       ((when lit)
        (b* ((uint (jstr (jget lit "UInt"))))
          (cond ((equal uint "U8") "u8")
                ((equal uint "U16") "u16")
                ((equal uint "U32") "u32")
                ((equal uint "U64") "u64")
                ((equal uint "U128") "u128")
                ((equal uint "Usize") "usize")
                (t "*"))))
       ((when (jget x "Slice")) "slice")
       ((when (jget x "Array")) "slice")
       (adt (jget x "Adt"))
       ((when adt)
        (b* ((id (jget adt "id"))
             (adt-id (and id (jnat (jget id "Adt"))))
             ((when adt-id)
              (b* ((name (omap::assoc adt-id (ictx->adt-names ictx))))
                (if name (cdr name) "*")))
             (builtin (and id (jstr (jget id "Builtin")))))
          (cond ((equal builtin "Slice") "slice")
                ((equal builtin "Array") "slice")
                (t "*")))))
    "*"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Constants and places.

(define json-to-const ((x json::value-optionp))
  :returns (mv erp (const constp))
  :short "Map a serialized constant expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "Integer scalars, booleans, and zero-field ADT values
     (unit-like constants) are supported;
     that is all the current inputs need."))
  (b* ((x (json::value-option-fix x))
       ((unless x) (mv (list :missing-const) (irr-const)))
       (kind (jget x "kind"))
       ((unless kind) (mv (list :missing-const-kind) (irr-const)))
       (lit (jget kind "Literal"))
       ((when lit)
        (b* ((scalar (jget lit "Scalar"))
             ((when scalar) (json-scalar-to-const scalar))
             (bool (jget lit "Bool"))
             ((when bool)
              (mv nil (const-bool (json::value-case bool :true)))))
          (mv (list :unsupported-literal-const (jkey1 lit)) (irr-const))))
       (adt (jget kind "Adt"))
       ((when adt)
        (b* ((fields (jidx adt 1))
             ((when (or (not fields)
                        (endp (jelems fields))))
              (mv nil (const-unit))))
          (mv (list :unsupported-adt-const) (irr-const)))))
    (mv (list :unsupported-const (jkey1 kind)) (irr-const))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm proj-elem-listp-of-append-when-both
   (implies (and (proj-elem-listp a)
                 (proj-elem-listp b))
            (proj-elem-listp (append a b)))
   :hints (("Goal"
            :induct (acl2::binary-append a b)
            :in-theory (enable acl2::binary-append
                               proj-elem-listp)))))

(define json-to-place ((x json::valuep))
  :returns (mv erp
               (place placep)
               (metadatap booleanp))
  :short "Map a serialized place."
  :long
  (xdoc::topstring
   (xdoc::p
    "The serialized form nests:
     a place is a local or a projection of a subplace
     by one element.
     This flattens it to a local with a projection list.
     A field projection whose kind names an enum variant
     becomes a downcast projection followed by
     a field projection.
     An index projection's index must be a plain local
     (as in rustc), and end-relative indexing is not supported.")
   (xdoc::p
    "A final pointer-metadata projection is stripped and
     reported through the @('metadatap') result instead;
     the callers that can accept one
     (an operand read) translate it to
     the pointer-metadata unary operation,
     and all other callers treat it as an error."))
  :measure (json::value-count x)
  :hooks nil
  (b* ((kind (jget x "kind"))
       ((unless kind) (mv (list :missing-place-kind) (irr-place) nil))
       (local (jnat (jget kind "Local")))
       ((when local)
        (mv nil (make-place :local local :projection nil) nil))
       (proj (jget kind "Projection"))
       ((unless proj) (mv (list :bad-place-kind (jkey1 kind))
                          (irr-place)
                          nil))
       (sub-json (jidx proj 0))
       ((unless sub-json) (mv (list :missing-subplace) (irr-place) nil))
       ((mv erp sub submeta) (json-to-place sub-json))
       ((when erp) (mv erp (irr-place) nil))
       ((when submeta)
        (mv (list :metadata-projection-not-final) (irr-place) nil))
       (elem (jidx proj 1))
       ((unless elem) (mv (list :missing-projection-elem) (irr-place) nil))
       ((when (equal (jstr elem) "Deref"))
        (mv nil
            (change-place sub
                          :projection (append (place->projection sub)
                                              (list (proj-elem-deref))))
            nil))
       ((when (equal (jstr elem) "PtrMetadata"))
        (mv nil sub t))
       (field (jget elem "Field"))
       ((when field)
        (b* ((fkind (jidx field 0))
             (fidx (jnat (jidx field 1)))
             ((unless fidx) (mv (list :bad-field-index) (irr-place) nil))
             (adt (and fkind (jget fkind "Adt")))
             (variant (and adt (jnat (jidx adt 1))))
             (new-elems (if variant
                            (list (proj-elem-downcast variant)
                                  (proj-elem-field fidx))
                          (list (proj-elem-field fidx)))))
          (mv nil
              (change-place sub
                            :projection (append (place->projection sub)
                                                new-elems))
              nil)))
       (index (jget elem "Index"))
       ((when index)
        (b* (((when (jtruep (jget index "from_end")))
              (mv (list :from-end-index) (irr-place) nil))
             (offset (jget index "offset"))
             (offset-place (and offset
                                (or (jget offset "Copy")
                                    (jget offset "Move"))))
             (offset-local (and offset-place
                                (jnat (jget (or (jget offset-place "kind")
                                                offset-place)
                                            "Local"))))
             ((unless offset-local)
              (mv (list :non-local-index-offset) (irr-place) nil)))
          (mv nil
              (change-place sub
                            :projection (append (place->projection sub)
                                                (list (proj-elem-index
                                                       offset-local))))
              nil))))
    (mv (list :unsupported-projection-elem (jkey1 elem))
        (irr-place)
        nil))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-to-place? ((x json::value-optionp))
  :returns (mv erp
               (place placep)
               (metadatap booleanp))
  :short "Map an optional serialized place."
  (b* ((x (json::value-option-fix x))
       ((unless x) (mv (list :missing-place) (irr-place) nil)))
    (json-to-place x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-to-operand ((x json::value-optionp))
  :returns (mv erp
               (operand operandp)
               (metadatap booleanp))
  :short "Map a serialized operand."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('metadatap') result reports a stripped final
     pointer-metadata projection, as in @(tsee json-to-place)."))
  (b* ((x (json::value-option-fix x))
       ((unless x) (mv (list :missing-operand) (irr-operand) nil))
       (copy (jget x "Copy"))
       ((when copy)
        (b* (((mv erp place metadatap) (json-to-place copy))
             ((when erp) (mv erp (irr-operand) nil)))
          (mv nil (operand-copy place) metadatap)))
       (move (jget x "Move"))
       ((when move)
        (b* (((mv erp place metadatap) (json-to-place move))
             ((when erp) (mv erp (irr-operand) nil)))
          (mv nil (operand-move place) metadatap)))
       (const (jget x "Const"))
       ((when const)
        (b* (((mv erp c) (json-to-const const))
             ((when erp) (mv erp (irr-operand) nil)))
          (mv nil (operand-constant c) nil))))
    (mv (list :unsupported-operand (jkey1 x)) (irr-operand) nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-to-operand-nometa ((x json::value-optionp))
  :returns (mv erp (operand operandp))
  :short "Map a serialized operand,
          rejecting pointer-metadata projections."
  (b* (((mv erp operand metadatap) (json-to-operand x))
       ((when erp) (mv erp (irr-operand)))
       ((when metadatap)
        (mv (list :unexpected-metadata-operand) (irr-operand))))
    (mv nil operand)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-to-operand-list ((xs json::value-listp))
  :returns (mv erp (operands operand-listp))
  :short "Map a list of serialized operands (no metadata reads)."
  (b* (((when (endp xs)) (mv nil nil))
       ((mv erp first)
        (json-to-operand-nometa (json::value-fix (car xs))))
       ((when erp) (mv erp nil))
       ((mv erp rest) (json-to-operand-list (cdr xs)))
       ((when erp) (mv erp nil)))
    (mv nil (cons first rest))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Rvalues.

(define json-to-bin-op ((x json::value-optionp))
  :returns (mv erp (op bin-opp))
  :short "Map a serialized binary operator."
  :long
  (xdoc::topstring
   (xdoc::p
    "The overflow-checked operators are their own variants.
     The operators parameterized by an overflow mode
     (wrapping, or undefined behavior on overflow &mdash;
     the latter always guarded by an explicit check in the input)
     map to the plain operators,
     whose semantics in the interpreter is wrapping."))
  (b* ((x (json::value-option-fix x))
       ((unless x) (mv (list :missing-bin-op) (bin-op-add)))
       (s (jstr x))
       ((when s)
        (cond ((equal s "BitXor") (mv nil (bin-op-bit-xor)))
              ((equal s "BitAnd") (mv nil (bin-op-bit-and)))
              ((equal s "BitOr") (mv nil (bin-op-bit-or)))
              ((equal s "Eq") (mv nil (bin-op-eq)))
              ((equal s "Ne") (mv nil (bin-op-ne)))
              ((equal s "Lt") (mv nil (bin-op-lt)))
              ((equal s "Le") (mv nil (bin-op-le)))
              ((equal s "Ge") (mv nil (bin-op-ge)))
              ((equal s "Gt") (mv nil (bin-op-gt)))
              ((equal s "AddChecked") (mv nil (bin-op-add-with-overflow)))
              ((equal s "SubChecked") (mv nil (bin-op-sub-with-overflow)))
              ((equal s "MulChecked") (mv nil (bin-op-mul-with-overflow)))
              (t (mv (list :unsupported-bin-op s) (bin-op-add)))))
       (key (jkey1 x)))
    (cond ((equal key "Add") (mv nil (bin-op-add)))
          ((equal key "Sub") (mv nil (bin-op-sub)))
          ((equal key "Mul") (mv nil (bin-op-mul)))
          ((equal key "Div") (mv nil (bin-op-div)))
          ((equal key "Rem") (mv nil (bin-op-rem)))
          ((equal key "Shl") (mv nil (bin-op-shl)))
          ((equal key "Shr") (mv nil (bin-op-shr)))
          (t (mv (list :unsupported-bin-op key) (bin-op-add))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-ref-mut ((x json::value-optionp))
  :returns (mut mutabilityp)
  :short "Map a serialized borrow or pointer kind to a mutability."
  (if (equal (jstr x) "Mut")
      (mutability-mut)
    (mutability-not)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-place-slicep ((x json::value-optionp))
  :returns (yes/no booleanp)
  :short "Check if a serialized place's recorded type is a slice."
  (b* ((x (json::value-option-fix x))
       ((unless x) nil)
       (ty (jget x "ty"))
       ((unless ty) nil)
       ((when (jget ty "Slice")) t)
       (adt (jget ty "Adt"))
       ((unless adt) nil)
       (id (jget adt "id")))
    (equal (jstr (and id (jget id "Builtin"))) "Slice")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-ref-to-rvalue ((x json::value-optionp) (mut mutabilityp))
  :returns (mv erp (rvalue rvaluep))
  :short "Map a serialized reference or raw-pointer rvalue."
  :long
  (xdoc::topstring
   (xdoc::p
    "A reborrow of a whole slice &mdash;
     the place is a bare dereference and
     its recorded type is a slice &mdash;
     becomes a copy of the fat pointer itself:
     the abstract syntax's reference rvalue produces
     a thin reference to an address,
     which cannot represent the slice window,
     while copying the reference value preserves it.
     Raw pointers are mapped as references
     (the modeled subset gives them the same semantics)."))
  (b* ((x (json::value-option-fix x))
       ((unless x) (mv (list :missing-ref) (irr-rvalue)))
       (place-json (jget x "place"))
       ((mv erp place metadatap) (json-to-place? place-json))
       ((when erp) (mv erp (irr-rvalue)))
       ((when metadatap)
        (mv (list :metadata-in-ref-place) (irr-rvalue)))
       ((place place) place)
       ((when (and (equal place.projection (list (proj-elem-deref)))
                   (json-place-slicep place-json)))
        (mv nil
            (rvalue-use (operand-copy (make-place :local place.local
                                                  :projection nil))))))
    (mv nil (rvalue-ref mut place))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-to-rvalue ((x json::value-optionp) (ictx ictxp))
  :returns (mv erp (rvalue rvaluep))
  :hooks nil
  :short "Map a serialized rvalue."
  (b* ((x (json::value-option-fix x))
       ((unless x) (mv (list :missing-rvalue) (irr-rvalue)))
       (use (jget x "Use"))
       ((when use)
        ;; {"Use": [operand, with-retag]}; the retag marker is
        ;; borrow-tracking bookkeeping with no runtime semantics
        (b* (((mv erp operand metadatap) (json-to-operand (jidx use 0)))
             ((when erp) (mv erp (irr-rvalue)))
             ((when metadatap)
              (mv nil (rvalue-unary-op (un-op-ptr-metadata) operand))))
          (mv nil (rvalue-use operand))))
       (binop (jget x "BinaryOp"))
       ((when binop)
        (b* (((mv erp op) (json-to-bin-op (jidx binop 0)))
             ((when erp) (mv erp (irr-rvalue)))
             ((mv erp left) (json-to-operand-nometa (jidx binop 1)))
             ((when erp) (mv erp (irr-rvalue)))
             ((mv erp right) (json-to-operand-nometa (jidx binop 2)))
             ((when erp) (mv erp (irr-rvalue))))
          (mv nil (rvalue-binary-op op left right))))
       (unop (jget x "UnaryOp"))
       ((when unop)
        (b* ((op (jidx unop 0))
             ((mv erp operand) (json-to-operand-nometa (jidx unop 1)))
             ((when erp) (mv erp (irr-rvalue)))
             ((when (equal (jstr op) "Not"))
              (mv nil (rvalue-unary-op (un-op-not) operand)))
             ((when (equal (jkey1 op) "Neg"))
              (mv nil (rvalue-unary-op (un-op-neg) operand)))
             (cast (and op (jget op "Cast")))
             ((unless cast)
              (mv (list :unsupported-un-op (jkey1 op)) (irr-rvalue)))
             (scalar (jget cast "Scalar"))
             ((when scalar)
              (b* (((mv erp ty) (json-literal-ty-to-ty (jidx scalar 1)))
                   ((when erp) (mv erp (irr-rvalue))))
                (mv nil (rvalue-cast (cast-kind-int-to-int) operand ty))))
             (unsize (jget cast "Unsize"))
             ((when unsize)
              (b* ((to-json (jidx unsize 1))
                   ((unless to-json)
                    (mv (list :missing-unsize-target) (irr-rvalue)))
                   ((mv erp ty) (json-to-ty to-json ictx))
                   ((when erp) (mv erp (irr-rvalue))))
                (mv nil (rvalue-cast (cast-kind-unsize) operand ty)))))
          (mv (list :unsupported-cast (jkey1 cast)) (irr-rvalue))))
       (agg (jget x "Aggregate"))
       ((when agg)
        (b* ((kind (jidx agg 0))
             (ops-json (jidx agg 1))
             ((mv erp operands)
              (json-to-operand-list (if ops-json (jelems ops-json) nil)))
             ((when erp) (mv erp (irr-rvalue)))
             (adt (and kind (jget kind "Adt")))
             ((unless adt)
              (mv (list :unsupported-aggregate-kind (jkey1 kind))
                  (irr-rvalue)))
             (tref (jidx adt 0))
             (id (and tref (jget tref "id")))
             (variant (jnat (jidx adt 1)))
             ((when (equal (jstr id) "Tuple"))
              (mv nil (rvalue-aggregate (agg-kind-tuple) operands)))
             (adt-id (and id (jnat (jget id "Adt"))))
             ((when adt-id)
              (b* ((name (omap::assoc adt-id (ictx->adt-names ictx)))
                   ((unless name)
                    (mv (list :unknown-adt-id adt-id) (irr-rvalue))))
                (mv nil
                    (rvalue-aggregate (agg-kind-adt (cdr name)
                                                    (or variant 0))
                                      operands))))
             ((unless (equal (jstr (and id (jget id "Builtin"))) "Array"))
              (mv (list :unsupported-aggregate-adt) (irr-rvalue)))
             (elem-json (jidx (jget (jget tref "generics") "types") 0))
             ((unless elem-json)
              (mv (list :missing-array-elem-ty) (irr-rvalue)))
             ((mv erp elem) (json-to-ty elem-json ictx))
             ((when erp) (mv erp (irr-rvalue))))
          (mv nil (rvalue-aggregate (agg-kind-array elem) operands))))
       (ref (jget x "Ref"))
       ((when ref)
        (json-ref-to-rvalue ref (json-ref-mut (jget ref "kind"))))
       (rawptr (jget x "RawPtr"))
       ((when rawptr)
        (json-ref-to-rvalue rawptr (json-ref-mut (jget rawptr "kind"))))
       (repeat (jget x "Repeat"))
       ((when repeat)
        (b* (((mv erp operand) (json-to-operand-nometa (jidx repeat 0)))
             ((when erp) (mv erp (irr-rvalue)))
             ((mv erp count) (json-const-to-nat (jidx repeat 2)))
             ((when erp) (mv erp (irr-rvalue))))
          (mv nil (rvalue-repeat operand count))))
       (discr (jget x "Discriminant"))
       ((when discr)
        (b* (((mv erp place metadatap) (json-to-place discr))
             ((when erp) (mv erp (irr-rvalue)))
             ((when metadatap)
              (mv (list :metadata-in-discriminant) (irr-rvalue))))
          (mv nil (rvalue-discriminant place)))))
    (mv (list :unsupported-rvalue (jkey1 x)) (irr-rvalue))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Statements and terminators.

(define json-to-statement ((x json::valuep) (ictx ictxp))
  :returns (mv erp (statement statementp))
  :hooks nil
  :short "Map a serialized statement."
  (b* ((kind (jget x "kind"))
       ((unless kind) (mv (list :missing-statement-kind) (statement-nop)))
       (live (jnat (jget kind "StorageLive")))
       ((when live) (mv nil (statement-storage-live live)))
       (dead (jnat (jget kind "StorageDead")))
       ((when dead) (mv nil (statement-storage-dead dead)))
       (assign (jget kind "Assign"))
       ((when assign)
        (b* (((mv erp place metadatap) (json-to-place? (jidx assign 0)))
             ((when erp) (mv erp (statement-nop)))
             ((when metadatap)
              (mv (list :metadata-assignment-target) (statement-nop)))
             ((mv erp rvalue) (json-to-rvalue (jidx assign 1) ictx))
             ((when erp) (mv erp (statement-nop))))
          (mv nil (statement-assign place rvalue)))))
    (mv (list :unsupported-statement (jkey1 kind)) (statement-nop))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-to-statement-list ((xs json::value-listp) (ictx ictxp))
  :returns (mv erp (statements statement-listp))
  :hooks nil
  :short "Map a list of serialized statements."
  (b* (((when (endp xs)) (mv nil nil))
       ((mv erp first)
        (json-to-statement (json::value-fix (car xs)) ictx))
       ((when erp) (mv erp nil))
       ((mv erp rest) (json-to-statement-list (cdr xs) ictx))
       ((when erp) (mv erp nil)))
    (mv nil (cons first rest))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-switch-values ((pairs json::value-listp))
  :returns (mv erp
               (values acl2::integer-listp)
               (targets acl2::nat-listp))
  :short "Map the value/target pairs of an integer switch."
  (b* (((when (endp pairs)) (mv nil nil nil))
       (pair (json::value-fix (car pairs)))
       (scalar (b* ((v (jidx pair 0))) (and v (jget v "Scalar"))))
       ((mv erp const) (json-scalar-to-const scalar))
       ((when erp) (mv erp nil nil))
       (value (const-case const
                          :uint (const-uint->value const)
                          :int (const-int->value const)
                          :otherwise nil))
       ((unless value) (mv (list :non-integer-switch-value) nil nil))
       (target (jnat (jidx pair 1)))
       ((unless target) (mv (list :bad-switch-target) nil nil))
       ((mv erp values targets) (json-switch-values (cdr pairs)))
       ((when erp) (mv erp nil nil)))
    (mv nil (cons value values) (cons target targets))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define find-index-head ((tys json::value-listp) (ictx ictxp))
  :returns (head acl2::stringp)
  :hooks nil
  :short "The first generic argument recognizable as an index type."
  (b* (((when (endp tys)) "*")
       (head (json-ty-head (json::value-fix (car tys)) ictx))
       ((when (member-equal head
                            (list "usize" "Range" "RangeTo" "RangeFrom")))
        head))
    (find-index-head (cdr tys) ictx)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define try-into-array4-p ((tys json::value-listp))
  :returns (yes/no booleanp)
  :short "Check that some generic argument is
          an array type of length 4."
  (b* (((when (endp tys)) nil)
       (ty (json::value-fix (car tys)))
       (array (jget ty "Array"))
       ((unless array) (try-into-array4-p (cdr tys)))
       ((mv erp len) (json-const-to-nat (jidx array 1))))
    (or (and (not erp) (equal len 4))
        (try-into-array4-p (cdr tys)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define finalize-callee ((class fun-classp)
                        (generics json::value-optionp)
                        (ictx ictxp))
  :returns (mv erp (name acl2::stringp))
  :hooks nil
  :short "Resolve a callee classification to a name,
          using the call site's generic arguments where needed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The indexing families pick the shim by the index type
     among the call's generic arguments.
     The iterator-conversion family maps to
     the (identity) iterator-conversion shim.
     The slice-to-array family requires the array length
     that the shim implements."))
  (b* ((class (fun-class-fix class))
       (generics (json::value-option-fix generics))
       (tys (b* ((v (and generics (jget generics "types"))))
              (if v (jelems v) nil))))
    (fun-class-case
     class
     :name (mv nil class.name)
     :slice-index
     (b* ((idx-head (find-index-head tys ictx))
          (base (cond ((equal idx-head "usize") "slice::index")
                      ((equal idx-head "Range") "slice::index_range")
                      ((equal idx-head "RangeTo") "slice::index_range_to")
                      ((equal idx-head "RangeFrom")
                       "slice::index_range_from")
                      (t nil)))
          ((unless base)
           (mv (list :unsupported-index-type idx-head) "")))
       (mv nil (if class.mutp
                   (acl2::string-append base "_mut")
                 base)))
     :into-iter (mv nil "Range::into_iter")
     :try-into
     (b* (((unless (try-into-array4-p tys))
           (mv (list :unsupported-try-into) "")))
       (mv nil "slice::try_into_array4")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-to-terminator ((x json::valuep) (ictx ictxp))
  :returns (mv erp (terminator terminatorp))
  :hooks nil
  :short "Map a serialized terminator."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unwind targets are dropped (the model is @('panic=abort')).
     An abort that names a panic becomes the abort terminator;
     an abort for undefined behavior,
     and the resume-unwinding terminator
     (which is reachable only along unwind edges),
     become the unreachable terminator."))
  (b* ((kind (jget x "kind"))
       ((unless kind)
        (mv (list :missing-terminator-kind) (terminator-return)))
       ((when (equal (jstr kind) "Return")) (mv nil (terminator-return)))
       ((when (equal (jstr kind) "UnwindResume"))
        (mv nil (terminator-unreachable)))
       (goto (jget kind "Goto"))
       ((when goto)
        (b* ((target (jnat (jget goto "target")))
             ((unless target) (mv (list :bad-goto-target)
                                  (terminator-return))))
          (mv nil (terminator-goto target))))
       (abort (jget kind "Abort"))
       ((when abort)
        (b* ((panic (jget abort "Panic"))
             ((when panic)
              (mv nil
                  (terminator-abort
                   (join-idents (json-name-idents panic))))))
          (mv nil (terminator-unreachable))))
       (switch (jget kind "Switch"))
       ((when switch)
        (b* (((mv erp discr)
              (json-to-operand-nometa (jget switch "discr")))
             ((when erp) (mv erp (terminator-return)))
             (targets (jget switch "targets"))
             ((unless targets)
              (mv (list :missing-switch-targets) (terminator-return)))
             (if-targets (jget targets "If"))
             ((when if-targets)
              (b* ((then-bb (jnat (jidx if-targets 0)))
                   (else-bb (jnat (jidx if-targets 1)))
                   ((unless (and then-bb else-bb))
                    (mv (list :bad-if-targets) (terminator-return))))
                (mv nil
                    (terminator-switch-int
                     discr
                     (make-switch-targets :values (list 0)
                                          :targets (list else-bb)
                                          :otherwise then-bb)))))
             (int-targets (jget targets "SwitchInt"))
             ((unless int-targets)
              (mv (list :bad-switch-targets (jkey1 targets))
                  (terminator-return)))
             (pairs-json (jidx int-targets 1))
             ((mv erp values bbs)
              (json-switch-values (if pairs-json (jelems pairs-json) nil)))
             ((when erp) (mv erp (terminator-return)))
             (otherwise (jnat (jidx int-targets 2)))
             ((unless otherwise)
              (mv (list :bad-switch-otherwise) (terminator-return))))
          (mv nil
              (terminator-switch-int
               discr
               (make-switch-targets :values values
                                    :targets bbs
                                    :otherwise otherwise)))))
       (assert (jget kind "Assert"))
       ((when assert)
        (b* ((inner (jget assert "assert"))
             ((unless inner)
              (mv (list :missing-assert) (terminator-return)))
             ((mv erp cond)
              (json-to-operand-nometa (jget inner "cond")))
             ((when erp) (mv erp (terminator-return)))
             (expected (jtruep (jget inner "expected")))
             (target (jnat (jget assert "target")))
             ((unless target)
              (mv (list :bad-assert-target) (terminator-return))))
          (mv nil (terminator-assert cond expected target))))
       (call (jget kind "Call"))
       ((when call)
        (b* ((inner (jget call "call"))
             ((unless inner)
              (mv (list :missing-call) (terminator-return)))
             (func (jget inner "func"))
             (regular (and func (jget func "Regular")))
             ((unless regular)
              (mv (list :unsupported-callee (jkey1 func))
                  (terminator-return)))
             (fun (b* ((k (jget regular "kind"))) (and k (jget k "Fun"))))
             (fun-id (and fun (jnat (jget fun "Regular"))))
             ((unless fun-id)
              (mv (list :unsupported-callee-kind) (terminator-return)))
             (class (omap::assoc fun-id (ictx->fun-classes ictx)))
             ((unless class)
              (mv (list :unknown-callee-id fun-id) (terminator-return)))
             ((mv erp name)
              (finalize-callee (cdr class) (jget regular "generics") ictx))
             ((when erp) (mv erp (terminator-return)))
             (args-json (jget inner "args"))
             ((mv erp args)
              (json-to-operand-list (if args-json (jelems args-json) nil)))
             ((when erp) (mv erp (terminator-return)))
             ((mv erp dest metadatap) (json-to-place? (jget inner "dest")))
             ((when erp) (mv erp (terminator-return)))
             ((when metadatap)
              (mv (list :metadata-call-dest) (terminator-return)))
             (target (jnat (jget call "target")))
             ((unless target)
              (mv (list :bad-call-target) (terminator-return))))
          (mv nil
              (terminator-call (operand-constant (const-fn name))
                               args
                               dest
                               target)))))
    (mv (list :unsupported-terminator (jkey1 kind)) (terminator-return))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Bodies.

(define json-to-basic-block ((x json::valuep) (ictx ictxp))
  :returns (mv erp (block basic-blockp))
  :hooks nil
  :short "Map a serialized basic block."
  (b* ((irr (make-basic-block :statements nil
                              :terminator (terminator-return)))
       (stmts-json (jget x "statements"))
       ((mv erp statements)
        (json-to-statement-list (if stmts-json (jelems stmts-json) nil)
                                ictx))
       ((when erp) (mv erp irr))
       (term-json (jget x "terminator"))
       ((unless term-json) (mv (list :missing-terminator) irr))
       ((mv erp terminator) (json-to-terminator term-json ictx))
       ((when erp) (mv erp irr)))
    (mv nil (make-basic-block :statements statements
                              :terminator terminator))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-to-basic-block-list ((xs json::value-listp) (ictx ictxp))
  :returns (mv erp (blocks basic-block-listp))
  :hooks nil
  :short "Map a list of serialized basic blocks."
  (b* (((when (endp xs)) (mv nil nil))
       ((mv erp first)
        (json-to-basic-block (json::value-fix (car xs)) ictx))
       ((when erp) (mv erp nil))
       ((mv erp rest) (json-to-basic-block-list (cdr xs) ictx))
       ((when erp) (mv erp nil)))
    (mv nil (cons first rest))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-to-local-tys ((xs json::value-listp) (ictx ictxp))
  :returns (mv erp (tys ty-listp))
  :hooks nil
  :short "Map the types of a serialized local-declaration list."
  (b* (((when (endp xs)) (mv nil nil))
       (local (json::value-fix (car xs)))
       (ty-json (jget local "ty"))
       ((unless ty-json) (mv (list :missing-local-ty) nil))
       ((mv erp ty) (json-to-ty ty-json ictx))
       ((when erp) (mv erp nil))
       ((mv erp rest) (json-to-local-tys (cdr xs) ictx))
       ((when erp) (mv erp nil)))
    (mv nil (cons ty rest))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-to-body ((x json::valuep) (ictx ictxp))
  :returns (mv erp (body bodyp))
  :hooks nil
  :short "Map a serialized unstructured function body."
  (b* ((unstructured (jget x "Unstructured"))
       ((unless unstructured)
        (mv (list :non-unstructured-body (jkey1 (json::value-fix x)))
            (irr-body)))
       (locals-obj (jget unstructured "locals"))
       ((unless locals-obj) (mv (list :missing-locals) (irr-body)))
       (arg-count (jnat (jget locals-obj "arg_count")))
       ((unless arg-count) (mv (list :missing-arg-count) (irr-body)))
       (locals-json (jget locals-obj "locals"))
       ((mv erp local-tys)
        (json-to-local-tys (if locals-json (jelems locals-json) nil)
                           ictx))
       ((when erp) (mv erp (irr-body)))
       (blocks-json (jget unstructured "body"))
       ((mv erp blocks)
        (json-to-basic-block-list (if blocks-json (jelems blocks-json) nil)
                                  ictx))
       ((when erp) (mv erp (irr-body))))
    (mv nil (make-body :locals local-tys
                       :arg-count arg-count
                       :blocks blocks))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Declaration-table construction.

(define json-type-decl-names ((decls json::value-listp)
                             (acc nat-string-mapp))
  :returns (names nat-string-mapp)
  :hooks nil
  :short "Map type-declaration ids to their final identifiers."
  (b* ((acc (nat-string-map-fix acc))
       ((when (endp decls)) acc)
       (d (json::value-fix (car decls)))
       (id (jnat (jget d "def_id")))
       ((unless id) (json-type-decl-names (cdr decls) acc))
       ((mv erp name) (json-name-last-ident (jget (b* ((m (jget d "item_meta")))
                                                    (or m d))
                                                  "name")))
       ((when erp) (json-type-decl-names (cdr decls) acc)))
    (json-type-decl-names (cdr decls) (omap::update id name acc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-type-decl-aliases ((decls json::value-listp)
                               (ictx ictxp)
                               (acc nat-ty-mapp))
  :returns (mv erp (aliases nat-ty-mapp))
  :hooks nil
  :short "Map type-alias declaration ids to their mapped definitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The context passed here carries the ADT names but no aliases,
     so an alias whose definition mentions another alias
     is not resolved (and is an error);
     the current inputs have no such aliases."))
  (b* ((acc (nat-ty-map-fix acc))
       ((when (endp decls)) (mv nil acc))
       (d (json::value-fix (car decls)))
       (id (jnat (jget d "def_id")))
       ((unless id) (json-type-decl-aliases (cdr decls) ictx acc))
       (kind (jget d "kind"))
       (alias (and kind (jget kind "Alias")))
       ((unless alias) (json-type-decl-aliases (cdr decls) ictx acc))
       ((mv erp ty) (json-to-ty alias ictx))
       ((when erp) (mv (list :bad-alias id erp) acc)))
    (json-type-decl-aliases (cdr decls) ictx (omap::update id ty acc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod trait-impl-info
  :short "Fixtype of trait-implementation summaries:
          the trait's name and the self type's head name."
  ((trait acl2::string)
   (self acl2::string))
  :pred trait-impl-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap trait-impl-map
  :short "Fixtype of maps from trait-implementation ids
          to their summaries."
  :key-type acl2::nat
  :val-type trait-impl-info
  :pred trait-impl-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-trait-impl-infos ((impls json::value-listp)
                              (trait-names nat-string-mapp)
                              (ictx ictxp)
                              (acc trait-impl-mapp))
  :returns (infos trait-impl-mapp)
  :hooks nil
  :short "Summarize the trait implementations:
          implemented trait and self type head."
  (b* ((acc (trait-impl-map-fix acc))
       (trait-names (nat-string-map-fix trait-names))
       ((when (endp impls)) acc)
       (d (json::value-fix (car impls)))
       (id (jnat (jget d "def_id")))
       ((unless id)
        (json-trait-impl-infos (cdr impls) trait-names ictx acc))
       (impl-trait (jget d "impl_trait"))
       ((unless impl-trait)
        (json-trait-impl-infos (cdr impls) trait-names ictx acc))
       (trait-id (jnat (jget impl-trait "id")))
       (trait-pair (and trait-id (omap::assoc trait-id trait-names)))
       (self (json-ty-head (b* ((g (jget impl-trait "generics"))
                                (tys (and g (jget g "types"))))
                             (and tys (jidx tys 0)))
                           ictx))
       (info (make-trait-impl-info :trait (if trait-pair
                                              (cdr trait-pair)
                                            "*")
                                   :self self)))
    (json-trait-impl-infos (cdr impls)
                           trait-names
                           ictx
                           (omap::update id info acc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define json-name-impl-info-elems ((elems json::value-listp)
                                  (trait-impls trait-impl-mapp)
                                  (ictx ictxp))
  :returns (mv (foundp booleanp)
               (trait acl2::stringp)
               (self acl2::stringp))
  :hooks nil
  :short "The trait and self-type head of the last impl element
          in a list of serialized path elements, if any."
  (b* (((when (endp elems)) (mv nil "" ""))
       ((mv foundp trait self)
        (json-name-impl-info-elems (cdr elems) trait-impls ictx))
       ((when foundp) (mv foundp trait self))
       (impl (jget (json::value-fix (car elems)) "Impl"))
       ((unless impl) (mv nil "" ""))
       (ty-impl (jget impl "Ty"))
       ((when ty-impl)
        (mv t "" (json-ty-head (jget ty-impl "skip_binder") ictx)))
       (trait-id (jnat (jget impl "Trait")))
       ((unless trait-id) (mv nil "" ""))
       (info (omap::assoc trait-id (trait-impl-map-fix trait-impls)))
       ((unless info) (mv nil "" "")))
    (mv t
        (trait-impl-info->trait (cdr info))
        (trait-impl-info->self (cdr info)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define classify-fun-decl ((d json::valuep)
                          (trait-impls trait-impl-mapp)
                          (ictx ictxp))
  :returns (mv erp (class fun-classp))
  :hooks nil
  :short "Classify one function declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "A crate-local function classifies to its own final identifier.
     A standard library declaration classifies by
     its defining impl's trait and self type and
     its method name, onto a shim name or a shim family;
     anything unrecognized classifies to its full path,
     which stops the interpreter with that name visible
     if it is ever called."))
  (b* ((meta (jget d "item_meta"))
       ((unless meta) (mv (list :missing-item-meta) (fun-class-name "")))
       (name (jget meta "name"))
       ((mv erp last) (json-name-last-ident name))
       ((when erp) (mv erp (fun-class-name "")))
       ((when (jtruep (jget meta "is_local")))
        (mv nil (fun-class-name last)))
       ((mv implp trait self)
        (json-name-impl-info-elems (if name (jelems name) nil)
                                   trait-impls
                                   ictx))
       ((when implp)
        (cond
         ;; an inherent impl (empty trait name):
         ;; the self type qualifies the method
         ((equal trait "")
          (mv nil (fun-class-name (qualify self last))))
         ((equal trait "Iterator")
          (mv nil (fun-class-name (qualify self last))))
         ((equal trait "DoubleEndedIterator")
          (mv nil (fun-class-name (qualify self last))))
         ((equal trait "IntoIterator")
          (mv nil (fun-class-into-iter)))
         ((equal trait "Index")
          (mv nil (fun-class-slice-index nil)))
         ((equal trait "IndexMut")
          (mv nil (fun-class-slice-index t)))
         ((equal trait "TryInto")
          (mv nil (fun-class-try-into)))
         ((equal trait "BitXorAssign")
          (mv nil (fun-class-name (qualify self last))))
         (t
          (mv nil
              (fun-class-name (join-idents (json-name-idents name)))))))
       (idents (json-name-idents name))
       ;; a trait method named through the trait itself,
       ;; e.g. Iterator::rev
       ((when (member-equal "Iterator" idents))
        (mv nil (fun-class-name (qualify "Iterator" last)))))
    (mv nil (fun-class-name (join-idents idents)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define classify-fun-decls ((decls json::value-listp)
                           (trait-impls trait-impl-mapp)
                           (ictx ictxp)
                           (acc fun-class-mapp))
  :returns (mv erp (classes fun-class-mapp))
  :hooks nil
  :short "Classify the function declarations."
  (b* ((acc (fun-class-map-fix acc))
       ((when (endp decls)) (mv nil acc))
       (d (json::value-fix (car decls)))
       (id (jnat (jget d "def_id")))
       ((unless id) (classify-fun-decls (cdr decls) trait-impls ictx acc))
       ((mv erp class) (classify-fun-decl d trait-impls ictx))
       ((when erp) (mv (list :bad-fun-decl id erp) acc)))
    (classify-fun-decls (cdr decls)
                        trait-impls
                        ictx
                        (omap::update id class acc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Whole-crate mapping.

(define json-to-fn-map ((decls json::value-listp) (ictx ictxp))
  :returns (mv erp (funs fn-mapp))
  :hooks nil
  :verify-guards :after-returns
  :short "Map the crate-local function declarations to
          the program's function table."
  (b* (((when (endp decls)) (mv nil nil))
       (d (json::value-fix (car decls)))
       ((mv erp rest) (json-to-fn-map (cdr decls) ictx))
       ((when erp) (mv erp nil))
       (meta (jget d "item_meta"))
       ((unless (and meta (jtruep (jget meta "is_local")))) (mv nil rest))
       (body-json (jget d "body"))
       ((unless body-json) (mv nil rest))
       ((mv erp name) (json-name-last-ident (jget meta "name")))
       ((when erp) (mv erp nil))
       ((mv erp body) (json-to-body body-json ictx))
       ((when erp) (mv (list :bad-body name erp) nil)))
    (mv nil (omap::update name body rest))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ullbc-translated-to-mir ((translated json::valuep))
  :returns (mv erp (program mir-programp))
  :hooks nil
  :short "Map a serialized translated crate to a MIR program."
  :long
  (xdoc::topstring
   (xdoc::p
    "The declaration tables are built first
     (ADT names, resolved type aliases,
     trait-implementation summaries,
     function classifications),
     then the crate-local function bodies are mapped.
     The ADT table of the resulting program is left empty:
     the interpreter's dynamic semantics does not consult it
     (enum values carry their variant indices)."))
  (b* ((type-decls (b* ((v (jget translated "type_decls")))
                     (if v (jelems v) nil)))
       (adt-names (json-type-decl-names type-decls nil))
       (ictx0 (make-ictx :adt-names adt-names
                         :alias-tys nil
                         :fun-classes nil))
       ((mv erp alias-tys)
        (json-type-decl-aliases type-decls ictx0 nil))
       ((when erp) (mv erp (irr-mir-program)))
       (ictx1 (change-ictx ictx0 :alias-tys alias-tys))
       (trait-names
        (json-type-decl-names
         (b* ((v (jget translated "trait_decls")))
           (if v (jelems v) nil))
         nil))
       (trait-impls
        (json-trait-impl-infos
         (b* ((v (jget translated "trait_impls")))
           (if v (jelems v) nil))
         trait-names
         ictx1
         nil))
       (fun-decls (b* ((v (jget translated "fun_decls")))
                    (if v (jelems v) nil)))
       ((mv erp fun-classes)
        (classify-fun-decls fun-decls trait-impls ictx1 nil))
       ((when erp) (mv erp (irr-mir-program)))
       (ictx (change-ictx ictx1 :fun-classes fun-classes))
       ((mv erp funs) (json-to-fn-map fun-decls ictx))
       ((when erp) (mv erp (irr-mir-program))))
    (mv nil (make-mir-program :funs funs :adts nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ullbc-to-mir ((envelope json::valuep))
  :returns (mv erp (program mir-programp))
  :hooks nil
  :short "Map a serialized crate envelope to a MIR program."
  :long
  (xdoc::topstring
   (xdoc::p
    "The envelope records the serializer's version,
     whether extraction reported errors,
     and the translated crate.
     The hashcons sharing is expanded here
     (see @(see hashcons-expansion)),
     so the envelope can be passed directly as parsed."))
  (b* (((when (jtruep (jget envelope "has_errors")))
        (mv (list :input-has-errors) (irr-mir-program)))
       ((mv erp expanded) (hc-expand envelope))
       ((when erp) (mv erp (irr-mir-program)))
       (translated (jget expanded "translated"))
       ((unless translated)
        (mv (list :missing-translated) (irr-mir-program))))
    (ullbc-translated-to-mir translated)))
