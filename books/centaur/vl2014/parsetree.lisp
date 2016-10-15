; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL2014")
(include-book "expr")
(include-book "util/commentmap")
(include-book "util/warnings")
(include-book "tools/flag" :dir :system)
(include-book "tools/templates" :dir :system)
(local (include-book "util/arithmetic"))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable double-containment)))
(local (in-theory (disable vl-atts-p-of-cdr-when-vl-atts-p
                           vl-atts-p-when-subsetp-equal
                           alistp-when-vl-atts-p-rewrite
                           default-car default-cdr
                           acl2::lower-bound-of-car-when-nat-listp
                           stringp-when-true-listp
                           acl2::consp-when-member-equal-of-cons-listp
                           acl2::consp-when-member-equal-of-atom-listp
                           consp-when-member-equal-of-vl-commentmap-p
                           consp-when-member-equal-of-vl-atts-p
                           (tau-system))))

; ----------------------------------------------------------------------------
;
;                            BIG WARNING MESSAGE
;
;     If you modify the any actual parse-tree syntax,
;
;                               then you should update the syntax version!
;
; ----------------------------------------------------------------------------

(defval *vl-current-syntax-version*
  :parents (vl-syntaxversion-p)
  :short "Version of VL syntax being used."

  :long "<p>This is a barbaric mechanism to make sure that we don't try to mix
together translations produced by different versions of VL.  Each design is
annotated with a @('version') field that must match exactly this string.</p>"

  ;; Current syntax version: generally a string like
  ;; "VL Syntax [date of modification]"
  "VL2014 Syntax 2016-02-05")

(define vl-syntaxversion-p (x)
  :parents (syntax)
  (equal x *vl-current-syntax-version*))

(define vl-syntaxversion-fix (x)
  :parents (vl-syntaxversion-p)
  :returns (version vl-syntaxversion-p)
  (if (vl-syntaxversion-p x)
      x
    *vl-current-syntax-version*)
  ///
  (defthm vl-syntaxversion-fix-when-vl-syntaxversion-p
    (implies (vl-syntaxversion-p x)
             (equal (vl-syntaxversion-fix x) x))))

(deffixtype vl-syntaxversion
  :pred vl-syntaxversion-p
  :fix vl-syntaxversion-fix
  :equiv vl-syntaxversion-equiv
  :define t
  :forward t)



(defxdoc syntax
  :parents (vl2014)
  :short "Representation of Verilog structures."

  :long "<p>We now describe our representation of Verilog's syntactic
structures.  For each kind of Verilog construct (expressions, statements,
declarations, instances, etc.) we introduce recognizer, constructor, and
accessor functions that enforce certain basic well-formedness criteria.</p>

<p>These structures correspond fairly closely to parse trees in the Verilog
grammar, although we make many simplifcations and generally present a much more
regular view of the source code.</p>")

(local (xdoc::set-default-parents syntax))

;; (defoption maybe-string stringp :pred acl2::maybe-stringp$inline
;;   ;; BOZO misplaced, also has documentation issues
;;   :parents nil
;;   :fix maybe-string-fix
;;   :equiv maybe-string-equiv)

(define maybe-string-fix ((x maybe-stringp))
  :returns (xx maybe-stringp)
  :hooks nil
  (mbe :logic (and x (str-fix x))
       :exec x)
  ///
  (defthm maybe-string-fix-when-maybe-stringp
    (implies (maybe-stringp x)
             (equal (maybe-string-fix x) x)))

  (defthm maybe-string-fix-under-iff
    (iff (maybe-string-fix x) x))

  (fty::deffixtype maybe-string :pred maybe-stringp :fix maybe-string-fix
    :equiv maybe-string-equiv :define t :forward t)

  (defrefinement maybe-string-equiv streqv
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable streqv))))))

(defprod vl-range
  :short "Representation of ranges on wire declarations, instance array
declarations, and so forth."
  :tag :vl-range
  :layout :tree

  ((msb vl-expr-p)
   (lsb vl-expr-p))

  :long "<p>Ranges are discussed in Section 7.1.5.</p>

<p>Ranges in declarations and array instances look like @('[msb:lsb]'), but do
not confuse them with part-select expressions which have the same syntax.</p>

<p>The expressions in the @('msb') and @('lsb') positions are expected to
resolve to constants.  Note that the parser does not try to simplify these
expressions, but some simplification is performed in transformations such as
@(see rangeresolve) and @(see unparameterization).</p>

<p>Even after the expressions have become constants, the Verilog-2005 standard
does not require @('msb') to be greater than @('lsb'), and neither index is
required to be zero.  In fact, even negative indicies seem to be permitted,
which is quite amazing and strange.</p>

<p>While we do not impose any restrictions in @('vl-range-p') itself, some
transformations expect the indices to be resolved to integers.  However, we now
try to support the use of both ascending and descending ranges.</p>")

(defoption vl-maybe-range vl-range-p
  :parents (syntax vl-range-p)
  ///
  (defthm type-when-vl-maybe-range-p
    (implies (vl-maybe-range-p x)
             (or (consp x)
                 (not x)))
    :hints(("Goal" :in-theory (enable vl-maybe-range-p)))
    :rule-classes :compound-recognizer))

(fty::deflist vl-maybe-range-list
              :elt-type vl-maybe-range-p
              :elementp-of-nil t
              :true-listp nil)

(fty::deflist vl-rangelist
              :elt-type vl-range-p
              :elementp-of-nil nil
              :true-listp nil)

(fty::deflist vl-rangelist-list
              :elt-type vl-rangelist-p
              :true-listp nil
              :elementp-of-nil t)





; -----------------------------------------------------------------------------
;
;                        Data Types (SystemVerilog)
;
; -----------------------------------------------------------------------------

(defenum vl-randomqualifier-p
  (nil
   :vl-rand
   :vl-randc)
  :short "Random qualifiers that can be put on struct or union members.")

(defenum vl-nettypename-p
  (:vl-wire ;; Most common so it goes first.
   :vl-tri
   :vl-supply0
   :vl-supply1
   :vl-triand
   :vl-trior
   :vl-tri0
   :vl-tri1
   :vl-trireg
   :vl-uwire
   :vl-wand
   :vl-wor)
  :short "Representation of wire types."

  :long "<p>Wires in Verilog can be given certain types.  We
represent these types using certain keyword symbols, whose names
correspond to the possible types.</p>")

(defoption vl-maybe-nettypename vl-nettypename-p)

(defenum vl-coretypename-p
  (;; integer vector types, i put these first since they're common
   :vl-logic
   :vl-reg
   :vl-bit
   ;; integer atom types:
   :vl-byte
   :vl-shortint
   :vl-int
   :vl-longint
   :vl-integer
   :vl-time
   ;; non integer types:
   :vl-shortreal
   :vl-real
   :vl-realtime
   ;; misc core data types
   :vl-string
   :vl-chandle
   :vl-event
   ;; it's convenient to include void here even though it's not part
   ;; of the grammar for data_type
   :vl-void
   )
  :short "Basic kinds of data types."
  :long "<p>Our <i>core types</i> basically correspond to the following small
subset of the valid @('data_type')s:</p>

@({
     data_type_or_void ::= data_type | 'void'
     data_type ::=
         integer_vector_type [signing] { packed_dimension }
       | integer_atom_type [signing]
       | non_integer_type
       | 'string'
       | 'chandle'
       | 'event'
       | <non core types >
})

<p>We include @('void') here only because it's convenient to do so.</p>")



(define vl-packeddimension-p (x)
  :short "Recognizes ranges and unsized dimensions."
  :long "<p>From the SystemVerilog-2012 grammar:</p>
@({
    unsized_dimension ::= '[' ']'
    packed_dimension ::= '[' constant_range ']' | unsized_dimension
})"

  (or (eq x :vl-unsized-dimension)
      (vl-range-p x))
  ///
  (defthm vl-packeddimension-p-when-vl-range-p
    (implies (vl-range-p x)
             (vl-packeddimension-p x)))
  (defthm vl-range-p-when-vl-packeddimension-p
    (implies (and (not (equal x :vl-unsized-dimension))
                  (vl-packeddimension-p x))
             (vl-range-p x))))

(define vl-packeddimension-fix ((x vl-packeddimension-p))
  :returns (x-fix vl-packeddimension-p)
  :inline t
  (mbe :logic (if (vl-packeddimension-p x)
                  x
                (vl-range-fix x))
       :exec x)
  :prepwork ((local (in-theory (enable vl-packeddimension-p))))
  ///
  (defthm vl-packeddimension-fix-when-vl-packeddimension-p
    (implies (vl-packeddimension-p x)
             (equal (vl-packeddimension-fix x)
                    x))))

(deffixtype vl-packeddimension
  :pred vl-packeddimension-p
  :fix vl-packeddimension-fix
  :equiv vl-packeddimension-equiv
  :define t
  :forward t)

(fty::deflist vl-packeddimensionlist
  :elt-type vl-packeddimension
  :elementp-of-nil nil)

(defoption vl-maybe-packeddimension vl-packeddimension-p)

(xdoc::defpointer vl-packeddimension vl-packeddimension-p)


(define vl-enumbasekind-p (x)
  :parents (vl-enumbasetype-p)
  :short "Kinds of base types for enums."
  :long "<p>The SystemVerilog-2012 rules for @('enum_base_type') are:</p>

@({
      enum_base_type ::=
          integer_atom_type   [signing]
        | integer_vector_type [signing] [packed_dimension]
        | type_identifier               [packed_dimension]
})

<p>A @('vl-enumbasetag-p') corresponds to the main part of this, i.e., it is
either:</p>

<ul>
 <li>A string, corresponding to the name of the @('type_identifier')</li>
 <li>A symbol like @(':vl-byte'), corresponding to an @('integer_atom_type'), or</li>
 <li>A symbol like @(':vl-logic'), corresponding to an @('integer_vector_type').</li>
</ul>

<p>Per Section 6.19, the default type is @('int').</p>"

  (or (stringp x)
      ;; integer atom types
      (eq x :vl-byte)
      (eq x :vl-shortint)
      (eq x :vl-int)
      (eq x :vl-longint)
      (eq x :vl-integer)
      (eq x :vl-time)
      ;; integer vector types
      (eq x :vl-bit)
      (eq x :vl-logic)
      (eq x :vl-reg)))

(define vl-enumbasekind-fix ((x vl-enumbasekind-p))
  :returns (x-fix vl-enumbasekind-p)
  :inline t
  (mbe :logic (if (vl-enumbasekind-p x)
                  x
                :vl-logic)
       :exec x)
  ///
  (defthm vl-enumbasekind-fix-when-vl-enumbasekind-p
    (implies (vl-enumbasekind-p x)
             (equal (vl-enumbasekind-fix x)
                    x))))

(deffixtype vl-enumbasekind
  :pred vl-enumbasekind-p
  :fix vl-enumbasekind-fix
  :equiv vl-enumbasekind-equiv
  :define t
  :forward t)

(defprod vl-enumbasetype
  :tag :vl-enumbasetype
  :layout :tree
  :short "The base types for SystemVerilog enumerations."
  ((kind    vl-enumbasekind-p)
   (signedp booleanp :rule-classes :type-prescription)
   (dim     vl-maybe-packeddimension-p))

  :long "<p>The base type for an enumeration is given by the following
SystemVerilog grammar rule:</p>

@({
      enum_base_type ::=
          integer_atom_type [signing]
        | integer_vector_type [signing] [packed_dimension]
        | type_identifier [packed_dimension]
})

<p>The main part of this (integer_atom_type, integer_vector_type, or
type_identifier) is captured by the <b>kind</b> field.</p>

<p>The <b>signedp</b> field isn't sensible for @('type_identifiers') but we
include it for uniformity.  For the other kinds of enums, it captures whether
the @('signed') keyword was mentioned.  or @('unsigned') keywords were
mentioned.</p>

<p>The optional dimension, if applicable.  BOZO we don't currently support
unsized dimensions.</p>")

(defprod vl-enumitem
  :tag :vl-enumitem
  :layout :tree
  :short "A single member of an @('enum')."
  ;; enum_name_declaration ::=
  ;;   enum_identifier [ [ integral_number [ : integral_number ] ] ] [ = constant_expression ]
  ((name  stringp           :rule-classes :type-prescription)
   (range vl-maybe-range-p)
   (value vl-maybe-expr-p)))

(fty::deflist vl-enumitemlist
  :elt-type vl-enumitem-p
  :elementp-of-nil nil)


;    variable_dimension ::= unsized_dimension
;                         | unpacked_dimension
;                         | associative_dimension
;                         | queue_dimension
;
;    unsized_dimension ::= '[' ']'
;
;    unpacked_dimension ::= '[' constant_range ']'
;                         | '[' constant_expression ']'
;
;    associative_dimension ::= '[' data_type ']'
;                            | '[' '*' ']'
;
;    queue_dimension ::= '[' '$' [ ':' constant_expression ] ']'

(deftypes data-types

; BOZO it's a little unfortunate to have to put these measures in here.
; Without these measures, in the case where a STRUCTMEMBER is an atom, the
; fixing function just recurs on (cadr x) and so on without ever checking
; consp, so we just need to rig things up so that structmember can always recur
; to datatype.  It'd be nice if that were more automatic.

  (deftagsum vl-datatype
    :measure (two-nats-measure (acl2-count x) 0)
    (:vl-coretype
     :layout :tree
     :base-name vl-coretype
     :short "Representation of basic SystemVerilog data types like @('integer')
             and @('string'), and also @('void')."

     ((name    vl-coretypename-p
               "Kind of primitive data type, e.g., @('byte'), @('string'),
                etc.")

      (signedp booleanp :rule-classes :type-prescription
               "Only valid for integer types, indicates whether the integer
                type is signed or not.")

      (pdims    vl-packeddimensionlist-p
               "Only valid for integer vector types (bit, logic, reg).  If present
                these are for an 'packed' array dimensions, i.e., the [7:0] part
                of a declaration like @('bit [7:0] memory [255:0]').  There can be
                arbitrarily many of these.")

      (udims   vl-packeddimensionlist-p
               "Unpacked array dimensions.")))

    (:vl-struct
     :layout :tree
     :base-name vl-struct
     :short "Representation of SystemVerilog structs."
     ;; data_type ::= ... | struct_union [ 'packed' [signing] ] '{'
     ;;                       struct_union_member { struct_union_member }
     ;;                     '}' { packed_dimension }
     ((packedp booleanp :rule-classes :type-prescription)
      (signedp booleanp :rule-classes :type-prescription)
      (members vl-structmemberlist-p)
      (pdims    vl-packeddimensionlist-p)
      (udims    vl-packeddimensionlist-p)))

    (:vl-union
     :layout :tree
     :base-name vl-union
     :short "Representation of SystemVerilog unions."
     ;; data_type ::= ... | struct_union [ 'packed' [signing] ] '{'
     ;;                       struct_union_member { struct_union_member }
     ;;                     '}' { packed_dimension }
     ((packedp booleanp :rule-classes :type-prescription)
      (signedp booleanp :rule-classes :type-prescription)
      (taggedp booleanp :rule-classes :type-prescription)
      (members vl-structmemberlist-p)
      (pdims    vl-packeddimensionlist-p)
      (udims    vl-packeddimensionlist-p)))

    (:vl-enum
     :layout :tree
     :base-name vl-enum
     :short "Representation of SystemVerilog enumerations."
     ;; data_type ::= ... | 'enum' [ enum_base_type ] '{'
     ;;                        enum_name_declaration { ',' enum_name_declaration }
     ;;                     '}' { packed_dimension }
     ((basetype vl-enumbasetype)
      (items    vl-enumitemlist-p)
      (pdims    vl-packeddimensionlist-p)
      (udims    vl-packeddimensionlist-p)))

    (:vl-usertype
     :layout :tree
     :base-name vl-usertype
     ;; data_type ::= ... | [ class_scope | package_scope ] type_identifier { packed_dimension }
     ((kind vl-expr-p "Kind of this type, should be an identifier or some
                       kind of scoped/hierarchical identifier.")
      (pdims    vl-packeddimensionlist-p)
      (udims    vl-packeddimensionlist-p)))


    ;;  BOZO not yet implemented:
    ;;
    ;; data_type ::= ...
    ;;  | 'virtual' [ 'interface' ] interface_identifier [ parameter_value_assignment ] [ '.' modport_identifier ]
    ;;  | class_type
    ;;  | type_reference
    )

  (fty::deflist vl-structmemberlist
    :measure (two-nats-measure (acl2-count x) 0)
    :elt-type vl-structmember
    :elementp-of-nil nil)

  (defprod vl-structmember
    :measure (two-nats-measure (acl2-count x) 1)
    :count vl-structmember-count
    :tag :vl-structmember
    :layout :tree
    :short "A single member of a struct or union."
    ;;   struct_union_member ::=  { attribute_instance } [random_qualifier]
    ;;                            data_type_or_void
    ;;                            list_of_variable_decl_assignments ';'
    ((atts vl-atts-p)
     (rand vl-randomqualifier-p)
     (type vl-datatype-p)
     ;; now we want a single variable_decl_assignment
     (name stringp :rule-classes :type-prescription)
     (rhs  vl-maybe-expr-p)
     )
    :long "<p>Currently our structure members are very limited.  In the long
run we may want to support more of the SystemVerilog grammar.  It allows a list
of variable declaration assignments, which can have fancy dimensions and
different kinds of @('new') operators.</p>

<p>Notes for the future:</p>

@({
   variable_decl_assignment ::=
         variable_identifier { variable_dimension } [ '=' expression ]
       | dynamic_array_variable_identifier unsized_dimension { variable_dimension } [ '=' dynamic_array_new ]
       | class_variable_identifier [ '=' class_new ]
})

<p>These fancy _identifiers are all just identifiers.  So really this is:</p>

@({
     variable_decl_assignment ::=
         identifier { variable_dimension }                   [ '=' expression ]
       | identifier unsized_dimension { variable_dimension } [ '=' dynamic_array_new ]
       | identifier                                          [ '=' class_new ]
})

<p>The @('new') keyword can occur in a variety of places.  One of these is
related to defining constructors for classes, e.g., in class constructor
prototypes/declarations we can have things like</p>

@({
     function ... new (...) ...
})

<p>And @('super.new(...)') and so on.  But for now let's think of these as
separate cases; that is, our approach to @('new') in other contexts doesn't
necessarily need to have anything to do with these constructors, which we might
instead handle more explicitly.</p>

<p>The other places where @('new') can occur are in:</p>

@({
    dynamic_array_new ::= new '[' expression ']' [ '(' expression ')' ]

    class_new ::= [ class_scope ] 'new' [ '(' list_of_arguments ')' ]
                | 'new' expression
})

<p>Which in turn can occur in blocking assignments:</p>

@({
         [some fancy lhs] = dynamic_array_new
      or [some other fancy lhs] = class_new
      or other things not involving new
})

<p>(Which is interesting because we also have to support a lot of other new
kinds of assignments like @('+=') and @('*='), so maybe this could become a
@('new=') kind of assignment or something.)</p>

<p>And they can also occur in variable decl assignments:</p>

@({
          simple id [ = expression ]
      or  some fancy lhs with some various dimensions [= dynamic_array_new]
      or  some simple lhs [= class_new]
})

<p>Which can occur in:</p>

<ul>
<li>SVA assertion variable declarations</li>
<li>Data declarations (e.g., top-level @('const suchandso = new ...')</li>
<li>Structure members in structs and unions.</li>
</ul>

<p>So maybe we don't so much need these to be expressions.  Maybe we can get
away with them as alternate kinds of assignments.</p>"))

(define vl-datatype->pdims ((x vl-datatype-p))
  :returns (pdims vl-packeddimensionlist-p)
  (vl-datatype-case x
    :vl-coretype x.pdims
    :vl-struct x.pdims
    :vl-union x.pdims
    :vl-enum x.pdims
    :vl-usertype x.pdims))

(define vl-datatype->udims ((x vl-datatype-p))
  :returns (udims vl-packeddimensionlist-p)
  (vl-datatype-case x
    :vl-coretype x.udims
    :vl-struct x.udims
    :vl-union x.udims
    :vl-enum x.udims
    :vl-usertype x.udims))

(define vl-datatype-update-dims ((pdims vl-packeddimensionlist-p)
                                 (udims vl-packeddimensionlist-p)
                                 (x vl-datatype-p))
  :returns (newx (and (vl-datatype-p newx)
                      (eq (vl-datatype-kind newx) (vl-datatype-kind x))))
  (vl-datatype-case x
    :vl-coretype (change-vl-coretype x :pdims pdims :udims udims)
    :vl-struct   (change-vl-struct   x :pdims pdims :udims udims)
    :vl-union    (change-vl-union    x :pdims pdims :udims udims)
    :vl-enum     (change-vl-enum     x :pdims pdims :udims udims)
    :vl-usertype (change-vl-usertype x :pdims pdims :udims udims))
  ///
  (defthm vl-datatype-update-dims-of-own
    (equal (vl-datatype-update-dims (vl-datatype->pdims x)
                                    (vl-datatype->udims x)
                                    x)
           (vl-datatype-fix x))
    :hints(("Goal" :in-theory (enable vl-datatype->udims
                                      vl-datatype->pdims))))

  (defthm vl-datatype->pdims-of-vl-datatype-update-dims
    (equal (vl-datatype->pdims (vl-datatype-update-dims pdims udims x))
           (vl-packeddimensionlist-fix pdims))
    :hints(("Goal" :in-theory (enable vl-datatype->pdims))))

  (defthm vl-datatype->udims-of-vl-datatype-update-dims
    (equal (vl-datatype->udims (vl-datatype-update-dims pdims udims x))
           (vl-packeddimensionlist-fix udims))
    :hints(("Goal" :in-theory (enable vl-datatype->udims)))))

(define vl-datatype-update-pdims ((pdims vl-packeddimensionlist-p) (x vl-datatype-p))
  :enabled t
  :prepwork ((local (in-theory (enable vl-datatype-update-dims vl-datatype->udims))))
  :returns (newx (and (vl-datatype-p newx)
                      (eq (vl-datatype-kind newx) (vl-datatype-kind x))))
  (mbe :logic (vl-datatype-update-dims pdims (vl-datatype->udims x) x)
       :exec  (vl-datatype-case x
                  :vl-coretype (change-vl-coretype x :pdims pdims)
                  :vl-struct (change-vl-struct x :pdims pdims)
                  :vl-union (change-vl-union x :pdims pdims)
                  :vl-enum (change-vl-enum x :pdims pdims)
                  :vl-usertype (change-vl-usertype x :pdims pdims))))

(define vl-datatype-update-udims ((udims vl-packeddimensionlist-p) (x vl-datatype-p))
  :enabled t
  :prepwork ((local (in-theory (enable vl-datatype-update-dims vl-datatype->pdims))))
  :returns (newx (and (vl-datatype-p newx)
                      (eq (vl-datatype-kind newx) (vl-datatype-kind x))))
  (mbe :logic (vl-datatype-update-dims (vl-datatype->pdims x) udims x)
       :exec  (vl-datatype-case x
                  :vl-coretype (change-vl-coretype x :udims udims)
                  :vl-struct (change-vl-struct x :udims udims)
                  :vl-union (change-vl-union x :udims udims)
                  :vl-enum (change-vl-enum x :udims udims)
                  :vl-usertype (change-vl-usertype x :udims udims))))


(defoption vl-maybe-datatype vl-datatype-p)


(defval *vl-plain-old-integer-type*
  :parents (vl-datatype)
  (hons-copy (make-vl-coretype :name    :vl-integer
                               :signedp t   ;; integer type is signed
                               :pdims    nil ;; Not applicable to integers
                               )))

(defval *vl-plain-old-real-type*
  :parents (vl-datatype)
  (hons-copy (make-vl-coretype :name    :vl-real
                               :signedp nil ;; Not applicable to reals
                               :pdims    nil ;; Not applicable to reals
                               )))

(defval *vl-plain-old-time-type*
  :parents (vl-datatype)
  (hons-copy (make-vl-coretype :name    :vl-time
                               :signedp nil ;; Not applicable to times
                               :pdims    nil ;; Not applicable to times
                               )))

(defval *vl-plain-old-realtime-type*
  :parents (vl-datatype)
  (hons-copy (make-vl-coretype :name    :vl-realtime
                               :signedp nil ;; Not applicable to realtimes
                               :pdims    nil ;; Not applicable to realtimes
                               )))

(defval *vl-plain-old-wire-type*
  :parents (vl-datatype)
  (hons-copy (make-vl-coretype :name    :vl-logic
                               :signedp nil
                               :pdims   nil)))

(defval *vl-plain-old-reg-type*
  :parents (vl-datatype)
  (hons-copy (make-vl-coretype :name    :vl-reg
                               :signedp nil
                               :pdims    nil)))


(defprod vl-interfaceport
  :parents (vl-port)
  :short "Representation of a single interface port."
  :tag :vl-interfaceport
  :layout :tree
  ((name stringp
         :rule-classes :type-prescription
         "Name (internal and external) of this interface port, e.g., @('foo')
          for @('simplebus.master foo').")

   (ifname stringp
           :rule-classes :type-prescription
           "For interface ports like @('simplebus foo') or @('simplebus.master foo'),
            this is the name of the interface, e.g., @('simplebus').  For
            non-interface ports it is just @('nil').")

   (modport maybe-stringp
            :rule-classes :type-prescription
            "For interface ports with modport components, e.g., @('simplebus.master foo'),
             this is the name of the modport being used, e.g., @('master').
             For plain interfaces like @('simplebus foo') or non-interface
             ports, this is just @('nil').")

   (udims   vl-packeddimensionlist-p
            "For interface ports only: the unpacked dimensions for this port.")

   (loc  vl-location-p
         "Where this port came from in the Verilog source code.")))

(defprod vl-regularport
  :parents (vl-port)
  :short "Representation of a single non-interface port."
  :tag :vl-regularport
  :layout :tree

  ((name maybe-stringp
         :rule-classes :type-prescription
         "The \"externally visible\" name of this port, for use in named module
          instances.  Usually it is best to avoid this; see below.")

   (expr vl-maybe-expr-p
         "How the port is wired internally within the module.  Most of the time,
          this is a simple identifier expression that is just @('name').  But
          it can also be more complex; see below.  The expression should be
          @('nil') for interface ports.")

   (loc  vl-location-p
         "Where this port came from in the Verilog source code."))

  :long "<p>In Verilog-2005, ports are described in Section 12.3 of the
standard.</p>

<p>It is important to understand the difference between ports and port
declarations.  We represent ports as @('vl-port') structures, whereas port
declarations re represented as @(see vl-portdecl) structures.  It is easy to
see the difference between ports and port declarations when modules are
declared using the \"non-ANSI\" syntax.</p>

@({
module mod(a,b,c) ;  <-- ports

  input [3:0] a;     <-- port declarations (not ports)
  input b;
  output c;

endmodule
})

<p>It is less easy to see this difference when the more concise \"ANSI\" syntax
is used:</p>

@({
module mod(
  input [3:0] a;   <-- ports and port declarations, mixed together
  input b;
  output c;
) ;
   ...
endmodule
})

<p>Regardless of which syntax is used, VL internally creates both ports and
portdecls as separate structures.</p>

<p>In most designs, there is a single port corresponding to each port
declaration.  However, in general Verilog permits more complex ports.  Here is
an example of a module where the ports have external names that are distinct
from their internal wiring.</p>

@({
module mod (a, .b(w), c[3:0], .d(c[7:4])) ;
  input a;
  input w;
  input [7:0] c;
  ...
endmodule
})

<p>In this example, the @('name')s of these ports would be, respectively:
@('\"a\"'), @('\"b\"'), @('nil') (because the third port has no externally
visible name), and @('\"d\"').  Meanwhile, the first two ports are internally
wired to @('a') and @('w'), respectively, while the third and fourth ports
collectively specify the bits of @('c').</p>

<p>SystemVerilog-2012 extends ports in several ways, but most of these
extensions (e.g., support for fancy data types) are related to the port
declarations rather than the ports.  One place where the ports themselves
<i>are</i> extended is for interface ports.  See @(see vl-port).</p>")

(deftranssum vl-port
  (vl-regularport
   vl-interfaceport)
  :short "Representation of a single port."
  :long "<p>Most ports are regular ports, see @(see vl-regularport).  However,
SystemVerilog also adds interface ports, see @(see vl-interfaceport).</p>

<p>It is generally best to <b>avoid using port names</b> except perhaps for
things like error messages.  Why?  As shown above, some ports might not have
names, and even when a port does have a name, it does not necessarily
correspond to any wires in the module.  Since these cases are exotic, code that
is based on port names is likely to work for simple test cases, but then fail
later when more complex examples are encountered!</p>

<p>Usually you should not need to deal with port names.  The @(see argresolve)
transform converts module instances that use named arguments into their plain
equivalents, and once this has been done there really isn't much reason to have
port names anymore.  Instead, you can work directly with the port's
expression.</p>

<p>Our @('vl-port-p') structures do not restrict the kinds of expressions that
may be used as the internal wiring, but we generally expect that each such
expression should satisfy @(see vl-portexpr-p).</p>

<p>A \"blank\" port expression (represented by @('nil')) means the port is not
connected to any wires within the module.  Our @(see argresolve) transform will
issue non-fatal @(see warnings) if any non-blank arguments are connected to
blank ports, or if blank arguments are connected to non-blank ports.  It is
usually not hard to support blank ports in other transformations.</p>

<p>The direction of a port can most safely be obtained by @(see
vl-port-direction).  Note that directions are not particularly reliable in
Verilog: one can assign to a input or read from an output, and in simulators
like Cadence this can actually impact values on wires in the supermodule as if
the ports have no buffers.  We call this \"backflow.\" <b>BOZO</b> eventually
implement a comprehensive approach to detecting and dealing with backflow.</p>

<p>The width of a port can be determined after expression sizing has been
performed by examining the width of the port expression.  See @(see
expression-sizing) for details.</p>")

(fty::deflist vl-portlist
              :elt-type vl-port-p
              :true-listp nil
              :elementp-of-nil nil)

(fty::deflist vl-interfaceportlist
              :elt-type vl-interfaceport-p
              :true-listp nil
              :elementp-of-nil nil)

(fty::deflist vl-regularportlist
  :elt-type vl-regularport
  :true-listp nil
  :elementp-of-nil nil)

(defthm vl-portlist-p-when-vl-interfaceportlist-p
  (implies (vl-interfaceportlist-p x)
           (vl-portlist-p x))
  :hints(("Goal" :induct (len x))))

(defthm vl-portlist-p-when-vl-regularportlist-p
  (implies (vl-regularportlist-p x)
           (vl-portlist-p x))
  :hints(("Goal" :induct (len x))))

(define vl-port->name ((x vl-port-p))
  :returns (name maybe-stringp :rule-classes :type-prescription)
  (b* ((x (vl-port-fix x)))
    (case (tag x)
      (:vl-regularport   (vl-regularport->name x))
      (:vl-interfaceport (vl-interfaceport->name x))
      (otherwise         (impossible)))))

(define vl-port->loc ((x vl-port-p))
  :returns (loc vl-location-p)
  (b* ((x (vl-port-fix x)))
    (case (tag x)
      (:vl-regularport   (vl-regularport->loc x))
      (:vl-interfaceport (vl-interfaceport->loc x))
      (otherwise         (progn$ (impossible) *vl-fakeloc*)))))

(defprojection vl-portlist->names ((x vl-portlist-p))
  :parents (vl-portlist-p)
  ;; [Jared] no longer true due to new transsum implementation, but probably
  ;; not really a very good idea in the first place.
  ;; :nil-preservingp t
  (vl-port->name x)
  ///
  (defthm string-listp-of-vl-portlist->names
    (equal (string-listp (vl-portlist->names x))
           (not (member nil (vl-portlist->names x)))))

  (defthm string-listp-of-remove-equal-of-vl-portlist->names
    (string-listp (remove-equal nil (vl-portlist->names x)))))

(define vl-collect-interface-ports-exec ((x vl-portlist-p) nrev)
  :parents (vl-collect-interface-ports)
  (b* (((when (atom x))
        (nrev-fix nrev))
       (x1 (vl-port-fix (car x)))
       ((when (eq (tag x1) :vl-interfaceport))
        (b* ((nrev (nrev-push x1 nrev)))
          (vl-collect-interface-ports-exec (cdr x) nrev))))
    (vl-collect-interface-ports-exec (cdr x) nrev)))

(define vl-collect-interface-ports
  :parents (vl-portlist-p)
  :short "Filter a @(see vl-portlist-p) to collect only the interface ports."
  ((x vl-portlist-p))
  :returns (ifports (and (vl-portlist-p ifports)
                         (vl-interfaceportlist-p ifports)))
  :verify-guards nil
  (mbe :logic
       (b* (((when (atom x))
             nil)
            (x1 (vl-port-fix (car x)))
            ((when (eq (tag x1) :vl-interfaceport))
             (cons x1 (vl-collect-interface-ports (cdr x)))))
         (vl-collect-interface-ports (cdr x)))
       :exec
       (with-local-nrev
         (vl-collect-interface-ports-exec x nrev)))
  ///
  (defthm vl-collect-interface-ports-exec-removal
    (equal (vl-collect-interface-ports-exec x nrev)
           (append nrev (vl-collect-interface-ports x)))
    :hints(("Goal" :in-theory (enable vl-collect-interface-ports-exec))))

  (verify-guards vl-collect-interface-ports)

  (defthm vl-collect-interface-ports-when-atom
    (implies (atom x)
             (equal (vl-collect-interface-ports x)
                    nil)))

  (defthm vl-collect-interface-ports-of-cons
    (equal (vl-collect-interface-ports (cons a x))
           (if (eq (tag (vl-port-fix a)) :vl-interfaceport)
               (cons (vl-port-fix a)
                     (vl-collect-interface-ports x))
             (vl-collect-interface-ports x)))))


(defenum vl-direction-p (:vl-input :vl-output :vl-inout)
  :short "Direction for a port declaration (input, output, or inout)."

  :long "<p>Each port declaration (see @(see vl-portdecl-p)) includes a
direction to indicate that the port is either an input, output, or inout.  We
represent these directions with the keyword @(':vl-input'), @(':vl-output'),
and @(':vl-inout'), respectively.</p>

<p>In our @(see argresolve) transformation, directions are also assigned to all
arguments of gate instances and most arguments of module instances.  See our
@(see vl-plainarg-p) structures for more information.</p>")

(defoption vl-maybe-direction vl-direction-p
  ///
  (defthm type-when-vl-maybe-direction-p
    (implies (vl-direction-p x)
             (and (symbolp x)
                  (not (equal x t))))
    :rule-classes :compound-recognizer))


(defprod vl-portdecl
  :short "Representation of Verilog port declarations."
  :tag :vl-portdecl
  :layout :tree

  ((name     stringp
             :rule-classes :type-prescription
             "An ordinary string that should agree with some identifier used in
              the \"internal\" wiring expressions from some port(s) in the
              module.")

   (dir      vl-direction-p
             "Says whether this port is an input, output, or bidirectional
              (inout) port.")

   (nettype  vl-maybe-nettypename-p)

   (type     vl-datatype-p
             "The type and size information for this port.  <b>Warning</b>: per
              Verilog-2005 page 175, port declarations and net/reg declarations
              must be checked against one another: if either declaration
              includes the @('signed') keyword, then both are to be considered
              signed.  The @(see loader) DOES NOT do this cross-referencing
              automatically; instead the @(see portdecl-sign) transformation
              needs to be run.  See also @(see
              vl-portdecl-and-moduleitem-compatible-p) which is part of our
              notion of @(see reasonable) modules.")

   (atts     vl-atts-p
             "Any attributes associated with this declaration.")

   (loc      vl-location-p
             "Where the port was declared in the source code."))

  :long "<p>See @(see vl-port) for related background.  Port declarations,
described in Section 12.3.3 of the Verilog-2005 standard, ascribe certain
properties (direction, signedness, size, and so on) to the ports of a module.
Here is an example:</p>

@({
module m(a, b) ;
  input [3:0] a ;  // <--- port declaration
  ...
endmodule
})

<p>Although Verilog allows multiple ports to be declared simultaneously, i.e.,
@('input w1, w2;'), our parser splits these merged declarations to create
separate @('vl-portdecl-p') objects for each port.  Because of this, every
@('vl-portdecl-p') has only a single name.</p>

<p>Most of the time, e.g., for @('a') in module @('m') above, the resulting
@(see vl-module) will have:</p>

<ul>
<li>A @(see vl-port) for @('a'),</li>
<li>A corresponding @(see vl-portdecl) that has the direction/type information, and</li>
<li>A corresponding @(see vl-vardecl) that looks like an ordinary variable.</li>
</ul>

<p>The exceptions to this are:</p>

<ul>
<li>Interface ports have no corresponding port/vardecl.</li>
<li>The ports/portdecls do not necessarily line up when complex ports are used,
see @(see vl-port) for details.</li>
</ul>")

(fty::deflist vl-portdecllist
              :elt-type vl-portdecl-p
              :true-listp nil
              :elementp-of-nil nil)


(defprod vl-gatedelay
  :short "Representation of delay expressions."
  :tag :vl-gatedelay
  :layout :tree

  ((rise vl-expr-p "Rising delay.")
   (fall vl-expr-p "Falling delay.")
   (high vl-maybe-expr-p "High-impedence delay or charge decay time." ))

  :long "<p><b>WARNING</b>.  We have not paid much attention to delays, and our
transformations probably do not handle them properly.</p>

<p>Delays are mainly discussed in 7.14 and 5.3, with some other discussion in
6.13 and the earlier parts of Section 7.  In short:</p>

<ul>
<li>A \"delay expression\" can be an arbitrary expression.  Of particular note,
    mintypmax expression such as 1:2:3 mean \"the delay is at least 1, usually
    2, and at most 3.\"</li>

<li>Up to three delay expressions are associated with each gate.  These are,
    in order,
      <ol>
        <li>a \"rise delay\",</li>
        <li>a \"fall delay\", and</li>
        <li>for regular gates, a \"high impedence\" delay; <br/>
            for triregs, a \"charge decay time\" delay</li>
      </ol></li>
</ul>

<p>The parser does not attempt to determine (3) in some cases, so it may be
left as @('nil').  Simulators that care about this will need to carefully
review the rules for correctly computing these delays.</p>")

(defoption vl-maybe-gatedelay vl-gatedelay-p
  ///
  (defthm type-when-vl-maybe-gatedelay-p
    (implies (vl-maybe-gatedelay-p x)
             (or (not x)
                 (consp x)))
    :hints(("Goal" :in-theory (enable vl-maybe-gatedelay-p)))
    :rule-classes :compound-recognizer))

(defenum vl-dstrength-p
  (:vl-supply
   :vl-strong
   :vl-pull
   :vl-weak
   :vl-highz)
  :parents (vl-gatestrength-p)
  :short "Representation of a drive strength for @(see vl-gatestrength-p)
objects."
  :long "<p>We represent Verilog's drive strengths with the keyword symbols
recognized by @(call vl-dstrength-p).</p>

<p>BOZO add references to the Verilog-2005 standard, description of what these
are.</p>")

(defprod vl-gatestrength
  :short "Representation of strengths for a assignment statements, gate
instances, and module instances."
  :tag :vl-gatestrength
  :layout :tree

  ((zero vl-dstrength-p "Drive strength toward logical zero.")
   (one  vl-dstrength-p "Drive strength toward logical one."))

  :long "<p><b>WARNING</b>.  We have not paid much attention to strengths, and
our transformations probably do not handle them properly.</p>

<p>See sections 7.1.2 and 7.9 of the Verilog-2005 standard for discussion of
strength modelling.  Every regular gate has, associated with it, two drive
strengths; a \"strength0\" which says how strong its output is when it is a
logical zero, and \"strength1\" which says how strong the output is when it is
a logical one.  Strengths also seem to be used on assignments and module
instances.</p>

<p>There seem to be some various rules for default strengths in 7.1.2, and also
in 7.13.  But our parser does not try to implement these defaults, and we only
associate strengths onto module items where they are explicitly
specified.</p>")

(defoption vl-maybe-gatestrength vl-gatestrength-p
  ///
  (defthm type-when-vl-maybe-gatestrength-p
    (implies (vl-maybe-gatestrength-p x)
             (or (not x)
                 (consp x)))
    :hints(("Goal" :in-theory (enable vl-maybe-gatestrength-p)))
    :rule-classes :compound-recognizer))


(defenum vl-cstrength-p (:vl-large :vl-medium :vl-small)
  :short "Representation of charge strengths."

  :long "<p>We represent Verilog's charge strengths with the keyword symbols
recognized by @(call vl-cstrength-p).</p>

<p>BOZO add references to the Verilog-2005 standard, description of what these
are.</p>")

(defoption vl-maybe-cstrength vl-cstrength-p
  ///
  (defthm type-when-vl-maybe-cstrength-p
    (implies (vl-maybe-cstrength-p x)
             (and (symbolp x)
                  (not (equal x t))))
    :hints(("Goal" :in-theory (enable vl-maybe-cstrength-p)))
    :rule-classes :compound-recognizer))


(defprod vl-assign
  :short "Representation of a continuous assignment statement."
  :tag :vl-assign
  :layout :tree

  ((lvalue   vl-expr-p "The location being assigned to.")
   (expr     vl-expr-p "The right-hand side.")
   (strength vl-maybe-gatestrength-p)
   (delay    vl-maybe-gatedelay-p)
   (atts     vl-atts-p
             "Any attributes associated with this assignment.")
   (loc      vl-location-p
             "Where the assignment was found in the source code."))

  :long "<p>In the Verilog sources, continuous assignment statements can take
two forms, as illustrated below.</p>

@({
module m (a, b, c) ;
  wire w1 = a & b ;     // <-- continuous assignment in a declaration
  wire w2;
  assign w2 = w1;       // <-- continuous assignment
endmodule
})

<p>Regardless of which form is used, the @(see parser) generates a
@('vl-assign-p') object.  Note that the following is also legal Verilog:</p>

@({
  assign foo = 1, bar = 2;
})

<p>But in such cases, the parser will create two @('vl-assign-p') objects, one
to represent the assignment to @('foo'), and the other to represent the
assignment to @('bar').  Hence, each @('vl-assign-p') represents only a single
assignment.</p>


<h4>Lvalue</h4>

<p>The @('lvalue') field must be an expression, and represents the location
being assigned to.  The formal syntax definition for Verilog only permits
lvalues to be:</p>

<ul>
 <li>identifiers,</li>
 <li>bit- or part-selects, and</li>
 <li>concatenations of the above.</li>
</ul>

<p>Furthermore, from Table 6.1, (p. 68), we find that only @('net')
declarations are permitted in continuous assignments; @('reg')s, @('integer')s,
and other variables must be assigned only using procedural assignments.  We
have experimentally verified (see @('test-assign.v')) that Cadence enforces
these rules.</p>

<p>Our parser does impose these syntactic restrictions, but in @('vl-assign-p')
we are perhaps overly permissive, and we only require that the @('lvalue') is
an expression.  Even so, some transforms may cause fatal warnings if these
semantic restrictions are violated, so one must be careful when generating
assignments.</p>

<h4>Expr</h4>

<p>The @('expr') is the expression being assigned to this lvalue.  We do not in
any way restrict the expression, nor have we found any restrictions discussed
in the Verilog-2005 standard.  Even so, it seems there must be some limits.
For instance, what does it mean to assign, say, a minimum/typical/maximum delay
expression?  For these sorts of reasons, some transforms may wish to only
permit a subset of all expressions here.</p>


<h4>Delay</h4>

<p>The @('delay') for a continuous assignment is discussed in 6.1.3 (page 71),
and specifies how long it takes for a change in the value of the right-hand
side to be propagated into the lvalue.  We represent the delay using a @(see
vl-maybe-gatedelay-p); if the @('delay') is @('nil'), it means that no delay
was specified.</p>

<p>Note (6.1.3) that when delays are provided in the combined declaration and
assignment statement, e.g., </p>

@({
  wire #10 a = 1, b = 2;
})

<p>that the delay is to be associated with each assignment, and NOT with the
net declaration for @('a').  Net delays are different than assignment delays;
see @(see vl-vardecl) for additional discussion.</p>

<p><b>Warning:</b> Although the parser is careful to handle the delay
correctly, we are generally uninterested in delays and our transforms may not
properly preserve them.</p>

<p><b>BOZO</b> Presumably the default delay is zero?  Haven't seen that yet,
though.</p>

<h4>Strength</h4>

<p>Strengths on continuous assignments are discussed in 6.1.4.  We represent
the strength using a @(see vl-maybe-gatestrength-p).  If a strength is not
provided, the parser sets this to @('nil').</p>

<p><b>Warning:</b> Although the parser is careful to handle the strength
correctly, we are generally uninterested in strengths and our transforms may not
properly preserve them.</p>")

(fty::deflist vl-assignlist
              :elt-type vl-assign-p
              :true-listp nil
              :elementp-of-nil nil)

(defprojection vl-assignlist->lvalues ((x vl-assignlist-p))
  :returns (lvalues vl-exprlist-p)
  :parents (vl-assignlist-p)
  (vl-assign->lvalue x))



; BOZO I'm not going to introduce this yet.  I think we should rename the expr
; field to rhs first, to prevent confusion between this and allexprs.

;; (defprojection vl-assignlist->exprs (x)
;;   (vl-assign->expr x)
;;   :guard (vl-assignlist-p x)
;;   :nil-preservingp t)


(defprod vl-alias
  :short "Representation of an alias declaration."
  :tag :vl-alias
  :layout :tree

  ((lhs     vl-expr-p "The left-hand side.")
   (rhs     vl-expr-p "The right-hand side.")
   (atts     vl-atts-p
             "Any attributes associated with this alias.")
   (loc      vl-location-p
             "Where the assignment was found in the source code.")))

(fty::deflist vl-aliaslist
  :elt-type vl-alias-p
  :true-listp nil
  :elementp-of-nil nil)

(defenum vl-lifetime-p
  (nil
   :vl-static
   :vl-automatic)
  :short "Representation of the lifetime of a variable.")

(defprod vl-vardecl
  :short "Representation of a single variable or net (e.g., wire) declaration."
  :tag :vl-vardecl
  :layout :tree

  ((name    stringp
            :rule-classes :type-prescription
            "Name of the variable being declared.")

   (type    vl-datatype-p
            "Kind of net or variable, e.g., wire, logic, reg, integer, real,
             etc.  Also contains sizing information.")

   (nettype vl-maybe-nettypename-p
            "If NIL, then this is really a variable, not a net.")

   (constp   booleanp
             :rule-classes :type-prescription
             "(Variables only).  Indicates whether the @('const') keyword was
             provided.")

   (varp     booleanp
             :rule-classes :type-prescription
             "(Variables only).  Indicates whether the @('var') keyword was
             provided.")

   (lifetime vl-lifetime-p
             "(Variables only).  See SystemVerilog-2012 Section 6.21.  There
              are pretty complex rules for variable lifetimes.  BOZO we don't
              really support this yet in any meaningful way, and the
              @('lifetime') field is currently just used to record whether a
              @('static') or @('automatic') keyword was found during parsing.")

   (initval vl-maybe-expr-p
            "(Variables only).  BOZO.  When present, indicates the initial
             value for the variable, e.g., if one writes @('integer i = 3;'),
             then the @('initval') will be the @(see vl-expr-p) for @('3').
             When wire declarations have initial values, the parser turns them
             into separate continuous assignment statements, instead.  It
             should turn these into separate initial blocks, I think.")

   (vectoredp  booleanp
               :rule-classes :type-prescription
               "(Nets only) True if the @('vectored') keyword was explicitly
                provided.")

   (scalaredp  booleanp
               :rule-classes :type-prescription
               "(Nets only) True if the @('scalared') keyword was explicitly
                provided.")

   (delay      vl-maybe-gatedelay-p
               "(Nets only) The delay associated with this wire, if any.
                For instance, @('wire #1 foo').")

   (cstrength  vl-maybe-cstrength-p
               "(Trireg nets only).  The charge strength associated with the
                net, if any.  For instance, @('trireg medium foo').")

   (atts    vl-atts-p
            "Any attributes associated with this declaration.")

   (loc     vl-location-p
            "Where the declaration was found in the source code."))

  :long "<p>Verilog-2005 and SystemVerilog-2012 distinguish between variables
and nets.  Historically, VL also separated these concepts in its basic
syntactic representation.  However, we eventually decided that merging together
the two concepts into a single syntactic representation would be simpler.  So,
today, @('vl-vardecl-p') objects are used for both @('net') declarations and
for @('reg')/variable declarations.</p>

<p>Net declarations introduce new wires with certain properties (type,
signedness, size, and so on).  Here are some examples of basic net
declarations.</p>

@({
module m (a, b, c) ;
  wire [4:0] w ;       // <-- plain net declaration
  wire ab = a & b ;    // <-- net declaration with assignment
  ...
endmodule
})

<p>Net declarations can also arise from using the combined form of port
declarations.</p>

@({
module m (a, b, c) ;
  input wire a;    // <-- net declaration in a port declaration
  ...
endmodule
})

<p>You can also string together net declarations, e.g., by writing @('wire w1,
w2;').  In all of these cases, our parser generates a separate
@('vl-vardecl-p') object for each declared wire.  When an assignment is also
present, the parser creates a corresponding, separate @(see vl-assign-p) object
to contain the assignment.  Hence, each @('vl-vardecl-p') really and truly only
represents a declaration.  Similarly, combined variable declarations such as
\"integer a, b\" are split apart into multiple, individual declarations.</p>

<h4>Arrays</h4>

<p>The @('dims') fields is for arrays.  Normally, you do not encounter these.
For instance, a wide wire declaration like this is <b>not</b> an array:</p>

@({
  wire [4:0] w;
})

<p>Instead, the @('[4:0]') part here is the @('range') of the wire and its
@('dims') are just @('nil').</p>

<p>In contrast, the @('dims') are a list of ranges, also optional, which follow
the wire name.  For instance, the arrdims of @('v') below is a singleton list
with the range @('[4:0]').</p>

@({
  wire v [4:0];
})

<p>Be aware that range and dims really are <b>different</b> things; @('w')
and @('v') are <i>not</i> equivalent except for their names.  In particular,
@('w') is a single, 5-bit wire, while @('v') is an array of five one-bit
wires.</p>

<p>Things are more complicated when a declaration includes both a range and
dims.  For instance</p>

@({
wire [4:0] a [10:0];
})

<p>declares @('a') to be an 11-element array of five-bit wires.  The @('range')
for @('a') is @('[4:0]'), and the arrdims are a list with one entry, namely the
range @('[10:0]').</p>

<p>At present, the translator has almost no support for arrdims.  However, the
parser should handle them just fine.</p>


<h4>Vectorness and Signedness</h4>

<p>These are only set to @('t') when the keywords @('vectored') or
@('scalared') are explicitly provided; i.e., they may both be @('nil').</p>

<p>I do not know what these keywords are supposed to mean; the Verilog-2005
specification says almost nothing about it, and does not even say what the
default is.</p>

<p>According to some random guy on the internet, it's supposed to be a syntax
error to try to bit- or part-select from a vectored net.  Maybe I can find a
more definitive explanation somewhere.  Hey, in 6.1.3 there are some
differences mentioned w.r.t. how delays go to scalared and vectored nets.
4.3.2 has a little bit more.</p>


<h4>Delay</h4>

<p>Net delays are described in 7.14, and indicate the time it takes for any
driver on the net to change its value.  The default delay is zero when no delay
is specified.  Even so, we represent the delay using a @(see
vl-maybe-gatedelay-p), and use @('NIL') when no delay is specified.</p>

<p>Note (from 6.1.3) that when delays are provided in the combined declaration
and assignment statement, e.g., </p>

@({
  wire #10 a = 1, b = 2;
})

<p>that the delay is to be associated with each assignment, and NOT with the
net declaration for @('a').  See @(see vl-assign-p) for more information.</p>

<p><b>BOZO</b> consider making it an explicit @(see vl-gatedelay-p) and setting
it to zero in the parser when it's not specified.</p>

<p><b>Warning:</b> we have not really paid attention to delays, and our
transformations probably do not preserve them correctly.</p>


<h4>Strengths</h4>

<p>If you look at the grammar for net declarations, you may notice drive
strengths.  But these are only used when the declaration includes assignments,
and in such cases the drive strength is a property of the assignments and is
not a property of the declaration.  Hence, there is no drive strength field
for net declarations.</p>

<p>The @('cstrength') field is only applicable to @('trireg')-type nets.  It
will be @('nil') for all other nets, and will also be @('nil') on @('trireg')
nets that do not explicitly give a charge strength.  Note that
@('vl-vardecl-p') does not enforce the requirement that only triregs have
charge strengths, but the parser does.</p>

<p><b>Warning:</b> we have not really paid attention to charge strengths, and
our transformations may not preserve it correctly.</p>")

(fty::deflist vl-vardecllist
              :elt-type vl-vardecl-p
              :true-listp nil
              :elementp-of-nil nil)



(defprod vl-plainarg
  :parents (vl-arguments-p)
  :short "Representation of a single argument in a plain argument list."
  :tag :vl-plainarg
  :layout :tree

  ((expr     vl-maybe-expr-p
             "Expression being connected to the port.  In programming languages
              parlance, this is the <i>actual</i>.  Note that this may be
              @('nil') because Verilog allows expressions to be \"blank\", in
              which case they represent an unconnected wire.")

   (portname maybe-stringp
             :rule-classes
             ((:type-prescription)
              (:rewrite
               :corollary (equal (stringp (vl-plainarg->portname x))
                                 (if (vl-plainarg->portname x)
                                     t
                                   nil))))
             "Not part of the Verilog syntax.  This <b>may</b> indicate the
              name of the port (i.e., the <i>formal</i>) that this expression
              is connected to; see below.")

   (dir      vl-maybe-direction-p
             "Not part of the Verilog syntax.  This <b>may</b> indicate the
              direction of this port; see below.")

   (atts     vl-atts-p
             "Any attributes associated with this argument."))

  :long "<p>There are two kinds of argument lists for module instantiations,
which we call <i>plain</i> and <i>named</i> arguments.</p>

@({
  modname instname ( 1, 2, 3 );             <-- \"plain\" arguments
  modname instname ( .a(1), .b(2), .c(3) ); <-- \"named\" arguments
})

<p>A @('vl-plainarg-p') represents a single argument in a plain argument
list.</p>

<p>The @('dir') is initially @('nil') but may get filled in by the @(see
argresolve) transformation to indicate whether this port for this argument is
an input, output, or inout for the module or gate being instantiated.  After
@(see argresolve), all well-formed <b>gate</b> instances will have their
direction information computed and so you may rely upon the @('dir') field for
gate instances.  <b>HOWEVER</b>, for <b>module</b> instances the direction of a
port may not be apparent; see @(see vl-port-direction) for details.  So even
after @(see argresolve) some arguments to module instances may not have a
@('dir') annotation, and you should generally not rely on the @('dir') field
for module instances.</p>

<p>The @('portname') is similar.  The @(see argresolve) transformation may
sometimes be able to fill in the name of the port, but this is meant only as a
convenience for error message generation.  This field should <b>never</b> be
used for anything that is semantically important.  No argument to a gate
instance will ever have a portname.  Also, since not every @(see vl-port-p) has
a name, some arguments to module instances may also not be given
portnames.</p>")

(fty::deflist vl-plainarglist
  :parents (vl-arguments-p)
  :elt-type vl-plainarg-p
  :true-listp nil
  :elementp-of-nil nil)

(fty::deflist vl-plainarglistlist
  :parents (vl-arguments-p)
  :elt-type vl-plainarglist-p
  :true-listp nil
  :elementp-of-nil t
  ///
  (defthm vl-plainarglist-p-of-strip-cars
    (implies (and (vl-plainarglistlist-p x)
                  (all-have-len x n)
                  (not (zp n)))
             (vl-plainarglist-p (strip-cars x)))
    :hints(("Goal" :in-theory (enable strip-cars))))

  (defthm vl-plainarglistlist-p-of-strip-cdrs
    (implies (vl-plainarglistlist-p x)
             (vl-plainarglistlist-p (strip-cdrs x)))
    :hints(("Goal" :in-theory (enable strip-cdrs)))))

(defprojection vl-plainarglist->exprs ((x vl-plainarglist-p))
  (vl-plainarg->expr x)
  ///
  (defthm vl-exprlist-p-of-vl-plainarglist->exprs
    (equal (vl-exprlist-p (vl-plainarglist->exprs x))
           (not (member nil (vl-plainarglist->exprs x)))))

  (defthm vl-exprlist-p-of-remove-nil-of-plainarglist->exprs
    (vl-exprlist-p (remove nil (vl-plainarglist->exprs x)))))


(defprod vl-namedarg
  :short "Representation of a single argument in a named argument list."
  :tag :vl-namedarg
  :layout :tree

  ((name stringp
         :rule-classes :type-prescription
         "Name of the port being connected to, e.g., @('foo') in
          @('.foo(3)')")

   (expr vl-maybe-expr-p
         "The <i>actual</i> being connected to this port; may be
          @('nil') for blank ports.")

   (nameonly-p booleanp
               "Indicates that this argument is an implicit named port
                connection, i.e., of the form @('.name').  SystemVerilog allows
                ports connections such as @('.foo, .bar, .baz').  This syntax
                is equivalent to @('.foo(foo), .bar(bar), .baz(baz)'), except
                that the names of these wires are required to exist in the
                instantiating module, i.e., no implicit nets are to be created.
                Note: the @('expr') for such a port should just be a simple
                idexpr.")

   (atts vl-atts-p
         "Any attributes associated with this argument."))

  :long "<p>See @(see vl-plainarg-p) for a general discussion of arguments.
Each @('vl-namedarg-p') represents a single argument in a named argument
list.</p>

<p>Unlike plain arguments, our named arguments do not have a direction field.
Our basic transformation strategy is to quickly eliminate named arguments and
rewrite everything as plain arguments; see the @(see argresolve) transform.
Because of this, we don't bother to annotate named arguments with their
directions.</p>")

(fty::deflist vl-namedarglist
              :elt-type vl-namedarg-p
              :true-listp nil
              :elementp-of-nil nil)

(deftagsum vl-arguments
  :short "Representation of arguments to a module instance (for ports, not
parameters)."

  :long "<p>There are two kinds of argument lists for the ports of module
instantiations, which we call <i>plain</i> and <i>named</i> arguments.</p>

@({
  modname instname ( 1, 2, 3 );             <-- \"plain\" arguments
  modname instname ( .a(1), .b(2), .c(3) ); <-- \"named\" arguments
})

<p>A @('vl-arguments-p') structure represents an argument list of either
variety.</p>"

  (:vl-arguments-plain
   :base-name vl-arguments-plain
   ((args vl-plainarglist-p
          "The actuals to the instance in order, e.g., @('1, 2, 3').")))

  (:vl-arguments-named
   :base-name vl-arguments-named
   ((args vl-namedarglist-p
          "The actuals to the instance and their names, e.g., @('.a(1), .b(2), .c(3)').")
    (starp booleanp
           "Indicates whether the @('.*') token was present."))))

(define vl-arguments->args ((x vl-arguments-p))
  :inline t
  :enabled t
  (vl-arguments-case x
    :vl-arguments-named x.args
    :vl-arguments-plain x.args))

(fty::deflist vl-argumentlist
              :elt-type vl-arguments-p
              :true-listp nil
              :elementp-of-nil nil)



(defsection vl-paramvalue
  :parents (vl-paramargs)
  :short "Representation for the actual values given to parameters."
  :long "<p>In Verilog-2005, the values for a parameterized module were always
ordinary expressions, e.g., 3 and 5 below.</p>

@({
      myalu #(.delay(3), .width(5)) alu1 (...);
})

<p>However, in SystemVerilog-2012 there can also be type parameters.  For
instance, a valid instance might look like:</p>

@({
      myalu #(.delay(3), .Bustype(logic [63:0])) myinst (...);
})

<p>The @('vl-paramvalue-p') is a sum-of-products style type that basically
corresponds to the SystemVerilog @('param_exprewssion') grammar rule:</p>

@({
     param_expression ::= mintypmax_expression | data_type | '$'
})

<p>But note that @('$') is a valid @(see vl-expr-p) so this essentially
collapses into only two cases: expression or data type.</p>")

(encapsulate
  ()
  (local (xdoc::set-default-parents vl-paramvalue))

  (local (defthmd l0
           (implies (vl-expr-p x)
                    (equal (vl-expr-kind x)
                           (tag x)))
           :hints(("Goal" :in-theory (enable vl-expr-kind vl-expr-p tag)))))

  (local (defthmd l1
           (implies (vl-datatype-p x)
                    (equal (vl-datatype-kind x)
                           (tag x)))
           :hints(("Goal" :in-theory (enable vl-datatype-kind tag vl-datatype-p)))))

  (local (defthm l2
           (implies (vl-expr-p x)
                    (or (eq (tag x) :atom)
                        (eq (tag x) :nonatom)))
           :rule-classes :forward-chaining
           :hints(("Goal" :use ((:instance l0))))))

  (local (defthm l3
           (implies (vl-datatype-p x)
                    (not (or (eq (tag x) :atom)
                             (eq (tag x) :nonatom))))
           :rule-classes :forward-chaining
           :hints(("Goal" :use ((:instance l1))))))


  (define vl-paramvalue-p (x)
    :short "Recognizer for valid @(see vl-paramvalue) structures."
    (mbe :logic
         (or (vl-expr-p x)
             (vl-datatype-p x))
         :exec
         (b* ((tag (tag x)))
           (if (or (eq tag :atom)
                   (eq tag :nonatom))
               (vl-expr-p x)
             (vl-datatype-p x))))
    ///
    (defthm type-when-vl-paramvalue-p
      (implies (vl-paramvalue-p x)
               (consp x))
      :rule-classes :compound-recognizer)

    (defthm vl-paramvalue-p-forward
      (implies (vl-paramvalue-p x)
               (or (vl-expr-p x)
                   (vl-datatype-p x)))
      :rule-classes :forward-chaining)

    (defthm vl-paramvalue-p-when-vl-expr-p
      (implies (vl-expr-p x)
               (vl-paramvalue-p x)))

    (defthm vl-paramvalue-p-when-vl-datatype-p
      (implies (vl-datatype-p x)
               (vl-paramvalue-p x))))

  (define vl-paramvalue-fix ((x vl-paramvalue-p))
    :short "Fixing function for @(see vl-paramvalue) structures."
    :inline t
    :returns (x-fix vl-paramvalue-p)
    (mbe :logic
         (if (vl-expr-p x)
             (vl-expr-fix x)
           (vl-datatype-fix x))
         :exec
         x)
    ///
    (defthm vl-paramvalue-fix-when-vl-paramvalue-p
      (implies (vl-paramvalue-p x)
               (equal (vl-paramvalue-fix x)
                      x))))

  (deffixtype vl-paramvalue
    :pred vl-paramvalue-p
    :fix vl-paramvalue-fix
    :equiv vl-paramvalue-equiv
    :define t
    :forward t)

  (define vl-paramvalue-expr-p ((x vl-paramvalue-p))
    :short "Fast recognizer for @(see vl-paramvalue)s that are expressions."
    :enabled t
    :inline t
    (mbe :logic (vl-expr-p (vl-paramvalue-fix x))
         :exec (b* ((tag (tag x)))
                 (or (eq tag :atom)
                     (eq tag :nonatom)))))

  (define vl-paramvalue-datatype-p ((x vl-paramvalue-p))
    :short "Fast recognizer for @(see vl-paramvalue)s that are expressions."
    :enabled t
    :inline t
    (mbe :logic (vl-datatype-p (vl-paramvalue-fix x))
         :exec (not (vl-paramvalue-expr-p x))))

  (defxdoc vl-paramvalue-case
    :short "Case macro for @(see vl-paramvalue)s."
    :long "@(def vl-paramvalue-case)")

  (defmacro vl-paramvalue-case (x &key expr datatype)
    `(if (vl-paramvalue-expr-p ,x)
         ,expr
       ,datatype)))

(fty::deflist vl-paramvaluelist
              :elt-type vl-paramvalue-p
              :true-listp nil
              :elementp-of-nil nil
              ///
              (defthm vl-paramvaluelist-p-when-vl-exprlist-p
                (implies (vl-exprlist-p x)
                         (vl-paramvaluelist-p x))
                :hints(("Goal" :induct (len x)))))

(local (defthm vl-paramvalue-fix-nonnil
         (vl-paramvalue-fix x)
         :hints(("Goal" :in-theory (enable (tau-system))))
         :rule-classes :type-prescription))

(defoption vl-maybe-paramvalue vl-paramvalue-p
  :parents (vl-paramargs)
  ///
  (defthm type-when-vl-maybe-paramvalue-p
    (implies (vl-maybe-paramvalue-p x)
             (or (consp x)
                 (not x)))
    :hints(("Goal" :in-theory (enable vl-maybe-paramvalue-p)))
    :rule-classes :compound-recognizer))

(defprod vl-namedparamvalue
  :parents (vl-paramargs)
  :short "Representation of a single, named parameter argument."
  :tag :vl-namedparamvalue
  :layout :tree

  ((name     stringp :rule-classes :type-prescription
             "The name of the parameter, e.g., @('size') in @('.size(3)')")

   (value    vl-maybe-paramvalue-p
             "The value being given to this parameter, e.g., @('3') in @('.size(3)').
              In Verilog-2005 this is usually an expression but might also be
              @('nil') because the value can be omitted.  SystemVerilog-2012
              extends this to also allow data types.")))

(fty::deflist vl-namedparamvaluelist
              :elt-type vl-namedparamvalue-p
              :true-listp nil
              :elementp-of-nil nil)

(deftagsum vl-paramargs
  :short "Representation of the values to use for a module instance's
  parameters (not ports)."

  :long "<p>There are two kinds of argument lists for the parameters of module
instantiations, which we call <i>plain</i> and <i>named</i> arguments.</p>

@({
  myalu #(3, 6) alu1 (...);                  <-- \"plain\" arguments
  myalu #(.size(3), .delay(6)) alu2 (...);   <-- \"named\" arguments
})

<p>A @('vl-paramargs-p') structure represents an argument list of either
variety.</p>"

  (:vl-paramargs-named
   :base-name vl-paramargs-named
   ((args vl-namedparamvaluelist-p)))

  (:vl-paramargs-plain
   :base-name vl-paramargs-plain
   ((args vl-paramvaluelist-p))))

(define vl-paramargs-empty-p ((x vl-paramargs-p))
  :parents (vl-paramargs)
  (vl-paramargs-case x
    :vl-paramargs-named (atom x.args)
    :vl-paramargs-plain (atom x.args)))


(defprod vl-modinst
  :short "Representation of a single module instance, user-defined primitive
instance, or a direct interface instance (not an interface port)."
  :tag :vl-modinst
  :layout :tree

  ((instname  maybe-stringp
              :rule-classes :type-prescription
              "Either the name of this instance or @('nil') if the instance has
               no name.  See also the @(see addinstnames) transform.")

   (modname   stringp
              :rule-classes :type-prescription
              "Name of the module, user-defined primitive, or interface that is
               being instantiated.")

   (range     vl-maybe-range-p
              "When present, indicates that this is an array of instances,
               instead of a single instance.")

   (paramargs vl-paramargs-p
              "Values to use for module parameters.  For instance, this might
               specify the width to use for an adder module, etc.")

   (portargs  vl-arguments-p
              "Connections to use for the submodule's input, output, and inout
               ports.")

   (str       vl-maybe-gatestrength-p
              "Strength for user-defined primitive instances.  Does not make
               sense for module instances.  VL mostly ignores this.")

   (delay     vl-maybe-gatedelay-p
              "Delay for user-defined primitive instances.  Does not make sense
               for module instances.  VL mostly ignores this.")

   (atts      vl-atts-p
              "Any attributes associated with this instance.")

   (loc       vl-location-p
              "Where the instance was found in the source code."))

  :long "<p>We represent module and user-defined primitive instances in a
uniform manner with @('vl-modinst-p') structures.  Because of this, certain
fields do not make sense in one context or another.  In particular, a UDP
instance should never have any parameter arguments, its port arguments should
always be an plain argument list, and it may not have a instname.  Meanwhile, a
module instance should never have a drive strength or a delay, and should
always have a instname.</p>

<p>As with variables, nets, etc., we split up combined instantiations such as
@('modname inst1 (...), inst2 (...)') into separate, individual structures, one
for @('inst1'), and one for @('inst2'), so that each @('vl-modinst-p')
represents exactly one instance (or instance array).</p>")

(fty::deflist vl-modinstlist
              :elt-type vl-modinst-p
              :true-listp nil
              :elementp-of-nil nil)


(defenum vl-gatetype-p
  (:vl-cmos
   :vl-rcmos
   :vl-bufif0
   :vl-bufif1
   :vl-notif0
   :vl-notif1
   :vl-nmos
   :vl-pmos
   :vl-rnmos
   :vl-rpmos
   :vl-and
   :vl-nand
   :vl-or
   :vl-nor
   :vl-xor
   :vl-xnor
   :vl-buf
   :vl-not
   :vl-tranif0
   :vl-tranif1
   :vl-rtranif1
   :vl-rtranif0
   :vl-tran
   :vl-rtran
   :vl-pulldown
   :vl-pullup)
  :short "Representation of gate types."
  :long "<p>We represent Verilog's gate types with the keyword symbols
recognized by @(call vl-gatetype-p).</p>")

(defprod vl-gateinst
  :short "Representation of a single gate instantiation."
  :tag :vl-gateinst
  :layout :tree
  ((type     vl-gatetype-p
             "What kind of gate this is, e.g., @('and'), @('xor'), @('rnmos'),
              etc."
             :rule-classes
             ((:rewrite)
              (:type-prescription
               :corollary
               ;; BOZO may not want to force this
               (implies (force (vl-gateinst-p x))
                        (and (symbolp (vl-gateinst->type x))
                             (not (equal (vl-gateinst->type x) t))
                             (not (equal (vl-gateinst->type x) nil)))))))

   (name     maybe-stringp
             :rule-classes
             ((:type-prescription)
              (:rewrite :corollary
                        (implies (force (vl-gateinst-p x))
                                 (equal (stringp (vl-gateinst->name x))
                                        (if (vl-gateinst->name x)
                                            t
                                          nil)))))
             "The name of this gate instance, or @('nil') if it has no name;
              see also the @(see addinstnames) transform.")

   (range    vl-maybe-range-p
             "When present, indicates that this is an array of instances
              instead of a single instance.")

   (strength vl-maybe-gatestrength-p
             "The parser leaves this as @('nil') unless it is explicitly provided.
              Note from Section 7.8 of the Verilog-2005 standard that pullup
              and pulldown gates are special in that the strength0 from a
              pullup source and the strength1 on a pulldown source are supposed
              to be ignored.  <b>Warning:</b> in general we have not paid much
              attention to strengths, so we may not handle them correctly in
              our various transforms.")

   (delay    vl-maybe-gatedelay-p
             "The parser leaves this as @('nil') unless it is explicitly provided.
              Certain gates (tran, rtran, pullup, and pulldown) never have
              delays according to the Verilog grammar, but this is only
              enforced by the parser, and is not part of our @('vl-gateinst-p')
              definition.  <b>Warning:</b> as with strengths, we have not paid
              much attention to delays, and our transforms may not handle them
              correctly.")

   (args     vl-plainarglist-p
             "Arguments to the gate instance.  Note that this differs from
              module instances where @(see vl-arguments-p) structures are used,
              because gate arguments are never named.  The grammar restricts
              how many arguments certain gates can have, but we do not enforce
              these restrictions in the definition of @('vl-gateinst-p').")

   (atts     vl-atts-p
             "Any attributes associated with this gate instance.")

   (loc      vl-location-p
             "Where the gate instance was found in the source code."))

  :long "<p>@('vl-gateinst-p') is our representation for any single gate
instance (or instance array).</p>

<p>The grammar for gate instantiations is quite elaborate, but the various
cases are so regular that a unified representation is possible.  Note that the
Verilog grammar restricts the list of expressions in certain cases, e.g., for
an @('and') gate, the first expression must be an lvalue.  Although our parser
enforces these restrictions, we do not encode them into the definition of
@('vl-gateinst-p').</p>")

(fty::deflist vl-gateinstlist
              :elt-type vl-gateinst-p
              :true-listp nil
              :elementp-of-nil nil)




(deftagsum vl-paramtype
  :parents (vl-paramdecl)
  :short "Representation of the kind and default for a parameter declaration."

  :long "<p>Both Verilog-2005 and SystemVerilog-2012 allow parameters to be
declared without any explicit type information, e.g., one can write:</p>

@({
    parameter size = 5;          <-- no explicit type, signedness, or range
    parameter signed foo = -1;   <-- explicitly signed, no explicit range
    parameter [3:0] bar = 2;     <-- explicitly 4 bits, no explicit signedness
})

<p>The ultimate, post-elaboration type and range of these parameters are
described in Verilog-2005 Section 12.2 and in SystemVerilog-2012 sections
6.20.2 and 23.10.  These rules are exotic.  When no explicit type/range is
given, the final type/range is taken from whatever value is ultimately assigned
to the parameter.  In other cases, i.e., there is only a signedness but no
explicit range, or vice versa, then some aspects of the final type/range are
determined by the value assigned to the parameter, and other aspects are
governed by the parameter declaration itself.</p>

<p>A consequence of these weird rules is that we cannot simply assign some
default type to plain parameter declarations.  Instead, we need to know that
the parameter doesn't have parts of its type specified.  To accommodate this,
we use @(see vl-implicitvalueparam) structures when the type of a parameter is
implicitly specified, or @(see vl-explicitvalueparam) structures for parameters
with explicitly specified types.</p>

<p>All of the above parameters are <b>value parameters</b>.  In Verilog-2005,
all parameters are value parameters.  However, in SystemVerilog-2012, it is
also possible to have type parameters (See Section 6.20.3), e.g.,</p>

@({
    parameter type bus_t = logic [31:0];
})

<p>Type parameters are quite different from value parameters.  We represent
their types as @(see vl-typeparam)s.</p>"

  (:vl-implicitvalueparam
   :layout :tree
   :base-name vl-implicitvalueparam
   :short "Representation for implicitly specified value parameter types."
   ((range   vl-maybe-range-p    "The range for this parameter, if provided.")
    (sign    vl-maybe-exprtype-p "The signedness for this parameter, if provided.")
    (default vl-maybe-expr-p     "The default value for this parameter, if provided.")))

  (:vl-explicitvalueparam
   :layout :tree
   :base-name vl-explicitvalueparam
   :short "Representation for explicitly specified value parameter types."
   ((type    vl-datatype     "Type of this parameter.")
    (default vl-maybe-expr-p "The default value for this parameter, if provided.")))

  (:vl-typeparam
   :layout :tree
   :short "Representation for type parameter types."
   :base-name vl-typeparam
   ((default vl-maybe-datatype-p "The default type for this parameter, if provided."))))


(defprod vl-paramdecl
  :short "Representation of a single @('parameter') or @('localparam')
declaration."
  :tag :vl-paramdecl
  :layout :tree

  ((name   stringp
           :rule-classes :type-prescription
           "Name of the parameter being declared.")

   (localp booleanp
           :rule-classes :type-prescription
           "True for @('localparam') declarations, @('nil') for @('parameter')
            declarations.  The difference is apparently that @('localparam')s
            such as @('TWICE_WIDTH') below cannot be overridden from outside
            the module, except insofar as that they depend upon non-local
            parameters.  (These @('localparam') declarations are a way to
            introduce named constants without polluting the @('`define')
            namespace.)")

   (type   vl-paramtype-p
           "Indicates the type and default value of the parameter, and also
            distinguishes between implicit/explicit value parameters and type
            parameters.")

   (atts   vl-atts-p
           "Any attributes associated with this declaration.")

   (loc    vl-location-p
           "Where the declaration was found in the source code."))

  :long "<p>Some examples of parameter declarations include:</p>

@({
module mymod (a, b, ...) ;
  parameter WIDTH = 3;
  localparam TWICE_WIDTH = 2 * WIDTH;
  ...
endmodule
})")

(fty::deflist vl-paramdecllist
              :elt-type vl-paramdecl-p
              :true-listp nil
              :elementp-of-nil nil)

(fty::deflist vl-paramdecllist-list
              :elt-type vl-paramdecllist-p
              :true-listp nil
              :elementp-of-nil t)



(define vl-importpart-p (x)
  (or (eq x :vl-import*)
      (stringp x))
  ///
  (defthm vl-importpart-p-when-stringp
    (implies (stringp x)
             (vl-importpart-p x)))

  (defthm vl-importpart-p-compound-recognizer
    (implies (vl-importpart-p x)
             (or (and (symbolp x)
                      (not (equal x nil))
                      (not (equal x t)))
                 (stringp x)))
    :rule-classes :compound-recognizer))

(define vl-importpart-fix ((x vl-importpart-p))
  :returns (part vl-importpart-p)
  (if (vl-importpart-p x)
      x
    :vl-import*)
  ///
  (defthm vl-importpart-fix-when-vl-importpart-p
    (implies (vl-importpart-p x)
             (equal (vl-importpart-fix x)
                    x))))

(fty::deffixtype vl-importpart
  :pred vl-importpart-p
  :fix vl-importpart-fix
  :equiv vl-importpart-equiv
  :define t
  :forward t)

(defprod vl-import
  :tag :vl-import
  :layout :tree
  :short "Representation of a single import item, i.e., @('import foo::bar;')."

  ((pkg  stringp :rule-classes :type-prescription
         "Package to import everything from, e.g., @('\"foo\"').")

   (part vl-importpart-p
         "Either: a single name to import, e.g., @('\"bar\"') above, or else
          the symbol @(':vl-import*'), which means import everything, as in
          @('import foo::*;').")

   (loc  vl-location-p)
   (atts vl-atts-p)))

(fty::deflist vl-importlist :elt-type vl-import-p
  :elementp-of-nil nil)



(deftranssum vl-blockitem
  :short "Recognizer for a valid block item."
  :long "<p>@('vl-blockitem-p') is a sum-of-products style type for recognizing
valid block items.  The valid block item declarations include variable
declarations and parameter declarations (parameter and localparam), which we
represent as @(see vl-vardecl-p) and @(see vl-paramdecl-p) objects,
respectively.</p>"
  (vl-vardecl
   vl-paramdecl
   vl-import))

;; [Jared] now automatic: tag-when-vl-blockitem-p-forward
;; (defthmd vl-blockitem-possible-tags
;;   (implies (vl-blockitem-p x)
;;            (or (equal (tag x) :vl-vardecl)
;;                (equal (tag x) :vl-paramdecl)
;;                (equal (tag x) :vl-import)))
;;   :rule-classes :forward-chaining)

;; [Jared] now automatic: tag-of-vl-blockitem-fix-forward
;; (defthmd vl-blockitem-fix-possible-tags
;;   (or (equal (tag (vl-blockitem-fix x)) :vl-vardecl)
;;       (equal (tag (vl-blockitem-fix x)) :vl-paramdecl)
;;       (equal (tag (vl-blockitem-fix x)) :vl-import))
;;   :hints (("goal" :use ((:instance vl-blockitem-possible-tags
;;                          (x (vl-blockitem-fix x))))))
;;   :rule-classes ((:forward-chaining :trigger-terms ((tag (vl-blockitem-fix x))))))

(defthm vl-blockitem-fix-type
  (consp (vl-blockitem-fix x))
  :rule-classes :type-prescription
  :hints(("Goal" :expand ((:with vl-blockitem-fix (vl-blockitem-fix x))))))

(fty::deflist vl-blockitemlist
  :elt-type vl-blockitem-p
  :true-listp nil
  :elementp-of-nil nil
  ///
  (defthm vl-blockitemlist-p-when-vl-vardecllist-p
    (implies (vl-vardecllist-p x)
             (vl-blockitemlist-p x))
    :hints(("Goal" :in-theory (enable vl-vardecllist-p
                                      vl-blockitemlist-p))))
  (defthm vl-blockitemlist-p-when-vl-paramdecllist-p
    (implies (vl-paramdecllist-p x)
             (vl-blockitemlist-p x))
    :hints(("Goal" :in-theory (enable vl-paramdecllist-p
                                      vl-blockitemlist-p))))
  (defthm vl-blockitemlist-p-when-vl-importlist-p
    (implies (vl-importlist-p x)
             (vl-blockitemlist-p x))
    :hints(("Goal" :in-theory (enable vl-importlist-p
                                      vl-blockitemlist-p)))))


(define vl-sort-blockitems-aux ((x vl-blockitemlist-p)
                                ;; accumulators
                                (vardecls-acc vl-vardecllist-p)
                                (paramdecls-acc vl-paramdecllist-p)
                                (imports-acc vl-importlist-p))
  :prepwork ((local (in-theory (enable tag-reasoning))))
  :returns (mv (vardecls vl-vardecllist-p)
               (paramdecls vl-paramdecllist-p)
               (imports vl-importlist-p))
  (b* (((when (atom x))
        (mv (rev (vl-vardecllist-fix vardecls-acc))
            (rev (vl-paramdecllist-fix paramdecls-acc))
            (rev (vl-importlist-fix imports-acc))))
       (x1 (vl-blockitem-fix (car x)))
       ((mv vardecls-acc paramdecls-acc imports-acc)
        (case (tag x1)
          (:vl-vardecl   (mv (cons x1 vardecls-acc)
                             paramdecls-acc
                             imports-acc))
          (:vl-paramdecl (mv vardecls-acc
                             (cons x1 paramdecls-acc)
                             imports-acc))
          (otherwise     (mv vardecls-acc
                             paramdecls-acc
                             (cons x1 imports-acc))))))
    (vl-sort-blockitems-aux (cdr x) vardecls-acc paramdecls-acc imports-acc)))

(define vl-sort-blockitems ((x vl-blockitemlist-p))
  :returns (mv (vardecls vl-vardecllist-p)
               (paramdecls vl-paramdecllist-p)
               (imports vl-importlist-p))
  (vl-sort-blockitems-aux x nil nil nil))


;                              EVENT CONTROLS
;
; Delay controls are represented just using tagged expressions.
;
; Repeat event controls are represented using simple aggregates.
;

(defenum vl-evatomtype-p
  (:vl-noedge
   :vl-posedge
   :vl-negedge)
  :parents (vl-evatom-p)
  :short "Type of an item in an event control list."
  :long "<p>Any particular atom in the event control list might have a
@('posedge'), @('negedge'), or have no edge specifier at all, e.g., for plain
atoms like @('a') and @('b') in @('always @(a or b)').</p>")

(defprod vl-evatom
  :short "A single item in an event control list."
  :tag :vl-evatom
  :layout :tree

  ((type vl-evatomtype-p
         "Kind of atom, e.g., posedge, negedge, or plain.")

   (expr vl-expr-p
         "Associated expression, e.g., @('foo') for @('posedge foo')."))

  :long "<p>Event expressions and controls are described in Section 9.7.</p>

<p>We represent the expressions for an event control (see @(see
vl-eventcontrol-p)) as a list of @('vl-evatom-p') structures.  Each individual
evatom is either a plain Verilog expression, or is @('posedge') or @('negedge')
applied to a Verilog expression.</p>")

(fty::deflist vl-evatomlist
              :elt-type vl-evatom-p
              :true-listp nil
              :elementp-of-nil nil)


(defprod vl-eventcontrol
  :short "Representation of an event controller like @('@(posedge clk)') or
@('@(a or b)')."
  :tag :vl-eventcontrol
  :layout :tree

  ((starp booleanp
          :rule-classes :type-prescription
          "True to represent @('@(*)'), or @('nil') for any other kind of
           event controller.")

   (atoms vl-evatomlist-p
          "A list of @(see vl-evatom-p)s that describe the various
           events. Verilog allows two kinds of syntax for these lists, e.g.,
           one can write @('@(a or b)') or @('@(a, b)').  The meaning is
           identical in either case, so we just use a list of atoms."))

  :long "<p>Event controls are described in Section 9.7.  We represent each
event controller as a @('vl-eventcontrol-p') aggregates.</p>")

(defprod vl-delaycontrol
  :short "Representation of a delay controller like @('#6')."
  :tag :vl-delaycontrol
  :layout :tree
  ((value vl-expr-p "The expression that governs the delay amount."))

  :long "<p>Delay controls are described in Section 9.7.  An example is</p>

@({
  #10 foo = 1;   <-- The #10 is a delay control
})")

(defprod vl-repeateventcontrol
  :short "Representation of @('repeat') constructs in intra-assignment delays."
  :tag :vl-repeat-eventcontrol
  :layout :tree
  ((expr vl-expr-p
         "The number of times to repeat the control, e.g., @('3') in the below
          example.")

   (ctrl vl-eventcontrol-p
         "Says which event to wait for, e.g., @('@(posedge clk)') in the below
          example."))

  :long "<p>See Section 9.7.7 of the Verilog-2005 standard.  These are used to
represent special intra-assignment delays, where the assignment should not
occur until some number of occurrences of an event.  For instance:</p>

@({
   a = repeat(3) @(posedge clk)   <-- repeat expr ctrl
         b;                       <-- statement to repeat
})

<p><b>BOZO</b> Consider consolidating all of these different kinds of
controls into a single, unified representation.  E.g., you could at
least extend eventcontrol with a maybe-expr that is its count, and get
rid of repeateventcontrol.</p>")

(deftranssum vl-delayoreventcontrol
  :short "BOZO document this."
  (vl-delaycontrol
   vl-eventcontrol
   vl-repeateventcontrol))

(local (defthm vl-delayoreventcontrol-fix-nonnil
         (vl-delayoreventcontrol-fix x)
         :hints(("Goal" :in-theory (enable (tau-system))))
         :rule-classes :type-prescription))

(defoption vl-maybe-delayoreventcontrol vl-delayoreventcontrol-p)


(defenum vl-assign-type-p
  (:vl-blocking
   :vl-nonblocking
   :vl-assign
   :vl-force)
  :parents (vl-stmt-p)
  :short "Type of an assignment statement."
  :long "<p>@(':vl-blocking') and @(':vl-nonblocking') are for
blocking/nonblocking procedural assignments, e.g., @('foo = bar') and @('foo <=
bar'), respectively.</p>

<p>@(':vl-assign') and @(':vl-force') are for procedural continuous
assignments, e.g., @('assign foo = bar') or @('force foo = bar'),
respectively.</p>")

(defenum vl-deassign-type-p
  (:vl-deassign :vl-release)
  :parents (vl-stmt-p)
  :short "Type of an deassignment statement.")

(defenum vl-casetype-p
  (nil
   :vl-casex
   :vl-casez)
  :parents (vl-stmt-p)
  :short "Recognizes the possible kinds of case statements."
  :long "<ul>

<li>@('nil') for ordinary @('case') statements,</li>
<li>@(':vl-casex') for @('casex') statements, and</li>
<li>@(':vl-casez') for @('casez') statements.</li>

</ul>")

(defenum vl-casecheck-p
  (nil
   :vl-unique
   :vl-unique0
   :vl-priority)
  :parents (vl-stmt-p)
  :short "Case statement violation checking mode."
  :long "<p>For ordinary @('case') statements this will be @('nil').  The other
values are for SystemVerilog's @('unique'), @('unique0'), and @('priority')
case statements.</p>")

(deftypes statements
  :short "Representation of a statement."

  :long "<p>Verilog includes a number of statements for behavioral modelling.
Some of these (assignments, event triggers, enables and disables) are
<b>atomic</b> in that they do not contain any sub-statements.  We call the
other statements (loops, cases, if statements, etc.) <b>compound</b> since they
contain sub-statements and are mutually-recursive with @('vl-stmt-p').</p>"

  :prepwork
  ((local (in-theory (disable VL-EXPR-P-OF-CAR-WHEN-VL-EXPRLIST-P
                              VL-MAYBE-EXPR-P-OF-CDAR-WHEN-VL-ATTS-P
                              VL-ATTS-P-OF-CDR-WHEN-VL-ATTS-P
                              ACL2::CONSP-OF-CAR-WHEN-ALISTP
                              acl2::car-when-all-equalp
                              VL-EXPRLIST-P-OF-CAR-WHEN-VL-EXPRLISTLIST-P
                              VL-EXPRLIST-P-OF-CDR-WHEN-VL-EXPRLIST-P
                              VL-EXPR-P-WHEN-VL-MAYBE-EXPR-P
                              VL-EXPRLISTLIST-P-OF-CDR-WHEN-VL-EXPRLISTLIST-P
                              ))))

  (fty::deflist vl-stmtlist
    :elt-type vl-stmt-p
    :true-listp t
    :elementp-of-nil nil)

  (fty::defalist vl-caselist
    :key-type vl-exprlist   ;; The match expressions in a case item
    :val-type vl-stmt       ;; The associated statement
    :true-listp t)

  (deftagsum vl-stmt

    (:vl-nullstmt
     :short "Representation of an empty statement."
     :base-name vl-nullstmt
     :layout :tree
     ((atts vl-atts-p "Any attributes associated with this statement."))

     :long "<p>We allow explicit null statements.  This allows us to
canonicalize @('if') expressions so that any missing branches are turned into
null statements.</p>")

    (:vl-assignstmt
     :layout :tree
     :base-name vl-assignstmt
     :short "Representation of an assignment statement."
     ((type   vl-assign-type-p
              "Kind of assignment statement, e.g., blocking, nonblocking, etc.")
      (lvalue vl-expr-p
              "Location being assigned to.  Note that the Verilog-2005 standard
               places various restrictions on lvalues, e.g., for a procedural
               assignment the lvalue may contain only plain variables, and
               bit-selects, part-selects, memory words, and nested
               concatenations of these things.  We do not enforce these
               restrictions in @('vl-assignstmt-p'), but only require that the
               lvalue is an expression.")
      (expr   vl-expr-p
              "The right-hand side expression that should be assigned to the
               lvalue.")
      (ctrl   vl-maybe-delayoreventcontrol-p
              "Control that affects when the assignment is done, if any.  These
               controls can be a delay like @('#(6)') or an event control like
               @('@(posedge clk)').  The rules for this are covered in Section
               9.2 and appear to perhaps be different depending upon the type
               of assignment.  Further coverage seems to be available in
               Section 9.7.7.")
      (atts   vl-atts-p
              "Any attributes associated with this statement.")
      (loc    vl-location-p
              "Where the statement was found in the source code."))
     :long "<p>Assignment statements are covered in Section 9.2.  There are two
major types of assignment statements.</p>

<h4>Procedural Assignments</h4>

<p>Procedural assignment statements may only be used to assign to @('reg'),
@('integer'), @('time'), @('realtime'), and memory data types, and cannot be
used to assign to ordinary nets such as @('wire')s.  There are two kinds of
procedural assignments: </p>

@({
   foo = bar ;     // \"blocking\" -- do the assignment now
   foo <= bar ;    // \"nonblocking\" -- schedule the assignment to occur
})

<p>The difference between these two statements has to do with Verilog's timing
model and simulation semantics.  In particular, a blocking assignment
\"executes before the statements that follow it,\" whereas a non-blocking
assignment only \"schedules\" an assignment to occur and can be thought of as
executing in parallel with what follows it.</p>

<h4>Continuous Procedural Assignments</h4>

<p>Continuous procedural assignment statements may apparently be used to assign
to either nets or variables.  There are two kinds:</p>

@({
  assign foo = bar ;  // only for variables
  force foo = bar ;   // for variables or nets
})

<p>We represent all of these kinds of assignment statements uniformly as
@('vl-assignstmt-p') objects.</p>

<h4>SystemVerilog Extensions</h4>

<p>SystemVerilog-2012 implements special additional assignment operators such
as @('a += b').  Per Section 11.4 of SystemVerilog-2012, these operators are
semantically equivalent to blocking assignment statements except that in the
case of index expressions such as @('a[i] += b'), the index @('i') is only
evaluated once.  VL's parser converts assignments such as @('a += b') into
blocking assignments such as @('a = a + b').  To note that this was a @('+=')
style assignment, the parser adds a @('VL_FANCY_ASSIGNMENT_OPERATOR') attribute
to the assignstmt.</p>

<p>SystemVerilog also adds increment and decrement operators, i.e., @('a++')
and @('a--').  These operators, per Section 11.4.2 of SystemVerilog-2012, also
\"behave as blocking assignments.\" VL2014 does not really support these
operators but they may be supported in the newer @(see vl::vl).</p>")

    (:vl-deassignstmt
     :short "Representation of a deassign or release statement."
     :base-name vl-deassignstmt
     :layout :tree
     ((type   vl-deassign-type-p)
      (lvalue vl-expr-p)
      (atts   vl-atts-p "Any attributes associated with this statement."))
     :long "<p>Deassign and release statements are described in Section 9.3.1 and
9.3.2.</p>")

    (:vl-enablestmt
     :short "Representation of an enable statement."
     :base-name vl-enablestmt
     :layout :tree
     ((id   vl-expr-p)
      (args vl-exprlist-p)
      (atts vl-atts-p "Any attributes associated with this statement."))
     :long "<p>Enable statements have an identifier (which should be either a
hierarchial identifier or a system identifier), which we represent as an
expression.  They also have a list of arguments, which are expressions.</p>")

    (:vl-disablestmt
     :short "Representation of a disable statement."
     :base-name vl-disablestmt
     :layout :tree
     ((id   vl-expr-p)
      (atts vl-atts-p "Any attributes associated with this statement."))
     :long "<p>Disable statements are simpler and just have a hierarchial
identifier.  Apparently there are no disable statements for system
identifiers.</p>")

    (:vl-eventtriggerstmt
     :short "Representation of an event trigger."
     :base-name vl-eventtriggerstmt
     :layout :tree
     ((id   vl-expr-p
            "Typically a name like @('foo') and @('bar'), but may instead be a
          hierarchical identifier.")
      (atts vl-atts-p
            "Any attributes associated with this statement."))

     :long "<p>Event trigger statements are used to explicitly trigger named
events.  They are discussed in Section 9.7.3 and looks like this:</p>

@({
 -> foo;
 -> bar[1][2][3];  // I think?
})

<p><b>BOZO</b> are we handling the syntax correctly?  What about the
expressions that can follow the trigger?  Maybe they just become part of the
@('id')?</p>")

    (:vl-casestmt
     :base-name vl-casestmt
     :layout :tree
     :short "Representation of case, casez, and casex statements."
     :long "<p>Case statements are discussed in the Verilog-2005 standard,
Section 9.5 (page 127), and in the SystemVerilog-2012 standard in Section
12.5 (page 270).</p>

<p>We do not yet support some SystemVerilog extensions, in particular:</p>

<ul>
 <li>@('case ... matches ...')</li>
 <li>@('case ... inside ...')</li>
</ul>"

     ((casetype vl-casetype-p
                "Basic case statement type: @('case'), @('casez'), or
                 @('casex').")
      (check    vl-casecheck-p
                "SystemVerilog violation checking specification: @('unique'),
                 @('unique0'), @('priority'), or none.")
      (test     vl-expr-p
                "The expression being tested.")
      (caselist vl-caselist-p
                "The match expressions and associated statements.")
      (default  vl-stmt-p
                "The default statement, if provided.  This is optional in the
                 Verilog and SystemVerilog syntax.  If it is omitted, our
                 parser will put a null statement here.")
      (atts     vl-atts-p)))

    (:vl-ifstmt
     :base-name vl-ifstmt
     :layout :tree
     :short "Representation of an if/then/else statement."
     :long "<h4>General Form:</h4>

@({
if (<condition>)
   <truebranch>
else
   <falsebranch>
})"
     ((condition   vl-expr-p)
      (truebranch  vl-stmt-p)
      (falsebranch vl-stmt-p)
      (atts        vl-atts-p)))

    (:vl-foreverstmt
     :base-name vl-foreverstmt
     :layout :tree
     :short "Representation of @('forever') statements."
     :long "<p>General syntax of a forever statement:</p>

@({
forever <body>;
})

<p>See Section 9.6 (page 130).  The forever statement continuously executes
<i>body</i>.</p>"
     ((body vl-stmt-p)
      (atts vl-atts-p)))


    (:vl-waitstmt
     :base-name vl-waitstmt
     :layout :tree
     :short "Representation of @('wait') statements."
     :long "<h4>General Form:</h4>

@({
wait (<condition>)
   <body>
})

<p>See Section 9.7.6 (page 136).  The wait statement first evaluates
<i>condition</i>.  If the result is true, <i>body</i> is executed.  Otherwise,
this flow of execution blocks until <i>condition</i> becomes 1, at which point
it resumes and <i>body</i> is executed.  There is no discussion of what happens
when the <i>condition</i> is X or Z.  I would guess it is treated as 0 like in
if statements, but who knows.</p>"
     ((condition vl-expr-p)
      (body      vl-stmt-p)
      (atts      vl-atts-p)))


    (:vl-repeatstmt
     :base-name vl-repeatstmt
     :layout :tree
     :short "Representation of @('repeat') statements."
     :long "<h4>General Form:</h4>

@({
repeat (<condition>)
   <body>
})

<p>See Section 9.6 (page 130).  The <i>condition</i> is presumably evaluated to
a natural number, and then <i>body</i> is executed that many times.  If the
expression evaluates to @('X') or @('Z'), it is supposed to be treated as zero
and the statement is not executed at all.  (What a crock!)</p>"
     ((condition vl-expr-p)
      (body      vl-stmt-p)
      (atts      vl-atts-p)))

    (:vl-whilestmt
     :base-name vl-whilestmt
     :layout :tree
     :short "Representation of @('while') statements."
     :long "<h4>General Form:</h4>

@({
while (<condition>)
   <body>
})

<p>See Section 9.6 (page 130).  The semantics are like those of while loops in
C; <i>body</i> is executed until <i>condition</i> becomes false.  If
<i>condition</i> is false to begin with, then <i>body</i> is not executed at
all.</p>"
     ((condition vl-expr-p)
      (body      vl-stmt-p)
      (atts      vl-atts-p)))

    (:vl-forstmt
     :base-name vl-forstmt
     :layout :tree
     :short "Representation of @('for') statements."
     :long "<h4>General Form:</h4>

@({
for( <for_initialization> ; <test> ; <for_step> )
   <body>
})

<p>A @('for_initialization') can either be a comma-separated list of variable
declarations with initial values, or a comma-separated list of assignments (of
previously declared variables).  A @('for_step') is a comma-separated list of
variable assignments, increments, or decrements.</p>

<p>See SystemVerilog Section 12.7.1.  The for statement acts like a for-loop in
C.  First, outside the loop, it executes the @('for_initialization')
assignments.  Then it evalutes <i>test</i>.  If <i>test</i> evaluates to
zero (or to X or Z) then the loop exists.  Otherwise, <i>body</i> is executed,
the @('for_step') is performed, and we loop back to evaluating
<i>test</i>.</p>

<p>The syntaxp for @('for_initialization') is a little tricky since it can
either have declarations or assignments to pre-existing variables, but not
both.  Our representation contains a @(see vl-vardecllist-p) with initial
values to cover the declaration case and a @(see vl-stmtlist-p) to cover the
assignment case; one or the other of these will be empty.</p>"
     ((initdecls vl-vardecllist-p)
      (initassigns vl-stmtlist-p)
      (test        vl-expr-p)
      (stepforms   vl-stmtlist-p)
      (body        vl-stmt-p)
      (atts        vl-atts-p)))

    (:vl-blockstmt
     :base-name vl-blockstmt
     :layout :tree
     :short "Representation of begin/end and fork/join blocks."
     :long "<h4>General Form:</h4>

@({
begin [ : <name> <declarations> ]
  <statements>
end

fork [ :<name> <declarations> ]
  <statements>
join
})

<p>See Section 9.8.  The difference betwen the two kinds of blocks is that in a
@('begin/end') block, statements are to be executed in order, whereas in a
@('fork/join') block, statements are executed simultaneously.</p>

<p>Blocks that are named can have local declarations, and can be referenced by
other statements (e.g., disable statements).  With regards to declarations:
\"All variables shall be static; that is, a unique location exists for all
variables, and leaving or entering blocks shall not affect the values stored in
them.\"</p>

<p>A further remark is that \"Block names give a means of uniquely identifying
all variables at any simulation time.\" This seems to suggest that one might
try to flatten all of the declarations in a module by, e.g., prepending the
block name to each variable name.</p>"

     ((sequentialp booleanp :rule-classes :type-prescription)
      (name        maybe-stringp :rule-classes :type-prescription)
      (imports     vl-importlist-p)
      (paramdecls  vl-paramdecllist-p)
      (vardecls    vl-vardecllist-p)
      (loaditems   vl-blockitemlist-p)
      (stmts       vl-stmtlist-p)
      (atts        vl-atts-p)))

    (:vl-timingstmt
     :base-name vl-timingstmt
     :layout :tree
     :short "Representation of timing statements."
     :long "<h4>General Form:</h4>

@({
<ctrl> <body>
})

<h4>Examples:</h4>

@({
#3 foo = bar;
@@(posedge clk) foo = bar;
@@(bar or baz) foo = bar | baz;
})"
     ((ctrl vl-delayoreventcontrol-p)
      (body vl-stmt-p)
      (atts vl-atts-p)))

    (:vl-returnstmt
     :base-name vl-returnstmt
     :layout :tree
     :short "Representation of return statements."
     ((val vl-maybe-expr-p)
      (atts vl-atts-p)))
    ))

;; NOTE: Other statement subtypes are declared in stmt-tools.  This is here
;; because scopestack needs it.
(define vl-blockstmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  (eq (vl-stmt-kind x) :vl-blockstmt))



(local (in-theory (disable vl-stmtlist-p-of-cdr-when-vl-stmtlist-p
                           consp-when-member-equal-of-vl-caselist-p
                           vl-stmt-p-when-member-equal-of-vl-stmtlist-p)))


;                       INITIAL AND ALWAYS BLOCKS
;
; Initial and always blocks just have a statement and, perhaps, some
; attributes.

(defprod vl-initial
  :short "Representation of an initial statement."
  :tag :vl-initial
  :layout :tree

  ((stmt vl-stmt-p
         "Represents the actual statement, e.g., @('r = 0') below.")

   (atts vl-atts-p
         "Any attributes associated with this @('initial') block.")

   (loc  vl-location-p
         "Where the initial block was found in the source code."))

  :long "<p>Initial statements in Verilog are used to set up initial values for
simulation.  For instance,</p>

@({
module mymod (a, b, ...) ;
   reg r, s;
   initial r = 0;   <-- initial statement
endmodule
})

<p><b>BOZO</b> Our plan is to eventually generate @('initial') statements from
register and variable declarations with initial values, i.e., @('reg r =
0;').</p>")


(defenum vl-alwaystype-p
  (:vl-always
   :vl-always-comb
   :vl-always-latch
   :vl-always-ff)
  :short "Indicates the kind of an always statement."
  :long "<p>In Verilog-2005 there are only @('always') statements.
SystemVerilog-2012 adds @('always_comb'), @('always_latch'), and
@('always_ff').</p>")

(defprod vl-always
  :short "Representation of an always statement."
  :tag :vl-always
  :layout :tree

  ((type vl-alwaystype-p
         "What kind of @('always') block this is, e.g., @('always'), @('always_comb'),
          @('always_latch'), or @('always_ff').")

   (stmt vl-stmt-p
         "The actual statement, e.g., @('@(posedge clk) myreg <= in')
          below. The statement does not have to include a timing control like
          @('@(posedge clk)') or @('@(a or b or c)'), but often does.")

   (atts vl-atts-p
         "Any attributes associated with this @('always') block.")

   (loc  vl-location-p
         "Where the always block was found in the source code."))

  :long "<p>Always statements in Verilog are often used to model latches and
flops, and to set up other simulation events.  A simple example would be:</p>

@({
module mymod (a, b, ...) ;
  always @(posedge clk) myreg <= in;
endmodule
})")

(fty::deflist vl-initiallist
  :elt-type vl-initial-p
  :elementp-of-nil nil)

(fty::deflist vl-alwayslist
  :elt-type vl-always-p
  :elementp-of-nil nil)



;; (defenum vl-taskporttype-p
;;   (:vl-unsigned
;;    :vl-signed
;;    :vl-integer
;;    :vl-real
;;    :vl-realtime
;;    :vl-time)
;;   :short "Representation for the type of task ports, function return types, and
;; function inputs."

;;   :long "<p>These are the various return types that can be used with a Verilog
;; task's input, output, or inout declarations.  For instance, a task can have
;; ports such as:</p>

;; @({
;;   task mytask;
;;     input integer count;  // type :vl-integer
;;     output signed value;  // type :vl-signed
;;     inout x;              // type :vl-unsigned
;;     ...
;;   endtask
;; })

;; <p>There isn't an explicit @('unsigned') type that you can write; so note that
;; @(':vl-unsigned') is really the type for \"plain\" ports that don't have an
;; explicit type label.</p>

;; <p>These same types are used for the return values of Verilog functions.  For
;; instance, we use @(':vl-unsigned') for a function like:</p>

;; @({ function [7:0] add_one ; ... endfunction })

;; <p>whereas we use @(':vl-real') for a function like:</p>

;; @({ function real get_ratio ; ... endfunction })

;; <p>Likewise, the inputs to Verilog functions use these same kinds of
;; types.</p>")

;; (defprod vl-taskport
;;   :short "Representation of a task port or a function input."
;;   :tag :vl-taskport
;;   :layout :Tree

;;   ((name  stringp
;;           :rule-classes :type-prescription
;;           "The name of this task port.")

;;    (dir   vl-direction-p
;;           :rule-classes
;;           ((:rewrite)
;;            (:type-prescription
;;             :corollary
;;             (implies (force (vl-taskport-p x))
;;                      (and (symbolp (vl-taskport->dir x))
;;                           (not (equal (vl-taskport->dir x) t))
;;                           (not (equal (vl-taskport->dir x) nil))))))
;;           "Says whether this is an input, output, or inout port.  Note that
;;            tasks can have all three kinds of ports, but functions only have
;;            inputs.")

;;    (type  vl-taskporttype-p
;;           :rule-classes
;;           ((:rewrite)
;;            (:type-prescription
;;             :corollary
;;             (implies (force (vl-taskport-p x))
;;                      (and (symbolp (vl-taskport->type x))
;;                           (not (equal (vl-taskport->type x) t))
;;                           (not (equal (vl-taskport->type x) nil))))))
;;           "Says what kind of port this is, i.e., @('integer'), @('real'),
;;           etc.")

;;    (range vl-maybe-range-p
;;           "The size of this input.  A range only makes sense when the type is
;;            @(':vl-unsigned') or @(':vl-signed').  It should be @('nil') when
;;            other types are used.")

;;    (atts  vl-atts-p
;;           "Any attributes associated with this input.")

;;    (loc   vl-location-p
;;           "Where this input was found in the source code."))

;;   :long "<p>Verilog tasks have ports that are similar to the ports of a module.
;; We represent these ports with their own @('vl-taskport-p') structures, rather
;; than reusing @(see vl-portdecl-p), because unlike module port declarations,
;; task ports can have types like @('integer') or @('real').</p>

;; <p>While Verilog functions don't have @('output') or @('inout') ports, they do
;; have input ports that are very similar to task ports.  So, we reuse
;; @('vl-taskport-p') structures for function inputs.</p>")

;; (fty::deflist vl-taskportlist :elt-type vl-taskport-p
;;   :elementp-of-nil nil)

;; (defprojection vl-taskportlist->names ((x vl-taskportlist-p))
;;   :returns (names string-listp)
;;   (vl-taskport->name x))


(defprod vl-fundecl
  :short "Representation of a single Verilog function."
  :tag :vl-fundecl
  :layout :tree

  ((name       stringp
               :rule-classes :type-prescription
               "Name of this function, e.g., @('lower_bits') below.")

   (lifetime   vl-lifetime-p
               "Indicates whether an explicit @('automatic') or @('static')
                lifetime was provided.  An automatic function is supposed to be
                reentrant and have its local parameters dynamically allocated
                for each function call, with various consequences.")

   (rettype    vl-datatype-p
               "Return type of the function, e.g., a function might return an
                ordinary unsigned or signed result of some width, or might
                return a @('real') value, etc.  For instance, the return type
                of @('lower_bits') below is @(':vl-unsigned').")

   (portdecls  vl-portdecllist-p
               "The arguments to the function, e.g., @('input [7:0] a') below.
                Functions must have at least one input.  We check this in our
                parser, but we don't syntactically enforce this requirement in
                the @('vl-fundecl-p') structure.  In Verilog-2005, functions
                may only have inputs (i.e., they can't have outputs or inouts),
                but our @(see vl-portdecl-p) structures have a direction, so in
                the context of a function declaration this direction should
                always be @(':vl-input').  In SystemVerilog functions can have
                other kinds of ports, but functions with output/inout ports
                have restrictions and can't be used in expressions like normal
                functions.")

   (imports     vl-importlist-p
                "Local package imports")

   (vardecls    vl-vardecllist-p
                "Local variable declarations, including ones for the ports and
                 return value (see below).")

   (paramdecls  vl-paramdecllist-p
                "Local parameter declarations")

   (blockitems  vl-blockitemlist-p
                "The declarations within the function, in parse order.  We sort
                 these out into the imports, vardecls, and paramdecls. It appears
                 that these may even contain event declarations, parameter declarations,
                 etc., which seems pretty absurd.")

   (body       vl-stmt-p
               "The body of the function.  We represent this as an ordinary statement,
                but it must follow certain rules as outlined in 10.4.4, e.g.,
                it cannot have any time controls, cannot enable tasks, cannot
                have non-blocking assignments, etc.")

   (atts       vl-atts-p
               "Any attributes associated with this function declaration.")

   (loc        vl-location-p
               "Where this declaration was found in the source code."))

  :long "<p>Functions are described in Section 10.4 of the Verilog-2005
standard.  An example of a function is:</p>

@({
function [3:0] lower_bits;
  input [7:0] a;
  reg [1:0] lowest_pair;
  reg [1:0] next_lowest_pair;
  begin
    lowest_pair = a[1:0];
    next_lowest_pair = a[3:2];
    lower_bits = {next_lowest_pair, lowest_pair};
  end
endfunction
})

<p>Note that functions don't have any inout or output ports.  Instead, you
assign to a function's name to indicate its return value.</p>

<p>To simplify scoping issues, we put \"hidden\" variables declarations for the
ports and return value of the function into its @('decls').  These ports are
marked with the @('VL_HIDDEN_DECL_FOR_TASKPORT') attribute.  The pretty printer
and other code rely on this attribute to produce the correct output.  These
extra declarations are created automatically by the loader.</p>")

(fty::deflist vl-fundecllist
  :elt-type vl-fundecl-p
  :elementp-of-nil nil)

(defprojection vl-fundecllist->names ((x vl-fundecllist-p))
  :returns (names string-listp)
  (vl-fundecl->name x))


(defprod vl-taskdecl
  :short "Representation of a single Verilog task."
  :tag :vl-taskdecl
  :layout :tree

  ((name       stringp
               :rule-classes :type-prescription
               "The name of this task.")

   (lifetime   vl-lifetime-p
               "Indicates whether an explicit @('automatic') or @('static')
                lifetime was provided.  Each invocation of an automatic task
                has its own copy of its variables.  For instance, the task
                below had probably better be automatic if it there are going to
                be concurrent instances of it running, since otherwise
                @('temp') could be corrupted by the other task.")

   (portdecls  vl-portdecllist-p
               "The input, output, and inout ports for the task.")

   (imports     vl-importlist-p
                "Local package imports")

   (vardecls    vl-vardecllist-p
                "Local variable declarations, including ones for the ports and
                 return value (see below); these are marked with
                 @('VL_HIDDEN_DECL_FOR_TASKPORT').")

   (paramdecls  vl-paramdecllist-p
                "Local parameter declarations")


   (blockitems  vl-blockitemlist-p
               "All the local declarations for the task; we sort these out into
                the imports, vardecls, and paramdecls above.")

   (body       vl-stmt-p
               "The statement that gives the actions for this task, i.e., the
                entire @('begin/end') statement in the below task.")

   (atts       vl-atts-p
               "Any attributes associated with this task declaration.")

   (loc        vl-location-p
               "Where this task was found in the source code."))

  :long "<p>Tasks are described in Section 10.2 of the Verilog-2005 standard.
An example of a task is:</p>

@({
task automatic dostuff;
  input [3:0] count;
  output inc;
  output onehot;
  output more;
  reg [2:0] temp;
  begin
    temp = count[0] + count[1] + count[2] + count[3];
    onehot = temp == 1;
    if (!onehot) $display(\"onehot is %b\", onehot);
    #10;
    inc = count + 1;
    more = count > prev_count;
  end
endtask
})

<p>Tasks are somewhat like <see topic='@(url vl-fundecl-p)'>functions</see>,
but they can have fewer restrictions, e.g., they can have multiple outputs, can
include delays, etc.</p>")

(fty::deflist vl-taskdecllist
  :elt-type vl-taskdecl-p
  :elementp-of-nil nil)

(defprojection vl-taskdecllist->names ((x vl-taskdecllist-p))
  :returns (names string-listp)
  (vl-taskdecl->name x))




(defprod vl-modport-port
  :parents (vl-interface)
  :short "A single port from a modport declaration."
  :long  "<p>The syntax for this is:</p>
@({
 modport_simple_ports_declaration ::=
 port_direction modport_simple_port { , modport_simple_port }

 modport_simple_port ::=
 port_identifier
 | . port_identifier ( [ expression ] )
 })

<p>As with regular ports, if the expression is not provided then the port
identifier is turned into an expression.  The variables used in the expression
must be declared in the interface, but it is permissible for the expression to
be non-sliceable, at least if it's an input.</p>"

  ((name stringp         "Name of the port; often the same as the expr")
   (dir  vl-direction-p  "Port direction")
   (expr vl-maybe-expr-p "Expression in terms of the declared variables of the interface.")
   (atts vl-atts-p       "attributes")
   (loc  vl-location-p :default *vl-fakeloc*))
  :prepwork ())

(fty::deflist vl-modport-portlist
  :elt-type vl-modport-port
  :elementp-of-nil nil
  :true-listp nil)

(defprod vl-modport
  :parents (vl-interface)
  :short "A modport declaration within an interface"
  :long "<p>Missing task/function import/exports and clocking blocks.</p>"
  ((name      stringp                "the name of the modport declaration; often master or slave")
   (ports     vl-modport-portlist-p  "the ports; names must be declared in the interface")
   (atts      vl-atts-p              "attributes")
   (loc       vl-location-p :default *vl-fakeloc*))
  :tag :vl-modport)

(fty::deflist vl-modportlist
  :elt-type vl-modport
  :elementp-of-nil nil
  :true-listp nil)


(defenum vl-fwdtypedefkind-p
  (:vl-enum
   :vl-struct
   :vl-union
   :vl-class
   :vl-interfaceclass)
  :parents (vl-fwdtypedef-p)
  :short "Kinds of forward type declarations.")

(defprod vl-fwdtypedef
  :tag :vl-fwdtypedef
  :short "Representation of a forward typedef like @('typedef struct foo_t;')."
  ((atts vl-atts-p)
   (kind vl-fwdtypedefkind-p)
   (name stringp)
   (loc  vl-location-p)))

(fty::deflist vl-fwdtypedeflist
  :elt-type vl-fwdtypedef-p
  :elementp-of-nil nil)

(defprod vl-typedef
  :tag :vl-typedef
  :short "Representation of a basic type declaration like @('typedef struct ... foo_t;')."
  ((name stringp)
   (type vl-datatype-p)
   (atts vl-atts-p)
   (minloc vl-location-p)
   (maxloc vl-location-p)
   (warnings vl-warninglist-p)
   (comments vl-commentmap-p)))

(defmacro vl-typedef->loc (x)
  `(vl-typedef->minloc ,x))

(fty::deflist vl-typedeflist
  :elt-type vl-typedef-p
  :elementp-of-nil nil)

(defprojection vl-typedeflist->names ((x vl-typedeflist-p))
  :parents (vl-typedeflist-p)
  :returns (names string-listp)
  (vl-typedef->name x))

(defprod vl-genvar
  :tag :vl-genvar
  :short "Representation of a genvar declaration."
  ((name stringp)
   (atts vl-atts-p)
   (loc  vl-location-p)))

(fty::deflist vl-genvarlist :elt-type vl-genvar :elementp-of-nil nil)

(encapsulate nil

  (defconst *vl-modelement-typenames*
    '(portdecl
      assign
      alias
      vardecl
      paramdecl
      fundecl
      taskdecl
      modinst
      gateinst
      always
      initial
      typedef
      import
      fwdtypedef
      modport
      genvar))

  (local (defun typenames-to-tags (x)
           (declare (xargs :mode :program))
           (if (atom x)
               nil
             (cons (intern$ (cat "VL-" (symbol-name (car x))) "KEYWORD")
                   (typenames-to-tags (cdr x))))))

  (make-event
   `(defconst *vl-modelement-tagnames*
      ',(typenames-to-tags *vl-modelement-typenames*)))

  (defun vl-typenames-to-tmplsubsts (types)
    (declare (xargs :mode :program))
    (if (atom types)
        nil
      (let ((name (symbol-name (car types))))
        (cons (make-tmplsubst
               :strs `(("__TYPE__" ,name . vl-package)
                       ("__ELTS__" ,(if (member (char name (1- (length name))) '(#\S #\s))
                                        (str::cat name "ES")
                                      (str::cat name "S")) . vl-package)))
              (vl-typenames-to-tmplsubsts (cdr types))))))

  (defconst *vl-modelement-tmplsubsts*
    (vl-typenames-to-tmplsubsts *vl-modelement-typenames*))

  (defun project-over-modelement-types (template)
    (declare (xargs :mode :program))
    (template-proj template *vl-modelement-tmplsubsts*))

  (defun append-over-modelement-types (template)
    (declare (xargs :mode :program))
    (template-append template *vl-modelement-tmplsubsts*))


  (make-event
   `(progn
      (deftranssum vl-modelement
        :short "Recognizer for an arbitrary module element."

        :long "<p>It is sometimes useful to be able to deal with module elements of
arbitrary types.  For instance, we often use this in error messages, along with
@(see vl-context-p), to describe where expressions occur.  We also use it in
our @(see parser), where before module formation, the module elements are
initially kept in a big, mixed list.</p>"
        ,(project-over-modelement-types 'vl-__type__))

      (fty::deflist vl-modelementlist
        :elt-type vl-modelement-p
        :elementp-of-nil nil
        ///
        (local (in-theory (enable vl-modelementlist-p)))
        . ,(project-over-modelement-types
            '(defthm vl-modelementlist-p-when-vl-__type__list-p
               (implies (vl-__type__list-p x)
                        (vl-modelementlist-p x)))))

      (define vl-modelement->loc ((x vl-modelement-p))
        :returns (loc vl-location-p :hints(("Goal" :in-theory (enable vl-modelement-fix
                                                                      vl-modelement-p
                                                                      tag-reasoning
                                                                      (tau-system)))))
        (let ((x (vl-modelement-fix x)))
          (case (tag x)
            . ,(project-over-modelement-types
                '(:vl-__type__ (vl-__type__->loc x))))))))


  (local (in-theory (disable acl2::o<-of-two-nats-measure o< o<-when-natps nfix)))
  (deftypes vl-genelement
    ;; :prepwork
    ;; ((local (defthm nfix-when-natp
    ;;           (implies (natp x)
    ;;                    (equal (nfix x) x))
    ;;           :hints(("Goal" :in-theory (enable nfix)))))
    ;;  (local (in-theory (disable default-car default-cdr
    ;;                             acl2::consp-of-car-when-alistp)))
    ;;  (local (defthm my-o<-of-two-nats-measure-1
    ;;           (implies (< (nfix a) (nfix b))
    ;;                    (o< (two-nats-measure a c) (two-nats-measure b d)))
    ;;           :hints(("Goal" :in-theory (enable acl2::o<-of-two-nats-measure)))))
    ;;  (local (defthm my-o<-of-two-nats-measure-2
    ;;           (implies (and (<= (nfix a) (nfix b))
    ;;                         (< (nfix c) (nfix d)))
    ;;                    (o< (two-nats-measure a c) (two-nats-measure b d)))
    ;;           :hints(("Goal" :in-theory (enable acl2::o<-of-two-nats-measure)))))
    ;;  )

    (deftagsum vl-genelement

      ;; NOTE: According to the SystemVerilog spec, generate/endgenerate just
      ;; defines a textual region, which makes "no semantic difference" in the module.
      ;; So (for now at least) we'll ignore them.

      ;; (:vl-genregion
      ;;  :base-name vl-genregion
      ;;  :layout :tree
      ;;  :short "A generate/endgenerate region"
      ;;  ((items vl-genelementlist     "the items contained in the region")
      ;;   (loc   vl-location)))

      (:vl-genloop
       :base-name vl-genloop
       :layout :tree
       :short "A loop generate construct"
       ((var        vl-id            "the iterator variable")
        (initval    vl-expr-p        "initial value of the iterator")
        (continue   vl-expr-p        "continue the loop until this is false")
        (nextval    vl-expr-p        "next value of the iterator")
        (body       vl-genelement "body of the loop")
        (loc        vl-location)))

      (:vl-genif
       :base-name vl-genif
       :layout :tree
       :short "An if generate construct"
       ((test       vl-expr-p        "the test of the IF")
        (then       vl-genelement "the block for the THEN case")
        (else       vl-genelement "the block for the ELSE case; empty if not provided")
        (loc        vl-location)))

      (:vl-gencase
       :base-name vl-gencase
       :layout :tree
       :short "A case generate construct"
       ((test      vl-expr-p         "the expression to test against the cases")
        (cases     vl-gencaselist    "the case generate items, except the default")
        (default   vl-genelement  "the default, which may be an empty genblock if not provided")
        (loc       vl-location)))

      (:vl-genblock
       :base-name vl-genblock
       :layout :tree
       :short "Normalized form of a generate construct that has been instantiated."
       ((name      maybe-stringp     "the name of the block, if named")
        (elems     vl-genelementlist-p)
        (loc       vl-location)))


      (:vl-genarray
       :base-name vl-genarray
       :layout :tree
       :short "Normalized form of a generate loop."
       ((name      maybe-stringp     "the name of the block array, if named")
        (var       vl-id             "the iterator variable")
        (blocks    vl-genarrayblocklist-p "the blocks produced by the loop")
        (loc       vl-location)))

      (:vl-genbase
       :base-name vl-genbase
       :layout :tree
       :short "A basic module/generate item"
       ((item      vl-modelement        "a generate item")))

      :measure (two-nats-measure (acl2-count x) 1))

    (fty::deflist vl-genelementlist :elt-type vl-genelement
      :true-listp t
      :elementp-of-nil nil
      :measure (two-nats-measure (acl2-count x) 1))

    (fty::defalist vl-gencaselist :key-type vl-exprlist :val-type vl-genelement
      :true-listp t
      :measure (two-nats-measure (acl2-count x) 5))

    (fty::deflist vl-genarrayblocklist :elt-type vl-genarrayblock
      :true-listp t :elementp-of-nil nil
      :measure (two-nats-measure (acl2-count x) 1))

    (defprod vl-genarrayblock
      ((index    integerp           "index of the iterator variable for this block")
       (elems    vl-genelementlist-p))
      :measure (two-nats-measure (acl2-count x) 3))

    :enable-rules (acl2::o-p-of-two-nats-measure
                   acl2::o<-of-two-nats-measure
                   acl2-count-of-car
                   acl2-count-of-cdr
                   acl2-count-of-cdr-same-fc
                   cons-equal
                   ;; default-car  default-cdr
                   nfix
                   ))

  (defthm vl-genelement-fix-type
    (consp (vl-genelement-fix x))
    :rule-classes :type-prescription
    :hints(("Goal" :expand ((:with vl-genelement-fix (vl-genelement-fix x))))))

  (define vl-genelement->loc ((x vl-genelement-p))
    :returns (loc vl-location-p)
    (vl-genelement-case x
      (:vl-genloop  x.loc)
      (:vl-genif    x.loc)
      (:vl-gencase  x.loc)
      (:vl-genblock x.loc)
      (:vl-genarray x.loc)
      (:vl-genbase  (vl-modelement->loc x.item)))))


(define vl-modelementlist->genelements ((x vl-modelementlist-p))
  :returns (xx vl-genelementlist-p)
  (if (atom x)
      nil
    (cons (make-vl-genbase :item (car x))
          (vl-modelementlist->genelements (cdr x)))))

(encapsulate nil

  ;; [Jared] now automatic
  ;; (defthm tag-when-vl-genelement-p-forward
  ;;   (implies (vl-genelement-p x)
  ;;            (or (equal (tag x) :vl-genbase)
  ;;                (equal (tag x) :vl-genloop)
  ;;                (equal (tag x) :vl-genif)
  ;;                (equal (tag x) :vl-gencase)
  ;;                (equal (tag x) :vl-genblock)
  ;;                (equal (tag x) :vl-genarray)))
  ;;   :hints(("Goal" :in-theory (enable tag vl-genelement-p)))
  ;;   :rule-classes :forward-chaining)

  (local (defthm vl-genelement-p-of-vl-genelement-fix-forward-for-tag
           (vl-genelement-p (vl-genelement-fix x))
           :rule-classes
           ((:forward-chaining :trigger-terms ((tag (vl-genelement-fix x)))))))

  (deftranssum vl-ctxelement
    ;; Add any tagged product that can be written with ~a and has a loc field.
    (vl-portdecl
     vl-assign
     vl-alias
     vl-vardecl
     vl-paramdecl
     vl-fundecl
     vl-taskdecl
     vl-modinst
     vl-gateinst
     vl-always
     vl-initial
     vl-typedef
     vl-import
     vl-fwdtypedef
     vl-modport
     vl-interfaceport
     vl-regularport
     vl-genelement))

  (local (defthm vl-genelement-kind-by-tag-when-vl-ctxelement-p
           (implies (and (vl-ctxelement-p x)
                         (vl-genelement-p x))
                    (equal (vl-genelement-kind x)
                           (tag x)))
           :hints(("Goal" :in-theory (enable vl-ctxelement-p
                                             vl-genelement-p
                                             vl-genelement-kind
                                             tag)))))

  (define vl-ctxelement->loc ((x vl-ctxelement-p))
    :returns (loc vl-location-p :hints(("Goal" :in-theory (enable vl-ctxelement-fix
                                                                  vl-ctxelement-p
                                                                  tag-reasoning
                                                                  (tau-system)))))
    :guard-hints (("Goal" :do-not-induct t))
    (let ((x (vl-ctxelement-fix X)))
      (case (tag x)
        (:vl-portdecl (vl-portdecl->loc x))
        (:vl-assign (vl-assign->loc x))
        (:vl-alias (vl-alias->loc x))
        (:vl-vardecl (vl-vardecl->loc x))
        (:vl-paramdecl (vl-paramdecl->loc x))
        (:vl-fundecl (vl-fundecl->loc x))
        (:vl-taskdecl (vl-taskdecl->loc x))
        (:vl-modinst (vl-modinst->loc x))
        (:vl-gateinst (vl-gateinst->loc x))
        (:vl-always (vl-always->loc x))
        (:vl-initial (vl-initial->loc x))
        (:vl-typedef (vl-typedef->loc x))
        (:vl-import (vl-import->loc x))
        (:vl-fwdtypedef (vl-fwdtypedef->loc x))
        (:vl-modport (vl-modport->loc x))
        (:vl-interfaceport (vl-interfaceport->loc x))
        (:vl-regularport (vl-regularport->loc x))
        (:vl-genbase (vl-modelement->loc (vl-genbase->item x)))
        (:vl-genloop (vl-genloop->loc x))
        (:vl-genif   (vl-genif->loc x))
        (:vl-gencase (vl-gencase->loc x))
        (:vl-genblock (vl-genblock->loc x))
        (:vl-genarray (vl-genarray->loc x))))))

(defprod vl-context1
  :short "Description of where an expression occurs."
  :tag :vl-context
  :layout :tree
  ((mod  stringp :rule-classes :type-prescription
         "The module where this module element was taken from.")
   (elem vl-ctxelement-p
         "Some element from the module.")))

(defxdoc vl-context
  :short "A context for @(see warnings)."

  :long "<p>Contexts are usually @(see vl-context1)s.  However, for more
generality, you can use any arbitrary object as a context.  The proper way to
do this is to wrap it using @('(vl-context x)').</p>

@(def vl-context)
@(def make-vl-context)")

(define vl-context-p ((x))
  :parents (vl-context)
  :prepwork ((set-tau-auto-mode nil))
  (declare (ignorable x))
  t
  ///
  (defthm vl-context-p-type
    (booleanp (vl-context-p x))
    :rule-classes :type-prescription)
  (in-theory (disable (:t vl-context-p)))

  (defthm vl-context-p-when-vl-ctxelement-p
    (implies (vl-ctxelement-p x)
             (vl-context-p x)))

  (defthm vl-context-p-when-vl-context1-p
    (implies (vl-context1-p x)
             (vl-context-p x))))

(define vl-context-fix ((x))
  :prepwork ((set-tau-auto-mode nil))
  :parents (vl-context)
  x
  ///
  (local (in-theory (enable vl-context-p)))
  (defthm vl-context-p-of-vl-context-fix
    (vl-context-p (vl-context-fix x)))
  (defthm vl-context-fix-when-vl-context-p
    (implies (vl-context-p x)
             (equal (vl-context-fix x) x)))

  (fty::deffixtype vl-context
    :pred vl-context-p
    :fix vl-context-fix
    :equiv vl-context-equiv
    :define t))

(defmacro make-vl-context (&rest args)
  `(vl-context (make-vl-context1 . ,args)))

(defmacro vl-context (x)
  `(vl-context-fix ,x))


(defprod vl-module
  :short "Representation of a single module."
  :tag :vl-module
  :layout :fulltree

  ((name       stringp
               :rule-classes :type-prescription
               "The name of this module as a string.  The name is used to
                instantiate this module, so generally we require that modules
                in our list have unique names.  A module's name is initially
                set when it is parsed, but it may not remain fixed throughout
                simplification.  For instance, during @(see unparameterization)
                a module named @('adder') might become @('adder$size=12').")

   (params     "Any @('defparam') statements for this module.  BOZO these are
                bad form anyway, but eventually we should provide better
                support for them and proper structures.")

   ;; BOZO possibly add lifetime declarations, but the spec seems pretty vague
   ;; about what they mean.  The only thing I see about them is that they are
   ;; the "default lifetime (static or automatic) of subroutines defined within
   ;; the module."  Which doesn't seem like a very good idea anyway...

   ;; BOZO possibly add timeunits declarations.

   (imports    vl-importlist-p
               "Import statements for this module, like @('import foo::*').")

   (ports      vl-portlist-p
               "The module's ports list, i.e., @('a'), @('b'), and @('c') in
                @('module mod(a,b,c);').")

   (portdecls  vl-portdecllist-p
               "The input, output, and inout declarations for this module,
                e.g., @('input [3:0] a;').")

   (vardecls   vl-vardecllist-p
               "Wire and variable declarations like @('wire [3:0] w'), @('tri v'),
                @('reg [3:0] r;'), @('integer i;'), @('real foo;'), and so forth.")

   (paramdecls vl-paramdecllist-p
               "The parameter declarations for this module, e.g., @('parameter
                width = 1;').")

   (fundecls   vl-fundecllist-p
               "Function declarations like @('function f ...').")

   (taskdecls  vl-taskdecllist-p
               "Task declarations, e.g., @('task foo ...').")

   (assigns    vl-assignlist-p
               "Top-level continuous assignments like @('assign lhs = rhs;').")

   (aliases    vl-aliaslist-p
               "Wire aliases, @('alias lhs = rhs;')")

   (modinsts   vl-modinstlist-p
               "Instances of modules and user-defined primitives, e.g.,
                @('adder my_adder1 (...);').")

   (gateinsts  vl-gateinstlist-p
               "Instances of primitive gates, e.g., @('and (o, a, b);').")

   (alwayses   vl-alwayslist-p
               "Always blocks like @('always @(posedge clk) ...').")

   (initials   vl-initiallist-p
               "Initial blocks like @('initial begin ...').")

   (genvars    vl-genvarlist-p
               "Genvar declarations.")

   (generates vl-genelementlist-p
              "Generate blocks including generate regions and for/if/case blocks.")

   (atts       vl-atts-p
               "Any attributes associated with this top-level module.")

   (minloc     vl-location-p
               "Where we found the @('module') keyword for this module, i.e.,
                the start of this module's source code.")

   (maxloc     vl-location-p
               "Where we found the @('endmodule') keyword for this module, i.e.,
                the end of this module's source code.")

   (origname   stringp
               :rule-classes :type-prescription
               "Original name of the module from parse time.  Unlike the
                module's @('name'), this is meant to remain fixed throughout
                all simplifications.  That is, while a module named @('adder')
                might be renamed to @('adder$size=12') during @(see
                unparameterization), its origname will always be @('adder').
                The @('origname') is only intended to be used for display
                purposes such as hyperlinking.")

   (warnings   vl-warninglist-p
               "A @(see warnings) accumulator that stores any problems we have
                with this module.  Warnings are semantically meaningful only in
                that any <i>fatal</i> warning indicates the module is invalid
                and should not be discarded.  The list of warnings may be
                extended by any transformation or well-formedness check.")

   (comments   vl-commentmap-p
               "A map from locations to source-code comments that occurred in
                this module.  We expect that comments are never consulted for
                any semantic meaning.  This field is mainly intended for
                displaying the transformed module with comments preserved,
                e.g., see @(see vl-ppc-module).")

   (loaditems  vl-genelementlist-p
               "See @(see make-implicit-wires).  This is a temporary container
                to hold the module elements, in program order, until the rest
                of the design has been loaded.  This field is \"owned\" by the
                @('make-implicit-wires') transform.  You should never access it
                or modify it in any other code.")

   (esim       "This is meant to be @('nil') until @(see esim) conversion, at
                which point it becomes the E module corresponding to this
                VL module."))
  :extra-binder-names (hands-offp
                       ifports
                       modnamespace))

(fty::deflist vl-modulelist
  :elt-type vl-module-p
  :elementp-of-nil nil)

(define vl-module->hands-offp ((x vl-module-p))
  :returns hands-offp
  :parents (vl-module-p)
  :short "Attribute that says a module should not be transformed."

  :long "<p>We use the ordinary <see topic='@(url vl-atts-p)'>attribute</see>
@('VL_HANDS_OFF') to say that a module should not be changed by @(see
transforms).</p>

<p>This is generally meant for use in VL @(see primitives).  The Verilog
definitions of these modules sometimes make use of fancy Verilog constructs.
Normally our transforms would try to remove these constructs, replacing them
with instances of primitives.  This can lead to funny sorts of problems if we
try to transform the primitives themselves.</p>

<p>For instance, consider the @(see *vl-1-bit-delay-1*) module.  This module
has a delayed assignment, @('assign #1 out = in').  If we hit this module with
the @(see delayredux) transform, we'll try to replace the delay with an
explicit instance of @('VL_1_BIT_DELAY_1').  But that's crazy: now the module
is trying to instantiate itself!</p>

<p>Similar issues can arise from trying to replace the @('always') statements
in a primitive flop/latch with instances of flop/latch primitives, etc.  So as
a general rule, we mark the primitives with @('VL_HANDS_OFF') and code our
transforms to not modules with this attribute.</p>"
  :prepwork ((local (defthm alistp-when-atts-p
                      (implies (vl-atts-p x)
                               (alistp x))
                      :hints(("Goal" :in-theory (enable alistp))))))
  :inline t
  (consp (assoc-equal "VL_HANDS_OFF" (vl-module->atts x))))

(define vl-module->ifports
  :short "Collect just the interface ports for a module."
  ((x vl-module-p))
  :returns (ports (vl-interfaceportlist-p ports))
  (vl-collect-interface-ports (vl-module->ports x))
  ///
  (local (defthm vl-regularportlist-p-when-no-interface-ports
           (implies (and (not (vl-collect-interface-ports x))
                         (vl-portlist-p x))
                    (vl-regularportlist-p x))
           :hints(("Goal" :induct (len x)))))

  (defthm vl-regularportlist-p-when-no-module->ifports
    (implies (not (vl-module->ifports x))
             (vl-regularportlist-p (vl-module->ports x)))
    :hints(("Goal" :in-theory (enable vl-module->ifports)))))



(defprojection vl-modulelist->names ((x vl-modulelist-p))
  :returns (names string-listp)
  :parents (vl-modulelist-p)
  (vl-module->name x))

(defprojection vl-modulelist->paramdecls ((x vl-modulelist-p))
  :returns (paramdecl-lists vl-paramdecllist-list-p)
  :parents (vl-modulelist-p)
  (vl-module->paramdecls x))

(defmapappend vl-modulelist->modinsts (x)
  (vl-module->modinsts x)
  :parents (vl-modulelist-p)
  :guard (vl-modulelist-p x)
  :transform-true-list-p nil
  :rest ((defthm vl-modinstlist-p-of-vl-modulelist->modinsts
           (vl-modinstlist-p (vl-modulelist->modinsts x)))
         (deffixequiv vl-modulelist->modinsts :args ((x vl-modulelist-p)))))

(defprojection vl-modulelist->esims ((x vl-modulelist-p))
  :parents (vl-modulelist-p)
  (vl-module->esim x))


(defoption vl-maybe-module vl-module-p
  :short "Recognizer for an @(see vl-module-p) or @('nil')."
  ///
  (defthm type-when-vl-maybe-module-p
    (implies (vl-maybe-module-p x)
             (or (not x)
                 (consp x)))
    :hints(("Goal" :in-theory (enable vl-maybe-module-p)))
    :rule-classes :compound-recognizer))


(defenum vl-udpsymbol-p
  (:vl-udp-0
   :vl-udp-1
   :vl-udp-x
   :vl-udp-?
   :vl-udp-b
   :vl-udp--
   :vl-udp-*
   :vl-udp-r
   :vl-udp-f
   :vl-udp-p
   :vl-udp-n)
  :short "Symbols that can occur in a UDP table"
  :long "<p>These are basically taken from Verilog-2005 Table 8-1.</p>

<ul>

<li>@(':vl-udp-0') &mdash; logic 0.</li>

<li>@(':vl-udp-1') &mdash; logic 1.</li>

<li>@(':vl-udp-x') &mdash; unknown.  Permitted in input/outputs of all UDPs and
current state of sequential UDPs.</li>

<li>@(':vl-udp-?') &mdash; iteration of 0, 1, and X.  Not permitted in outputs.</li>

<li>@(':vl-udp-b') &mdash; iteration of 0 and 1.  Permitted in inputs of all
udps and current state of sequential udps, not in outputs.</li>

<li>@(':vl-udp--') &mdash; no change.  Permitted only in the output field of a
sequential UDP.</li>

<li>@(':vl-udp-*') &mdash; any value change on input, same as @('(??)').</li>

<li>@(':vl-udp-r') &mdash; rising edge on input, same as @('(01)').</li>

<li>@(':vl-udp-f') &mdash; falling edge on input, same as @('(10)').</li>

<li>@(':vl-udp-p') &mdash; any potential positive edge on the input, iteration of
                           @('(01)'), @('(0x)'), @('(x1)').</li>

<li>@(':vl-udp-n') &mdash; any potential negative edge on the input, iteration of
                           @('(10)'), @('(1x)'), @('(x0)').</li>

</ul>")

(defoption vl-maybe-udpsymbol
  vl-udpsymbol-p)

(defprod vl-udpedge
  :tag :vl-udplevel
  :layout :tree
  :short "Representation of an explicit edge that can occur in a UDP table,
e.g., @('(01)') or @('(1?)')."
  ((prev vl-udpsymbol-p)
   (next vl-udpsymbol-p)))

(define vl-udpentry-p (x)
  :short "Representation of any entry in a UDP table."
  :returns bool
  (mbe :logic
       (or (vl-udpsymbol-p x)
           (vl-udpedge-p x))
       :exec
       (if (consp x)
           (vl-udpedge-p x)
         (vl-udpsymbol-p x)))
  ///
  (defthm vl-udpentry-p-when-vl-udpsymbol-p
    (implies (vl-udpsymbol-p x)
             (vl-udpentry-p x)))
  (defthm vl-udpentry-p-when-vl-udpedge-p
    (implies (vl-udpedge-p x)
             (vl-udpentry-p x))))

(define vl-udpentry-fix (x)
  :parents (vl-udpentry-p)
  :returns (entry vl-udpentry-p)
  :inline t
  (if (vl-udpentry-p x)
      x
    :vl-udp-0)
  ///
  (defthm vl-udpentry-fix-when-vl-udpentry-p
    (implies (vl-udpentry-p x)
             (equal (vl-udpentry-fix x)
                    x))))

(deffixtype vl-udpentry
  :pred vl-udpentry-p
  :fix vl-udpentry-fix
  :equiv vl-udpentry-equiv
  :define t
  :forward t)

(fty::deflist vl-udpentrylist
  :elt-type vl-udpentry-p
  :elementp-of-nil nil)

(defprod vl-udpline
  :short "Representation of one line of a UDP table."
  :tag    :vl-udpline
  :layout :tree
  ((inputs  vl-udpentrylist-p
            "The input entries, i.e., whatever occurs before the first colon.")
   (output  vl-udpsymbol-p
            "The output value.")
   (current vl-maybe-udpsymbol-p
            "For sequential UDPs only: the current state.")))

(fty::deflist vl-udptable
  :elt-type vl-udpline-p
  :elementp-of-nil nil)

(defprod vl-udp
  :short "Representation of a user defined @('primitive')."
  :tag :vl-udp
  :layout :tree

  ((name        stringp :rule-classes :type-prescription
                "The name of this udp as a string.")

   (output      vl-portdecl-p
                "Declaration of the output port, which always comes first.")

   (inputs      vl-portdecllist-p
                "Port declarations for the input ports, in order.")

   (sequentialp booleanp
                "True when this is a sequential (instead of combinational) UDP.")

   (table       vl-udptable-p
                "The UDP state table.")

   (initval     vl-maybe-expr-p
                "For sequential UDPs, the initial value for the register, if specified.")

   (warnings    vl-warninglist-p)
   (minloc      vl-location-p)
   (maxloc      vl-location-p)
   (atts        vl-atts-p)
   (comments    vl-commentmap-p)))

(fty::deflist vl-udplist
  :elt-type vl-udp-p
  :elementp-of-nil nil)

(defprojection vl-udplist->names ((x vl-udplist-p))
  :parents (vl-udplist-p)
  :returns (names string-listp)
  (vl-udp->name x))


(defprod vl-config
  :short "Representation of a single @('config')."
  :tag :vl-config
  :layout :tree
  ((name stringp
         :rule-classes :type-prescription
         "The name of this config as a string.")
   ;; ...
   (warnings vl-warninglist-p)
   (minloc   vl-location-p)
   (maxloc   vl-location-p)
   (atts     vl-atts-p)
   (comments vl-commentmap-p))
  :long "BOZO incomplete stub -- we don't really support configs yet.")

(fty::deflist vl-configlist :elt-type vl-config-p
  :elementp-of-nil nil)

(defprojection vl-configlist->names ((x vl-configlist-p))
  :parents (vl-configlist-p)
  :returns (names string-listp)
  (vl-config->name x))


(defprod vl-package
  :short "Representation of a single @('package')."
  :tag :vl-package
  :layout :tree
  ((name stringp
         :rule-classes :type-prescription
         "The name of this package as a string.")
   (lifetime   vl-lifetime-p)
   (imports    vl-importlist-p)
   (fundecls   vl-fundecllist-p)
   (taskdecls  vl-taskdecllist-p)
   (typedefs   vl-typedeflist-p)
   (paramdecls vl-paramdecllist-p)
   (vardecls   vl-vardecllist-p)
   (warnings   vl-warninglist-p)
   (minloc     vl-location-p)
   (maxloc     vl-location-p)
   (atts       vl-atts-p)
   (comments   vl-commentmap-p))
  :long "<p>BOZO we haven't finished out all the things that can go inside of
packages.  Eventually there will be new fields here.</p>")

(fty::deflist vl-packagelist :elt-type vl-package-p
  :elementp-of-nil nil)

(defprojection vl-packagelist->names ((x vl-packagelist-p))
  :parents (vl-packagelist-p)
  :returns (names string-listp)
  (vl-package->name x))




(defprod vl-interface
  :short "Representation of a single @('interface')."
  :tag :vl-interface
  :layout :tree
  ((name stringp
         :rule-classes :type-prescription
         "The name of this interface as a string.")
   (ports      vl-portlist-p)
   (portdecls  vl-portdecllist-p)
   (paramdecls vl-paramdecllist-p)
   (vardecls   vl-vardecllist-p)
   (modports   vl-modportlist-p)
   (generates  vl-genelementlist-p)
   (imports    vl-importlist-p)
   ;; ...
   (warnings vl-warninglist-p)
   (minloc   vl-location-p)
   (maxloc   vl-location-p)
   (atts     vl-atts-p)
   (origname stringp :rule-classes :type-prescription)
   (comments vl-commentmap-p)

   (loaditems  vl-genelementlist-p
               "See @(see make-implicit-wires).  This is a temporary container
                to hold the module elements, in program order, until the rest
                of the design has been loaded."))

  :long "BOZO incomplete stub -- we don't really support interfaces yet."

  :extra-binder-names (ifports))

(fty::deflist vl-interfacelist :elt-type vl-interface-p
  :elementp-of-nil nil)

(defprojection vl-interfacelist->names ((x vl-interfacelist-p))
  :parents (vl-interfacelist-p)
  :returns (names string-listp)
  (vl-interface->name x))



(defprod vl-program
  :short "Representation of a single @('program')."
  :tag :vl-program
  :layout :tree
  ((name stringp
         :rule-classes :type-prescription
         "The name of this program as a string.")
   ;; ...
   (warnings vl-warninglist-p)
   (minloc   vl-location-p)
   (maxloc   vl-location-p)
   (atts     vl-atts-p)
   (comments vl-commentmap-p))
  :long "BOZO incomplete stub -- we don't really support programs yet.")

(fty::deflist vl-programlist :elt-type vl-program-p
  :elementp-of-nil nil)

(defprojection vl-programlist->names ((x vl-programlist-p))
  :parents (vl-programlist-p)
  :returns (names string-listp)
  (vl-program->name x))





(defprod vl-design
  :short "Top level representation of all modules, interfaces, programs, etc.,
resulting from parsing some Verilog source code."
  :tag :vl-design
  :layout :tree
  ((version    vl-syntaxversion-p "Version of VL syntax being used."
               :default *vl-current-syntax-version*)
   (mods       vl-modulelist-p    "List of all modules.")
   (udps       vl-udplist-p       "List of user defined primtives.")
   (interfaces vl-interfacelist-p "List of interfaces.")
   (programs   vl-programlist-p   "List of all programs.")
   (packages   vl-packagelist-p   "List of all packages.")
   (configs    vl-configlist-p    "List of configurations.")
   (vardecls   vl-vardecllist-p   "Top-level variable declarations.")
   (taskdecls  vl-taskdecllist-p  "Top-level task declarations.")
   (fundecls   vl-fundecllist-p   "Top-level function declarations.")
   (paramdecls vl-paramdecllist-p "Top-level (local and non-local) parameter declarations.")
   (imports    vl-importlist-p    "Top-level package import statements.")
   (fwdtypes   vl-fwdtypedeflist-p "Forward (incomplete) typedefs.")
   (typedefs   vl-typedeflist-p    "Regular (non-forward, complete) typedefs.")
   ;; BOZO lots of things still missing
   (warnings   vl-warninglist-p   "So-called \"floating\" warnings.")
   (comments   vl-commentmap-p    "So-called \"floating\" comments.")

   ))

(defoption vl-maybe-design vl-design-p)






;; BOZO these will have to move up at some point

(defenum vl-distweighttype-p
  (:vl-weight-each
   :vl-weight-total)
  :short "Representation of the @(':=') or @(':/') weight operators."
  :long "<p>See SystemVerilog-2012 Section 18.5.4, Distribution, and also see
@(see vl-distitem).</p>

<ul>

<li>@(':vl-weight-each') stands for the @(':=') operator, which assigns the
same weight to each item in the range.</li>

<li>@(':vl-weight-total') stands for the @(':/') operator, which assigns a
weight to the range as a whole, i.e., the weight of each value in the range
will become @('weight/n') where @('n') is the number of items in the
range.</li>

</ul>

<p>Both operators have the same meaning when applied to a single expression
instead of a range.</p>")

(defprod vl-distitem
  :short "Representation of weighted distribution information."
  :layout :tree
  :tag :vl-distitem

  ((left  vl-expr-p
          "The sole or left expression in a dist item.  For instance, @('left')
           will be @('100') in either @('100 := 1') or @('[100:102] := 1').")

   (right vl-maybe-expr-p
          "The right expression in a dist item that has a value range, or nil
           if this dist item just has a single item.  For instance, @('right')
           would be @('nil') in @('100 := 1'), but would be @('102') in
           @('[100:102] := 1').")

   (type  vl-distweighttype-p
          "The weight type, i.e., @(':vl-weight-each') for @(':=')-style dist items,
           or @(':vl-weight-total') for @(':/')-style dist items.  Note per
           SystemVerilog-2012 Section 18.5.4, if no weight is specified, the
           default weight is @(':= 1'), i.e., the default is
           @(':vl-weight-each').")

   (weight vl-expr-p
           "The weight, e.g., @('1') in @('100 := 1').  Note per
            SystemVerilog-2012 Section 18.5.4, if no weight is specified, the
            default weight is @(':= 1'), so the default weight is @('1')."))

  :long "<p>See SystemVerilog-2012 Section 18.5.4, Distribution.  This is our
representation of a single @('dist_item').  The associated grammar rules
are:</p>

@({
     dist_item ::= value_range [ dist_weight ]

     dist_weight ::= ':=' expression             ;; see vl-distweighttype-p
                   | ':/' expression

     value_range ::= expression
                   | [ expression : expression ]
})")

(fty::deflist vl-distlist
  :elt-type vl-distitem
  :elementp-of-nil nil)

(defprod vl-exprdist
  :short "Representation of @('expr dist { ... }') constructs."
  :tag :vl-exprdist
  :layout :tree
  ((expr vl-expr-p
         "The left-hand side expression, which per SystemVerilog-2012 Section
          18.5.4 should involve at least one @('rand') variable.")
   (dist vl-distlist-p
         "The desired ranges of values and probability distribution.")))

(defprod vl-cycledelayrange
  :short "Representation of cycle delay ranges in SystemVerilog sequences."
  :layout :tree
  :tag :vl-cycledelayrange

  ((left  vl-expr-p
          "The left-hand side expression.  Examples: @('left') is @('5') in @('##5'),
           @('10') in @('##[10:20]'), 0 in @('##[*]'), and 1 in @('##[+]').
           Supposed to be a constant expression that produces a non-negative
           integer value.")

   (right vl-maybe-expr-p
          "The right-hand side expression, if applicable.  Note that our
           expression representation allows us to directly represent @('$') as
           a @(see vl-keyguts) atom, so in case of ranges like @('##[1:$]'),
           @('right') is just the expression for @('$').  Other examples:
           @('right') is @('nil') in @('##5'), @('20') in @('##[10:20]'), @('$')
           in @('##[*]'), and @('$') in @('##[+]').  Supposed to be a constant
           expression that produces a non-negative integer value that is at
           least as large as @('left')."))

  :long "<p>See SystemVerilog-2012 Section 16.7.  This is essentially our
representation of the following grammar rules:</p>

@({
     cycle_delay_range ::= '##' constant_primary
                         | '##' '[' cycle_delay_const_range_expression ']'
                         | '##[*]'
                         | '##[+]'

     cycle_delay_const_range_expression ::= constant_expression ':' constant_expression
                                          | constant_expression ':' '$'
})

<p>Note (page 346) that the expressions here (constant_primary or
constant_expressions) are supposed to be determined at compile time and result
in nonnegative integer expressions.  The @('$') token means the end of
simulation, or for formal verification tools indicates a finite but unbounded
range.  The right-hand side expression is supposed to be greater than or equal
to the left-hand side expression.</p>

<p>Some of this syntax is unnecessary:</p>

<ul>
<li>The syntax @('##[*]') just means @('##[0:$]')</li>
<li>The syntax @('##[+]') just means @('##[1:$]')</li>
</ul>

<p>Accordingly in our internal representation we don't bother with these, but
instead just translate them into @('0,$') or @('1,$') ranges.</p>")


(defenum vl-repetitiontype-p
  (:vl-repetition-consecutive
   :vl-repetition-goto
   :vl-repetition-nonconsecutive)
  :short "Representation of SystemVerilog assertion sequence repetition types,
i.e., @('[*...]'), @('[->...]'), or @('[=...]') style repetition."
  :long "<p>See SystemVerilog-2012 Section 16.9.2.</p>

<ul>
<li>@('[* ...]'), @('[*]'), and @('[+]') is called <b>consecutive</b> repetition</li>
<li>@('[-> ...]') is called <b>goto</b> repetition</li>
<li>@('[= ...]') is called <b>nonconsecutive</b> repetition</li>
</ul>")

(defprod vl-repetition
  :short "Representation of a SystemVerilog assertion sequence repetition."
  :tag :vl-repetition
  :layout :tree

  ((type vl-repetitiontype-p
         "Kind of repetition, i.e., consecutive, goto, or nonconsecutive.")

   (left vl-expr-p
         "Sole or left bound on the repetition.  Examples: @('left') is 3 for
          any of @('[* 3]'),
                 @('[* 3:4]'),
                 @('[-> 3]'),
                 @('[-> 3:4]'),
                 @('[= 3]'), or
                 @('[= 3:4]').
          In the special cases of @('[*]') and @('[+]'), @('left') should be
          0 and 1, respectively.")

   (right vl-maybe-expr-p
          "Right bound on the repetition if applicable.  For instance,
           @('right') is
                 @('nil') for any of @('[* 3]'),
                                     @('[-> 3]'), or
                                     @('[= 3]').
           It is @('4') for any of @('[* 3:4]'),
                                   @('[-> 3:4]'), or
                                   @('[= 3:4]').
           It is @('$') for @('[*]') or @('[+]')."))

  :long "<p>See SystemVerilog-2012 Section 16.9.2.</p>

<p>Note from Page 357 that @('[*]') is equivalent to @('[0:$]') and @('[+]') is
equivalent to @('[1:$]'), so we don't bother with separate representations of
these.</p>")
