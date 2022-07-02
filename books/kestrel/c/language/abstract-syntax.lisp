; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "kestrel/fty/defset" :dir :system)

; to generate more typed list theorems:
(local (include-book "std/lists/append" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax
  :parents (language)
  :short "A preliminary abstract syntax of C."
  :long
  (xdoc::topstring
   (xdoc::p
    "This abstract syntax is preliminary in the sense that
     it is neither general nor complete.
     It is not general because it assumes the use of ASCII characters.
     which is not necessarily the case according to [C].
     It is not complete because it does not cover all the C constructs.
     Nonetheless, it covers a useful and interesting subset of C,
     with the ASCII assumption being largely supported
     (as part of perhaps a larger character set like Unicode).")
   (xdoc::p
    "We plan to generalize and extend this abstract syntax
     to not make specific assumptions and to cover all the C constructs.
     In particular, we plan to use the formalization of "
    (xdoc::seetopic "character-sets" "character sets")
    " to lift the ASCII assumption.")
   (xdoc::p
    "This abstract syntax models C code after preprocessing.
     As part of a more comprehensive formalization of C,
     we also plan to formalize abstract syntax before preprocessing,
     and in fact to formalize the translation phases [C:5.1.1.2] in detail."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod ident
  :short "Fixtype of identifiers [C:6.4.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we represent C identifiers as ACL2 strings,
     which suffice to represent all the ASCII C identifiers.
     We wrap ACL2 strings into a one-field product fixtype
     to make it easier to modify or extend this fixtype in the future.")
   (xdoc::p
    "Unconstrained ACL2 strings may not be valid C ASCII identifiers.
     In the future we may extend this fixtype
     with suitable restrictions on the ACL2 string.")
   (xdoc::p
    "A C implementation may limit
     the number of significant characters in identifiers
     [C:6.4.2.1/5] [C:6.4.2.1/6] [C:5.2.4.1],
     to 31 for external identifiers and 63 for internal identifiers.
     In the future, we may add this constraint to this fixtype."))
  ((name string))
  :tag :ident
  :pred identp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist ident-list
  :short "Fixtype of lists of identifiers."
  :elt-type ident
  :true-listp t
  :elementp-of-nil nil
  :pred ident-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset ident-set
  :short "Fixtype of osets of identifiers."
  :elt-type ident
  :elementp-of-nil nil
  :pred ident-setp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum iconst-base
  :short "Fixtype of bases of integer constants [C:6.4.4.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Decimal (base 10), octal (base 8), and hexadecimal (base 16)
     integer constants are supported in C.
     This fixtype captures these three possible bases."))
  (:dec ())
  (:oct ())
  (:hex ())
  :pred iconst-basep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum iconst-length
  :short "Fixtype of lengths of integer constants [C:6.4.4.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "An integer constant may have
     (i) an @('l') or @('L') suffix,
     or (ii) an @('ll') or @('LL') suffix,
     or (iii) no such suffix.
     This fixtype captures these three possibilities,
     without distinguishing between the lowercase and uppercase variants
     (given the similarity between `l' and `1' and `I' in many fonts,
     it could be argued that one should always use the uppercase variants,
     as recommended in the Java language specification for Java).")
   (xdoc::p
    "Since the grammar in [C] refers to these as <i>long-suffix</i>,
     it seems appropriate to call these the `length' of an integer constant,
     which justifies the name of this fixtype."))
  (:none ())
  (:long ())
  (:llong ())
  :pred iconst-lengthp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod iconst
  :short "Fixtype of integer constants [C:6.4.4.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we define a C integer constants as consisting of
     a natural number, a base, an unsigned flag, and a length suffix.
     While this does not cover every syntactic aspect of an integer constant,
     it covers the important ones.")
   (xdoc::p
    "The natural number is the value.
     In base 10, the value has a unique syntactic representation,
     because it is required to start with no 0.
     In C, @('0') is always an octal integer constant,
     so our abstract syntax here captures a bit more,
     namely a decimal integer constant 0 that does not exist in C.
     This is not an issue for now,
     because our pretty-printer turns that into @('0')
     in the same way as if it were octal.")
   (xdoc::p
    "In base 8, the value has a unique syntactic representation
     if we assume exactly one leading 0,
     which is not a significant limitation.")
   (xdoc::p
    "In base 16, the value has a unique syntactc representation
     if we assume no leading 0s and either lowercase or uppercase letters
     (i.e. we do not capture the difference between
     the hexadecimal digits @('a') and @('A')).
     We also do not capture the distinction between
     the hexadecimal prefixes @('0x') and @('0X').")
   (xdoc::p
    "We do not capture the distinction between the @('u') and @('U'),
     which is not very important."))
  ((value nat)
   (base iconst-base)
   (unsignedp bool)
   (length iconst-length))
  :tag :iconst
  :pred iconstp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption iconst-option
  iconst
  :short "Fixtype of optional integer constants."
  :pred iconst-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum const
  :short "Fixtype of constants [C:6.4.4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only capture integer and enumeration constants,
     but we include placeholders for floating and character constants.")
   (xdoc::p
    "The C grammar for enumeration constants [C:6.4.4.3/1] [C:6.4.4/1]
     is actually ambiguous in expressions [C:6.5.1/1]:
     an identifier that appears where an expression is expected
     could be either a primary expression identifier (e.g. denoting an object)
     or an enumeration constant.
     The two cases cannot be disambiguated during parsing,
     as they need to take into account static semantic constraints.")
   (xdoc::p
    "Despite this ambiguity,
     for now we keep enumeration constants in this abstract syntax.
     In a future extension of our formalization of C,
     concrete syntax could be parsed
     into abstract syntax without enumeration constants,
     and then the static semantics could turn some identifier expressions
     into enumeration constants,
     according to the static semantics constraints.
     Alternatively, in the future we may remove enumeration constants from here,
     and just use identifiers in expressions,
     which may denote either enumeration constants or other things."))
  (:int ((get iconst)))
  (:float ())
  (:enum ((get ident)))
  (:char ())
  :pred constp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum tyspecseq
  :short "Fixtype of sequences of type specifiers [C:6.7.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A sequence of one or more type specifiers in a declaration
     specifies a type.
     The allowed sequences are described in [C:6.7.2].
     This fixtype captures (some of) these sequences.")
   (xdoc::p
    "We capture type specifier sequences for
     the @('void') type,
     the plain @('char') type,
     the standard signed and unsigned integer types (which include @('_Bool')),
     the (real and complex) floating types,
     limited forms of structure, union, and enumeration types,
     and type definition names.
     Complex floating types are not supported by all implementations;
     we include them in the abstract syntax,
     because it must suffice to represent all implementations,
     but they can be used only if supported.")
   (xdoc::p
    "The form of structure, union, and enumeration types is limited
     to the case of a single identifier (i.e. tag) [C:6.7.2.1] [C:6.7.2.2],
     without members or enumerators.
     Syntactically, declarations that define
     (members of) structure and union types
     and (enumerators) of enumeration types
     are also type specifiers.
     But we capture them elsewhere in our abstract syntax.
     We use @('tyspecseq') only for parts of the code
     that reference existing types,
     not that introduce them.
     In that context, there is a distinction between
     defining a structure type and merely referencing it.")
   (xdoc::p
    "We do not capture atomic type specifiers for now.
     These involve additional syntactic complexities,
     as they contain type names,
     which are defined below to depend on type specifier sequences;
     so adding atomic type specifiers would introduce a mutual recursion
     in the definition of these fixtypes,
     which is doable but can perhaps be avoided for a while,
     until we actually need atomic type specifiers.")
   (xdoc::p
    "This @('tyspecseq') fixtype has one constructor
     for each item in the list in [C:6.7.2/2],
     where different items are different types
     (syntactically speaking,
     as type definition names may be equal to other types).
     Each item in that list lists one of more sequences,
     meant to represent multisets, i.e. where order does not matter.
     We capture all the possible multisets for each item,
     via boolean fields that say whether
     elements of a sequence are present or absent:
     for example, @('(make-tyspecseq-sshort :signed t :int nil)')
     represents @('signed short');
     see the pretty-printer for details.
     However, we do not capture
     different sequentializations of the same multiset,
     e.g. we capture @('signed short') but not @('short signed').
     We capture the sequences listed in [C:6.7.2/2]
     that represent the multiset.
     Arguably, those are the sequences that should always be used,
     despite other equivalent sequences being allowed.")
   (xdoc::p
    "The type specifiers in a declaration
     may be intermixed with other declaration specifiers [C:6.7/1] [C:6.7.2/2]
     (e.g. one could write @('unsigned auto int x = 1;')),
     so long as their sequence (ignoring any intermixed non-type specifiers)
     is valid according to [C:6.7.2/2].
     This intermixing is probably best avoided,
     so our abstract syntax does not allow it:
     our type specifier sequences are meant to be contiguous."))
  (:void ())
  (:char ())
  (:schar ())
  (:uchar ())
  (:sshort ((signed bool)
            (int bool)))
  (:ushort ((int bool)))
  (:sint ((signed bool :reqfix (if (not int) t signed))
          (int bool :reqfix (if (not signed) t int)))
   :require (or signed int))
  (:uint ((int bool)))
  (:slong ((signed bool)
           (int bool)))
  (:ulong ((int bool)))
  (:sllong ((signed bool)
            (int bool)))
  (:ullong ((int bool)))
  (:bool ())
  (:float ((complex bool)))
  (:double ((complex bool)))
  (:ldouble ((complex bool)))
  (:struct ((tag ident)))
  (:union ((tag ident)))
  (:enum ((tag ident)))
  (:typedef ((name ident)))
  :pred tyspecseqp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist tyspecseq-list
  :short "Fixtype of lists of sequences of type specifiers."
  :elt-type tyspecseq
  :true-listp t
  :elementp-of-nil nil
  :pred tyspecseq-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption tyspecseq-option
  tyspecseq
  :short "Fixtype of optional sequences of type specifiers."
  :pred tyspecseq-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum obj-declor
  :short "Fixtype of object declarators [C:6.7.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are declarators for objects.
     [C] does not have a separate syntactic category for them,
     but in our abstract syntax for now
     we differentiate them from other kinds of declarators.")
   (xdoc::p
    "For now we only capture three kinds of object declarators:
     (i) a direct declarator consisting of a single identifier;
     (ii) a pointer declarator consisting of
     the pointer notation @('*')
     and (recursively) an object declarator; and
     (iii) an array (direct) declarator consisting of
     an object declarator (recursively)
     and the array notation @('[]') with
     either nothing in it (i.e. unspecified size)
     or an integer constant in it (i.e. specified size).
     Using an integer constant as size is less general than [C] allows,
     but it suffices for now.")
   (xdoc::p
    "Note that we can represent sequences of pointer notations @('* ... *')
     by nesting the @(':pointer') constructor.
     Note also that a direct declarator may be a (parenthesized) declarator,
     but in our abstract syntax we just have declarators,
     which we can nest under the @(':array') constructor,
     so we do not need to represent parentheses explicitly."))
  (:ident ((get ident)))
  (:pointer ((decl obj-declor)))
  (:array ((decl obj-declor)
           (size iconst-option)))
  :pred obj-declorp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum obj-adeclor
  :short "Fixtype of abstract object declarators [C:6.7.7]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are abstract declarators for objects.
     [C] does not have a separate syntactic category for them,
     but in our abstract syntax it is useful
     to differentiate them from other kinds of abstract declarators.")
   (xdoc::p
    "For now we only capture three kinds of abstract object declarators,
     corresponding to the (non-abstract) object declarators
     captured in @(tsee obj-declor):
     an abstract declarator is like a declarator without the identifier.
     Abstract declarators are used in type names,
     which are like declarations without identifiers [C:6.7.7/2].")
   (xdoc::p
    "From a point of view,
     it may seem strange to have an explicit value, in this fixtype,
     for no abstract object declarator,
     since the fixtype should consist of abstract object declarators.
     However, this modeling choice is justified by
     the correspondence between abstract declarators and declarators
     explained just above."))
  (:none ())
  (:pointer ((decl obj-adeclor)))
  (:array ((decl obj-adeclor)
           (size iconst-option)))
  :pred obj-adeclorp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod tyname
  :short "Fixtype of type names [C:6.7.7]."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only capture type names consisting of
     the type specifier sequences captured by @(tsee tyspecseq)
     and the abstract object declarators captures by @(tsee obj-adeclor)."))
  ((tyspec tyspecseq)
   (declor obj-adeclor))
  :tag :tyname
  :pred tynamep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist tyname-list
  :short "Fixtype of lists of type names."
  :elt-type tyname
  :true-listp t
  :elementp-of-nil nil
  :pred tyname-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum unop
  :short "Fixtype of unary operators [C:6.5.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We capture all of them:
     address,
     indirection,
     unary plus,
     unary minus,
     bitwise negation/complement,
     and logical negation/complement.")
   (xdoc::p
    "Note that preincrement @('++') and predecrement @('--')
     are not considered unary operators in the C grammar [C:6.5.3/1],
     even though preincrement and predecrement expressions
     are considered unary expressions,
     along with others with the @('sizeof') and @('_Alignof') operators,
     and even though the title of [C:6.5.3] is `Unary Operators'.
     We may include all those operators into this fixtype,
     since it makes sense from the point of view of the abstract syntax."))
  (:address ())
  (:indir ())
  (:plus ())
  (:minus ())
  (:bitnot ())
  (:lognot ())
  :pred unopp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist unop-list
  :short "Fixtype of lists of unary operators."
  :elt-type unop
  :true-listp t
  :elementp-of-nil nil
  :pred unop-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum binop
  :short "Fixtype of binary operators [C:6.5.5-14] [C:6.5.16]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We capture all of them; they all take and return integers
     (along with values of other types).
     The C grammar does not have a nonterminal for binary operators
     (it has one for unary operators [C:6.5.3]),
     but the grammar rules for binary operations implicitly describe them.")
   (xdoc::p
    "These are
     multiplication,
     division,
     remainder,
     addition,
     subtraction,
     shift (left and right),
     relations (less than (or equal to) and greater than (or equal to)),
     equality (and non-equality),
     bitwise conjunction,
     bitwise exclusive disjunction,
     bitwise inclusive disjunction,
     logical conjunction,
     logical disjunction,
     assignment (simple and compound)."))
  (:mul ())
  (:div ())
  (:rem ())
  (:add ())
  (:sub ())
  (:shl ())
  (:shr ())
  (:lt ())
  (:gt ())
  (:le ())
  (:ge ())
  (:eq ())
  (:ne ())
  (:bitand ())
  (:bitxor ())
  (:bitior ())
  (:logand ())
  (:logor ())
  (:asg ())
  (:asg-mul ())
  (:asg-div ())
  (:asg-rem ())
  (:asg-add ())
  (:asg-sub ())
  (:asg-shl ())
  (:asg-shr ())
  (:asg-and ())
  (:asg-xor ())
  (:asg-ior ())
  :pred binopp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist binop-list
  :short "Fixtype of lists of binary operators."
  :elt-type binop
  :true-listp t
  :elementp-of-nil nil
  :pred binop-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes expr-fixtypes
  :short "Mutually recursive fixtypes for expressions."

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum expr
    :parents (atc-abstract-syntax expr-fixtypes)
    :short "Fixtype of expressions [C:6.5]."
    :long
    (xdoc::topstring
     (xdoc::p
      "For now, we only cover some of the primary expressions [C:6.5.1],
       namely identifiers and constants.
       String literals will be covered later.
       Generic selections may be covered eventually, if needed.
       Parenthesized expression are implicitly covered in the abstract syntax,
       whose structure provides the grouping.")
     (xdoc::p
      "Of the postfix expressions [C:6.5.2],
       for now we only cover
       array subscripting,
       function calls (where we limit the function to be an identifier),
       structure and union member access
       (both forms: @('.') directly on structures and unions,
       as well as @('->') on pointers to structures and unions),
       and post-increment/decrement.
       Richer expressions for functions in function calls
       (e.g. function pointers)
       will be added if/when needed.
       Compound literals will be added as needed.")
     (xdoc::p
      "Of the unary expressions [C:6.5.3],
       for now we only cover pre-increment/decrement,
       and the ones built with the unary operators.
       Note that the grammar in [C] does not define as unary operators
       all the operators of unary expressions,
       e.g. @('++') is not a unary operator grammatically.
       We follow that here, but use @(':unary') as the tag for
       the expressions built with the unary operators in @(tsee unop).
       We will cover @('sizeof') later.
       We will cover @('_Alignof') if needed.")
     (xdoc::p
      "We include cast expressions,
       but only with the currently limited type names
       captured by @(tsee tyname).")
     (xdoc::p
      "We use a general notion of binary expression to represent
       multiplicative [C:6.5.5],
       additive [C:6.5.6],
       shift [C:6.5.7],
       relational [C:6.5.8],
       equality [C:6.5.9],
       bitwise conjunction [C:6.5.10],
       bitwise exclusive disjunction [C:6.5.11],
       bitwise inclusive disjunction [C:6.5.12],
       logical conjunction [C:6.5.13],
       logical disjunction [C:6.5.14], and
       assigment [C:6.5.16]
       expressions.
       The grammar in [C] classifies these as different kinds of expressions
       also in order to capture the precedences among the various operators;
       however, in an abstract syntax, this is not necessary.")
     (xdoc::p
      "We include ternary conditional expressions.")
     (xdoc::p
      "We do not include the comma operator.
       It will be easy to include, if needed."))
    (:ident ((get ident)))
    (:const ((get const)))
    (:arrsub ((arr expr) (sub expr)))
    (:call ((fun ident)
            (args expr-list)))
    (:member ((target expr)
              (name ident)))
    (:memberp ((target expr)
               (name ident)))
    (:postinc ((arg expr)))
    (:postdec ((arg expr)))
    (:preinc ((arg expr)))
    (:predec ((arg expr)))
    (:unary ((op unop) (arg expr)))
    (:cast ((type tyname)
            (arg expr)))
    (:binary ((op binop)
              (arg1 expr)
              (arg2 expr)))
    (:cond ((test expr)
            (then expr)
            (else expr)))
    :pred exprp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deflist expr-list
    :short "Fixtype of lists of expressions."
    :elt-type expr
    :true-listp t
    :elementp-of-nil nil
    :pred expr-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption expr-option
  expr
  :short "Fixtype of optional expressions."
  :pred expr-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod struct-declon
  :short "Fixtype of structure declarations [C:6.7.2.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are used inside structure and union specifiers:
     they do not declare structure types, but rather their members.
     (A better name for these could be `member declarations',
     but we follow [C] of course.)")
   (xdoc::p
    "For now we only capture structure declarations that consist of
     a type specifier sequence
     and a structure declarator that is an object declarator.
     We do not capture static assertions.
     We do not capture bit field sizes."))
  ((tyspec tyspecseq)
   (declor obj-declor))
  :tag :struct-declon
  :pred struct-declonp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist struct-declon-list
  :short "Fixtype of lists of structure declarations."
  :elt-type struct-declon
  :true-listp t
  :elementp-of-nil nil
  :pred struct-declon-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum tag-declon
  :short "Fixtype of declarations of structure, union, and enumeration types
          [C:6.7.2.1] [C:6.7.2.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are declarations that consists of
     single structure, union, and enumeration specifiers,
     which introduce structure, union, and enumeration types.
     These kinds of types are all identified by tags [C:6.2.3],
     which justifies our choice of name for this fixtype.")
   (xdoc::p
    "These are declarations that include
     the structure or union members,
     or the enumerators (which are identifiers).
     That is, these tag declarations introduce the type with that tag.
     We only model structure and union members
     of the form discussed in @(tsee struct-declon);
     we only model enumerators that are single identifiers,
     without bindings to constant expressions."))
  (:struct ((tag ident)
            (members struct-declon-list)))
  (:union ((tag ident)
           (members struct-declon-list)))
  (:enum ((tag ident)
          (enumerators ident-list)))
  :pred tag-declonp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod param-declon
  :short "Fixtype of parameter declarations [C:6.7.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are used as part of function declarators,
     to specify the parameters of a function.")
   (xdoc::p
    "We only support parameter declarations consisting of
     type specifier sequences and object declarators.
     This also implies that we only use named function parameters
     (i.e. no abstract declarators)."))
  ((tyspec tyspecseq)
   (declor obj-declor))
  :tag :param-declon
  :pred param-declonp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist param-declon-list
  :short "Fixtype of lists of parameter declarations."
  :elt-type param-declon
  :true-listp t
  :elementp-of-nil nil
  :pred param-declon-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum fun-declor
  :short "Fixtype of function declarators [C:6.7.6]."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only model function declarators [C:6.7.6.3]
     consisting of an identifier as the direct declarator
     and a (parenthesized) list of parameter declarations,
     preceded by zero or more pointer designations (i.e. @('*')).
     The pointer designations are captured via a recursive structure,
     which makes this fixtype more extensible in the future.")
   (xdoc::p
    "This is somewhat similar to @(tsee obj-declor),
     except that there is an identifier and a list of parameters
     instead of just an identifier (for the base case of the fixtype),
     and except that there is no array designation possible.
     The latter is because functions cannot return array types [C:6.7.6.3/1]."))
  (:base ((name ident)
          (params param-declon-list)))
  (:pointer ((decl fun-declor)))
  :pred fun-declorp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum fun-adeclor
  :short "Fixtype of abstract function declarators [C:6.7.7]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The relation between this fixtype and @(tsee fun-declor)
     is analogous to the one between @(tsee obj-adeclor) and @(tsee obj-declor).
     Namely, an abstract function declarator is
     a function declarator without the name."))
  (:base ((params param-declon-list)))
  (:pointer ((decl fun-adeclor)))
  :pred fun-adeclorp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod fun-declon
  :short "Fixtype of function declarations [C:6.7]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A function declaration consists of
     a type specifier sequence
     and a function declarator."))
  ((tyspec tyspecseq)
   (declor fun-declor))
  :tag :fun-declon
  :pred fun-declonp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum initer
  :short "Fixtype of initializers [C:6.7.9]."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only model initializers tht consists of
     either a single expression or a list of expressions,
     where the latter models a list between curly braces
     of initializers consisting of single expressions.
     Note that, since currently we do not model the comma operator,
     our use of any expressions here
     matches the use of assignment expressions in [C]."))
  (:single ((get expr)))
  (:list ((get expr-list)))
  :pred initerp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod obj-declon
  :short "Fixtype of object declarations [C:6.7]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are declarations for objects.
     [C] does not have a separate syntactic category for them,
     but in our abstract syntax it is useful
     to differentiate them from other kinds of declarators.")
   (xdoc::p
    "For now we define an object declaration as consisting of
     a type specification sequence,
     an object declarator,
     and an initializer.
     We could easily make the initializer optional for greater generality.")
   (xdoc::p
    "For now we model
     no storage class specifiers
     no type qualifiers,
     no function specifiers,
     and no alignment specifiers.")
   (xdoc::p
    "An object declaration as defined here is like
     a parameter declaration (as defined in our abstract syntax)
     with an initializer."))
  ((tyspec tyspecseq)
   (declor obj-declor)
   (init initerp))
  :tag :obj-declon
  :pred obj-declonp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum label
  :short "Fixtype of labels of labeled statements [C:6.8.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the entities on the left of the colon in a labeled statement.
     For now we do not capture the restriction that
     the expression after a @('case') is constant;
     we may formalize, and use here, the notion of constant expression later.")
   (xdoc::p
    "We cannot use @(':case') for the @('case') label,
     because the generated constructor @('label-case')
     would conflict with the generated macro @('label-case');
     so we use @(':cas') instead."))
  (:name ((get ident)))
  (:cas ((get expr)))
  (:default ())
  :pred labelp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes stmt-fixtypes
  :short "Mutually recursive fixtypes for statements (and blocks)."

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum stmt
    :short "Fixtype of statements [C:6.8]."
    :long
    (xdoc::topstring
     (xdoc::p
      "We capture almost all the statements:
       labeled [C:6.8.1],
       compound [C:6.8.2],
       expression and null [C:6.8.3],
       selection [C:6.8.4],
       iteration [C:6.8.5] (with the limitation explained below),
       and jump [C:6.8.6].
       We do not allow declarations in @('for') statements for now;
       we will add that later."))
    (:labeled ((label label)
               (body stmt)))
    (:compound ((items block-item-list)))
    (:expr ((get expr)))
    (:null ())
    (:if ((test expr)
          (then stmt)))
    (:ifelse ((test expr)
              (then stmt)
              (else stmt)))
    (:switch ((ctrl expr)
              (body stmt)))
    (:while ((test expr)
             (body stmt)))
    (:dowhile ((body stmt)
               (test expr)))
    (:for ((init expr-option)
           (test expr-option)
           (next expr-option)
           (body stmt)))
    (:goto ((target ident)))
    (:continue ())
    (:break ())
    (:return ((value expr-option)))
    :pred stmtp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum block-item
    :short "Fixtype of block items [C:6.8.2]."
    :long
    (xdoc::topstring
     (xdoc::p
      "These are declarations and statements.")
     (xdoc::p
      "We limit declarations to object declarations for now."))
    (:declon ((get obj-declon)))
    (:stmt ((get stmt)))
    :pred block-itemp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (fty::deflist block-item-list
    :short "Fixtype of lists of block items."
    :elt-type block-item
    :true-listp t
    :elementp-of-nil nil
    :pred block-item-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption stmt-option
  stmt
  :short "Fixtype of optional statements."
  :pred stmt-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod fundef
  :short "Fixtype of function definitions [C:6.9.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We model a function definition as consisting of
     a type specifier sequence,
     a function declarator,
     and a body.
     With respect to [C:6.9.1/1],
     the type specifier sequence are the declaration specifiers,
     the function declarator is the declarator,
     and the body is the compound statement.
     We do not model function definitions with parameter names
     and separate declarations for them before the body.")
   (xdoc::p
    "Since the body of a function definition must be a compound statement,
     we formalize the body as
     the list of block items that form the compound statement.")
   (xdoc::p
    "Since a function declaration consists of
     a type specifier sequence and a function declarator,
     this product fixtype of function definitions is isomorphic to
     a product fixtype of a function declaration and a body.
     However, even though this would work in abstract syntax,
     in concrete syntax a function declaration has to end with a semicolon
     (and that is why the grammar rule in [C:6.9.1/1]
     does not use a declaration, but rather its components)."))
  ((tyspec tyspecseq)
   (declor fun-declor)
   (body block-item-list))
  :tag :fundef
  :pred fundefp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist fundef-list
  :short "Fixtype of lists of function definitions."
  :elt-type fundef
  :true-listp t
  :elementp-of-nil nil
  :pred fundef-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum ext-declon
  :short "Fixtype of external declarations [C:6.9]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We support declarations for objects
     and tags (i.e. structure, union, and enumeration types."))
  (:fundef ((get fundef)))
  (:obj-declon ((get obj-declon)))
  (:tag-declon ((get tag-declon)))
  :pred ext-declonp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist ext-declon-list
  :short "Fixtype of lists of external declarations."
  :elt-type ext-declon
  :true-listp t
  :elementp-of-nil nil
  :pred ext-declon-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod transunit
  :short "Fixtype of translation units [C:6.9]."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of a list of external declarations
     (which should be non-empty according to the grammar in [C],
     but we will capture this constraint later or elsewhere).
     We create this one-field product fixtype
     so that in the future it may be easier to extend this fixtype
     with more information if needed."))
  ((declons ext-declon-list))
  :tag :transunit
  :pred transunitp)
