; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "preprocessor-lexemes")

(local (include-book "kestrel/utilities/nfix" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ preprocessor-files
  :parents (preprocessor)
  :short "An abstract syntax for preprocessor files."
  :long
  (xdoc::topstring
   (xdoc::p
    "The C grammar defines a notion of preprocessing files [C17:6.10/1],
     which is also captured in our ABNF @(see grammar).
     To facilitate a planned extension of our approach to "
    (xdoc::seetopic "preservable-inclusions"
                    "preserve @('#include') directives")
    ", we introduce an abstract syntax for preprocessor files,
     where we use `preprocessor' instead of `preprocessing'
     for consistency with the naming of other parts of our preprocessor.")
   (xdoc::p
    "This abstract syntax is mainly concerned with conditionals
     (i.e. @('#if') etc.) and their nested structure."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum pexpr
  :short "Fixtype of preprocessor expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define ASTs for the constant expressions
     in @('#if') and @('#elif') directives [C17:6.10.1].
     These are similar to @(tsee expr) in our full abstract syntax:
     see that fixtype along with this one.
     We represent integer constant expressions [C17:6.6/6],
     with modifications motivated by the fact that we are preprocessing.
     [C17:6.6/6] does not give a completely precise definition;
     we discuss and motivate our choices below.")
   (xdoc::p
    "We represent integer constants as preprocessing numbers:
     we elaborate preprocessing numbers into integer constants
     (if they can be elaborated as such)
     during evaluation, after parsing.")
   (xdoc::p
    "Although [C17:6.6/6] allows floating constants
     as immediate operands of casts (to integer types, presumably),
     this does not seem to apply to the preprocessor.
     The preprocessor does not really know about types and casts.
     Indeed, both GCC and Clang fail when attempting to use
     a cast of a floating constant, or any cast in fact,
     as the expression of a conditional.
     Thus, we exclude floating constants.")
   (xdoc::p
    "We have a separate fixtype summand for character constants.
     These are explicitly called for in [C17:6.10.1/4], see footnote 171.")
   (xdoc::p
    "Unlike @(tsee expr), there are no enumeration constants here:
     they are just identifiers at this point,
     which are turned into @('0') [C17:6.10.1/4] during parsing.")
   (xdoc::p
    "We include no string literals, since they do not have integer types.")
   (xdoc::p
    "Although parenthesized expressions are not needed for evaluation,
     we include them to facilitate their subsequent printing to files:
     since we do not modify the expressions after parsing,
     re-printing them inclusive of parentheses does not disrupt precedences.")
   (xdoc::p
    "Since the only allowed operands are numbers and characters [C17:6.6/6],
     it seems reasonable to exclude operations that require
     lvalues or pointer values or aggregate values.
     This excludes compound literals,
     array subscript operations,
     and structure/union member access;
     among the unary operators, it excludes @('&') and @('*');
     among the binary operators, it excludes all forms of assignment.
     Instead of using subtypes of @(tsee unop) and @(tsee binop),
     we spell out the allowed unary and binary operators
     as separate fixtype summands.")
   (xdoc::p
    "Perhaps somewhat inconsistently with [C17:6.6/6],
     [C17:6.6/3] allows for certain kinds of expressions
     to occur only in sub-expressions that are not evaluated.
     We omit them completely for now, to keep things simpler;
     we will add support for them later if needed.
     These are the unary operators that take lvalues (increment and decrement),
     the assignment operators (simple and compound),
     function calls,
     and comma expressions.")
   (xdoc::p
    "Note also that the comma operator is excluded at the top level
     by the fact the grammar rule for constant expressions says that
     they are conditional expressions [C17:6.6/1].")
   (xdoc::p
    "Although [C17:6.6/6] explictly calls out @('sizeof') and @('_Alignof'),
     both GCC and Clang reject them,
     which makes sense because the preprocessor
     does not really know about types.")
   (xdoc::p
    "Although [C17:6.6/6] explicitly calls out casts,
     both GCC and Clang reject them, as mentioned earlier.")
   (xdoc::p
    "Neither [C17:6.10.1] nor [C17:6.6/6] mention generic selections.
     Both GCC and Clang reject them.
     This makes sense because the preprocessor
     does not really know about types.")
   (xdoc::p
    "We avoid any GCC or Clang extensions for now.")
   (xdoc::p
    "Unlike @(tsee expr), there is no need to include ambiguous expressions.
     Those only arise when certain identifiers
     may ambiguously denote variables or types,
     but there are no identifiers here.")
   (xdoc::p
    "There is an additional kind of expression here, not found in @(tsee expr),
     namely the @('defined') operator [C17:6.10.1/1].")
   (xdoc::p
    "Unlike other parts of preprocessing file ASTs,
     we do not include any comments or white space here,
     but we may do that at some point."))
  (:number ((number pnumber)))
  (:char ((char cconst)))
  (:paren ((inner pexpr)))
  (:plus ((arg pexpr)))
  (:minus ((arg pexpr)))
  (:bitnot ((arg pexpr)))
  (:lognot ((arg pexpr)))
  (:mul ((arg1 pexpr) (arg2 pexpr)))
  (:div ((arg1 pexpr) (arg2 pexpr)))
  (:rem ((arg1 pexpr) (arg2 pexpr)))
  (:add ((arg1 pexpr) (arg2 pexpr)))
  (:sub ((arg1 pexpr) (arg2 pexpr)))
  (:shl ((arg1 pexpr) (arg2 pexpr)))
  (:shr ((arg1 pexpr) (arg2 pexpr)))
  (:lt ((arg1 pexpr) (arg2 pexpr)))
  (:gt ((arg1 pexpr) (arg2 pexpr)))
  (:le ((arg1 pexpr) (arg2 pexpr)))
  (:ge ((arg1 pexpr) (arg2 pexpr)))
  (:eq ((arg1 pexpr) (arg2 pexpr)))
  (:ne ((arg1 pexpr) (arg2 pexpr)))
  (:bitand ((arg1 pexpr) (arg2 pexpr)))
  (:bitxor ((arg1 pexpr) (arg2 pexpr)))
  (:bitior ((arg1 pexpr) (arg2 pexpr)))
  (:logand ((arg1 pexpr) (arg2 pexpr)))
  (:logor ((arg1 pexpr) (arg2 pexpr)))
  (:cond ((test pexpr) (then pexpr) (else pexpr)))
  (:defined ((name ident)))
  :pred pexprp
  :prepwork ((set-induction-depth-limit 1)))

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-pexpr
  :short "An irrelevant preprocessor expression."
  :type pexprp
  :body (pexpr-number (irr-pnumber)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum pif
  :short "Fixtype of preprocessor `if' directives."
  :long
  (xdoc::topstring
   (xdoc::p
    "There are the three kinds that can open an `if' section.")
   (xdoc::p
    "This fixtype only captures the directive, i.e. the first line,
     not the whole `if' section, which is captured elsewhere."))
  (:if ((expr pexpr)))
  (:ifdef ((name ident)))
  (:ifndef ((name ident)))
  :pred pifp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes pparts/conds
  :short "Fixtypes of preprocessor group parts and related entities."

;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum ppart
    :parents (preprocessor-files pparts/conds)
    :short "Fixtype of preprocessor group parts."
    :long
    (xdoc::topstring
     (xdoc::p
      "We do not distinguish between control lines and text lines:
       we represent both as lists of lexemes.")
     (xdoc::p
      "A conditional section consists of an `if' directive,
       the group parts under that first condition,
       zero or more `elif' groups,
       and an optional `else' group."))
    (:line ((lexemes plexeme-list)))
    (:cond ((if pif)
            (parts ppart-list)
            (elifs pelif-list)
            (else pelse-option)))
    :pred ppartp
    :measure (two-nats-measure (acl2-count x) 0))

;;;;;;;;;;;;;;;;;;;;

  (fty::deflist ppart-list
    :parents (preprocessor-files pparts/conds)
    :short "Fixtype of lists of preprocessor group parts."
    :elt-type ppart
    :true-listp t
    :elementp-of-nil nil
    :pred ppart-listp
    :measure (two-nats-measure (acl2-count x) 0)

    ///

    (defruled true-listp-when-ppart-listp
      (implies (ppart-listp x)
               (true-listp x))
      :induct t
      :enable true-listp))

;;;;;;;;;;;;;;;;;;;;

  (fty::defprod pelif
    :parents (preprocessor-files pparts/conds)
    :short "Fixtype of preprocessor `elif' groups."
    :long
    (xdoc::topstring
     (xdoc::p
      "An `elif' group consists of the controlling expression
       and the zero or more controlled group parts."))
    ((expr pexpr)
     (parts ppart-list))
    :pred pelifp
    :measure (two-nats-measure (acl2-count x) 1))

;;;;;;;;;;;;;;;;;;;;

  (fty::deflist pelif-list
    :parents (preprocessor-files pparts/conds)
    :short "Fixtype of lists of preprocessor `elif' groups."
    :elt-type pelif
    :true-listp t
    :elementp-of-nil nil
    :pred pelif-listp
    :measure (two-nats-measure (acl2-count x) 0))

;;;;;;;;;;;;;;;;;;;;

  (fty::defprod pelse
    :parents (preprocessor-files pparts/conds)
    :short "Fixtype of `else' groups."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is just a list of group parts,
       but we wrap into a fixtype so we can make an option type from it."))
    ((parts ppart-list))
    :pred pelsep
    :measure (two-nats-measure (acl2-count x) 1))

;;;;;;;;;;;;;;;;;;;;

  (fty::defoption pelse-option
    pelse
    :parents (preprocessor-files pparts/conds)
    :short "Fixtype of optional `else' groups."
    :pred pelse-optionp
    :measure (two-nats-measure (acl2-count x) 2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod pfile
  :short "Fixtype of preprocessor files."
  ((parts ppart-list))
  :pred pfilep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-pfile
  :short "An irrelevant preprocessor file."
  :type pfilep
  :body (pfile nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define concatenate-cond-bodies ((parts ppart-listp)
                                 (elifs pelif-listp)
                                 (else? pelse-optionp))
  :returns (pparts ppart-listp)
  :short "Concatenate all the bodies of a conditional."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function takes as input the last three components
     of the @(':cond') summand of @(tsee ppart);
     the first component is not needed here.
     We concatenate all the bodies of the conditional.")
   (xdoc::p
    "This operation may seem strange at first sight,
     given that the branches of a conditional should be exclusive.
     However, it is always called on conditionals in which
     at most one branch is populated, all other branches being empty.
     Such as the conditionals currently generated by our preprocessor.
     Thus, in effect, this operation removes the conditional scaffolding
     and only retains the group parts of the branch that was selected.
     This operation is used when full expansion is required by the options,
     because in this case we do not keep any preprocessing directives."))
  (append (ppart-list-fix parts)
          (concatenate-elif-bodies elifs)
          (and else? (pelse->parts else?)))
  :prepwork
  ((define concatenate-elif-bodies ((elifs pelif-listp))
     :returns (pparts ppart-listp)
     :parents nil
     (cond ((endp elifs) nil)
           (t (append (pelif->parts (car elifs))
                      (concatenate-elif-bodies (cdr elifs))))))))
