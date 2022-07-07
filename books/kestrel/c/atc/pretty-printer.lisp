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

(include-book "pretty-printing-options")

(include-book "../language/abstract-syntax")

(include-book "kestrel/utilities/messages" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/strings/octal" :dir :system)
(include-book "std/strings/hex" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; library extensions

(defrulel msgp-when-stringp
  (implies (stringp x)
           (msgp x)))

(defrulel msgp-when-consp-and-stringp-and-character-alistp
  (implies (and (consp x)
                (stringp (car x))
                (character-alistp (cdr x)))
           (msgp x)))

(local (in-theory (disable msgp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-pretty-printer
  :parents (atc-implementation)
  :short "A pretty-printer of C abstract syntax for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "This pretty-printer produces text
     in the form of @(tsee msgp) and @(tsee msg-listp) values.
     The latter generally consist of lines of text;
     that is always the case at the top level,
     i.e. a C translation unit is turned into a list of lines.
     Some pretty-printing functions produce @(tsee msgp) values
     that other pretty-printing functions
     incorporate into larger text.
     In the pretty-printing functions,
     we consistently use the result names
     @('part') for @(tsee msgp) values that are part of lines,
     @('parts') for @(tsee msg-listp) values that are lists of parts of lines,
     @('line') for @(tsee msgp) values that are individual lines, and
     @('lines') for @(tsee msg-listp) values that are multiple lines.")
   (xdoc::p
    "A separate function writes the lines for a C translation unit
     to an output channel, which is associated to a file.")
   (xdoc::p
    "Currently in our abstract syntax there is no distinction between
     translation units and preprocessing translation units.
     However, it is the latter, not the former,
     that must be pretty-printed to files
     [C:5.1.1.2].")
   (xdoc::p
    "We use some "
    (xdoc::seetopic "atc-pretty-printing-options" "pretty-printing options")
    " that influence some aspects of the pretty-printing.
     For now only a simple option is supported,
     but more options may be supported."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-indent ((level natp))
  :returns (part msgp)
  :short "Pretty-print identation spaces."
  :long
  (xdoc::topstring-p
   "The non-blank content of each line is indented at a certain level.
    The level is passed as argument here.
    We indent by increments of 4 spaces;
    this could be an "
   (xdoc::seetopic "atc-pretty-printing-options" "option")
   " in the future.
    Thus, we return a string (which is also a message)
    consisting of a number of spaces equal to 4 times the level.")
  (implode (repeat (* 4 (lnfix level)) #\Space))
  :hooks (:fix)
  :prepwork
  ((local (include-book "std/typed-lists/character-listp" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-comma-sep ((parts msg-listp))
  :returns (part msgp :hyp (msg-listp parts))
  :short "Turn zero or more parts into a single part
          containing the zero or more parts, comma-separated."
  (cond ((endp parts) "")
        ((endp (cdr parts)) (car parts))
        (t (msg "~@0, ~@1"
                (car parts)
                (pprint-comma-sep (cdr parts))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-ident ((id identp))
  :returns (part msgp)
  :short "Pretty-print an identifier."
  (ident->name id)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-ident-list ((ids ident-listp))
  :returns (parts msg-listp)
  :short "Pretty-print a list of identifiers."
  (cond ((endp ids) nil)
        (t (cons (pprint-ident (car ids))
                 (pprint-ident-list (cdr ids)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-iconst-length ((ts iconst-lengthp))
  :returns (part msgp)
  :short "Pretty-print a length suffix of integer constants."
  :long
  (xdoc::topstring-p
   "As noted in @(tsee iconst-length),
    we use uppercase letters.")
  (iconst-length-case ts
                      :none ""
                      :long "L"
                      :llong "LL")
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-dec-const ((n natp))
  :returns (part msgp)
  :short "Pretty-print a decimal constant."
  :long
  (xdoc::topstring-p
   "According to the grammar [C:6.4.4.1],
    a `decimal constant' is a sequence of decimal digits
    that does not start with @('0');
    with the optional suffixes, this becomes an integer constant.
    As noted in @(tsee iconst), we allow 0 here,
    which is turned into the single digit @('0').")
  (str::nat-to-dec-string (lnfix n))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-oct-const ((n natp))
  :returns (part msgp)
  :short "Pretty-print an octal constant."
  :long
  (xdoc::topstring-p
   "According to the grammar [C:6.4.4.1],
    an `octal constant' is a sequence of octal digits starting with @('0');
    with the optional suffixes, this becomes an integer constant.")
  (if (zp n)
      "0"
    (str::cat "0" (str::nat-to-oct-string n)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-hex-const ((n natp))
  :returns (part msgp)
  :short "Pretty-print a hexadecimal constant."
  :long
  (xdoc::topstring-p
   "According to the grammar [C:6.4.4.1],
    a `hexadecimal constant' is a sequence of hexadecimal digits
    preceded by @('0x') or @('0X');
    with the optional suffixes, this becomes an integer constant.
    We print this with lowercase prefix and with no leading zeros,
    unless the number is 0, in which case we print @('0x0').")
  (str::cat "0x" (str::nat-to-hex-string (lnfix n)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-iconst ((c iconstp))
  :returns (part msgp)
  :short "Pretty-print an integer constant."
  :long
  (xdoc::topstring-p
   "If the constant is unsigned, we print the uppercase @('U'),
    not the lowercase @('u').")
  (b* (((iconst c) c))
    (msg "~@0~@1~@2"
         (iconst-base-case c.base
                           :dec (pprint-dec-const c.value)
                           :oct (pprint-oct-const c.value)
                           :hex (pprint-hex-const c.value))
         (if c.unsignedp "U" "")
         (pprint-iconst-length c.length)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-const ((c constp))
  :returns (part msgp)
  :short "Pretty-print a constant."
  :long
  (xdoc::topstring-p
   "We cause an error when we encounter the placeholders for
    floating, enumeration, and character constants.")
  (const-case c
              :int (pprint-iconst c.get)
              :float (prog2$ (raise "Internal error: ~
                                     floating constants not supported.")
                             "")
              :enum (pprint-ident c.get)
              :char (prog2$ (raise "Internal error: ~
                                    character constants not supported.")
                            ""))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-tyspecseq ((tss tyspecseqp))
  :returns (part msgp)
  :short "Pretty-print a sequence of type specifiers."
  :long
  (xdoc::topstring-p
   "As noted in @(tsee tyspecseq),
    for now we only capture one sequence for each type,
    so we need to pick what to print here.
    We pick the shortest (or only) choice for each type.")
  (tyspecseq-case tss
                  :void "void"
                  :char "char"
                  :schar "signed char"
                  :uchar "unsigned char"
                  :sshort (msg "~s0short~s1"
                               (if tss.signed "signed " "")
                               (if tss.int " int" ""))
                  :ushort (msg "unsigned short~s0"
                               (if tss.int " int" ""))
                  :sint (cond ((and tss.signed tss.int) "signed int")
                              (tss.signed "signed")
                              (tss.int "int")
                              (t (prog2$ (impossible) "")))
                  :uint (msg "unsigned~s0"
                             (if tss.int " int" ""))
                  :slong (msg "~s0long~s1"
                              (if tss.signed "signed " "")
                              (if tss.int " int" ""))
                  :ulong (msg "unsigned long~s0"
                              (if tss.int " int" ""))
                  :sllong (msg "~s0long long~s1"
                               (if tss.signed "signed " "")
                               (if tss.int " int" ""))
                  :ullong (msg "unsigned long long~s0"
                               (if tss.int " int" ""))
                  :bool "_Bool"
                  :float (msg "float~s0"
                              (if tss.complex " _Complex" ""))
                  :double (msg "double~s0"
                               (if tss.complex " _Complex" ""))
                  :ldouble (msg "long double~s0"
                                (if tss.complex " _Complex" ""))
                  :struct (msg "struct ~@0"
                               (pprint-ident tss.tag))
                  :union (msg "union ~@0"
                              (pprint-ident tss.tag))
                  :enum (msg "union ~@0"
                             (pprint-ident tss.tag))
                  :typedef (pprint-ident tss.name))
  :hooks (:fix)
  :guard-hints (("Goal"
                 :use (:instance tyspecseq-sint-requirements (x tss))
                 :in-theory (disable tyspecseq-sint-requirements))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-obj-declor ((declor obj-declorp))
  :returns (part msgp)
  :short "Pretty-print an object declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This requires a bit of care,
     because we may need to print parentheses for proper grouping.
     This is similar to the "
    (xdoc::seetopic "pprint-expressions" "pretty-printing of expressions")
    ", but much simpler,
     so we do can put all the logic into this pretty-printing function,
     avoiding all the structure needed for expressions
     (which need that structure due to their greater complexity).
     The idea is the same, though.")
   (xdoc::p
    "Array declarators bind tighter than pointer declarators.
     E.g. @('*x[]') is like @('*(x[])'), not like @('(*x)[]').
     This is because the concrete syntax @('*x[]') must be organized,
     according to the C grammar [C:6.7.6],
     as a <i>pointer</i> and a <i>direct-declarator</i>,
     the latter consisting of
     another <i>direct-declarator</i> for just the identifier @('x')
     and of square brackets with nothing between them.")
   (xdoc::p
    "So, analogously to the treatment of expressions,
     we need to take the relative precendence of pointer and array declarators
     when pretty-printing them:")
   (xdoc::ul
    (xdoc::li
     "If a declarator is an identifier, we just print it.")
    (xdoc::li
     "If a declarator is a pointer declarator,
      we recursively pretty-print its sub-declarator,
      and then we add @('*') in front.
      We do not add any parentheses in this case.
      So, if the sub-declarator is a pointer one,
      the two @('*') will print one after the other, as desired.
      If instead the sub-declarator is an array one,
      then as explained above it binds tighter, so it needs no parentheses.")
    (xdoc::li
     "If a declarator is an array one,
      we recursively pretty-print its sub-declarator.
      If that sub-declarator is a pointer one,
      then we need to parenthesize it,
      because otherwise things would bind in the wrong way.
      If instead the sub-declarator is an identifier or an array one,
      then no parentheses are added, as desired.")))
  (obj-declor-case
   declor
   :ident (pprint-ident declor.get)
   :pointer (msg "*~@0" (pprint-obj-declor declor.decl))
   :array (b* ((sub (pprint-obj-declor declor.decl)))
            (if (obj-declor-case declor.decl :pointer)
                (msg "(~@0)[~@1]"
                     sub
                     (if declor.size
                         (pprint-iconst declor.size)
                       ""))
              (msg "~@0[~@1]"
                   sub
                   (if declor.size
                       (pprint-iconst declor.size)
                     "")))))
  :measure (obj-declor-count declor)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-obj-adeclor ((declor obj-adeclorp))
  :returns (part msgp)
  :short "Pretty-print an abstract object declarator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee pprint-obj-declor).")
   (xdoc::p
    "We print the empty string when there is no declarator,
     but this case never happens when this pretty-printing function
     is called from @(tsee pprint-tyname)."))
  (obj-adeclor-case
   declor
   :none ""
   :pointer (msg "*~@0" (pprint-obj-adeclor declor.decl))
   :array (b* ((sub (pprint-obj-adeclor declor.decl)))
            (if (obj-adeclor-case declor.decl :array)
                (msg "(~@0)[~@1]"
                     sub
                     (if declor.size
                         (pprint-iconst declor.size)
                       ""))
              (msg "~@0[~@1]"
                   sub
                   (if declor.size
                       (pprint-iconst declor.size)
                     "")))))
  :measure (obj-adeclor-count declor)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-tyname ((tn tynamep))
  :returns (part msgp)
  :short "Pretty-print a type name."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there is a declarator,
     we add a space beween it and the type specifier sequence.
     Otherwise, we just print the type specifier sequence."))
  (b* (((tyname tn) tn))
    (if (obj-adeclor-case tn.declor :none)
        (pprint-tyspecseq tn.tyspec)
      (msg "~@0 ~@1"
           (pprint-tyspecseq tn.tyspec)
           (pprint-obj-adeclor tn.declor))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-unop ((op unopp))
  :returns (part msgp)
  :short "Pretty-print a unary operator."
  (unop-case op
             :address "&"
             :indir "*"
             :plus "+"
             :minus "-"
             :bitnot "~~" ; a single ~ is interpreted as a directive
             :lognot "!")
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-binop ((op binopp))
  :returns (part msgp)
  :short "Pretty-print a binary operator."
  (binop-case op
              :mul "*"
              :div "/"
              :rem "%"
              :add "+"
              :sub "-"
              :shl "<<"
              :shr ">>"
              :lt "<"
              :gt ">"
              :le "<="
              :ge ">="
              :eq "=="
              :ne "!="
              :bitand "&"
              :bitxor "^"
              :bitior "|"
              :logand "&&"
              :logor "||"
              :asg "="
              :asg-mul "*="
              :asg-div "/="
              :asg-rem "%="
              :asg-add "+="
              :asg-sub "-="
              :asg-shl "<<="
              :asg-shr ">>="
              :asg-and "&="
              :asg-xor "^="
              :asg-ior "|=")
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc pprint-expressions
  :short "Pretty-printing of expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The tree structure of the abstract syntax of C expressions
     describes the grouping of nested subexpressions.
     For instance, the tree")
   (xdoc::codeblock
    "(expr-binary (binop-mul)"
    "             (expr-binary (binop-add)"
    "                          (expr-ident (make-ident :name \"x\"))"
    "                          (expr-ident (make-ident :name \"y\")))"
    "             (expr-ident (make-ident :name \"z\")))")
   (xdoc::p
    "represents the expression @('(x + y) * z').
     Note that, when this expression is written in concrete syntax as just done,
     parentheses must be added,
     because @('*') binds tighter (i.e. has a higher priority) than @('+')
     in C.")
   (xdoc::p
    "The relative priorities of C operators are implicitly defined
     by the C grammar of expressions,
     which also defines the left vs. right associativity
     of binary operators.
     For instance, the rules in [C:6.5.5] and [C:6.5.6] tell us that
     (i) @('+') binds tighter than @('*') and
     (ii) @('+') is left-associative:")
   (xdoc::ul
    (xdoc::li
     "Consider an expression @('x + y * z').
      In order to parse this as a <i>multiplicative-expression</i>,
      @('x + y') would have to be a <i>multiplicative-expression</i>),
      which is not.
      Thus, the original expression can only be parsed
      as an <i>additive-expression</i>.")
    (xdoc::li
     "Consider an expression @('x * y + z').
      In order to parse this as a <i>multiplicative-expression</i>,
      @('y + z') would have to be a <i>cast-expression</i>,
      which is not.
      Thus, the original expression can only be parsed
      as an <i>additive-expression</i>.")
    (xdoc::li
     "Consider an expression @('x + y + z').
      In order to right-associate it (i.e. @('x + (y + z)')),
      @('y + z') would have to be a <i>multiplicative-expression</i>,
      which is not.
      Thus, the original expression can only be left-associated
      (i.e. @('(x + y) + z'))."))
   (xdoc::p
    "Our pretty-printer adds parentheses
     based on the relative priorities of the C operators
     and the left or right associativity of the C binary operators,
     following the grammar.
     The approach is explained in the following paragraphs.")
   (xdoc::p
    "We define `grades' of expressions
     that correspond to certain nonterminals of the C grammar,
     such as a grade of additive expressions
     corresponding to the nonterminal <i>additive-expression</i>.
     We define a mapping from the expressions of our abstract syntax
     to their grades,
     e.g. @('(expr-binary (binop-add) ... ...)')
     and @('(expr-binary (binop-sub) ... ...)')
     are mapped to the grade of additive expressions.")
   (xdoc::p
    "We define a total order on expression grades that is
     the reflexive and transitive closure of the binary relation
     that consists of the pairs @('grade1 < grade2') such that
     there is a grammar (sub)rule <i>nonterm2: nonterm1</i>
     saying that the nonterminal <i>nonterm2</i> corresponding to @('grade2')
     may expand to the nonterminal <i>nonterm1</i> corresponding to @('grade1').
     For instance, @('grade1') is the grade of multiplicative expressions
     and @('grade2') is the grade of additive expressions,
     because there is a (sub)rule
     <i>additive-expression: multiplicative-expression</i> in the grammar.
     (Here by `subrule' we mean a rule not necessarily in the grammar
     but obtainable by selecting just some of the alternatives in the definiens
     that are on different lines in [C].)
     The nonterminal <i>additive-expression</i> also has other alternatives,
     but those are not single nonterminals;
     here we are only concerned with single nonterminals as rule definientia.
     The reason is explained below.")
   (xdoc::p
    "Besides the abstract syntactic expression to pretty-print,
     the pretty-printer for expression has an argument
     that is the grade of expression that must be pretty-printed
     at that point.
     At the top level, this second argument is
     the grade of top-level expressions,
     i.e. the grade that corresponds to
     the nonterminal <i>expression</i> [C:6.5.17].
     As the pretty-printer descends into subexpressions,
     the second argument is changed according to
     the grammar rule corresponding to the super-expressions.
     For instance, when pretty-printing the left and right subexpressions
     of a super-expression @('(expr-binary (binop-add) left right)'),
     we recursively call the pretty-printer twice,
     once on @('left') and once on @('right').
     Because of the grammar rule
     <i>additive-expression:
        additive-expression <tt>+</tt> multiplicative-expression</i>
     that corresponds to the super-expression,
     the recursive call on @('left') will have as second argument
     the grade of <i>additive-expression</i>,
     while the recursive call on @('right') will have as second argument
     the grade of <i>multiplicative-expression</i>.
     The second argument of the pretty-printer is used as follows:
     the pretty-printer compares the second argument
     (i.e. the expected grade of expression)
     with the grade of the expression passed as first argument
     (i.e. the actual grade of expression),
     according to the total order on expression grades described above;
     if the actual grade is less than or equal to the expected grade,
     the expression is pretty-printed without parentheses,
     otherwise parentheses are added.
     The reason why no parentheses are needed in the first case is that
     the nonterminal for the expected grade can be expanded,
     possibly in multiple steps,
     into the nonterminal for the actual grade:
     or conversely, the actual expression can be parsed
     into an expression of the expected grade.
     On the other hand, if the actual grade is greater than the expected grade,
     there is no such possibility;
     by adding parentheses, we change the grade of the actual expression
     into the one at the bottom of the total order,
     i.e. the grade corresponding to <i>primary-expression</i>,
     which again lets the parenthesized expression be parsed
     into an expression of the expected grade.")
   (xdoc::p
    "For instance, consider the abstract syntax tree for @('(x + y) * z'),
     shown earlier as motivating example.
     Assume that it is pretty-printed as a top-level expression,
     i.e. that the second argument is the grade of <i>expression</i>
     (the expected grade).
     Since the actual grade of the expression is
     the one for <i>multiplicative-expression</i>,
     which is less than or equal to the one for <i>expression</i>
     (via
     <i>assignment-expression</i>,
     <i>conditional-expression</i>,
     <i>logical-OR-expression</i>,
     <i>logical-AND-expression</i>,
     <i>inclusive-OR-expression</i>,
     <i>exclusive-OR-expression</i>,
     <i>AND-expression</i>,
     <i>equality-expression</i>,
     <i>relational-expression</i>,
     <i>shift-expression</i>, and
     <i>additive-expression</i>),
     no parentheses are printed at the top level.
     When pretty-printing the left subexpression @('x + y'),
     the expected grade is <i>multiplicative-expression</i>:
     since the actual grade of @('x + y') is <i>additive-expression</i>,
     which is greater than the expected grade,
     parentheses must be added,
     as mentioned when the example was first presented.
     On the other hand, when pretty-printing the right subexpression @('z'),
     the expected grade is <i>cast-expression</i>:
     since the actual grade of @('z') is <i>primary-expression</i>,
     which is less than the expected grade,
     no parentheses are printed.")
   (xdoc::p
    "The total order on expression grades only considers, as mentioned,
     (sub)rules of the form <i>nonterm2: nonterm1</i>
     where <i>nonterm1</i> is a single nonterminal.
     Rule definientia that are not single terminals
     are captured as tree structures in our abstract syntax,
     and thus have their own explicit grade.
     On the other hand, single-nonterminal definientia
     do not correspond to any tree structure,
     but rather allow the same expression to have, in effect,
     different grades (a form of subtyping).")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum expr-grade
  :short "Grades of expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see pprint-expressions) for background.")
   (xdoc::p
    "The grade @(':top') corresponds to the nonterminal <i>expression</i>;
     the grade @(':ior') corresponds to
     the nonterminal <i>inclusive-OR-expression</i>;
     the grade @(':xor') corresponds to
     the nonterminal <i>exclusive-OR-expression</i>;
     each of the other grades, @(':<grade>'), corresponds to
     the nonterminal <i>&lt;grade&gt;-expression</i>.")
   (xdoc::p
    "We stop at primary expressions:
     we do not need grades for <i>identifier</i>, <i>constant</i>, etc."))
  (:top ())
  (:assignment ())
  (:conditional ())
  (:logical-or ())
  (:logical-and ())
  (:ior ())
  (:xor ())
  (:and ())
  (:equality ())
  (:relational ())
  (:shift ())
  (:additive ())
  (:multiplicative ())
  (:cast ())
  (:unary ())
  (:postfix ())
  (:primary ())
  :pred expr-gradep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr->grade ((expr exprp))
  :returns (grade expr-gradep)
  :short "Grade of an abstract syntactic expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see pprint-expressions) for background."))
  (expr-case expr
             :ident (expr-grade-primary)
             :const (expr-grade-primary)
             :arrsub (expr-grade-postfix)
             :call (expr-grade-postfix)
             :member (expr-grade-postfix)
             :memberp (expr-grade-postfix)
             :postinc (expr-grade-postfix)
             :postdec (expr-grade-postfix)
             :preinc (expr-grade-unary)
             :predec (expr-grade-unary)
             :unary (expr-grade-unary)
             :cast (expr-grade-cast)
             :binary (binop-case expr.op
                                 :mul (expr-grade-multiplicative)
                                 :div (expr-grade-multiplicative)
                                 :rem (expr-grade-multiplicative)
                                 :add (expr-grade-additive)
                                 :sub (expr-grade-additive)
                                 :shl (expr-grade-shift)
                                 :shr (expr-grade-shift)
                                 :lt (expr-grade-relational)
                                 :gt (expr-grade-relational)
                                 :le (expr-grade-relational)
                                 :ge (expr-grade-relational)
                                 :eq (expr-grade-equality)
                                 :ne (expr-grade-equality)
                                 :bitand (expr-grade-and)
                                 :bitxor (expr-grade-xor)
                                 :bitior (expr-grade-ior)
                                 :logand (expr-grade-logical-and)
                                 :logor (expr-grade-logical-or)
                                 :asg (expr-grade-assignment)
                                 :asg-mul (expr-grade-assignment)
                                 :asg-div (expr-grade-assignment)
                                 :asg-rem (expr-grade-assignment)
                                 :asg-add (expr-grade-assignment)
                                 :asg-sub (expr-grade-assignment)
                                 :asg-shl (expr-grade-assignment)
                                 :asg-shr (expr-grade-assignment)
                                 :asg-and (expr-grade-assignment)
                                 :asg-xor (expr-grade-assignment)
                                 :asg-ior (expr-grade-assignment))
             :cond (expr-grade-conditional))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-grade-<= ((grade1 expr-gradep) (grade2 expr-gradep))
  :returns (yes/no booleanp)
  :short "Total order over expression grades."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see pprint-expressions) for background.")
   (xdoc::p
    "We assign a numeric index to every grade
     and then we compare the indices.
     The indices indicate precedence:
     the smaller the index, the higher the precedence."))
  (<= (expr-grade-index grade1)
      (expr-grade-index grade2))
  :hooks (:fix)

  :prepwork
  ((define expr-grade-index ((grade expr-gradep))
     :returns (index natp)
     (expr-grade-case grade
                      :top 16
                      :assignment 15
                      :conditional 14
                      :logical-or 13
                      :logical-and 12
                      :ior 11
                      :xor 10
                      :and 9
                      :equality 8
                      :relational 7
                      :shift 6
                      :additive 5
                      :multiplicative 4
                      :cast 3
                      :unary 2
                      :postfix 1
                      :primary 0)
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define binop-expected-grades ((op binopp))
  :returns (mv (left-grade expr-gradep)
               (right-grade expr-gradep))
  :short "Expression grades of the operands of the binary operators."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see pprint-expressions) for background.")
   (xdoc::p
    "These are based on the grammar rules."))
  (binop-case op
              :mul (mv (expr-grade-multiplicative) (expr-grade-cast))
              :div (mv (expr-grade-multiplicative) (expr-grade-cast))
              :rem (mv (expr-grade-multiplicative) (expr-grade-cast))
              :add (mv (expr-grade-additive) (expr-grade-multiplicative))
              :sub (mv (expr-grade-additive) (expr-grade-multiplicative))
              :shl (mv (expr-grade-shift) (expr-grade-additive))
              :shr (mv (expr-grade-shift) (expr-grade-additive))
              :lt (mv (expr-grade-relational) (expr-grade-shift))
              :gt (mv (expr-grade-relational) (expr-grade-shift))
              :le (mv (expr-grade-relational) (expr-grade-shift))
              :ge (mv (expr-grade-relational) (expr-grade-shift))
              :eq (mv (expr-grade-equality) (expr-grade-relational))
              :ne (mv (expr-grade-equality) (expr-grade-relational))
              :bitand (mv (expr-grade-and) (expr-grade-equality))
              :bitxor (mv (expr-grade-xor) (expr-grade-and))
              :bitior (mv (expr-grade-ior) (expr-grade-xor))
              :logand (mv (expr-grade-ior) (expr-grade-logical-and))
              :logor (mv (expr-grade-logical-or) (expr-grade-logical-and))
              :asg (mv (expr-grade-unary) (expr-grade-assignment))
              :asg-mul (mv (expr-grade-unary) (expr-grade-assignment))
              :asg-div (mv (expr-grade-unary) (expr-grade-assignment))
              :asg-rem (mv (expr-grade-unary) (expr-grade-assignment))
              :asg-add (mv (expr-grade-unary) (expr-grade-assignment))
              :asg-sub (mv (expr-grade-unary) (expr-grade-assignment))
              :asg-shl (mv (expr-grade-unary) (expr-grade-assignment))
              :asg-shr (mv (expr-grade-unary) (expr-grade-assignment))
              :asg-and (mv (expr-grade-unary) (expr-grade-assignment))
              :asg-xor (mv (expr-grade-unary) (expr-grade-assignment))
              :asg-ior (mv (expr-grade-unary) (expr-grade-assignment)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines pprint-expr
  :short "Pretty-print an expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see pprint-expressions) for background.")
   (xdoc::p
    "We first pretty-print the expression,
     and then we wrap it in parentheses
     if the expected grade is smaller than the actual grade.")
   (xdoc::p
    "When recursively pretty-printing subexpressions,
     the grade arguments passed for the subexpressions
     are determined by the relevant grammar rules.")
   (xdoc::p
    "The function to pretty-print lists of expressions
     takes a single grade argument,
     because we only need to pretty-print lists of expressions
     that all have the same required grade.")
   (xdoc::p
    "When printing unary expressions,
     we need to be careful about not printing
     two nested @('-') expressions as @('--') or
     two nested @('+') expressions ad @('++'),
     otherwise they are interpreted as predecrement or postincrement
     by the C compiler.
     Thus, we interpose a space when these two situations occur.")
   (xdoc::p
    "We treat the pretty-printing of conditional expressions
     slightly differently based on the pretty-printing option
     about parenthesizing nested conditional expressions.
     The difference is in the expected grades
     used for the `then' and `else' subexpressions.
     If that flag is not set,
     we print things with minimal parentheses,
     and therefore we use
     the top grade for `then' and the conditional grade for `else',
     consistently with the grammar rule for conditional expressions.
     This means that if the `then' and/or `else' is a conditional expression,
     it is not parenthesized.
     If instead the flag is set,
     then we use a lower grade for both `then' and `else',
     precisely the grade just one lower than conditional expressions,
     namely the grade of logical disjunction.
     This means that if the `then' and/or `else' is a conditional expression,
     it is parenthesized, in order to lower its grade."))

  (define pprint-expr ((expr exprp)
                       (expected-grade expr-gradep)
                       (options pprint-options-p))
    :returns (part msgp)
    (b* ((actual-grade (expr->grade expr))
         (part (expr-case
                expr
                :ident (pprint-ident expr.get)
                :const (pprint-const expr.get)
                :arrsub (msg "~@0[~@1]"
                             (pprint-expr expr.arr (expr-grade-postfix) options)
                             (pprint-expr expr.sub (expr-grade-top) options))
                :call (msg "~@0(~@1)"
                           (pprint-ident expr.fun)
                           (pprint-comma-sep (pprint-expr-list expr.args
                                                               (expr-grade-top)
                                                               options)))
                :member (msg "~@0.~@1"
                             (pprint-expr expr.target
                                          (expr-grade-postfix)
                                          options)
                             (pprint-ident expr.name))
                :memberp (msg "~@0->~@1"
                              (pprint-expr expr.target
                                           (expr-grade-postfix)
                                           options)
                              (pprint-ident expr.name))
                :postinc (msg "~@0++"
                              (pprint-expr expr.arg
                                           (expr-grade-postfix)
                                           options))
                :postdec (msg "~@0--"
                              (pprint-expr expr.arg
                                           (expr-grade-postfix)
                                           options))
                :preinc (msg "++~@0"
                             (pprint-expr expr.arg
                                          (expr-grade-unary)
                                          options))
                :predec (msg "--~@0)"
                             (pprint-expr expr.arg
                                          (expr-grade-unary)
                                          options))
                :unary (msg "~@0~s1~@2"
                            (pprint-unop expr.op)
                            (if (or (and (unop-case expr.op :minus)
                                         (expr-case expr.arg :unary)
                                         (unop-case (expr-unary->op expr.arg)
                                                    :minus))
                                    (and (unop-case expr.op :plus)
                                         (expr-case expr.arg :unary)
                                         (unop-case (expr-unary->op expr.arg)
                                                    :plus)))
                                " "
                              "")
                            (pprint-expr expr.arg (expr-grade-cast) options))
                :cast (msg "(~@0) ~@1"
                           (pprint-tyname expr.type)
                           (pprint-expr expr.arg (expr-grade-cast) options))
                :binary (b* (((mv left-grade right-grade)
                              (binop-expected-grades expr.op)))
                          (msg "~@0 ~@1 ~@2"
                               (pprint-expr expr.arg1 left-grade options)
                               (pprint-binop expr.op)
                               (pprint-expr expr.arg2 right-grade options)))
                :cond (b* ((lower
                            (pprint-options->parenthesize-nested-conditionals
                             options))
                           (then-grade (if lower
                                           (expr-grade-logical-or)
                                         (expr-grade-top)))
                           (else-grade (if lower
                                           (expr-grade-logical-or)
                                         (expr-grade-conditional))))
                        (msg "~@0 ? ~@1 : ~@2"
                             (pprint-expr expr.test
                                          (expr-grade-logical-or)
                                          options)
                             (pprint-expr expr.then
                                          then-grade
                                          options)
                             (pprint-expr expr.else
                                          else-grade
                                          options))))))
      (if (expr-grade-<= actual-grade expected-grade)
          part
        (msg "(~@0)" part)))
    :measure (expr-count expr))

  (define pprint-expr-list ((exprs expr-listp)
                            (expected-grade expr-gradep)
                            (options pprint-options-p))
    :returns (parts msg-listp)
    (cond ((endp exprs) nil)
          (t (cons (pprint-expr (car exprs) expected-grade options)
                   (pprint-expr-list (cdr exprs) expected-grade options))))
    :measure (expr-list-count exprs))

  :ruler-extenders :all

  :verify-guards nil ; done below
  ///
  (verify-guards pprint-expr)

  (fty::deffixequiv-mutual pprint-expr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-line-blank ()
  :returns (line msgp)
  :short "Pretty-print a blank line of code."
  "~%")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-line ((content msgp) (level natp))
  :returns (line msgp)
  :short "Pretty-print a (non-blank) line of code."
  :long
  (xdoc::topstring-p
   "The content to print is preceded by indentation
    according to the current level.")
  (msg "~s0~@1~%" (pprint-indent level) content))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-struct-declon ((member struct-declonp) (level natp))
  :returns (line msgp)
  :short "Pretty-print a structure declaration."
  (b* (((struct-declon member) member))
    (pprint-line (msg "~@0 ~@1;"
                      (pprint-tyspecseq member.tyspec)
                      (pprint-obj-declor member.declor))
                 (lnfix level)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-struct-declon-list ((members struct-declon-listp) (level natp))
  :returns (lines msg-listp)
  :short "Pretty-print a list of stucture declarations."
  (cond ((endp members) nil)
        (t (cons (pprint-struct-declon (car members) level)
                 (pprint-struct-declon-list (cdr members) level))))
  ///
  (fty::deffixequiv pprint-struct-declon-list
    :hints (("Goal" :in-theory (disable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-tag-declon ((declon tag-declonp) (level natp))
  :returns (lines msg-listp)
  :short "Pretty-print a tag declaration."
  (tag-declon-case
   declon
   :struct (append (list (pprint-line (msg "struct ~@0 {"
                                           (pprint-ident declon.tag))
                                      (lnfix level)))
                   (pprint-struct-declon-list declon.members (1+ (lnfix level)))
                   (list (pprint-line "};"
                                      (lnfix level))))
   :union (append (list (pprint-line (msg "union ~@0 {"
                                          (pprint-ident declon.tag))
                                     (lnfix level)))
                  (pprint-struct-declon-list declon.members (1+ (lnfix level)))
                  (list (pprint-line "};"
                                     (lnfix level))))
   :enum (list (pprint-line (msg "enum ~@0 {,@1};"
                                 (pprint-ident declon.tag)
                                 (pprint-comma-sep
                                  (pprint-ident-list declon.enumerators)))
                            (lnfix level))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-param-declon ((param param-declonp))
  :returns (part msgp)
  :short "Pretty-print a parameter declaration."
  (b* (((param-declon param) param))
    (msg "~@0 ~@1"
         (pprint-tyspecseq param.tyspec)
         (pprint-obj-declor param.declor)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-param-declon-list ((params param-declon-listp))
  :returns (parts msg-listp)
  :short "Pretty-print a list of parameter declarations."
  (cond ((endp params) nil)
        (t (cons (pprint-param-declon (car params))
                 (pprint-param-declon-list (cdr params)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-fun-declor ((declor fun-declorp))
  :returns (part msgp)
  :short "Pretty-print a function declarator."
  (fun-declor-case
   declor
   :base (msg "~@0(~@1)"
              (pprint-ident declor.name)
              (pprint-comma-sep (pprint-param-declon-list declor.params)))
   :pointer (msg "*~@0" (pprint-fun-declor declor.decl)))
  :measure (fun-declor-count declor)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-fun-declon ((declon fun-declonp) (level natp))
  :returns (lines msg-listp)
  :short "Pretty-print a function declaration."
  (b* (((fun-declon declon) declon))
    (list (pprint-line (msg "~@0 ~@1;"
                            (pprint-tyspecseq declon.tyspec)
                            (pprint-fun-declor declon.declor))
                       (lnfix level))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-initer ((initer initerp) (options pprint-options-p))
  :returns (part msgp)
  :short "Pretty-print an initializer."
  (initer-case
   initer
   :single (pprint-expr initer.get (expr-grade-top) options)
   :list (msg "{~@0}"
              (pprint-comma-sep (pprint-expr-list initer.get
                                                  (expr-grade-top)
                                                  options))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-obj-declon ((declon obj-declonp)
                           (level natp)
                           (options pprint-options-p))
  :returns (lines msg-listp)
  :short "Pretty-print an object declaration."
  (b* (((obj-declon declon) declon))
    (list (pprint-line (msg "~@0 ~@1 = ~@2;"
                            (pprint-tyspecseq declon.tyspec)
                            (pprint-obj-declor declon.declor)
                            (pprint-initer declon.init options))
                       (lnfix level))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-label ((lab labelp))
  :returns (part msgp)
  :short "Pretty-print a label."
  :long
  (xdoc::topstring-p
   "We also print a space just after the colon,
    so that the sub-statement after the label is separated by a space.")
  (label-case lab
              :name (msg "~@0: "
                         (pprint-ident lab.get))
              :cas "case: "
              :default "default: ")
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines pprint-stmt
  :short "Pretty-print a statement."
  :long
  (xdoc::topstring
   (xdoc::p
    "Note that we print the block items that form a compound statement
     one after the other, without surrounding curly braces.
     We print those curly braces when printing the surrounding statements.")
   (xdoc::p
    "For simplicity, and perhaps for good style,
     we always print curly braces around certain sub-statements
     (e.g. of @('if'))."))

  (define pprint-stmt ((stmt stmtp)
                       (level natp)
                       (options pprint-options-p))
    :returns (lines msg-listp)
    (stmt-case
     stmt
     :labeled (append (list
                       (pprint-line (msg "~@0 {"
                                         (pprint-label stmt.label))
                                    level))
                      (pprint-stmt stmt.body (1+ level) options)
                      (list (pprint-line "}" level)))
     :compound (pprint-block-item-list stmt.items level options)
     :expr (list
            (pprint-line (msg "~@0;"
                              (pprint-expr stmt.get (expr-grade-top) options))
                         level))
     :null (list (pprint-line ";" level))
     :if (append (list
                  (pprint-line (msg "if (~@0) {"
                                    (pprint-expr stmt.test
                                                 (expr-grade-top)
                                                 options))
                               level))
                 (pprint-stmt stmt.then (1+ level) options)
                 (list (pprint-line "}" level)))
     :ifelse (append (list
                      (pprint-line (msg "if (~@0) {"
                                        (pprint-expr stmt.test
                                                     (expr-grade-top)
                                                     options))
                                   level))
                     (pprint-stmt stmt.then (1+ level) options)
                     (list (pprint-line "} else {" level))
                     (pprint-stmt stmt.else (1+ level) options)
                     (list (pprint-line "}" level)))
     :switch (append (list
                      (pprint-line (msg "switch (~@0) {"
                                        (pprint-expr stmt.ctrl
                                                     (expr-grade-top)
                                                     options))
                                   level))
                     (pprint-stmt stmt.body (1+ level) options)
                     (list (pprint-line "}" level)))
     :while (append (list
                     (pprint-line (msg "while (~@0) {"
                                       (pprint-expr stmt.test
                                                    (expr-grade-top)
                                                    options))
                                  level))
                    (pprint-stmt stmt.body (1+ level) options)
                    (list (pprint-line "}" level)))
     :dowhile (append (list (pprint-line "do {" level))
                      (pprint-stmt stmt.body (1+ level) options)
                      (list
                       (pprint-line (msg "} while (~@0);"
                                         (pprint-expr stmt.test
                                                      (expr-grade-top)
                                                      options))
                                    level)))
     :for (append (list
                   (pprint-line (msg "for (~@0; ~@1; ~@2) {"
                                     (if stmt.init
                                         (pprint-expr stmt.init
                                                      (expr-grade-top)
                                                      options)
                                       "")
                                     (if stmt.test
                                         (pprint-expr stmt.test
                                                      (expr-grade-top)
                                                      options)
                                       "")
                                     (if stmt.next
                                         (pprint-expr stmt.next
                                                      (expr-grade-top)
                                                      options)
                                       ""))
                                level))
                  (pprint-stmt stmt.body (1+ level) options)
                  (list (pprint-line "}" level)))
     :goto (list (pprint-line (msg "goto ~@0;"
                                   (pprint-ident stmt.target))
                              level))
     :continue (list (pprint-line "continue;" level))
     :break (list (pprint-line "break;" level))
     :return (list (if stmt.value
                       (pprint-line (msg "return ~@0;"
                                         (pprint-expr stmt.value
                                                      (expr-grade-top)
                                                      options))
                                    level)
                     (pprint-line "return;" level))))
    :measure (stmt-count stmt))

  (define pprint-block-item ((item block-itemp)
                             (level natp)
                             (options pprint-options-p))
    :returns (lines msg-listp)
    (block-item-case item
                     :declon (pprint-obj-declon item.get level options)
                     :stmt (pprint-stmt item.get level options))
    :measure (block-item-count item))

  (define pprint-block-item-list ((items block-item-listp)
                                  (level natp)
                                  (options pprint-options-p))
    :returns (lines msg-listp)
    (cond ((endp items) nil)
          (t (append (pprint-block-item (car items) level options)
                     (pprint-block-item-list (cdr items) level options))))
    :measure (block-item-list-count items)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-fundef ((fdef fundefp) (options pprint-options-p))
  :returns (lines msg-listp)
  :short "Pretty-print a function definition."
  :long
  (xdoc::topstring-p
   "This is always at the top level,
    so we initialize the indentation level of the body to 1.")
  (b* (((fundef fdef) fdef))
    (append (list (pprint-line (msg "~@0 ~@1 {"
                                    (pprint-tyspecseq fdef.tyspec)
                                    (pprint-fun-declor fdef.declor))
                               0))
            (pprint-block-item-list fdef.body 1 options)
            (list (pprint-line "}" 0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-ext-declon ((ext ext-declonp) (options pprint-options-p))
  :returns (lines msg-listp)
  :short "Pretty-print an external declaration."
  (ext-declon-case ext
                   :fundef (pprint-fundef ext.get options)
                   :obj-declon (pprint-obj-declon ext.get 0 options)
                   :tag-declon (pprint-tag-declon ext.get 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-ext-declon-list ((exts ext-declon-listp)
                                (options pprint-options-p))
  :returns (lines msg-listp)
  :short "Pretty-print a list of external declarations."
  :long
  (xdoc::topstring-p
   "We print a blank line before each one.")
  (cond ((endp exts) nil)
        (t (append (list (pprint-line-blank))
                   (pprint-ext-declon (car exts) options)
                   (pprint-ext-declon-list (cdr exts) options)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-transunit ((tunit transunitp) (options pprint-options-p))
  :returns (lines msg-listp)
  :short "Pretty-print a translation units."
  (b* (((transunit tunit) tunit))
    (pprint-ext-declon-list tunit.declons options)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprinted-lines-to-channel ((lines msg-listp) (channel symbolp) state)
  :returns state
  :mode :program
  :short "Write pretty-printed lines to a channel."
  (b* (((when (endp lines)) state)
       ((mv & state)
        (fmt1! "~@0" (list (cons #\0 (car lines))) 0 channel state nil)))
    (pprinted-lines-to-channel (cdr lines) channel state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defttag :open-output-channel!)

(define pprinted-lines-to-file ((lines msg-listp) (filepath stringp) state)
  :returns (mv erp val state)
  :mode :program
  :short "Write pretty-printed lines to a file."
  :long
  (xdoc::topstring
   (xdoc::p
    "We set the soft and hard right margins to very large values
     to avoid line breaks in virtually all cases.
     Setting these margins to ``infinity'' is not supported.")
   (xdoc::p
    "In the future, we may improve the pretty-printer
     to take into consideration a specified right margin,
     breaking and identing lines appropriately."))
  (state-global-let*
   ((fmt-soft-right-margin 1000000 set-fmt-soft-right-margin)
    (fmt-hard-right-margin 1000000 set-fmt-hard-right-margin))
   (b* (((mv channel state) (open-output-channel! filepath :character state))
        (state (pprinted-lines-to-channel lines channel state))
        (state (close-output-channel channel state)))
     (acl2::value nil))))

(defttag nil)
