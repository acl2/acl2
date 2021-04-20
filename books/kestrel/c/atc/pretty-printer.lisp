; C Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2020 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "abstract-syntax")

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
     to an output channel, which is associated to a file.
     The newline characters are added to this function;
     they do not appear in the @(tsee msgp) and @(tsee msg-listp) values.")
   (xdoc::p
    "Currently in our abstract syntax there is no distinction between
     translation units and preprocessing translation units.
     However, it is the latter, not the former,
     that must be pretty-printed to files
     [C:5.1.1.2]."))
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
    We indent by increments of 4 spaces.
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

(define pprint-iconst-tysuffix ((ts iconst-tysuffixp))
  :returns (part msgp)
  :short "Pretty-print a type suffix of integer constants."
  :long
  (xdoc::topstring-p
   "As noted in @(tsee iconst-tysuffix),
    we use uppercase letters.")
  (iconst-tysuffix-case ts
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
  (str::natstr (lnfix n))
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
    (str::cat "0" (str::natstr8 n)))
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
  (str::cat "0x" (str::natstr16 (lnfix n)))
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
         (pprint-iconst-tysuffix c.type)))
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
              :enum (prog2$ (raise "Internal error: ~
                                    enumeration constants not supported.")
                            "")
              :char (prog2$ (raise "Internal error: ~
                                    character constants not supported.")
                            ""))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-unop ((op unopp))
  :returns (part msgp)
  :short "Pretty-print a unary operator."
  (unop-case op
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

(define pprint-tyspecseq ((tss tyspecseqp))
  :returns (part msgp)
  :short "Pretty-print a sequence of type specifiers."
  :long
  (xdoc::topstring-p
   "As noted in @(tsee tyspecseq),
    for now we only capture one sequence for each type,
    so we need to pick what to print here.
    We pick the minimal choice for each type.")
  (tyspecseq-case tss
                  :char "char"
                  :schar "signed char"
                  :sshort "short"
                  :sint "int"
                  :slong "long"
                  :sllong "long long"
                  :uchar "unsigned char"
                  :ushort "unsigned short"
                  :uint "unsigned int"
                  :ulong "unsigned long"
                  :ullong "unsigned long long")
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-tyname ((tn tynamep))
  :returns (part msgp)
  :short "Pretty-print a type name."
  (msg "~@0~s1"
       (pprint-tyspecseq (tyname->specs tn))
       (if (tyname->pointerp tn) " *" ""))
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
     such as a the grade of additive expressions
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
     (Here by 'subrule' we mean a rule not necessarily in the grammar
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
     of a super-expression @('(binary-expr (binop-add) left right)'),
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
     Thus, we interpose a space when these two situations occur."))

  (define pprint-expr ((expr exprp) (expected-grade expr-gradep))
    :returns (part msgp)
    (b* ((actual-grade (expr->grade expr))
         (part (expr-case
                expr
                :ident (pprint-ident expr.get)
                :const (pprint-const expr.get)
                :arrsub (msg "~@0[~@1]"
                             (pprint-expr expr.arr (expr-grade-postfix))
                             (pprint-expr expr.sub (expr-grade-top)))
                :call (msg "~@0(~@1)"
                           (pprint-ident expr.fun)
                           (pprint-comma-sep
                            (pprint-expr-list expr.args (expr-grade-top))))
                :postinc (msg "~@0++"
                              (pprint-expr expr.arg (expr-grade-postfix)))
                :postdec (msg "~@0--"
                              (pprint-expr expr.arg (expr-grade-postfix)))
                :preinc (msg "++~@0"
                             (pprint-expr expr.arg (expr-grade-unary)))
                :predec (msg "--~@0)"
                             (pprint-expr expr.arg (expr-grade-unary)))
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
                            (pprint-expr expr.arg (expr-grade-cast)))
                :cast (msg "(~@0) ~@1"
                           (pprint-tyname expr.type)
                           (pprint-expr expr.arg (expr-grade-cast)))
                :binary (b* (((mv left-grade right-grade)
                              (binop-expected-grades expr.op)))
                          (msg "~@0 ~@1 ~@2"
                               (pprint-expr expr.arg1 left-grade)
                               (pprint-binop expr.op)
                               (pprint-expr expr.arg2 right-grade)))
                :cond (msg "~@0 ? ~@1 : ~@2"
                           (pprint-expr expr.test (expr-grade-logical-or))
                           (pprint-expr expr.then (expr-grade-top))
                           (pprint-expr expr.else (expr-grade-conditional))))))
      (if (expr-grade-<= actual-grade expected-grade)
          part
        (msg "(~@0)" part)))
    :measure (expr-count expr))

  (define pprint-expr-list ((exprs expr-listp) (expected-grade expr-gradep))
    :returns (parts msg-listp)
    (cond ((endp exprs) nil)
          (t (cons (pprint-expr (car exprs) expected-grade)
                   (pprint-expr-list (cdr exprs) expected-grade))))
    :measure (expr-list-count exprs))

  :ruler-extenders :all

  :verify-guards nil ; done below
  ///
  (verify-guards pprint-expr)

  (fty::deffixequiv-mutual pprint-expr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-declor ((declor declorp))
  :returns (part msgp)
  :short "Pretty-print a declarator."
  (msg "~s0~@1"
       (if (declor->pointerp declor) "*" "")
       (pprint-ident (declor->ident declor)))
  :hooks (:fix))

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

(define pprint-declon ((declon declonp) (level natp))
  :returns (part msgp)
  :short "Pretty-print a declaration."
  (b* (((declon declon) declon))
    (pprint-line (msg "~@0 ~@1 = ~@2;"
                      (pprint-tyspecseq declon.type)
                      (pprint-declor declon.declor)
                      (pprint-expr declon.init (expr-grade-top)))
                 (lnfix level)))
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

  (define pprint-stmt ((stmt stmtp) (level natp))
    :returns (lines msg-listp)
    (stmt-case
     stmt
     :labeled (append (list
                       (pprint-line (msg "~@0 {"
                                         (pprint-label stmt.label))
                                    level))
                      (pprint-stmt stmt.body (1+ level))
                      (list (pprint-line "}" level)))
     :compound (pprint-block-item-list stmt.items level)
     :expr (list
            (pprint-line (msg "~@0;"
                              (pprint-expr stmt.get (expr-grade-top)))
                         level))
     :null (list (pprint-line ";" level))
     :if (append (list
                  (pprint-line (msg "if (~@0) {"
                                    (pprint-expr stmt.test (expr-grade-top)))
                               level))
                 (pprint-stmt stmt.then (1+ level))
                 (list (pprint-line "}" level)))
     :ifelse (append (list
                      (pprint-line (msg "if (~@0) {"
                                        (pprint-expr stmt.test (expr-grade-top)))
                                   level))
                     (pprint-stmt stmt.then (1+ level))
                     (list (pprint-line "} else {" level))
                     (pprint-stmt stmt.else (1+ level))
                     (list (pprint-line "}" level)))
     :switch (append (list
                      (pprint-line (msg "switch (~@0) {"
                                        (pprint-expr stmt.ctrl (expr-grade-top)))
                                   level))
                     (pprint-stmt stmt.body (1+ level))
                     (list (pprint-line "}" level)))
     :while (append (list
                     (pprint-line (msg "while (~@0) {"
                                       (pprint-expr stmt.test (expr-grade-top)))
                                  level))
                    (pprint-stmt stmt.body (1+ level))
                    (list (pprint-line "}" level)))
     :dowhile (append (list (pprint-line "do {" level))
                      (pprint-stmt stmt.body (1+ level))
                      (list
                       (pprint-line (msg "} while (~@0);"
                                         (pprint-expr stmt.test (expr-grade-top)))
                                    level)))
     :for (append (list
                   (pprint-line (msg "for (~@0; ~@1; ~@2) {"
                                     (if stmt.init
                                         (pprint-expr stmt.init (expr-grade-top))
                                       "")
                                     (if stmt.test
                                         (pprint-expr stmt.test (expr-grade-top))
                                       "")
                                     (if stmt.next
                                         (pprint-expr stmt.next (expr-grade-top))
                                       ""))
                                level))
                  (pprint-stmt stmt.body (1+ level))
                  (list (pprint-line "}" level)))
     :goto (list (pprint-line (msg "goto ~@0;"
                                   (pprint-ident stmt.target))
                              level))
     :continue (list (pprint-line "continue;" level))
     :break (list (pprint-line "break;" level))
     :return (list (if stmt.value
                       (pprint-line (msg "return ~@0;"
                                         (pprint-expr stmt.value
                                                      (expr-grade-top)))
                                    level)
                     (pprint-line "return;" level))))
    :measure (stmt-count stmt))

  (define pprint-block-item ((item block-itemp) (level natp))
    :returns (lines msg-listp)
    (block-item-case item
                     :declon (list (pprint-declon item.get level))
                     :stmt (pprint-stmt item.get level))
    :measure (block-item-count item))

  (define pprint-block-item-list ((items block-item-listp) (level natp))
    :returns (lines msg-listp)
    (cond ((endp items) nil)
          (t (append (pprint-block-item (car items) level)
                     (pprint-block-item-list (cdr items) level))))
    :measure (block-item-list-count items)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-param-declon ((param param-declonp))
  :returns (part msgp)
  :short "Pretty-print a parameter declaration."
  (b* (((param-declon param) param))
    (msg "~@0 ~@1"
         (pprint-tyspecseq param.type)
         (pprint-declor param.declor)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-param-declon-list ((params param-declon-listp))
  :returns (parts msg-listp)
  :short "Pretty-print a list of parameter-declarations."
  (cond ((endp params) nil)
        (t (cons (pprint-param-declon (car params))
                 (pprint-param-declon-list (cdr params)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-fundef ((fdef fundefp))
  :returns (lines msg-listp)
  :short "Pretty-print a function definition."
  :long
  (xdoc::topstring-p
   "This is always at the top level,
    so we initialize the indentation level of the body to 1.")
  (b* (((fundef fdef) fdef))
    (append (list (pprint-line (msg "~@0 ~@1(~@2) {"
                                    (pprint-tyspecseq fdef.result)
                                    (pprint-ident fdef.name)
                                    (pprint-comma-sep
                                     (pprint-param-declon-list fdef.params)))
                               0))
            (pprint-stmt fdef.body 1)
            (list (pprint-line "}" 0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-ext-declon ((ext ext-declonp))
  :returns (lines msg-listp)
  :short "Pretty-print an external declaration."
  (ext-declon-case ext
                   :fundef (pprint-fundef ext.get)
                   :declon (raise "Internal error: ~
                                 non-function-definition external declarations ~
                                 not supported.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-ext-declon-list ((exts ext-declon-listp))
  :returns (lines msg-listp)
  :short "Pretty-print a list of external declarations."
  :long
  (xdoc::topstring-p
   "We print a blank line before each one.")
  (cond ((endp exts) nil)
        (t (append (list (pprint-line-blank))
                   (pprint-ext-declon (car exts))
                   (pprint-ext-declon-list (cdr exts))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-transunit ((tunit transunitp))
  :returns (lines msg-listp)
  :short "Pretty-print a translation units."
  (b* (((transunit tunit) tunit))
    (pprint-ext-declon-list tunit.declons)))

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
