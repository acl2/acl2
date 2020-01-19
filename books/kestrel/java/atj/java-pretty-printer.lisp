; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "java-abstract-syntax")

(include-book "kestrel/utilities/messages" :dir :system)
(include-book "kestrel/utilities/strings/hexchars" :dir :system)
(include-book "std/strings/binary" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/strings/hex" :dir :system)
(include-book "std/strings/octal" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-java-pretty-printer
  :parents (atj-implementation)
  :short "A pretty-printer for the abstract syntax of Java,
          for ATJ's implementation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This pretty-printer produces text
     in the form of @(tsee msgp) and @(tsee msg-listp) values.
     The latter generally consist of lines of text;
     that is always the case at the top level,
     i.e. a Java compilation unit is turned into a list of lines.
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
    "A separate function writes the lines for a Java compilation unit
     to an output channel, which is associated to a file.
     The newline characters are added to this function;
     they do not appear in the @(tsee msgp) and @(tsee msg-listp) values."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Library extensions.

(defrulel msgp-when-stringp
  (implies (stringp x)
           (msgp x)))

(defrulel msgp-when-consp-and-stringp-and-character-alistp
  (implies (and (consp x)
                (stringp (car x))
                (character-alistp (cdr x)))
           (msgp x)))

(local (in-theory (disable msgp)))

(defrulel msg-listp-when-string-listp
  :parents nil
  (implies (string-listp x)
           (msg-listp x))
  :enable msg-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-indent ((level natp))
  :returns (spaces stringp)
  :short "Spaces from the left margin for the specified level of indentation."
  :long
  (xdoc::topstring-p
   "We indent by increments of 4 spaces.")
  (implode (repeat (* 4 level) #\Space))
  :prepwork
  ((local (include-book "std/typed-lists/character-listp" :dir :system))))

(define print-comma-sep ((parts msg-listp))
  :returns (part msgp :hyp (msg-listp parts))
  :short "Turn zero or more parts into a single part
          containing the initial parts, comma-separated."
  (cond ((endp parts) "")
        ((endp (cdr parts)) (car parts))
        (t (msg "~@0, ~@1"
                (car parts)
                (print-comma-sep (cdr parts))))))

(define print-jchar ((char characterp))
  :returns (part msgp)
  :short "Pretty-print a character."
  :long
  (xdoc::topstring
   (xdoc::p
    "This turns an ACL2 character, viewed as a Java character,
     into a form that can be correctly pretty-printed
     when the character is part of a Java character or string literal.
     This takes into account
     not only Java's character and string literal syntax [JLS:3.10],
     but also the fact that the pretty-printer uses ACL2's formatted printing,
     where the tilde has a special meaning.")
   (xdoc::p
    "A single quote or double quote or backslash is preceded by a backslash.
     Double quotes do not need a preceding backslash in a character literal,
     and single quotes do not need a preceding backslash in a string literal,
     but for now for simplicity we escape both single and double quotes
     in both character and string literals.")
   (xdoc::p
    "The other characters with codes between 32 and 125 are left unchanged.")
   (xdoc::p
    "For backspace, horizontal tab, line feed, form feed, and carriage return
     we use the escape sequences
     @('\b'), @('\t'), @('\n'), @('\f'), and @('\r').")
   (xdoc::p
    "All the other characters, including tilde,
     are turned into their octal escapes.
     This is needed for tilde,
     which otherwise would cause errors or misinterpretations
     in ACL2's formatted printing."))
  (b* (((when (member char '(#\' #\" #\\))) (implode (list #\\ char)))
       (code (char-code char))
       ((when (and (<= 32 code)
                   (<= code 125))) (implode (list char)))
       ((when (= code 8)) "\\b")
       ((when (= code 9)) "\\t")
       ((when (= code 10)) "\\n")
       ((when (= code 12)) "\\f")
       ((when (= code 13)) "\\r"))
    (implode (cons #\\ (str::natchars8 code)))))

(define print-jchars ((chars character-listp))
  :returns (part msgp)
  :short "Lift @(tsee print-jchar) to lists."
  :long
  (xdoc::topstring-p
   "The representations of the characters are juxtaposed one after the other.
    This is used only for string literals, not character literals.")
  (cond ((endp chars) "")
        (t (msg "~@0~@1"
                (print-jchar (car chars))
                (print-jchars (cdr chars))))))

(define print-jliteral ((lit jliteralp))
  :returns (part msgp)
  :short "Pretty-print a literal."
  :long
  (xdoc::topstring-p
   "We pretty-print our limited form of floating-point literals
    just by appending @('.0') after their decimal integer digits.")
  (jliteral-case
   lit
   :integer (b* ((digits (jintbase-case
                          lit.base
                          :decimal (str::natstr lit.value)
                          :hexadecimal (str::cat "0x" (str::natstr16 lit.value))
                          :octal (if (= lit.value 0)
                                     "0"
                                   (str::cat "0" (str::natstr8 lit.value)))
                          :binary (str::cat "0b" (str::natstr2 lit.value)))))
              (if lit.long?
                  (str::cat digits "L")
                digits))
   :floating (b* ((digits (str::natstr lit.value)))
               (str::cat digits ".0"))
   :boolean (if lit.value "true" "false")
   :character (msg "'~@0'" (print-jchar lit.value))
   :string (msg "\"~@0\"" (print-jchars (explode lit.value)))
   :null "null"))

(define print-primitive-type ((ptype primitive-typep))
  :returns (part msgp)
  :short "Pretty-print a primitive type."
  (primitive-type-case ptype
                       :boolean "boolean"
                       :char "char"
                       :byte "byte"
                       :short "short"
                       :int "int"
                       :long "long"
                       :float "float"
                       :double "double"))

(define print-jtype ((type jtypep))
  :returns (part msgp)
  :short "Pretty-print a type."
  (jtype-case type
              :prim (print-primitive-type type.type)
              :class type.name
              :array (msg "~@0[]" (print-jtype type.comp)))
  :measure (jtype-count type))

(define print-junop ((unop junopp))
  :returns (part msgp)
  :short "Pretty-print a unary operator."
  (junop-case unop
              :preinc "++"
              :predec "--"
              :uplus "+"
              :uminus "-"
              :bitcompl "~~" ; a single ~ is interpreted as a directive
              :logcompl "!"))

(define print-jbinop ((binop jbinopp))
  :returns (part msgp)
  :short "Pretty-print a binary operator."
  (jbinop-case binop
               :mul "*"
               :div "/"
               :rem "%"
               :add "+"
               :sub "-"
               :shl "<<"
               :sshr ">>"
               :ushr ">>>"
               :lt "<"
               :gt ">"
               :le "<="
               :ge ">="
               :eq "=="
               :ne "!="
               :and "&"
               :xor "^"
               :ior "|"
               :condand "&&"
               :condor "||"
               :asg "="
               :asg-mul "*="
               :asg-div "/="
               :asg-rem "%="
               :asg-add "+="
               :asg-sub "-="
               :asg-shl "<<="
               :asg-sshr ">>="
               :asg-ushr ">>>="
               :asg-and "&="
               :asg-xor "^="
               :asg-ior "|="))

(defxdoc print-jexprs
  :short "Pretty-printing of expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The tree structure of the abstract syntax of Java expressions
     describes the grouping of nested subexpressions.
     For instance, the tree")
   (xdoc::codeblock
    "(jexpr-binary (jbinop-mul)"
    "              (jexpr-binary (jbinop-add)"
    "                            (jexpr-name \"x\")"
    "                            (jexpr-name \"y\"))"
    "              (jexpr-name \"z\"))")
   (xdoc::p
    "represents the expression @('(x + y) * z').
     Note that, when this expression is written in concrete syntax as just done,
     parentheses must be added,
     because @('*') binds tighter (i.e. has a higher priority) than @('+')
     in Java.")
   (xdoc::p
    "The relative priorities of Java operators are implicitly defined
     by the Java grammar of expressions,
     which also defines the left vs. right associativity
     of binary operators.
     For instance, with reference to "
    (xdoc::seetopic "grammar" "the ABNF grammar")
    ", the rules tell us that
     (i) @('+') binds tighter than @('*') and
     (ii) @('+') is left-associative:")
   (xdoc::ul
    (xdoc::li
     "Consider an expression @('x + y * z').
      In order to parse this as a @('multiplicative-expression'),
      @('x + y') would have to be a @('multiplicative-expression'),
      which is not.
      Thus, the original expression can only be parsed
      as an @('additive-expression').")
    (xdoc::li
     "Consider an expression @('x * y + z').
      In order to parse this as a @('multiplicative-expression'),
      @('y + z') would have to be a @('unary-expression'),
      which is not.
      Thus, the original expression can only be parsed
      as an @('additive-expression').")
    (xdoc::li
     "Consider an expression @('x + y + z').
      In order to right-associate it (i.e. @('x + (y + z)')),
      @('y + z') would have to be a @('multiplicative-expression'),
      which is not.
      Thus, the original expression can only be left-associated
      (i.e. @('(x + y) + z'))."))
   (xdoc::p
    "Our pretty-printer adds parentheses
     based on the relative priorities of the Java operators
     and the left or right associativity of the Java binary operators,
     following the grammar.
     The approach is explained in the following paragraphs.")
   (xdoc::p
    "We define ``ranks'' of expressions
     that correspond to certain nonterminals of the Java grammar,
     such as a the rank of additive expressions
     corresponding to the nonterminal @('additive-expression').
     We define a mapping from the expressions of our abstract syntax
     to their ranks,
     e.g. @('(jexpr-binary (jbinop-add) ... ...)')
     and @('(jexpr-binary (jbinop-sub) ... ...)')
     are mapped to the rank of additive expressions.")
   (xdoc::p
    "We define a partial order on expression ranks that is
     the reflexive and transitive closure of the binary relation
     that consists of the pairs @('rank1 < rank2') such that
     there is a grammar (sub)rule @('nonterm2 = nonterm1')
     saying that the nonterminal @('nonterm2') corresponding to @('rank2')
     may expand to the nonterminal @('nonterm1') corresponding to @('rank1').
     For instance, @('rank1') is the rank of multiplicative expressions
     and @('rank2') is the rank of additive expressions,
     because there is a (sub)rule
     @('additive-expression = multiplicative-expression') in the grammar.
     (Here by 'subrule' we mean a rule not necessarily in the grammar
     but obtainable by selecting just some of the alternatives in the definiens
     that are separated by slashes in ABNF.)
     The nonterminal @('additive-expression') also has other alternatives,
     but those are not single nonterminals;
     here we are only concerned with single nonterminals as rule definientia.
     The reason is explained below.")
   (xdoc::p
    "Besides the abstract syntactic expression to pretty-print,
     the pretty-printer for expression has an argument
     that is the rank of expression that must be pretty-printed
     at that point.
     At the top level, this second argument is
     the rank of top-level expressions,
     i.e. the rank that corresponds to the nonterminal @('expression').
     As the pretty-printer descends into subexpressions,
     the second argument is changed according to
     the grammar rule corresponding to the super-expressions.
     For instance, when pretty-printing the left and right subexpressions
     of a super-expression @('(jbinary-expr (jbinop-add) left right)'),
     we recursively call the pretty-printer twice,
     once on @('left') and once on @('right').
     Because of the grammar rule
     @('additive-expression =
        additive-expression \"+\" multiplicative-expression')
     that corresponds to the super-expression,
     the recursive call on @('left') will have as second argument
     the rank of @('additive-expression'),
     while the recursive call on @('right') will have as second argument
     the rank of @('multiplicative-expression').
     The second argument of the pretty-printer is used as follows:
     the pretty-printer compares the second argument
     (i.e. the expected rank of expression)
     with the rank of the expression passed as first argument
     (i.e. the actual rank of expression),
     according to the partial order on expression ranks described above;
     if the actual rank is less than or equal to the expected rank,
     the expression is pretty-printed without parentheses,
     otherwise parentheses are added.
     The reason why no parentheses are needed in the first case is that
     the nonterminal for the expected rank can be expanded,
     possibly in multiple steps,
     into the nonterminal for the actual rank:
     or conversely, the actual expression can be parsed
     into an expression of the expected rank.
     On the other hand, if the actual rank is greater than, or unrelated to,
     the expected rank, there is no such possibility;
     by adding parentheses, we ``change'' the rank of the actual expression
     into the bottom of the partial order,
     i.e. the rank corresponding to @('primary'),
     which again lets the parenthesize expression be parsed
     into an expression of the expected rank.")
   (xdoc::p
    "For instance, consider the abstract syntax tree for @('(x + y) * z'),
     shown earlier as motivating example.
     Assume that it is pretty-printed as a top-level expression,
     i.e. that the second argument is the rank of @('expression')
     (the expected rank).
     Since the actual rank of the expression is
     the one for @('multiplicative-expression'),
     which is less than or equal to the one for @('expression')
     (via
     @('assignment-expression'),
     @('conditional-expression'),
     @('conditional-or-expression'),
     @('conditional-and-expression'),
     @('inclusive-or-expression'),
     @('exclusive-or-expression'),
     @('and-expression'),
     @('equality-expression'),
     @('relational-expression'),
     @('shift-expression'), and
     @('additive-expression')),
     no parentheses are printed at the top level.
     When pretty-printing the left subexpression @('x + y'),
     the expected rank is @('multiplicative-expression'):
     since the actual rank of @('x + y') is @('additive-expression'),
     which is greater than the expected rank,
     parentheses must be added,
     as mentioned when the example was first presented.
     On the other hand, when pretty-printing the right subexpression @('z'),
     the expected rank is @('unary-expression'):
     since the actual rank of @('z') is @('primary'),
     which is less than the expected rank,
     no parentheses are printed.")
   (xdoc::p
    "The partial order on expression ranks only considers, as mentioned,
     (sub)rules of the form @('nonterm2 = nonterm1')
     where @('nonterm1') is a single nonterminal.
     Rule definientia that are not single terminals
     are captured as tree structures in our abstract syntax,
     and thus have their own explicit rank.
     On the other hand, single-nonterminal definientia
     do not correspond to any tree structure,
     but rather allow the same expression to have, in effect,
     different ranks (a form of subtyping).")))

(fty::deftagsum jexpr-rank
  :short "Ranks of expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "See "
    (xdoc::seetopic "print-jexprs" "here")
    " for motivation.")
   (xdoc::p
    "The rank @(':expression') corresponds to the nonterminal @('expression').
     The rank @(':primary') corresponds to the nonterminal @('primary').
     Each of the other ranks, @(':<rank>'), corresponds to
     the nonterminal @('<rank>-expression').")
   (xdoc::p
    "We omit a rank for @('lambda-expression'),
     because our abstract syntax does not capture lambda expressions
     (but even if it did, we would omit a rank for them
     for the same reason why we omit the ranks described in the next sentence).
     We omit ranks for
     @('assignment'),
     @('pre-increment-expression'),
     @('pre-decrement-expression'),
     @('unary-expression-not-plus-minus'),
     @('cast-expression'), and
     @('primary-no-new-array')
     because we do not need them:
     we could imagine expanding their definitions
     in the definientia where they appear,
     for our pretty-printing purposes.
     We stop at primary expressions:
     we do not need ranks for
     @('literal'), @('class-instance-creation-expression'), etc.,
     because those do not have any (sub)rules
     with single-nonterminal definientia for expressions."))
  (:expression ())
  (:assignment ())
  (:conditional ())
  (:conditional-or ())
  (:conditional-and ())
  (:inclusive-or ())
  (:exclusive-or ())
  (:and ())
  (:equality ())
  (:relational ())
  (:shift ())
  (:additive ())
  (:multiplicative ())
  (:unary ())
  (:postfix ())
  (:primary ())
  :pred jexpr-rankp)

(define jexpr->rank ((expr jexprp))
  :returns (rank jexpr-rankp)
  :short "Rank of an abstract syntactic expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "See "
    (xdoc::seetopic "print-jexprs" "here")
    " for motivation.")
   (xdoc::p
    "Expressions that do not have their own rank (e.g. literals)
     are mapped to the rank of the most specific nonterminal
     that they (more precisely, their concrete syntactic counterpart)
     can be generated from:
     this is rank @(':primary') for most of them,
     except that expression names are mapped to rank @(':postfix')
     and that cast expressions are mapped to rank @(':unary')."))
  (jexpr-case expr
              :literal (jexpr-rank-primary)
              :name (jexpr-rank-postfix)
              :newarray (jexpr-rank-primary)
              :newarray-init (jexpr-rank-primary)
              :array (jexpr-rank-primary)
              :newclass (jexpr-rank-primary)
              :field (jexpr-rank-primary)
              :method (jexpr-rank-primary)
              :smethod (jexpr-rank-primary)
              :imethod (jexpr-rank-primary)
              :postinc (jexpr-rank-postfix)
              :postdec (jexpr-rank-postfix)
              :cast (jexpr-rank-unary)
              :unary (jexpr-rank-unary)
              :binary (jbinop-case expr.op
                                   :mul (jexpr-rank-multiplicative)
                                   :div (jexpr-rank-multiplicative)
                                   :rem (jexpr-rank-multiplicative)
                                   :add (jexpr-rank-additive)
                                   :sub (jexpr-rank-additive)
                                   :shl (jexpr-rank-shift)
                                   :sshr (jexpr-rank-shift)
                                   :ushr (jexpr-rank-shift)
                                   :lt (jexpr-rank-relational)
                                   :gt (jexpr-rank-relational)
                                   :le (jexpr-rank-relational)
                                   :ge (jexpr-rank-relational)
                                   :eq (jexpr-rank-equality)
                                   :ne (jexpr-rank-equality)
                                   :and (jexpr-rank-and)
                                   :xor (jexpr-rank-exclusive-or)
                                   :ior (jexpr-rank-inclusive-or)
                                   :condand (jexpr-rank-conditional-and)
                                   :condor (jexpr-rank-conditional-or)
                                   :asg (jexpr-rank-assignment)
                                   :asg-mul (jexpr-rank-assignment)
                                   :asg-div (jexpr-rank-assignment)
                                   :asg-rem (jexpr-rank-assignment)
                                   :asg-add (jexpr-rank-assignment)
                                   :asg-sub (jexpr-rank-assignment)
                                   :asg-shl (jexpr-rank-assignment)
                                   :asg-sshr (jexpr-rank-assignment)
                                   :asg-ushr (jexpr-rank-assignment)
                                   :asg-and (jexpr-rank-assignment)
                                   :asg-xor (jexpr-rank-assignment)
                                   :asg-ior (jexpr-rank-assignment))
              :instanceof (jexpr-rank-relational)
              :cond (jexpr-rank-conditional)
              :paren (jexpr-rank-primary)))

(define jexpr-rank-<= ((rank1 jexpr-rankp) (rank2 jexpr-rankp))
  :returns (yes/no booleanp)
  :short "Order over expression ranks."
  :long
  (xdoc::topstring
   (xdoc::p
    "See "
    (xdoc::seetopic "print-jexprs" "here")
    " for motivation.")
   (xdoc::p
    "The partial order over expression ranks is actually a linear order.
     (However, our pretty-printing approach should work
     with partial orders that are not linear orders.)
     So we define the linear order by mapping each rank to a numeric index
     so that the indices provide the order of the ranks.
     The specific numeric values are unimportant;
     only their relative ordering is."))
  (<= (jexpr-rank-index rank1)
      (jexpr-rank-index rank2))

  :prepwork
  ((define jexpr-rank-index ((rank jexpr-rankp))
     :returns (index natp)
     (jexpr-rank-case rank
                      :expression 15
                      :assignment 14
                      :conditional 13
                      :conditional-or 12
                      :conditional-and 11
                      :inclusive-or 10
                      :exclusive-or 9
                      :and 8
                      :equality 7
                      :relational 6
                      :shift 5
                      :additive 4
                      :multiplicative 3
                      :unary 2
                      :postfix 1
                      :primary 0))))

(define jbinop-expected-ranks ((op jbinopp))
  :returns (mv (left-rank jexpr-rankp)
               (right-rank jexpr-rankp))
  :short "Expression ranks of the operands of a binary operator."
  :long
  (xdoc::topstring-p
   "These are based on the grammar rules.")
  (jbinop-case
   op
   :mul (mv (jexpr-rank-multiplicative) (jexpr-rank-unary))
   :div (mv (jexpr-rank-multiplicative) (jexpr-rank-unary))
   :rem (mv (jexpr-rank-multiplicative) (jexpr-rank-unary))
   :add (mv (jexpr-rank-additive) (jexpr-rank-multiplicative))
   :sub (mv (jexpr-rank-additive) (jexpr-rank-multiplicative))
   :shl (mv (jexpr-rank-shift) (jexpr-rank-additive))
   :sshr (mv (jexpr-rank-shift) (jexpr-rank-additive))
   :ushr (mv (jexpr-rank-shift) (jexpr-rank-additive))
   :lt (mv (jexpr-rank-relational) (jexpr-rank-shift))
   :gt (mv (jexpr-rank-relational) (jexpr-rank-shift))
   :le (mv (jexpr-rank-relational) (jexpr-rank-shift))
   :ge (mv (jexpr-rank-relational) (jexpr-rank-shift))
   :eq (mv (jexpr-rank-equality) (jexpr-rank-relational))
   :ne (mv (jexpr-rank-equality) (jexpr-rank-relational))
   :and (mv (jexpr-rank-and) (jexpr-rank-equality))
   :xor (mv (jexpr-rank-exclusive-or) (jexpr-rank-and))
   :ior (mv (jexpr-rank-inclusive-or) (jexpr-rank-exclusive-or))
   :condand (mv (jexpr-rank-conditional-and) (jexpr-rank-inclusive-or))
   :condor (mv (jexpr-rank-conditional-or) (jexpr-rank-conditional-and))
   :asg (mv (jexpr-rank-postfix) (jexpr-rank-expression))
   :asg-mul (mv (jexpr-rank-postfix) (jexpr-rank-expression))
   :asg-div (mv (jexpr-rank-postfix) (jexpr-rank-expression))
   :asg-rem (mv (jexpr-rank-postfix) (jexpr-rank-expression))
   :asg-add (mv (jexpr-rank-postfix) (jexpr-rank-expression))
   :asg-sub (mv (jexpr-rank-postfix) (jexpr-rank-expression))
   :asg-shl (mv (jexpr-rank-postfix) (jexpr-rank-expression))
   :asg-sshr (mv (jexpr-rank-postfix) (jexpr-rank-expression))
   :asg-ushr (mv (jexpr-rank-postfix) (jexpr-rank-expression))
   :asg-and (mv (jexpr-rank-postfix) (jexpr-rank-expression))
   :asg-xor (mv (jexpr-rank-postfix) (jexpr-rank-expression))
   :asg-ior (mv (jexpr-rank-postfix) (jexpr-rank-expression))))

(defines print-jexpr
  :short "Pretty-print an expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "See "
    (xdoc::seetopic "print-jexprs" "here")
    " for motivation.")
   (xdoc::p
    "We first pretty-print the expression,
     and then we wrap it in parentheses
     if the expected rank is smaller than the actual rank.")
   (xdoc::p
    "When recursively pretty-printing subexpressions,
     the ranks argument passed for the subexpressions
     are determined by the relevant grammar rules.")
   (xdoc::p
    "The function to pretty-print lists of expressions
     takes a single rank argument,
     because we only need to pretty-print lists of expressions
     that all have the same required rank.")
   (xdoc::p
    "According to the grammar,
     the target of a field access expression should be a primary
     (or a possibly type-qualified @('super')) [JLS:15.11],
     but that would prevent it from being an expression name [JLS:15.8];
     thus, here we pretend that the target of a field access expression
     is a postfix expression, which includes expression names
     (similarly to array access expressions);
     this should be investigated further in [JLS]."))

  (define print-jexpr ((expr jexprp) (expected-rank jexpr-rankp))
    :returns (part msgp)
    (b* ((actual-rank (jexpr->rank expr))
         (part (jexpr-case
                expr
                :literal (print-jliteral expr.get)
                :name expr.get
                :newarray (msg "new ~@0[~@1]"
                               (print-jtype expr.type)
                               (print-jexpr expr.size (jexpr-rank-expression)))
                :newarray-init (msg "new ~@0[]{~@1}"
                                    (print-jtype expr.type)
                                    (print-comma-sep
                                     (print-jexpr-list
                                      expr.init (jexpr-rank-expression))))
                :array (msg "~@0[~@1]"
                            (print-jexpr expr.array (jexpr-rank-postfix))
                            (print-jexpr expr.index (jexpr-rank-expression)))
                :newclass (msg "new ~@0(~@1)"
                               (print-jtype expr.type)
                               (print-comma-sep
                                (print-jexpr-list
                                 expr.args (jexpr-rank-expression))))
                :field (msg "~@0.~@1"
                            (print-jexpr expr.target (jexpr-rank-primary))
                            expr.name)
                :method (msg "~@0(~@1)"
                             expr.name
                             (print-comma-sep
                              (print-jexpr-list
                               expr.args (jexpr-rank-expression))))
                :smethod (msg "~@0.~@1(~@2)"
                              (print-jtype expr.type)
                              expr.name
                              (print-comma-sep
                               (print-jexpr-list
                                expr.args (jexpr-rank-expression))))
                :imethod (msg "~@0.~@1(~@2)"
                              (print-jexpr expr.target (jexpr-rank-primary))
                              expr.name
                              (print-comma-sep
                               (print-jexpr-list
                                expr.args (jexpr-rank-expression))))
                :postinc (msg "~@0++"
                              (print-jexpr expr.arg (jexpr-rank-postfix)))
                :postdec (msg "~@0--"
                              (print-jexpr expr.arg (jexpr-rank-postfix)))
                :cast (msg "(~@0) ~@1"
                           (print-jtype expr.type)
                           (print-jexpr expr.arg (jexpr-rank-unary)))
                :unary (msg "~@0~@1"
                            (print-junop expr.op)
                            (print-jexpr expr.arg (jexpr-rank-unary)))
                :binary (b* (((mv left-rank
                                  right-rank) (jbinop-expected-ranks expr.op)))
                          (msg "~@0 ~@1 ~@2"
                               (print-jexpr expr.left left-rank)
                               (print-jbinop expr.op)
                               (print-jexpr expr.right right-rank)))
                :instanceof (msg "~@0 instanceof ~@1"
                                 (print-jexpr expr.left (jexpr-rank-relational))
                                 (print-jtype expr.right))
                :cond (msg "~@0 ? ~@1 : ~@2"
                           (print-jexpr expr.test (jexpr-rank-conditional-or))
                           (print-jexpr expr.then (jexpr-rank-expression))
                           (print-jexpr expr.else (jexpr-rank-conditional)))
                :paren (msg "(~@0)"
                            (print-jexpr expr.get (jexpr-rank-expression))))))
      (if (jexpr-rank-<= actual-rank expected-rank)
          part
        (msg "(~@0)" part)))
    :measure (jexpr-count expr))

  (define print-jexpr-list ((exprs jexpr-listp) (expected-rank jexpr-rankp))
    :returns (parts msg-listp)
    (cond ((endp exprs) nil)
          (t (cons (print-jexpr (car exprs) expected-rank)
                   (print-jexpr-list (cdr exprs) expected-rank))))
    :measure (jexpr-list-count exprs))

  :ruler-extenders :all

  :verify-guards nil ; done below
  ///
  (verify-guards print-jexpr))

(define print-jline-blank ()
  :returns (line msgp)
  :short "Pretty-print a blank line of code."
  "~%")

(define print-jline ((content msgp) (indent-level natp))
  :returns (line msgp)
  :short "Pretty-print a (non-blank) line of code."
  :long
  (xdoc::topstring-p
   "The content to print is preceded by
    indentation according to the current level.")
  (msg "~s0~@1~%" (atj-indent indent-level) content))

(define print-jlocvar ((locvar jlocvarp) (indent-level natp))
  :returns (line msgp)
  :short "Pretty-print a local variable declaration."
  (b* (((jlocvar locvar) locvar))
    (if locvar.init?
        (print-jline (msg "~@0~@1 ~@2 = ~@3;"
                          (if locvar.final? "final " "")
                          (print-jtype locvar.type)
                          locvar.name
                          (print-jexpr locvar.init? (jexpr-rank-expression)))
                     indent-level)
      (print-jline (msg "~@0~@1 ~@2;"
                        (if locvar.final? "final " "")
                        (print-jtype locvar.type)
                        locvar.name)
                   indent-level))))

(defines print-jstatems+jblocks
  :short "Pretty-print a statement or block."
  :long
  (xdoc::topstring-p
   "Note that we print the statements that form a block
    one after the other, without surrounding them with curly braces.
    We do print curly braces when printing
    method declarations and @('if') statements,
    producing valid Java concrete syntax,
    but our current treatment of blocks is somewhat ``improper'',
    because syntactically blocks include curly braces.
    This impropriety should be remedied
    in future versions of this pretty-printer.")

  (define print-jstatem ((statem jstatemp) (indent-level natp))
    :returns (lines msg-listp)
    (jstatem-case
     statem
     :locvar (list (print-jlocvar statem.get indent-level))
     :expr (list (print-jline (msg "~@0;"
                                   (print-jexpr statem.get
                                                (jexpr-rank-expression)))
                              indent-level))
     :return (list (if statem.expr?
                       (print-jline (msg "return ~@0;"
                                         (print-jexpr statem.expr?
                                                      (jexpr-rank-expression)))
                                    indent-level)
                     (print-jline "return;" indent-level)))
     :throw (list (print-jline (msg "throw ~@0;"
                                    (print-jexpr statem.expr
                                                 (jexpr-rank-expression)))
                               indent-level))
     :break (list (print-jline "break;" indent-level))
     :continue (list (print-jline "continue;" indent-level))
     :if (append (list (print-jline (msg "if (~@0) {"
                                         (print-jexpr statem.test
                                                      (jexpr-rank-expression)))
                                    indent-level))
                 (print-jblock statem.then (1+ indent-level))
                 (list (print-jline "}" indent-level)))
     :ifelse (append (list (print-jline (msg "if (~@0) {"
                                             (print-jexpr
                                              statem.test
                                              (jexpr-rank-expression)))
                                        indent-level))
                     (print-jblock statem.then (1+ indent-level))
                     (list (print-jline "} else {" indent-level))
                     (print-jblock statem.else (1+ indent-level))
                     (list (print-jline "}" indent-level)))
     :while (append (list (print-jline (msg "while (~@0) {"
                                            (print-jexpr
                                             statem.test
                                             (jexpr-rank-expression)))
                                       indent-level))
                    (print-jblock statem.body (1+ indent-level))
                    (list (print-jline "}" indent-level)))
     :do (append (list (print-jline "do {" indent-level))
                 (print-jblock statem.body (1+ indent-level))
                 (list (print-jline (msg "} while (~@0);"
                                         (print-jexpr statem.test
                                                      (jexpr-rank-expression)))
                                    indent-level)))
     :for (append (list (print-jline (msg "for (~@0; ~@1; ~@2) {"
                                          (print-jexpr statem.init
                                                       (jexpr-rank-expression))
                                          (print-jexpr statem.test
                                                       (jexpr-rank-expression))
                                          (print-jexpr statem.update
                                                       (jexpr-rank-expression)))
                                     indent-level))
                  (print-jblock statem.body (1+ indent-level))
                  (list (print-jline "}" indent-level))))
    :measure (jstatem-count statem))

  (define print-jblock ((block jblockp) (indent-level natp))
    :returns (lines msg-listp)
    (cond ((endp block) nil)
          (t (append (print-jstatem (car block) indent-level)
                     (print-jblock (cdr block) indent-level))))
    :measure (jblock-count block)))

(define print-jaccess ((access jaccessp))
  :returns (part msgp)
  :short "Pretty-print an access modifier."
  (jaccess-case access
                :public "public "
                :protected "protected "
                :private "private "
                :default ""))

(define print-jfield ((field jfieldp) (indent-level natp))
  :returns (line msgp)
  :short "Pretty-print a field declaration."
  (b* (((jfield field) field))
    (if field.init?
        (print-jline (msg "~@0~@1~@2~@3~@4~@5 ~@6 = ~@7;"
                          (print-jaccess field.access)
                          (if field.static? "static " "")
                          (if field.final? "final " "")
                          (if field.transient? "transient " "")
                          (if field.volatile? "volatile " "")
                          (print-jtype field.type)
                          field.name
                          (print-jexpr field.init? (jexpr-rank-expression)))
                     indent-level)
      (print-jline (msg "~@0~@1~@2~@3~@4~@5 ~@6;"
                        (print-jaccess field.access)
                        (if field.static? "static " "")
                        (if field.final? "final " "")
                        (if field.transient? "transient " "")
                        (if field.volatile? "volatile " "")
                        (print-jtype field.type)
                        field.name)
                   indent-level))))

(define print-jresult ((result jresultp))
  :returns (part msgp)
  :short "Pretty-print a method result."
  (jresult-case result
                :type (print-jtype result.get)
                :void "void"))

(define print-jparam ((param jparamp))
  :returns (part msgp)
  :short "Pretty-print a formal parameter."
  (b* (((jparam param) param))
    (msg "~@0~@1 ~@2"
         (if param.final? "final " "")
         (print-jtype param.type)
         param.name)))

(define print-jparam-list ((params jparam-listp))
  :returns (parts msg-listp)
  :short "Pretty-print a formal parameter list."
  (cond ((endp params) nil)
        (t (cons (print-jparam (car params))
                 (print-jparam-list (cdr params))))))

(define print-jmethod ((method jmethodp) (indent-level natp))
  :returns (lines msg-listp)
  :short "Pretty-print a method declaration."
  (b* (((jmethod method) method)
       (modifiers (msg "~@0~@1~@2~@3~@4~@5~@6"
                       (print-jaccess method.access)
                       (if method.abstract? "abstract " "")
                       (if method.static? "static " "")
                       (if method.final? "final " "")
                       (if method.synchronized? "synchronized " "")
                       (if method.native? "native " "")
                       (if method.strictfp? "strictfp " ""))))
    (append (list (print-jline (msg "~@0~@1 ~@2(~@3) ~@4{"
                                    modifiers
                                    (print-jresult method.result)
                                    method.name
                                    (print-comma-sep
                                     (print-jparam-list method.params))
                                    (if method.throws
                                        (msg "throws ~@0 "
                                             (print-comma-sep method.throws))
                                      ""))
                               indent-level))
            (print-jblock method.body (1+ indent-level))
            (list (print-jline "}" indent-level)))))

(define print-jcinitializer ((initializer jcinitializerp) (indent-level natp))
  :returns (lines msg-listp)
  :short "Pretty-print a class initializer."
  (append (list (print-jline (if (jcinitializer->static? initializer)
                                 "static {"
                               "{")
                             indent-level))
          (print-jblock (jcinitializer->code initializer) (1+ indent-level))
          (list (print-jline "}" indent-level))))

(defines print-jclasses+jcmembers
  :short "Pretty-print a class declaration or class member declaration."
  :long
  (xdoc::topstring-p
   "These are mutually recursive because classes may be class members.")

  (define print-jcmember ((member jcmemberp) (indent-level natp))
    :returns (lines msg-listp)
    :short "Pretty-print a class member declaration."
    (jcmember-case member
                   :field (list (print-jfield member.get indent-level))
                   :method (print-jmethod member.get indent-level)
                   :class (print-jclass member.get indent-level))
    :measure (jcmember-count member))

  (define print-jcbody-element ((body-element jcbody-element-p)
                                (indent-level natp))
    :returns (lines msg-listp)
    :short "Pretty-print a class body declaration."
    (jcbody-element-case body-element
                         :member (print-jcmember body-element.get indent-level)
                         :init (print-jcinitializer body-element.get
                                                    indent-level))
    :measure (jcbody-element-count body-element))

  (define print-jcbody-element-list ((body-elements jcbody-element-listp)
                                     (indent-level natp))
    :returns (lines msg-listp)
    :short "Pretty-print a sequence of class body declarations."
    :long
    (xdoc::topstring-p
     "Each one is preceded by a blank line.")
    (cond ((endp body-elements) nil)
          (t (append (list (print-jline-blank))
                     (print-jcbody-element (car body-elements)
                                           indent-level)
                     (print-jcbody-element-list (cdr body-elements)
                                                indent-level))))
    :measure (jcbody-element-list-count body-elements))

  (define print-jclass ((class jclassp) (indent-level natp))
    :returns (lines msg-listp)
    :short "Pretty-print a class declaration."
    (b* (((jclass class) class)
         (modifiers (msg "~@0~@1~@2~@3~@4"
                         (print-jaccess class.access)
                         (if class.abstract? "abstract " "")
                         (if class.static? "static " "")
                         (if class.final? "final " "")
                         (if class.strictfp? "strictfp " ""))))
      (append (list (print-jline (msg "~@0class ~@1 ~@2{"
                                      modifiers
                                      class.name
                                      (if class.superclass?
                                          (msg "extends ~@0 "
                                               class.superclass?)
                                        ""))
                                 indent-level))
              (print-jcbody-element-list class.body (1+ indent-level))
              (list (print-jline "}" indent-level))))
    :measure (jclass-count class)))

(define print-jclass-list ((classes jclass-listp) (indent-level natp))
  :returns (lines msg-listp)
  :short "Pretty-print a sequence of class declarations."
  :long
  (xdoc::topstring-p
   "Each one is preceded by a blank line.")
  (cond ((endp classes) nil)
        (t (append (list (print-jline-blank))
                   (print-jclass (car classes) indent-level)
                   (print-jclass-list (cdr classes) indent-level)))))

(define print-jimport ((import jimportp) (indent-level natp))
  :returns (line msgp)
  :short "Pretty-print an import declaration."
  (print-jline (msg "import ~s0~@1;"
                    (if (jimport->static? import) "static " "")
                    (jimport->target import))
               indent-level))

(define print-jimports ((imports jimport-listp) (indent-level natp))
  :returns (lines msg-listp)
  :short "Pretty-print a sequence of import declarations."
  (cond ((endp imports) nil)
        (t (cons (print-jimport (car imports) indent-level)
                 (print-jimports (cdr imports) indent-level)))))

(define print-jcunit ((cunit jcunitp))
  :returns (lines msg-listp)
  :short "Pretty-print a compilation unit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function does not have an indentation level argument,
     because it starts at level 0.")
   (xdoc::p
    "If there is a package declaration,
     we precede the import declarations (if any)
     with a blank line to separate the latter from the former."))
  (b* (((jcunit cunit) cunit))
    (append (if cunit.package?
                (list (print-jline (msg "package ~@0;"
                                        cunit.package?)
                                   0))
              nil)
            (if (and cunit.imports
                     cunit.package?)
                (cons (print-jline-blank)
                      (print-jimports cunit.imports 0))
              (print-jimports cunit.imports 0))
            (print-jclass-list cunit.types 0))))

(define print-jlines-to-channel ((lines msg-listp) (channel symbolp) state)
  :returns state
  :mode :program ; because of FMT1!
  :short "Write pretty-printed lines to an output channel."
  (cond ((endp lines) state)
        (t (b* (((mv & state) (fmt1! "~@0"
                                     (list (cons #\0 (car lines)))
                                     0 channel state nil)))
             (print-jlines-to-channel (cdr lines) channel state)))))

(defttag :open-input-channel)

(define print-to-jfile ((lines msg-listp) (filename stringp) state)
  :returns state
  :mode :program ; because of FMT1! in PRINT-JLINES-TO-CHANNEL
  :short "Write pretty-printed lines to a file."
  (b* (((mv channel state) (open-output-channel! filename :character state))
       (state (print-jlines-to-channel lines channel state))
       (state (close-output-channel channel state)))
    state))

(defttag nil)
