; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "files")

(include-book "kestrel/utilities/messages" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/strings/octal" :dir :system)
(include-book "std/strings/hex" :dir :system)

(local (include-book "std/typed-lists/character-listp" :dir :system))

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

(defxdoc+ pretty-printer
  :parents (concrete-syntax)
  :short "A pretty-printer for Leo (code) files."
  :long
  (xdoc::topstring
   (xdoc::p
    "This pretty-printer produces text
     in the form of @(tsee msgp) and @(tsee msg-listp) values.
     The latter generally consist of lines of text;
     that is always the case at the top level,
     i.e. a Leo file is turned into a list of lines.
     Some pretty-printing functions produce @(tsee msgp) values
     that other pretty-printing functions
     incorporate into larger text.
     In the pretty-printing functions,
     we consistently use the result names
     @('part') for @(tsee msgp) values that are part of lines,
     @('parts') for @(tsee msg-listp) values that are lists of parts of lines,
     @('line') for @(tsee msgp) values that are individual lines, and
     @('lines') for @(tsee msg-listp) values that are multiple lines."))
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
    this could be a pretty-printing option in the future.
    Thus, we return a string (which is also a message)
    consisting of a number of spaces equal to 4 times the level.")
  (str::implode (repeat (* 4 (lnfix level)) #\Space))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-comma-separated ((parts msg-listp))
  :returns (part msgp :hyp (msg-listp parts))
  :short "Turn zero or more parts into a single part
          containing the zero or more parts, comma-separated."
  (cond ((endp parts) "")
        ((endp (cdr parts)) (car parts))
        (t (msg "~@0, ~@1"
                (car parts)
                (pprint-comma-separated (cdr parts))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-boolean ((bool booleanp))
  :returns (part msgp)
  :short "Pretty-print a boolean."
  (if bool "true" "false")
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-natural ((nat natp))
  :returns (part msgp)
  :short "Pretty-print a natural number."
  (str::nat-to-dec-string nat)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-integer ((int integerp))
  :returns (part msgp)
  :short "Pretty-print an integer number."
  (str::int-to-dec-string int)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-char ((char charp))
  :returns (part msgp)
  :short "Pretty-print a character."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the Leo character is ASCII, there are two cases:
     if the code is between 32 and 126 (i.e. it is printable),
     we print the character as the corresponding ACL2 character;
     otherwise (i.e. the code is between 0 and 31, or is 127),
     we print it as an ASCII escape.
     If the Leo character is not ASCII, we print is as a Unicode escape."))
  (b* ((code (char->codepoint char)))
    (cond ((and (<= 32 code)
                (<= code 126))
           (str::implode (list (code-char code))))
          ((<= code 127)
           (msg "\\x~s0~s1"
                (str::implode
                 (list (str::octal-digit-to-char (truncate code 16))))
                (str::implode
                 (list (str::hex-digit-to-char (rem code 16))))))
          (t (msg "\\u{~s0}"
                  (str::nat-to-hex-string code)))))
  :hooks (:fix)
  :prepwork ((local (include-book "arithmetic-3/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-char-list ((chars char-listp))
  :returns (part msgp)
  :short "Pretty-print a list of characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "We juxtapose them one after the other."))
  (cond ((endp chars) "")
        (t (msg "~@0~@1"
                (pprint-char (car chars))
                (pprint-char-list (cdr chars)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-address ((addr addressp))
  :returns (part msgp)
  :short "Pretty-print an address."
  (address->name addr)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-identifier ((iden identifierp))
  :returns (part msgp)
  :short "Pretty-print an identifier."
  (identifier->name iden)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-programid ((id programidp))
  :returns (part msgp)
  :short "Pretty-print a @('programid')."
  (msg "~@0.~@1"
       (pprint-identifier (programid->name id))
       (pprint-identifier (programid->network id)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-locator ((loc locatorp))
  :returns (part msgp)
  :short "Pretty-print a locator."
  (msg "~@0/~@1"
       (pprint-programid (locator->program loc))
       (pprint-identifier (locator->name loc)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-bitsize-to-utype ((bsz bitsizep))
  :returns (part msgp)
  :short "Pretty-print a bit size to an unsigned type."
  (bitsize-case bsz
                :8 "u8"
                :16 "u16"
                :32 "u32"
                :64 "u64"
                :128 "u128")
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-bitsize-to-itype ((bsz bitsizep))
  :returns (part msgp)
  :short "Pretty-print a bit size to a signed type."
  (bitsize-case bsz
                :8 "i8"
                :16 "i16"
                :32 "i32"
                :64 "i64"
                :128 "i128")
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-coordinate ((coor coordinatep))
  :returns (part msgp)
  :short "Pretty-print a group literal coordinate."
  (coordinate-case coor
                   :explicit (pprint-integer coor.get)
                   :sign-high "+"
                   :sign-low "-"
                   :inferred "_")
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-group-literal ((lit group-literalp))
  :returns (part msgp)
  :short "Pretty-print a group literal."
  (group-literal-case lit
                      :affine (msg "(~@0, ~@1)group"
                                   (pprint-coordinate lit.x)
                                   (pprint-coordinate lit.y))
                      :product (msg "~@0group"
                                    (pprint-natural lit.factor)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-literal ((lit literalp))
  :returns (part msgp)
  :short "Pretty-print a literal."
  (literal-case lit
                :bool (pprint-boolean lit.val)
                :unsigned (msg "~@0~@1"
                               (pprint-natural lit.val)
                               (pprint-bitsize-to-utype lit.size))
                :signed (msg "~@0~@1"
                             (pprint-natural lit.val)
                             (pprint-bitsize-to-itype lit.size))
                :string (msg "\"~@0\""
                             (pprint-char-list lit.get))
                :address (pprint-address lit.get)
                :field (msg "~@0field"
                            (pprint-natural lit.val))
                :group (pprint-group-literal lit.get)
                :scalar (msg "~@0scalar"
                             (pprint-natural lit.val)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines pprint-type
  :short "Pretty-print a type."

  (define pprint-type ((type typep))
    :returns (part msgp)
    (type-case type
               :bool "bool"
               :unsigned (pprint-bitsize-to-utype type.size)
               :signed (pprint-bitsize-to-itype type.size)
               :field "field"
               :group "group"
               :scalar "scalar"
               :address "address"
               :string "string"
               :internal-named (if type.recordp
                                   (msg "~@0.record" (pprint-identifier type.get))
                                 (msg "~@0" (pprint-identifier type.get)))
               :external-named (if type.recordp
                                   (msg "~@0.record" (pprint-locator type.get))
                                 (msg "~@0" (pprint-locator type.get)))
               :unit "()"
               :tuple (msg "(~@0)"
                           (pprint-comma-separated
                            (pprint-type-list type.components))))
    :measure (type-count type))

  (define pprint-type-list ((types type-listp))
    :returns (parts msg-listp)
    (cond ((endp types) nil)
          (t (cons (pprint-type (car types))
                   (pprint-type-list (cdr types)))))
    :measure (type-list-count types))

  :verify-guards nil ; done below
  ///
  (verify-guards pprint-type)

  (fty::deffixequiv-mutual pprint-type))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *unops-opcall-print-names*
  :short "Unary operators to be printed as @('e.op().')"
  :long
  (xdoc::topstring
   (xdoc::p
    "This constant is an alist that maps unary operator types
     to the identifier string used to print them using operator-call syntax.")
   (xdoc::p
    "If a unary operator type is not a key in this map,
     then the unary operator will be printed in prefix form
     by @(see pprint-unop).")
   (xdoc::p
    "Some unary operators only have operator-call syntax
     and some have both operator-call syntax and prefix syntax.
     The former must be listed here to printable; the latter
     may be added here to force them to print in operator-call
     syntax."))
  '((:abs . "abs")
    (:abs-wrapped . "abs_wrapped")
    (:double . "double")
    (:inv . "inv")
    (:square . "square")
    (:square-root . "square_root")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-unop ((op unopp))
  :returns (part msgp)
  :short "Pretty-print a unary operator."
  (unop-case op
             :not "!"
             :neg "-"
             :otherwise (prog2$ (raise "op ~x0 should have been handled as an operator call" (unop-kind op))
                                "ERROR"))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *binops-opcall-print-names*
  :short "Binary operators to be printed as @('e1.op(e2).')"
  :long
  (xdoc::topstring
   (xdoc::p
    "This constant is an alist that maps binary operator types
     to the identifier string used to print them using operator-call syntax.")
   (xdoc::p
    "If a binary operator type is not a key in this map,
     then the binary operator will be printed in infix form
     by @(see pprint-binop).")
   (xdoc::p
    "Some binary operators only have operator-call syntax
     and some have both operator-call syntax and prefix syntax.
     The former must be listed here to printable; the latter
     may be added here to force them to print in operator-call
     syntax."))
  '((:nand . "nand")
    (:nor . "nor")
    (:pow-wrapped . "pow_wrapped")
    (:mul-wrapped . "mul_wrapped")
    (:div-wrapped . "div_wrapped")
    (:rem-wrapped . "rem_wrapped")
    (:add-wrapped . "add_wrapped")
    (:sub-wrapped . "sub_wrapped")
    (:shl-wrapped . "shl_wrapped")
    (:shr-wrapped . "shr_wrapped")
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-binop ((op binopp))
  :returns (part msgp)
  :short "Pretty-print a binary operator."
  (binop-case op
              :and "&&"
              :or "||"
              :eq "=="
              :ne "!="
              :ge ">="
              :gt ">"
              :le "<="
              :lt "<"
              :bitxor "^"
              :bitior "|"
              :bitand "&"
              :shl "<<"
              :shr ">>"
              :add "+"
              :sub "-"
              :mul "*"
              :div "/"
              :rem "%"
              :pow "**"
              :otherwise (prog2$ (raise "op ~x0 should have been handled as an operator call"
                                        (binop-kind op))
                                 "ERROR")
              )
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc pprint-expression-algorithm
  :short "Algorithm for pretty-printing expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The tree structure of the abstract syntax of expressions
     describes the grouping of nested subexpressions.
     For instance, the tree")
   (xdoc::codeblock
    "(expression-binary (binop-mul)"
    "                   (expression-binary (binop-add)"
    "                                      (expression-var/const"
    "                                       (identifier \"x\"))"
    "                                      (expression-var/const"
    "                                       (identifier \"y\")))"
    "                   (expression-var/const (identifier \"z\")))")
   (xdoc::p
    "represents the expression @('(x + y) * z').
     Note that, when this expression is written in concrete syntax as just done,
     parentheses must be added,
     because @('*') binds tighter (i.e. has a higher priority) than @('+').")
   (xdoc::p
    "The relative priorities of operators are implicitly defined
     by the grammar of expressions,
     which also defines the left vs. right associativity
     of binary operators.
     For instance, the ABNF grammar rules of Leo tells us that
     (i) @('+') binds tighter than @('*') and
     (ii) @('+') is left-associative:")
   (xdoc::ul
    (xdoc::li
     "Consider an expression @('x + y * z').
      In order to parse this as a @('multiplicative-expression')
      @('x + y') would have to be a @('multiplicative-expression'),
      which is not.
      Thus, the original expression can only be parsed
      as an @('additive-expression').")
    (xdoc::li
     "Consider an expression @('x * y + z').
      In order to parse this as a @('multiplicative-expression'),
      @('y + z') would have to be an @('exponential-expression'),
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
     based on the relative priorities of the operators
     and the left or right associativity of the binary operators,
     following the grammar.
     The approach is explained in the following paragraphs.")
   (xdoc::p
    "We define `grades' of expressions
     that correspond to certain nonterminals of the grammar,
     such as a grade of additive expressions
     corresponding to the nonterminal @('additive-expression').
     We define a mapping from the expressions of our abstract syntax
     to their grades,
     e.g. @('(expression-binary (binop-add) ... ...)')
     and @('(expression-binary (binop-sub) ... ...)')
     are mapped to the grade of additive expressions.")
   (xdoc::p
    "We define a total order on expression grades that is
     the reflexive and transitive closure of the binary relation
     that consists of the pairs @('grade1 < grade2') such that
     there is a grammar (sub)rule @('nonterm2 = nonterm1')
     saying that the nonterminal @('nonterm2') corresponding to @('grade2')
     may expand to the nonterminal @('nonterm1') corresponding to @('grade1').
     For instance, @('grade1') is the grade of multiplicative expressions
     and @('grade2') is the grade of additive expressions,
     because there is a (sub)rule
     @('additive-expression = multiplicative-expression') in the grammar.
     (Here by `subrule' we mean a rule not necessarily in the grammar
     but obtainable by selecting just some of the alternatives in the definiens
     that are different grammar alternatives.)
     The nonterminal @('additive-expression') also has other alternatives,
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
     the nonterminal @('expression').
     As the pretty-printer descends into subexpressions,
     the second argument is changed according to
     the grammar rule corresponding to the super-expressions.
     For instance, when pretty-printing the left and right subexpressions
     of a super-expression @('(expression-binary (binop-add) left right)'),
     we recursively call the pretty-printer twice,
     once on @('left') and once on @('right').
     Because of the grammar rule
     @('additive-expression =
        additive-expression \"+\" multiplicative-expression')
     that corresponds to the super-expression,
     the recursive call on @('left') will have as second argument
     the grade of @('additive-expression'),
     while the recursive call on @('right') will have as second argument
     the grade of @('multiplicative-expression').
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
     i.e. the grade corresponding to @('primary-expression'),
     which again lets the parenthesized expression be parsed
     into an expression of the expected grade.")
   (xdoc::p
    "For instance, consider the abstract syntax tree for @('(x + y) * z'),
     shown earlier as motivating example.
     Assume that it is pretty-printed as a top-level expression,
     i.e. that the second argument is the grade of @('expression')
     (the expected grade).
     Since the actual grade of the expression is
     the one for @('multiplicative-expression'),
     which is less than or equal to the one for @('expression')
     (via
     @('conditional-expression'),
     @('binary-expression'),
     @('boolean-or-expression'),
     @('boolean-and-expression'),
     @('equality-expression'),
     @('ordering-expression'),
     @('bitwise-exclusive-or-expression'),
     @('bitwise-inclusive-or-expression'),
     @('bitwise-and-expression'),
     @('shift-expression'), and
     @('additive-expression')),
     no parentheses are printed at the top level.

     When pretty-printing the left subexpression @('x + y'),
     the expected grade is @('multiplicative-expression'):
     since the actual grade of @('x + y') is @('additive-expression'),
     which is greater than the expected grade,
     parentheses must be added,
     as mentioned when the example was first presented.
     On the other hand, when pretty-printing the right subexpression @('z'),
     the expected grade is @('exponential-expression'):
     since the actual grade of @('z') is @('primary-expression'),
     which is less than the expected grade,
     no parentheses are printed.")
   (xdoc::p
    "The total order on expression grades only considers, as mentioned,
     (sub)rules of the form @('nonterm2: nonterm1')
     where @('nonterm1') is a single nonterminal.
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
    "See @(see pprint-expression-algorithm) for background.")
   (xdoc::p
    "The grade @(':top') corresponds to the nonterminal @('expression');
     each of the other grades, @(':<grade>'), corresponds to
     the nonterminal @('<grade>-expression').")
   (xdoc::p
    "We do not need a grade for @('binary-expression'),
     which is just a synonym of @('boolean-or-expression').")
   (xdoc::p
    "We stop at primary expressions:
     we do not need grades for @('identifier'), @('literal'), etc."))
  (:top ())
  (:conditional ())
  (:disjunctive ())
  (:conjunctive ())
  (:equality ())
  (:ordering ())
  (:bitwise-xor ())
  (:bitwise-ior ())
  (:bitwise-and ())
  (:shift ())
  (:additive ())
  (:multiplicative ())
  (:exponential ())
  (:unary ())
  (:postfix ())
  (:primary ())
  :pred expr-gradep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr->grade ((expr expressionp))
  :returns (grade expr-gradep)
  :short "Grade of an abstract syntactic expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see pprint-expression-algorithm) for background."))
  (expression-case expr
                   :literal (expr-grade-primary)
                   :var/const (expr-grade-primary)
                   :assoc-const (expr-grade-primary)
                   :unary (expr-grade-unary)
                   :binary (binop-case expr.op
                                       :pow (expr-grade-exponential)
                                       :mul (expr-grade-multiplicative)
                                       :div (expr-grade-multiplicative)
                                       :rem (expr-grade-multiplicative)
                                       :add (expr-grade-additive)
                                       :sub (expr-grade-additive)
                                       :shr (expr-grade-shift)
                                       :shl (expr-grade-shift)
                                       :bitand (expr-grade-bitwise-and)
                                       :bitior (expr-grade-bitwise-ior)
                                       :bitxor (expr-grade-bitwise-xor)
                                       :lt (expr-grade-ordering)
                                       :gt (expr-grade-ordering)
                                       :le (expr-grade-ordering)
                                       :ge (expr-grade-ordering)
                                       :eq (expr-grade-equality)
                                       :ne (expr-grade-equality)
                                       :and (expr-grade-conjunctive)
                                       :or (expr-grade-disjunctive)
                                       ;; operator call syntax:
                                       :nand (expr-grade-postfix)
                                       :nor (expr-grade-postfix)
                                       :pow-wrapped (expr-grade-postfix)
                                       :mul-wrapped (expr-grade-postfix)
                                       :div-wrapped (expr-grade-postfix)
                                       :rem-wrapped (expr-grade-postfix)
                                       :add-wrapped (expr-grade-postfix)
                                       :sub-wrapped (expr-grade-postfix)
                                       :shr-wrapped (expr-grade-postfix)
                                       :shl-wrapped (expr-grade-postfix))
                   :unit (expr-grade-primary)
                   :tuple (expr-grade-primary)
                   :tuple-component (expr-grade-postfix)
                   :struct (expr-grade-primary)
                   :struct-component (expr-grade-postfix)
                   :cond (expr-grade-conditional)
                   :internal-call (expr-grade-primary)
                   :external-call (expr-grade-primary)
                   :static-call (expr-grade-primary))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-grade-<= ((grade1 expr-gradep) (grade2 expr-gradep))
  :returns (yes/no booleanp)
  :short "Total order over expression grades."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see pprint-expression-algorithm) for background.")
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
                      :top 14
                      :conditional 14
                      :disjunctive 13
                      :conjunctive 12
                      :equality 11
                      :ordering 10
                      :bitwise-xor 9
                      :bitwise-ior 8
                      :bitwise-and 7
                      :shift 6
                      :additive 5
                      :multiplicative 4
                      :exponential 3
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
    "See @(see pprint-expression-algorithm) for background.")
   (xdoc::p
    "These are based on the grammar rules."))
  (binop-case op
              :pow (mv (expr-grade-unary) (expr-grade-exponential))
              :mul (mv (expr-grade-multiplicative) (expr-grade-exponential))
              :div (mv (expr-grade-multiplicative) (expr-grade-exponential))
              :rem (mv (expr-grade-multiplicative) (expr-grade-exponential))
              :add (mv (expr-grade-additive) (expr-grade-multiplicative))
              :sub (mv (expr-grade-additive) (expr-grade-multiplicative))
              :shl (mv (expr-grade-shift) (expr-grade-additive))
              :shr (mv (expr-grade-shift) (expr-grade-additive))
              :bitand (mv (expr-grade-bitwise-and) (expr-grade-shift))
              :bitior (mv (expr-grade-bitwise-ior) (expr-grade-bitwise-and))
              :bitxor (mv (expr-grade-bitwise-xor) (expr-grade-bitwise-ior))
              :lt (mv (expr-grade-additive) (expr-grade-additive))
              :gt (mv (expr-grade-additive) (expr-grade-additive))
              :le (mv (expr-grade-additive) (expr-grade-additive))
              :ge (mv (expr-grade-additive) (expr-grade-additive))
              :eq (mv (expr-grade-ordering) (expr-grade-ordering))
              :ne (mv (expr-grade-ordering) (expr-grade-ordering))
              :and (mv (expr-grade-conjunctive) (expr-grade-equality))
              :or (mv (expr-grade-disjunctive) (expr-grade-conjunctive))
              :nand (mv (expr-grade-postfix) (expr-grade-top))
              :nor (mv (expr-grade-postfix) (expr-grade-top))
              :pow-wrapped (mv (expr-grade-postfix) (expr-grade-top))
              :mul-wrapped (mv (expr-grade-postfix) (expr-grade-top))
              :div-wrapped (mv (expr-grade-postfix) (expr-grade-top))
              :rem-wrapped (mv (expr-grade-postfix) (expr-grade-top))
              :add-wrapped (mv (expr-grade-postfix) (expr-grade-top))
              :sub-wrapped (mv (expr-grade-postfix) (expr-grade-top))
              :shl-wrapped (mv (expr-grade-postfix) (expr-grade-top))
              :shr-wrapped (mv (expr-grade-postfix) (expr-grade-top))
              )
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines pprint-expression
  :short "Pretty-print an expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see pprint-expression-algorithm) for background.")
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
     that all have the same required grade."))

  (define pprint-expression ((expr expressionp)
                             (expected-grade expr-gradep))
    :returns (part msgp)
    (b* ((actual-grade (expr->grade expr))
         (part
          (expression-case
           expr
           :literal (pprint-literal expr.get)
           :var/const (pprint-identifier expr.name)
           :assoc-const (msg "~@0::~@1"
                             (pprint-type expr.type)
                             (pprint-identifier expr.name))
           :unary
           (b* ((op-call-name (cdr (assoc (unop-kind expr.op)
                                          *unops-opcall-print-names*)))
                ((when (stringp op-call-name))
                 (msg "~@0.~@1()"
                      ;; NOTE: when postfix-expression is added this
                      ;; expr-grade-primary may need to change to
                      ;; expr-grade-postfix.
                      (pprint-expression expr.arg (expr-grade-primary))
                      op-call-name)))
             (msg "~@0~@1"
                  (pprint-unop expr.op)
                  (pprint-expression expr.arg (expr-grade-unary))))
           :binary
           (b* ((op-call-name (cdr (assoc (binop-kind expr.op)
                                          *binops-opcall-print-names*)))
                ((when (stringp op-call-name))
                 (msg "BINOP OPERATOR CALL PRINTING NOT YET SUPPORTED"))
                ((mv left-grade right-grade)
                 (binop-expected-grades expr.op)))
             (msg "~@0 ~@1 ~@2"
                  (pprint-expression expr.arg1 left-grade)
                  (pprint-binop expr.op)
                  (pprint-expression expr.arg2 right-grade)))
           :cond
           (msg "~@0 ? ~@1 : ~@2"
                (pprint-expression expr.test (expr-grade-disjunctive))
                (pprint-expression expr.then (expr-grade-top))
                (pprint-expression expr.else (expr-grade-top)))
           :unit (msg "()")
           :tuple
           (msg "(~@0)"
                (pprint-comma-separated
                 (pprint-expression-list expr.components (expr-grade-top))))
           :tuple-component
           (msg "~@0.~@1"
                (pprint-expression expr.tuple (expr-grade-postfix)))
           :struct
           (msg "~@0 { ~@1 }"
                (pprint-identifier expr.type)
                (pprint-comma-separated
                 (pprint-struct-init-list expr.components)))
           :struct-component
           (msg "~@0.~@1"
                (pprint-expression expr.struct (expr-grade-postfix))
                (pprint-identifier expr.component))
           :internal-call
           (msg "~@0(~@1)"
                (pprint-identifier expr.fun)
                (pprint-comma-separated
                 (pprint-expression-list expr.args (expr-grade-top))))
           :external-call
           (msg "~@0(~@1)"
                (pprint-locator expr.fun)
                (pprint-comma-separated
                 (pprint-expression-list expr.args (expr-grade-top))))
           :static-call
           (msg "~@0::~@1(~@2)"
                (pprint-type expr.type)
                (pprint-identifier expr.fun)
                (pprint-comma-separated
                 (pprint-expression-list expr.args (expr-grade-top)))))))
      (if (expr-grade-<= actual-grade expected-grade)
          part
        (msg "(~@0)" part)))
    :measure (expression-count expr))

  (define pprint-expression-list ((exprs expression-listp)
                                  (expected-grade expr-gradep))
    :returns (parts msg-listp)
    (cond ((endp exprs) nil)
          (t (cons (pprint-expression (car exprs) expected-grade)
                   (pprint-expression-list (cdr exprs) expected-grade))))
    :measure (expression-list-count exprs))

  (define pprint-struct-init ((cinit struct-initp))
    :returns (part msgp)
    (msg "~@0: ~@1"
         (pprint-identifier (struct-init->name cinit))
         (pprint-expression (struct-init->expr cinit) (expr-grade-top)))
    :measure (struct-init-count cinit))

  (define pprint-struct-init-list ((cinits struct-init-listp))
    :returns (parts msg-listp)
    (cond ((endp cinits) nil)
          (t (cons (pprint-struct-init (car cinits))
                   (pprint-struct-init-list (cdr cinits)))))
    :measure (struct-init-list-count cinits))

  :ruler-extenders :all

  :verify-guards nil ; done below
  ///
  (verify-guards pprint-expression)

  (fty::deffixequiv-mutual pprint-expression
                           :hints (("Goal" :in-theory (enable expr->grade)))))

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
  (msg "~s0~@1~%" (pprint-indent level) content)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-vardecl ((decl vardeclp) (level natp))
  :returns (line msgp)
  :short "Pretty-print a variable declaration."
  (b* (((vardecl decl) decl))
    (pprint-line
     (msg "let ~@0: ~@1 = ~@2;"
          (pprint-identifier decl.name)
          (pprint-type decl.type)
          (pprint-expression decl.init (expr-grade-top)))
     level))
  :prepwork ((local (in-theory (disable nfix))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-constdecl ((decl constdeclp) (level natp))
  :returns (line msgp)
  :short "Pretty-print a constant declaration."
  (b* (((constdecl decl) decl))
    (pprint-line
     (msg "const ~@0: ~@1 = ~@2;"
          (pprint-identifier decl.name)
          (pprint-type decl.type)
          (pprint-expression decl.init (expr-grade-top)))
     level))
  :prepwork ((local (in-theory (disable nfix))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-console ((cnsl consolep) (level natp))
  :returns (line msgp)
  :short "Pretty-print a console call."
  (pprint-line
   (console-case
    cnsl
    :assert (msg "console.assert(~@0);"
                 (pprint-expression cnsl.arg (expr-grade-top)))
    :error (msg "console.error(\"~@0\"~s1~@2);"
                (pprint-char-list cnsl.string)
                (if (consp cnsl.exprs) "," "")
                (pprint-comma-separated
                 (pprint-expression-list cnsl.exprs (expr-grade-top))))
    :log (msg "console.log(\"~@0\"~s1~@2);"
              (pprint-char-list cnsl.string)
              (if (consp cnsl.exprs) "," "")
              (pprint-comma-separated
               (pprint-expression-list cnsl.exprs (expr-grade-top)))))
   level)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines pprint-statement
  :short "Pretty-print a statement."

  (define pprint-statement ((stmt statementp) (level natp))
    :returns (lines msg-listp)
    (statement-case
     stmt
     :let (list (pprint-vardecl stmt.get level))
     :const (list (pprint-constdecl stmt.get level))
     :assign (list (pprint-line
                    (msg "~@0 = ~@1;"
                         (pprint-expression stmt.left (expr-grade-top))
                         (pprint-expression stmt.right (expr-grade-top)))
                    level))
     :return (list (pprint-line
                    (msg "return ~@0;"
                         (pprint-expression stmt.value (expr-grade-top)))
                    level))
     :for (append (list (pprint-line
                         (msg "for ~@0: ~@1 in ~@2..~s3~@4 {"
                              (pprint-identifier stmt.name)
                              (pprint-type stmt.type)
                              (pprint-expression stmt.from (expr-grade-top))
                              (if stmt.inclusivep "=" "")
                              (pprint-expression stmt.to (expr-grade-top)))
                         level))
                  (pprint-statement-list stmt.body (1+ level))
                  (list (pprint-line "}" level)))
     :if (append (pprint-branch-list stmt.branches level)
                 (list (pprint-line "else {" level))
                 (pprint-statement-list stmt.else (1+ level))
                 (list (pprint-line "}" level)))
     :console (list (pprint-console stmt.get level))
     ;; TODO: the next three
     :finalize (list (pprint-line
                      "pretty-print-finalize-statement-not-yet-implemented"
                      level))
     :increment (list (pprint-line
                       "pretty-print-increment-statement-not-yet-implemented"
                       level))
     :decrement (list (pprint-line
                       "pretty-print-decrement-statement-not-yet-implemented"
                       level))
     :block (append (list (pprint-line "{" level))
                    (pprint-statement-list stmt.get (1+ level))
                    (list (pprint-line "}" level))))
    :measure (statement-count stmt))

  (define pprint-statement-list ((stmts statement-listp) (level natp))
    :returns (lines msg-listp)
    (cond ((endp stmts) nil)
          (t (append (pprint-statement (car stmts) level)
                     (pprint-statement-list (cdr stmts) level))))
    :measure (statement-list-count stmts))

  (define pprint-branch ((branch branchp) (level natp))
    :returns (lines msg-listp)
    (b* (((branch branch) branch))
      (append (list (pprint-line
                     (msg "if ~@0 {"
                          (pprint-expression branch.test (expr-grade-top)))
                     level))
              (pprint-statement-list branch.body (1+ level))
              (list (pprint-line "}" level))))
    :measure (branch-count branch))

  (define pprint-branch-list ((branches branch-listp) (level natp))
    :returns (lines msg-listp)
    (cond ((endp branches) nil)
          (t (append (pprint-branch (car branches) level)
                     (pprint-branch-list (cdr branches) level))))
    :measure (branch-list-count branches)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-var/const-sort ((fps var/const-sortp))
  :returns (part msgp)
  :short "Pretty-print a variable or constant sort."
  :long
  (xdoc::topstring
   (xdoc::p
    "Nothing is printed for private, since it is the default.")
   (xdoc::p
    "A space is printed after each of the others,
     so that the message part returned by this fucntion
     can be always put in front of the rest of the function parameter."))
  (var/const-sort-case fps
                      :public "public "
                      :private ""
                      :constant "constant "
                      :const "const ")
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-funparam ((param funparamp))
  :returns (part msgp)
  :short "Pretty-print a function parameter."
  (b* (((funparam param) param))
    (msg "~@0~@1: ~@2"
         (pprint-var/const-sort param.sort)
         (pprint-identifier param.name)
         (pprint-type param.type)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-funparam-list ((params funparam-listp))
  :returns (parts msg-listp)
  :short "Pretty-print a list of function parameters."
  (cond ((endp params) nil)
        (t (cons (pprint-funparam (car params))
                 (pprint-funparam-list (cdr params)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-annotation ((ann annotationp) (level natp))
  :returns (line msgp)
  :short "Pretty-print an annotation."
  (b* (((annotation ann) ann))
    (pprint-line (msg "@~@0"
                      (pprint-identifier ann.name))
                 level)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-annotation-list ((anns annotation-listp)
                               (level natp))
  :returns (lines msg-listp)
  :short "Pretty-print a list of annotations, one per line."
  (cond ((endp anns) nil)
        (t (cons (pprint-annotation (car anns) level)
                 (pprint-annotation-list (cdr anns) level)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-fundecl ((decl fundeclp) (level natp))
  :returns (lines msg-listp)
  :short "Pretty-print a function declaration."
  (b* (((fundecl decl) decl))
    (append (pprint-annotation-list decl.annotations level)
            (list (pprint-line
                   (msg "function ~@0(~@1) -> ~@2 {"
                        (pprint-identifier decl.name)
                        (pprint-comma-separated
                         (pprint-funparam-list decl.inputs))
                        (pprint-type decl.output))
                   level))
            (pprint-statement-list decl.body (1+ level))
            (list (pprint-line "}" level)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-compdecl ((decl compdeclp))
  :returns (part msgp)
  :short "Pretty-print a struct component declaration."
  (msg "~@0: ~@1"
       (pprint-identifier (compdecl->name decl))
       (pprint-type (compdecl->type decl)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-compdecl-list ((decls compdecl-listp) (level natp))
  :returns (lines msg-listp)
  :short "Pretty-print a list of struct component declarations."
  (cond ((endp decls) nil)
        ((endp (cdr decls)) (list (pprint-line (pprint-compdecl (car decls))
                                               level)))
        (t (append (list (pprint-line
                          (msg "~@0," (pprint-compdecl (car decls)))
                          level))
                   (pprint-compdecl-list (cdr decls) level)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-structdecl ((decl structdeclp) (level natp))
  :returns (lines msg-listp)
  :short "Pretty-print a struct declaration."
  (b* (((structdecl decl) decl))
    (append (list (pprint-line
                   (msg "~s0 ~@1 {"
                        (if decl.recordp "record" "struct")
                        (pprint-identifier decl.name))
                   level))
            (pprint-compdecl-list decl.components (1+ level))
            (list (pprint-line "}" level)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-mappingdecl ((decl mappingdeclp) (level natp))
  :returns (lines msg-listp)
  :short "Pretty-print a mapping declaration."
  (b* (((mappingdecl decl) decl))
    (list (pprint-line
           (msg "mapping ~@0: ~@1 => ~@2;"
                (pprint-identifier decl.name)
                (pprint-type decl.domain-type)
                (pprint-type decl.range-type))
           level))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-topdecl ((decl topdeclp))
  :returns (lines msg-listp)
  :short "Pretty-print a top-level declaration."
  (topdecl-case decl
                :function (pprint-fundecl decl.get 1)
                :struct (pprint-structdecl decl.get 1)
                :mapping (pprint-mappingdecl decl.get 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-topdecl-list ((decls topdecl-listp))
  :returns (lines msg-listp)
  :short "Pretty-print a list of top-level declarations."
  (cond ((endp decls) nil)
        ((endp (cdr decls)) (pprint-topdecl (car decls)))
        (t (append (pprint-topdecl (car decls))
                   (list (pprint-line-blank))
                   (pprint-topdecl-list (cdr decls))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-importdecl ((decl importdeclp))
  :returns (part msgp)
  :short "Pretty-print an import declaration."
  (msg "import ~@0;" (pprint-programid (importdecl->program decl)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-importdecl-list ((decls importdecl-listp))
  :returns (lines msg-listp)
  :short "Pretty-print a list of import-level declarations."
  (cond ((endp decls) nil)
        ((endp (cdr decls)) (list (pprint-importdecl (car decls))))
        (t (cons (pprint-importdecl (car decls))
                 (append
                  (list (pprint-line-blank))
                  (pprint-importdecl-list (cdr decls)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-programdecl ((pdecl programdeclp))
  :returns (lines msg-listp)
  :short "Pretty-print a program."
  (cons (pprint-line (msg "program ~@0 {"
                          (pprint-programid (programdecl->id pdecl)))
                     0)
        (append (pprint-topdecl-list (programdecl->items pdecl))
                (list (pprint-line (msg "}") 0))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pprint-file ((file filep))
  :returns (lines msg-listp)
  :short "Pretty-print a file."
  (append (pprint-importdecl-list (file->imports file))
          (pprint-programdecl (file->program file))))
