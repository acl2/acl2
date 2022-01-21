; Java Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "../types")
(include-book "../java-primitive-arrays")

(include-book "kestrel/std/system/check-unary-lambda-call" :dir :system)
(include-book "kestrel/std/system/unquote-term" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pre-translation-type-annotation
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          addition of type annotations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done only in the shallow embedding.")
   (xdoc::p
    "This step annotates ACL2 terms with ATJ types:
     (i) each ACL2 term is wrapped with a function named @('[src>dst]'),
     where @('src') identifies the ATJ types of the term
     and @('dst') identifies ATJ types to which the term must be converted to;
     (ii) each ACL2 variable @('var') in a term is renamed to @('[type]var'),
     where @('type') identifies the ATJ type of the variable.")
   (xdoc::p
    "Both @('src') and @('dst') above identify non-empty lists of ATJ types.
     This is because an ACL2 term may return multiple values (see @(tsee mv)):
     each list consists of two or more ATJ types when he ACL2 term does;
     otherwise, it consists of one ATJ type only.
     The two lists (for @('src') and @('dst')) will always have the same length,
     because ACL2 prevents treating
     single values as multiple values,
     multiple values as single values,
     or multiple values of a certain number
     as multiple values of a different number.
     Non-executable functions relax these restrictions,
     but their body includes calls of @('acl2::throw-nonexec-error'),
     which has raw Lisp code and is currently not whitelisted by ATJ.")
   (xdoc::p
    "These annotations facilitate the ACL2-to-Java translation,
     which uses the type annotations as ``instructions'' for
     (i) which types to declare Java local variables with, and
     (ii) which Java conversion code to insert around expressions.")
   (xdoc::p
    "The annotated terms are still ACL2 terms, but with a specific structure.
     This should let us prove, in the ACL2 logic,
     the equality of the annotated terms with the original terms,
     under suitable variable rebinding,
     and by introducing the @('[src>dst]') functions as identities.
     (This has not been done yet.)"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-id ((type atj-typep))
  :returns (id stringp)
  :short "Short string identifying an ATJ type."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use a short two-letter string to identify each ATJ type.
     For the @(':acl2') types,
     the first letter is @('A')
     and the second letter is from the class name or @('B') for @(':aboolean').
     For the @(':jprim') types,
     the first letter is @('J') and the second letter is from [JVMS:4.3.2].
     For the @(':jprimarr') types,
     the first letter is @('Y') (which is the ending letter of `array')
     and the second letter is from [JVMS:4.3.2]."))
  (atj-type-case type
                 :acl2 (atj-atype-case type.get
                                       :integer "AI"
                                       :rational "AR"
                                       :number "AN"
                                       :character "AC"
                                       :string "AS"
                                       :symbol "AY"
                                       :boolean "AB"
                                       :cons "AP"
                                       :value "AV")
                 :jprim (primitive-type-case type.get
                                             :boolean "JZ"
                                             :char "JC"
                                             :byte "JB"
                                             :short "JS"
                                             :int "JI"
                                             :long "JJ"
                                             :float "JF"
                                             :double "JD")
                 :jprimarr (primitive-type-case type.comp
                                                :boolean "YZ"
                                                :char "YC"
                                                :byte "YB"
                                                :short "YS"
                                                :int "YI"
                                                :long "YJ"
                                                :float "YF"
                                                :double "YD"))
  :hooks (:fix)
  ///

  (defrule atj-type-id-injective
    (equal (equal (atj-type-id x)
                  (atj-type-id y))
           (atj-type-equiv x y))
    :enable (atj-type-kind
             atj-type-fix
             atj-type-acl2->get
             atj-type-jprim->get
             atj-type-jprimarr->comp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-of-id ((id stringp))
  :returns (type atj-typep)
  :short "ATJ type identified by a short string."
  :long
  (xdoc::topstring-p
   "This is the inverse of @(tsee atj-type-id).")
  (cond ((equal id "AI") (atj-type-acl2 (atj-atype-integer)))
        ((equal id "AR") (atj-type-acl2 (atj-atype-rational)))
        ((equal id "AN") (atj-type-acl2 (atj-atype-number)))
        ((equal id "AC") (atj-type-acl2 (atj-atype-character)))
        ((equal id "AS") (atj-type-acl2 (atj-atype-string)))
        ((equal id "AY") (atj-type-acl2 (atj-atype-symbol)))
        ((equal id "AB") (atj-type-acl2 (atj-atype-boolean)))
        ((equal id "AP") (atj-type-acl2 (atj-atype-cons)))
        ((equal id "AV") (atj-type-acl2 (atj-atype-value)))
        ((equal id "JZ") (atj-type-jprim (primitive-type-boolean)))
        ((equal id "JC") (atj-type-jprim (primitive-type-char)))
        ((equal id "JB") (atj-type-jprim (primitive-type-byte)))
        ((equal id "JS") (atj-type-jprim (primitive-type-short)))
        ((equal id "JI") (atj-type-jprim (primitive-type-int)))
        ((equal id "JJ") (atj-type-jprim (primitive-type-long)))
        ((equal id "JF") (atj-type-jprim (primitive-type-float)))
        ((equal id "JD") (atj-type-jprim (primitive-type-double)))
        ((equal id "YZ") (atj-type-jprimarr (primitive-type-boolean)))
        ((equal id "YC") (atj-type-jprimarr (primitive-type-char)))
        ((equal id "YB") (atj-type-jprimarr (primitive-type-byte)))
        ((equal id "YS") (atj-type-jprimarr (primitive-type-short)))
        ((equal id "YI") (atj-type-jprimarr (primitive-type-int)))
        ((equal id "YJ") (atj-type-jprimarr (primitive-type-long)))
        ((equal id "YF") (atj-type-jprimarr (primitive-type-float)))
        ((equal id "YD") (atj-type-jprimarr (primitive-type-double)))
        (t (prog2$
            (raise "Internal error: ~x0 does not identify a type." id)
            (atj-type-irrelevant))))
  ///

  (defrule atj-type-of-id-of-atj-type-id
    (equal (atj-type-of-id (atj-type-id x))
           (atj-type-fix x))
    :enable (atj-type-id
             atj-type-fix
             atj-type-acl2->get
             atj-type-jprim->get
             atj-type-jprimarr->comp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-types-id ((types atj-type-listp))
  :guard (consp types)
  :returns (id stringp)
  :short "String identifying a non-empty list of ATJ types."
  :long
  (xdoc::topstring-p
   "We concatenate the short strings returned by @(tsee atj-type-id).")
  (atj-types-id-aux types)
  :hooks (:fix)

  :prepwork
  ((define atj-types-id-aux ((types atj-type-listp))
     :returns (id stringp)
     :parents nil
     (cond ((endp types) "")
           (t (str::cat (atj-type-id (car types))
                        (atj-types-id-aux (cdr types)))))
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-types-of-id ((id stringp))
  :returns (types atj-type-listp)
  :short "Non-empty list of ATJ types identified by
          a concatenation of short strings."
  :long
  (xdoc::topstring-p
   "This is the inverse of @(tsee atj-types-id).")
  (b* ((types (atj-types-of-id-aux (explode id) id)))
    (if (consp types)
        types
      (prog2$
       (raise "Internal error: ~x0 identifies an empty list of types." id)
       (list (atj-type-irrelevant)))))

  :prepwork
  ((define atj-types-of-id-aux ((chars character-listp) (id stringp))
     :returns (types atj-type-listp)
     :parents nil
     (b* (((when (endp chars)) nil)
          ((unless (>= (len chars) 2))
           (raise "Internal error: ~x0 does not identify a list of types." id))
          (first-id (implode (list (first chars) (second chars))))
          (first-type (atj-type-of-id first-id))
          (rest-types (atj-types-of-id-aux (cddr chars) id)))
       (cons first-type rest-types))))

  ///

  (more-returns
   (types consp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-conv ((src-types atj-type-listp) (dst-types atj-type-listp))
  :guard (and (consp src-types)
              (consp dst-types))
  :returns (name symbolp)
  :short "ATJ type conversion function names used to annotate ACL2 terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned in @(see atj-pre-translation-type-annotation),
     each ACL2 term is wrapped with a function named @('[src>dst]'),
     where @('src') identifies the ATJ types of the term
     and @('dst') identifies an ATJ types
     to which the term must be converted to.")
   (xdoc::p
    "These function names are all in the @('\"JAVA\"') package.
     For now we do not need these functions to actually exist in the ACL2 world,
     because annotated terms are only created ephemerally as data
     manipulated by the ATJ code generation functions.
     However, in order to prove that the type annotation process
     preserves the ACL2 meaning of terms,
     these functions will need to exist and be defined as identify functions,
     which can be easily done with a macro when that becomes important."))
  (intern$ (str::cat "["
                     (atj-types-id src-types)
                     ">"
                     (atj-types-id dst-types)
                     "]")
           "JAVA")
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-types-of-conv ((conv symbolp))
  :returns (mv (src-types atj-type-listp)
               (dst-types atj-type-listp))
  :short "Source and destination ATJ types of a conversion function."
  :long
  (xdoc::topstring-p
   "This is the inverse of @(tsee atj-type-conv).")
  (b* ((string (symbol-name conv))
       ((unless (and (> (length string) 0)
                     (eql (char string 0) #\[)
                     (eql (char string (1- (length string))) #\])))
        (raise "Internal error: ~x0 is not a conversion function." conv)
        (mv (list (atj-type-irrelevant)) (list (atj-type-irrelevant))))
       (pos (position #\> string))
       ((unless (natp pos))
        (raise "Internal error: ~x0 is not a conversion function." conv)
        (mv (list (atj-type-irrelevant)) (list (atj-type-irrelevant))))
       (src-id (subseq string 1 pos))
       (dst-id (subseq string (1+ pos) (1- (length string))))
       (src-types (atj-types-of-id src-id))
       (dst-types (atj-types-of-id dst-id)))
    (mv src-types dst-types))
  :guard-hints (("Goal"
                 :use ((:instance acl2::nth-of-index-when-member
                        (k #\>) (x (explode (symbol-name conv)))))
                 :in-theory (disable acl2::nth-of-index-when-member)))
  :prepwork ((local (include-book "std/lists/index-of" :dir :system)))
  ///

  (more-returns
   (src-types consp :rule-classes :type-prescription)
   (dst-types consp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-conv-allowed-p ((src-type atj-typep)
                                 (dst-type atj-typep))
  :returns (yes/no booleanp)
  :short "Ensure that a conversion between ATJ types is allowed."
  :long
  (xdoc::topstring
   (xdoc::p
    "Not all @('[src>dst]') wrappers are allowed during type annotation.
     These wrappers server to generate Java code
     to convert from the source to the destination types.
     This conversion is ``automatic'' in the sense that
     there is no corresponding conversion function
     in the original (i.e. not-typed-annotated) ACL2 code.")
   (xdoc::p
    "For example,
     we allow a conversion from @(':ainteger') to @(':anumber'),
     which may happen when an integer is passed to a function
     whose input type is that of numbers.
     As another example,
     we allow a conversion from @(':avalue') to @(':astring'),
     which may be justified by guard verification,
     since the inferred types are decidable over-approximations.")
   (xdoc::p
    "However, we do not allow conversions
     between @(':astring') and @(':anumber'),
     because those two types are disjoint:
     it is never the case, even when guards are verified,
     that a number may be (turned into) a string
     or a string may be (turned into) a number.
     This situation should only happen
     with program-mode or non-guard-verified code.")
   (xdoc::p
    "Among the @(':acl2') types, we allow conversions exactly when
     the two types have values in common.
     Currently this is only the case when one is a subset of the other,
     but future extensions of the ATJ types may result in
     more general situations.")
   (xdoc::p
    "We disallow any conversions
     involving the @(':jprim') and @(':jprimarr') types,
     unless the two types are identical, of course.
     That is, no @(':acl2') type can be converted to a @(':j...') type,
     and no @(':j...') type can be converted to an @(':acl2') type.
     Furthermore, no @(':j...') type can be converted
     to a different @(':j...') type.
     The reason for these restrictions is that we want to keep
     the @(':j...') types separate
     from each other and from the @(':acl2') types,
     and only allow explicit conversions between these,
     i.e. via functions that the developer must write
     in the original (i.e. non-typed-annotated) ACL2 code.")
   (xdoc::p
    "This predicate says whether
     a conversion between two single types is allowed.
     The predicate @(tsee atj-types-conv-allowed-p)
     does the same for type lists,
     which are actually used in the conversion functions
     used to wrap ACL2 terms during type annotation."))
  (if (and (atj-type-case src-type :acl2)
           (atj-type-case dst-type :acl2))
      (or (atj-type-<= src-type dst-type)
          (atj-type-<= dst-type src-type))
    (atj-type-equiv src-type dst-type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-types-conv-allowed-p ((src-types atj-type-listp)
                                  (dst-types atj-type-listp))
  :guard (and (consp src-types) (consp dst-types))
  :returns (yes/no booleanp)
  :short "Lift @(tsee atj-type-conv-allowed-p) to lists of types."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two lists should always have the same length.
     The conversion between type lists is allowed if and only if
     it is allowed element-wise."))
  (if (= (len src-types) (len dst-types))
      (atj-types-conv-allowed-p-aux src-types dst-types)
    (raise "Internal error: ~
            the type lists ~x0 and ~x1 differe in length."
           src-types dst-types))

  :prepwork
  ((define atj-types-conv-allowed-p-aux ((src-types atj-type-listp)
                                         (dst-types atj-type-listp))
     :guard (= (len src-types) (len dst-types))
     :returns (yes/no booleanp)
     :parents nil
     (or (endp src-types)
         (and (atj-type-conv-allowed-p (car src-types)
                                       (car dst-types))
              (atj-types-conv-allowed-p-aux (cdr src-types)
                                            (cdr dst-types)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-wrap-term ((term pseudo-termp)
                            (src-types atj-type-listp)
                            (dst-types? atj-type-listp))
  :guard (consp src-types)
  :returns (wrapped-term pseudo-termp)
  :short "Wrap an ACL2 term with a type conversion function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The conversion is from the source types to the destination types.
     If the destination types are the empty list,
     they are treated as if they were equal to the source types,
     i.e. the conversion is a no-op.")
   (xdoc::p
    "If the destination type list is not empty,
     we ensure that the conversion is allowed.
     If it is not, we stop with an error:
     this is a ``deep'' input validation error,
     because the problem is in the ACL2 code provided by the user."))
  (b* (((unless (mbt (pseudo-termp term))) nil)
       ((when (and (consp dst-types?)
                   (not (atj-types-conv-allowed-p src-types dst-types?))))
        (raise "Type annotation failure: ~
                cannot convert from ~x0 to ~x1."
               src-types dst-types?))
       (conv (if dst-types?
                 (atj-type-conv src-types dst-types?)
               (atj-type-conv src-types src-types))))
    (fcons-term* conv term)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-unwrap-term ((term pseudo-termp))
  :returns (mv (unwrapped-term pseudo-termp)
               (src-types atj-type-listp)
               (dst-types atj-type-listp))
  :short "Unwrap an ACL2 term wrapped by @(tsee atj-type-wrap-term)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is essentially the inverse function,
     except that it always returns a list of destination types,
     never @('nil')."))
  (b* ((term (if (mbt (pseudo-termp term)) term nil))
       ((when (or (variablep term)
                  (fquotep term)
                  (flambda-applicationp term)))
        (raise "Internal error: the term ~x0 has the wrong format." term)
        (mv nil (list (atj-type-irrelevant)) (list (atj-type-irrelevant))))
       (fn (ffn-symb term))
       ((when (flambdap fn))
        (raise "Internal error: the term ~x0 has the wrong format." term)
        (mv nil (list (atj-type-irrelevant)) (list (atj-type-irrelevant))))
       ((mv src-types dst-types) (atj-types-of-conv fn)))
    (mv (fargn term 1) src-types dst-types))
  ///

  (more-returns
   (src-types consp :rule-classes :type-prescription)
   (dst-types consp :rule-classes :type-prescription))

  (defret acl2-count-of-atj-type-unwrap-term-linear
    (implies unwrapped-term
             (< (acl2-count unwrapped-term)
                (acl2-count term)))
    :rule-classes :linear)

  (defret pseudo-term-count-of-atj-type-unwrap-term
    (implies (not (pseudo-term-case unwrapped-term :null))
             (< (pseudo-term-count unwrapped-term)
                (pseudo-term-count term)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable pseudo-term-call->args
                                       pseudo-term-kind
                                       pseudo-term-count)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-rewrap-term ((term pseudo-termp)
                              (dst-types atj-type-listp))
  :guard (consp dst-types)
  :returns (rewrapped-term pseudo-termp)
  :short "Re-wrap an ACL2 term with a type conversion function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when a term is
     preliminarily wrapped with a type conversion function,
     but its wrapping is then finalized with a different conversion function.
     So here we replace the wrapper.")
   (xdoc::p
    "We only change the destination types of the conversion function.
     The source types are unchanged.")
   (xdoc::p
    "We also check that the new conversion is allowed.
     We stop with an error if that is not the case;
     as in @(tsee atj-type-wrap-term),
     this is a ``deep'' input validation error.")
   (xdoc::p
    "If the term is a call of @(tsee if),
     we recursively re-wrap its branches,
     which therefore will return the same types.
     Then we wrap the @(tsee if) call
     with the identity conversion.
     The reason for descending into the @(tsee if) branches
     is that (the least upper bound of) the types of the @(tsee if) branches
     are used, in the translation to Java,
     to determine the types of the Java local variables
     that store the result of (one or the other) branch.
     In order to allow the mapping of ATJ subtypes to Java non-subtypes,
     we need to push the conversions into the @(tsee if) branches."))
  (b* (((mv term src-types &) (atj-type-unwrap-term term))
       ((when (null term)) ; for termination
        (raise "Internal error: unwrapped null term ~x0." term))
       ((when (not (atj-types-conv-allowed-p src-types dst-types)))
        (raise "Type annotation failure: ~
                cannot convert from ~x0 to ~x1."
               src-types dst-types))
       ((mv ifp test then else) (check-if-call term)))
    (if ifp
        (atj-type-wrap-term (fcons-term* 'if
                                         test
                                         (atj-type-rewrap-term then dst-types)
                                         (atj-type-rewrap-term else dst-types))
                            dst-types
                            dst-types)
      (atj-type-wrap-term term src-types dst-types)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-rewrap-terms ((terms pseudo-term-listp)
                               (dst-typess atj-type-list-listp))
  :guard (and (cons-listp dst-typess)
              (= (len terms) (len dst-typess)))
  :returns (rewrapped-terms pseudo-term-listp)
  :short "Lift @(tsee atj-type-rewrap-term) to lists."
  (cond ((endp terms) nil)
        (t (cons (atj-type-rewrap-term (car terms)
                                       (car dst-typess))
                 (atj-type-rewrap-terms (cdr terms)
                                        (cdr dst-typess))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-wrapped-variable-p ((term pseudo-termp))
  :returns (yes/no booleanp)
  :short "Check whether an annotated term is a variable."
  :long
  (xdoc::topstring-p
   "That is, we must first unwrap the term,
    and then check whether it is a variable.")
  (b* (((mv term & &) (atj-type-unwrap-term term)))
    (variablep term)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-annotate-var ((var symbolp) (types atj-type-listp))
  :guard (consp types)
  :returns (annotated-var symbolp)
  :short "Annotate an ACL2 variable with a non-empty list of types."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned in @(see atj-pre-translation-type-annotation),
     we systematically add type information to each ACL2 variable.
     We do so by adding @('[types]') before the variable name,
     where @('types') identifies a list of ATJ types.")
   (xdoc::p
    "The result of this function is never the symbol @('nil'),
     because the name of that symbol always starts with @('[')."))
  (packn-pos (list "[" (atj-types-id types) "]" var) var)
  ///

  (defrule atj-type-annotate-var-not-nil
    (implies (symbolp var)
             (not (equal (atj-type-annotate-var var types) nil)))
    :rule-classes :type-prescription
    :enable (atj-type-annotate-var)
    :disable symbol-name-intern-in-package-of-symbol
    :use ((:instance symbol-name-intern-in-package-of-symbol
           (s (implode (cons #\[
                             (append (explode (atj-types-id types))
                                     (cons #\] (explode-atom var 10))))))
           (any-symbol var))
          (:instance lemma
           (x "NIL")
           (y (implode (cons #\[
                             (append (explode (atj-types-id types))
                                     (cons #\] (explode-atom var 10))))))))
    :prep-lemmas
    ((defruled lemma
       (implies (and (stringp x)
                     (stringp y)
                     (equal x y))
                (equal (char x 0)
                       (char y 0)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-unannotate-var ((var symbolp))
  :returns (mv (unannotated-var symbolp)
               (types atj-type-listp))
  :short "Decompose an annotated ACL2 variable into
          its unannotated counterpart and its types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the inverse of @(tsee atj-type-annotate-var)."))
  (b* ((string (symbol-name var))
       ((unless (and (> (length string) 0)
                     (eql (char string 0) #\[)))
        (raise "Internal error: ~x0 is not an annotated variable." var)
        (mv nil (list (atj-type-irrelevant))))
       (pos (position #\] string))
       ((unless (natp pos))
        (raise "Internal error: ~x0 is not an annotated variable." var)
        (mv nil (list (atj-type-irrelevant))))
       (types-id (subseq string 1 pos))
       (types (atj-types-of-id types-id))
       (unannotated-string (subseq string (1+ pos) (length string)))
       (unannotated-var (intern-in-package-of-symbol unannotated-string var)))
    (mv unannotated-var types))
  :guard-hints (("Goal"
                 :use ((:instance acl2::nth-of-index-when-member
                        (k #\]) (x (explode (symbol-name var)))))
                 :in-theory (disable acl2::nth-of-index-when-member)))
  :prepwork ((local (include-book "std/lists/index-of" :dir :system)))
  ///

  (more-returns
   (types consp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-annotate-vars ((vars symbol-listp)
                                (types atj-type-listp))
  :guard (int= (len vars) (len types))
  :returns (new-vars symbol-listp)
  :short "Annotate each of a list of ACL2 variable
          with a corresponding singleton list of types."
  (cond ((endp vars) nil)
        (t (cons (atj-type-annotate-var (car vars) (list (car types)))
                 (atj-type-annotate-vars (cdr vars) (cdr types)))))
  ///

  (defret len-of-atj-type-annotate-vars
    (equal (len new-vars)
           (len vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-unannotate-vars ((vars symbol-listp))
  :returns (unannotated-vars symbol-listp)
  :short "Remove the type annotations from a list of variables."
  :long
  (xdoc::topstring-p
   "The annotating types are discarded.")
  (b* (((when (endp vars)) nil)
       ((mv var &) (atj-type-unannotate-var (car vars)))
       (vars (atj-type-unannotate-vars (cdr vars))))
    (cons var vars))
  ///

  (defret len-of-atj-type-unannotate-vars
    (equal (len unannotated-vars)
           (len vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-type-annotate-term
  :short "Add ATJ type annotations to ACL2 terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type annotation procedure involves inferring the types of terms,
     and wrapping terms with type conversion functions
     to match certain type requirements.")
   (xdoc::p
    "The @('var-types') input assigns types to (at least)
     all the free variables in the term that is being annotated.
     At the top level (see @(tsee atj-type-annotate-formals+body)),
     @('var-types') is initialized with the formal parameters of a function
     and with its corresponding input types.
     When we encounter a lambda expression in a term,
     @('var-types') is updated with an alist that assigns
     to the formal parameters of the lambda expression
     the types inferred for the actual arguments of the lambda expression;
     that is, unlike at the top level, at intermediate levels
     variables receive the types inferred for their binding terms.
     Here `updated' means that
     the new alist is appended before the existing one:
     recall that, due to the pre-translation step
     that removes trivial lambda-bound variables,
     lambda expressions may not be closed at this point;
     thus, the appending achieves the desired ``overwriting''.")
   (xdoc::p
    "Even though variables can be annotated by multiple types in general
     (see @(tsee atj-type-annotate-var)),
     @('var-types') assigns single types to variables.
     The only variables annotated with lists of two or more types
     are the @('mv') vars that arise in the translation of @(tsee mv-let)
     (see @(tsee fty-check-mv-let-call)).
     These @('mv') variables are treated specially
     by the type annotation process,
     without a need to add them to @('var-types').")
   (xdoc::p
    "The @('required-types?') input specifies
     the type(s) required for the term, if any.
     This is @('nil') if there are no requirements;
     it is a singleton list if the term is single-valued;
     it is a list of two or more types if the term is multi-valued.
     At the top level (see @(tsee atj-type-annotate-formals+body)),
     @('required-types?') consists of the output type(s) of the function
     (singleton if single-valued, of length two or more if multi-valued):
     the body of the function must have the output type(s) of the function.
     The recursive function @('atj-type-annotate-args'),
     which operates on the arguments of a function call,
     does not take a list of required types as input.")
   (xdoc::p
    "The result of annotating a term is not only the annotated term,
     but also the type(s) of the wrapped term.
     This is always the same as the required types
     when there are required types;
     when there are no required types,
     the resulting type(s) is/are the one(s) inferred for the term.")
   (xdoc::p
    "The type inferred for a variable is the one assigned by @('var-types').
     (As already mentioned before,
     the @('mv') variables annotated with two or more types
     are handled specially;
     they are never passed to this function directly.)
     We annotate the variable with its associated type;
     note that the variable names in @('var-types')
     do not have type annotations.
     We wrap the variable with a type conversion function
     from the inferred type(s) to the required type(s) if supplied,
     or to the inferred type(s) (i.e. no-op conversion) if not supplied.")
   (xdoc::p
    "The type inferred for a quoted constant
     is determined by the value of the quoted constant.
     We wrap the quoted constant with a type conversion function
     as discussed above.")
   (xdoc::p
    "The non-strict function @(tsee if) is treated specially,
     because eventually it is translated to a Java @('if'),
     which assigns either the `then' part or the `else' part
     to a Java local variable.
     The type of the Java local variable is
     (the Java counterpart of) @('required-types?') if supplied:
     in this case, when @('required-types?') is recursively passed
     to the second and third argument of the @(tsee if),
     both terms will be wrapped so that they have the required type(s).
     However, if @('required-types?') is @('nil'),
     the recursive annotation of the `then' and `else' subterms
     may produce different types,
     and so in this case we re-wrap those terms
     with the least upper bound of the two types.
     The case of a term of the form @('(if a a b)')
     is treated a little differently,
     but there is no substantial difference.
     In the general case of @('(if a b c)') with @('a') different from @('b'),
     there is never any required type for the test @('a'),
     because in the Java code it is just used
     to generate the test of the @('if');
     ACL2 should ensure that the test of an @(tsee if) is single-valued,
     but we defensively check for that.
     In all cases, the @(tsee if) is wrapped with
     the identify conversion function for the overall type(s),
     for uniformity and to readily indicate the type
     of the Java local variable to generate.")
   (xdoc::p
    "For a lambda expression
     (other than the kind resulting from an @(tsee mv-let),
     whose treatment is described below),
     the argument terms are annotated without required types.
     The inferred types are then assigned to the formal parameters
     when the body of the lambda expression is annotated.
     We annotate all the formal parameters of the lambda expression;
     but note that the new @('var-types') has non-annotated variable names.
     Note that the list of types returned by @(tsee atj-type-annotate-args)
     has a different meaning from
     the one returned by @(tsee atj-type-annotate-term):
     while the latter is a single or multiple type for a single term,
     the latter consists of a single type for each argument
     (more on this below).")
   (xdoc::p
    "For a named function call
     other than @(tsee mv)
     (whose treatment is described below)
     and other than the array creation functions
     in @(tsee *atj-jprimarr-new-init-fns*)
     (whose treatment is also described below),
     the function's types are obtained.
     We first try annotating the argument terms without required types
     (as done for a lambda expression as explained above),
     thus inferring types for the arguments.
     Then we look for the function types (of the named function)
     whose input types are wider than or the same as
     the inferred argument types.
     If there are some, we select the one whose input types are the least
     (this always exists because of the closure property
     checked by @(tsee atj-other-function-type);
     see the documentation of that macro and supporting functions for details);
     we then use the output type(s) of the selected function type
     as the type(s) inferred for the function call,
     and wrap it to adapt to the required type(s) for the function call if any.
     The successful selection of such a function type means that,
     in the generated Java code, an overloaded method will be called
     based on the argument types inferred by the Java compiler.
     If there are no function types satisfying the above condition,
     we look at the primary function type (which always exists),
     and its input types become the required ones for the argument terms,
     while the output type(s) are used to infer the type(s) for the call,
     which is then wrapped as needed to match the required type(s) if any.")
   (xdoc::p
    "If we encounter a call of @(tsee mv),
     which may be introduced by a previous pre-translation step,
     we allow its arguments to have any types
     and we regard the call as having the multiple type obtained
     by putting the argument types into a list.
     We also collect the required (if present) or inferred (otherwise) types
     in a list without duplications that is threaded through these functions.
     This list does not affect the type annotations,
     but is used by the code generation functions
     in order to determine which @(tsee mv) classes must be generated.")
   (xdoc::p
    "If we encounter a call of
     an array creation function in @(tsee *atj-jprimarr-new-init-fns*),
     and if @(':guards') is @('t'),
     we ensure that its (only) argument is a translated @(tsee list) call,
     i.e. a (possibly empty) nest of @(tsee cons)es
     ending with a quoted @('nil').
     If it is not, we stop with an error,
     which is really a (deep) input validation error.
     If it is a @(tsee list) call, we extract its element terms.
     We type-annotate them, and we ensure that their result types
     are consistent with the array's component type.
     If they are not, it is a (deep) input validation error.
     If everything checks, then we make the annotated arguments
     directly arguments of the array creation function,
     which therefore is now treated
     as a function with a variable number of arguments.")
   (xdoc::p
    "Before attempting to process lambda expression or named function calls
     as described above,
     we first check whether the term is a translated @(tsee mv-let).
     For this to be the case,
     not only @(tsee fty-check-mv-let-call) must succeed,
     yielding variables @('var1'), ..., @('varn')
     and subterms @('mv-term') and @('body-term'),
     but also the term assigned to the @('mv') variable
     must have multiple types.
     If the term is not a translated @(tsee mv-let),
     the term is processed as any other term.
     If the term is a translated @(tsee mv-let),
     we annotate it by building a term of the form")
   (xdoc::codeblock
    "([reqinf>reqinf]"
    " ((lambda ([types]mv)"
    "          ([reqinf>reqinf]"
    "           ((lambda ([type1]var1 ... [typen]varn)"
    "                    ([...>reqinf] body-term))"
    "            ([AV>type1] (mv-nth ([AI>AI] '0)"
    "                                ([types>types] [types]mv)))"
    "            ..."
    "            ([AV>typen] (mv-nth ([AI>AI] 'n-1)"
    "                                ([types>types] [types]mv))))))"
    "  ([types>types] mv-term)))")
   (xdoc::p
    "where @('types') consists of @('type1'), ..., @('typen'),
     and where @('reqinf') is @('required-types?') if non-@('nil')
     or otherwise the types inferred for @('body-term').
     This term is systematically annotated in the same way as any other term,
     so that subsequent pre-processing steps can treat all terms uniformly.
     The @('[AV>typei]') conversions
     are consistent with the function type of @(tsee mv-nth),
     so that, as we are adding more direct support for @(tsee mv) in ATJ,
     the code generation functions can still treat these newly annotated terms
     as before, i.e. treating multiple values as lists.")
   (xdoc::p
    "The function @('atj-type-annotate-mv-let') first checks whether the term
     has the structure of a translated @(tsee mv-let).
     Then it annotates the term to which the @('mv') variable is bound,
     inferring a non-empty list of types (i.e. @('types') above) for it:
     if the list is a singleton,
     the term is actually not a translated @(tsee mv-let),
     and the function returns a failure,
     letting @('atj-type-annotate-term') handle the term.
     Otherwise, after checking that the number of types
     is consistent with the number of variables
     (this is never expected to fail),
     we annotate the body term:
     we pass the top-level required types (if any),
     and we update @('var-types') with the @(tsee mv-let) variables
     associated to the types for the term to which @('mv') is bound;
     we do not need to update @('var-types') with @('mv')
     because @(tsee fty-check-mv-let-call) ensures that
     the variable @('mv') does not occur free in the body term.
     Note that, in general, some variables bound to @(tsee mv-nth) calls
     may have been removed by a previous pre-translation step,
     the one that removes unused variables (see @(tsee fty-check-mv-let-call));
     thus, in order to extend @('var-types'),
     we select the types for which there are actually variables.")
   (xdoc::p
    "In @('atj-type-annotate-args'), we check that
     the types inferred for each single argument are a singleton.
     Except for the argument of @('((lambda (mv) ...) mv-term)')
     in a translated @(tsee mv-let),
     in ACL2 all the arguments of function calls must be single-valued.
     We do not expect this check to ever fail.")
   (xdoc::p
    "Note that an annotated term is still a regular term,
     but it has a certain structure."))

  (define atj-type-annotate-term ((term pseudo-termp)
                                  (required-types? atj-type-listp)
                                  (var-types atj-symbol-type-alistp)
                                  (mv-typess atj-type-list-listp)
                                  (guards$ booleanp)
                                  (wrld plist-worldp))
    :guard (cons-listp mv-typess)
    :returns (mv (annotated-term pseudo-termp)
                 (resulting-types (and (atj-type-listp resulting-types)
                                       (consp resulting-types)))
                 (new-mv-typess (and (atj-type-list-listp new-mv-typess)
                                     (cons-listp new-mv-typess))))
    (b* (((unless (mbt (atj-type-listp required-types?)))
          (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
         ((unless (mbt (atj-symbol-type-alistp var-types)))
          (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
         ((unless (mbt (and (atj-type-list-listp mv-typess)
                            (cons-listp mv-typess))))
          (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
         ((when (pseudo-term-case term :null))
          (raise "Internal error: null term.")
          (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
         ((when (pseudo-term-case term :var))
          (b* ((var (pseudo-term-var->name term))
               (var+type (assoc-eq var var-types))
               ((unless (consp var+type))
                (prog2$
                 (raise "Internal error: the variable ~x0 has no type." term)
                 (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil)))
               (type (cdr var+type))
               (types (list type))
               (var (atj-type-annotate-var var types))
               ((unless (<= (len required-types?) 1))
                (raise "Internal error: ~
                        requiring multiple types ~x0 ~
                        for a single-type variable ~x1."
                       required-types? var)
                (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil)))
            (mv (atj-type-wrap-term (pseudo-term-var var)
                                    types
                                    required-types?)
                (or required-types? types)
                mv-typess)))
         ((when (pseudo-term-case term :quote))
          (b* ((value (pseudo-term-quote->val term))
               (type (atj-type-of-value value))
               (types (list type))
               ((unless (<= (len required-types?) 1))
                (raise "Internal error: ~
                        requiring multiple types ~x0 ~
                        for a quoted constant ~x1."
                       required-types? term)
                (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil)))
            (mv (atj-type-wrap-term term types required-types?)
                (or required-types? types)
                mv-typess)))
         ((mv successp annotated-term resulting-types mv-typess)
          (atj-type-annotate-mv-let term
                                    required-types?
                                    var-types
                                    mv-typess
                                    guards$
                                    wrld))
         ((when successp) (mv annotated-term resulting-types mv-typess))
         (fn (pseudo-term-call->fn term))
         (args (pseudo-term-call->args term))
         ((when (and (eq fn 'if)
                     (int= (len args) 3))) ; should be always true
          (b* ((test (first args))
               (then (second args))
               (else (third args)))
            (if (equal test then) ; it's an OR
                (b* ((first test)
                     (second else)
                     ((unless (<= (len required-types?) 1))
                      (raise "Internal error: ~
                              requiring multiple types ~x0 ~
                              for the term ~x1."
                             required-types? term)
                      (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
                     ((mv first first-types mv-typess)
                      (atj-type-annotate-term first
                                              required-types?
                                              var-types
                                              mv-typess
                                              guards$
                                              wrld))
                     ((unless (= (len first-types) 1))
                      (raise "Internal error: ~
                              the first disjunct ~x0 of the term ~x1 ~
                              returns multiple values."
                             first term)
                      (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
                     ((mv second second-types mv-typess)
                      (atj-type-annotate-term second
                                              required-types?
                                              var-types
                                              mv-typess
                                              guards$
                                              wrld))
                     ((unless (= (len second-types) 1))
                      (raise "Internal error: ~
                              the second disjunct ~x0 of the term ~x1 ~
                              returns multiple values."
                             second term)
                      (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
                     (types (or required-types?
                                (atj-type-list-join first-types second-types)))
                     ((unless (atj-type-listp types))
                      (raise "Type annotation failure: ~
                              cannot merge types ~x0 with types ~x1."
                             first-types second-types)
                      (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
                     (first (if required-types?
                                first
                              (atj-type-rewrap-term first types)))
                     (second (if required-types?
                                 second
                               (atj-type-rewrap-term second types)))
                     (term (pseudo-term-call 'if (list first first second))))
                  (mv (atj-type-wrap-term term types types)
                      types
                      mv-typess))
              (b* (((mv test test-types mv-typess)
                    (atj-type-annotate-term test
                                            nil
                                            var-types
                                            mv-typess
                                            guards$
                                            wrld))
                   ((unless (= (len test-types) 1))
                    (raise "Internal error: ~
                            the test ~x0 of the term ~x1 ~
                            returns multiple values."
                           test term)
                    (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
                   ((mv then then-types mv-typess)
                    (atj-type-annotate-term then
                                            required-types?
                                            var-types
                                            mv-typess
                                            guards$
                                            wrld))
                   ((mv else else-types mv-typess)
                    (atj-type-annotate-term else
                                            required-types?
                                            var-types
                                            mv-typess
                                            guards$
                                            wrld))
                   ((unless (= (len then-types) (len else-types)))
                    (raise "Internal error: ~
                            the branches ~x0 and ~x1 of the term ~x2 ~
                            have different numbers of types, ~
                            namely ~x3 and ~x4."
                           then else term then-types else-types)
                    (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
                   ((unless (or (null required-types?)
                                (= (len required-types?) (len then-types))))
                    (raise "Internal error: ~
                            requiring the types ~x0 for the term ~x1, ~
                            which has a different number of types ~x2."
                           required-types? term (len then-types))
                    (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
                   (types (or required-types?
                              (atj-type-list-join then-types else-types)))
                   ((unless (atj-type-listp types))
                    (raise "Type annotation failure: ~
                            cannot merge types ~x0 with types ~x1."
                           then-types else-types)
                    (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
                   (then (if required-types?
                             then
                           (atj-type-rewrap-term then types)))
                   (else (if required-types?
                             else
                           (atj-type-rewrap-term else types)))
                   (term (pseudo-term-call 'if (list test then else))))
                (mv (atj-type-wrap-term term types types)
                    types
                    mv-typess)))))
         ((when (and guards$
                     (atj-jprimarr-new-init-fn-p fn)))
          (b* (((unless (= (len args) 1))
                (raise "Internal error: ~
                        the function ~x0 has arguments ~x1."
                       fn args)
                (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
               (arg (car args))
               ((mv list-call? args) (check-list-call arg))
               ((unless list-call?)
                (raise "Type annotation failure: ~
                        the argument ~x0 of ~x1 is not ~
                        a translated LIST call."
                       arg fn)
                (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
               ((unless (< (pseudo-term-list-count args)
                           (pseudo-term-count term)))
                (raise "Internal error: ~
                        the size of the subterms ~x0 of ~x1 ~
                        does not decrease."
                       args term)
                (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
               ((mv args types mv-typess) (atj-type-annotate-args args
                                                                  var-types
                                                                  mv-typess
                                                                  guards$
                                                                  wrld))
               (ptype (atj-jprimarr-new-init-fn-to-ptype fn))
               ((unless (equal types
                               (repeat (len args) (atj-type-jprim ptype))))
                (raise "Type annotation failure: ~
                        the types ~x0 of the arguments ~x1 of ~x2 ~
                        do not all match the array type."
                       types args fn)
                (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
               (term (pseudo-term-call fn args))
               (types (list (atj-type-jprimarr ptype))))
            (mv (atj-type-wrap-term term types required-types?)
                (or required-types? types)
                mv-typess)))
         ((mv args types mv-typess) (atj-type-annotate-args args
                                                            var-types
                                                            mv-typess
                                                            guards$
                                                            wrld))
         ((when (eq fn 'mv))
          (b* (((unless (>= (len types) 2))
                (raise "Internal error: ~
                        found MV applied to arguments ~x0."
                       args)
                (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
               ((unless (or (null required-types?)
                            (= (len types) (len required-types?))))
                (raise "Internal error: ~
                        requiring the types ~x0 for the term ~x1."
                       required-types? term)
                (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
               (resulting-types (or required-types? types)))
            (mv (atj-type-wrap-term (pseudo-term-call 'mv args)
                                    types
                                    required-types?)
                resulting-types
                (add-to-set-equal resulting-types mv-typess))))
         ((when (pseudo-term-case term :fncall))
          (b* ((fn-info (atj-get-function-type-info fn guards$ wrld))
               (main-fn-type (atj-function-type-info->main fn-info))
               (other-fn-types (atj-function-type-info->others fn-info))
               (all-fn-types (cons main-fn-type other-fn-types))
               (fn-type? (atj-function-type-of-min-input-types types
                                                               all-fn-types)))
            (if fn-type?
                (b* ((in-types (atj-function-type->inputs fn-type?))
                     (out-types (atj-function-type->outputs fn-type?))
                     ((unless (= (len in-types) (len args)))
                      (raise "Internal error: ~
                              the function ~x0 has ~x1 arguments ~
                              but a different number of input types ~x2."
                             fn (len args) (len in-types))
                      (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
                     ((unless (= (len in-types) (len types)))
                      (raise "Internal error: ~
                              the input types ~x0 of the function ~x1 ~
                              differ in number from the argument types ~x2."
                             in-types fn types)
                      (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
                     (args (atj-type-rewrap-terms
                            args (atj-type-list-to-type-list-list in-types)))
                     ((unless (consp out-types))
                      (raise "Internal error: ~
                              no output types in function type ~x0."
                             fn-type?)
                      (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
                     ((unless (or (null required-types?)
                                  (= (len required-types?) (len out-types))))
                      (raise "Internal error: ~
                              requiring the types ~x0 for the term ~x1, ~
                              which has a different number of types ~x2."
                             required-types? term out-types)
                      (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil)))
                  (mv (atj-type-wrap-term (pseudo-term-call fn args)
                                          out-types
                                          required-types?)
                      (or required-types? out-types)
                      mv-typess))
              (b* ((in-types (atj-function-type->inputs main-fn-type))
                   (out-types (atj-function-type->outputs main-fn-type))
                   ((unless (= (len in-types) (len args)))
                    (raise "Internal error: ~
                            the function ~x0 has ~x1 arguments ~
                            but a different number of input types ~x2."
                           fn (len args) (len in-types))
                    (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
                   ((unless (= (len in-types) (len types)))
                    (raise "Internal error: ~
                            the input types ~x0 of the function ~x1 ~
                            differ in number from the argument types ~x2."
                           in-types fn types)
                    (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil))
                   (args (atj-type-rewrap-terms
                          args (atj-type-list-to-type-list-list in-types)))
                   ((unless (consp out-types))
                    (raise "Internal error: ~
                            the function ~x0 has an empty list of output types."
                           fn)
                    (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil)))
                (mv (atj-type-wrap-term (pseudo-term-call fn args)
                                        out-types
                                        required-types?)
                    (or required-types? out-types)
                    mv-typess)))))
         (formals (pseudo-lambda->formals fn))
         (var-types (append (pairlis$ formals types) var-types))
         (formals (atj-type-annotate-vars formals types))
         ((mv body types mv-typess)
          (atj-type-annotate-term (pseudo-lambda->body fn)
                                  required-types?
                                  var-types
                                  mv-typess
                                  guards$
                                  wrld))
         (term (pseudo-term-call (pseudo-lambda formals body) args))
         ((unless (or (null required-types?)
                      (= (len required-types?) (len types))))
          (raise "Internal error: ~
                  requiring the types ~x0 for the term ~x1, ~
                  whose inferred types are ~x2."
                 required-types? term types)
          (mv (pseudo-term-null) (list (atj-type-irrelevant)) nil)))
      (mv (atj-type-wrap-term term
                              types
                              required-types?)
          (or required-types? types)
          mv-typess))
    ;; 2nd component is non-0
    ;; so that the call of ATJ-TYPE-ANNOTATE-MV-LET decreases:
    :measure (two-nats-measure (pseudo-term-count term) 1))

  (define atj-type-annotate-mv-let ((term pseudo-termp)
                                    (required-types? atj-type-listp)
                                    (var-types atj-symbol-type-alistp)
                                    (mv-typess atj-type-list-listp)
                                    (guards$ booleanp)
                                    (wrld plist-worldp))
    :guard (cons-listp mv-typess)
    :returns (mv (success booleanp)
                 (annotated-term pseudo-termp)
                 (resulting-types (and (atj-type-listp resulting-types)
                                       (consp resulting-types)))
                 (new-mv-typess (and (atj-type-list-listp new-mv-typess)
                                     (cons-listp new-mv-typess))))
    (b* (((unless (mbt (atj-type-listp required-types?)))
          (mv nil nil (list (atj-type-irrelevant)) nil))
         ((unless (mbt (atj-symbol-type-alistp var-types)))
          (mv nil nil (list (atj-type-irrelevant)) nil))
         ((unless (mbt (and (atj-type-list-listp mv-typess)
                            (cons-listp mv-typess))))
          (mv nil nil (list (atj-type-irrelevant)) nil))
         ((mv mv-let-p mv-var vars indices & mv-term body-term)
          (fty-check-mv-let-call term))
         ((unless mv-let-p)
          (mv nil nil (list (atj-type-irrelevant)) mv-typess))
         ((mv annotated-mv-term mv-term-types mv-typess)
          (atj-type-annotate-term mv-term nil var-types mv-typess guards$ wrld))
         ((when (= (len mv-term-types) 1))
          (mv nil nil (list (atj-type-irrelevant)) mv-typess))
         (annotated-mv (atj-type-annotate-var mv-var mv-term-types))
         (sel-types (atj-select-mv-term-types indices mv-term-types))
         (annotated-vars (atj-type-annotate-vars vars sel-types))
         (var-types (append (pairlis$ vars sel-types) var-types))
         ((mv annotated-body-term body-term-types mv-typess)
          (atj-type-annotate-term body-term
                                  required-types?
                                  var-types
                                  mv-typess
                                  guards$
                                  wrld))
         ((unless (or (null required-types?)
                      (= (len required-types?) (len body-term-types))))
          (raise "Internal error: ~
                  requiring the types ~x0 for the term ~x1, ~
                  whose inferred types are ~x2."
                 required-types? term body-term-types)
          (mv nil nil (list (atj-type-irrelevant)) nil))
         (wrapped-mv (atj-type-wrap-term annotated-mv mv-term-types nil))
         (annotated-mv-nth-calls (atj-type-annotate-mv-nth-terms sel-types
                                                                 indices
                                                                 wrapped-mv))
         (inner-lambda (pseudo-lambda annotated-vars annotated-body-term))
         (inner-lambda-app (pseudo-term-call inner-lambda
                                             annotated-mv-nth-calls))
         (annotated-inner-lambda-app (atj-type-wrap-term inner-lambda-app
                                                         body-term-types
                                                         body-term-types))
         (outer-lambda (pseudo-lambda (list annotated-mv)
                                      annotated-inner-lambda-app))
         (outer-lambda-app (pseudo-term-call outer-lambda
                                             (list annotated-mv-term)))
         (final-term (atj-type-wrap-term outer-lambda-app
                                         body-term-types
                                         body-term-types)))
      (mv t
          final-term
          (or required-types? body-term-types)
          mv-typess))
    :measure (two-nats-measure (pseudo-term-count term) 0))

  (define atj-type-annotate-args ((args pseudo-term-listp)
                                  (var-types atj-symbol-type-alistp)
                                  (mv-typess atj-type-list-listp)
                                  (guards$ booleanp)
                                  (wrld plist-worldp))
    :guard (cons-listp mv-typess)
    :returns (mv (annotated-args (and (pseudo-term-listp annotated-args)
                                      (equal (len annotated-args)
                                             (len args))))
                 (resulting-types (and (atj-type-listp resulting-types)
                                       (equal (len resulting-types)
                                              (len args))))
                 (new-mv-typess (and (atj-type-list-listp new-mv-typess)
                                     (cons-listp new-mv-typess))))
    (b* (((unless (mbt (atj-symbol-type-alistp var-types)))
          (mv (repeat (len args) (pseudo-term-null))
              (repeat (len args) (atj-type-irrelevant))
              nil))
         ((unless (mbt (and (atj-type-list-listp mv-typess)
                            (cons-listp mv-typess))))
          (mv (repeat (len args) (pseudo-term-null))
              (repeat (len args) (atj-type-irrelevant))
              nil))
         ((when (endp args)) (mv nil nil mv-typess))
         ((mv arg types mv-typess) (atj-type-annotate-term (car args)
                                                           nil ; REQUIRED-TYPES?
                                                           var-types
                                                           mv-typess
                                                           guards$
                                                           wrld))
         ((unless (= (len types) 1))
          (raise "Internal error: ~
                  the function argument ~x0 has types ~x1."
                 (car args) types)
          (mv (repeat (len args) (pseudo-term-null))
              (repeat (len args) (atj-type-irrelevant))
              nil))
         (type (car types))
         ((mv args types mv-typess) (atj-type-annotate-args (cdr args)
                                                            var-types
                                                            mv-typess
                                                            guards$
                                                            wrld)))
      (mv (cons arg args) (cons type types) mv-typess))
    :measure (two-nats-measure (pseudo-term-list-count args) 0))

  :prepwork

  ((define atj-type-annotate-mv-nth-terms ((types atj-type-listp)
                                           (indices nat-listp)
                                           (wrapped-mv pseudo-termp))
     :guard (= (len types) (len indices))
     :returns (terms pseudo-term-listp)
     (b* (((when (endp types)) nil)
          (wrapped-index (atj-type-wrap-term (pseudo-term-quote
                                              (car indices))
                                             (list (atj-type-acl2
                                                    (atj-atype-integer)))
                                             (list (atj-type-acl2
                                                    (atj-atype-integer)))))
          (mv-nth-call (pseudo-term-call 'mv-nth
                                         (list wrapped-index wrapped-mv)))
          (wrapped-mv-nth-call (atj-type-wrap-term mv-nth-call
                                                   (list (atj-type-acl2
                                                          (atj-atype-value)))
                                                   (list (car types))))
          (rest (atj-type-annotate-mv-nth-terms (cdr types)
                                                (cdr indices)
                                                wrapped-mv)))
       (cons wrapped-mv-nth-call rest))
     ///
     (defret len-of-atj-type-annotate-mv-nth-terms
       (equal (len terms)
              (len types))))

   (define atj-select-mv-term-types ((indices nat-listp)
                                     (mv-types atj-type-listp))
     :returns (selected-mv-types atj-type-listp)
     (b* (((unless (mbt (nat-listp indices)))
           (repeat (len indices) (atj-type-irrelevant)))
          ((unless (mbt (atj-type-listp mv-types)))
           (repeat (len indices) (atj-type-irrelevant)))
          ((when (endp indices)) nil)
          (index (car indices))
          ((unless (< index (len mv-types)))
           (raise "Internal error: ~
                   index ~x0 has no corresponding type in ~x1."
                  index mv-types)
           (repeat (len indices) (atj-type-irrelevant)))
          (type (nth index mv-types))
          (rest-types (atj-select-mv-term-types (cdr indices) mv-types)))
       (cons type rest-types))
     ///
     (defret len-of-atj-select-mv-term-types
       (equal (len selected-mv-types)
              (len indices))))

   (local (include-book "std/lists/top" :dir :system))

   (local (in-theory (disable pseudo-termp
                              acl2::consp-under-iff-when-true-listp))))

  :verify-guards nil ; done below

  ///

  (defrulel verify-guards-lemma-1
    (implies (>= (len x) 1)
             (consp x)))

  (defrulel verify-guards-lemma-2
    (implies (atj-type-listp x)
             (true-listp x)))

  (defrulel verify-guards-lemma-3
    (implies (symbolp x)
             (pseudo-termp x))
    :enable pseudo-termp)

  (verify-guards atj-type-annotate-term
    :hints (("Goal"
             :in-theory (enable pseudo-fn-args-p
                                pseudo-var-p
                                atj-jprimarr-new-init-fn-p
                                len-of-fty-check-mv-let-call.indices/vars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-annotate-formals+body ((formals symbol-listp)
                                        (body pseudo-termp)
                                        (in-types atj-type-listp)
                                        (out-types atj-type-listp)
                                        (mv-typess atj-type-list-listp)
                                        (guards$ booleanp)
                                        (wrld plist-worldp))
  :guard (and (int= (len formals) (len in-types))
              (consp out-types)
              (cons-listp mv-typess))
  :returns (mv (annotated-formals symbol-listp)
               (annotated-body pseudo-termp)
               (new-mv-typess (and (atj-type-list-listp new-mv-typess)
                                   (cons-listp new-mv-typess))))
  :short "Add ATJ type annotations to the formal parameters and body
          of an ACL2 function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input and output types of the function are supplied as arguments.
     We annotate the body, using the output types as the required types.
     We initialize the variable-type alist
     to assign the input types to the formal parameters.
     We also annotate the formal parameters,
     but note that @('var-types') has non-annotated variable names.")
   (xdoc::p
    "We collect all the @(tsee mv) types in the body
     for which we will need to generate @(tsee mv) classes."))
  (b* ((var-types (pairlis$ formals in-types))
       (formals (atj-type-annotate-vars formals in-types))
       ((mv body & mv-typess)
        (atj-type-annotate-term
         body out-types var-types mv-typess guards$ wrld)))
    (mv formals body mv-typess))
  ///

  (defret len-of-atj-type-annotate-formals+body.new-formals
    (equal (len annotated-formals)
           (len formals))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-check-annotated-mv-let-call ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (mv-var symbolp)
               (mv-term pseudo-termp)
               (vars symbol-listp)
               (indices nat-listp)
               (body-term pseudo-termp))
  :short "Recognize and decompose type-annotated @(tsee mv-let)s."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type annotation pre-translation step recognizes @(tsee mv-let)s
     and transforms them as explained in @(tsee atj-type-annotate-term).
     So the resulting term should have the form")
   (xdoc::codeblock
    "([reqinf>reqinf]"
    " ((lambda ([types]mv)"
    "          ([reqinf>reqinf]"
    "           ((lambda ([type1]var1 ... [typen]varn)"
    "                    ([...>reqinf] body-term))"
    "            ([AV>type1] (mv-nth ([AI>AI] '0)"
    "                                ([types>types] [types]mv)))"
    "            ..."
    "            ([AV>typen] (mv-nth ([AI>AI] 'n-1)"
    "                                ([types>types] [types]mv))))))"
    "  ([types>types] mv-term)))")
   (xdoc::p
    "where @('mv') may not be the symbol `@('mv')' but some other symbol.
     Because of the pre-translation step that removes unused variables,
     the formals and arguments of the inner lambda
     may be fewer than the elements of @('types');
     i.e. some @(tsee mv-nth) indices may be skipped.")
   (xdoc::p
    "This code recognizes terms of the form above,
     returning some of the constituents if successful.
     The @('mv-var') result is @('[types]mv'),
     i.e. the annotated multi-value variable.
     The @('mv-term') result is @('([types>types] mv-term)'),
     i.e. the wrapped multi-value term.
     The @('vars') result is @('([type1]var1 ... [typen]varn)')
     (possibly skipping some indices),
     i.e. the list of formals of the inner lambda expression,
     all annotated.
     The @('indices') result is the ordered list of @(tsee mv-nth) indices
     actually present; these are 0-based.
     The @('body-term') result is @('([...>reqinf] body-term)'),
     i.e. the wrapped body of the inner lambda expression.."))
  (b* (((mv outer-lambda-call reqinf reqinf2) (atj-type-unwrap-term term))
       ((unless (equal reqinf reqinf2)) (mv nil nil nil nil nil nil))
       ((mv okp mv-var wrapped-inner-lambda-call mv-term)
        (check-unary-lambda-call outer-lambda-call))
       ((unless okp) (mv nil nil nil nil nil nil))
       ((mv & types) (atj-type-unannotate-var mv-var))
       ((unless (> (len types) 1)) (mv nil nil nil nil nil nil))
       ((mv & src-types dst-types) (atj-type-unwrap-term mv-term))
       ((unless (and (equal src-types types)
                     (equal dst-types types)))
        (raise "Internal error: malformed term ~x0." term)
        (mv nil nil nil nil nil nil))
       ((mv inner-lambda-call src-types dst-types)
        (atj-type-unwrap-term wrapped-inner-lambda-call))
       ((unless (and (equal src-types reqinf)
                     (equal dst-types reqinf))) (mv nil nil nil nil nil nil))
       ((mv okp vars body-term args) (check-lambda-call inner-lambda-call))
       ((unless okp)
        (raise "Internal error: malformed term ~x0." term)
        (mv nil nil nil nil nil nil))
       ((mv & & dst-types) (atj-type-unwrap-term body-term))
       ((unless (equal dst-types reqinf))
        (raise "Internal error: malformed term ~x0." term)
        (mv nil nil nil nil nil nil))
       (indices (atj-check-annotated-mv-let-call-aux
                 args vars types mv-var)))
    (mv t mv-var mv-term vars indices body-term))
  :guard-hints (("Goal"
                 :in-theory
                 (enable acl2::len-of-check-lambda-calls.formals-is-args)))

  :prepwork

  ((define atj-check-annotated-mv-let-call-aux ((args pseudo-term-listp)
                                                (vars symbol-listp)
                                                (types atj-type-listp)
                                                (mv-var symbolp))
     :guard (and (= (len vars) (len args))
                 (consp types))
     :returns (indices nat-listp)
     :parents nil
     (b* (((when (endp args)) nil)
          ((mv arg arg-src arg-dst) (atj-type-unwrap-term (car args)))
          ((unless (and (not (variablep arg))
                        (not (fquotep arg))
                        (eq (ffn-symb arg) 'mv-nth)
                        (= (len (fargs arg)) 2)
                        (equal (fargn arg 2)
                               (atj-type-wrap-term mv-var types types))))
           (raise "Internal error: malformed term ~x0." (car args))
           (repeat (len args) 0))
          ((mv index index-src index-dst) (atj-type-unwrap-term (fargn arg 1)))
          ((unless (and (quotep index)
                        (equal index-src (list (atj-type-acl2
                                                (atj-atype-integer))))
                        (equal index-dst (list (atj-type-acl2
                                                (atj-atype-integer))))))
           (raise "Internal error: malformed term ~x0." (car args))
           (repeat (len args) 0))
          (index (unquote-term index))
          ((unless (integer-range-p 0 (len types) index))
           (raise "Internal error: malformed term ~x0." (car args))
           (repeat (len args) 0))
          ((unless (and (equal arg-src (list (atj-type-acl2 (atj-atype-value))))
                        (equal arg-dst (list (nth index types)))))
           (raise "Internal error: malformed term ~x0." (car args))
           (repeat (len args) 0))
          (var (car vars))
          ((mv & var-types) (atj-type-unannotate-var var))
          ((unless (equal var-types (list (nth index types))))
           (raise "Internal error: malformed term ~x0." (car args))
           (repeat (len args) 0)))
       (cons index (atj-check-annotated-mv-let-call-aux (cdr args)
                                                        (cdr vars)
                                                        types
                                                        mv-var)))

     :prepwork

     ((local (include-book "std/typed-lists/nat-listp" :dir :system))

      (defrulel verify-guards-lemma
        (implies (and (pseudo-termp term)
                      (not (variablep term))
                      (not (fquotep term)))
                 (pseudo-termp (fargn term 1)))
        :expand ((pseudo-termp term))))

     ///

     (defret len-of-atj-check-annotated-mv-let-call-aux
       (equal (len indices) (len args)))))

  ///

  (defret len-of-atj-check-annotated-mv-let.vars/indices
    (equal (len indices)
           (len vars))
    :hints (("Goal"
             :in-theory
             (enable acl2::len-of-check-lambda-calls.formals-is-args))))

  (in-theory (disable len-of-atj-check-annotated-mv-let.vars/indices))

  (defret atj-check-annotated-mv-let-mv-term-smaller
    (implies yes/no
             (< (acl2-count mv-term)
                (acl2-count term)))
    :rule-classes :linear
    :hints (("Goal"
             :use (acl2-count-of-atj-type-unwrap-term-linear
                   (:instance acl2::acl2-count-of-check-unary-lambda-call.arg
                    (term (mv-nth 0 (atj-type-unwrap-term term)))))
             :in-theory (disable
                         acl2-count-of-atj-type-unwrap-term-linear
                         acl2::acl2-count-of-check-unary-lambda-call.arg))))

  (defret atj-check-annotated-mv-let-body-term-smaller
    (implies yes/no
             (< (acl2-count body-term)
                (acl2-count term)))
    :rule-classes :linear
    :hints (("Goal"
             :use (acl2-count-of-atj-type-unwrap-term-linear
                   (:instance acl2::acl2-count-of-check-unary-lambda-call.arg
                    (term (mv-nth 0 (atj-type-unwrap-term term))))
                   (:instance acl2-count-of-atj-type-unwrap-term-linear
                    (term (mv-nth 2 (check-unary-lambda-call
                                     (mv-nth 0 (atj-type-unwrap-term term))))))
                   (:instance acl2::acl2-count-of-check-lambda-call.body
                    (term
                     (mv-nth 0 (atj-type-unwrap-term
                                (mv-nth 2 (check-unary-lambda-call
                                           (mv-nth 0 (atj-type-unwrap-term
                                                      term)))))))))
             :in-theory (disable
                         acl2-count-of-atj-type-unwrap-term-linear
                         acl2::acl2-count-of-check-unary-lambda-call.arg
                         acl2::acl2-count-of-check-lambda-call.body)))))
