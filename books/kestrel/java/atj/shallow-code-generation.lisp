; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "common-code-generation")
(include-book "pre-translation")
(include-book "post-translation")
(include-book "primitives")

(include-book "kestrel/std/basic/organize-symbols-by-pkg" :dir :system)
(include-book "kestrel/std/basic/symbol-package-name-lst" :dir :system)
(include-book "kestrel/std/system/formals-plus" :dir :system)
(include-book "kestrel/std/system/tail-recursive-p" :dir :system)
(include-book "kestrel/std/system/ubody" :dir :system)
(include-book "std/typed-alists/cons-pos-alistp" :dir :system)

(local (include-book "kestrel/std/basic/symbol-name-lst" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-shallow-code-generation
  :parents (atj-code-generation)
  :short "Code generation that is specific to the shallow embedding approach."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc atj-shallow-quoted-constants
  :short "Representation of quoted constants in the shallow embedding."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     each quoted constant in the ACL2 code
     is translated to a Java static final field
     that is calculated once at class initialization time
     and then just referenced in the Java code.
     Since ACL2 values are objects,
     this avoids recalculating the object
     (whether it is created or reused, e.g. when interned)
     every time the shallowly embedded quoted constant
     is executed in the Java code.")
   (xdoc::p
    "We extract all the quoted constants
     from the pre-translated bodies of the ACL2 functions,
     and we create a static final field for each.
     For now we only do this for quoted numbers, characters, and strings,
     but we will cover the other quoted values soon.
     The fields for these quoted constants
     are declared in the generated main class;
     they are named in a way that describes their value,
     e.g. see @(tsee atj-gen-shallow-number-field-name).")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defaggregate atj-qconstants
  :short "Recognize a structured collection of quoted constants."
  :long
  (xdoc::topstring
   (xdoc::p
    "As we collect quoted constants for the purposes described "
    (xdoc::seetopic "atj-shallow-quoted-constants" "here")
    ", we store their values (without quotes)
     in a record where they are partitioned into:
     (i) integers;
     (ii) other (i.e. non-integer) rationals;
     (iii) other (i.e. non-rational) numbers;
     (iv) characters;
     (v) strings;
     (vi) symbols;
     (vii) @(tsee cons) pairs.
     The first six are duplicate-free lists of appropriate types.
     The seventh is an alist from the pairs to positive integer indices:
     the first collected pair gets index 1,
     the second one gets index 2,
     and so on;
     we organize this as an alist instead of a list
     so that the indices are explicit
     and so that we can more easily optimize this with a fast alist
     in the future.
     The index for the next @(tsee cons) pair is stored in this record.
     The use of the indices is explained in
     @(tsee atj-gen-shallow-cons-field-name).
     The alist has unique keys, by construction."))
  ((integers (and (integer-listp integers)
                  (no-duplicatesp integers)))
   (rationals (and (rational-listp rationals)
                   (no-duplicatesp rationals)))
   (numbers (and (acl2-number-listp numbers)
                 (no-duplicatesp numbers)))
   (chars (and (character-listp chars)
               (no-duplicatesp chars)))
   (strings (and (string-listp strings)
                 (no-duplicatesp-equal strings)))
   (symbols (and (symbol-listp symbols)
                 (no-duplicatesp-eq symbols)))
   (pairs cons-pos-alistp)
   (next-index posp))
  ///

  (defrule posp-of-atj-qconstants->next-index
    (implies (atj-qconstants-p record)
             (posp (atj-qconstants->next-index record)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-add-qconstant (value (record atj-qconstants-p))
  :returns (new-record atj-qconstants-p :hyp :guard)
  :short "Add (the value of) a quoted constant to a structured collection."
  :long
  (xdoc::topstring
   (xdoc::p
    "We add the value to the appropriate list, unless it is already present.
     The process is slightly more complicated for @(tsee cons) pairs,
     as it involves an alist;
     if the pair is not already in the alist,
     we add it, associated with the next index to use,
     and we increment the next index to use in the record."))
  (b* (((atj-qconstants record) record))
    (cond ((integerp value)
           (change-atj-qconstants
            record
            :integers (add-to-set value record.integers)))
          ((rationalp value)
           (change-atj-qconstants
            record
            :rationals (add-to-set value record.rationals)))
          ((acl2-numberp value)
           (change-atj-qconstants
            record
            :numbers (add-to-set value record.numbers)))
          ((characterp value)
           (change-atj-qconstants
            record
            :chars (add-to-set value record.chars)))
          ((stringp value)
           (change-atj-qconstants
            record
            :strings (add-to-set-equal value record.strings)))
          ((symbolp value)
           (change-atj-qconstants
            record
            :symbols (add-to-set-eq value record.symbols)))
          ((consp value)
           (b* ((value+index? (assoc-equal value record.pairs)))
             (if (consp value+index?)
                 record
               (change-atj-qconstants
                record
                :pairs (acons value record.next-index record.pairs)
                :next-index (1+ record.next-index)))))
          (t (prog2$
              (raise "Internal error: ~x0 is not a recognized value." value)
              record))))
  :guard-hints (("Goal" :in-theory (disable posp)))
  :prepwork
  ((defrulel verify-guards-lemma
     (implies (posp x)
              (posp (1+ x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-add-qconstants-in-term
  :short "Collect all the quoted constants in a term."
  :long
  (xdoc::topstring
   (xdoc::p
    "We return all the values of the quoted constants
     that appear directly quoted in the term.
     That is, for each sub-term of the form @('(quote <value>)'),
     we return @('<value>').
     This excludes value that occur (only) inside other quoted values,
     e.g. @('(quote (<value> . ...))').")
   (xdoc::p
    "The record that stores the collected constants
     is threaded through the recursive functions."))

  (define atj-add-qconstants-in-term ((term pseudo-termp)
                                      (qconsts atj-qconstants-p))
    :returns (new-qconsts atj-qconstants-p :hyp (atj-qconstants-p qconsts))
    (b* (((when (variablep term)) qconsts)
         ((when (fquotep term)) (atj-add-qconstant (unquote-term term) qconsts))
         (fn (ffn-symb term))
         (qconsts (if (flambdap fn)
                      (atj-add-qconstants-in-term (lambda-body fn) qconsts)
                    qconsts)))
      (atj-add-qconstants-in-terms (fargs term) qconsts)))

  (define atj-add-qconstants-in-terms ((terms pseudo-term-listp)
                                       (qconsts atj-qconstants-p))
    :returns (new-qconsts atj-qconstants-p :hyp (atj-qconstants-p qconsts))
    (b* (((when (endp terms)) qconsts)
         (qconsts (atj-add-qconstants-in-term (car terms) qconsts)))
      (atj-add-qconstants-in-terms (cdr terms) qconsts)))

  :verify-guards nil ; done below
  ///
  (verify-guards atj-add-qconstants-in-term))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-integer-id-part ((integer integerp))
  :returns (core stringp)
  :short "Turn an ACL2 integer into a Java identifier part."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is part of the names of the static final fields for quoted numbers.")
   (xdoc::p
    "We turn the integer into its (base 10) digits,
     prepended by @('minus') if negative."))
  (if (>= integer 0)
      (str::natstr integer)
    (str::cat "minus" (str::natstr (- integer)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-rational-id-part ((rational rationalp))
  :returns (core stringp)
  :short "Turn an ACL2 rational into a Java identifier part."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is part of the names of the static final fields for quoted numbers.")
   (xdoc::p
    "If the rational is an integer,
     we use @(tsee atj-gen-shallow-integer-id-part).
     Otherwise, we generate the integer numerator,
     followed by @('_over_') to denote the fraction,
     followed by the integer denominator (always greater than 1)."))
  (if (integerp rational)
      (atj-gen-shallow-integer-id-part rational)
    (str::cat (atj-gen-shallow-integer-id-part (numerator rational))
              "_over_"
              (atj-gen-shallow-integer-id-part (denominator rational)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-number-id-part ((number acl2-numberp))
  :returns (core stringp)
  :short "Turn an ACL2 number into a Java identifier part."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is part of the names of the static final fields for quoted numbers.")
   (xdoc::p
    "If the number is a rational,
     we use @(tsee atj-gen-shallow-rational-id-part).
     Otherwise, we generate the rational real part,
     followed by @('_plus_i_') to denote the formal complex sum,
     followed by the rational imaginary part (never 0)."))
  (if (rationalp number)
      (atj-gen-shallow-rational-id-part number)
    (str::cat (atj-gen-shallow-rational-id-part (realpart number))
              "_plus_i_"
              (atj-gen-shallow-rational-id-part (imagpart number)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-number-field-name ((number acl2-numberp))
  :returns (name stringp)
  :short "Generate the name of the Java field for an ACL2 quoted number."
  :long
  (xdoc::topstring-p
   "We prepend @('$N_') (for `number')
    to the representation of the number.")
  (str::cat "$N_" (atj-gen-shallow-number-id-part number)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-number-field ((number acl2-numberp))
  :returns (field jfieldp)
  :short "Generate a Java field for an ACL2 quoted number."
  :long
  (xdoc::topstring-p
   "This is a private static final field with an initializer,
    which constructs the number value.
    The type and the initializer are the most specific applicable.")
  (b* ((name (atj-gen-shallow-number-field-name number))
       (init (cond ((integerp number) (atj-gen-integer number))
                   ((rationalp number) (atj-gen-rational number))
                   (t (atj-gen-number number))))
       (type (cond ((integerp number) *aij-type-int*)
                   ((rationalp number) *aij-type-rational*)
                   (t *aij-type-number*))))
    (make-jfield :access (jaccess-private)
                 :static? t
                 :final? t
                 :transient? nil
                 :volatile? nil
                 :type type
                 :name name
                 :init init)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-number-fields ((numbers acl2-number-listp))
  :returns (fields jfield-listp)
  :short "Lift @(tsee atj-gen-shallow-number-field) to lists."
  (cond ((endp numbers) nil)
        (t (cons (atj-gen-shallow-number-field (car numbers))
                 (atj-gen-shallow-number-fields (cdr numbers))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-char-field-name ((char characterp))
  :returns (name stringp)
  :short "Generate the name of the Java field for an ACL2 quoted character."
  :long
  (xdoc::topstring-p
   "We prepend @('$C_') (for `character')
    to a representation of the character itself.")
  (str::cat "$C_" (implode (atj-char-to-jchars-id char nil nil nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-char-field ((char characterp))
  :returns (field jfieldp)
  :short "Generate a Java field for an ACL2 quoted character."
  :long
  (xdoc::topstring-p
   "This is a private static final field with an initializer,
    which constructs the character value.")
  (b* ((name (atj-gen-shallow-char-field-name char))
       (init (atj-gen-char char))
       (type *aij-type-char*))
    (make-jfield :access (jaccess-private)
                 :static? t
                 :final? t
                 :transient? nil
                 :volatile? nil
                 :type type
                 :name name
                 :init init)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-char-fields ((chars character-listp))
  :returns (fields jfield-listp)
  :short "Lift @(tsee atj-gen-shallow-char-field) to lists."
  (cond ((endp chars) nil)
        (t (cons (atj-gen-shallow-char-field (car chars))
                 (atj-gen-shallow-char-fields (cdr chars))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-string-field-name ((string stringp))
  :returns (name stringp)
  :short "Generate the name of the Java field for an ACL2 quoted string."
  :long
  (xdoc::topstring-p
   "We prepend @('$S_') (for `string')
    to a representation of the string itself.")
  (str::cat "$S_" (implode (atj-chars-to-jchars-id
                            (explode string) nil :space nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-string-field ((string stringp))
  :returns (field jfieldp)
  :short "Generate a Java field for an ACL2 quoted string."
  :long
  (xdoc::topstring-p
   "This is a private static final field with an initializer,
    which constructs the string value.")
  (b* ((name (atj-gen-shallow-string-field-name string))
       (init (atj-gen-string string))
       (type *aij-type-string*))
    (make-jfield :access (jaccess-private)
                 :static? t
                 :final? t
                 :transient? nil
                 :volatile? nil
                 :type type
                 :name name
                 :init init)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-string-fields ((strings string-listp))
  :returns (fields jfield-listp)
  :short "Lift @(tsee atj-gen-shallow-string-field) to lists."
  (cond ((endp strings) nil)
        (t (cons (atj-gen-shallow-string-field (car strings))
                 (atj-gen-shallow-string-fields (cdr strings))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-symbol-field-name ((symbol symbolp))
  :returns (name stringp)
  :short "Generate the name of the Java field for an ACL2 quoted symbol."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prepend @('$Q_') (for `quote')
     to a representation of the symbol itself.
     We only use the name of the symbol, not the package name,
     because unlike other fields for quoted constants
     (which go into the main class)
     the ones for symbols go into the classes for the packages.
     We do not flip uppercase and lowercase,
     but we map dashes (which are very common in ACL2 symbols)
     to underscores (which are more readable in Java).")
   (xdoc::p
    "However, for @('t') and @('nil'), we just generate @('T') and @('NIL').
     These two symbols are very common, and this special treatment in Java
     somewhat mirrors the fact that they do not need to be quoted
     in untranslated ACL2 terms."))
  (cond ((eq symbol t) "T")
        ((eq symbol nil) "NIL")
        (t (str::cat "$Q_" (implode (atj-chars-to-jchars-id
                                     (explode (symbol-name symbol))
                                     nil :dash nil))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-symbol-field ((symbol symbolp))
  :returns (field jfieldp)
  :short "Generate a Java field for an ACL2 quoted symbol."
  :long
  (xdoc::topstring-p
   "This is a public static final field with an initializer,
    which constructs the string value.
    It is thus part of the public interface offered by
    the code generated by ATJ.
    Unlike the fields for other types of quoted constants,
    this one is declared in the class for the package of the symbol
    (or for a pacakge that imports the symbol).")
  (b* ((name (atj-gen-shallow-symbol-field-name symbol))
       (init (atj-gen-symbol symbol))
       (type *aij-type-symbol*))
    (make-jfield :access (jaccess-public)
                 :static? t
                 :final? t
                 :transient? nil
                 :volatile? nil
                 :type type
                 :name name
                 :init init)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-symbol-fields ((symbols symbol-listp))
  :returns (fields jfield-listp)
  :short "Lift @(tsee atj-gen-shallow-symbol-field) to lists."
  (cond ((endp symbols) nil)
        (t (cons (atj-gen-shallow-symbol-field (car symbols))
                 (atj-gen-shallow-symbol-fields (cdr symbols))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-cons-field-name ((cons consp) (qpairs cons-pos-alistp))
  :returns (name stringp)
  :short "Generate the name of the Java field
          for an ACL2 quoted @(tsee cons) pair."
  :long
  (xdoc::topstring
   (xdoc::p
    "When this function is called,
     the @(tsee cons) pair in question has already been collected
     in an @(tsee atj-qconstants) record,
     whose alist from @(tsee cons) pairs to indices
     is passed to this function.
     We prepend @('$P_') (for `pair')
     to the index associated to the @(tsee cons) pair in the alist.")
   (xdoc::p
    "Since @(tsee cons) pairs may be potentially large (unlike atoms),
     there is no easy way to generate a good field name based on the value,
     unlike in @(tsee atj-gen-shallow-number-field-name) and others.
     Thus, as we collect @(tsee cons) pairs from terms,
     we assign unique indices to them, stored in the alist,
     and we use the index as the name for the field
     that contains the associated @(tsee cons) pair."))
  (b* ((cons+index (assoc-equal cons qpairs))
       ((unless (consp cons+index))
        (raise "Internal error: no index for CONS pair ~x0." cons)
        "")
       (index (cdr cons+index)))
    (str::cat "$P_" (str::natstr index))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-cons-field ((cons consp) (qpairs cons-pos-alistp))
  :returns (field jfieldp)
  :short "Generate a Java field for an ACL2 quoted @(tsee cons) pair."
  :long
  (xdoc::topstring-p
   "This is a private static final field with an initializer,
    which constructs the @(tsee cons) value.")
  (b* ((name (atj-gen-shallow-cons-field-name cons qpairs))
       (init (atj-gen-value-flat cons))
       (type *aij-type-cons*))
    (make-jfield :access (jaccess-private)
                 :static? t
                 :final? t
                 :transient? nil
                 :volatile? nil
                 :type type
                 :name name
                 :init init)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-cons-fields ((conses alistp) (qpairs cons-pos-alistp))
  :returns (fields jfield-listp)
  :short "Lift @(tsee atj-gen-shallow-cons-field) to lists."
  :long
  (xdoc::topstring-p
   "A true list of @(tsee consp) pairs is actually an @(tsee alistp),
    so we use that as the type of the first argument.
    However, it is treated as a list, not as an alist.")
  (cond ((endp conses) nil)
        (t (cons (atj-gen-shallow-cons-field (car conses) qpairs)
                 (atj-gen-shallow-cons-fields (cdr conses) qpairs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-number ((number acl2-numberp))
  :returns (expr jexprp)
  :short "Generate a shallowly embedded ACL2 quoted number."
  :long
  (xdoc::topstring-p
   "This is just a reference to the field for the quoted number.")
  (jexpr-name (atj-gen-shallow-number-field-name number)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-char ((char characterp))
  :returns (expr jexprp)
  :short "Generate a shallowly embedded ACL2 quoted character."
  :long
  (xdoc::topstring-p
   "This is just a reference to the field for the quoted character.")
  (jexpr-name (atj-gen-shallow-char-field-name char)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-string ((string stringp))
  :returns (expr jexprp)
  :short "Generate a shallowly embedded ACL2 quoted string."
  :long
  (xdoc::topstring-p
   "This is just a reference to the field for the quoted string.")
  (jexpr-name (atj-gen-shallow-string-field-name string)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-symbol ((symbol symbolp)
                                (pkg-class-names string-string-alistp)
                                (curr-pkg stringp))
  :returns (expr jexprp)
  :short "Generate a shallowly embedded ACL2 quoted symbol."
  :long
  (xdoc::topstring
   (xdoc::p
    "This depends on the current package,
     i.e. the package of the function where the quoted symbol occurs.
     If the current package is the same as the symbol's package,
     or if the current package imports the symbol,
     then we just generate the simple name of the field,
     because the field will be declared in the class for the current package.
     Otherwise, we generate a qualified name,
     preceded by the name of the class for the symbol's package.
     This mirrors the rules for symbol references in ACL2."))
  (b* ((sym-pkg (symbol-package-name symbol))
       (simple-name (atj-gen-shallow-symbol-field-name symbol))
       ((when (or (equal sym-pkg curr-pkg)
                  (member-eq symbol (pkg-imports curr-pkg))))
        (jexpr-name simple-name))
       (class-name (atj-get-pkg-class-name sym-pkg pkg-class-names)))
    (jexpr-name (str::cat class-name "." simple-name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-cons ((cons consp) (qpairs cons-pos-alistp))
  :returns (expr jexprp)
  :short "Generate a shallowly embedded ACL2 quoted @(tsee cons) pair."
  :long
  (xdoc::topstring-p
   "This is just a reference to the field for the quoted @(tsee cons) pair.")
  (jexpr-name (atj-gen-shallow-cons-field-name cons qpairs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-value (value
                               (qpairs cons-pos-alistp)
                               (pkg-class-names string-string-alistp)
                               (curr-pkg stringp))
  :returns (expr jexprp)
  :short "Generate a shallowly  embedded ACL2 value."
  :long
  (xdoc::topstring-p
   "For numbers, characters, strings, and symbols,
    we use functions specialized to the shallow embedding.
    For other values (i.e. @(tsee cons) pair),
    for now we use @(tsee atj-gen-value-flat).")
  (cond ((acl2-numberp value) (atj-gen-shallow-number value))
        ((characterp value) (atj-gen-shallow-char value))
        ((stringp value) (atj-gen-shallow-string value))
        ((symbolp value) (atj-gen-shallow-symbol value
                                                 pkg-class-names
                                                 curr-pkg))
        ((consp value) (atj-gen-shallow-cons value qpairs))
        (t (prog2$ (raise "Internal error: ~x0 is not a recognized value" value)
                   (jexpr-name "")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fnname ((fn symbolp)
                                (pkg-class-names string-string-alistp)
                                (fn-method-names symbol-string-alistp)
                                (curr-pkg stringp))
  :guard (not (equal curr-pkg ""))
  :returns (method-name stringp)
  :short "Generate a shallowly embedded ACL2 function name."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     each ACL2 function is represented as a Java method.
     The Java methods for all the ACL2 functions that are translated to Java
     are partitioned by ACL2 packages:
     there is a Java class for each ACL2 package,
     and the Java method for each ACL2 function
     is in the Java class corresponding to the ACL2 package of the function.")
   (xdoc::p
    "These are all static methods, which can therefore be referenced as
     @('<class>.<method>') in Java code,
     not dissmilarly to @('<pkg>::<fn>') in ACL2.
     However, inside @('<class>'), it suffices to use @('<method>'),
     which is more readable.
     Furthermore, since we generate method synonyms under certain conditions,
     as explained in @(tsee atj-gen-shallow-synonym-method),
     it suffices to use @('<method>')
     if the function is imported by the package.
     Thus, we prepend the Java class name to the Java method name
     if and only if the current ACL2 package (the @('curr-pkg') argument)
     differs from the ACL2 function's package
     and the package does not import the function.")
   (xdoc::p
    "The Java class name @('<class>') is looked up
     in the alist @('pkg-class-names'),
     and the Java method name @('<method>') is looked up
      in the alist @('fn-method-names')."))
  (b* ((pkg (symbol-package-name fn))
       (class? (if (or (equal pkg curr-pkg)
                       (member-eq fn (pkg-imports curr-pkg)))
                   ""
                 (b* ((class (atj-get-pkg-class-name pkg pkg-class-names)))
                   (str::cat class "."))))
       (method (atj-get-fn-method-name fn fn-method-names)))
    (str::cat class? method)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-let-bindings ((vars symbol-listp)
                                      (blocks jblock-listp)
                                      (exprs jexpr-listp))
  :guard (and (int= (len blocks) (len vars))
              (int= (len exprs) (len vars)))
  :returns (block jblockp :hyp (jblock-listp blocks))
  :short "Generate shallowly embedded ACL2 @(tsee let) bindings."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     ACL2 lambda expressions (i.e. @(tsee let)s)
     are handled by assigning the Java expressions
     generated from the actual parameters of the lambda expression
     to Java local variables corresponding to the formal parameters.
     This function generates these bindings,
     given the ACL2 variables that are the formal arguments
     and the Java expressions to assign to them.
     Each binding is preceded by the block (if any)
     generated for the corresponding actual argument of the lambda expression.")
   (xdoc::p
    "Prior to calling this function,
     the variables of all the lambda expressiona have been marked
     as `new' or `old' via @(tsee atj-mark-term).
     We extract this mark and use it to generate
     either a variable declaration with initializer (for `new')
     or an assignment to an existing variable (for `old').")
   (xdoc::p
    "Prior to calling this function,
     the variables of all the lambda expressions have been annotated
     via @(tsee atj-type-annotate-term).
     Thus, each ACL2 variable name carries its own type,
     which we use to determine the Java type of the Java variable.")
   (xdoc::p
    "Prior to calling this function,
     the variables of all the lambda expressions have been renamed
     via @(tsee atj-rename-term).
     Thus, we directly turn each ACL2 variable into a Java variable name
     (after removing the type annotations)."))
  (b* (((when (endp vars)) nil)
       (var (car vars))
       (expr (car exprs))
       ((mv var new?) (atj-unmark-var var))
       ((mv var type) (atj-type-unannotate-var var))
       (jvar (symbol-name var))
       (var-block (if new?
                      (jblock-locvar (atj-type-to-jtype type) jvar expr)
                    (jblock-asg (jexpr-name jvar) expr)))
       (first-block (append (car blocks) var-block))
       (rest-block (atj-gen-shallow-let-bindings (cdr vars)
                                                 (cdr blocks)
                                                 (cdr exprs))))
    (append first-block rest-block)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-adapt-expr-from-jprim-to-cons
  ((expr jexprp)
   (type (member-eq type '(:jboolean :jchar :jbyte :jshort :jint :jlong)))
   (pkg-class-names string-string-alistp)
   (curr-pkg stringp))
  :returns (new-expr jexprp)
  :short "Adapt a Java expression
          from a Java primitive type to type @('Acl2ConsValue')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee atj-adapt-expr-to-type),
     when the source ATJ type is a @(':j...') type
     and the destination ATJ type is @(':acons') or @(':avalue').
     In our ACL2 model of Java,
     Java primitive values are represented as
     values satisfying @(tsee int-value-p) and analogous predicates.
     We convert from the Java primitive type returned by the expression
     to the Java @('Acl2ConsValue') that represents
     the ACL2 representation of the Java primitive value.")
   (xdoc::p
    "The representation is explicated and checked "
    (xdoc::seetopic "atj-java-primitive-values-representation-check" "here")
    ". We first create the ``core'' expression from the initial expression:
     this core expression is
     an @('Acl2Symbol') (@('t') or @('nil')) for @(':jboolean'),
     or an @('Acl2Integer') for the other @(':j...') types.
     Then we create a list of length 2 (as two @('Acl2ConsPair')s)
     whose first element is the @('Acl2Symbol')
     for the keyword for the primitive type,
     and whose second element is the aforementioned core expression."))
  (b* ((acl2-symbol-t-expr (atj-gen-shallow-symbol
                            t pkg-class-names curr-pkg))
       (acl2-symbol-nil-expr (atj-gen-shallow-symbol
                              nil pkg-class-names curr-pkg))
       (acl2-core-expr (case type
                         (:jboolean (jexpr-cond expr
                                                acl2-symbol-t-expr
                                                acl2-symbol-nil-expr))
                         (t (jexpr-smethod *aij-type-int*
                                           "make"
                                           (list expr)))))
       (acl2-inner-cons-expr (jexpr-smethod *aij-type-cons*
                                            "make"
                                            (list acl2-core-expr
                                                  acl2-symbol-nil-expr)))
       (acl2-keyword-name (case type
                            (:jboolean "BOOLEAN")
                            (:jchar "CHAR")
                            (:jbyte "BYTE")
                            (:jshort "SHORT")
                            (:jint "INT")
                            (:jlong "LONG")
                            (t (impossible))))
       (acl2-keyword-boolean-expr (jexpr-smethod *aij-type-symbol*
                                                 "makeKeyword"
                                                 (list
                                                  (jexpr-literal-string
                                                   acl2-keyword-name))))
       (acl2-outer-cons-expr (jexpr-smethod *aij-type-cons*
                                            "make"
                                            (list acl2-keyword-boolean-expr
                                                  acl2-inner-cons-expr))))
    acl2-outer-cons-expr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-adapt-expr-from-value-to-jprim
  ((expr jexprp)
   (type (member-eq type '(:jboolean :jchar :jbyte :jshort :jint :jlong)))
   (pkg-class-names string-string-alistp)
   (curr-pkg stringp))
  :returns (new-expr jexprp)
  :short "Adapt a Java expression
          from type @('Acl2Value') to a Java primitive type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee atj-adapt-expr-to-type),
     when the source ATJ type is @(':acons') or @(':avalue')
     and the destination ATJ type is a @(':j...') type.
     This performs the inverse adaptation
     of the one made by @(tsee atj-adapt-expr-from-jprim-to-cons):
     see that function for a discussion of
     the Java representation of the ACL2 representation
     of the Java primitive values.")
   (xdoc::p
    "Assuming guard verification,
     the argument of this function should always be
     an expression that returns an @('Acl2Value') with the right representation,
     i.e. the representation explicated and checked "
    (xdoc::seetopic "atj-java-primitive-values-representation-check" "here")
    ". We cast the @('Acl2Value') to a @('Acl2ConsPair'),
     get its @(tsee cdr),
     cast that to @('Acl2ConsPair'),
     and get its @(tsee car),
     which is then further adapted as follows:
     for @(':jboolean'),
     we cast it to @('Acl2Symbol'),
     and turn that into a @('boolean')
     based on whether it is @('t') or not;
     for @(':jchar'), @(':jbyte'), and @(':jshort'),
     we cast it to @('Acl2Integer'),
     get its numeric value as an @('int'),
     and cast it to @('char'), @('byte'), or @('short');
     for @(':jint'),
     we cast it to @('Acl2Integer'),
     and get its numeric value as @('int');
     for @(':jlong'),
     we cast it to @('Acl2Integer'),
     and get its numeric value as @('long')."))
  (b* ((acl2-symbol-nil-expr (atj-gen-shallow-symbol
                              nil pkg-class-names curr-pkg))
       (acl2-outer-cons-expr (jexpr-cast *aij-type-cons* expr))
       (acl2-cdr-expr (jexpr-imethod acl2-outer-cons-expr "getCdr" nil))
       (acl2-inner-cons-expr (jexpr-cast *aij-type-cons* acl2-cdr-expr))
       (acl2-car-expr (jexpr-imethod acl2-inner-cons-expr "getCar" nil)))
    (case type
      (:jboolean
       (b* ((acl2-symbol-expr (jexpr-cast *aij-type-symbol* acl2-car-expr)))
         (jexpr-binary (jbinop-eq) acl2-symbol-expr acl2-symbol-nil-expr)))
      (:jchar
       (b* ((acl2-integer-expr (jexpr-cast *aij-type-int* acl2-car-expr))
            (int-expr (jexpr-imethod acl2-integer-expr "getJavaInt" nil)))
         (jexpr-cast (jtype-char) int-expr)))
      (:jbyte
       (b* ((acl2-integer-expr (jexpr-cast *aij-type-int* acl2-car-expr))
            (int-expr (jexpr-imethod acl2-integer-expr "getJavaInt" nil)))
         (jexpr-cast (jtype-byte) int-expr)))
      (:jshort
       (b* ((acl2-integer-expr (jexpr-cast *aij-type-int* acl2-car-expr))
            (int-expr (jexpr-imethod acl2-integer-expr "getJavaInt" nil)))
         (jexpr-cast (jtype-short) int-expr)))
      (:jint
       (b* ((acl2-integer-expr (jexpr-cast *aij-type-int* acl2-car-expr)))
         (jexpr-imethod acl2-integer-expr "getJavaInt" nil)))
      (:jlong
       (b* ((acl2-integer-expr (jexpr-cast *aij-type-int* acl2-car-expr)))
         (jexpr-imethod acl2-integer-expr "getJavaLong" nil)))
      (t (prog2$ (impossible) (jexpr-fix expr))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-adapt-expr-to-type ((expr jexprp)
                                (src-type atj-typep)
                                (dst-type atj-typep)
                                (pkg-class-names string-string-alistp)
                                (curr-pkg stringp))
  :returns (new-expr jexprp :hyp (jexprp expr))
  :short "Adapt a Java expression from a source type to a destination type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when generating
     shallowly embedded ACL2 calls of named functions.
     As explained " (xdoc::seetopic "atj-types" "here") ",
     when the type of an actual argument of a function call
     is not the same as or a subtype (according to Java subtyping) of
     the type of the formal argument,
     ATJ adds Java code to convert from the former type to the latter type.")
   (xdoc::p
    "This code generation function does that.
     The input Java expression is the one generated for the actual argument,
     whose type is @('src-type') (for `source type').
     The input @('dst-type') (for `destination type')
     is the type of the corresponding formal argument.")
   (xdoc::p
    "A conversion from a @(':j...') type to another type
     is possible only if the other type is @(':acons') or @(':avalue');
     otherwise, the assumption of guard verification must be violated somehow.
     A conversion to a @(':j...') type from another type
     is possible only if the other type is @(':acons') or @(':avalue');
     otherwise, the assumption of guard verification must be violated somehow.
     To convert between the AIJ class types,
     if the source type is a subtype of or the same type as
     the destination type
     (which can be checked via @(tsee atj-type-<=),
     we leave the expression unchanged;
     otherwise, we insert a cast to the destination type,
     which is expected to always succeed
     under the assumption of guard verification."))
  (cond ((eq src-type dst-type) expr)
        ((member-eq src-type '(:jboolean :jchar :jbyte :jshort :jint :jlong))
         (if (member-eq dst-type '(:acons :avalue))
             (atj-adapt-expr-from-jprim-to-cons
              expr src-type pkg-class-names curr-pkg)
           (prog2$ (raise "Internal error: ~
                           attempting to convert the Java expression ~x0 ~
                           from type ~x1 to type ~x2."
                          expr src-type dst-type)
                   expr)))
        ((member-eq dst-type '(:jboolean :jchar :jbyte :jshort :jint :jlong))
         (if (member-eq src-type '(:acons :avalue))
             (atj-adapt-expr-from-value-to-jprim
              expr dst-type pkg-class-names curr-pkg)
           (prog2$ (raise "Internal error: ~
                           attempting to convert the Java expression ~x0 ~
                           from type ~x1 to type ~x2."
                          expr src-type dst-type)
                   expr)))
        ((atj-type-<= src-type dst-type) expr)
        (t (jexpr-cast (atj-type-to-jtype dst-type) expr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-adapt-exprs-to-types ((exprs jexpr-listp)
                                  (src-types atj-type-listp)
                                  (dst-types atj-type-listp)
                                  (pkg-class-names string-string-alistp)
                                  (curr-pkg stringp))
  :guard (and (= (len exprs) (len src-types))
              (= (len exprs) (len dst-types)))
  :returns (new-exprs jexpr-listp :hyp (jexpr-listp exprs))
  :short "Lift @(tsee atj-adapt-expr-to-type) to lists."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used for all the arguments of a function call."))
  (cond ((endp exprs) nil)
        (t (cons (atj-adapt-expr-to-type (car exprs)
                                         (car src-types)
                                         (car dst-types)
                                         pkg-class-names
                                         curr-pkg)
                 (atj-adapt-exprs-to-types (cdr exprs)
                                           (cdr src-types)
                                           (cdr dst-types)
                                           pkg-class-names
                                           curr-pkg)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-gen-cond-exprs*
  :short "Flag saying whether ATJ should attempt to
          generate Java conditional expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is an internal flag, developer-oriented.
     If @('t'), ATJ will generate shallowly embedded
     Java conditional expressions @('... ? ... : ...')
     under suitable conditions;
     see the code generation functions that reference this flag.")
   (xdoc::p
    "This flag is currently @('nil'),
     because, with the current tests,
     the code looked less readable overall
     then when this flag is @('t').
     This flag may be removed eventually."))
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-gen-shallow-term-fns
  :short "Functions to generate shallowly embedded ACL2 terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     the actual arguments of an ACL2 function or lambda expression
     are calculated by the generated Java code,
     and then the (shallowly embedded) ACL2 function or lambda expression
     is called on them.
     However, for the non-strict function @(tsee if)
     and the non-strict ``pseudo-function'' @('or')
     (see the documentation of AIJ for details on the latter),
     the generated Java code follows a different strategy,
     in order to realize the required non-strictness.
     This strategy involves generating Java local variables
     to store results of arguments of non-strict ACL2 functions.
     The base name to use for these variables
     is an argument of these code generation functions.")
   (xdoc::p
    "These code generation functions assume that the ACL2 terms
     have been type-annotated via @(tsee atj-type-annotate-term).
     They also assume that all the variables of the ACL2 terms have been marked
     via @(tsee atj-mark-var-new) and @(tsee atj-mark-var-old),
     and renamed via @(tsee atj-rename-term).
     If the @(':guards') input is @('nil'),
     then all the type annotations consist of
     the type @(':avalue') of all ACL2 values,
     i.e. it is as if there were no types."))

  (define atj-gen-shallow-iftest ((test pseudo-termp)
                                  (jvar-result-base stringp)
                                  (jvar-result-index posp)
                                  (pkg-class-names string-string-alistp)
                                  (fn-method-names symbol-string-alistp)
                                  (curr-pkg stringp)
                                  (qpairs cons-pos-alistp)
                                  (guards$ booleanp)
                                  (wrld plist-worldp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-result-index posp :hyp (posp jvar-result-index)))
    :parents (atj-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded ACL2 @(tsee if) test."
    :long
    (xdoc::topstring
     (xdoc::p
      "See @(tsee atj-gen-shallow-ifapp) for a general description
       of how ACL2 @(tsee if)s are translated to Java @('if')s.")
     (xdoc::p
      "Here we handle the test of the @(tsee if).
       If the test has the form @('(boolean-value->bool b)'),
       as explained in @(tsee atj-types-for-boolean-value-destructor),
       we translate @('b') to its Java equivalent,
       ``ignoring'' @(tsee boolean-value->bool).
       More precisely, we are dealing with annotated terms,
       so we look for @(tsee if) tests of the form
       @('([AS>AS] (boolean-value->bool ([JZ>JZ] <jbool>)))'),
       where @('<jbool>') evidently returns
       (our ACL2 model of) a Java boolean value,
       given the @('[JZ>JZ]') (non-)conversion (see @(tsee atj-type-conv)),
       where the destination type @(':jboolean')
       is the one assigned to the input of @(tsee boolean-value->bool).
       When an @(tsee if) test is type-annotated,
       no specific type is required for the test
       (see @(tsee atj-type-annotate-term)),
       so since the output type @(':asymbol')
       is assigned to @(tsee boolean-value->bool),
       the @('[AS>AS]') (non-)conversion will always wrap the test.")
     (xdoc::p
      "So, if the @(tsee if) test has the form just explained,
       we translate just @('<jbool>') to Java.
       Otherwise, we translate the whole test term,
       and return an expression that compares it with
       (the Java representation of) @('nil')."))
    (b* ((jbool? ; non-NIL iff TEST has the form explained above
          (b* (((mv test src-type dst-type) (atj-type-unwrap-term test))
               ((unless (and (eq src-type :asymbol)
                             (eq dst-type :asymbol)))
                nil)
               ((unless (and (consp test)
                             (eq (ffn-symb test)
                                 'boolean-value->bool$inline)
                             (int= (len (fargs test)) 1))) ; always true
                nil)
               (test (fargn test 1))
               ((unless (and (consp test)
                             (eq (ffn-symb test)
                                 (atj-type-conv :jboolean :jboolean))
                             (int= (len (fargs test)) 1))) ; always true
                nil))
            test))
         ((mv block
              expr
              jvar-result-index) (atj-gen-shallow-term (or jbool? test)
                                                       jvar-result-base
                                                       jvar-result-index
                                                       pkg-class-names
                                                       fn-method-names
                                                       curr-pkg
                                                       qpairs
                                                       guards$
                                                       wrld))
         (expr (if jbool?
                   expr
                 (jexpr-binary (jbinop-ne)
                               expr
                               (atj-gen-shallow-symbol
                                nil pkg-class-names curr-pkg)))))
      (mv block expr jvar-result-index))
    ;; 2nd component is non-0
    ;; so that the call of ATJ-GEN-SHALLOW-TERM decreases:
    :measure (two-nats-measure (acl2-count test) 1))

  (define atj-gen-shallow-ifapp ((test pseudo-termp)
                                 (then pseudo-termp)
                                 (else pseudo-termp)
                                 (type atj-typep)
                                 (jvar-result-base stringp)
                                 (jvar-result-index posp)
                                 (pkg-class-names string-string-alistp)
                                 (fn-method-names symbol-string-alistp)
                                 (curr-pkg stringp)
                                 (qpairs cons-pos-alistp)
                                 (guards$ booleanp)
                                 (wrld plist-worldp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-result-index posp :hyp (posp jvar-result-index)))
    :parents (atj-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded ACL2 @(tsee if) application."
    :long
    (xdoc::topstring
     (xdoc::p
      "Consider a call @('(if a b c)').
       If the Java code generated for @('a')
       consists of the block @('<a-block>') and expression @('<a-expr>'),
       and similarly for @('b') and @('c'),
       we generate the Java block")
     (xdoc::codeblock
      "<a-block>"
      "<type> <result> = null;"
      "if (<a-expr> != NIL) {"
      "    <b-blocks>"
      "    <result> = <b-expr>;"
      "} else {"
      "    <c-blocks>"
      "    <result> = <c-expr>;"
      "}")
     (xdoc::p
      "and the Java expression @('<result>'),
       where @('<result>') consists of
       the base name in the parameter @('jvar-result-base')
       followed by a numeric index.")
     (xdoc::p
      "In other words, we first compute the test
       and create a local variable to store the final result.
       Based on the test, we execute either branch (for non-strictness),
       storing the result into the variable.")
     (xdoc::p
      "The type @('<type>') of the result variable is
       derived from the ATJ type passed to this code generation function.
       See @(tsee atj-gen-shallow-fnapp) for details.")
     (xdoc::p
      "If the flag @(tsee *atj-gen-cond-exprs*) is set,
       and if both @('<b-block>') and @('<c-block>') are empty,
       we generate the Java block")
     (xdoc::codeblock
      "<a-block>")
     (xdoc::p
      "and the Java expression")
     (xdoc::codeblock
      "<a-expr> != NIL ? <b-expr> : <c-expr>")
     (xdoc::p
      "However, if the test of the @(tsee if) has the form
       @('([AS>AS] (boolean-value->bool ([JZ>JZ] a)))'),
       we generate just @('<a-expr>') as the test of the Java @('if'):
       see @(tsee atj-gen-shallow-iftest) for details."))
    (b* (((mv test-block
              test-expr
              jvar-result-index) (atj-gen-shallow-iftest test
                                                         jvar-result-base
                                                         jvar-result-index
                                                         pkg-class-names
                                                         fn-method-names
                                                         curr-pkg
                                                         qpairs
                                                         guards$
                                                         wrld))
         ((mv then-block
              then-expr
              jvar-result-index) (atj-gen-shallow-term then
                                                       jvar-result-base
                                                       jvar-result-index
                                                       pkg-class-names
                                                       fn-method-names
                                                       curr-pkg
                                                       qpairs
                                                       guards$
                                                       wrld))
         ((mv else-block
              else-expr
              jvar-result-index) (atj-gen-shallow-term else
                                                       jvar-result-base
                                                       jvar-result-index
                                                       pkg-class-names
                                                       fn-method-names
                                                       curr-pkg
                                                       qpairs
                                                       guards$
                                                       wrld))
         ((when (and *atj-gen-cond-exprs*
                     (null then-block)
                     (null else-block)))
          (b* ((block test-block)
               (expr (jexpr-cond test-expr
                                 then-expr
                                 else-expr)))
            (mv block
                expr
                jvar-result-index)))
         (jtype (atj-type-to-jtype type))
         ((mv result-locvar-block jvar-result jvar-result-index)
          (atj-gen-jlocvar-indexed jtype
                                   jvar-result-base
                                   jvar-result-index
                                   (jexpr-literal-null)))
         (if-block (jblock-ifelse
                    test-expr
                    (append then-block
                            (jblock-asg-name jvar-result then-expr))
                    (append else-block
                            (jblock-asg-name jvar-result else-expr))))
         (block (append test-block
                        result-locvar-block
                        if-block))
         (expr (jexpr-name jvar-result)))
      (mv block
          expr
          jvar-result-index))
    ;; 2nd component is greater than 0 and 1
    ;; so that the call of ATJ-GEN-SHALLOW-IFTEST decreases
    ;; and each call of ATJ-GEN-SHALLOW-TERM decreases
    ;; even when the ACL2-COUNTs of the other two addends are 0:
    :measure (two-nats-measure (+ (acl2-count test)
                                  (acl2-count then)
                                  (acl2-count else))
                               2))

  (define atj-gen-shallow-orapp ((first pseudo-termp)
                                 (second pseudo-termp)
                                 (type atj-typep)
                                 (jvar-result-base stringp)
                                 (jvar-result-index posp)
                                 (pkg-class-names string-string-alistp)
                                 (fn-method-names symbol-string-alistp)
                                 (curr-pkg stringp)
                                 (qpairs cons-pos-alistp)
                                 (guards$ booleanp)
                                 (wrld plist-worldp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-result-index posp :hyp (posp jvar-result-index)))
    :parents (atj-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded ACL2 @('or') application."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is for the @('or') ACL2 ``pseudo-function''
       (see the AIJ documentation for details).
       We treat @('(or a b)') non-strictly like @('(if a a b)'),
       but we avoid calculating @('a') twice.
       Somewhat similarly to how we treat @(tsee if),
       we generate the Java block")
     (xdoc::codeblock
      "<a-block>"
      "<type> <result> = <a-expr>;"
      "if (<result> == NIL) {"
      "    <b-blocks>"
      "    <result> = <b-expr>;"
      "}")
     (xdoc::p
      "and the Java expression @('<result>')."))
    (b* (((mv first-block
              first-expr
              jvar-result-index) (atj-gen-shallow-term first
                                                       jvar-result-base
                                                       jvar-result-index
                                                       pkg-class-names
                                                       fn-method-names
                                                       curr-pkg
                                                       qpairs
                                                       guards$
                                                       wrld))
         ((mv second-block
              second-expr
              jvar-result-index) (atj-gen-shallow-term second
                                                       jvar-result-base
                                                       jvar-result-index
                                                       pkg-class-names
                                                       fn-method-names
                                                       curr-pkg
                                                       qpairs
                                                       guards$
                                                       wrld))
         (jtype (atj-type-to-jtype type))
         ((mv result-locvar-block jvar-result jvar-result-index)
          (atj-gen-jlocvar-indexed jtype
                                   jvar-result-base
                                   jvar-result-index
                                   first-expr))
         (if-block (jblock-if
                    (jexpr-binary (jbinop-eq)
                                  (jexpr-name jvar-result)
                                  (atj-gen-shallow-symbol
                                   nil pkg-class-names curr-pkg))
                    (append second-block
                            (jblock-asg-name jvar-result second-expr))))
         (block (append first-block
                        result-locvar-block
                        if-block))
         (expr (jexpr-name jvar-result)))
      (mv block
          expr
          jvar-result-index))
    ;; 2nd component is non-0
    ;; so that each call of ATJ-GEN-SHALLOW-TERM decreases
    ;; even when the ACL2-COUNT of the other addend is 0:
    :measure (two-nats-measure (+ (acl2-count first)
                                  (acl2-count second))
                               1))

  (define atj-gen-shallow-primconstrapp ((fn (member-eq
                                              fn *atj-primitive-constructors*))
                                         (arg pseudo-termp)
                                         (src-type atj-typep)
                                         (dst-type atj-typep)
                                         (jvar-result-base stringp)
                                         (jvar-result-index posp)
                                         (pkg-class-names string-string-alistp)
                                         (fn-method-names symbol-string-alistp)
                                         (curr-pkg stringp)
                                         (qpairs cons-pos-alistp)
                                         (wrld plist-worldp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-result-index posp :hyp (posp jvar-result-index)))
    :parents (atj-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded
            ACL2 application of a Java primitive constructor."
    :long
    (xdoc::topstring
     (xdoc::p
      "This code generation function is called
       only if @(':guards') is @('t').")
     (xdoc::p
      "If the @(':guards') input is @('t'),
       the functions that model the construction of Java primtive values
       (i.e. @(tsee boolean-value) etc.)
       are treated specially.
       If the argument is a quoted constant,
       the function application is translated
       to the constant Java primitive expression
       whose value is the quoted constant.
       If the argument is not a quoted constant,
       we first translate it to a Java expression in the general way;
       we then wrap the expression with code
       to convert it to the appropriate Java primitive type.
       In all cases, we convert the resulting expression, as needed,
       to match the destination type.")
     (xdoc::p
      "Note that we are dealing with annotated terms,
       so the argument of the constructor must be unwrapped
       to be examined."))
    (b* (((mv arg & &) (atj-type-unwrap-term arg))
         ((unless arg) ; for termination proof
          (mv nil (jexpr-name "irrelevant") jvar-result-index)))
      (if (quotep arg)
          (cond ((eq fn 'boolean-value)
                 (b* ((boolean (unquote-term arg))
                      ((unless (booleanp boolean))
                       (prog2$
                        (raise "Internal error: BOOLEAN-VALUE applied to ~x0."
                               boolean)
                        (mv nil (jexpr-name "irrelevant") jvar-result-index)))
                      (expr (atj-gen-jboolean boolean))
                      (expr (atj-adapt-expr-to-type
                             expr src-type dst-type pkg-class-names curr-pkg)))
                   (mv nil expr jvar-result-index)))
                ((eq fn 'char-value)
                 (b* ((char (unquote-term arg))
                      ((unless (ubyte16p char))
                       (prog2$
                        (raise "Internal error: CHAR-VALUE applied to ~x0."
                               char)
                        (mv nil (jexpr-name "irrelevant") jvar-result-index)))
                      (expr (atj-gen-jchar char))
                      (expr (atj-adapt-expr-to-type
                             expr src-type dst-type pkg-class-names curr-pkg)))
                   (mv nil expr jvar-result-index)))
                ((eq fn 'byte-value)
                 (b* ((byte (unquote-term arg))
                      ((unless (sbyte8p byte))
                       (prog2$
                        (raise "Internal error: BYTE-VALUE applied to ~x0."
                               byte)
                        (mv nil (jexpr-name "irrelevant") jvar-result-index)))
                      (expr (atj-gen-jbyte byte))
                      (expr (atj-adapt-expr-to-type
                             expr src-type dst-type pkg-class-names curr-pkg)))
                   (mv nil expr jvar-result-index)))
                ((eq fn 'short-value)
                 (b* ((short (unquote-term arg))
                      ((unless (sbyte16p short))
                       (prog2$
                        (raise "Internal error: SHORT-VALUE applied to ~x0."
                               short)
                        (mv nil (jexpr-name "irrelevant") jvar-result-index)))
                      (expr (atj-gen-jshort short))
                      (expr (atj-adapt-expr-to-type
                             expr src-type dst-type pkg-class-names curr-pkg)))
                   (mv nil expr jvar-result-index)))
                ((eq fn 'int-value)
                 (b* ((int (unquote-term arg))
                      ((unless (sbyte32p int))
                       (prog2$
                        (raise "Internal error: INT-VALUE applied to ~x0."
                               int)
                        (mv nil (jexpr-name "irrelevant") jvar-result-index)))
                      (expr (atj-gen-jint int))
                      (expr (atj-adapt-expr-to-type
                             expr src-type dst-type pkg-class-names curr-pkg)))
                   (mv nil expr jvar-result-index)))
                ((eq fn 'long-value)
                 (b* ((long (unquote-term arg))
                      ((unless (sbyte64p long))
                       (prog2$
                        (raise "Internal error: LONG-VALUE applied to ~x0."
                               long)
                        (mv nil (jexpr-name "irrelevant") jvar-result-index)))
                      (expr (atj-gen-jlong long))
                      (expr (atj-adapt-expr-to-type
                             expr src-type dst-type pkg-class-names curr-pkg)))
                   (mv nil expr jvar-result-index)))
                (t (mv (impossible)
                       (jexpr-name "irrelevant")
                       jvar-result-index)))
        (b* (((mv arg-block
                  arg-expr
                  jvar-result-index) (atj-gen-shallow-term arg
                                                           jvar-result-base
                                                           jvar-result-index
                                                           pkg-class-names
                                                           fn-method-names
                                                           curr-pkg
                                                           qpairs
                                                           t ; GUARDS$
                                                           wrld))
             (expr (cond
                    ((eq fn 'boolean-value)
                     (atj-adapt-expr-to-type
                      arg-expr :asymbol src-type pkg-class-names curr-pkg))
                    ((member-eq fn '(char-value
                                     byte-value
                                     short-value
                                     int-value
                                     long-value))
                     (atj-adapt-expr-to-type
                      arg-expr :ainteger src-type pkg-class-names curr-pkg))
                    (t (prog2$ (impossible)
                               (jexpr-name "irrelevant"))))))
          (mv arg-block
              (atj-adapt-expr-to-type
               expr src-type dst-type pkg-class-names curr-pkg)
              jvar-result-index))))
    ;; 2nd component is non-0
    ;; so that the call of ATJ-GEN-SHALLOW-TERM decreases:
    :measure (two-nats-measure (acl2-count arg) 1))

  (define atj-gen-shallow-primunapp ((fn (member-eq fn *atj-primitive-unops*))
                                     (operand pseudo-termp)
                                     (src-type atj-typep)
                                     (dst-type atj-typep)
                                     (jvar-result-base stringp)
                                     (jvar-result-index posp)
                                     (pkg-class-names string-string-alistp)
                                     (fn-method-names symbol-string-alistp)
                                     (curr-pkg stringp)
                                     (qpairs cons-pos-alistp)
                                     (wrld plist-worldp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-result-index posp :hyp (posp jvar-result-index)))
    :parents (atj-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded
            ACL2 application of a Java primitive unary operation."
    :long
    (xdoc::topstring
     (xdoc::p
      "This code generation function is called
       only if @(':guards') is @('t').")
     (xdoc::p
      "If the @(':guards') input is @('t'),
       the functions that model Java primitive unary operations
       (i.e. @(tsee int-minus) etc.) are treated specially.
       We generate Java code to compute the operand,
       and generate a Java unary expression
       whose operator corresponds to the function.
       We parenthesize the Java expression
       to avoid errors due to operator precedences
       when expressions are nested;
       in the future we should take precedences into account
       to avoid unnecessary parentheses and make the code more readable
       (it may be actually better to handle this in the pretty-printer).
       For the primitive conversions, we generate a cast to the target type:
       for widening conversions, this is unnecessary,
       but for now we use this simple scheme
       that may also emphasize clarity in the code;
       we may revisit this decision in the future."))
    (b* (((mv operand-block
              operand-expr
              jvar-result-index) (atj-gen-shallow-term operand
                                                       jvar-result-base
                                                       jvar-result-index
                                                       pkg-class-names
                                                       fn-method-names
                                                       curr-pkg
                                                       qpairs
                                                       t ; GUARDS$
                                                       wrld))
         (expr (if (member-eq fn '(boolean-not
                                   int-plus
                                   long-plus
                                   int-minus
                                   long-minus
                                   int-not
                                   long-not))
                   (b* ((unop (case fn
                                (boolean-not (junop-logcompl))
                                (int-plus (junop-uplus))
                                (long-plus (junop-uplus))
                                (int-minus (junop-uminus))
                                (long-minus (junop-uminus))
                                (int-not (junop-bitcompl))
                                (long-not (junop-bitcompl)))))
                     (jexpr-unary unop operand-expr))
                 (b* ((jtype (case fn
                               (byte-to-short (jtype-short))
                               (byte-to-int (jtype-int))
                               (byte-to-long (jtype-long))
                               (short-to-int (jtype-int))
                               (short-to-long (jtype-long))
                               (int-to-long (jtype-long))
                               (char-to-int (jtype-int))
                               (char-to-long (jtype-long))
                               (short-to-byte (jtype-byte))
                               (int-to-byte (jtype-byte))
                               (long-to-byte (jtype-byte))
                               (char-to-byte (jtype-byte))
                               (int-to-short (jtype-short))
                               (long-to-short (jtype-short))
                               (char-to-short (jtype-short))
                               (long-to-int (jtype-int))
                               (short-to-char (jtype-char))
                               (int-to-char (jtype-char))
                               (long-to-char (jtype-char))
                               (byte-to-char (jtype-char)))))
                   (jexpr-cast jtype operand-expr))))
         (block operand-block))
      (mv block
          (atj-adapt-expr-to-type
           expr src-type dst-type pkg-class-names curr-pkg)
          jvar-result-index))
    ;; 2nd component is non-0
    ;; so that the call of ATJ-GEN-SHALLOW-TERM decreases:
    :measure (two-nats-measure (acl2-count operand)
                               1))

  (define atj-gen-shallow-primbinapp ((fn (member-eq fn *atj-primitive-binops*))
                                      (left pseudo-termp)
                                      (right pseudo-termp)
                                      (src-type atj-typep)
                                      (dst-type atj-typep)
                                      (jvar-result-base stringp)
                                      (jvar-result-index posp)
                                      (pkg-class-names string-string-alistp)
                                      (fn-method-names symbol-string-alistp)
                                      (curr-pkg stringp)
                                      (qpairs cons-pos-alistp)
                                      (wrld plist-worldp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-result-index posp :hyp (posp jvar-result-index)))
    :parents (atj-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded
            ACL2 application of a Java primitive binary operation."
    :long
    (xdoc::topstring
     (xdoc::p
      "This code generation function is called
       only if @(':guards') is @('t').")
     (xdoc::p
      "If the @(':guards') input is @('t'),
       the functions that model Java primitive binary operations
       (i.e. @(tsee int-add) etc.) are treated specially.
       We generate Java code to compute the left and right operands,
       and generate a Java binary expression
       whose operator corresponds to the function.
       We parenthesize the Java expression
       to avoid errors due to operator precedences
       when expressions are nested;
       in the future we should take precedences into account
       to avoid unnecessary parentheses and make the code more readable
       (it may be actually better to handle this in the pretty-printer)."))
    (b* (((mv left-block
              left-expr
              jvar-result-index) (atj-gen-shallow-term left
                                                       jvar-result-base
                                                       jvar-result-index
                                                       pkg-class-names
                                                       fn-method-names
                                                       curr-pkg
                                                       qpairs
                                                       t ; GUARDS$
                                                       wrld))
         ((mv right-block
              right-expr
              jvar-result-index) (atj-gen-shallow-term right
                                                       jvar-result-base
                                                       jvar-result-index
                                                       pkg-class-names
                                                       fn-method-names
                                                       curr-pkg
                                                       qpairs
                                                       t ; GUARDS$
                                                       wrld))
         (binop (case fn
                  (boolean-and (jbinop-and))
                  (boolean-xor (jbinop-xor))
                  (boolean-ior (jbinop-ior))
                  (boolean-eq (jbinop-eq))
                  (boolean-neq (jbinop-ne))
                  (int-add (jbinop-add))
                  (long-add (jbinop-add))
                  (int-sub (jbinop-sub))
                  (long-sub (jbinop-sub))
                  (int-mul (jbinop-mul))
                  (long-mul (jbinop-mul))
                  (int-div (jbinop-div))
                  (long-div (jbinop-div))
                  (int-rem (jbinop-rem))
                  (long-rem (jbinop-rem))
                  (int-and (jbinop-and))
                  (long-and (jbinop-and))
                  (int-xor (jbinop-xor))
                  (long-xor (jbinop-xor))
                  (int-ior (jbinop-ior))
                  (long-ior (jbinop-ior))
                  (int-eq (jbinop-eq))
                  (long-eq (jbinop-eq))
                  (int-neq (jbinop-ne))
                  (long-neq (jbinop-ne))
                  (int-less (jbinop-lt))
                  (long-less (jbinop-lt))
                  (int-lesseq (jbinop-le))
                  (long-lesseq (jbinop-le))
                  (int-great (jbinop-gt))
                  (long-great (jbinop-gt))
                  (int-greateq (jbinop-ge))
                  (long-greateq (jbinop-ge))
                  (int-int-shiftl (jbinop-shl))
                  (long-long-shiftl (jbinop-shl))
                  (long-int-shiftl (jbinop-shl))
                  (int-long-shiftl (jbinop-shl))
                  (int-int-shiftr (jbinop-sshr))
                  (long-long-shiftr (jbinop-sshr))
                  (long-int-shiftr (jbinop-sshr))
                  (int-long-shiftr (jbinop-sshr))
                  (int-int-ushiftr (jbinop-ushr))
                  (long-long-ushiftr (jbinop-ushr))
                  (long-int-ushiftr (jbinop-ushr))
                  (int-long-ushiftr (jbinop-ushr))))
         (expr (jexpr-binary binop left-expr right-expr))
         (block (append left-block right-block)))
      (mv block
          (atj-adapt-expr-to-type
           expr src-type dst-type pkg-class-names curr-pkg)
          jvar-result-index))
    ;; 2nd component is non-0
    ;; so that each call of ATJ-GEN-SHALLOW-TERM decreases
    ;; even when the ACL2-COUNT of the other addend is 0:
    :measure (two-nats-measure (+ (acl2-count left)
                                  (acl2-count right))
                               1))

  (define atj-gen-shallow-fnapp ((fn pseudo-termfnp)
                                 (args pseudo-term-listp)
                                 (src-type atj-typep)
                                 (dst-type atj-typep)
                                 (jvar-result-base stringp)
                                 (jvar-result-index posp)
                                 (pkg-class-names string-string-alistp)
                                 (fn-method-names symbol-string-alistp)
                                 (curr-pkg stringp)
                                 (qpairs cons-pos-alistp)
                                 (guards$ booleanp)
                                 (wrld plist-worldp))
    :guard (and (not (equal curr-pkg ""))
                (or (not (pseudo-lambdap fn))
                    (equal (len (lambda-formals fn))
                           (len args))))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-result-index posp :hyp (posp jvar-result-index)))
    :parents (atj-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded ACL2 function application."
    :long
    (xdoc::topstring
     (xdoc::topstring
      "Terms of the form @('(if a a b)') are treated as @('(or a b)'),
       via a separate function, non-strictly.
       Other @(tsee if) calls are handled via a separate function,
       also non-strictly.
       We only pass one of @('src-type') or @('dst-type')
       to this separate function,
       because those two types are always equal for @(tsee if):
       see @(tsee atj-type-annotate-term).")
     (xdoc::p
      "If @(':guards') is @('t'),
       calls of ACL2 functions that model
       Java primitive constructors and operations
       are handled via separate functions.")
     (xdoc::p
      "In all other cases, in which the call is always strict,
       we first generate Java code to compute all the actual arguments.
       Calls of lambda expression are handled by a separate function.
       If the function is a named one,
       we generate a call of the method that corresponds to the ACL2 function,
       and we wrap that into a Java conversion if needed.
       (We treat the Java abstract syntax somewhat improperly here,
       by using a generic method call with a possibly qualified method name,
       which should be therefore a static method call;
       this still produces correct Java code,
       but it should be handled more properly
       in a future version of this implementation.)
       Note that, because of the type annotations of the ACL2 terms,
       the actual argument expressions will have types
       appropriate to the method's formal argument types."))
    (b* (((when (and (eq fn 'if)
                     (int= (len args) 3))) ; should be always true
          (b* ((first (first args))
               (second (second args))
               (athird (third args)))
            (if (equal first second)
                (atj-gen-shallow-orapp first
                                       athird
                                       dst-type ; = SRC-TYPE
                                       jvar-result-base
                                       jvar-result-index
                                       pkg-class-names
                                       fn-method-names
                                       curr-pkg
                                       qpairs
                                       guards$
                                       wrld)
              (atj-gen-shallow-ifapp first
                                     second
                                     athird
                                     dst-type ; = SRC-TYPE
                                     jvar-result-base
                                     jvar-result-index
                                     pkg-class-names
                                     fn-method-names
                                     curr-pkg
                                     qpairs
                                     guards$
                                     wrld))))
         ((when (and guards$
                     (member-eq fn *atj-primitive-constructors*)
                     (int= (len args) 1))) ; should be always true
          (atj-gen-shallow-primconstrapp fn
                                         (car args)
                                         src-type
                                         dst-type
                                         jvar-result-base
                                         jvar-result-index
                                         pkg-class-names
                                         fn-method-names
                                         curr-pkg
                                         qpairs
                                         wrld))
         ((when (and guards$
                     (member-eq fn *atj-primitive-unops*)
                     (int= (len args) 1))) ; should be always true
          (atj-gen-shallow-primunapp fn
                                     (car args)
                                     src-type
                                     dst-type
                                     jvar-result-base
                                     jvar-result-index
                                     pkg-class-names
                                     fn-method-names
                                     curr-pkg
                                     qpairs
                                     wrld))
         ((when (and guards$
                     (member-eq fn *atj-primitive-binops*)
                     (int= (len args) 2))) ; should be always true
          (atj-gen-shallow-primbinapp fn
                                      (first args)
                                      (second args)
                                      src-type
                                      dst-type
                                      jvar-result-base
                                      jvar-result-index
                                      pkg-class-names
                                      fn-method-names
                                      curr-pkg
                                      qpairs
                                      wrld))
         ((mv arg-blocks
              arg-exprs
              jvar-result-index) (atj-gen-shallow-terms args
                                                        jvar-result-base
                                                        jvar-result-index
                                                        pkg-class-names
                                                        fn-method-names
                                                        curr-pkg
                                                        qpairs
                                                        guards$
                                                        wrld))
         ((when (symbolp fn))
          (b* ((expr (jexpr-method
                      (atj-gen-shallow-fnname fn
                                              pkg-class-names
                                              fn-method-names
                                              curr-pkg)
                      arg-exprs))
               (expr (atj-adapt-expr-to-type
                      expr src-type dst-type pkg-class-names curr-pkg)))
            (mv (flatten arg-blocks)
                expr
                jvar-result-index)))
         ((mv lambda-block
              lambda-expr
              jvar-result-index) (atj-gen-shallow-lambda (lambda-formals fn)
                                                         (lambda-body fn)
                                                         arg-blocks
                                                         arg-exprs
                                                         src-type
                                                         dst-type
                                                         jvar-result-base
                                                         jvar-result-index
                                                         pkg-class-names
                                                         fn-method-names
                                                         curr-pkg
                                                         qpairs
                                                         guards$
                                                         wrld)))
      (mv lambda-block
          lambda-expr
          jvar-result-index))
    ;; 2nd component is greater than the one of ATJ-GEN-SHALLOW-LAMBDA
    ;; so that the call of ATJ-GEN-SHALLOW-LAMBDA decreases
    ;; even when FN is a non-symbol atom (impossible under the guard),
    ;; and it is non-0
    ;; so that the call of ATJ-GEN-SHALLOW-TERMS decreases
    ;; even when the ACL2-COUNT of FN is 0:
    :measure (two-nats-measure (+ (acl2-count fn)
                                  (acl2-count args))
                               2))

  (define atj-gen-shallow-lambda ((formals symbol-listp)
                                  (body pseudo-termp)
                                  (arg-blocks jblock-listp)
                                  (arg-exprs jexpr-listp)
                                  (src-type atj-typep)
                                  (dst-type atj-typep)
                                  (jvar-result-base stringp)
                                  (jvar-result-index posp)
                                  (pkg-class-names string-string-alistp)
                                  (fn-method-names symbol-string-alistp)
                                  (curr-pkg stringp)
                                  (qpairs cons-pos-alistp)
                                  (guards$ booleanp)
                                  (wrld plist-worldp))
    :guard (and (int= (len arg-blocks) (len formals))
                (int= (len arg-exprs) (len formals))
                (not (equal curr-pkg "")))
    :returns (mv (block jblockp :hyp (jblock-listp arg-blocks))
                 (expr jexprp)
                 (new-jvar-result-index posp :hyp (posp jvar-result-index)))
    :parents (atj-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded ACL2 lambda expression,
            applied to given Java expressions as arguments."
    :long
    (xdoc::topstring
     (xdoc::p
      "We generate @(tsee let) bindings for the formal parameters.
       Then we generate Java code for the body of the lambda expression."))
    (b* ((let-block (atj-gen-shallow-let-bindings formals
                                                  arg-blocks
                                                  arg-exprs))
         ((mv body-block
              body-expr
              jvar-result-index) (atj-gen-shallow-term body
                                                       jvar-result-base
                                                       jvar-result-index
                                                       pkg-class-names
                                                       fn-method-names
                                                       curr-pkg
                                                       qpairs
                                                       guards$
                                                       wrld)))
      (mv (append let-block body-block)
          (atj-adapt-expr-to-type
           body-expr src-type dst-type pkg-class-names curr-pkg)
          jvar-result-index))
    ;; 2nd component is non-0
    ;; so that the call of ATJ-GEN-SHALLOW-TERM decreases:
    :measure (two-nats-measure (acl2-count body) 1))

  (define atj-gen-shallow-term ((term pseudo-termp)
                                (jvar-result-base stringp)
                                (jvar-result-index posp)
                                (pkg-class-names string-string-alistp)
                                (fn-method-names symbol-string-alistp)
                                (curr-pkg stringp)
                                (qpairs cons-pos-alistp)
                                (guards$ booleanp)
                                (wrld plist-worldp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (block jblockp)
                 (expr jexprp)
                 (new-jvar-result-index posp :hyp (posp jvar-result-index)))
    :parents (atj-code-generation atj-gen-shallow-term-fns)
    :short "Generate a shallowly embedded ACL2 term."
    :long
    (xdoc::topstring
     (xdoc::p
      "Prior to calling this function,
       the term has been type-annotated via @(tsee atj-type-annotate-term).
       Thus, we first unwrap it and decompose its wrapper.")
     (xdoc::p
      "Prior to calling this function,
       the ACL2 variables have been renamed, via @(tsee atj-rename-term),
       so that they have the right names as Java variables.
       Thus, if the ACL2 term is a variable,
       we remove its type annotation
       and generate a Java variable with the same name.
       Then we wrap it with a Java conversion, if needed.")
     (xdoc::p
      "If the ACL2 term is a quoted constant,
       we represent it as its value.
       We wrap the resulting expression with a Java conversion, if needed."))
    (b* (((mv term src-type dst-type) (atj-type-unwrap-term term))
         ((unless term) ; for termination proof
          (mv nil (jexpr-name "dummy") jvar-result-index))
         ((when (variablep term))
          (b* (((mv var &) (atj-unmark-var term))
               ((mv var &) (atj-type-unannotate-var var))
               (expr (jexpr-name (symbol-name var)))
               (expr (atj-adapt-expr-to-type
                      expr src-type dst-type pkg-class-names curr-pkg)))
            (mv nil expr jvar-result-index)))
         ((when (fquotep term))
          (b* ((value (unquote-term term))
               (expr (atj-gen-shallow-value value
                                            qpairs
                                            pkg-class-names
                                            curr-pkg))
               (expr (atj-adapt-expr-to-type
                      expr src-type dst-type pkg-class-names curr-pkg)))
            (mv nil expr jvar-result-index))))
      (atj-gen-shallow-fnapp (ffn-symb term)
                             (fargs term)
                             src-type
                             dst-type
                             jvar-result-base
                             jvar-result-index
                             pkg-class-names
                             fn-method-names
                             curr-pkg
                             qpairs
                             guards$
                             wrld))
    :measure (two-nats-measure (acl2-count term) 0))

  (define atj-gen-shallow-terms ((terms pseudo-term-listp)
                                 (jvar-result-base stringp)
                                 (jvar-result-index posp)
                                 (pkg-class-names string-string-alistp)
                                 (fn-method-names symbol-string-alistp)
                                 (curr-pkg stringp)
                                 (qpairs cons-pos-alistp)
                                 (guards$ booleanp)
                                 (wrld plist-worldp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (blocks (and (jblock-listp blocks)
                              (equal (len blocks) (len terms))))
                 (exprs (and (jexpr-listp exprs)
                             (equal (len exprs) (len terms))))
                 (new-jvar-result-index posp :hyp (posp jvar-result-index)))
    :parents (atj-code-generation atj-gen-shallow-term-fns)
    :short "Lift @(tsee atj-gen-shallow-term) to lists."
    (if (endp terms)
        (mv nil nil jvar-result-index)
      (b* (((mv first-block
                first-expr
                jvar-result-index) (atj-gen-shallow-term (car terms)
                                                         jvar-result-base
                                                         jvar-result-index
                                                         pkg-class-names
                                                         fn-method-names
                                                         curr-pkg
                                                         qpairs
                                                         guards$
                                                         wrld))
           ((mv rest-blocks
                rest-exprs
                jvar-result-index) (atj-gen-shallow-terms (cdr terms)
                                                          jvar-result-base
                                                          jvar-result-index
                                                          pkg-class-names
                                                          fn-method-names
                                                          curr-pkg
                                                          qpairs
                                                          guards$
                                                          wrld)))
        (mv (cons first-block rest-blocks)
            (cons first-expr rest-exprs)
            jvar-result-index)))
    :measure (two-nats-measure (acl2-count terms) 0))

  :verify-guards nil ; done below
  ///
  (verify-guards atj-gen-shallow-term
    :hints (("Goal" :in-theory (enable atj-type-unwrap-term
                                       unquote-term
                                       pseudo-termfnp
                                       pseudo-lambdap)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fnnative-method ((fn symbolp)
                                         (fn-type atj-function-type-p)
                                         (method-name stringp)
                                         (method-param-names string-listp)
                                         (method-body jblockp))
  :guard (aij-nativep fn)
  :returns (method jmethodp)
  :short "Generate a Java method with the given types
          for an ACL2 function that is natively implemented in AIJ."
  :long
  (xdoc::topstring
   (xdoc::p
    "AIJ's @('Acl2NativeFunction') class provides native Java implementations
     of certain ACL2 functions, as public static Java methods.
     Thus, in the shallow embedding approach,
     we could translate references to these ACL2 functions
     to the names of those public static Java methods.
     However, for greater uniformity and readability,
     we generate wrapper Java methods
     for these natively implemented ACL2 functions.
     The names of these methods are constructed in the same way as
     the Java methods for the non-natively implemented ACL2 functions.
     These methods reside in the Java classes generated for
     the ACL2 packages of the ACL2 functions.")
   (xdoc::p
    "For each of these natively implemented ACL2 functions,
     @('Acl2NativeFunction') has a corresponding Java method
     that takes @('Acl2Value') objects as arguments.
     For some of these functions,
     @('Acl2NativeFunction') also has overloaded Java methods
     that take argument objects of narrower types
     that correspond to the primary and (if present) secondary ATJ types
     associated to the ACL2 function via the macros
     @(tsee def-atj-main-function-type) and
     @(tsee def-atj-other-function-type).")
   (xdoc::p
    "We generate a wrapper method for each such overloaded method:
     the argument and return types of the wrapper method
     are the same as the ones of the wrapped method in @('Acl2NativeFunction').
     This function generates one of these methods,
     as determined by the function type supplied as input.
     The types are the only thing that varies across the wrapper methods:
     their names, bodies, and other attributes are all the same;
     thus, these are calculated once and passed as inputs to this function.
     Note that the bodies of the wrapper methods automatically call
     different methods in @('Acl2NativeFunction') based on the types;
     the called methods are resolved by the Java compiler."))
  (b* ((in-types (atj-function-type->inputs fn-type))
       (out-type (atj-function-type->output fn-type))
       ((unless (= (len in-types) (len method-param-names)))
        (raise "Internal error: ~
                the number ~x0 of input types for ~x1 ~
                differs from the number ~x2 of calculated method arguments."
               (len in-types) fn (len method-param-names))
        (ec-call (jmethod-fix :this-is-irrelevant))))
    (make-jmethod :access (jaccess-public)
                  :abstract? nil
                  :static? t
                  :final? nil
                  :synchronized? nil
                  :native? nil
                  :strictfp? nil
                  :result (jresult-type (atj-type-to-jtype out-type))
                  :name method-name
                  :params (atj-gen-paramlist
                           method-param-names
                           (atj-type-list-to-jtype-list in-types))
                  :throws (list *aij-class-undef-pkg-exc*)
                  :body method-body)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fnnative-methods ((fn symbolp)
                                          (fn-types atj-function-type-listp)
                                          (method-name stringp)
                                          (method-param-names string-listp)
                                          (method-body jblockp))
  :guard (aij-nativep fn)
  :returns (methods jmethod-listp)
  :short "Lift @(tsee atj-gen-shallow-fnnative-method)
          to lists of function types."
  (cond ((endp fn-types) nil)
        (t (cons (atj-gen-shallow-fnnative-method fn
                                                  (car fn-types)
                                                  method-name
                                                  method-param-names
                                                  method-body)
                 (atj-gen-shallow-fnnative-methods fn
                                                   (cdr fn-types)
                                                   method-name
                                                   method-param-names
                                                   method-body)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fnnative-all-methods
  ((fn symbolp)
   (pkg-class-names string-string-alistp)
   (fn-method-names symbol-string-alistp)
   (guards$ booleanp)
   (verbose$ booleanp)
   (wrld plist-worldp))
  :guard (aij-nativep fn)
  :returns (methods jmethod-listp)
  :short "Generate all the overloaded Java methods
          for an ACL2 function that is natively implemented in AIJ."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee atj-gen-shallow-fnnative-method) first.
     Here we calculate, once, the data to pass to that function
     (via @(tsee atj-gen-shallow-fnnative-methods)).")
   (xdoc::p
    "We retrieve all the primary and secondary function types of @('fn'),
     and generate an overloaded method for each.
     Note that if @('guards$') is @('nil'),
     then the retrieved function types boil down to one
     that consists of all @(':value') types."))
  (b* ((curr-pkg (symbol-package-name fn))
       (method-name (atj-gen-shallow-fnname fn
                                            pkg-class-names
                                            fn-method-names
                                            curr-pkg))
       ((run-when verbose$)
        (cw "  ~s0 for ~x1~%" method-name fn))
       (method-param-names
        (case fn
          (intern-in-package-of-symbol (list "str" "sym"))
          (if (list "x" "y" "z"))
          ((pkg-imports
            pkg-witness) (list "pkg"))
          ((coerce
            binary-+
            binary-*
            <
            complex
            cons
            equal
            bad-atom<=) (list "x" "y"))
          (t (list "x"))))
       (fn-info (atj-get-function-type-info fn guards$ wrld))
       (main-fn-type (atj-function-type-info->main fn-info))
       (other-fn-types (atj-function-type-info->others fn-info))
       (all-fn-types (cons main-fn-type other-fn-types))
       (jcall-method-name
        (case fn
          (characterp "execCharacterp")
          (stringp "execStringp")
          (symbolp "execSymbolp")
          (integerp "execIntegerp")
          (rationalp "execRationalp")
          (complex-rationalp "execComplexRationalp")
          (acl2-numberp "execAcl2Numberp")
          (consp "execConsp")
          (char-code "execCharCode")
          (code-char "execCodeChar")
          (coerce "execCoerce")
          (intern-in-package-of-symbol "execInternInPackageOfSymbol")
          (symbol-package-name "execSymbolPackageName")
          (symbol-name "execSymbolName")
          (pkg-imports "execPkgImports")
          (pkg-witness "execPkgWitness")
          (unary-- "execUnaryMinus")
          (unary-/ "execUnarySlash")
          (binary-+ "execBinaryPlus")
          (binary-* "execBinaryStar")
          (< "execLessThan")
          (complex "execComplex")
          (realpart "execRealPart")
          (imagpart "execImagPart")
          (numerator "execNumerator")
          (denominator "execDenominator")
          (cons "execCons")
          (car "execCar")
          (cdr "execCdr")
          (equal "execEqual")
          (bad-atom<= "execBadAtomLessThanOrEqualTo")
          (if "execIf")
          (t (impossible))))
       (jcall-arg-exprs (jexpr-name-list method-param-names))
       (jcall (jexpr-smethod *aij-type-native-fn*
                             jcall-method-name
                             jcall-arg-exprs))
       (method-body (jblock-return jcall)))
    (atj-gen-shallow-fnnative-methods fn
                                      all-fn-types
                                      method-name
                                      method-param-names
                                      method-body))
  :guard-hints (("Goal" :in-theory (enable aij-nativep primitivep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fndef-method ((fn symbolp)
                                      (fn-type atj-function-type-p)
                                      (formals symbol-listp)
                                      (body pseudo-termp)
                                      (method-name stringp)
                                      (qconsts atj-qconstants-p)
                                      (pkg-class-names string-string-alistp)
                                      (fn-method-names symbol-string-alistp)
                                      (curr-pkg stringp)
                                      (guards$ booleanp)
                                      (wrld plist-worldp))
  :guard (and (not (aij-nativep fn))
              (not (equal curr-pkg "")))
  :returns (mv (method jmethodp)
               (new-qconsts atj-qconstants-p :hyp (atj-qconstants-p qconsts)))
  :short "Generate a Java method with the given types
          for an ACL2 function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     each ACL2 function definition is turned into a Java method.
     This is a public static method
     with the same number of parameters as the ACL2 function.
     More precisely, we generate an overloaded method
     for each primary and secondary function type associated to the function
     via @(tsee def-atj-main-function-type)
     and @(tsee def-atj-other-function-type).")
   (xdoc::p
    "This function generates one such method,
     based on the (primary or secondary) function type passed as input.
     First, we pre-translate the function.
     Then, we translate the pre-translated function to a Java method.
     Finally, we post-translate the Java method.")
   (xdoc::p
    "We also collect all the quoted constants
     in the pre-translated function body,
     and add it to the collection that it threaded through.")
   (xdoc::p
    "The formals and body of the function, as well as the method name,
     are the same for all the overloaded methods,
     so they are calculated once and passed to this function.
     However, the generation of the Java method
     (pre-translation, translation, and post-translation)
     must be done afresh for each overloaded methods,
     because it is affected by the function types,
     which are turned into the method's argument and result types:
     with different types,
     there may be different type annotations,
     and in particular different type conversions.
     In fact, it is expected that, with narrower types,
     there will be fewer type conversions.
     The pre-translation steps before the type annotation step
     could be actually factored out and done once,
     but for greater implementation simplicity here we repeat them
     for every overloaded method."))
  (b* ((in-types (atj-function-type->inputs fn-type))
       (out-type (atj-function-type->output fn-type))
       ((unless (= (len in-types) (len formals)))
        (raise "Internal error: ~
                the number ~x0 of parameters of ~x1 ~
                does not match the number ~x2 of input types of ~x1."
               (len formals) fn (len in-types))
        (mv (ec-call (jmethod-fix :this-is-irrelevant)) qconsts))
       ((mv formals body)
        (atj-pre-translate fn formals body in-types out-type nil guards$ wrld))
       (qconsts (atj-add-qconstants-in-term body qconsts))
       ((mv formals &) (atj-unmark-vars formals))
       ((mv formals &) (atj-type-unannotate-vars formals))
       (method-params (atj-gen-paramlist
                       (symbol-name-lst formals)
                       (atj-type-list-to-jtype-list in-types)))
       ((mv body-block body-expr &)
        (atj-gen-shallow-term body
                              "$result" 1
                              pkg-class-names
                              fn-method-names
                              curr-pkg
                              (atj-qconstants->pairs qconsts)
                              guards$
                              wrld))
       (method-body (append body-block
                            (jblock-return body-expr)))
       (tailrecp (and (logicp fn wrld)
                      (= 1 (len (irecursivep fn wrld)))
                      (tail-recursive-p fn wrld)))
       (method-body (atj-post-translate method-name
                                        method-params
                                        method-body
                                        tailrecp))
       (method (make-jmethod :access (jaccess-public)
                             :abstract? nil
                             :static? t
                             :final? nil
                             :synchronized? nil
                             :native? nil
                             :strictfp? nil
                             :result (jresult-type (atj-type-to-jtype out-type))
                             :name method-name
                             :params method-params
                             :throws (list *aij-class-undef-pkg-exc*)
                             :body method-body)))
    (mv method qconsts)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fndef-methods ((fn symbolp)
                                       (fn-types atj-function-type-listp)
                                       (formals symbol-listp)
                                       (body pseudo-termp)
                                       (method-name stringp)
                                       (qconsts atj-qconstants-p)
                                       (pkg-class-names string-string-alistp)
                                       (fn-method-names symbol-string-alistp)
                                       (curr-pkg stringp)
                                       (guards$ booleanp)
                                       (wrld plist-worldp))
  :guard (and (not (aij-nativep fn))
              (not (equal curr-pkg "")))
  :returns (mv (methods jmethod-listp)
               (new-qconsts atj-qconstants-p :hyp (atj-qconstants-p qconsts)))
  :short "Lift @(tsee atj-gen-shallow-fndef-method) to lists of function types."
  (b* (((when (endp fn-types)) (mv nil qconsts))
       ((mv first-methods
            qconsts) (atj-gen-shallow-fndef-method fn
                                                   (car fn-types)
                                                   formals
                                                   body
                                                   method-name
                                                   qconsts
                                                   pkg-class-names
                                                   fn-method-names
                                                   curr-pkg
                                                   guards$
                                                   wrld))
       ((mv rest-methods
            qconsts) (atj-gen-shallow-fndef-methods fn
                                                    (cdr fn-types)
                                                    formals
                                                    body
                                                    method-name
                                                    qconsts
                                                    pkg-class-names
                                                    fn-method-names
                                                    curr-pkg
                                                    guards$
                                                    wrld)))
    (mv (cons first-methods rest-methods) qconsts)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fndef-all-methods
  ((fn symbolp)
   (qconsts atj-qconstants-p)
   (pkg-class-names string-string-alistp)
   (fn-method-names symbol-string-alistp)
   (guards$ booleanp)
   (verbose$ booleanp)
   (wrld plist-worldp))
  :guard (not (aij-nativep fn))
  :returns (mv (methods jmethod-listp)
               (new-qconsts atj-qconstants-p :hyp (atj-qconstants-p qconsts)))
  :short "Generate all the overloaded Java methods
          for an ACL2 function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee atj-gen-shallow-fndef-method) first.
     Here we calculate, once, the data to pass to that function
     (via @(tsee atj-gen-shallow-fndef-methods)).")
   (xdoc::p
    "We retrieve all the primary and secondary function types of @('fn'),
     and generate an overloaded method for each.
     Note that if @('guards$') is @('nil'),
     then the retrieved function types boil down to one
     that consists of all @(':value') types."))
  (b* ((curr-pkg (symbol-package-name fn))
       (formals (formals+ fn wrld))
       (body (ubody+ fn wrld))
       ((run-when (null body))
        (raise "Internal error: ~
                the function ~x0 has no unnormalized body."
               fn))
       (fn-info (atj-get-function-type-info fn guards$ wrld))
       (main-fn-type (atj-function-type-info->main fn-info))
       (other-fn-types (atj-function-type-info->others fn-info))
       (all-fn-types (cons main-fn-type other-fn-types))
       (method-name (atj-gen-shallow-fnname fn
                                            pkg-class-names
                                            fn-method-names
                                            curr-pkg))
       ((run-when verbose$)
        (cw "  ~s0 for ~x1~%" method-name fn)))
    (atj-gen-shallow-fndef-methods fn
                                   all-fn-types
                                   formals
                                   body
                                   method-name
                                   qconsts
                                   pkg-class-names
                                   fn-method-names
                                   curr-pkg
                                   guards$
                                   wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-fn-methods ((fn symbolp)
                                    (qconsts atj-qconstants-p)
                                    (pkg-class-names string-string-alistp)
                                    (fn-method-names symbol-string-alistp)
                                    (guards$ booleanp)
                                    (verbose$ booleanp)
                                    (wrld plist-worldp))
  :returns (mv (methods jmethod-listp)
               (new-qconsts atj-qconstants-p :hyp (atj-qconstants-p qconsts)))
  :short "Generate all the overloaded Java methods
          for an ACL2 function natively implemented in AIJ
          or for an ACL2 function definition."
  :long
  (xdoc::topstring-p
   "We also add all the quoted constants to the collection.
    The collection does not change for native functions.")
  (if (aij-nativep fn)
      (mv (atj-gen-shallow-fnnative-all-methods fn
                                                pkg-class-names
                                                fn-method-names
                                                guards$
                                                verbose$
                                                wrld)
          qconsts)
    (atj-gen-shallow-fndef-all-methods fn
                                       qconsts
                                       pkg-class-names
                                       fn-method-names
                                       guards$
                                       verbose$
                                       wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-all-fn-methods ((fns symbol-listp)
                                        (qconsts atj-qconstants-p)
                                        (pkg-class-names string-string-alistp)
                                        (fn-method-names symbol-string-alistp)
                                        (guards$ booleanp)
                                        (verbose$ booleanp)
                                        (wrld plist-worldp))
  :returns (mv (methods jmethod-listp)
               (new-qconsts atj-qconstants-p :hyp (atj-qconstants-p qconsts)))
  :short "Lift @(tsee atj-gen-shallow-fn-methods) to lists of functions."
  (b* (((when (endp fns)) (mv nil qconsts))
       ((mv first-methods
            qconsts) (atj-gen-shallow-fn-methods (car fns)
                                                 qconsts
                                                 pkg-class-names
                                                 fn-method-names
                                                 guards$
                                                 verbose$
                                                 wrld))
       ((mv rest-methods
            qconsts) (atj-gen-shallow-all-fn-methods (cdr fns)
                                                     qconsts
                                                     pkg-class-names
                                                     fn-method-names
                                                     guards$
                                                     verbose$
                                                     wrld)))
    (mv (append first-methods rest-methods) qconsts)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-synonym-method-params ((n natp))
  :returns (formals string-listp)
  :short "Generate shallowly embedded formal parameters for
          the function synonyms generated by
          @(tsee atj-gen-shallow-synonym-method)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The exact formal parameters are not important,
     so for now we just generate @('x1'), @('x2'), ..., @('xn'),
     where @('n') is the arity.
     These are valid Java parameter names."))
  (atj-gen-shallow-synonym-method-params-aux n nil)

  :prepwork
  ((define atj-gen-shallow-synonym-method-params-aux ((n natp)
                                                      (acc string-listp))
     :returns (formals string-listp :hyp (string-listp acc))
     (cond ((zp n) acc)
           (t (atj-gen-shallow-synonym-method-params-aux
               (1- n) (cons (str::cat "x" (str::natstr n)) acc)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-synonym-method ((fn symbolp)
                                        (fn-type atj-function-type-p)
                                        (pkg-class-names string-string-alistp)
                                        (fn-method-names symbol-string-alistp)
                                        (wrld plist-worldp))
  :returns (method jmethodp)
  :short "Generate a Java method with the given types
          for an ACL2 function synonym."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to mimic, as far as name references are concerned,
     the importing of a function symbol in a package.")
   (xdoc::p
    "For instance,
     the built-in @(tsee cons) is in the @('\"COMMON-LISP\"') package
     (i.e. that is its @(tsee symbol-package-name)),
     but that symbol is imported by the @('\"ACL2\"') package,
     making it referenceable as @('acl2::cons')
     besides the ``canonical'' @('common-lisp::cons').
     In particular, in the @('\"ACL2\"') package
     it can be referenced as just @('cons'),
     which makes ACL2 code much more readable.")
   (xdoc::p
    "In the shallow embedding,
     we translate these two ACL2 packages to two different Java classes,
     and the method that corresponds to @(tsee cons)
     is declared in the class for @('\"COMMON-LISP\"'),
     where the method can be referenced by simple name,
     without qualifying it with the class name.
     But in classes for other packages, e.g. the class for @('\"ACL2\"'),
     it would have to be qualified.")
   (xdoc::p
    "To avoid this verbosity,
     we generate a ``synonym'' of the method for @(tsee cons)
     in each class of a package that imports @(tsee cons),
     e.g. in the class for @('\"ACL2\"').
     This function generates this synonym method,
     which is just defined to call the method
     in the class of its proper package.
     This makes the generated Java code much more readable.
     It is hoped that the JVM JIT may optimize the indirection away.")
   (xdoc::p
    "The @('fn') parameter is the name of the ACL2 function in question,
     e.g. @(tsee cons) in the example above.")
   (xdoc::p
    "We pass the @(tsee symbol-package-name) of @('fn')
     to @(tsee atj-gen-shallow-fnname)
     to ensure that the result is the simple name of the method,
     which goes into the generated method declaration.")
   (xdoc::p
    "Recall that, for each ACL2 function,
     we generate as many overloaded Java methods
     as the number of primary and secondary types of the function.
     Accordingly, we must generate
     the same number of overloaded methods for the function synonyms.
     This function generates the overloaded method
     for the function type passed as argument."))
  (b* ((in-types (atj-function-type->inputs fn-type))
       (out-type (atj-function-type->output fn-type))
       (fn-pkg (symbol-package-name fn))
       (method-name (atj-gen-shallow-fnname fn
                                            pkg-class-names
                                            fn-method-names
                                            fn-pkg))
       (method-param-names (atj-gen-shallow-synonym-method-params
                            (arity+ fn wrld)))
       ((unless (= (len method-param-names) (len in-types)))
        (raise "Internal error: ~
                the number ~x0 of input types of ~x1 ~
                differs from the arity ~x2 of ~x1."
               (len in-types) fn (len method-param-names))
        (ec-call (jmethod-fix :this-is-irrelevant)))
       (method-params (atj-gen-paramlist
                       method-param-names
                       (atj-type-list-to-jtype-list in-types)))
       (class (atj-get-pkg-class-name fn-pkg pkg-class-names))
       (method-body (jblock-return
                     (jexpr-smethod (jtype-class class)
                                    method-name
                                    (jexpr-name-list method-param-names)))))
    (make-jmethod :access (jaccess-public)
                  :abstract? nil
                  :static? t
                  :final? nil
                  :synchronized? nil
                  :native? nil
                  :strictfp? nil
                  :result (jresult-type (atj-type-to-jtype out-type))
                  :name method-name
                  :params method-params
                  :throws (list *aij-class-undef-pkg-exc*)
                  :body method-body)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-synonym-methods ((fn symbolp)
                                         (fn-types atj-function-type-listp)
                                         (pkg-class-names string-string-alistp)
                                         (fn-method-names symbol-string-alistp)
                                         (wrld plist-worldp))
  :returns (methods jmethod-listp)
  :short "Lift @(tsee atj-gen-shallow-synonym-method)
          to lists of function types."
  (cond ((endp fn-types) nil)
        (t (cons (atj-gen-shallow-synonym-method fn
                                                 (car fn-types)
                                                 pkg-class-names
                                                 fn-method-names
                                                 wrld)
                 (atj-gen-shallow-synonym-methods fn
                                                  (cdr fn-types)
                                                  pkg-class-names
                                                  fn-method-names
                                                  wrld)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-synonym-all-methods
  ((fn symbolp)
   (pkg-class-names string-string-alistp)
   (fn-method-names symbol-string-alistp)
   (guards$ booleanp)
   (wrld plist-worldp))
  :returns (methods jmethod-listp)
  :short "Generate all the overloaded Java methods
          for an ACL2 function synonym."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee atj-gen-shallow-synonym-method) first.")
   (xdoc::p
    "We retrieve all the primary and secondary function types of @('fn'),
     and generate an overloaded method for each.
     Note that if @('guards$') is @('nil'),
     then the retrieved function types boil down to one
     that consists of all @(':value') types."))
  (b* ((fn-info (atj-get-function-type-info fn guards$ wrld))
       (main-fn-type (atj-function-type-info->main fn-info))
       (other-fn-types (atj-function-type-info->others fn-info))
       (all-fn-types (cons main-fn-type other-fn-types)))
    (atj-gen-shallow-synonym-methods fn
                                     all-fn-types
                                     pkg-class-names
                                     fn-method-names
                                     wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-all-synonym-methods
  ((fns symbol-listp)
   (pkg-class-names string-string-alistp)
   (fn-method-names symbol-string-alistp)
   (guards$ booleanp)
   (wrld plist-worldp))
  :returns (methods jmethod-listp)
  :short "Lift @(tsee atj-gen-shallow-synonym-all-methods)
          to lists of functions."
  (cond ((endp fns) nil)
        (t (append (atj-gen-shallow-synonym-all-methods (car fns)
                                                        pkg-class-names
                                                        fn-method-names
                                                        guards$
                                                        wrld)
                   (atj-gen-shallow-all-synonym-methods (cdr fns)
                                                        pkg-class-names
                                                        fn-method-names
                                                        guards$
                                                        wrld)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-pkg-methods ((pkg stringp)
                                     (fns-by-pkg string-symbollist-alistp)
                                     (fns+natives symbol-listp)
                                     (qconsts atj-qconstants-p)
                                     (pkg-class-names string-string-alistp)
                                     (fn-method-names symbol-string-alistp)
                                     (guards$ booleanp)
                                     (verbose$ booleanp)
                                     (wrld plist-worldp))
  :returns (mv (methods jmethod-listp)
               (new-qconsts atj-qconstants-p :hyp (atj-qconstants-p qconsts)))
  :short "Generate all the methods of the class for an ACL2 package."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate methods for the functions in @('fns-by-pkg')
     (i.e. the functions to translate to Java, including natives,
     organized by package)
     that are associated to @('pkg').")
   (xdoc::p
    "We also generate synonym methods for all the functions in @('fns+native')
     (i.e. the functions to translate to Java, including natives)
     that are in other ACL2 packages but that are imported by @('pkg');
     see @(tsee atj-gen-shallow-synonym-method) for motivation.")
   (xdoc::p
    "Recall that, for each ACL2 function or function synonym,
     we generate one overloaded method
     for each primary or secondary type of the function.")
   (xdoc::p
    "We sort all the methods.")
   (xdoc::p
    "We also collect all the quoted constants
     that occur in the functions in @('pkg') that are translated to Java."))
  (b* ((fns (cdr (assoc-equal pkg fns-by-pkg)))
       ((run-when (and verbose$
                       (consp fns)))
        (cw "~%Generate the Java methods ~
               for the ACL2 functions in package ~s0:~%" pkg))
       ((mv fn-methods
            qconsts) (atj-gen-shallow-all-fn-methods fns
                                                     qconsts
                                                     pkg-class-names
                                                     fn-method-names
                                                     guards$
                                                     verbose$
                                                     wrld))
       (imported-fns (intersection-eq fns+natives (pkg-imports pkg)))
       (imported-fns (sort-symbol-listp imported-fns))
       (synonym-methods (atj-gen-shallow-all-synonym-methods imported-fns
                                                             pkg-class-names
                                                             fn-method-names
                                                             guards$
                                                             wrld))
       (all-methods (append synonym-methods fn-methods)))
    (mv (mergesort-jmethods all-methods)
        qconsts))
  :prepwork
  ((local (include-book "std/typed-lists/symbol-listp" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defalist string-jmethodlist-alistp (x)
  :short "Alists from package names (strings) to true lists of Java methods."
  :key (stringp x)
  :val (jmethod-listp x)
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-all-pkg-methods ((pkgs string-listp)
                                         (fns-by-pkg string-symbollist-alistp)
                                         (fns+natives symbol-listp)
                                         (qconsts atj-qconstants-p)
                                         (pkg-class-names string-string-alistp)
                                         (fn-method-names symbol-string-alistp)
                                         (guards$ booleanp)
                                         (verbose$ booleanp)
                                         (wrld plist-worldp))
  :returns (mv (methods-by-pkg string-jmethodlist-alistp
                               :hyp (string-listp pkgs))
               (new-qconsts atj-qconstants-p :hyp (atj-qconstants-p qconsts)))
  :verify-guards :after-returns
  :short "Generate all the methods of the classes for all the ACL2 packages."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through all the packages in @('pkgs')
     and construct an alist from the packages there
     to the corresponding method lists
     (i.e. the methods of the class that corresponds to the package).
     If there are no methods for a package,
     we do not add an entry for the package in the alist."))
  (b* (((when (endp pkgs)) (mv nil qconsts))
       (pkg (car pkgs))
       ((mv first-methods
            qconsts) (atj-gen-shallow-pkg-methods pkg
                                                  fns-by-pkg
                                                  fns+natives
                                                  qconsts
                                                  pkg-class-names
                                                  fn-method-names
                                                  guards$
                                                  verbose$
                                                  wrld))
       ((mv rest-methods
            qconsts) (atj-gen-shallow-all-pkg-methods (cdr pkgs)
                                                      fns-by-pkg
                                                      fns+natives
                                                      qconsts
                                                      pkg-class-names
                                                      fn-method-names
                                                      guards$
                                                      verbose$
                                                      wrld)))
    (if (null first-methods)
        (mv rest-methods qconsts)
      (mv (acons pkg first-methods rest-methods)
          qconsts))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-pkg-fields ((pkg stringp)
                                    (quoted-symbols symbol-listp)
                                    (quoted-symbols-by-pkg
                                     string-symbollist-alistp))
  :returns (fields jfield-listp)
  :short "Generate all the fields of the class for an ACL2 package."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate fields for the symbols in @('quoted-symbols-by-pkg')
     (i.e. the quoted symbols that appear in the bodies of the ACL2 functions
     that are translated to Java,
     organized by package)
     that are associated to @('pkg').
     These are all symbols whose package name is @('pkg').")
   (xdoc::p
    "We also generate fields for the symbols in @('quoted-symbols')
     (i.e. all the symbols in @('quoted-symbols-by-pkg'), in a flat list)
     that are imported by @('pkg').
     This enables the unqualified reference to them in the lass for @('pkg');
     see @(tsee atj-gen-shallow-symbol).")
   (xdoc::p
    "We sort all the fields, so that they appear in that order."))
  (b* ((syms (cdr (assoc-equal pkg quoted-symbols-by-pkg)))
       (imported-syms (intersection-eq quoted-symbols (pkg-imports pkg)))
       (all-syms (append syms imported-syms))
       (all-fields (atj-gen-shallow-symbol-fields all-syms)))
    (mergesort-jfields all-fields)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defalist string-jfieldlist-alistp (x)
  :short "Alists from package names (strings) to true lists of Java fields."
  :key (stringp x)
  :val (jfield-listp x)
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-all-pkg-fields ((pkgs string-listp)
                                        (quoted-symbols symbol-listp)
                                        (quoted-symbols-by-pkg
                                         string-symbollist-alistp))
  :returns (fields-by-pkg string-jfieldlist-alistp :hyp (string-listp pkgs))
  :verify-guards :after-returns
  :short "Generate all the fields of the class for all the ACL2 packages."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through all the packages in @('pkgs')
     and construct an alist from the packages there
     to the corresponding fields lists
     (i.e. the fields of the class that corresponds to the package).
     If there are no fields for a package,
     we do not add an entry for the package in the alist."))
  (b* (((when (endp pkgs)) nil)
       (pkg (car pkgs))
       (first-fields (atj-gen-shallow-pkg-fields pkg
                                                 quoted-symbols
                                                 quoted-symbols-by-pkg))
       (rest-fields (atj-gen-shallow-all-pkg-fields (cdr pkgs)
                                                    quoted-symbols
                                                    quoted-symbols-by-pkg)))
    (if (null first-fields)
        rest-fields
      (acons pkg first-fields rest-fields))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-pkg-class ((pkg stringp)
                                   (fields-by-pkg string-jfieldlist-alistp)
                                   (methods-by-pkg string-jmethodlist-alistp)
                                   (pkg-class-names string-string-alistp)
                                   (verbose$ booleanp))
  :returns (class jclassp)
  :short "Generate the class for an ACL2 package."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the shallow embedding approach,
     we generate a Java class for each ACL2 package.
     This is a public static Java class,
     nested into the main Java class that ATJ generates.")
   (xdoc::p
    "The fields are in the @('fields-by-pkg') alist,
     which is calculated (elsewhere)
     via @(tsee atj-gen-shallow-all-pkg-fields).")
   (xdoc::p
    "The methods are in the @('methods-by-pkg') alist,
     which is calculated (elsewhere)
     via @(tsee atj-gen-shallow-all-pkg-methods)."))
  (b* ((class-name (atj-get-pkg-class-name pkg pkg-class-names))
       ((run-when verbose$)
        (cw "  ~s0 for ~s1~%" class-name pkg))
       (fields (cdr (assoc-equal pkg fields-by-pkg)))
       (methods (cdr (assoc-equal pkg methods-by-pkg))))
    (make-jclass :access (jaccess-public)
                 :abstract? nil
                 :static? t
                 :final? nil
                 :strictfp? nil
                 :name class-name
                 :superclass? nil
                 :superinterfaces nil
                 :body (append (jfields-to-jcbody-elements fields)
                               (jmethods-to-jcbody-elements methods)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-pkg-classes ((pkgs string-listp)
                                     (fields-by-pkg string-jfieldlist-alistp)
                                     (methods-by-pkg string-jmethodlist-alistp)
                                     (pkg-class-names string-string-alistp)
                                     (verbose$ booleanp))
  :returns (classes jclass-listp)
  :short "Lift @(tsee atj-gen-shallow-pkg-class) to lists."
  :long
  (xdoc::topstring-p
   "If the class for a package has an empty body, we skip it.")
  (b* (((when (endp pkgs)) nil)
       (class (atj-gen-shallow-pkg-class (car pkgs)
                                         fields-by-pkg
                                         methods-by-pkg
                                         pkg-class-names
                                         verbose$))
       (classes (atj-gen-shallow-pkg-classes (cdr pkgs)
                                             fields-by-pkg
                                             methods-by-pkg
                                             pkg-class-names
                                             verbose$)))
    (if (null (jclass->body class))
        classes
      (cons class classes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-static-initializer ((pkgs string-listp))
  :returns (initializer jcinitializerp)
  :short "Generate the static initializer
          for the main (i.e. non-test) Java class declaration,
          in the shallow embedding approach."
  :long
  (xdoc::topstring
   (xdoc::p
    "This contains code to initialize the ACL2 environment:
     we build the Java representation of the ACL2 packages."))
  (make-jcinitializer :static? t
                      :code (atj-gen-pkgs pkgs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-main-class ((pkgs string-listp)
                                    (fns-to-translate symbol-listp)
                                    (guards$ booleanp)
                                    (java-class$ stringp)
                                    (verbose$ booleanp)
                                    (wrld plist-worldp))
  :guard (no-duplicatesp-equal pkgs)
  :returns (mv (class jclassp)
               (pkg-class-names string-string-alistp :hyp (string-listp pkgs))
               (fn-method-names symbol-string-alistp
                                :hyp (symbol-listp fns-to-translate)))
  :short "Generate the main (i.e. non-test) Java class declaration,
          in the shallow embedding approach."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a public class.
     [JLS:7.6] says that a Java implementation may require
     public classes to be in files with the same names (plus extension).
     The code that we generate satisfies this requirement.")
   (xdoc::p
    "The class contains the initialization method,
     the methods to build the ACL2 packages,
     the classes that contain methods for the ACL2 functions,
     the fields for quoted constants (only numbers and characters for now),
     and the static initializer.")
   (xdoc::p
    "It is critical that the static initializer
     comes before the fields for the quoted constants,
     so that the ACL2 environment is initialized
     before the field initializers, which construct ACL2 values,
     are executed;
     [JLS:12.4.1] says that the class initialization code
     is executed in textual order.")
   (xdoc::p
    "We ensure that the ACL2 functions natively implemented in AIJ
     (currently the ACL2 primitive functions)
     are included,
     we organize the resulting functions by packages,
     and we proceed to generate the Java nested classes,
     after the methods to build the packages.")
   (xdoc::p
    "We also return the alist from ACL2 package names to Java class names
     and the alist from ACL2 function symbols to Java method names,
     which must be eventually passed to the functions that generate
     the Java test class.")
   (xdoc::p
    "We initialize the symbols of the @(tsee atj-qconstants) structure
     with @('t') and @('nil'),
     because their Java representations are sometimes generated
     (by @(tsee atj-adapt-expr-from-jprim-to-cons))
     even when these two symbols are not used in any of the ACL2 functions
     that are translated to Java."))
  (b* (((run-when verbose$)
        (cw "~%Generate the Java methods to build the ACL2 packages:~%"))
       (pkg-methods (atj-gen-pkg-methods pkgs verbose$))
       (pkg-methods (mergesort-jmethods pkg-methods))
       (fns+natives (append fns-to-translate
                            (strip-cars *primitive-formals-and-guards*)))
       ((unless (no-duplicatesp-eq fns+natives))
        (raise "Internal error: ~
                the list ~x0 of function names has duplicates." fns+natives)
        (mv (ec-call (jclass-fix :this-is-irrelevant)) nil nil))
       (pkg-class-names (atj-pkgs-to-classes pkgs java-class$))
       (fn-method-names (atj-fns-to-methods fns+natives))
       (fns-by-pkg (organize-symbols-by-pkg fns+natives))
       (qconsts (make-atj-qconstants :integers nil
                                     :rationals nil
                                     :numbers nil
                                     :chars nil
                                     :strings nil
                                     :symbols (list t nil)
                                     :pairs nil
                                     :next-index 1))
       ((mv methods-by-pkg qconsts)
        (atj-gen-shallow-all-pkg-methods pkgs
                                         fns-by-pkg
                                         fns+natives
                                         qconsts
                                         pkg-class-names
                                         fn-method-names
                                         guards$
                                         verbose$
                                         wrld))
       ((atj-qconstants qconsts) qconsts)
       (qsymbols qconsts.symbols)
       (qsymbols-by-pkg (organize-symbols-by-pkg qsymbols))
       (fields-by-pkg (atj-gen-shallow-all-pkg-fields pkgs
                                                      qsymbols
                                                      qsymbols-by-pkg))
       ((run-when verbose$)
        (cw "~%Generate the Java classes for the ACL2 packages:~%"))
       (classes (atj-gen-shallow-pkg-classes pkgs
                                             fields-by-pkg
                                             methods-by-pkg
                                             pkg-class-names
                                             verbose$))
       ((run-when verbose$)
        (cw "~%Generate the main Java class.~%"))
       (qinteger-fields (atj-gen-shallow-number-fields qconsts.integers))
       (qrational-fields (atj-gen-shallow-number-fields qconsts.rationals))
       (qnumber-fields (atj-gen-shallow-number-fields qconsts.numbers))
       (qchar-fields (atj-gen-shallow-char-fields qconsts.chars))
       (qstring-fields (atj-gen-shallow-string-fields qconsts.strings))
       (qcons-fields (atj-gen-shallow-cons-fields (strip-cars qconsts.pairs)
                                                  qconsts.pairs))
       (all-qconst-fields (append qinteger-fields
                                  qrational-fields
                                  qnumber-fields
                                  qchar-fields
                                  qstring-fields
                                  qcons-fields))
       (all-qconst-fields (mergesort-jfields all-qconst-fields))
       (static-init (atj-gen-shallow-static-initializer pkgs))
       (init-method (atj-gen-init-method))
       (body-class (append (list (jcbody-element-init static-init))
                           (jmethods-to-jcbody-elements pkg-methods)
                           (jfields-to-jcbody-elements all-qconst-fields)
                           (jclasses-to-jcbody-elements classes)
                           (list (jcbody-element-member
                                  (jcmember-method init-method))))))
    (mv (make-jclass :access (jaccess-public)
                     :abstract? nil
                     :static? nil
                     :final? nil
                     :strictfp? nil
                     :name java-class$
                     :superclass? nil
                     :superinterfaces nil
                     :body body-class)
        pkg-class-names
        fn-method-names))

  :prepwork

  ((local (include-book "std/typed-lists/symbol-listp" :dir :system))

   (defrulel verify-guards-lemma
     (implies (cons-pos-alistp alist)
              (alistp (strip-cars alist))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-main-cunit ((guards$ booleanp)
                                    (java-package$ stringp)
                                    (java-class$ stringp)
                                    (pkgs string-listp)
                                    (fns-to-translate symbol-listp)
                                    (verbose$ booleanp)
                                    (wrld plist-worldp))
  :guard (no-duplicatesp-equal pkgs)
  :returns (mv (cunit jcunitp)
               (pkg-class-names string-string-alistp :hyp (string-listp pkgs))
               (fn-method-names symbol-string-alistp
                                :hyp (symbol-listp fns-to-translate)))
  :short "Generate the main Java compilation unit,
          in the shallow embedding approach."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the generated imports are changed,
     the constant @(tsee *atj-disallowed-class-names*)
     must be modified accordingly.")
   (xdoc::p
    "We also return the alist from ACL2 package names to Java class names
     and the alist from ACL2 function symbols to Java method names,
     which must be eventually passed to the functions that generate
     the Java test class."))
  (b* (((mv class pkg-class-names fn-method-names)
        (atj-gen-shallow-main-class
         pkgs fns-to-translate guards$ java-class$ verbose$ wrld))
       ((run-when verbose$)
        (cw "~%Generate the main Java compilation unit.~%"))
       (cunit
        (make-jcunit
         :package? java-package$
         :imports (list
                   (make-jimport :static? nil
                                 :target (str::cat *aij-package* ".*"))
                   ;; keep in sync with *ATJ-DISALLOWED-CLASS-NAMES*:
                   (make-jimport :static? nil :target "java.math.BigInteger")
                   (make-jimport :static? nil :target "java.util.ArrayList")
                   (make-jimport :static? nil :target "java.util.List"))
         :types (list class))))
    (mv cunit pkg-class-names fn-method-names)))
