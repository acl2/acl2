; Java Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "common-code-generation")

(include-book "kestrel/std/system/unquote-term" :dir :system)
(include-book "std/typed-alists/cons-pos-alistp" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-shallow-quoted-constant-generation
  :parents (atj-code-generation)
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
     e.g. see @(tsee atj-gen-shallow-number-field-name)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defaggregate atj-qconstants
  :short "Recognize a structured collection of quoted constants."
  :long
  (xdoc::topstring
   (xdoc::p
    "As we collect quoted constants for the purposes described "
    (xdoc::seetopic "atj-shallow-quoted-constant-generation" "here")
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
      (str::nat-to-dec-string integer)
    (str::cat "minus" (str::nat-to-dec-string (- integer)))))

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
                 :init? init)))

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
       (init (atj-gen-char char t nil))
       (type *aij-type-char*))
    (make-jfield :access (jaccess-private)
                 :static? t
                 :final? t
                 :transient? nil
                 :volatile? nil
                 :type type
                 :name name
                 :init? init)))

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
       (init (atj-gen-string string t nil))
       (type *aij-type-string*))
    (make-jfield :access (jaccess-private)
                 :static? t
                 :final? t
                 :transient? nil
                 :volatile? nil
                 :type type
                 :name name
                 :init? init)))

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
   "This is a package-private static final field with an initializer,
    which constructs the string value.
    Unlike the fields for other types of quoted constants,
    this one is declared in the class for the package of the symbol
    (or for a pacakge that imports the symbol).
    This field cannot be private,
    otherwise the classes for other packages could not access it.")
  (b* ((name (atj-gen-shallow-symbol-field-name symbol))
       (init (atj-gen-symbol symbol t nil))
       (type *aij-type-symbol*))
    (make-jfield :access (jaccess-default)
                 :static? t
                 :final? t
                 :transient? nil
                 :volatile? nil
                 :type type
                 :name name
                 :init? init)))

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
    (str::cat "$P_" (str::nat-to-dec-string index))))

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
                 :init? init)))

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

(define atj-gen-shallow-char ((char characterp) (guards$ booleanp))
  :returns (expr jexprp)
  :short "Generate a shallowly embedded ACL2 quoted character."
  :long
  (xdoc::topstring
   (xdoc::p
    "If guards are assumed,
     we generate the corresponding Java character literal.")
   (xdoc::p
    "Otherwise,
     we generate a reference to the field for the quoted character."))
  (if guards$
      (jexpr-literal-character char)
    (jexpr-name (atj-gen-shallow-char-field-name char))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-string ((string stringp) (guards$ booleanp))
  :returns (expr jexprp)
  :short "Generate a shallowly embedded ACL2 quoted string."
  :long
  (xdoc::topstring
   (xdoc::p
    "If guards are assumed,
     we generate the corresponding Java string expression.")
   (xdoc::p
    "Otherwise,
     we generate a reference to the field for the quoted string."))
  (if guards$
      (atj-gen-jstring string)
    (jexpr-name (atj-gen-shallow-string-field-name string))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-gen-shallow-symbol ((symbol symbolp)
                                (pkg-class-names string-string-alistp)
                                (curr-pkg stringp)
                                (guards$ booleanp))
  :returns (expr jexprp)
  :short "Generate a shallowly embedded ACL2 quoted symbol."
  :long
  (xdoc::topstring
   (xdoc::p
    "If guards are assumed and the symbol is an ACL2 boolean,
     we generate the corresponding Java boolean literal.")
   (xdoc::p
    "In all other cases,
     the generated expression depends on the current package,
     i.e. the package of the function where the quoted symbol occurs.
     If the current package is the same as the symbol's package,
     or if the current package imports the symbol,
     then we just generate the simple name of the field,
     because the field will be declared in the class for the current package.
     Otherwise, we generate a qualified name,
     preceded by the name of the class for the symbol's package.
     This mirrors the rules for symbol references in ACL2."))
  (b* (((when (and guards$
                   (booleanp symbol)))
        (if symbol (jexpr-literal-true) (jexpr-literal-false)))
       (sym-pkg (symbol-package-name symbol))
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
                               (curr-pkg stringp)
                               (guards$ booleanp))
  :returns (expr jexprp)
  :short "Generate a shallowly embedded ACL2 value."
  (cond ((acl2-numberp value) (atj-gen-shallow-number value))
        ((characterp value) (atj-gen-shallow-char value guards$))
        ((stringp value) (atj-gen-shallow-string value guards$))
        ((symbolp value) (atj-gen-shallow-symbol value
                                                 pkg-class-names
                                                 curr-pkg
                                                 guards$))
        ((consp value) (atj-gen-shallow-cons value qpairs))
        (t (prog2$ (raise "Internal error: ~x0 is not a recognized value."
                          value)
                   (jexpr-name "")))))
