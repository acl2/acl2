; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "builtin")
(include-book "unambiguity")
(include-book "validation-information")

(include-book "kestrel/utilities/messages" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)

(local (include-book "std/alists/top" :dir :system))

(local (in-theory (enable* abstract-syntax-unambp-rules)))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ validator
  :parents (syntax-for-tools)
  :short "Validator of the C abstract syntax for tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides syntactic validity,
     C code must satisfy a number of additional constraints
     in order to be compiled.
     These constraints form the static semantics of C.
     C compilers check that the code satisfies these constraints
     prior to translating it.")
   (xdoc::p
    "Here we provide a validator of C code,
     whose purpose is to check those constraints,
     i.e. to check whether the C code is valid and compilable.")
   (xdoc::p
    "If successful, the validator adds information to the abstract syntax,
     which downstream tools (e.g. C-to-C transformations) can make use of.")
   (xdoc::p
    "We start with an approximate validator
     that should accept all valid C code
     but also some invalid C code (due to the approximation).
     Even in its approximate form,
     this is useful to perform some validation,
     and to calculate information (approximate types)
     useful for manipulating the abstract syntax
     (e.g. for C-to-C transformations).")
   (xdoc::p
    "In a sense, the validator extends the @(see disambiguator),
     which performs an even more approximate validation,
     just enough to disambiguate the abstract syntax.
     Thus, there are structural similarities between
     the validator and the disambiguator.")
   (xdoc::p
    "Similarly to a compiler, the validator makes use of a symbol table,
     which tracks information about the symbols (identifiers) in the code.
     These symbol tables, called `validation tables', are, in some sense,
     an extension of the disambiguation tables used by the disambiguator.
     See @(tsee valid-table).")
   (xdoc::p
    "We use "
    (xdoc::seetopic "acl2::error-value-tuples" "error-value tuples")
    " to handle errors in the validator.")
   (xdoc::p
    "The ACL2 functions that validate
     the various constructs of the abstract syntax
     follow the @('valid-<fixtype>') naming scheme,
     where @('<fixtype>') is the name of
     the fixtype of the abstract syntax construct,
     and where @('valid') is best read as an abbreviation of `validate'
     rather than as the adjective `valid'."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-empty-scope ()
  :returns (scope valid-scopep)
  :short "Empty validator scope."
  :long
  (xdoc::topstring
   (xdoc::p
    "Scopes always start empty, i.e. with no identifiers.
     This function returns the empty scope."))
  (make-valid-scope :ord nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-init-table ()
  :returns (table valid-tablep)
  :short "Initial validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "This contains one empty scope (the initial file scope)."))
  (make-valid-table :scopes (list (valid-empty-scope))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-table-num-scopes ((table valid-tablep))
  :returns (num natp)
  :short "Number of scopes in a validation table."
  (len (valid-table->scopes table))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-push-scope ((table valid-tablep))
  :returns (new-table valid-tablep)
  :short "Push a scope onto the validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "The newly pushed scope is always empty."))
  (b* ((scopes (valid-table->scopes table))
       (new-scopes (cons (valid-empty-scope) scopes)))
    (change-valid-table table :scopes new-scopes))
  :hooks (:fix)
  ///

  (defret valid-table-num-scopes-of-valid-push-scope
    (equal (valid-table-num-scopes new-table)
           (1+ (valid-table-num-scopes table)))
    :hints (("Goal" :in-theory (enable valid-table-num-scopes len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-pop-scope ((table valid-tablep))
  :returns (new-table valid-tablep)
  :short "Pop a scope from the validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "The popped scope is discarded."))
  (b* (((unless (> (valid-table-num-scopes table) 0))
        (raise "Internal error: no scopes in validation table.")
        (valid-table-fix table))
       (scopes (valid-table->scopes table))
       (new-scopes (cdr scopes)))
    (change-valid-table table :scopes new-scopes))
  :hooks (:fix)
  ///

  (defret valid-table-num-scopes-of-valid-pop-scope
    (equal (valid-table-num-scopes new-table)
           (1- (valid-table-num-scopes table)))
    :hyp (> (valid-table-num-scopes table) 0)
    :hints (("Goal" :in-theory (enable valid-table-num-scopes len max fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-lookup-ord ((ident identp) (table valid-tablep))
  :returns (mv (info? valid-ord-info-optionp) (currentp booleanp))
  :short "Look up an ordinary identifier in a validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "According to the visibility and hiding rules [C17:6.2.1/2],
     we look up the identifier starting from the innermost scope.
     We stop as soon as we find a match.
     We return @('nil') if we reach the outermost scope
     without finding a match.")
   (xdoc::p
    "We also return a flag saying whether the identifier was found
     in the current (i.e. innermost) scope or in some other scope.
     We initialize this flag to @('t'),
     and we set to @('nil') when we perform the recursive call.
     The flag is irrelevant if the first result is @('nil'),
     but in this case the returned flag is @('nil') too."))
  (valid-lookup-ord-loop ident (valid-table->scopes table) t)
  :hooks (:fix)

  :prepwork
  ((define valid-lookup-ord-loop ((ident identp)
                                  (scopes valid-scope-listp)
                                  (currentp booleanp))
     :returns (mv (info? valid-ord-info-optionp) (updated-currentp booleanp))
     :parents nil
     (b* (((when (endp scopes)) (mv nil nil))
          (scope (car scopes))
          (ord-scope (valid-scope->ord scope))
          (ident+info (assoc-equal (ident-fix ident) ord-scope))
          ((when ident+info) (mv (cdr ident+info) (bool-fix currentp))))
       (valid-lookup-ord-loop ident (cdr scopes) nil))
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;

(define valid-lookup-ord-file-scope ((ident identp) (table valid-tablep))
  :returns (info? valid-ord-info-optionp)
  :short "Look up an ordinary identifier
          in the file scope of a validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unlike @(tsee valid-lookup-ord), this skips any block scopes,
     and directly looks up the identifier in the file scope.
     It is used in some situations."))
  (b* ((scopes (valid-table->scopes table))
       ((when (endp scopes)) (raise "Internal error: no scopes."))
       (scope (car (last scopes)))
       (ident+info (assoc-equal (ident-fix ident)
                                (valid-scope->ord scope)))
       ((when ident+info) (cdr ident+info)))
    nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-add-ord ((ident identp)
                       (info valid-ord-infop)
                       (table valid-tablep))
  :returns (new-table valid-tablep)
  :short "Add an ordinary identifier to the validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "We pass the information to associate to the identifier.")
   (xdoc::p
    "The identifier is always added to
     the first (i.e. innermost, i.e. current) scope.
     We check the existence of at least one scope;
     recall that there must be always a file scope.")
   (xdoc::p
    "If the identifier is already present in the current scope,
     its information is overwritten,
     but we only call this function after checking that
     this overwriting is acceptable,
     i.e. when it ``refines'' the validation information for the identifier.
     We could consider adding a guard to this function
     that characterizes the acceptable overwriting."))
  (b* (((unless (> (valid-table-num-scopes table) 0))
        (raise "Internal error: no scopes in validation table.")
        (valid-table-fix table))
       (scopes (valid-table->scopes table))
       (scope (car scopes))
       (ord-scope (valid-scope->ord scope))
       (new-ord-scope (acons (ident-fix ident)
                             (valid-ord-info-fix info)
                             ord-scope))
       (new-scope (change-valid-scope scope :ord new-ord-scope))
       (new-scopes (cons new-scope (cdr scopes))))
    (change-valid-table table :scopes new-scopes))
  :guard-hints (("Goal" :in-theory (enable valid-table-num-scopes acons)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define valid-add-ord-file-scope ((ident identp)
                                  (info valid-ord-infop)
                                  (table valid-tablep))
  :returns (new-table valid-tablep)
  :short "Add an ordinary identifier
          to the file scope of a validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unlike @(tsee valid-add-ord), this skips any block scopes,
     and directly updates the file scope at the bottom of the stack.
     It is used in some situations."))
  (b* ((scopes (valid-table->scopes table))
       ((when (endp scopes))
        (raise "Internal error: no scopes.")
        (irr-valid-table))
       (scope (car (last scopes)))
       (ord-scope (valid-scope->ord scope))
       (new-ord-scope (acons (ident-fix ident)
                             (valid-ord-info-fix info)
                             ord-scope))
       (new-scope (change-valid-scope scope :ord new-ord-scope))
       (new-scopes (append (butlast scopes 1) (list new-scope))))
    (change-valid-table table :scopes new-scopes))
  :guard-hints (("Goal" :in-theory (enable acons)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define valid-add-ord-objfuns-file-scope ((idents ident-listp)
                                          (type typep)
                                          (linkage linkagep)
                                          (defstatus valid-defstatusp)
                                          (uid uidp)
                                          (table valid-tablep))
  :returns (mv (new-uid uidp)
               (new-table valid-tablep))
  :short "Add a list of ordinary identifiers
          corresponding to objects or functions
          to the file scope of a validation table."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee valid-add-ord-file-scope)."))
  (if (endp idents)
      (mv (uid-fix uid) (valid-table-fix table))
    (valid-add-ord-objfuns-file-scope
      (cdr idents)
      type
      linkage
      defstatus
      (uid-increment uid)
      (valid-add-ord-file-scope (car idents)
                                (make-valid-ord-info-objfun
                                  :type type
                                  :linkage linkage
                                  :defstatus defstatus
                                  :uid uid)
                                table)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-dec/oct/hex-const ((const dec/oct/hex-constp))
  :returns (value natp)
  :short "Validate a decimal, octal, or hexadecimal constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of constant is always valid,
     but for this function we use the naming scheme @('valid-...')
     for uniformity with the other validator's functions.")
   (xdoc::p
    "This function actually evaluates the constant, to a natural number.
     This is needed by the validator in order to assign
     types to integer constants.
     This function returns a natural number,
     which can be arbitrarily large;
     whether an integer constant is too large is checked elsewhere.")
   (xdoc::p
    "For a decimal or octal constant, the value is a component of the fixtype.
     For a hexadecimal constant, we use a library function
     to convert the digits into a value;
     the digits are as they appear in the concrete syntax,
     i.e. in big-endian order."))
  (dec/oct/hex-const-case
   const
   :dec const.value
   :oct const.value
   :hex (str::hex-digit-chars-value const.digits))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-iconst ((iconst iconstp) (ienv ienvp))
  :returns (mv (erp maybe-msgp) (new-iconst iconstp) (type typep))
  :short "Validate an integer constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "An integer constant is valid iff
     it has a type according to the table in [C17:6.4.4.1/5].
     We formalize that table here, and we return the type of the constant.
     If the constant is too large,
     it does not have a type, and it is invalid."))
  (b* (((reterr) (irr-iconst) (irr-type))
       ((iconst iconst) iconst)
       (value (valid-dec/oct/hex-const iconst.core))
       ((erp type)
        (b* (((reterr) (irr-type)))
          (cond
           ((not iconst.suffix?)
            (if (dec/oct/hex-const-case iconst.core :dec)
                (cond ((ienv-sint-rangep value ienv) (retok (type-sint)))
                      ((ienv-slong-rangep value ienv) (retok (type-slong)))
                      ((ienv-sllong-rangep value ienv) (retok (type-sllong)))
                      (t (retmsg$ "The constant ~x0 is too large."
                                  (iconst-fix iconst))))
              (cond ((ienv-sint-rangep value ienv) (retok (type-sint)))
                    ((ienv-uint-rangep value ienv) (retok (type-uint)))
                    ((ienv-slong-rangep value ienv) (retok (type-slong)))
                    ((ienv-ulong-rangep value ienv) (retok (type-ulong)))
                    ((ienv-sllong-rangep value ienv) (retok (type-sllong)))
                    ((ienv-ullong-rangep value ienv) (retok (type-ullong)))
                    (t (retmsg$ "The constant ~x0 is too large."
                                (iconst-fix iconst))))))
           ((isuffix-case iconst.suffix? :u)
            (cond ((ienv-uint-rangep value ienv) (retok (type-uint)))
                  ((ienv-ulong-rangep value ienv) (retok (type-ulong)))
                  ((ienv-ullong-rangep value ienv) (retok (type-ullong)))
                  (t (retmsg$ "The constant ~x0 is too large."
                              (iconst-fix iconst)))))
           ((isuffix-case iconst.suffix? :l)
            (cond
             ((member-eq (lsuffix-kind (isuffix-l->length iconst.suffix?))
                         '(:locase-l :upcase-l))
              (if (dec/oct/hex-const-case iconst.core :dec)
                  (cond ((ienv-slong-rangep value ienv) (retok (type-slong)))
                        ((ienv-sllong-rangep value ienv) (retok (type-sllong)))
                        (t (retmsg$ "The constant ~x0 is too large."
                                    (iconst-fix iconst))))
                (cond ((ienv-slong-rangep value ienv) (retok (type-slong)))
                      ((ienv-ulong-rangep value ienv) (retok (type-ulong)))
                      ((ienv-sllong-rangep value ienv) (retok (type-sllong)))
                      ((ienv-ullong-rangep value ienv) (retok (type-ullong)))
                      (t (retmsg$ "The constant ~x0 is too large."
                                  (iconst-fix iconst))))))
             ((member-eq (lsuffix-kind (isuffix-l->length iconst.suffix?))
                         '(:locase-ll :upcase-ll))
              (if (dec/oct/hex-const-case iconst.core :dec)
                  (cond ((ienv-sllong-rangep value ienv) (retok (type-sllong)))
                        (t (retmsg$ "The constant ~x0 is too large."
                                    (iconst-fix iconst))))
                (cond ((ienv-sllong-rangep value ienv) (retok (type-sllong)))
                      ((ienv-ullong-rangep value ienv) (retok (type-ullong)))
                      (t (retmsg$ "The constant ~x0 is too large."
                                  (iconst-fix iconst))))))
             (t (prog2$ (impossible) (retmsg$ "")))))
           ((or (and (isuffix-case iconst.suffix? :ul)
                     (member-eq (lsuffix-kind
                                 (isuffix-ul->length iconst.suffix?))
                                '(:locase-l :upcase-l)))
                (and (isuffix-case iconst.suffix? :lu)
                     (member-eq (lsuffix-kind
                                 (isuffix-lu->length iconst.suffix?))
                                '(:locase-l :upcase-l))))
            (cond ((ienv-ulong-rangep value ienv) (retok (type-ulong)))
                  ((ienv-ullong-rangep value ienv) (retok (type-ullong)))
                  (t (retmsg$ "The constant ~x0 is too large."
                              (iconst-fix iconst)))))
           ((or (and (isuffix-case iconst.suffix? :ul)
                     (member-eq (lsuffix-kind
                                 (isuffix-ul->length iconst.suffix?))
                                '(:locase-ll :upcase-ll)))
                (and (isuffix-case iconst.suffix? :lu)
                     (member-eq (lsuffix-kind
                                 (isuffix-lu->length iconst.suffix?))
                                '(:locase-ll :upcase-ll))))
            (cond ((ienv-ullong-rangep value ienv) (retok (type-ullong)))
                  (t (retmsg$ "The constant ~x0 is too large."
                              (iconst-fix iconst)))))
           (t (prog2$ (impossible) (retmsg$ ""))))))
       (info (make-iconst-info :type type :value value))
       (new-iconst (change-iconst iconst :info info)))
    (retok new-iconst type))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-fconst ((fconst fconstp))
  :returns (type typep)
  :short "Validate a floating constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "A floating constant is always valid:
     [C17:6.4.4.2] states no restrictions,
     except for a recommended practice
     to provide a diagnostic message in certain cases,
     which also instructs to proceed with compilation nonetheless,
     suggesting that it should be only a warning, not an error.")
   (xdoc::p
    "The type is determined solely by the suffix, including its absence
     [C17:6.4.4.2/4]."))
  (b* ((suffix? (fconst-case fconst
                             :dec fconst.suffix?
                             :hex fconst.suffix?)))
    (cond ((not suffix?) (type-double))
          ((or (fsuffix-case suffix? :locase-f)
               (fsuffix-case suffix? :upcase-f))
           (type-float))
          ((or (fsuffix-case suffix? :locase-l)
               (fsuffix-case suffix? :upcase-l))
           (type-ldouble))
          (t (prog2$ (impossible) (irr-type)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-univ-char-name ((ucn univ-char-name-p) (max natp))
  :returns (mv (erp maybe-msgp) (code natp))
  :short "Validate a universal character name."
  :long
  (xdoc::topstring
   (xdoc::p
    "If validation is successful, we return the numeric code of the character.")
   (xdoc::p
    "[C17:6.4.3/2] states some restriction on the character code.
     [C17:6.4.4.4/4] and (implicitly) [C17:6.4.5/4]
     state type-based restrictions on
     the character codes of octal and hexadecimal escapes,
     based on the (possibly absent) prefix of
     the character constant or string literal.
     But it seems reasonable that the same range restrictions
     should also apply to universal character names;
     some experiments with the C compiler on Mac confirms this."))
  (b* (((reterr) 0)
       (code (univ-char-name-case
              ucn
              :locase-u (str::hex-digit-chars-value
                         (list (hex-quad->1st ucn.quad)
                               (hex-quad->2nd ucn.quad)
                               (hex-quad->3rd ucn.quad)
                               (hex-quad->4th ucn.quad)))
              :upcase-u (str::hex-digit-chars-value
                         (list (hex-quad->1st ucn.quad1)
                               (hex-quad->2nd ucn.quad1)
                               (hex-quad->3rd ucn.quad1)
                               (hex-quad->4th ucn.quad1)
                               (hex-quad->1st ucn.quad2)
                               (hex-quad->2nd ucn.quad2)
                               (hex-quad->3rd ucn.quad2)
                               (hex-quad->4th ucn.quad2)))))
       ((when (and (< code #xa0)
                   (not (= code #x24))
                   (not (= code #x40))
                   (not (= code #x60))))
        (retmsg$ "The universal character name ~x0 has a code ~x1
                  that is below A0h but is not 24h or 40h or 60h."
                 (univ-char-name-fix ucn) code))
       ((when (and (<= #xd800 code)
                   (<= code #xdfff)))
        (retmsg$ "The universal character name ~x0 has a code ~x1
                  between D800h and DFFFh."
                 (univ-char-name-fix ucn) code))
       ((when (> code (nfix max)))
        (retmsg$ "The universal character name ~x0 has a code ~x1 above ~x2."
                 (univ-char-name-fix ucn) code (nfix max))))
    (retok code))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-simple-escape ((esc simple-escapep))
  :returns (code natp)
  :short "Validate a simple escape."
  :long
  (xdoc::topstring
   (xdoc::p
    "Simple escapes are always valid.
     This function returns their ASCII codes.
     Note that these always fit in any of the types
     mentioned in [C17:6.4.4.4/4].
     The GCC escape @('\\%') is like the character @('%')."))
  (simple-escape-case
   esc
   :squote (char-code #\')
   :dquote (char-code #\")
   :qmark (char-code #\?)
   :bslash (char-code #\\)
   :a 7
   :b 8
   :f 12
   :n 10
   :r 13
   :t 9
   :v 11
   :percent (char-code #\%))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-oct-escape ((esc oct-escapep) (max natp))
  :returns (mv (erp maybe-msgp) (code natp))
  :short "Validate an octal escape."
  :long
  (xdoc::topstring
   (xdoc::p
    "[C17:6.4.4.4/9] states restrictions on
     the numeric value of an octal escape used in a character constant,
     based on the prefix of the character constant;
     similarly restrictions apply to octal escapes in string literals
     [C17:6.4.5/4].
     This ACL2 function is used to check
     both octal escapes in character constants
     and octal escapes in string literals:
     we pass as input the maximum allowed character code,
     which is determined from the character constant or string literal prefix
     if present (see callers),
     and suffices to express the applicable restrictions."))
  (b* (((reterr) 0)
       (code (oct-escape-case
              esc
              :one (str::oct-digit-char-value esc.digit)
              :two (str::oct-digit-chars-value (list esc.digit1
                                                     esc.digit2))
              :three (str::oct-digit-chars-value (list esc.digit1
                                                       esc.digit2
                                                       esc.digit3)))))
    (if (<= code (nfix max))
        (retok code)
      (retmsg$ "The octal escape sequence ~x0 has value ~x1, ~
                which exceeds the maximum allowed ~x2, ~
                required in the context of where this octal escape occurs."
               (oct-escape-fix esc)
               code
               (nfix max))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-escape ((esc escapep) (max natp))
  :returns (mv (erp maybe-msgp) (code natp))
  :short "Validate an escape sequence."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the escape sequence is valid, we return its character code.
     For simple and octal escapes, and for universal character names,
     we use separate validation functions.
     For a hexadecimal escape, we calculate the numeric value,
     and we subject them to same restrictions as octal escapes
     [C17:6.4.4.4/9] [C17:6.4.5/4].")
   (xdoc::p
    "Although [C17] does not seem to state that explicitly,
     it seems reasonable that the same restriction applies to
     universal character names;
     we will revise this if that turns out to be not the case."))
  (b* (((reterr) 0))
    (escape-case
     esc
     :simple (retok (valid-simple-escape esc.unwrap))
     :oct (valid-oct-escape esc.unwrap max)
     :hex (b* ((code (str::hex-digit-chars-value esc.unwrap)))
            (if (<= code (nfix max))
                (retok code)
              (retmsg$ "The hexadecimal escape sequence ~x0 has value ~x1, ~
                        which exceeds the maximum allowed ~x2, ~
                        required in the context where ~
                        this hexadecimal escape occurs."
                       (escape-fix esc)
                       code
                       (nfix max))))
     :univ (valid-univ-char-name esc.unwrap max)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-c-char ((cchar c-char-p) (prefix? cprefix-optionp) (ienv ienvp))
  :returns (mv (erp maybe-msgp) (code natp))
  :short "Validate a character of a character constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "If validation succeeds, we return the character code.")
   (xdoc::p
    "The grammar [C17:6.4.4.4/1] excludes (direct) character codes
     for single quote and new-line.
     For the latter, we check both line feed and carriage return.
     Note that our lexer normalizes both to line feed,
     and excludes line feed when lexing @('c-char');
     here we make an independent check,
     but in the future we could make that
     an invariant in the abstract syntax.")
   (xdoc::p
    "[C17:6.4.4.4/4] says that, based on the (possibly absent) prefix
     of the character constant of which this character is part,
     the character code of an octal or hexadecimal escape must fit in
     @('unsigned char'), or
     @('wchar_t'), or
     @('char16_t'), or
     @('char32_t').
     To properly capture the range of the latter three types,
     we should probably extend our implementation environments
     with information about which built-in types those types expand to,
     and then use again the implementation environment
     to obtain the maximun values of such built-in types.
     For now, we just use the maximum Unicode code points,
     i.e. effectively we do not enforce any restriction."))
  (b* (((reterr) 0)
       (max (if prefix?
                #x10ffff
              (ienv->uchar-max ienv))))
    (c-char-case
     cchar
     :char (cond ((= cchar.unwrap (char-code #\'))
                  (retmsg$ "Single quote cannot be used directly ~
                            in a character constant."))
                 ((= cchar.unwrap 10)
                  (retmsg$ "Line feed cannot be used directly ~
                            in a character constant."))
                 ((= cchar.unwrap 13)
                  (retmsg$ "Carriage return cannot be used directly ~
                            in a character constant."))
                 ((> cchar.unwrap max)
                  (retmsg$ "The character with code ~x0 ~
                            exceed the maximum ~x1 allowed for ~
                            a character constant with prefix ~x2."
                           cchar.unwrap max (cprefix-option-fix prefix?)))
                 (t (retok cchar.unwrap)))
     :escape (valid-escape cchar.unwrap max)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-c-char-list ((cchars c-char-listp)
                           (prefix? cprefix-optionp)
                           (ienv ienvp))
  :returns (mv (erp maybe-msgp) (codes nat-listp))
  :short "Validate a list of characters of a character constant."
  (b* (((reterr) nil)
       ((when (endp cchars)) (retok nil))
       ((erp code) (valid-c-char (car cchars) prefix? ienv))
       ((erp codes) (valid-c-char-list (cdr cchars) prefix? ienv)))
    (retok (cons code codes)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-cconst ((cconst cconstp) (ienv ienvp))
  :returns (mv (erp maybe-msgp) (type typep))
  :short "Validate a character constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check the characters that form the constant,
     with respect to the prefix (if any).
     If validation is successful, we return the type of the constant.
     According to [C17:6.4.4.4/10],
     a character constant without prefix has type @('int').
     According to [C17:6.4.4.4/11],
     a character constant with a prefix has type
     @('wchar_t'), @('char16_t'), or @('char32_t');
     since for now we do not model these,
     we return an unknown type in this case.")
   (xdoc::p
    "The types @('wchar_t'), @('char16_t'), and @('char32_t')
     may vary across implementations.
     In order to handle these in a general way,
     we should probably extend our implementation environments
     with information about which built-in types those types expand to.
     Once we do that, we will be able to perform
     a full validation of character constants here."))
  (b* (((reterr) (irr-type))
       ((cconst cconst) cconst)
       ((erp &) (valid-c-char-list cconst.cchars cconst.prefix? ienv)))
    (if cconst.prefix?
        (retok (type-unknown))
      (retok (type-sint))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-enum-const ((econst identp) (table valid-tablep))
  :returns (mv (erp maybe-msgp) (type typep))
  :short "Validate an enumeration constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we validate an enumeration constant that occurs as an expression.
     Thus, the validation table must include that (ordinary) identifier,
     with the information of being an enumeration constant.
     Its type is always @('int') [C17:6.7.2.2/3],
     so this function always returns that type if validation succeeds;
     we could have this function return nothing if there's no error,
     but we have it return the @('int') type for uniformity and simplicity."))
  (b* (((reterr) (irr-type))
       ((mv info &) (valid-lookup-ord econst table))
       ((unless info)
        (retmsg$ "The identifier ~x0, used as an enumeration constant, ~
                  is not in scope."
                 (ident-fix econst)))
       ((unless (valid-ord-info-case info :enumconst))
        (retmsg$ "The identifier ~x0, used as an enumeration constant, ~
                  is in scope, but it is not an enumeration constant: ~
                  its information is ~x1."
                 (ident-fix econst) info)))
    (retok (type-sint)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-const ((const constp) (table valid-tablep) (ienv ienvp))
  :returns (mv (erp maybe-msgp) (new-const constp) (type typep))
  :short "Validate a constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "If validation is successful, we return the type of the constant."))
  (b* (((reterr) (irr-const) (irr-type)))
    (const-case
     const
     :int (b* (((erp iconst type) (valid-iconst const.unwrap ienv)))
            (retok (const-int iconst) type))
     :float (b* ((type (valid-fconst const.unwrap)))
              (retok (const-fix const) type))
     :enum (b* (((erp type) (valid-enum-const const.unwrap table)))
             (retok (const-fix const) type))
     :char (b* (((erp type) (valid-cconst const.unwrap ienv)))
             (retok (const-fix const) type))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-s-char ((schar s-char-p) (prefix? eprefix-optionp) (ienv ienvp))
  :returns (mv (erp maybe-msgp) (code natp))
  :short "Validate a character of a string literal."
  :long
  (xdoc::topstring
   (xdoc::p
    "If validation succeeds, we return the character code.
     [C17:6.4.5/4] says that the same restrictions that apply
     to @('c-char')s in character constants
     also apply to @('s-char')s in string literals.
     So this function is similar to @(tsee valid-c-char),
     except that we prohibit double quote instead of single quote,
     based on the grammar in [C17:6.4.5/1]."))
  (b* (((reterr) 0)
       (max (if prefix?
                #x10ffff
              (ienv->uchar-max ienv))))
    (s-char-case
     schar
     :char (cond ((= schar.unwrap (char-code #\"))
                  (retmsg$ "Double quote cannot be used directly ~
                            in a string literal."))
                 ((= schar.unwrap 10)
                  (retmsg$ "Line feed cannot be used directly ~
                            in a character constant."))
                 ((= schar.unwrap 13)
                  (retmsg$ "Carriage return cannot be used directly ~
                            in a character constant."))
                 ((> schar.unwrap max)
                  (retmsg$ "The character with code ~x0 ~
                            exceeds the maximum ~x1 allowed for ~
                            a character constant with prefix ~x2."
                           schar.unwrap max (eprefix-option-fix prefix?)))
                 (t (retok schar.unwrap)))
     :escape (valid-escape schar.unwrap max)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-s-char-list ((cchars s-char-listp)
                           (prefix? eprefix-optionp)
                           (ienv ienvp))
  :returns (mv (erp maybe-msgp) (codes nat-listp))
  :short "Validate a list of characters of a string literal."
  (b* (((reterr) nil)
       ((when (endp cchars)) (retok nil))
       ((erp code) (valid-s-char (car cchars) prefix? ienv))
       ((erp codes) (valid-s-char-list (cdr cchars) prefix? ienv)))
    (retok (cons code codes)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-stringlit ((strlit stringlitp) (ienv ienvp))
  :returns (mv (erp maybe-msgp) (type typep))
  :short "Validate a string literal."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check the characters that form the string literal,
     with respect to the prefix (if any).
     If validation is successful, we return the type of the string literal,
     which according to [C17:6.4.5/6], is an array type
     of @('char') or @('wchar_t') or @('char16_t') or @('char32_t').
     In our current approximate type system,
     we just have a single type for arrays, so we return that."))
  (b* (((reterr) (irr-type))
       ((stringlit strlit) strlit)
       ((erp &) (valid-s-char-list strlit.schars strlit.prefix? ienv)))
    (retok (type-array)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-stringlit-list ((strlits stringlit-listp) (ienv ienvp))
  :returns (mv (erp maybe-msgp) (type typep))
  :short "Validate a list of string literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our abstract syntax preserves information about
     adjacent string literals [C17:5.1.1.2/6],
     by using lists of string literals, instead of single string literals,
     in various places.
     So the validator also operates on such lists of string literals.")
   (xdoc::p
    "One basic requirement is that the list is not empty,
     because there must be at least one string literal;
     in the future we could built that constraint into the abstract syntax,
     but for now we put that as a check in the validator.")
   (xdoc::p
    "Another requirement is that
     there cannot be both UTF-8 and wide prefixes [C17:6.4.5/2],
     where these kinds of prefixes are defined in [C17:6.4.5/3].
     We check that by projecting the optional prefixes
     and checking for incompatible occurrences.")
   (xdoc::p
    "Whether string literals with different prefixes
     (satisfying the requirement just mentioned)
     can be concatenated, and what their combined type is,
     is implementation-defined [C17:6.4.5/5].
     We plan to extend our implementation environments
     with information about how to treat those cases,
     but for now we allow all concatenations,
     and the resulting type is just our approximate type for all arrays."))
  (b* (((reterr) (irr-type))
       ((erp) (valid-stringlit-list-loop strlits ienv))
       ((unless (consp strlits))
        (retmsg$ "There must be at least one string literal."))
       (prefixes (stringlit-list->prefix?-list strlits))
       ((when (and (member-equal (eprefix-locase-u8) prefixes)
                   (or (member-equal (eprefix-locase-u) prefixes)
                       (member-equal (eprefix-upcase-u) prefixes)
                       (member-equal (eprefix-upcase-l) prefixes))))
        (retmsg$ "Incompatible prefixes ~x0 in the list of string literals."
                 prefixes)))
    (retok (type-array)))
  :hooks (:fix)
  :prepwork
  ((define valid-stringlit-list-loop ((strlits stringlit-listp) (ienv ienvp))
     :returns (erp maybe-msgp)
     :parents nil
     (b* (((reterr))
          ((when (endp strlits)) (retok))
          ((erp &) (valid-stringlit (car strlits) ienv)))
       (valid-stringlit-list-loop (cdr strlits) ienv))
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-var ((var identp) (table valid-tablep))
  :returns (mv (erp maybe-msgp)
               (type typep)
               (linkage linkagep)
               (uid uidp))
  :short "Validate a variable."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to validate the @(':ident') case of the @(tsee expr) fixtype.
     This is the case of a variable, not an enumeration constant,
     which is part of the @(':const') case of @(tsee expr).
     Recall that the parser initially parses all identifiers used as expressions
     under the @(':ident') case, but the disambiguator re-classifies
     some of them under the @(':const') case, as appropriate.")
   (xdoc::p
    "A variable (i.e. identifier) is valid if
     it is found in the validation table,
     recorded as denoting an object or function
     [C17:6.5.1/2].
     The type and the linkage are obtained from the table."))
  (b* (((reterr) (irr-type) (irr-linkage) (irr-uid))
       ((mv info &) (valid-lookup-ord var table))
       ((unless info)
        (retmsg$ "The variable ~x0 is not in scope." (ident-fix var)))
       ((unless (valid-ord-info-case info :objfun))
        (retmsg$ "The identifier ~x0, used as a variable,is in scope, ~
                  but does not denote an object or function."
                 (ident-fix var))))
    (retok (valid-ord-info-objfun->type info)
           (valid-ord-info-objfun->linkage info)
           (valid-ord-info-objfun->uid info)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-gensel ((expr exprp)
                      (type typep)
                      (type-alist type-option-type-alistp))
  :guard (expr-case expr :gensel)
  :returns (mv (erp maybe-msgp) (type typep))
  :short "Validate a generic selection expression,
          given the types for the components."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we do not perform any of the checks prescribed in [C17:6.5.1.1/2].
     We will perform them later, when we refine our validator.
     We return the unknown type."))
  (declare (ignore expr type type-alist))
  (retok (type-unknown))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-arrsub ((expr exprp) (type-arg1 typep) (type-arg2 typep))
  :guard (expr-case expr :arrsub)
  :returns (mv (erp maybe-msgp) (type typep))
  :short "Validate an array subscripting expression,
          given the types of the two sub-expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "After converting array types to pointer types,
     one sub-expression must have pointer type,
     and the other sub-expression must have integer type
     [C17:6.5.2.1/1].
     The expression should have the type referenced by the pointer type,
     but since for now we model just one pointer type,
     the type of the expression is unknown.")
   (xdoc::p
    "There is no need to perform function-to-pointer conversion,
     because that would result in a pointer to function,
     which is disallowed,
     as it has to be a pointer to a complete object type [C17:6.5.2.1/1].
     So by leaving function types as such, we automatically disallow them."))
  (b* (((reterr) (irr-type))
       ((when (or (type-case type-arg1 :unknown)
                  (type-case type-arg2 :unknown)))
        (retok (type-unknown)))
       (type1 (type-apconvert type-arg1))
       (type2 (type-apconvert type-arg2))
       ((unless (or (and (type-case type1 :pointer)
                         (type-integerp type2))
                    (and (type-integerp type1)
                         (type-case type2 :pointer))))
        (retmsg$ "In the array subscripting expression ~x0, ~
                  the first sub-expression has type ~x1, ~
                  and the second sub-expression has type ~x2."
                 (expr-fix expr)
                 (type-fix type-arg1)
                 (type-fix type-arg2))))
    (retok (type-unknown)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-funcall ((expr exprp) (type-fun typep) (types-arg type-listp))
  :guard (expr-case expr :funcall)
  :returns (mv (erp maybe-msgp) (type typep))
  :short "Validate a function call expression,
          given the types of the sub-expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "After converting function types to pointer types,
     the first sub-expression must have pointer type [C17:6.5.2.2/1];
     since we currently have just one pointer type,
     we cannot check that it is a pointer to a function.
     For the same reason,
     we do not check the argument types against the function type [C17:6.5.2.2/2].
     Also for the same reason,
     we return the unknown type,
     because we do not have information about the result type.")
   (xdoc::p
    "There is no need to perform array-to-pointer conversion,
     because array types cannot have function element types,
     but only (complete) object element types [C17:6.2.5/20].
     Thus, the conversion could never result into a pointer to a function."))
  (b* (((reterr) (irr-type))
       ((when (or (type-case type-fun :unknown)
                  (member-equal (type-unknown) (type-list-fix types-arg))))
        (retok (type-unknown)))
       (type (type-fpconvert type-fun))
       ((unless (type-case type :pointer))
        (retmsg$ "In the function call expression ~x0, ~
                  the first sub-expression has type ~x1."
                 (expr-fix expr)
                 (type-fix type-fun))))
    (retok (type-unknown)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-member ((expr exprp) (type-arg typep))
  :guard (expr-case expr :member)
  :returns (mv (erp maybe-msgp) (type typep))
  :short "Validate a member expression,
          given the type of the sub-expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The argument type must be a structure or union type [C17:6.5.2.3/1].
     Since a pointer type is not allowed here,
     there is no need to convert arrays or functions to pointers.")
   (xdoc::p
    "For now we only have one type for structures and one type for unions.
     We cannot look up the member type, so we return the unknown type."))
  (b* (((reterr) (irr-type))
       ((when (type-case type-arg :unknown))
        (retok (type-unknown)))
       ((unless (or (type-case type-arg :struct)
                    (type-case type-arg :union)))
        (retmsg$ "In the member expression ~x0, ~
                  the sub-expression has type ~x1."
                 (expr-fix expr) (type-fix type-arg))))
    (retok (type-unknown)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-memberp ((expr exprp) (type-arg typep))
  :guard (expr-case expr :memberp)
  :returns (mv (erp maybe-msgp) (type typep))
  :short "Validate a member pointer expression,
          given the type of the sub-expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type of the sub-expression is
     calculated (recursively) by @(tsee valid-expr).")
   (xdoc::p
    "The argument type must be a pointer to a structure or union type
     [C17:6.5.2.3/2].
     We need to convert arrays to pointers,
     and then we just check that we have the (one) pointer type;
     we will refine this when we refine our type system.
     We do not conver functions to pointers,
     because that would result into a pointer to function,
     which is not a pointer to structure or union as required;
     thus, by leaving function types unchanged, we reject them here.")
   (xdoc::p
    "Since we cannot yet look up members in structure and union types,
     we return the unknown type."))
  (b* (((reterr) (irr-type))
       ((when (type-case type-arg :unknown))
        (retok (type-unknown)))
       (type (type-apconvert type-arg))
       ((unless (type-case type :pointer))
        (retmsg$ "In the member pointer expression ~x0, ~
                  the sub-expression has type ~x1."
                 (expr-fix expr) (type-fix type-arg))))
    (retok (type-unknown)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-unary ((expr exprp) (op unopp) (type-arg typep) (ienv ienvp))
  :guard (expr-case expr :unary)
  :returns (mv (erp maybe-msgp) (type typep))
  :short "Validate a unary expression,
          given the type of the sub-expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('&') operator requires an lvalue of any type as operand
     [C17:6.5.3.2/1] [C17:6.5.3.2/3],
     but we are not yet distinguishing lvalues from non-lvalues,
     so we allow any type of operand, and we return the (one) pointer type.")
   (xdoc::p
    "The @('*') unary operator requires an operand of a pointer type
     [C17:6.5.3.2/2],
     after array-to-pointer and function-to-pointer conversions;
     as always, we also need to allow the unknown type.
     Since we only have one type for pointers for now,
     the resulting type is unknown.")
   (xdoc::p
    "The @('+') and @('-') unary operators
     require an operand of an arithmetic type [C17:6.5.3.3/1],
     and the result has the promoted type [C17:6.5.3.3/2].
     There is no need for array-to-pointer and function-to-pointer conversions,
     because they never result in arithmetic types.")
   (xdoc::p
    "The @('~') operator requires an operand of an integer type [C17:6.5.3.3/1],
     and the result has the promoted type [C17:.6.5.3.3/4].
     There is no need for array-to-pointer and function-to-pointer conversions,
     because they never result in arithmetic types.")
   (xdoc::p
    "The @('!') operator requires an operand of a scalar type [C17:6.5.3.3/1],
     and result is always @('signed int') [C17:6.5.3.3/5].
     Since pointers may be involved, we perform
     array-to-pointer and function-to-pointer conversions.")
   (xdoc::p
    "The @('sizeof') operator applied to an expression
     requires a non-function complete type [C17:6.5.3.4/1].
     In our current approximate type system,
     we just exclude function types,
     but we do not have a notion of complete types yet.
     The result has type @('size_t') [C17:6.5.3.4/5],
     whose definition is implementation-defined,
     so for now we just return the unknown type;
     we will need to extend implementation environments
     with information about the definition of @('size_t').")
   (xdoc::p
    "The @('++') pre-increment and @('--') pre-decrement operators
     require a real or pointer operand [C17:6.5.3.1/1].
     Since these expressions are equivalent to assignments
     [C17:6.5.3.1/2] [C17:6.5.3.1/3],
     the type of the result must be the type of the operand.
     We do not perform array-to-pointer or function-to-pointer conversions,
     because those result in pointers, not lvalues as required [C17:6.5.3.1/1].")
   (xdoc::p
    "The @('++') post-increment and @('--') post-decrement operators
     require a real or pointer operand [C17:6.5.2.4/1].
     The type of the result is the same as the operand
     [C17:6.5.2.4/2] [C17:6.5.2.4/3].
     We do not perform array-to-pointer or function-to-pointer conversions,
     because those result in pointers, not lvalues as required [C17:6.5.2.4/1]."))
  (b* (((reterr) (irr-type))
       ((when (type-case type-arg :unknown))
        (retok (type-unknown)))
       (msg (msg$ "In the unary expression ~x0, ~
                   the sub-expression has type ~x1."
                 (expr-fix expr) (type-fix type-arg))))
    (case (unop-kind op)
      (:address (retok (type-pointer)))
      (:indir (b* ((type (type-fpconvert (type-apconvert type-arg)))
                   ((unless (type-case type :pointer))
                    (reterr msg)))
                (retok (type-unknown))))
      ((:plus :minus) (b* (((unless (type-arithmeticp type-arg))
                            (reterr msg)))
                        (retok (type-promote type-arg ienv))))
      (:bitnot (b* (((unless (type-integerp type-arg))
                     (reterr msg)))
                 (retok (type-promote type-arg ienv))))
      (:lognot (b* ((type (type-fpconvert (type-apconvert type-arg)))
                    ((unless (type-scalarp type))
                     (reterr msg)))
                 (retok (type-sint))))
      ((:preinc :predec :postinc :postdec)
       (b* (((unless (or (type-realp type-arg)
                         (type-case type-arg :pointer)))
             (reterr msg)))
         (retok (type-fix type-arg))))
      (:sizeof (b* (((when (type-case type-arg :function))
                     (reterr msg)))
                 (retok (type-unknown))))
      (t (prog2$ (impossible) (retmsg$ "")))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-binary ((expr exprp)
                      (op binopp)
                      (type-arg1 typep)
                      (type-arg2 typep)
                      (ienv ienvp))
  :guard (expr-case expr :binary)
  :returns (mv (erp maybe-msgp) (type typep))
  :short "Validate a binary expression,
          given the type of the sub-expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('*') binary and @('/') operators
     require arithmetic operands [C17:6.5.5/2].
     The result is the common type according to
     the usual arithmetic conversions [C17:6.5.5/3].
     There is no need for array-to-pointer or function-to-pointer conversions
     because those never produce arithmetic types.")
   (xdoc::p
    "The @('%') operator requires integer operands [C17:6.5.5/2].
     The result is from the usual arithmetic conversions [C17:6.5.5/3].
     No array-to-pointer or function-to-pointer conversions are needed.")
   (xdoc::p
    "The @('+') binary operator requires
     either two arithmetic operands
     or an integer and a pointer operand
     [C17:6.5.6/2].
     In the first case, the result is from the usual arithmetic conversions
     [C17:6.5.6/4].
     In the second case, the result is the pointer type [C17:6.5.6/8].
     Because of that second case, which involves pointers,
     we perform array-to-pointer conversion.
     We do not perform function-to-pointer conversion,
     because that would result in a pointer to function,
     while a pointer to complete object type is required.")
   (xdoc::p
    "The @('-') binary operator requires
     either two arithmetic operands,
     or two pointer operands,
     or a pointer first operand and an integer second operand
     [C17:6.5.6/3].
     In the first case, the result is from the usual arithmetic conversions
     [C17:6.5.6/4].
     In the second case, the result has type @('ptrdiff_t') [C17:6.5.6/9],
     which has an implementation-specific definition,
     and so we return the unknown type in this case.
     In the third case, the result has the pointer type [C17:6.5.6/8].
     Because of the second and third cases, which involve pointers,
     we perform array-to-pointer conversion.
     We do not perform function-to-pointer conversion,
     because that would result in a pointer to function,
     while a pointer to complete object type is required.")
   (xdoc::p
    "The @('<<') and @('>>') operators require integer operands [C17:6.5.7/2].
     The type of the result is the type of the promoted left operand
     [C17:6.5.7/3].
     There is no need for
     array-to-pointer or function-to-pointer conversions.")
   (xdoc::p
    "The @('<'), @('>'), @('<='), and @('>=') operators
     require real types or pointer types [C17:6.5.8/2].
     The result is always @('signed int') [C17:6.5.8/6].
     Since pointers may be involved,
     we perform array-to-pointer conversion.
     We do not perform function-to-pointer conversion,
     because that would result in a pointer to function,
     while a pointer to object type is required.
     The standard does not allow
     a null pointer constants [C17:6.3.2.3/3] without the @('void *') cast
     to be used as an operand while the other operand has pointer type.
     But we found it accepted by practical compilers,
     so it is probably a GCC extensions,
     and for this reason we accept it for now;
     we should extend our implementation environments with
     information about whether GCC extensions are allowed,
     and condition acceptance under that flag.
     Since we do not have code yet to recognize null pointer constants,
     we accept any integer expression;
     that is, we allow one pointer operand and one integer operand.")
   (xdoc::p
    "The @('==') and @('!=') operators require
     arithmetic types or pointer types [C17:6.5.9/2];
     Distinctions betwen qualified and unqualified pointer types,
     as well as @('void') or non-@('void') pointers types are ignored
     since we currently approximate all of these as a single pointer type.
     Since we do not yet implement evaluation of constant expressions,
     all integer expressions are considered potential null pointer constants:
     so we allow an operand to be a pointer and the other to be an integer,
     to accommodate a null pointer constant [C17:6.3.2.3/3]
     without the @('void *') cast.
     The result is always @('signed int') [C17:6.5.9/3].
     Since pointers may be involved,
     we perform array-to-pointer and function-to-pointer conversions.")
   (xdoc::p
    "The @('&'), @('^'), and @('|') operators require integer operands
     [C17:6.5.10/2] [C17:6.5.11/2] [C17:6.5.12/2].
     The result has the type from the usual arithmetic conversions
     [C17:6.5.10/3] [C17:6.5.11/3] [C17:6.5.12/3].
     No array-to-pointer or function-to-pointer conversion is needed.")
   (xdoc::p
    "The @('&&') and @('||') operators require scalar types
     [C17:6.5.13/2] [C17:6.5.14/2].
     The result has type @('signed int') [C17:6.5.13/3] [C17:6.5.14/3].
     Since pointers may be involved, we need to perform
     array-to-pointer and function-to-pointer conversions.")
   (xdoc::p
    "The @('=') simple assignment operator requires
     an lvalue as left operand [C17:6.5.16/2],
     but currently we do not check that.
     In our currently approximate type system,
     the requirements in [C17:6.5.16.1/1] reduce to the following four cases.")
   (xdoc::ol
    (xdoc::li
     "Both operands have arithmetic types.")
    (xdoc::li
     "The left operand has a structure or union type, and the two operand types
      are compatible.")
    (xdoc::li
     "The left operand has the pointer type and the right operand is either a
      pointer or a null pointer constant (approximated as anything of an
      integer type).")
    (xdoc::li
     "The left operand has the boolean type and the right operand has the
      pointer type."))
   (xdoc::p
    "We do not perform array-to-pointer or function-to-pointer conversion
     on the left operand, because the result would not be an lvalue.
     The type of the result is the type of the left operand [C17:6.5.16/3].")
   (xdoc::p
    "The @('*=') and @('/=') operators require arithmetic operands
     [C17:6.5.16.2/2],
     and the result has the type of the first operand [C17:6.5.16/3].
     No array-to-pointer or function-to-pointer conversions are needed.")
   (xdoc::p
    "The @('%=') operator requires integer operands [C17:6.5.16.2/2],
     and the result has the type of the first operand [C17:6.5.16/3].
     No array-to-pointer or function-to-pointer conversions are needed.")
   (xdoc::p
    "The @('+=') and @('-=') operands require
     either arithmetic operands
     or a first pointer operand and a second integer operand
     [C17:6.5.16.2/1].
     The result has the type of the first operand [C17:6.5.16/3].
     Since pointers may be involved,
     we perform array-to-pointer and function-to-pointer conversions.")
   (xdoc::p
    "The @('<<='), @('>>='), @('&='), @('^='), and @('|=') operators
     require integer operands [C17:6.5.13.2/2].
     The result has the type of the first operand [C17:6.5.13/3].
     No array-to-pointer or function-to-pointer conversions are needed."))
  (b* (((reterr) (irr-type))
       ((when (or (type-case type-arg1 :unknown)
                  (type-case type-arg2 :unknown)))
        (retok (type-unknown)))
       (msg (msg$ "In the binary expression ~x0, ~
                   the sub-expressiona have types ~x1 and ~x2."
                  (expr-fix expr) (type-fix type-arg1) (type-fix type-arg2))))
    (case (binop-kind op)
      ((:mul :div) (b* (((unless (and (type-arithmeticp type-arg1)
                                      (type-arithmeticp type-arg2)))
                         (reterr msg)))
                     (retok (type-uaconvert type-arg1 type-arg2 ienv))))
      (:rem (b* (((unless (and (type-arithmeticp type-arg1)
                               (type-arithmeticp type-arg2)))
                  (reterr msg)))
              (retok (type-uaconvert type-arg1 type-arg2 ienv))))
      (:add (b* ((type1 (type-apconvert type-arg1))
                 (type2 (type-apconvert type-arg2)))
              (cond
               ((and (type-arithmeticp type1)
                     (type-arithmeticp type2))
                (retok (type-uaconvert type1 type2 ienv)))
               ((or (and (type-integerp type1)
                         (type-case type2 :pointer))
                    (and (type-case type1 :pointer)
                         (type-integerp type2)))
                (retok (type-pointer)))
               (t (reterr msg)))))
      (:sub (b* ((type1 (type-apconvert type-arg1))
                 (type2 (type-apconvert type-arg2)))
              (cond
               ((and (type-arithmeticp type1)
                     (type-arithmeticp type2))
                (retok (type-uaconvert type1 type2 ienv)))
               ((and (type-case type1 :pointer)
                     (type-integerp type2))
                (retok (type-pointer)))
               ((and (type-case type1 :pointer)
                     (type-case type2 :pointer))
                (retok (type-unknown)))
               (t (reterr msg)))))
      ((:shl :shr) (b* (((unless (and (type-integerp type-arg1)
                                      (type-integerp type-arg2)))
                         (reterr msg)))
                     (retok (type-promote type-arg1 ienv))))
      ((:lt :gt :le :ge)
       (b* ((type1 (type-apconvert type-arg1))
            (type2 (type-apconvert type-arg2))
            ((unless (or (and (type-realp type1)
                              (type-realp type2))
                         (if (type-case type1 :pointer)
                             (or (type-case type2 :pointer)
                                 (expr-null-pointer-constp (expr-binary->arg2 expr) type2))
                           (and (expr-null-pointer-constp (expr-binary->arg1 expr) type1)
                                (type-case type2 :pointer)))))
             (reterr msg)))
         (retok (type-sint))))
      ((:eq :ne) (b* ((type1 (type-fpconvert (type-apconvert type-arg1)))
                      (type2 (type-fpconvert (type-apconvert type-arg2)))
                      ((unless (or (and (type-arithmeticp type1)
                                        (type-arithmeticp type2))
                                   (if (type-case type1 :pointer)
                                       (or (type-case type2 :pointer)
                                           (expr-null-pointer-constp (expr-binary->arg2 expr) type2))
                                     (and (expr-null-pointer-constp (expr-binary->arg1 expr) type1)
                                          (type-case type2 :pointer)))))
                       (reterr msg)))
                   (retok (type-sint))))
      ((:bitand :bitxor :bitior)
       (b* (((unless (and (type-integerp type-arg1)
                          (type-integerp type-arg2)))
             (reterr msg)))
         (retok (type-uaconvert type-arg1 type-arg2 ienv))))
      ((:logand :logor)
       (b* ((type1 (type-fpconvert (type-apconvert type-arg1)))
            (type2 (type-fpconvert (type-apconvert type-arg2)))
            ((unless (and (type-scalarp type1)
                          (type-scalarp type2)))
             (reterr msg)))
         (retok (type-sint))))
      (:asg (b* ((type1 type-arg1)
                 (type2 (type-fpconvert (type-apconvert type-arg2)))
                 ((unless (or (and (type-arithmeticp type1)
                                   (type-arithmeticp type2))
                              (and (or (type-case type1 :struct)
                                       (type-case type1 :union))
                                   (type-compatiblep type1 type2))
                              (and (type-case type1 :pointer)
                                   (or (type-case type2 :pointer)
                                       (expr-null-pointer-constp (expr-binary->arg2 expr) type2)))
                              (and (type-case type1 :bool)
                                   (type-case type2 :pointer))))
                  (reterr msg)))
              (retok (type-fix type-arg1))))
      ((:asg-mul :asg-div)
       (b* (((unless (and (type-arithmeticp type-arg1)
                          (type-arithmeticp type-arg2)))
             (reterr msg)))
         (retok (type-fix type-arg1))))
      (:asg-rem (b* (((unless (and (type-integerp type-arg1)
                                   (type-integerp type-arg2)))
                      (reterr msg)))
                  (retok (type-fix type-arg1))))
      ((:asg-add :asg-sub)
       (b* ((type1 (type-fpconvert (type-apconvert type-arg1)))
            (type2 (type-fpconvert (type-apconvert type-arg2)))
            ((unless (or (and (type-arithmeticp type1)
                              (type-arithmeticp type2))
                         (and (type-case type1 :pointer)
                              (type-integerp type2))))
             (reterr msg)))
         (retok (type-fix type-arg1))))
      ((:asg-shl :asg-shr :asg-and :asg-xor :asg-ior)
       (b* (((unless (and (type-integerp type-arg1)
                          (type-integerp type-arg2)))
             (reterr msg)))
         (retok (type-fix type-arg1))))
      (t (prog2$ (impossible) (retmsg$ "")))))
  :guard-hints (("Goal" :in-theory (disable (:e tau-system))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-sizeof/alignof ((expr exprp) (type typep))
  :guard (or (expr-case expr :sizeof)
             (expr-case expr :alignof))
  :returns (mv (erp maybe-msgp) (type1 typep))
  :short "Validate a @('sizeof') operator applied to a type name,
          or an @('alignof') operator,
          given the type denoted by the argument type name."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('sizeof') operator applied to an type name
     requires a non-function complete type [C17:6.5.3.4/1].
     In our current approximate type system,
     we just exclude function types,
     but we do not have a notion of complete types yet.
     The result has type @('size_t') [C17:6.5.3.4/5],
     whose definition is implementation-defined,
     so for now we just return the unknown type;
     we will need to extend implementation environments
     with information about the definition of @('size_t')."))
  (b* (((reterr) (irr-type))
       ((when (type-case type :function))
        (retmsg$ "In the ~s0 type expression ~x1, ~
                  the argument ~x2 is a function type."
                 (case (expr-kind expr)
                   (:sizeof "sizeof")
                   (:alignof "_Alignof")
                   (t (impossible)))
                 (expr-fix expr)
                 (type-fix type))))
    (retok (type-unknown)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-cast ((expr exprp) (type-cast typep) (type-arg typep))
  :guard (expr-case expr :cast)
  :returns (mv (erp maybe-msgp) (type1 typep))
  :short "Validate a cast expression,
          given the type denoted by the type name
          and the type of the argument expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type name must denote the void type or a scalar type [C17:6.5.4/2].
     The expression must have scalar type [C17:6.5.4/2].
     Since scalar types involve pointers,
     we perform array-to-pointer and function-to-pointer conversions.
     The result is the type denoted by the type name."))
  (b* (((reterr) (irr-type))
       ((when (or (type-case type-cast :unknown)
                  (type-case type-arg :unknown)))
        (retok (type-unknown)))
       (type1-arg (type-fpconvert (type-apconvert type-cast)))
       ((unless (or (type-case type-cast :void)
                    (type-scalarp type-cast)))
        (retmsg$ "In the cast expression ~x0, the cast type is ~x1."
                 (expr-fix expr) (type-fix type-cast)))
       ((unless (type-scalarp type1-arg))
        (retmsg$ "In the cast expression ~x0, ~
                  the argument expression has type ~x1."
                 (expr-fix expr) (type-fix type-arg))))
    (retok (type-fix type-cast)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-cond ((expr exprp)
                    (type-test typep)
                    (type-then typep)
                    (type-else typep)
                    (ienv ienvp))
  :guard (expr-case expr :cond)
  :returns (mv (erp maybe-msgp) (type typep))
  :short "Validate a conditional expression,
          given types for its operands."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first operand must have scalar type [C17:6.5.15/2].
     In our currently approximate type system,
     the other two operands must have
     both arithmetic type,
     or both the same structure type,
     or both the union type,
     or both the void type,
     or both the pointer type,
     or one pointer type and the other operand a null pointer constant
     [C17:6.5.15/3].
     Currently, null pointer constants [C17:6.3.2.3/3] are approximated as any
     expression with an integer type.
     The type of the result is
     the one from the usual arithmetic converions
     in the first case,
     and the common type in the other cases
     [C17:6.5.15/5].
     Since pointers may be involved, we need to perform
     array-to-pointer and function-to-pointer conversions."))
  (b* (((reterr) (irr-type))
       ((when (or (type-case type-test :unknown)
                  (type-case type-then :unknown)
                  (type-case type-else :unknown)))
        (retok (type-unknown)))
       (type1 (type-fpconvert (type-apconvert type-test)))
       (type2 (type-fpconvert (type-apconvert type-then)))
       (type3 (type-fpconvert (type-apconvert type-else)))
       ((unless (type-scalarp type1))
        (retmsg$ "In the conditional expression ~x0, ~
                  the first operand has type ~x1."
                 (expr-fix expr) (type-fix type-test)))
       ((when (and (type-arithmeticp type2)
                   (type-arithmeticp type3)))
        (retok (type-uaconvert type2 type3 ienv)))
       ((when (and (type-case type2 :struct)
                   (type-case type3 :struct)))
        (if (type-equiv type2 type3)
            (retok type2)
          (retmsg$ "Struct types ~x0 and ~x1 are incompatible."
                   type2
                   type3)))
       ((when (and (type-case type2 :union)
                   (type-case type3 :union)))
        (retok (type-union)))
       ((when (if (type-case type2 :pointer)
                  (or (type-case type3 :pointer)
                      (expr-null-pointer-constp (expr-cond->else expr) type3))
                (and (if (expr-cond->then expr)
                         (expr-null-pointer-constp (expr-cond->then expr) type2)
                       (expr-null-pointer-constp (expr-cond->test expr) type2))
                     (type-case type3 :pointer))))
        (retok (type-pointer))))
    (retmsg$ "In the conditional expression ~x0, ~
              the second operand has type ~x1 ~
              and the third operand has type ~x2."
             (expr-fix expr) (type-fix type-then) (type-fix type-else)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-type-spec-list-residual ((tyspecs type-spec-listp))
  :guard (and (type-spec-list-unambp tyspecs)
              (consp tyspecs))
  :returns (mv (erp maybe-msgp) (type typep))
  :short "Validate a residual list of type specifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Type specifiers occur as elements of
     declaration specifiers
     (see grammar rule @('declaration-specifiers'))
     and specifier and qualifier lists
     (see grammar rule @('specifier-qualifier-list')).
     As we validate those two kinds of lists,
     when we encounter type specifiers that, like for example @('void'),
     uniquely determine a type,
     and must be the only type specifier occurring in the list,
     we perform all the necessary checks on type specifiers
     as part of validating those lists.")
   (xdoc::p
    "But when instead we encounter type specifiers that
     do not uniquely and solely determine a type,
     such as @('unsigned') and @('char'),
     we collect all of them and then we call this validation function
     to validate whether this residual sequence of type specifier
     determines a unique type or not.
     If it does not, it is an error,
     because every type specifier sub-sequence
     of a sequence of declaration specifiers
     or of a sequence of specifiers and qualifiers
     must denote a type.
     Here, `residual' refers not to the list of type specifiers,
     which are in fact all the ones occurring as sub-sequence,
     but to the fact that we perform the ``residual'' validation.")
   (xdoc::p
    "Here we accept all the lists of type specifiers in [C17:6.7.2/2]
     except for those that are singletons determining a type
     and that may not be part of longer sequences.")
   (xdoc::p
    "The GCC documentation says that @('__int128')
     can be used alone for signed,
     or accompanied by @('unsigned') for unsigned.
     But we also found it accompanied by @('signed')
     (and its underscore variations)
     in practical code,
     which seems indeed consistent with other types like @('signed int');
     so we accept all three variants.
     But for now we map all of them to the unknown type."))
  (b* (((reterr) (irr-type)))
    (cond
     ((type-spec-list-char-p tyspecs)
      (retok (type-char)))
     ((type-spec-list-signed-char-p tyspecs)
      (retok (type-schar)))
     ((type-spec-list-unsigned-char-p tyspecs)
      (retok (type-uchar)))
     ((or (type-spec-list-short-p tyspecs)
          (type-spec-list-signed-short-p tyspecs)
          (type-spec-list-short-int-p tyspecs)
          (type-spec-list-signed-short-int-p tyspecs))
      (retok (type-sshort)))
     ((or (type-spec-list-unsigned-short-p tyspecs)
          (type-spec-list-unsigned-short-int-p tyspecs))
      (retok (type-ushort)))
     ((or (type-spec-list-int-p tyspecs)
          (type-spec-list-signed-p tyspecs)
          (type-spec-list-signed-int-p tyspecs))
      (retok (type-sint)))
     ((or (type-spec-list-unsigned-p tyspecs)
          (type-spec-list-unsigned-int-p tyspecs))
      (retok (type-uint)))
     ((or (type-spec-list-long-p tyspecs)
          (type-spec-list-signed-long-p tyspecs)
          (type-spec-list-long-int-p tyspecs)
          (type-spec-list-signed-long-int-p tyspecs))
      (retok (type-slong)))
     ((or (type-spec-list-unsigned-long-p tyspecs)
          (type-spec-list-unsigned-long-int-p tyspecs))
      (retok (type-ulong)))
     ((or (type-spec-list-long-long-p tyspecs)
          (type-spec-list-signed-long-long-p tyspecs)
          (type-spec-list-long-long-int-p tyspecs)
          (type-spec-list-signed-long-long-int-p tyspecs))
      (retok (type-sllong)))
     ((or (type-spec-list-unsigned-long-long-p tyspecs)
          (type-spec-list-unsigned-long-long-int-p tyspecs))
      (retok (type-ullong)))
     ((type-spec-list-float-p tyspecs)
      (retok (type-float)))
     ((type-spec-list-double-p tyspecs)
      (retok (type-double)))
     ((type-spec-list-long-double-p tyspecs)
      (retok (type-ldouble)))
     ((type-spec-list-float-complex-p tyspecs)
      (retok (type-floatc)))
     ((type-spec-list-double-complex-p tyspecs)
      (retok (type-doublec)))
     ((type-spec-list-long-double-complex-p tyspecs)
      (retok (type-ldoublec)))
     ((or (type-spec-list-int128-p tyspecs)
          (type-spec-list-signed-int128-p tyspecs))
      (retok (type-unknown)))
     ((type-spec-list-unsigned-int128-p tyspecs)
      (retok (type-unknown)))
     (t (retmsg$ "The type specifier sequence ~x0 is invalid."
                 (type-spec-list-fix tyspecs)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-stor-spec-list ((storspecs stor-spec-listp)
                              (ident identp)
                              (type typep)
                              (fundefp booleanp)
                              (table valid-tablep))
  :returns (mv (erp maybe-msgp)
               (typedefp booleanp)
               (linkage linkagep)
               (lifetime? lifetime-optionp))
  :short "Validate a list of storage class specifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function is called on the sub-list of storage class specifiers
     of a list of declaration specifiers,
     after determining the identifier being declared and its type,
     which are both passed as input to this function,
     along with the current validation table.")
   (xdoc::p
    "Only a few sequences of storage class specifiers are allowed [C17:6.7.1/2],
     also depending on whether the declaration is in a block or file scope
     [C17:6.7.1/3],
     which we can see from the validation table.
     Each allowed sequence of storage class specifiers may determine
     that a @('typedef') name is being declared,
     or that an object or function is being declared,
     with a certain linkage and lifetime.
     So we return as results
     a flag saying that a @('typedef') name is being declared,
     a linkage,
     and an optional lifetime.
     We explain all the possibilities below,
     for each allowed sequence of storage class specifiers.")
   (xdoc::p
    "If the storage class specifier sequence is @('typedef'),
     a @('typedef') name is being declared,
     so we return @('t') as the @('typedef') flag result.
     This is the only case in which this result is @('t');
     in all other cases, that result is @('nil'),
     because in all other cases we are not declaring a @('typedef') name.
     A @('typedef') name (which is an identifier) has no linkage
     [C17:6.2.2/1] [C17:6.2.2/6].
     Since lifetime (i.e. storage duration) only applies to objects [C17:6.2.4/1],
     we return @('nil') as lifetime, i.e. no lifetime.")
   (xdoc::p
    "If the storage class specifier sequence is @('extern'),
     linkage may be external or not,
     based on whether there is already
     a declaration of the same identifiers in scope or not
     and whether that previous declaration specifies a linkage or not
     [C17:6.2.2/4].
     So we look up the identifier in the validation table.
     If nothing is found, then the linkage is external.
     If an object or function is found with external or internal linkage,
     then the linkage of the new declaration
     is the one of that object or function;
     the two declarations must refer to the same object or function,
     but we check elsewhere that the two declarations
     are consistent with each other.
     If an object or function is found with no linkage,
     or a @('typedef') is found (which has no linkage [C17:6.2.2/6]),
     or an enumeration constant is found (which has no linkage [C17:6.2.2/6]),
     then the linkage of the new declaration is external;
     the two declarations must refer to different entities.
     In any case, the linkage is always either internal or external.
     If the type is that of a function,
     there is no lifetime, which only applies to objects [C17:6.2.4/1].
     If the type is that of an object,
     the lifetime is static [C17:6.2.4/3],
     because as mentioned above the linkage is always internal or external.")
   (xdoc::p
    "If the storage class specifier sequence is
     @('extern _Thread_local') or @('_Thread_local extern'),
     then the type must not be that of a function [C17:6.7.1/4].
     The lifetime is thread [C17:6.2.4/4],
     while the linkage is determined as in the @('extern') case above.")
   (xdoc::p
    "If the storage class specifier sequence is @('static'),
     things differ whether the identifier is declared
     in the file scope or in a block scope.
     If we are in the file scope, the linkage is internal [C17:6.2.2/3].
     If we are in a block scope, it depends on whether
     we are declaring an object or a function.
     If it is an object, it has no linkage [C17:6.2.2/6],
     because it does not have @('extern').
     If it is a function it is an error [C17:6.7.1/7].
     The lifetime is absent (i.e. @('nil')) for a function,
     since lifetimes only apply to objects [C17:6.2.4/1];
     it is static otherwise [C17:6.2.4/3].")
   (xdoc::p
    "If the storage class specifier sequence is
     @('static _Thread_local') or @('_Thread_local static'),
     then the type must not be that of a function [C17:6.7.1/4].
     Linkage is determined as in the previous case.
     The lifetime is thread.")
   (xdoc::p
    "If the storage class specifier sequence is @('_Thread_local'),
     the type must not be one of a function [C17:6.7.1/4].
     Since we must have an object, the lifetime is thread.
     If we are in a block scope, it is an error,
     because in that case there must also be @('extern') or @('static')
     [C17:6.7.1/3].
     Since we cannot be in a block scope, we must be in the file scope.
     [C17:6.2.2] does not seem to specify the linkage for this case,
     perhaps because @('_Thread_local') was added at some point,
     but [C17:6.2.2] was not updated accordingly:
     [C17:6.2.2/5] specifies external linkage
     for the case of an object in a file scope without storage class specifiers,
     but this should be probably interpreted as
     including the @('_Thread_local') case,
     which makes sense, and is consistent with some clearer wording
     in the newly released C23 standard.")
   (xdoc::p
    "If the storage class specifier sequence is @('auto') or @('register'),
     we must not be in a file scope [C17:6.9/2];
     so we must be in a block scope.
     The type must not be one of a function.
     Thus, it has no linkage [C17:6.2.2/6].
     The lifetime is automatic [C17:6.2.4/5].")
   (xdoc::p
    "If there are no storage class specifiers (i.e. the sequence is empty),
     things differ based on
     whether the identifier declares an object or a function,
     and whether we are in the file scope or a block scope.
     If the type is that of a function,
     linkage is determined as if it had the @('extern') specifier [C17:6.2.2/5];
     in this case, there is no lifetime.
     For an object with file scope,
     the linkage is external [C17:6.2.2/5],
     and thus the lifetime is static [C17:6.2.4/3].
     For an object block scope, there is no linkage [C17:6.2.2/6],
     and the lifetime is automatic [C17:6.2.4/5].")
   (xdoc::p
    "We prove that if @('typedefp') is @('t')
     then @('lifetime?') is @('nil') and there is no linkage.
     We prove that if a function is being declared,
     then the linkage is always external or internal,
     and that the only possible sequences of storage class specifiers
     are @('extern'), @('static'), and nothing.
     We prove that if an object is declared in the file scope,
     then the linkage is always external or internal.")
   (xdoc::p
    "The @('fundefp') input is @('t') when this function is called on
     the storage class specifiers of a function definition.
     The reason is that, when this function is called in that situation,
     the validation table contains a block scope for the function body,
     but the storage class specifiers checked here are in the file scope:
     so checking the validation table to determine,
     for the purpose of validating the storage class specifiers,
     whether we are in a block or file scope,
     would give an incorrect result.
     So we use the @('fundefp') flag to adjust the check.
     This flag is @('nil') in all other situations."))
  (b* (((reterr) nil (irr-linkage) nil))
    (cond
     ((stor-spec-list-typedef-p storspecs)
      (retok t (linkage-none) nil))
     ((stor-spec-list-extern-p storspecs)
      (b* ((linkage
            (b* (((mv info? &) (valid-lookup-ord ident table))
                 ((unless info?)
                  (linkage-external))
                 ((unless (valid-ord-info-case info? :objfun))
                  (linkage-external))
                 (previous-linkage (valid-ord-info-objfun->linkage info?)))
              (if (linkage-case previous-linkage :none)
                  (linkage-external)
                previous-linkage)))
           (lifetime? (if (type-case type :function)
                          nil
                        (lifetime-static))))
        (retok nil linkage lifetime?)))
     ((stor-spec-list-extern-thread-p storspecs)
      (b* (((when (type-case type :function))
            (retmsg$ "The storage class specifier '_Thread_local' ~
                      cannot be used in the declaration of the function ~x0."
                     (ident-fix ident)))
           (linkage
            (b* (((mv info? &) (valid-lookup-ord ident table))
                 ((unless info?)
                  (linkage-external))
                 ((unless (valid-ord-info-case info? :objfun))
                  (linkage-external))
                 (previous-linkage (valid-ord-info-objfun->linkage info?)))
              (if (linkage-case previous-linkage :none)
                  (linkage-external)
                previous-linkage))))
        (retok nil linkage (lifetime-thread))))
     ((stor-spec-list-static-p storspecs)
      (b* ((block-scope-p (and (> (valid-table-num-scopes table) 1)
                               (not fundefp)))
           ((when (and block-scope-p
                       (type-case type :function)))
            (retmsg$ "The storage class specifier 'static' ~
                      cannot be used in the declaration of the function ~x0."
                     (ident-fix ident)))
           (linkage (if block-scope-p
                        (linkage-none)
                      (linkage-internal)))
           (lifetime? (if (type-case type :function)
                          nil
                        (lifetime-static))))
        (retok nil linkage lifetime?)))
     ((stor-spec-list-static-thread-p storspecs)
      (b* (((when (type-case type :function))
            (retmsg$ "The storage class specifier '_Thread_local' ~
                      cannot be used in the declaration of the function ~x0."
                     (ident-fix ident)))
           (block-scope-p (and (> (valid-table-num-scopes table) 1)
                               (not fundefp)))
           (linkage (if block-scope-p
                        (linkage-none)
                      (linkage-internal)))
           (lifetime? (lifetime-thread)))
        (retok nil linkage lifetime?)))
     ((stor-spec-list-thread-p storspecs)
      (b* (((when (type-case type :function))
            (retmsg$ "The storage class specifier '_Thread_local' ~
                      cannot be used in the declaration of the function ~x0."
                     (ident-fix ident)))
           ((when (and (> (valid-table-num-scopes table) 1)
                       (not fundefp)))
            (retmsg$ "The storage class specifier '_Thread_local' ~
                      cannot be used in a block scope ~
                      without 'extern' or 'static', ~
                      for the declaration of the object ~x0."
                     (ident-fix ident))))
        (retok nil (linkage-external) (lifetime-thread))))
     ((or (stor-spec-list-auto-p storspecs)
          (stor-spec-list-register-p storspecs))
      (b* (((when (type-case type :function))
            (retmsg$ "The storage class specifier '~s0' ~
                      cannot be used in the declaration of the function ~x1."
                     (if (stor-spec-list-auto-p storspecs)
                         "auto"
                       "register")
                     (ident-fix ident)))
           ((unless (and (> (valid-table-num-scopes table) 1)
                         (not fundefp)))
            (retmsg$ "The storage class specifier '~s0' ~
                      cannot be used in the file scope, for identifier ~x1."
                     (if (stor-spec-list-auto-p storspecs)
                         "auto"
                       "register")
                     (ident-fix ident))))
        (retok nil (linkage-none) (lifetime-auto))))
     ((endp storspecs)
      (if (type-case type :function)
          (b* (((mv info? &) (valid-lookup-ord ident table))
               ((unless info?)
                (retok nil (linkage-external) nil))
               ((unless (valid-ord-info-case info? :objfun))
                (retok nil (linkage-external) nil))
               (previous-linkage (valid-ord-info-objfun->linkage info?)))
            (if (linkage-case previous-linkage :none)
                (retok nil (linkage-external) nil)
              (retok nil previous-linkage nil)))
        (if (and (> (valid-table-num-scopes table) 1)
                 (not fundefp))
            (retok nil (linkage-none) (lifetime-auto))
          (retok nil (linkage-external) (lifetime-static)))))
     (t (retmsg$ "The storage class specifier sequence ~x0 is invalid."
                 (stor-spec-list-fix storspecs)))))
  :hooks (:fix)

  ///

  (defret no-lifetime-of-valid-stor-spec-list-when-typedef
    (implies typedefp
             (not lifetime?)))

  (defret no-linkage-of-valid-stor-spec-list-when-typedef
    (implies typedefp
             (equal (linkage-kind linkage) :none)))

  (defret ext/int-linkage-of-valid-stor-spec-when-function
    (implies (and (not erp)
                  (not typedefp)
                  (type-case type :function))
             (not (equal (linkage-kind linkage)
                         :none))))

  (defret ext/int-linkage-of-valid-stor-spec-list-when-file-object
    (implies (and (not erp)
                  (not typedefp)
                  (not (type-case type :function))
                  (equal (valid-table-num-scopes table) 1))
             (not (equal (linkage-kind linkage)
                         :none))))

  (defret lifetime-of-valid-stor-spec-when-object
    (implies (and (not erp)
                  (not typedefp)
                  (not (type-case type :function)))
             lifetime?))

  (defret extern/static/none-when-valid-stor-spec-list-function
    (implies (and (not erp)
                  (not typedefp)
                  (type-case type :function))
             (or (stor-spec-list-extern-p storspecs)
                 (stor-spec-list-static-p storspecs)
                 (endp storspecs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines valid-exprs/decls/stmts
  :short "Validate expressions, declarations, statements,
          and related artifacts."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since we currently have an approximate model of types,
     with the `unknown type' among them (see @(tsee type)),
     wherever a certain kind of type is required (e.g. an integer type),
     we also need to allow the unknown type,
     because that could the required kind of type.
     Our currently approximate validator must not reject valid programs,
     because it needs to deal with any practical programs we encounter.
     Eventually, when we refine our validator and our model of types
     to no longer be approximate and include the unknown type,
     we will rescind this extra allowance for the unknown type.")
   (xdoc::p
    "Each validation function takes and returns
     an abstract syntax entity (of the appropriate kind)
     and returns a transformed one (of the same kind).
     Currently there is no change,
     but soon we will be adding information to the abstract syntax."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-expr ((expr exprp)
                      (table valid-tablep)
                      (uid uidp)
                      (ienv ienvp))
    :guard (expr-unambp expr)
    :returns (mv (erp maybe-msgp)
                 (new-expr exprp)
                 (type typep)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "If validation is successful,
       we return the type of the expression,
       the set of types returned by @('return') statements in the expression,
       and a possibly updated validation table.
       The reason for the set of @('return') types
       is that, as a GCC extension, an expression may consist of a statement,
       and the validation of statements involves sets of @('return') types:
       see @(tsee valid-stmt).
       In case of successful validation,
       we also return a possibly enriched expression:
       the enrichment consists of a type added as
       information for identifier expression;
       that is the type of the identifier expression,
       calculated by the validator.")
     (xdoc::p
      "For now we do not distinguish lvalues [C17:6.3.2.1/1].
       To do that, we will introduce a richer notion of expression type
       that includes a type and also
       an indication of whether the expression is an lvalue;
       we will also perform lvalue conversion where needed.
       This is already done in @(see c::static-semantics),
       for the subset of C that is formalized.")
     (xdoc::p
      "We use separate functions to validate the various kinds of expressions,
       to minimize case splits in the mutually recursive clique of functions.
       But we need to calculate types for sub-expressions recursively here,
       and pass the types to those separate functions.")
     (xdoc::p
      "Expressions without subexpressions return
       the empty set of @('return') types.
       Other expressions return the union of the sets
       obtained from validating the sub-constructs.")
     (xdoc::p
      "To validate a compound literal, first we validate the type name,
       obtaining a type if that validation is successful.
       Then we validate the initializers with optional designations,
       passing the type because in general their validation depends on that;
       however, in our currently approximate type system,
       all the information we need back from
       the validation of the initializers with optional designations
       is the possibly updated validation table.
       The type of the compound literal is the one denoted by the type name.
       We also need to pass an indication of
       the storage duration (i.e. lifetime) of the object,
       which is either static or automatic,
       based on whether the compound literal occurs
       outside or inside the body of a function [C17:6.5.2.5/5],
       which we can see based on whether
       the number of scopes in the validation table is 1 or not
       (recall that this number is never 0).")
     (xdoc::p
      "In a conditional expression, the second operand may be absent;
       this is a GCC extension.
       However, for validation, we normalize the situation
       by replicating the type of the first operand for the second operand,
       when there is no second operand,
       according to the semantics of the absence of the second operand.")
     (xdoc::p
      "For the comma operator, we validate both sub-expressions,
       and the resulting type is the one of the second sub-expression
       [C17:6.5.17/2].")
     (xdoc::p
      "For a statement expression, we push a new scope for the block
       and we validate the block items. We then pop the scope.
       If a type is returned, that is the type of the expression.
       Otherwise, the expression has type @('void'),
       as described in the GCC documentation of statement expressions.")
     (xdoc::p
      "The GCC extension @('__builtin_types_compatible_p')
       is validated by validating its argument type names.
       The result is @('signed int'), according to the GCC manual.")
     (xdoc::p
      "For the GCC extension @('__builtin_offsetof'),
       for now we just validate
       its component type names and expressions (if any),
       but without checking that the member designators are valid;
       for that, we need a more refined type system.
       The result has type @('size_t') [C17:7.19],
       whose definition is implementation-dependent,
       and thus for now we return the unknown type."))
    (b* (((reterr) (irr-expr) (irr-type) nil (irr-valid-table) (irr-uid))
         (uid (uid-fix uid)))
      (expr-case
       expr
       :ident (b* (((erp type linkage uid) (valid-var expr.ident table))
                   (info (make-var-info :type type
                                        :linkage linkage
                                        :uid uid)))
                (retok (make-expr-ident :ident expr.ident
                                        :info info)
                       type
                       nil
                       (valid-table-fix table)
                       uid))
       :const (b* (((erp const type) (valid-const expr.const table ienv)))
                (retok (expr-const const)
                       type
                       nil
                       (valid-table-fix table)
                       uid))
       :string (b* (((erp type) (valid-stringlit-list expr.strings ienv)))
                 (retok (expr-fix expr)
                        type
                        nil
                        (valid-table-fix table)
                        uid))
       :paren (b* (((erp new-inner type types table uid)
                    (valid-expr expr.inner table uid ienv)))
                (retok (expr-paren new-inner) type types table uid))
       :gensel (b* (((erp new-control type-control types-control table uid)
                     (valid-expr expr.control table uid ienv))
                    ((erp new-assocs type-alist types-assoc table uid)
                     (valid-genassoc-list expr.assocs table uid ienv))
                    ((erp type) (valid-gensel expr type-control type-alist)))
                 (retok (make-expr-gensel :control new-control
                                          :assocs new-assocs)
                        type
                        (set::union types-control types-assoc)
                        table
                        uid))
       :arrsub (b* (((erp new-arg1 type-arg1 types-arg1 table uid)
                     (valid-expr expr.arg1 table uid ienv))
                    ((erp new-arg2 type-arg2 types-arg2 table uid)
                     (valid-expr expr.arg2 table uid ienv))
                    ((erp type) (valid-arrsub expr type-arg1 type-arg2)))
                 (retok (make-expr-arrsub :arg1 new-arg1 :arg2 new-arg2)
                        type
                        (set::union types-arg1 types-arg2)
                        table
                        uid))
       :funcall (b* (((erp new-fun type-fun types-fun table uid)
                      (valid-expr expr.fun table uid ienv))
                     ((erp new-args types-arg rtypes-arg table uid)
                      (valid-expr-list expr.args table uid ienv))
                     ((erp type) (valid-funcall expr type-fun types-arg)))
                  (retok (make-expr-funcall :fun new-fun :args new-args)
                         type
                         (set::union types-fun rtypes-arg)
                         table
                         uid))
       :member (b* (((erp new-arg type-arg types-arg table uid)
                     (valid-expr expr.arg table uid ienv))
                    ((erp type) (valid-member expr type-arg)))
                 (retok (make-expr-member :arg new-arg :name expr.name)
                        type
                        types-arg
                        table
                        uid))
       :memberp (b* (((erp new-arg type-arg types-arg table uid)
                      (valid-expr expr.arg table uid ienv))
                     ((erp type) (valid-memberp expr type-arg)))
                  (retok (make-expr-memberp :arg new-arg :name expr.name)
                         type
                         types-arg
                         table
                         uid))
       :complit (b* (((erp new-type type types-type table uid)
                      (valid-tyname expr.type table uid ienv))
                     ((when (type-case type :function))
                      (retmsg$ "The type of the compound literal ~x0 ~
                                is a function type."
                               (expr-fix expr)))
                     ((when (type-case type :void))
                      (retmsg$ "The type of the compound literal ~x0 ~
                                is void."
                               (expr-fix expr)))
                     (lifetime (if (> (valid-table-num-scopes table) 1)
                                   (lifetime-auto)
                                 (lifetime-static)))
                     ((erp new-elems types-elems table uid)
                      (valid-desiniter-list
                       expr.elems type lifetime table uid ienv)))
                  (retok (make-expr-complit :type new-type
                                            :elems new-elems
                                            :final-comma expr.final-comma)
                         type
                         (set::union types-type types-elems)
                         table
                         uid))
       :unary (b* (((erp new-arg type-arg types-arg table uid)
                    (valid-expr expr.arg table uid ienv))
                   ((erp type) (valid-unary expr expr.op type-arg ienv))
                   (info (make-expr-unary-info :type type)))
                (retok (make-expr-unary :op expr.op
                                        :arg new-arg
                                        :info info)
                       type
                       types-arg
                       table
                       uid))
       :sizeof (b* (((erp new-type type types table uid)
                     (valid-tyname expr.type table uid ienv))
                    ((erp type1) (valid-sizeof/alignof expr type)))
                 (retok (expr-sizeof new-type) type1 types table uid))
       :alignof (b* (((erp new-type type types table uid)
                      (valid-tyname expr.type table uid ienv))
                     ((erp type1) (valid-sizeof/alignof expr type)))
                  (retok (make-expr-alignof :type new-type
                                            :uscores expr.uscores)
                         type1
                         types
                         table
                         uid))
       :cast (b* (((erp new-type type-cast types-cast table uid)
                   (valid-tyname expr.type table uid ienv))
                  ((erp new-arg type-arg types-arg table uid)
                   (valid-expr expr.arg table uid ienv))
                  ((erp type) (valid-cast expr type-cast type-arg)))
               (retok (make-expr-cast :type new-type :arg new-arg)
                      type
                      (set::union types-cast types-arg)
                      table
                      uid))
       :binary (b* (((erp new-arg1 type-arg1 types-arg1 table uid)
                     (valid-expr expr.arg1 table uid ienv))
                    ((erp new-arg2 type-arg2 types-arg2 table uid)
                     (valid-expr expr.arg2 table uid ienv))
                    ((erp type)
                     (valid-binary expr expr.op type-arg1 type-arg2 ienv))
                    (info (make-expr-binary-info :type type)))
                 (retok (make-expr-binary :op expr.op
                                          :arg1 new-arg1
                                          :arg2 new-arg2
                                          :info info)
                        type
                        (set::union types-arg1 types-arg2)
                        table
                        uid))
       :cond (b* (((erp new-test type-test types-test table uid)
                   (valid-expr expr.test table uid ienv))
                  ((erp new-then type-then? types-then table uid)
                   (valid-expr-option expr.then table uid ienv))
                  (type-then (or type-then? type-test))
                  ((erp new-else type-else types-else table uid)
                   (valid-expr expr.else table uid ienv))
                  ((erp type)
                   (valid-cond expr type-test type-then type-else ienv)))
               (retok (make-expr-cond :test new-test
                                      :then new-then
                                      :else new-else)
                      type
                      (set::union types-test (set::union types-then types-else))
                      table
                      uid))
       :comma (b* (((erp new-first & types1 table uid)
                    (valid-expr expr.first table uid ienv))
                   ((erp new-next type types2 table uid)
                    (valid-expr expr.next table uid ienv)))
                (retok (make-expr-comma :first new-first :next new-next)
                       type
                       (set::union types1 types2)
                       table
                       uid))
       :stmt (b* ((table (valid-push-scope table))
                  ((erp new-items types type? table uid)
                   (valid-block-item-list expr.items table uid ienv))
                  (table (valid-pop-scope table))
                  (type (or type? (type-void))))
               (retok (expr-stmt new-items) type types table uid))
       :tycompat (b* (((erp new-type1 & types1 table uid)
                       (valid-tyname expr.type1 table uid ienv))
                      ((erp new-type2 & types2 table uid)
                       (valid-tyname expr.type2 table uid ienv)))
                   (retok (make-expr-tycompat :type1 new-type1
                                              :type2 new-type2)
                          (type-sint)
                          (set::union types1 types2)
                          table
                          uid))
       :offsetof (b* (((erp new-type & types table uid)
                       (valid-tyname expr.type table uid ienv))
                      ((erp new-member more-types table uid)
                       (valid-member-designor
                         expr.member table uid ienv)))
                   (retok (make-expr-offsetof :type new-type
                                              :member new-member)
                          (type-unknown)
                          (set::union types more-types)
                          table
                          uid))
       :va-arg (b* (((erp new-list & list-types table uid)
                     (valid-expr expr.list table uid ienv))
                    ((erp new-type & type-types table uid)
                     (valid-tyname expr.type table uid ienv)))
                 (retok (make-expr-va-arg :list new-list :type new-type)
                        (type-unknown)
                        (set::union list-types type-types)
                        table
                        uid))
       :extension (b* (((erp new-expr type types table uid)
                        (valid-expr expr.expr table uid ienv)))
                    (retok (expr-extension new-expr)
                           type
                           types
                           table
                           uid))
       :otherwise (prog2$ (impossible) (retmsg$ ""))))
    :measure (expr-count expr))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-expr-list ((exprs expr-listp)
                           (table valid-tablep)
                           (uid uidp)
                           (ienv ienvp))
    :guard (expr-list-unambp exprs)
    :returns (mv (erp maybe-msgp)
                 (new-exprs expr-listp)
                 (types type-listp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of expressions."
    :long
    (xdoc::topstring
     (xdoc::p
      "We validate all the expressions, one after the other,
       and we return the resulting types, in the same order.
       We also return the union of all the @('return') types.
       We also return a possibly updated validation table."))
    (b* (((reterr) nil nil nil (irr-valid-table) (irr-uid))
         ((when (endp exprs))
          (retok nil nil nil (valid-table-fix table) (uid-fix uid)))
         ((erp new-expr type return-types table uid)
          (valid-expr (car exprs) table uid ienv))
         ((erp new-exprs types more-return-types table uid)
          (valid-expr-list (cdr exprs) table uid ienv)))
      (retok (cons new-expr new-exprs)
             (cons type types)
             (set::union return-types more-return-types)
             table
             uid))
    :measure (expr-list-count exprs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-expr-option ((expr? expr-optionp)
                             (table valid-tablep)
                             (uid uidp)
                             (ienv ienvp))
    :guard (expr-option-unambp expr?)
    :returns (mv (erp maybe-msgp)
                 (new-expr? expr-optionp)
                 (type? type-optionp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an optional expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "If there is no expression,
       we return @('nil') as the optional type,
       we return the empty set of @('return') types,
       and the validation table unchanged."))
    (b* (((reterr) nil nil nil (irr-valid-table) (irr-uid)))
      (expr-option-case
       expr?
       :some (valid-expr expr?.val table uid ienv)
       :none (retok nil
                    nil
                    nil
                    (valid-table-fix table)
                    (uid-fix uid))))
    :measure (expr-option-count expr?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-const-expr ((cexpr const-exprp)
                            (table valid-tablep)
                            (uid uidp)
                            (ienv ienvp))
    :guard (const-expr-unambp cexpr)
    :returns (mv (erp maybe-msgp)
                 (new-cexpr const-exprp)
                 (type typep)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a constant expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "Besides being valid expressions,
       constant expression must satisfy other requirements [C17:6.6].
       Fow now we do not check these requirements,
       but when we do we may need to extend this validation function
       to return not only a type but also a value,
       namely the value of the constant expression."))
    (b* (((reterr)
          (irr-const-expr) (irr-type) nil (irr-valid-table) (irr-uid))
         ((erp new-expr type types table uid)
          (valid-expr (const-expr->expr cexpr) table uid ienv)))
      (retok (const-expr new-expr) type types table uid))
    :measure (const-expr-count cexpr))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-const-expr-option ((cexpr? const-expr-optionp)
                                   (table valid-tablep)
                                   (uid uidp)
                                   (ienv ienvp))
    :guard (const-expr-option-unambp cexpr?)
    :returns (mv (erp maybe-msgp)
                 (new-cexpr? const-expr-optionp)
                 (type? type-optionp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an optional constant expression."
    :long
    (xdoc::topstring
     (xdoc::p
      "If there is no constant expression,
       we return @('nil') as the optional type,
       we return the empty set of @('return') types,
       and the validation table unchanged."))
    (b* (((reterr) nil nil nil (irr-valid-table) (irr-uid)))
      (const-expr-option-case
       cexpr?
       :some (valid-const-expr cexpr?.val table uid ienv)
       :none (retok nil
                    nil
                    nil
                    (valid-table-fix table)
                    (uid-fix uid))))
    :measure (const-expr-option-count cexpr?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-genassoc ((genassoc genassocp)
                          (table valid-tablep)
                          (uid uidp)
                          (ienv ienvp))
    :guard (genassoc-unambp genassoc)
    :returns (mv (erp maybe-msgp)
                 (new-genassoc genassocp)
                 (tyname-type type-optionp)
                 (expr-type typep)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a generic association."
    :long
    (xdoc::topstring
     (xdoc::p
      "If the generic association has a type name,
       we validate it and return the type that it denotes.
       If the generic association has @('default'),
       we return @('nil') as the @('tyname-type') result.
       Either way, we validate the expression, and return its type."))
    (b* (((reterr)
          (irr-genassoc) nil (irr-type) nil (irr-valid-table) (irr-uid)))
      (genassoc-case
       genassoc
       :type (b* (((erp new-type tyname-type tyname-types table uid)
                   (valid-tyname genassoc.type table uid ienv))
                  ((erp new-expr expr-type expr-types table uid)
                   (valid-expr genassoc.expr table uid ienv)))
               (retok (make-genassoc-type :type new-type :expr new-expr)
                      tyname-type
                      expr-type
                      (set::union tyname-types expr-types)
                      table
                      uid))
       :default (b* (((erp new-expr expr-type expr-types table uid)
                      (valid-expr genassoc.expr table uid ienv)))
                  (retok (genassoc-default new-expr)
                         nil
                         expr-type
                         expr-types
                         table
                         uid))))
    :measure (genassoc-count genassoc))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-genassoc-list ((genassocs genassoc-listp)
                               (table valid-tablep)
                               (uid uidp)
                               (ienv ienvp))
    :guard (genassoc-list-unambp genassocs)
    :returns (mv (erp maybe-msgp)
                 (new-genassocs genassoc-listp)
                 (type-alist type-option-type-alistp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of generic associations."
    :long
    (xdoc::topstring
     (xdoc::p
      "We validate each generic association, one after the other.
       We put the calculated types (and optional types) into an alist,
       which we return.
       There may be repeated keys in the alist: it is a feature,
       so we can separately check their uniqueness."))
    (b* (((reterr) nil nil nil (irr-valid-table) (irr-uid))
         ((when (endp genassocs))
          (retok nil nil nil (valid-table-fix table) (uid-fix uid)))
         ((erp new-genassoc tyname-type? expr-type types table uid)
          (valid-genassoc (car genassocs) table uid ienv))
         ((erp new-genassocs type-alist more-types table uid)
          (valid-genassoc-list (cdr genassocs) table uid ienv)))
      (retok (cons new-genassoc new-genassocs)
             (acons tyname-type? expr-type type-alist)
             (set::union types more-types)
             table
             uid))
    :measure (genassoc-list-count genassocs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-member-designor ((memdesign member-designorp)
                                 (table valid-tablep)
                                 (uid uidp)
                                 (ienv ienvp))
    :guard (member-designor-unambp memdesign)
    :returns (mv (erp maybe-msgp)
                 (new-memdesign member-designorp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a member designator."
    (b* (((reterr) (irr-member-designor) nil (irr-valid-table) (irr-uid)))
      (member-designor-case
       memdesign
       :ident (retok (member-designor-fix memdesign)
                     nil
                     (valid-table-fix table)
                     (uid-fix uid))
       :dot (b* (((erp new-member types table uid)
                  (valid-member-designor
                    memdesign.member table uid ienv)))
              (retok (make-member-designor-dot :member new-member
                                               :name memdesign.name)
                     types
                     table
                     uid))
       :sub (b* (((erp new-member types table uid)
                  (valid-member-designor
                    memdesign.member table uid ienv))
                 ((erp new-expr & more-types table uid)
                  (valid-expr memdesign.index table uid ienv)))
              (retok (make-member-designor-sub :member new-member
                                               :index new-expr)
                     (set::union types more-types)
                     table
                     uid))))
    :measure (member-designor-count memdesign))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-type-spec ((tyspec type-specp)
                           (type? type-optionp)
                           (tyspecs type-spec-listp)
                           (table valid-tablep)
                           (uid uidp)
                           (ienv ienvp))
    :guard (and (type-spec-unambp tyspec)
                (type-spec-list-unambp tyspecs)
                (not (and type? tyspecs)))
    :returns (mv (erp maybe-msgp)
                 (new-tyspec type-specp)
                 (new-type? type-optionp)
                 (new-tyspecs type-spec-listp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a type specifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "Type specifiers are used to specify types, as described in [C17:6.7.2/2].
       Certain type specifiers individually specify a type,
       and there cannot be other type specifiers;
       an example is @('void').
       Other type specifiers may individually specify a type,
       but they may be also combined with other type specifiers
       to specify a different type;
       an example is @('signed').
       The type specifier @('_Complex') does not individually specify any type,
       and must be always combined with other type specifiers.")
     (xdoc::p
      "Given these possibilities,
       our approach is to validate type specifiers in order,
       while going through the declaration specifiers,
       or the specifier and qualifier lists,
       where they occur.
       As we go through them, we thread through two pieces of information:
       an optional type,
       non-@('nil') when a type has been definitely determined,
       and a list of type specifiers encountered so far.
       These two cannot be non-@('nil') at the same time, as the guard requires:
       if a type has been determined,
       there is no need to keep track of the type specifiers so far;
       and if we are keeping track of the type specifiers so far,
       we must not have determined a type yet.")
     (xdoc::p
      "Initially,
       the optional type and the list of type specifiers are both @('nil'),
       because we neither have encountered any type specifiers
       nor determined a type.
       If we encounter a type specifier like @('void')
       that individually denotes a type,
       we ensure that no other type specifiers were encountered before,
       and we determine the type.
       Once a type is determined, any type specifier will cause an error.
       We may get at the end without a determined type yet,
       but we will have the list of all the type specifiers,
       which is used, in another validation function,
       to determined the type if any.")
     (xdoc::p
      "Our current type system does not model atomic types,
       so for an atomic type we validate the type name
       and we regard the atomic type as denoting the same type.")
     (xdoc::p
      "For a structure or union or enumeration type specifier,
       we recursively validate their sub-structures,
       and the type is determined in all cases.")
     (xdoc::p
      "For @('typedef') names,
       we look up the type definition in the validation table.
       If no such entry exists in the table, validation fails.
       Otherwise, we return the type in the table entry
       as the one denoted by the @('typedef') name.
       The latter is an important point, because it means that
       we always fully expand @('typedef') names
       to their @('typedef')-name-free types
       (recall that @(tsee type) has no case for @('typedef') names).
       In a translation unit, no forward references are allowed,
       so the first @('typedef') (if any) cannot refer to others;
       later @('typedef')s may refer to previous ones,
       but since we expand their definientia through this table lookup,
       we effectively always recursively expand all @('typedef')s.
       This may be exactly what is needed for validation,
       but we will revisit this choice if needed.")
     (xdoc::p
      "For now, for simplicity, we regard
       all the type specifiers that are GCC extensions
       to determine the unknown type;
       except for an empty structure type specifier,
       which determines the structure type.
       The @('__int128') may be preceded by @('unsigned'),
       according to the GCC documentation;
       we found, in practical code,
       that it can also be preceded by @('signed') and its underscore variants;
       so @('__int128') alone does not determine a type,
       and we use @(tsee valid-type-spec-list-residual)
       to determine the type, if any, as done in other cases."))
    (b* (((reterr) (irr-type-spec) nil nil nil (irr-valid-table) (irr-uid))
         (uid (uid-fix uid))
         ((when type?)
          (retmsg$ "Since the type ~x0 has been determined, ~
                    there must be no more type specifiers, ~
                    but ~x1 follows instead."
                   (type-option-fix type?) (type-spec-fix tyspec)))
         (same-table (valid-table-fix table))
         (ext-tyspecs (rcons (type-spec-fix tyspec)
                             (type-spec-list-fix tyspecs)))
         (msg-bad-preceding (msg$ "The type specifier ~x0 ~
                                   must not be preceded by ~x1."
                                  (type-spec-fix tyspec)
                                  (type-spec-list-fix tyspecs))))
      (type-spec-case
       tyspec
       :void (if (endp tyspecs)
                 (retok (type-spec-void) (type-void) nil nil same-table uid)
               (reterr msg-bad-preceding))
       :char (retok (type-spec-char) nil ext-tyspecs nil same-table uid)
       :short (retok (type-spec-short) nil ext-tyspecs nil same-table uid)
       :int (retok (type-spec-int) nil ext-tyspecs nil same-table uid)
       :long (retok (type-spec-long) nil ext-tyspecs nil same-table uid)
       :float (retok (type-spec-float) nil ext-tyspecs nil same-table uid)
       :double (retok (type-spec-double) nil ext-tyspecs nil same-table uid)
       :signed (retok (type-spec-signed tyspec.uscores)
                      nil
                      ext-tyspecs
                      nil
                      same-table
                      uid)
       :unsigned (retok (type-spec-unsigned)
                        nil
                        ext-tyspecs
                        nil
                        same-table
                        uid)
       :bool (if (endp tyspecs)
                 (retok (type-spec-bool) (type-bool) nil nil same-table uid)
               (reterr msg-bad-preceding))
       :complex (retok (type-spec-complex) nil ext-tyspecs nil same-table uid)
       :atomic (b* (((unless (endp tyspecs)) (reterr msg-bad-preceding))
                    ((erp new-type type types table uid)
                     (valid-tyname tyspec.type table uid ienv)))
                 (retok (type-spec-atomic new-type)
                        type
                        nil
                        types
                        table
                        uid))
       :struct (b* (((unless (endp tyspecs)) (reterr msg-bad-preceding))
                    ((erp new-spec types table uid)
                     (valid-struni-spec
                       tyspec.spec table uid ienv))
                    ((struni-spec tyspec.spec) tyspec.spec))
                 (retok (type-spec-struct new-spec)
                        (type-struct tyspec.spec.name?)
                        nil
                        types
                        table
                        uid))
       :union (b* (((unless (endp tyspecs)) (reterr msg-bad-preceding))
                   ((erp new-spec types table uid)
                    (valid-struni-spec tyspec.spec table uid ienv)))
                (retok (type-spec-union new-spec)
                       (type-union)
                       nil
                       types
                       table
                       uid))
       :enum (b* (((unless (endp tyspecs)) (reterr msg-bad-preceding))
                  ((erp new-spec types table uid)
                   (valid-enumspec tyspec.spec table uid ienv)))
               (retok (type-spec-enum new-spec)
                      (type-enum)
                      nil
                      types
                      table
                      uid))
       :typedef (b* (((unless (endp tyspecs))
                      (reterr msg-bad-preceding))
                     ((mv info? -)
                      (valid-lookup-ord tyspec.name table))
                     ((unless info?)
                      (retmsg$ "The identifier ~x0 is not an in-scope ~
                                ordinary identifier."
                               (ident->unwrap tyspec.name))))
                  (valid-ord-info-case
                   info?
                   :typedef (retok (type-spec-typedef tyspec.name)
                                   info?.def
                                   nil
                                   nil
                                   same-table
                                   uid)
                   :otherwise (retmsg$ "The identifier ~x0 does not ~
                                        represent a typedef.")))
       :int128 (retok (make-type-spec-int128 :uscoret tyspec.uscoret)
                      nil
                      ext-tyspecs
                      nil
                      same-table
                      uid)
       :float32 (if (endp tyspecs)
                    (retok (type-spec-float32)
                           (type-unknown)
                           nil
                           nil
                           same-table
                           uid)
                  (reterr msg-bad-preceding))
       :float32x (if (endp tyspecs)
                     (retok (type-spec-float32x)
                            (type-unknown)
                            nil
                            nil
                            same-table
                            uid)
                   (reterr msg-bad-preceding))
       :float64 (if (endp tyspecs)
                    (retok (type-spec-float64)
                           (type-unknown)
                           nil
                           nil
                           same-table
                           uid)
                  (reterr msg-bad-preceding))
       :float64x (if (endp tyspecs)
                     (retok (type-spec-float64x)
                            (type-unknown)
                            nil
                            nil
                            same-table
                            uid)
                   (reterr msg-bad-preceding))
       :float128 (if (endp tyspecs)
                     (retok (type-spec-float128)
                            (type-unknown)
                            nil
                            nil
                            same-table
                            uid)
                   (reterr msg-bad-preceding))
       :float128x (if (endp tyspecs)
                      (retok (type-spec-float128x)
                             (type-unknown)
                             nil
                             nil
                             same-table
                             uid)
                    (reterr msg-bad-preceding))
       :builtin-va-list (if (endp tyspecs)
                            (retok (type-spec-builtin-va-list)
                                   (type-unknown)
                                   nil
                                   nil
                                   same-table
                                   uid)
                          (reterr msg-bad-preceding))
       :struct-empty (if (endp tyspecs)
                         (retok (type-spec-struct-empty tyspec.name?)
                                (type-struct tyspec.name?)
                                nil
                                nil
                                same-table
                                uid)
                       (reterr msg-bad-preceding))
       :typeof-expr (if (endp tyspecs)
                        (retok (type-spec-fix tyspec)
                               (type-unknown)
                               nil
                               nil
                               same-table
                               uid)
                      (reterr msg-bad-preceding))
       :typeof-type (if (endp tyspecs)
                        (retok (type-spec-fix tyspec)
                               (type-unknown)
                               nil
                               nil
                               same-table
                               uid)
                      (reterr msg-bad-preceding))
       :auto-type (if (endp tyspecs)
                      (retok (type-spec-fix tyspec)
                             (type-unknown)
                             nil
                             nil
                             same-table
                             uid)
                    (reterr msg-bad-preceding))
       :otherwise (prog2$ (impossible) (retmsg$ ""))))
    :measure (type-spec-count tyspec)

    ///

    (defret type-spec-list-unambp-of-valid-type-spec
      (type-spec-list-unambp new-tyspecs)
      :hyp (type-spec-list-unambp tyspecs)
      :hints
      (("Goal" :expand (valid-type-spec tyspec type? tyspecs table uid ienv))))

    (defret not-type-and-type-specs-of-valid-type-spec
      (not (and new-type? new-tyspecs))
      :hints
      (("Goal"
        :expand (valid-type-spec tyspec type? tyspecs table uid ienv)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-spec/qual ((specqual spec/qual-p)
                           (type? type-optionp)
                           (tyspecs type-spec-listp)
                           (table valid-tablep)
                           (uid uidp)
                           (ienv ienvp))
    :guard (and (spec/qual-unambp specqual)
                (type-spec-list-unambp tyspecs)
                (not (and type? tyspecs)))
    :returns (mv (erp maybe-msgp)
                 (new-specqual spec/qual-p)
                 (new-type? type-optionp)
                 (new-tyspecs type-spec-listp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a specifier or qualifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "For now we ignore type qualifiers [C17:6.7.3],
       as they do not have any impact on our approximate type system.
       We validate alignment specifiers (in a separate validation function),
       but make no use of them in our approximate type system.
       Thus, the validation of a specifier or qualifier
       returns the same results as
       the validation of a type specifier (see @(tsee valid-type-spec)).
       For now we also skip over attributes completely;
       see the ABNF grammar for @('specifier-qualifier-list')."))
    (b* (((reterr) (irr-spec/qual) nil nil nil (irr-valid-table) (irr-uid))
         (uid (uid-fix uid)))
      (spec/qual-case
       specqual
       :typespec (b* (((erp new-spec type? tyspecs types table uid)
                       (valid-type-spec
                        specqual.spec type? tyspecs table uid ienv)))
                   (retok (spec/qual-typespec new-spec)
                          type?
                          tyspecs
                          types
                          table
                          uid))
       :typequal (retok (spec/qual-typequal specqual.qual)
                        (type-option-fix type?)
                        (type-spec-list-fix tyspecs)
                        nil
                        (valid-table-fix table)
                        uid)
       :align (b* (((erp new-spec types table uid)
                    (valid-align-spec specqual.spec table uid ienv)))
                (retok (spec/qual-align new-spec)
                       (type-option-fix type?)
                       (type-spec-list-fix tyspecs)
                       types
                       table
                       uid))
       :attrib (retok (spec/qual-attrib specqual.spec)
                      (type-option-fix type?)
                      (type-spec-list-fix tyspecs)
                      nil
                      (valid-table-fix table)
                      uid)))
    :measure (spec/qual-count specqual)

    ///

    (defret type-spec-list-unambp-of-valid-spec/qual
      (type-spec-list-unambp new-tyspecs)
      :hyp (type-spec-list-unambp tyspecs)
      :hints
      (("Goal" :expand (valid-spec/qual specqual type? tyspecs table uid ienv))))

    (defret not-type-and-type-specs-of-valid-spec/qual
      (not (and new-type? new-tyspecs))
      :hyp (not (and type? tyspecs))
      :hints
      (("Goal"
        :expand ((valid-spec/qual specqual nil tyspecs table uid ienv)
                 (valid-spec/qual specqual type? nil table uid ienv)))))

    (defret not-type-specs-of-valid-spec/qual-when-type
      (implies new-type?
               (not new-tyspecs))
      :hyp (not (and type? tyspecs))
      :hints (("Goal" :use not-type-and-type-specs-of-valid-spec/qual))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-spec/qual-list ((specquals spec/qual-listp)
                                (type? type-optionp)
                                (tyspecs type-spec-listp)
                                (table valid-tablep)
                                (uid uidp)
                                (ienv ienvp))
    :guard (and (spec/qual-list-unambp specquals)
                (type-spec-list-unambp tyspecs)
                (not (and type? tyspecs)))
    :returns (mv (erp maybe-msgp)
                 (new-specquals spec/qual-listp)
                 (type typep)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of specifiers and qualifiers."
    :long
    (xdoc::topstring
     (xdoc::p
      "If validation is successful,
       we return the type determined by
       the type specifiers in the sequence.")
     (xdoc::p
      "We validate specifiers and qualifiers from left to right,
       threading the partial results through.
       When we reach the end, if the type has not been determined yet,
       we look at the collected type specifiers and determine the type,
       via a separate validation function.
       If there are no type specifiers, but no type has been determined,
       it means that there were no type specifiers at all [C17:6.7.2/2]."))
    (b* (((reterr) nil (irr-type) nil (irr-valid-table) (irr-uid))
         (uid (uid-fix uid))
         ((when (endp specquals))
          (cond
           (type?
             (retok nil
                    (type-option-fix type?)
                    nil
                    (valid-table-fix table)
                    uid))
           ((consp tyspecs)
            (b* (((erp type) (valid-type-spec-list-residual tyspecs)))
              (retok nil type nil (valid-table-fix table) uid)))
           (t (retmsg$ "The specifier and qualifier list ~x0 ~
                        contains no type specifiers."
                       (spec/qual-list-fix specquals)))))
         ((erp new-specqual type? tyspecs types table uid)
          (valid-spec/qual
            (car specquals) type? tyspecs table uid ienv))
         ((erp new-specquals type more-types table uid)
          (valid-spec/qual-list
            (cdr specquals) type? tyspecs table uid ienv)))
      (retok (cons new-specqual new-specquals)
             type
             (set::union types more-types)
             table
             uid))
    :measure (spec/qual-list-count specquals))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-align-spec ((align align-specp)
                            (table valid-tablep)
                            (uid uidp)
                            (ienv ienvp))
    :guard (align-spec-unambp align)
    :returns (mv (erp maybe-msgp)
                 (new-align align-specp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an alignment specifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "For now we just validate the type name or expression,
       possibly extending the validation table,
       but we do not check whether the alignment specifier
       is appropriate for the place where it occurs [C17:6.7.5].")
     (xdoc::p
      "In the version with the expression,
       the latter must have integer type [C17:6.7.5/3].
       The version with the type name
       is equivalent to @('_Alignas(_Alignof(typename))'),
       and thus we perform the same checks as in
       the @(':alignof') case of @(tsee valid-expr),
       including @(tsee valid-sizeof/alignof)."))
    (b* (((reterr) (irr-align-spec) nil (irr-valid-table) (irr-uid)))
      (align-spec-case
       align
       :alignas-type
       (b* (((erp new-type type types table uid)
             (valid-tyname align.type table uid ienv))
            ((when (type-case type :function))
             (retmsg$ "In the alignment specifier ~x0, ~
                       the argument ~x2 is a function type."
                      (align-spec-fix align) type)))
         (retok (align-spec-alignas-type new-type) types table uid))
       :alignas-expr
       (b* (((erp new-expr type types table uid)
             (valid-const-expr align.expr table uid ienv))
            ((unless (or (type-integerp type)
                         (type-case type :unknown)))
             (retmsg$ "In the alignment specifier ~x0, ~
                       the argument has type ~x1."
                      (align-spec-fix align) type)))
         (retok (align-spec-alignas-expr new-expr) types table uid))
       :alignas-ambig (prog2$ (impossible) (retmsg$ ""))))
    :measure (align-spec-count align))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-decl-spec ((declspec decl-specp)
                           (type? type-optionp)
                           (tyspecs type-spec-listp)
                           (storspecs stor-spec-listp)
                           (table valid-tablep)
                           (uid uidp)
                           (ienv ienvp))
    :guard (and (decl-spec-unambp declspec)
                (type-spec-list-unambp tyspecs)
                (not (and type? tyspecs)))
    :returns (mv (erp maybe-msgp)
                 (new-declspec decl-specp)
                 (new-type? type-optionp)
                 (new-tyspecs type-spec-listp)
                 (new-storspecs stor-spec-listp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a declaration specifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "For now we ignore
       type qualifiers,
       function specifiers,
       and attributes.
       We validate alignment specifiers but we do not make any use of them
       in our currently approximate type system.
       We handle type specifiers similarly to @(tsee valid-spec/qual).
       In addition, we collect all the storage class specifiers
       encountered as we go through the declaration specifiers."))
    (b* (((reterr)
          (irr-decl-spec) nil nil nil nil (irr-valid-table) (irr-uid))
         (uid (uid-fix uid)))
      (decl-spec-case
       declspec
       :stoclass (retok (decl-spec-stoclass declspec.spec)
                        (type-option-fix type?)
                        (type-spec-list-fix tyspecs)
                        (rcons declspec.spec (stor-spec-list-fix storspecs))
                        nil
                        (valid-table-fix table)
                        uid)
       :typespec (b* (((erp new-spec type? tyspecs types table uid)
                       (valid-type-spec
                        declspec.spec type? tyspecs table uid ienv)))
                   (retok (decl-spec-typespec new-spec)
                          type?
                          tyspecs
                          (stor-spec-list-fix storspecs)
                          types
                          table
                          uid))
       :typequal (retok (decl-spec-typequal declspec.qual)
                        (type-option-fix type?)
                        (type-spec-list-fix tyspecs)
                        (stor-spec-list-fix storspecs)
                        nil
                        (valid-table-fix table)
                        uid)
       :function (retok (decl-spec-function declspec.spec)
                        (type-option-fix type?)
                        (type-spec-list-fix tyspecs)
                        (stor-spec-list-fix storspecs)
                        nil
                        (valid-table-fix table)
                        uid)
       :align (b* (((erp new-spec types table uid)
                    (valid-align-spec declspec.spec table uid ienv)))
                (retok (decl-spec-align new-spec)
                       (type-option-fix type?)
                       (type-spec-list-fix tyspecs)
                       (stor-spec-list-fix storspecs)
                       types
                       table
                       uid))
       :attrib (retok (decl-spec-attrib declspec.spec)
                      (type-option-fix type?)
                      (type-spec-list-fix tyspecs)
                      (stor-spec-list-fix storspecs)
                      nil
                      (valid-table-fix table)
                      uid)
       :stdcall (retok (decl-spec-stdcall)
                       (type-option-fix type?)
                       (type-spec-list-fix tyspecs)
                       (stor-spec-list-fix storspecs)
                       nil
                       (valid-table-fix table)
                       uid)
       :declspec (retok (decl-spec-declspec declspec.arg)
                        (type-option-fix type?)
                        (type-spec-list-fix tyspecs)
                        (stor-spec-list-fix storspecs)
                        nil
                        (valid-table-fix table)
                        uid)))
    :measure (decl-spec-count declspec)

    ///

    (defret type-spec-list-unambp-of-valid-decl-spec
      (type-spec-list-unambp new-tyspecs)
      :hyp (type-spec-list-unambp tyspecs)
      :hints
      (("Goal"
        :expand (valid-decl-spec declspec type? tyspecs storspecs table uid ienv))))

    (defret not-type-and-type-specs-of-valid-decl-spec
      (not (and new-type? new-tyspecs))
      :hyp (not (and type? tyspecs))
      :hints
      (("Goal"
        :expand ((valid-decl-spec declspec nil tyspecs storspecs table uid ienv)
                 (valid-decl-spec declspec type? nil storspecs table uid ienv)))))

    (defret not-type-specs-of-valid-decl-spec-when-type
      (implies new-type?
               (not new-tyspecs))
      :hyp (not (and type? tyspecs))
      :hints (("Goal" :use not-type-and-type-specs-of-valid-decl-spec))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-decl-spec-list ((declspecs decl-spec-listp)
                                (type? type-optionp)
                                (tyspecs type-spec-listp)
                                (storspecs stor-spec-listp)
                                (table valid-tablep)
                                (uid uidp)
                                (ienv ienvp))
    :guard (and (decl-spec-list-unambp declspecs)
                (type-spec-list-unambp tyspecs)
                (not (and type? tyspecs)))
    :returns (mv (erp maybe-msgp)
                 (new-declspecs decl-spec-listp)
                 (type typep)
                 (all-storspecs stor-spec-listp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of declaration specifiers."
    :long
    (xdoc::topstring
     (xdoc::p
      "If validation is successful, we return
       the type determined by the type specifiers,
       and the list of storage class specifiers
       extracted from the declaration specifiers.")
     (xdoc::p
      "We go through each element of the list,
       threading the partial results through.
       When we reach the end of the list,
       if a type has been determined, we return it.
       Otherwise, we use a separate function to attempt to determine it
       from the collected type specifiers."))
    (b* (((reterr) nil (irr-type) nil nil (irr-valid-table) (irr-uid))
         (uid (uid-fix uid))
         ((when (endp declspecs))
          (cond
           (type? (retok nil
                         (type-option-fix type?)
                         (stor-spec-list-fix storspecs)
                         nil
                         (valid-table-fix table)
                         uid))
           ((consp tyspecs)
            (b* (((erp type) (valid-type-spec-list-residual tyspecs)))
              (retok nil
                     type
                     (stor-spec-list-fix storspecs)
                     nil
                     (valid-table-fix table)
                     uid)))
           (t (retmsg$ "The declaration specifiers ~x0 ~
                        contain no type specifiers."
                       (decl-spec-list-fix declspecs)))))
         ((erp new-declspec type? tyspecs storspecs types table uid)
          (valid-decl-spec
            (car declspecs) type? tyspecs storspecs table uid ienv))
         ((erp new-declspecs type storspecs more-types table uid)
          (valid-decl-spec-list
           (cdr declspecs) type? tyspecs storspecs table uid ienv)))
      (retok (cons new-declspec new-declspecs)
             type
             storspecs
             (set::union types more-types)
             table
             uid))
    :measure (decl-spec-list-count declspecs)

    ///

    (more-returns
     (all-storspecs true-listp :rule-classes :type-prescription)))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-initer ((initer initerp)
                        (target-type typep)
                        (lifetime lifetimep)
                        (table valid-tablep)
                        (uid uidp)
                        (ienv ienvp))
    :guard (and (initer-unambp initer)
                (not (type-case target-type :function))
                (not (type-case target-type :void)))
    :returns (mv (erp maybe-msgp)
                 (new-initer initerp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an initializer."
    :long
    (xdoc::topstring
     (xdoc::p
      "The target type passed as input is
       the type of the object being initialized,
       which must not be a function or void type [C17:6.7.9/3].
       The lifetime kind passed as input is
       the one of the object being initialized.")
     (xdoc::p
      "If the target type is a scalar,
       the initializer must be either a single expression,
       or a singleton initializer list without designators
       [C17:6.7.9/11].
       The latter is an expression enclosed in braces;
       experiments show that the final comma is allowed.
       The same constraints as in assignments apply here
       [C17:6.7.9/11] [C17:6.5.16.1/1]:
       see @(tsee valid-binary) for how we currently approximate the checks.
       We perform array-to-pointer and function-to-pointer conversions
       on the expression, as pointers may be required.
       We accept expressions of integer type when expecting a pointer type
       to approximate conversion of null pointer constants.")
     (xdoc::p
      "If the target type is the structure or union type,
       the initializer is a single expression,
       and the object has automatic storage duration,
       that expression must also have a compatible structure or union type
       [C17:6.7.9/13].")
     (xdoc::p
      "If the target type is an array of characters (of various types),
       the initializer may be a single string literal,
       subject to some constraints [C17:6.7.9/14] [C17:6.7.9/15].
       In our currently approximated type system,
       we must allow any kind of string literal with any array target type.")
     (xdoc::p
      "If the target type is an aggregate or union type,
       and the initializer is a brace-enclosed list,
       then we process the elements of the list,
       via a separate validation function
       [C17:6.7.9/16] [C17:6.7.9/17] [C17:6.7.9/18].")
     (xdoc::p
      "If none of the case above holds, validation fails."))
    (b* (((reterr) (irr-initer) nil (irr-valid-table) (irr-uid))
         (uid (uid-fix uid)))
      (cond
       ((type-case target-type :unknown)
        (initer-case
         initer
         :single (b* (((erp new-expr & types table uid)
                       (valid-expr initer.expr table uid ienv)))
                   (retok (initer-single new-expr) types table uid))
         :list (b* (((erp new-elems types table uid)
                     (valid-desiniter-list
                      initer.elems (type-unknown) lifetime table uid ienv)))
                 (retok (make-initer-list :elems new-elems
                                          :final-comma initer.final-comma)
                        types
                        table
                        uid))))
       ((type-scalarp target-type)
        (b* (((erp expr)
              (b* (((reterr) (irr-expr)))
                (initer-case
                 initer
                 :single (retok initer.expr)
                 :list (b* (((unless (and (consp initer.elems)
                                          (endp (cdr initer.elems))))
                             (retmsg$ "The initializer list ~x0 ~
                                       for the target type ~x1 ~
                                       is not a singleton."
                                      (initer-fix initer)
                                      (type-fix target-type)))
                            ((desiniter desiniter) (car initer.elems))
                            ((unless (endp desiniter.designors))
                             (retmsg$ "The initializer list ~x0 ~
                                       for the target type ~x1 ~
                                       is a singleton ~
                                       but it has designators."
                                      (initer-fix initer)
                                      (type-fix target-type)))
                            ((unless (initer-case desiniter.initer :single))
                             (retmsg$ "The initializer list ~x0 ~
                                       for the target type ~x1 ~
                                       is a singleton without designators ~
                                       but the inner initializer ~
                                       is not a single expression."
                                      (initer-fix initer)
                                      (type-fix target-type))))
                         (retok (initer-single->expr desiniter.initer))))))
             ((erp new-expr init-type types table uid)
              (valid-expr expr table uid ienv))
             (type (type-fpconvert (type-apconvert init-type)))
             ((unless (or (and (type-arithmeticp target-type)
                               (or (type-arithmeticp type)
                                   (type-case type :unknown)))
                          (and (type-case target-type :bool)
                               (or (type-case type :pointer)
                                   (type-case type :unknown)))
                          (and (type-case target-type :pointer)
                               (or (type-case type :pointer)
                                   (type-case type :unknown)
                                   (expr-null-pointer-constp expr type)))))
              (retmsg$ "The initializer ~x0 for the target type ~x1 ~
                        has type ~x2."
                       (initer-fix initer)
                       (type-fix target-type)
                       init-type))
             (new-initer
              (initer-case
               initer
               :single (initer-single new-expr)
               :list (make-initer-list
                      :elems (list (make-desiniter
                                    :designors nil
                                    :initer (initer-single new-expr)))
                      :final-comma initer.final-comma))))
          (retok new-initer types table uid)))
       ((and (or (type-case target-type :struct)
                 (type-case target-type :union))
             (initer-case initer :single)
             (lifetime-case lifetime :auto))
        (b* (((erp new-expr type types table uid)
              (valid-expr (initer-single->expr initer) table uid ienv))
             ((unless (or (type-equiv type target-type)
                          (type-case type :unknown)))
              (retmsg$ "The initializer ~x0 for the target type ~x1 ~
                        of an object in automatic storage has type ~x2.~%"
                       (initer-fix initer)
                       (type-fix target-type)
                       table
                       uid)))
          (retok (initer-single new-expr) types table uid)))
       ((and (type-case target-type :array)
             (initer-case initer :single)
             (expr-case (initer-single->expr initer) :string))
        (b* (((erp &) (valid-stringlit-list
                       (expr-string->strings (initer-single->expr initer))
                       ienv)))
          (retok (initer-single
                  (expr-string
                   (expr-string->strings (initer-single->expr initer))))
                 nil
                 (valid-table-fix table)
                 uid)))
       ((and (or (type-aggregatep target-type)
                 (type-case target-type :union))
             (initer-case initer :list))
        (b* (((erp new-elems types table uid)
              (valid-desiniter-list
                (initer-list->elems initer) (type-unknown)
                lifetime table uid ienv)))
          (retok (make-initer-list
                  :elems new-elems
                  :final-comma (initer-list->final-comma initer))
                 types
                 table
                 uid)))
       (t (retmsg$ "The initializer ~x0 for the target type ~x1 is disallowed."
                   (initer-fix initer) (type-fix target-type)))))
    :measure (initer-count initer))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-initer-option ((initer? initer-optionp)
                               (target-type typep)
                               (lifetime? lifetime-optionp)
                               (table valid-tablep)
                               (uid uidp)
                               (ienv ienvp))
    :guard (and (initer-option-unambp initer?)
                (or (not initer?)
                    lifetime?)
                (or (not initer?)
                    (not (type-case target-type :function)))
                (or (not initer?)
                    (not (type-case target-type :void))))
    :returns (mv (erp maybe-msgp)
                 (new-initer? initer-optionp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an optional initializer."
    :long
    (xdoc::topstring
     (xdoc::p
      "If there is no initializer, validation succeeds.
       Otherwise, we validate the initializer.")
     (xdoc::p
      "The guard on the target type is weakened,
       compared to @(tsee valid-initer):
       if there is no initializer, the type can be anything,
       because the restriction applies only to initializers [C17:6.7.9/3]."))
    (b* (((reterr) nil nil (irr-valid-table) (irr-uid))
         (uid (uid-fix uid)))
      (initer-option-case
       initer?
       :some (valid-initer initer?.val
                           target-type
                           (lifetime-option-fix lifetime?)
                           table
                           uid
                           ienv)
       :none (retok nil nil (valid-table-fix table) uid)))
    :measure (initer-option-count initer?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-desiniter ((desiniter desiniterp)
                           (target-type typep)
                           (lifetime lifetimep)
                           (table valid-tablep)
                           (uid uidp)
                           (ienv ienvp))
    :guard (and (desiniter-unambp desiniter)
                (not (type-case target-type :function))
                (not (type-case target-type :void)))
    :returns (mv (erp maybe-msgp)
                 (new-desiniter desiniterp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an initializer with optional designation."
    :long
    (xdoc::topstring
     (xdoc::p
      "The target type passed as argument is the type
       that the list of designators must be applicable to."))
    (b* (((reterr) (irr-desiniter) nil (irr-valid-table) (irr-uid))
         ((desiniter desiniter) desiniter)
         ((erp new-design & types table uid)
          (valid-designor-list
            desiniter.designors target-type table uid ienv))
         ((erp new-init more-types table uid)
          (valid-initer
            desiniter.initer target-type lifetime table uid ienv)))
      (retok (make-desiniter :designors new-design :initer new-init)
             (set::union types more-types)
             table
             uid))
    :measure (desiniter-count desiniter))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-desiniter-list ((desiniters desiniter-listp)
                                (target-type typep)
                                (lifetime lifetimep)
                                (table valid-tablep)
                                (uid uidp)
                                (ienv ienvp))
    :guard (and (desiniter-list-unambp desiniters)
                (not (type-case target-type :function))
                (not (type-case target-type :void)))
    :returns (mv (erp maybe-msgp)
                 (new-desiniters desiniter-listp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of zero or more
            initializers with optional designations."
    :long
    (xdoc::topstring
     (xdoc::p
      "The target type passed as argument is the type
       that each list of designators must be applicable to."))
    (b* (((reterr) nil nil (irr-valid-table) (irr-uid))
         (uid (uid-fix uid))
         ((when (endp desiniters))
          (retok nil nil (valid-table-fix table) uid))
         ((erp new-desiniter types table uid)
          (valid-desiniter
            (car desiniters) target-type lifetime table uid ienv))
         ((erp new-desiniters more-types table uid)
          (valid-desiniter-list
           (cdr desiniters) target-type lifetime table uid ienv)))
      (retok (cons new-desiniter new-desiniters)
             (set::union types more-types)
             table
             uid))
    :measure (desiniter-list-count desiniters))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-designor ((designor designorp)
                          (target-type typep)
                          (table valid-tablep)
                          (uid uidp)
                          (ienv ienvp))
    :guard (and (designor-unambp designor)
                (not (type-case target-type :function))
                (not (type-case target-type :void)))
    :returns (mv (erp maybe-msgp)
                 (new-designor designorp)
                 (new-target-type typep)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a designator."
    :long
    (xdoc::topstring
     (xdoc::p
      "The target type passed as input is
       the one that the designator must apply to;
       the target type returned as result is
       the one that results from applying the designator to it.
       The target type is the type of the current object [C17:6.7.9/17].
       A subscript designator requires an array target type,
       and must have an integer expression [C17:6.7.9/6];
       the result is the unknown type,
       because currently we have just one array type
       without information about the element type.
       A dotted designator requires a struct or union type [C17:6.7.9/7];
       the result is the unknown type,
       because currently we do not have information about the members."))
    (b* (((reterr)
          (irr-designor) (irr-type) nil (irr-valid-table) (irr-uid))
         (uid (uid-fix uid)))
      (designor-case
       designor
       :sub (b* (((erp new-index index-type index-types table uid)
                  (valid-const-expr designor.index table uid ienv))
                 ((unless (or (type-integerp index-type)
                              (type-case index-type :unknown)))
                  (retmsg$ "The index of the designator ~x0 has type ~x1."
                            (designor-fix designor)
                            index-type))
                 ((unless (or (type-case target-type :array)
                              (type-case target-type :unknown)))
                  (retmsg$ "The target type of the designator ~x0 is ~x1."
                           (designor-fix designor)
                           (type-fix target-type))))
              (retok (designor-sub new-index)
                     (type-unknown)
                     index-types
                     table
                     uid))
       :dot (b* (((unless (or (type-case target-type :struct)
                              (type-case target-type :union)
                              (type-case target-type :unknown)))
                  (retmsg$ "The target type of the designator ~x0 is ~x1."
                            (designor-fix designor)
                            (type-fix target-type))))
              (retok (designor-dot designor.name)
                     (type-unknown)
                     nil
                     (valid-table-fix table)
                     uid))))
    :measure (designor-count designor)

    ///

    (defret valid-designor.new-target-type-not-function
      (implies (not erp)
               (not (equal (type-kind new-target-type)
                           :function)))
      :hints
      (("Goal" :expand (valid-designor designor target-type table uid ienv))))

    (defret valid-designor.new-target-type-not-void
      (implies (not erp)
               (not (equal (type-kind new-target-type)
                           :void)))
      :hints
      (("Goal" :expand (valid-designor designor target-type table uid ienv)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-designor-list ((designors designor-listp)
                               (target-type typep)
                               (table valid-tablep)
                               (uid uidp)
                               (ienv ienvp))
    :guard (and (designor-list-unambp designors)
                (not (type-case target-type :function))
                (not (type-case target-type :void)))
    :returns (mv (erp maybe-msgp)
                 (new-designors designor-listp)
                 (new-target-type typep)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of zero or more designators."
    :long
    (xdoc::topstring
     (xdoc::p
      "The target type passed as argument is the current type
       that the designators must be applicable to.
       The target type returned as result is the type
       resulting from the application of the designators."))
    (b* (((reterr) nil (irr-type) nil (irr-valid-table) (irr-uid))
         (uid (uid-fix uid))
         ((when (endp designors))
          (retok nil
                 (type-fix target-type)
                 nil
                 (valid-table-fix table)
                 uid))
         ((erp new-designor target-type types table uid)
          (valid-designor (car designors) target-type table uid ienv))
         ((erp new-designors target-type more-types table uid)
          (valid-designor-list
            (cdr designors) target-type table uid ienv)))
      (retok (cons new-designor new-designors)
             target-type
             (set::union types more-types)
             table
             uid))
    :measure (designor-list-count designors))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-declor ((declor declorp)
                        (fundef-params-p booleanp)
                        (type typep)
                        (table valid-tablep)
                        (uid uidp)
                        (ienv ienvp))
    :guard (declor-unambp declor)
    :returns (mv (erp maybe-msgp)
                 (new-declor declorp)
                 (new-fundef-params-p booleanp)
                 (new-type typep)
                 (ident identp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "This function is called after validating
       a list of declaration specifiers,
       or a list of specifiers and qualifiers:
       if the validation of those lists is successful,
       they determine a type, which the declarator can further refine:
       we pass that type as input to this validation function,
       which returns the possibly refined type,
       along with the identifier being declared.
       This function is also called recursively,
       since declarators and direct declarators are mutually recursive.")
     (xdoc::p
      "The @('fundef-params-p') flag is @('t')
       when this function is called
       to validate the declarator of a function definition,
       and only when the parameters of the function have not been validated yet.
       Its new value @('new-fundef-params-p'), returned as result,
       stays @('t') if the parameters of the function
       have still not been validated yet,
       because they are not found in this declarator;
       otherwise, its new value is @('nil').
       If the input @('fundef-params-p') is @('nil'),
       then @('new-fundef-params-p') is @('nil') as well.
       The exact handling of this flag,
       and the exact treatment of the parameters of function declarations,
       are explained in @(tsee valid-dirdeclor).")
     (xdoc::p
      "In our currently approximate type system,
       we do not validate type qualifiers, or attributes.
       So the only role of the @('pointers') component of @(tsee declor)
       is to refine the type passed as input into the pointer type
       [C17:6.7.6.1/1].
       This resulting type is then passed to
       the function to validate the direct declarator that follows.")
     (xdoc::p
      "We also pass the @('fundef-params-p') flag to @(tsee valid-dirdeclor),
       and relay the @('new-fundef-params-p') output.
       The reason is that, after peeling off the pointers,
       which refine the return result of the function,
       the direct declarator is still expected to be for a function,
       and we have not validated the parameters yet."))
    (b* (((reterr)
          (irr-declor) nil (irr-type) (irr-ident)
          nil (irr-valid-table) (irr-uid))
         ((declor declor) declor)
         (type (if (consp declor.pointers)
                   (type-pointer)
                 type))
         ((erp new-dirdeclor fundef-params-p type ident types table uid)
          (valid-dirdeclor
            declor.direct fundef-params-p type table uid ienv)))
      (retok (make-declor :pointers declor.pointers :direct new-dirdeclor)
             fundef-params-p
             type
             ident
             types
             table
             uid))
    :measure (declor-count declor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-declor-option ((declor? declor-optionp)
                               (type typep)
                               (table valid-tablep)
                               (uid uidp)
                               (ienv ienvp))
    :guard (declor-option-unambp declor?)
    :returns (mv (erp maybe-msgp)
                 (new-declor? declor-optionp)
                 (new-type typep)
                 (ident? ident-optionp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an optional declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "If there is no declarator,
       we return the type and validation table unchanged,
       and no identifier.
       Otherwise, we validate the declarator,
       using a separate validation function.")
     (xdoc::p
      "This function does not take or return a @('fundef-params-p') flag
       because optional declarators are not used in function parameters."))
    (b* (((reterr) nil (irr-type) nil nil (irr-valid-table) (irr-uid)))
      (declor-option-case
       declor?
       :none (retok nil
                    (type-fix type)
                    nil
                    nil
                    (valid-table-fix table)
                    (uid-fix uid))
       :some (b* (((erp new-declor & type ident types table uid)
                   (valid-declor declor?.val nil type table uid ienv)))
               (retok new-declor type ident types table uid))))
    :measure (declor-option-count declor?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-dirdeclor ((dirdeclor dirdeclorp)
                           (fundef-params-p booleanp)
                           (type typep)
                           (table valid-tablep)
                           (uid uidp)
                           (ienv ienvp))
    :guard (dirdeclor-unambp dirdeclor)
    :returns (mv (erp maybe-msgp)
                 (new-dirdeclor dirdeclorp)
                 (new-fundef-params-p booleanp)
                 (new-type typep)
                 (ident identp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a direct declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "The type passed as input is the one resulting from the validation of
       the list of declaration specifiers
       or the list of specifiers and qualifiers
       that precedes the declarator of which the direct declarator is part.
       This type is refined according to the direct declarator,
       and we return the refined type,
       along with the declared identifier.")
     (xdoc::p
      "The meaning of the @('fundef-params-p') flag passed as input is
       the same as in @(tsee valid-declor): see that function's documentation.")
     (xdoc::p
      "If the direct declarator is just an identifier,
       the type is not further refined by this direct declarator.")
     (xdoc::p
      "If the direct declarator is a parenthesized declarator,
       we recursively validate the declarator.")
     (xdoc::p
      "If the direct declarator is one of the array kinds,
       we refine the type to the array type [C17:6.7.6.2/3]
       (so in our currently approximate type system
       the input type is effectively ignored),
       and we recursively validate the enclosed direct declarator.
       Then we validate the index expression (if present),
       ensuring that it has integer type.
       For now we do not check that, if these expressions are constant,
       their values are greater than 0 [C17:6.7.6.2/1].
       Currently we do not need to do anything
       with type qualifiers and attributes.
       The @('fundef-params-p') flag is threaded through.")
     (xdoc::p
      "If the direct declarator is one of the function kinds,
       we ensure that the input type, which is the function return type,
       is not a function or array type [C17:6.7.6.3/1].
       We refine the input type to a function type
       (which in our current type system means we override it),
       and we validate the declarator.
       Then things differ between the kinds of function declarators.")
     (xdoc::p
      "In a function declarator with a parameter type list,
       we push a new scope for the parameters,
       and we validate the parameters (which adds them to the new scope),
       passing the @('fundef-params-p') resulting from
       the recursive validation of the enclosed direct declarator.
       This resulting flag is @('t') if
       the parameters of the function being defined
       have not been validated yet,
       which means that the parameters of the current direct declarator
       are in fact the ones of the function.
       So we return @('nil') as the @('new-fundef-params-p') result,
       so that any outer function declarator
       is not treated as the one
       whose parameters are for the function definition,
       if we are validating one.
       To make things clearer, consider a function definition")
     (xdoc::codeblock
      "void (*f(int x, int y))(int z) { ... }")
     (xdoc::p
      "which defines a function @('f') with parameters @('x') and @('y'),
       which returns a pointer to a function
       that has a parameter @('z') and returns @('void').
       When we validate the full declarator of this function definition,
       @('fundef-params-p') is @('t').
       When we encounter the outer function declarator,
       first we recursively process the inner function declarator,
       whose input @('fundef-params-p') is still @('t'),
       and whose output @('new-fundef-params-p') is @('nil').
       That way, when we continue validating the outer function declarator,
       we do not treat @('z') as a parameter of the function definition.
       In any case, when the current function declarator
       is the one whose parameters are for the function definition,
       i.e. when @('fundef-params-p') is @('t'),
       after validating the parameters, which pushes a new scope with them,
       we return the validation table as such,
       so that when we later validate the function body,
       we already have the top-level scope for the body.
       If instead @('fundef-params-p') is @('nil'),
       the parameters form a function prototype scope [C17:6.2.1/4],
       which is therefore popped.")
     (xdoc::p
      "For the function declarator with a parameter type list,
       we handle the special case of a single @('void') [C17:6.7.6.3/10]
       before calling a separate function to validate the parameters.")
     (xdoc::p
      "A function declarator with a non-empty name list can only occur
       as the parameters of a function being defined [C17:6.7.6.3/3]
       Thus, unless the list is empty,
       we raise an error unless @('fundef-params-p') is @('t'),
       i.e. unless we are validating the parameters of a defined function.
       Note that the value of @('fundef-params-p') is the one
       after validating the inner direct declarator.
       If we are not validating the declarator of a function definition
       (i.e. if @('fundef-params-p') is @('nil')),
       in which case as just mentioned the list must be empty,
       there is nothing left to do, and we return;
       note that there is no function prototype scope here.
       Otherwise, we ensure that the names have no duplicates,
       and we push a new scope for the parameters and the function body,
       but we do not add the parameters to the new scope,
       because their types are specified by the declarations
       that must occur between the end of the whole function declarator
       and the beginning of the defined function's body."))
    (b* (((reterr)
          (irr-dirdeclor) nil (irr-type) (irr-ident)
          nil (irr-valid-table) (irr-uid))
         (uid (uid-fix uid)))
      (dirdeclor-case
       dirdeclor
       :ident
       (retok (dirdeclor-ident dirdeclor.ident)
              (bool-fix fundef-params-p)
              (type-fix type)
              dirdeclor.ident
              nil
              (valid-table-fix table)
              uid)
       :paren
       (b* (((erp new-declor fundef-params-p type ident types table uid)
             (valid-declor
               dirdeclor.inner fundef-params-p type table uid ienv)))
         (retok (dirdeclor-paren new-declor)
                fundef-params-p
                type
                ident
                types
                table
                uid))
       :array
       (b* ((type (type-array))
            ((erp new-dirdeclor fundef-params-p type ident types table uid)
             (valid-dirdeclor
               dirdeclor.declor fundef-params-p type table uid ienv))
            ((erp new-expr? index-type? more-types table uid)
             (valid-expr-option dirdeclor.size? table uid ienv))
            ((when (and index-type?
                        (not (type-integerp index-type?))
                        (not (type-case index-type? :unknown))))
             (retmsg$ "The index expression ~
                       of the direct declarator ~x0 ~
                       has type ~x1."
                      (dirdeclor-fix dirdeclor)
                      index-type?)))
         (retok (make-dirdeclor-array :declor new-dirdeclor
                                      :qualspecs dirdeclor.qualspecs
                                      :size? new-expr?)
                fundef-params-p
                type
                ident
                (set::union types more-types)
                table
                uid))
       :array-static1
       (b* ((type (type-array))
            ((erp new-dirdeclor fundef-params-p type ident types table uid)
             (valid-dirdeclor
               dirdeclor.declor fundef-params-p type table uid ienv))
            ((erp new-expr index-type more-types table uid)
             (valid-expr dirdeclor.size table uid ienv))
            ((unless (or (type-integerp index-type)
                         (type-case index-type :unknown)))
             (retmsg$ "The index expression ~
                       of the direct declarator ~x0 ~
                       has type ~x1."
                      (dirdeclor-fix dirdeclor)
                      index-type)))
         (retok (make-dirdeclor-array-static1 :declor new-dirdeclor
                                              :qualspecs dirdeclor.qualspecs
                                              :size new-expr)
                fundef-params-p
                type
                ident
                (set::union types more-types)
                table
                uid))
       :array-static2
       (b* ((type (type-array))
            ((erp new-dirdeclor fundef-params-p type ident types table uid)
             (valid-dirdeclor
               dirdeclor.declor fundef-params-p type table uid ienv))
            ((erp new-expr index-type more-types table uid)
             (valid-expr dirdeclor.size table uid ienv))
            ((unless (or (type-integerp index-type)
                         (type-case index-type :unknown)))
             (retmsg$ "The index expression ~
                       of the direct declarator ~x0 ~
                       has type ~x1."
                      (dirdeclor-fix dirdeclor)
                      index-type)))
         (retok (make-dirdeclor-array-static2 :declor new-dirdeclor
                                              :qualspecs dirdeclor.qualspecs
                                              :size new-expr)
                fundef-params-p
                type
                ident
                (set::union types more-types)
                table
                uid))
       :array-star
       (b* ((type (type-array))
            ((erp new-dirdeclor fundef-params-p type ident types table uid)
             (valid-dirdeclor
              dirdeclor.declor fundef-params-p type table uid ienv)))
         (retok (make-dirdeclor-array-star :declor new-dirdeclor
                                           :qualspecs dirdeclor.qualspecs)
                fundef-params-p
                type
                ident
                types
                table
                uid))
       :function-params
       (b* (((when (or (type-case type :function)
                       (type-case type :array)))
             (retmsg$ "The direct declarator ~x0 has type ~x1."
                       (dirdeclor-fix dirdeclor)
                       (type-fix type)))
            (type (type-function))
            ((erp new-dirdeclor fundef-params-p type ident types table uid)
             (valid-dirdeclor
               dirdeclor.declor fundef-params-p type table uid ienv))
            (table (valid-push-scope table))
            ((erp new-params more-types table uid)
             (if (equal dirdeclor.params
                        (list (make-param-declon
                               :specs (list (decl-spec-typespec (type-spec-void)))
                               :declor (param-declor-none))))
                 (retok dirdeclor.params nil table uid)
               (valid-param-declon-list
                dirdeclor.params fundef-params-p table uid ienv)))
            (table (if fundef-params-p
                       table
                     (valid-pop-scope table))))
         (retok (make-dirdeclor-function-params :declor new-dirdeclor
                                                :params new-params
                                                :ellipsis dirdeclor.ellipsis)
                nil
                type
                ident
                (set::union types more-types)
                table
                uid))
       :function-names
       (b* (((when (or (type-case type :function)
                       (type-case type :array)))
             (retmsg$ "The direct declarator ~x0 has type ~x1."
                      (dirdeclor-fix dirdeclor)
                      (type-fix type)))
            (type (type-function))
            ((erp new-dirdeclor fundef-params-p type ident types table uid)
             (valid-dirdeclor
               dirdeclor.declor fundef-params-p type table uid ienv))
            ((when (and (consp dirdeclor.names)
                        (not fundef-params-p)))
             (retmsg$ "A non-empty list of parameter names ~
                       occurs in a function declarator ~x0 ~
                       that is not part of a function definition."
                      (dirdeclor-fix dirdeclor)))
            ((when (not fundef-params-p))
             (retok (make-dirdeclor-function-names :declor new-dirdeclor
                                                   :names dirdeclor.names)
                    nil
                    type
                    ident
                    types
                    table
                    uid))
            ((unless (no-duplicatesp-equal dirdeclor.names))
             (retmsg$ "The list of parameter names ~
                       in the function declarator ~x0 ~
                       has duplicates."
                      (dirdeclor-fix dirdeclor)))
            (table (valid-push-scope table)))
         (retok (make-dirdeclor-function-names :declor new-dirdeclor
                                               :names dirdeclor.names)
                nil
                type
                ident
                types
                table
                uid))))
    :measure (dirdeclor-count dirdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-absdeclor ((absdeclor absdeclorp)
                           (type typep)
                           (table valid-tablep)
                           (uid uidp)
                           (ienv ienvp))
    :guard (absdeclor-unambp absdeclor)
    :returns (mv (erp maybe-msgp)
                 (new-absdeclor absdeclorp)
                 (new-type typep)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an abstract declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is fairly similar to @(tsee valid-declor)
       (see that function's documentation),
       but since the declarator is abstract,
       there is no identifier being declared to return.
       Furthermore, there is no flag for function definitions,
       since a function definition uses a declarator,
       not an abstract declarator."))
    (b* (((reterr)
          (irr-absdeclor) (irr-type) nil (irr-valid-table) (irr-uid))
         ((absdeclor absdeclor) absdeclor)
         (type (if (consp absdeclor.pointers)
                   (type-pointer)
                 type))
         ((erp new-direct? type types table uid)
          (valid-dirabsdeclor-option
            absdeclor.direct? type table uid ienv)))
      (retok (make-absdeclor :pointers absdeclor.pointers :direct? new-direct?)
             type
             types
             table
             uid))
    :measure (absdeclor-count absdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-absdeclor-option ((absdeclor? absdeclor-optionp)
                                  (type typep)
                                  (table valid-tablep)
                                  (uid uidp)
                                  (ienv ienvp))
    :guard (absdeclor-option-unambp absdeclor?)
    :returns (mv (erp maybe-msgp)
                 (new-absdeclor? absdeclor-optionp)
                 (new-type typep)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an optional abstract declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "If there is no abstract declarator,
       we return the type and validation table unchanged.
       Otherwise, we validate the abstract declarator,
       using a separate validation function."))
    (b* (((reterr) nil (irr-type) nil (irr-valid-table)))
      (absdeclor-option-case
       absdeclor?
       :none (retok nil
                    (type-fix type)
                    nil
                    (valid-table-fix table)
                    (uid-fix uid))
       :some (valid-absdeclor absdeclor?.val type table uid ienv)))
    :measure (absdeclor-option-count absdeclor?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-dirabsdeclor ((dirabsdeclor dirabsdeclorp)
                              (type typep)
                              (table valid-tablep)
                              (uid uidp)
                              (ienv ienvp))
    :guard (dirabsdeclor-unambp dirabsdeclor)
    :returns (mv (erp maybe-msgp)
                 (new-dirabsdeclor dirabsdeclorp)
                 (new-type typep)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a direct abstract declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is fairly similar to @(tsee valid-dirdeclor)
       (see that function's documentation),
       but since the direct declarator is abstract,
       there is no identifier being declared to return.
       Furthermore, there is no flag for function definitions,
       since a function definition uses a (direct) declarator,
       not an (direct) abstract declarator."))
    (b* (((reterr)
          (irr-dirabsdeclor) (irr-type) nil (irr-valid-table) (irr-uid))
         (uid (uid-fix uid)))
      (dirabsdeclor-case
       dirabsdeclor
       :paren
       (b* (((erp new-absdeclor type types table uid)
             (valid-absdeclor dirabsdeclor.inner type table uid ienv)))
         (retok (dirabsdeclor-paren new-absdeclor)
                type
                types
                table
                uid))
       :array
       (b* ((type (type-array))
            ((erp new-declor? type types table uid)
             (valid-dirabsdeclor-option
               dirabsdeclor.declor? type table uid ienv))
            ((erp new-size? index-type? more-types table uid)
             (valid-expr-option dirabsdeclor.size? table uid ienv))
            ((when (and index-type?
                        (not (type-integerp index-type?))
                        (not (type-case index-type? :unknown))))
             (retmsg$ "The index expression ~
                       of the direct abstract declarator ~x0 ~
                       has type ~x1."
                      (dirabsdeclor-fix dirabsdeclor)
                      index-type?)))
         (retok (make-dirabsdeclor-array
                 :declor? new-declor?
                 :qualspecs dirabsdeclor.qualspecs
                 :size? new-size?)
                type
                (set::union types more-types)
                table
                uid))
       :array-static1
       (b* ((type (type-array))
            ((erp new-declor? type types table uid)
             (valid-dirabsdeclor-option
               dirabsdeclor.declor? type table uid ienv))
            ((erp new-size index-type more-types table uid)
             (valid-expr dirabsdeclor.size table uid ienv))
            ((unless (or (type-integerp index-type)
                         (type-case index-type :unknown)))
             (retmsg$ "The index expression ~
                       of the direct abstract declarator ~x0 ~
                       has type ~x1."
                      (dirabsdeclor-fix dirabsdeclor)
                      index-type)))
         (retok (make-dirabsdeclor-array-static1
                 :declor? new-declor?
                 :qualspecs dirabsdeclor.qualspecs
                 :size new-size)
                type
                (set::union types more-types)
                table
                uid))
       :array-static2
       (b* ((type (type-array))
            ((erp new-declor? type types table uid)
             (valid-dirabsdeclor-option
               dirabsdeclor.declor? type table uid ienv))
            ((erp new-size index-type more-types table uid)
             (valid-expr dirabsdeclor.size table uid ienv))
            ((unless (or (type-integerp index-type)
                         (type-case index-type :unknown)))
             (retmsg$ "The index expression ~
                       of the direct abstract declarator ~x0 ~
                       has type ~x1."
                      (dirabsdeclor-fix dirabsdeclor)
                      index-type)))
         (retok (make-dirabsdeclor-array-static2
                 :declor? new-declor?
                 :qualspecs dirabsdeclor.qualspecs
                 :size new-size)
                type
                (set::union types more-types)
                table
                uid))
       :array-star
       (b* ((type (type-array))
            ((erp new-declor? type types table uid)
             (valid-dirabsdeclor-option
               dirabsdeclor.declor? type table uid ienv)))
         (retok (dirabsdeclor-array-star new-declor?)
                type
                types
                table
                uid))
       :function
       (b* (((when (or (type-case type :function)
                       (type-case type :array)))
             (retmsg$ "The direct abstract declarator ~x0 ~
                       has type ~x1."
                      (dirabsdeclor-fix dirabsdeclor)
                      (type-fix type)))
            (type (type-function))
            ((erp new-declor? type types table uid)
             (valid-dirabsdeclor-option
               dirabsdeclor.declor? type table uid ienv))
            (table (valid-push-scope table))
            ((erp new-params more-types table uid)
             (if (equal dirabsdeclor.params
                        (list (make-param-declon
                               :specs (list (decl-spec-typespec (type-spec-void)))
                               :declor (param-declor-none))))
                 (retok dirabsdeclor.params nil table uid)
               (valid-param-declon-list
                 dirabsdeclor.params nil table uid ienv)))
            (table (valid-pop-scope table)))
         (retok (make-dirabsdeclor-function :declor? new-declor?
                                            :params new-params
                                            :ellipsis dirabsdeclor.ellipsis)
                type
                (set::union types more-types)
                table
                uid))
       :dummy-base
       (prog2$ (impossible) (retmsg$ ""))))
    :measure (dirabsdeclor-count dirabsdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-dirabsdeclor-option ((dirabsdeclor? dirabsdeclor-optionp)
                                     (type typep)
                                     (table valid-tablep)
                                     (uid uidp)
                                     (ienv ienvp))
    :guard (dirabsdeclor-option-unambp dirabsdeclor?)
    :returns (mv (erp maybe-msgp)
                 (new-dirabsdeclor? dirabsdeclor-optionp)
                 (new-type typep)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an optional direct abstract declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "If there is no direct abstract declarator,
       we return the type and validation table unchanged.
       Otherwise, we validate the direct abstract declarator,
       using a separate validation function."))
    (b* (((reterr) nil (irr-type) nil (irr-valid-table) (irr-uid)))
      (dirabsdeclor-option-case
       dirabsdeclor?
       :none (retok nil
                    (type-fix type)
                    nil
                    (valid-table-fix table)
                    (uid-fix uid))
       :some (valid-dirabsdeclor
               dirabsdeclor?.val type table uid ienv)))
    :measure (dirabsdeclor-option-count dirabsdeclor?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-param-declon ((paramdecl param-declonp)
                              (fundef-params-p booleanp)
                              (table valid-tablep)
                              (uid uidp)
                              (ienv ienvp))
    :guard (param-declon-unambp paramdecl)
    :returns (mv (erp maybe-msgp)
                 (new-paramdecl param-declonp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a parameter declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "The @('fundef-params-p') input is @('t') iff
       we are validating the parameter of a function definition.")
     (xdoc::p
      "We validate the declaration specifiers,
       which results in a type,
       a list of storage class specifiers,
       and a possibly updated table.
       We ensure that the list of storage class specifiers
       is either empty or the singleton @('register') [C17:6.7.6.3/2].")
     (xdoc::p
      "We validate the parameter declarator,
       ensuring that it has an identifier if @('fundef-params-p') is @('t')
       [C17:6.9.1/5].
       We adjust the type if necessary [C17:6.7.6.3/7] [C17:6.7.6.3/8].
       If the parameter declarator has an identifier,
       we extend the validation table with it,
       unless there is already an ordinary identifier
       with the same name in the same (i.e. current) scope;
       since parameters have no linkage [C17:6.2.2/6],
       they can be only declared once in the same scope [C17:6.7/3].
       Parameters of function declarations have no linkage [C17:6.2.2/6].
       Since storage is allocated for them when the function is called,
       they are considered defined [C17:6.7/5]."))
    (b* (((reterr) (irr-param-declon) nil (irr-valid-table) (irr-uid))
         (uid (uid-fix uid))
         ((param-declon paramdecl) paramdecl)
         ((erp new-specs type storspecs types table uid)
          (valid-decl-spec-list paramdecl.specs nil nil nil table uid ienv))
         ((unless (or (endp storspecs)
                      (stor-spec-list-register-p storspecs)))
          (retmsg$ "The parameter declaration ~x0 ~
                    has storage class specifiers ~x1."
                   (param-declon-fix paramdecl)
                   (stor-spec-list-fix storspecs)))
         ((erp new-decl type ident? more-types table uid)
          (valid-param-declor paramdecl.declor type table uid ienv))
         ((when (and fundef-params-p
                     (not ident?)))
          (retmsg$ "The parameter declaration ~x0 ~
                    is for a function definition but has no identifier."
                   (param-declon-fix paramdecl)))
         (type (if (type-case type :array)
                   (type-pointer)
                 type))
         (type (if (type-case type :function)
                   (type-pointer)
                 type))
         ((when (not ident?))
          (retok (make-param-declon :specs new-specs :declor new-decl)
                 (set::union types more-types)
                 table
                 uid))
         (ord-info (make-valid-ord-info-objfun
                    :type type
                    :linkage (linkage-none)
                    :defstatus (valid-defstatus-defined)
                    :uid uid))
         (uid (uid-increment uid))
         ((mv info? currentp) (valid-lookup-ord ident? table))
         ((when (and info? currentp))
          (retmsg$ "The parameter declared in ~x0 ~
                    in already declared in the current scope ~
                    with associated information ~x1."
                   (param-declon-fix paramdecl) info?))
         (table (valid-add-ord ident? ord-info table)))
      (retok (make-param-declon :specs new-specs :declor new-decl)
             (set::union types more-types)
             table
             uid))
    :measure (param-declon-count paramdecl))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-param-declon-list ((paramdecls param-declon-listp)
                                   (fundef-params-p booleanp)
                                   (table valid-tablep)
                                   (uid uidp)
                                   (ienv ienvp))
    :guard (param-declon-list-unambp paramdecls)
    :returns (mv (erp maybe-msgp)
                 (new-paramdecls param-declon-listp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of parameter declarations."
    :long
    (xdoc::topstring
     (xdoc::p
      "IWe validate each parameter in turn,
       threading the validation table through,
       using a separate validation function."))
    (b* (((reterr) nil nil (irr-valid-table) (irr-uid))
         ((when (endp paramdecls))
          (retok nil nil (valid-table-fix table) (uid-fix uid)))
         ((erp new-paramdecl types table uid)
          (valid-param-declon
            (car paramdecls) fundef-params-p table uid ienv))
         ((erp new-paramdecls more-types table uid)
          (valid-param-declon-list
            (cdr paramdecls) fundef-params-p table uid ienv)))
      (retok (cons new-paramdecl new-paramdecls)
             (set::union types more-types)
             table
             uid))
    :measure (param-declon-list-count paramdecls))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-param-declor ((paramdeclor param-declorp)
                              (type typep)
                              (table valid-tablep)
                              (uid uidp)
                              (ienv ienvp))
    :guard (param-declor-unambp paramdeclor)
    :returns (mv (erp maybe-msgp)
                 (new-paramdeclor param-declorp)
                 (new-type typep)
                 (ident? ident-optionp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a parameter declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "The input type is the one resulting from
       the declaration specifiers of the parameter declaration
       of which the parameter declarator is part of.
       If validation is successful,
       we return a possibly refined type,
       and an optional identifier.")
     (xdoc::p
      "If the parameter declarator is a (non-abstract) declarator,
       we return the possibly refined type and the identifier.
       If the parameter declarator is an abstract declarator,
       we return the possibly refined type but no identifier.
       If the parameter declarator is absent,
       we return the type unchanged and no identifier."))
    (b* (((reterr)
          (irr-param-declor) (irr-type) (irr-ident)
          nil (irr-valid-table) (irr-uid))
         (uid (uid-fix uid)))
      (param-declor-case
       paramdeclor
       :nonabstract
       (b* (((erp new-declor & type ident types table uid)
             (valid-declor
               paramdeclor.declor nil type table uid ienv)))
         (retok (param-declor-nonabstract new-declor)
                type
                ident
                types
                table
                uid))
       :abstract
       (b* (((erp new-absdeclor type types table uid)
             (valid-absdeclor paramdeclor.declor type table uid ienv)))
         (retok (param-declor-abstract new-absdeclor)
                type
                nil
                types
                table
                uid))
       :none
       (retok (param-declor-none)
              (type-fix type)
              nil
              nil
              (valid-table-fix table)
              uid)
       :ambig
       (prog2$ (impossible) (retmsg$ ""))))
    :measure (param-declor-count paramdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-tyname ((tyname tynamep)
                        (table valid-tablep)
                        (uid uidp)
                        (ienv ienvp))
    :guard (tyname-unambp tyname)
    :returns (mv (erp maybe-msgp)
                 (new-tyname tynamep)
                 (type typep)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a type name."
    :long
    (xdoc::topstring
     (xdoc::p
      "A valid type name denotes a type,
       so we return a type if validation is successful.")
     (xdoc::p
      "First we validate the list of specifiers and qualifiers,
       which returns a type if successful.
       Then we validate the optional abstract declarator,
       which returns a possibly refined type.
       We return the latter type."))
    (b* (((reterr) (irr-tyname) (irr-type) nil (irr-valid-table) (irr-uid))
         ((tyname tyname) tyname)
         ((erp new-specquals type types table uid)
          (valid-spec/qual-list tyname.specquals nil nil table uid ienv))
         ((erp new-decl? type more-types table uid)
          (valid-absdeclor-option tyname.declor? type table uid ienv))
         (info (make-tyname-info :type type)))
      (retok (make-tyname :specquals new-specquals
                          :declor? new-decl?
                          :info info)
             type
             (set::union types more-types)
             table
             uid))
    :measure (tyname-count tyname))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-struni-spec ((struni-spec struni-specp)
                             (table valid-tablep)
                             (uid uidp)
                             (ienv ienvp))
    :guard (struni-spec-unambp struni-spec)
    :returns (mv (erp maybe-msgp)
                 (new-struni-spec struni-specp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a structure or union specifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check that there is at least a name or a list of members
       [C17:6.7.2.1/2].")
     (xdoc::p
      "For now our validation tables include
       no information about structure and union tags,
       so we do not extend the validation table,
       if the structure or union specifier has a name.
       However, we validate the members, if present."))
    (b* (((reterr) (irr-struni-spec) nil (irr-valid-table) (irr-uid))
         ((struni-spec struni-spec) struni-spec)
         ((when (and (not struni-spec.name?)
                     (endp struni-spec.members)))
          (retmsg$ "The structure or union specifier ~x0 ~
                    has no name and no members."
                   (struni-spec-fix struni-spec)))
         ((erp new-members types table uid)
          (valid-structdecl-list
            struni-spec.members nil table uid ienv)))
      (retok (make-struni-spec :name? struni-spec.name?
                               :members new-members)
             types
             table
             uid))
    :measure (struni-spec-count struni-spec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-structdecl ((structdecl structdeclp)
                            (previous ident-listp)
                            (table valid-tablep)
                            (uid uidp)
                            (ienv ienvp))
    :guard (structdecl-unambp structdecl)
    :returns (mv (erp maybe-msgp)
                 (new-structdecl structdeclp)
                 (new-previous ident-listp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a structure declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "The @('previous') input consists of
       the names of the members that precede this structure declaration
       in the structure or union specifier being validated.
       The @('new-previous') output consists of
       the extension of @('previous') with
       the names of the members declared by this structure declaration.")
     (xdoc::p
      "If the structure declaration declares members,
       first we validate the list of specifiers and qualifiers,
       obtaining a type if the validation is successful.
       Then we use a separate validation function for the structure declarators,
       which also returns a possibly extended list of member names.")
     (xdoc::p
      "If the structure declaration consists of a static assertion declaration,
       we validate it using a separate validation function.
       The list of member names is unchanged.")
     (xdoc::p
      "If the structure declaration is empty (i.e. a semicolon),
       which is a GCC extension,
       the list of member names and the validation table are unchanged."))
    (b* (((reterr) (irr-structdecl) nil nil (irr-valid-table) (irr-uid))
         (uid (uid-fix uid)))
      (structdecl-case
       structdecl
       :member
       (b* (((erp new-specqual type types table uid)
             (valid-spec/qual-list
               structdecl.specqual nil nil table uid ienv))
            ((erp new-declor previous more-types table uid)
             (valid-structdeclor-list
              structdecl.declor previous type table uid ienv)))
         (retok (make-structdecl-member :extension structdecl.extension
                                        :specqual new-specqual
                                        :declor new-declor
                                        :attrib structdecl.attrib)
                previous
                (set::union types more-types)
                table
                uid))
       :statassert
       (b* (((erp new-statassert types table uid)
             (valid-statassert structdecl.unwrap table uid ienv)))
         (retok (structdecl-statassert new-statassert)
                (ident-list-fix previous)
                types
                table
                uid))
       :empty
       (retok (structdecl-empty)
              (ident-list-fix previous)
              nil
              (valid-table-fix table)
              uid)))
    :measure (structdecl-count structdecl))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-structdecl-list ((structdecls structdecl-listp)
                                 (previous ident-listp)
                                 (table valid-tablep)
                                 (uid uidp)
                                 (ienv ienvp))
    :guard (structdecl-list-unambp structdecls)
    :returns (mv (erp maybe-msgp)
                 (new-structdecls structdecl-listp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of structure declarators."
    :long
    (xdoc::topstring
     (xdoc::p
      "The @('previous') input consists of
       the names of the members that precede these structure declarations
       (which declare more members)
       in the structure or union specifier being validated.
       This list is used to ensure uniqueness of member names."))
    (b* (((reterr) nil nil (irr-valid-table) (irr-uid))
         (uid (uid-fix uid))
         ((when (endp structdecls))
          (retok nil nil (valid-table-fix table) uid))
         ((erp new-structdecl previous types table uid)
          (valid-structdecl
            (car structdecls) previous table uid ienv))
         ((erp new-structdecls more-types table uid)
          (valid-structdecl-list
            (cdr structdecls) previous table uid ienv)))
      (retok (cons new-structdecl new-structdecls)
             (set::union types more-types)
             table
             uid))
    :measure (structdecl-list-count structdecls))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-structdeclor ((structdeclor structdeclorp)
                              (previous ident-listp)
                              (type typep)
                              (table valid-tablep)
                              (uid uidp)
                              (ienv ienvp))
    :guard (structdeclor-unambp structdeclor)
    :returns (mv (erp maybe-msgp)
                 (new-structdeclor structdeclorp)
                 (new-previous ident-listp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a structure declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "The @('previous') input and @('new-previous') output
       have the same meaning as in @(tsee valid-structdecl).")
     (xdoc::p
      "The @('type') input comes from the list of specifiers and qualifiers
       that precedes the list of structure declarators
       of which this structure declarator is an element.
       We ensure that there is either a declarator or a constant expression
       (this is actually a syntactic constraint,
       but it is currently not captured in the abstract syntax,
       so we check it here).
       If there is a declarator, we validate it,
       and we add the declared identifier to the list member names,
       after ensuring that it is not already there.
       If there is a constant expression, we validate it,
       but for now we do not perform any checks related to its value
       [C17:6.7.2.1/4];
       we also do not constrain the types of bit fields [C17:6.7.2.1/5],
       but we ensure that the constant expression, if present, is integer."))
    (b* (((reterr) (irr-structdeclor) nil nil (irr-valid-table) (irr-uid))
         ((structdeclor structdeclor) structdeclor)
         ((when (and (not structdeclor.declor?)
                     (not structdeclor.expr?)))
          (retmsg$ "The structure declarator ~x0 is empty."
                   (structdeclor-fix structdeclor)))
         ((erp new-declor? & ident? types table uid)
          (valid-declor-option
            structdeclor.declor? type table uid ienv))
         (previous (ident-list-fix previous))
         ((when (and ident?
                     (member-equal ident? previous)))
          (retmsg$ "The structure declarator ~x0 ~
                    duplicates the member name."
                   (structdeclor-fix structdeclor)))
         (previous (if ident?
                       (rcons ident? previous)
                     previous))
         ((erp new-expr? width-type? more-types table uid)
          (valid-const-expr-option structdeclor.expr? table uid ienv))
         ((when (and width-type?
                     (not (type-integerp width-type?))
                     (not (type-case width-type? :unknown))))
          (retmsg$ "The structure declarator ~x0 ~
                    has a width of type ~x1."
                   (structdeclor-fix structdeclor)
                   width-type?)))
      (retok (make-structdeclor :declor? new-declor? :expr? new-expr?)
             previous
             (set::union types more-types)
             table
             uid))
    :measure (structdeclor-count structdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-structdeclor-list ((structdeclors structdeclor-listp)
                                   (previous ident-listp)
                                   (type typep)
                                   (table valid-tablep)
                                   (uid uidp)
                                   (ienv ienvp))
    :guard (structdeclor-list-unambp structdeclors)
    :returns (mv (erp maybe-msgp)
                 (new-structdeclors structdeclor-listp)
                 (new-previous ident-listp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list structure declarators."
    :long
    (xdoc::topstring
     (xdoc::p
      "We validate each structure declarator in turn,
       threading the data through.
       Note that the same type
       (coming from the list of specifiers and qualifiers)
       is passed to the validation function for each structure declarator,
       since that type applied to all them
       (possibly refined, possibly differently, by the structure declarators."))
    (b* (((reterr) nil nil nil (irr-valid-table) (irr-uid))
         (uid (uid-fix uid))
         ((when (endp structdeclors))
          (retok nil
                 (ident-list-fix previous)
                 nil
                 (valid-table-fix table)
                 uid))
         ((erp new-structdeclor previous types table uid)
          (valid-structdeclor
            (car structdeclors) previous type table uid ienv))
         ((erp new-structdeclors previous more-types table uid)
          (valid-structdeclor-list
           (cdr structdeclors) previous type table uid ienv)))
      (retok (cons new-structdeclor new-structdeclors)
             previous
             (set::union types more-types)
             table
             uid))
    :measure (structdeclor-list-count structdeclors))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-enumspec ((enumspec enumspecp)
                          (table valid-tablep)
                          (uid uidp)
                          (ienv ienvp))
    :guard (enumspec-unambp enumspec)
    :returns (mv (erp maybe-msgp)
                 (new-enumspec enumspecp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an enumeration specifier."
    :long
    (xdoc::topstring
     (xdoc::p
      "We check that there is at least a name of a list of enumerators;
       although this is a syntactic constraint,
       it is currently not captured in our abstract syntax,
       so we double-check it here.")
     (xdoc::p
      "For now our validation tables include
       no information about enumeration tags,
       so we do not extend the validation table,
       if the enumeration specifier has a name.
       However, we validate the enumerators, if present."))
    (b* (((reterr) (irr-enumspec) nil (irr-valid-table) (irr-uid))
         ((enumspec enumspec) enumspec)
         ((when (and (not enumspec.name)
                     (endp enumspec.list)))
          (retmsg$ "The enumeration specifier ~x0 ~
                    has no name and no enumerators."
                   (enumspec-fix enumspec)))
         ((erp new-list types table uid)
          (valid-enumer-list enumspec.list table uid ienv)))
      (retok (make-enumspec :name enumspec.name
                            :list new-list
                            :final-comma enumspec.final-comma)
             types
             table
             uid))
    :measure (enumspec-count enumspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-enumer ((enumer enumerp)
                        (table valid-tablep)
                        (uid uidp)
                        (ienv ienvp))
    :guard (enumer-unambp enumer)
    :returns (mv (erp maybe-msgp)
                 (new-enumer enumerp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an enumerator."
    :long
    (xdoc::topstring
     (xdoc::p
      "The enumeration constant is added to the validation table [C17:6.2.1/7],
       unless there is already an ordinary identifier
       with the same name and in the same (i.e. current) scope;
       since enumeration constants have no linkage [C17:6.2.2/6],
       they can be only declared once in the same scope [C17:6.7/3].
       If there is a constant expression,
       we validate it and check that it has integer type,
       but for now we do not check that the value
       is representable as @('int') [C17:6.7.2.2/2]."))
    (b* (((reterr) (irr-enumer) nil (irr-valid-table) (irr-uid))
         ((enumer enumer) enumer)
         ((mv info? currentp) (valid-lookup-ord enumer.name table))
         ((when (and info? currentp))
          (retmsg$ "The enumerator declared in ~x0 ~
                    in already declared in the current scope ~
                    with associated information ~x1."
                   (enumer-fix enumer) info?))
         (table (valid-add-ord enumer.name (valid-ord-info-enumconst) table))
         ((erp new-value type? types table uid)
          (valid-const-expr-option enumer.value table uid ienv))
         ((when (and type?
                     (not (type-integerp type?))
                     (not (type-case type? :unknown))))
          (retmsg$ "The value of the numerator ~x0 has type ~x1."
                   (enumer-fix enumer) type?)))
      (retok (make-enumer :name enumer.name :value new-value)
             types
             table
             uid))
    :measure (enumer-count enumer))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-enumer-list ((enumers enumer-listp)
                             (table valid-tablep)
                             (uid uidp)
                             (ienv ienvp))
    :guard (enumer-list-unambp enumers)
    :returns (mv (erp maybe-msgp)
                 (new-enumers enumer-listp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of enumerators."
    :long
    (xdoc::topstring
     (xdoc::p
      "We go through each enumerator in order,
       extending the validation table with each."))
    (b* (((reterr) nil nil (irr-valid-table) (irr-uid))
         (uid (uid-fix uid))
         ((when (endp enumers))
          (retok nil nil (valid-table-fix table) uid))
         ((erp new-enumer types table uid)
          (valid-enumer (car enumers) table uid ienv))
         ((erp new-enumers more-types table uid)
          (valid-enumer-list (cdr enumers) table uid ienv)))
      (retok (cons new-enumer new-enumers)
             (set::union types more-types)
             table
             uid))
    :measure (enumer-list-count enumers))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-statassert ((statassert statassertp)
                            (table valid-tablep)
                            (uid uidp)
                            (ienv ienvp))
    :guard (statassert-unambp statassert)
    :returns (mv (erp maybe-msgp)
                 (new-statassert statassertp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a static assertion declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "We validate the constant expression, which must be integer [C17:6.7.10/3],
       and we validate the string literal(s)."))
    (b* (((reterr) (irr-statassert) nil (irr-valid-table) (irr-uid))
         ((statassert statassert) statassert)
         ((erp new-test type types table uid)
          (valid-const-expr statassert.test table uid ienv))
         ((unless (or (type-integerp type)
                      (type-case type :unknown)))
          (retmsg$ "The expression in the static assertion declaration ~x0 ~
                    has type ~x1."
                   (statassert-fix statassert)
                   type))
         ((erp &) (valid-stringlit-list statassert.message ienv)))
      (retok (make-statassert :test new-test :message statassert.message)
             types
             table
             uid))
    :measure (statassert-count statassert))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-initdeclor ((initdeclor initdeclorp)
                            (type typep)
                            (storspecs stor-spec-listp)
                            (table valid-tablep)
                            (uid uidp)
                            (ienv ienvp))
    :guard (initdeclor-unambp initdeclor)
    :returns (mv (erp maybe-msgp)
                 (new-initdeclor initdeclorp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate an initializer declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "Initializer declarators [C17:6.7/1]
       appear in declarations, after declaration specifiers.
       The latter determine a type, passed as input,
       which an initializer declarator may refine.
       We also pass as input the storage class specifiers
       extracted from the declaration specifiers.")
     (xdoc::p
      "We validate the declarator,
       which returns the identifier and the possibly refined type.
       Here the @('fundef-params-p') flag is always @('nil'),
       because we are not in a function definition.")
     (xdoc::p
      "Then we validate the storage class specifiers,
       which together with the identifier and final type
       determine whether we are declaring a @('typedef'),
       and what the linkage and lifetime are.")
     (xdoc::p
      "If the @('typedef') flag is @('t'),
       there must be no initializer,
       because we are not declaring an object.
       In this case, we add the @('typedef') to the validation table.
       A @('typedef') may be redefined in the same scope
       assuming the two types are compatible and not variably modified
       [C17:6.7/3] (the latter of which is inexpressible in our current
       approximate type system
       so we conservatively permit redefinition of any compatible types).")
     (xdoc::p
      "If the @('typedef') flag is @('nil'),
       the identifier may denote a function or an object.
       The initializer may be present only if
       the type is not that of a function,
       because initializers only apply to objects,
       and the type is not void,
       because the type must be complete [C17:6.7.9/3].
       We validate the initializer if present;
       we pass the type of the identifier,
       so the initializer is checked against that.")
     (xdoc::p
      "We calculate the definition status for the declaration.
       If we are declaring a function, the status is undefined,
       because we do not have a function body here.
       Otherwise, we are declaring an object.
       If we are in a block scope,
       the status is undefined if the object has external linkage
       (because it refers to some external entity from the block),
       while it is defined otherwise
       (because the declaration allocates storage for the object).
       If we are in a file scope, we follow [C17:6.9.2/1] and [C17:6.9.2/2]:
       an initializer makes the status defined;
       otherwise, the presence of @('extern') makes the status undefined
       and its absence makes the status defined.
       This is slightly different from what [C17:6.9.2/2] says,
       which mentions no storage class specifier or @('static'),
       but it seems clear that this neglects to consider @('_Thread_local');
       in fact, the wording in the newly released C23 standard is clearer.")
     (xdoc::p
      "We look up the identifier in the validation table.
       If no information is found in the validation table,
       we add the identifier to the table.
       If the current declaration has no linkage,
       or if the information in the table has no linkage
       (which includes the case of the information in the table
       being for a @('typedef') or an enumeration constant),
       the two must denote different entities,
       and thus we ensure that the one in the table
       is not in the same (i.e. current) scope [C17:6.2.1/4] [C17:6.7/3];
       if the checks pass, we add the identifier to the table.
       If instead both have internal or external linkage,
       they must refer to the same entity,
       and so we ensure that the types are the same.
       We also need to check that the linkages are the same,
       in which case we still add the identifier to the table,
       to record that it is also declared in the current scope;
       in this case, it is not clear whether we should suitable combine
       the old and new definition statuses,
       but for now we just use the newest.
       It is an error if the current linkage is internal
       while the one in the table is external.
       The situation where the current one is external
       while the one in the table is internal cannot happen,
       because as defined in @(tsee valid-stor-spec-list),
       the current one would ``inherit''
       the internal linkage from the previous one.")
     (xdoc::p
      "For now we ignore the optional assembler name specifier,
       as well as any attribute specifiers."))
    (b* (((reterr) (irr-initdeclor) nil (irr-valid-table) (irr-uid))
         (uid (uid-fix uid))
         ((initdeclor initdeclor) initdeclor)
         ((erp new-declor & type ident types table uid)
          (valid-declor initdeclor.declor nil type table uid ienv))
         ((erp typedefp linkage lifetime?)
          (valid-stor-spec-list storspecs ident type nil table))
         ((when typedefp)
          (b* (((when initdeclor.init?)
                (retmsg$ "The typedef name ~x0 ~
                          has an initializer ~x1."
                         ident initdeclor.init?))
               ((mv info? currentp) (valid-lookup-ord ident table))
               ((when (and info?
                           currentp
                           (or (not (valid-ord-info-case info? :typedef))
                               (not (type-compatiblep
                                     (valid-ord-info-typedef->def info?)
                                     type)))))
                (retmsg$ "The typedef name ~x0 ~
                          is already declared in the current scope ~
                          with associated information ~x1."
                         ident info?))
               (table (valid-add-ord ident (valid-ord-info-typedef type) table)))
            (retok (make-initdeclor :declor new-declor
                                    :asm? initdeclor.asm?
                                    :attribs initdeclor.attribs
                                    :init? nil)
                   types
                   table
                   uid)))
         ((when (and initdeclor.init?
                     (or (type-case type :function)
                         (type-case type :void))))
          (retmsg$ "The identifier ~x0 has type ~x1, ~
                    which disallows the initializer, ~
                    but the initializer ~x2 is present."
                   ident type initdeclor.init?))
         ((erp new-init? more-types table uid)
          (valid-initer-option
            initdeclor.init? type lifetime? table uid ienv))
         (defstatus (if (type-case type :function)
                        (valid-defstatus-undefined)
                      (if (> (valid-table-num-scopes table) 1)
                          (if (linkage-case linkage :external)
                              (valid-defstatus-undefined)
                            (valid-defstatus-defined))
                        (if initdeclor.init?
                            (valid-defstatus-defined)
                          (if (member-equal (stor-spec-extern)
                                            (stor-spec-list-fix storspecs))
                              (valid-defstatus-undefined)
                            (valid-defstatus-tentative))))))
         ((mv info? currentp) (valid-lookup-ord ident table))
         ((when (not info?))
          (b* ((new-info (make-valid-ord-info-objfun
                          :type type
                          :linkage linkage
                          :defstatus defstatus
                          :uid uid))
               (uid (uid-increment uid))
               (table (valid-add-ord ident new-info table)))
            (retok (make-initdeclor :declor new-declor
                                    :asm? initdeclor.asm?
                                    :attribs initdeclor.attribs
                                    :init? new-init?)
                   (set::union types more-types)
                   table
                   uid)))
         ((when (or (valid-ord-info-case info? :typedef)
                    (valid-ord-info-case info? :enumconst)))
          (if currentp
              (retmsg$ "The identifier ~x0 ~
                        is already declared in the current scope ~
                        with associated information ~x1."
                       ident info?)
            (b* ((new-info (make-valid-ord-info-objfun
                            :type type
                            :linkage linkage
                            :defstatus defstatus
                            :uid uid))
                 (uid (uid-increment uid))
                 (table (valid-add-ord ident new-info table)))
              (retok (make-initdeclor :declor new-declor
                                      :asm? initdeclor.asm?
                                      :attribs initdeclor.attribs
                                      :init? new-init?)
                     (set::union types more-types)
                     table
                     uid))))
         ((valid-ord-info-objfun info) info?)
         ((when (or (linkage-case linkage :none)
                    (linkage-case info.linkage :none)))
          (if currentp
              (retmsg$ "The identifier ~x0 ~
                        is already declared in the current scope ~
                        with associated information ~x1."
                       ident info?)
            (b* ((new-info (make-valid-ord-info-objfun
                            :type type
                            :linkage linkage
                            :defstatus defstatus
                            :uid uid))
                 (uid (uid-increment uid))
                 (table (valid-add-ord ident new-info table)))
              (retok (make-initdeclor :declor new-declor
                                      :asm? initdeclor.asm?
                                      :attribs initdeclor.attribs
                                      :init? new-init?)
                     (set::union types more-types)
                     table
                     uid))))
         ((unless (or (equal type info.type)
                      (equal type (type-unknown))
                      (equal info.type (type-unknown))))
          (retmsg$ "The identifier ~x0 ~
                    is declared with type ~x1 ~
                    after being declared with type ~x2."
                   ident type info.type))
         ((when (and (linkage-case linkage :internal)
                     (linkage-case info.linkage :external)))
          (retmsg$ "The identifier ~x0 ~
                    is declared with internal linkage ~
                    after being declared with external linkage."
                   ident))
         ((when (and (linkage-case linkage :external)
                     (linkage-case info.linkage :internal)))
          (raise "Internal error: ~ the identifier ~x0 ~
                  is declared with external linkage ~
                  after being declared with internal linkage."
                 ident)
          (retmsg$ ""))
         (new-info (make-valid-ord-info-objfun
                    :type type
                    :linkage linkage
                    :defstatus defstatus
                    :uid uid))
         (uid (uid-increment uid))
         (table (valid-add-ord ident new-info table)))
      (retok (make-initdeclor :declor new-declor
                              :asm? initdeclor.asm?
                              :attribs initdeclor.attribs
                              :init? new-init?)
             (set::union types more-types)
             table
             uid))
    :measure (initdeclor-count initdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-initdeclor-list ((initdeclors initdeclor-listp)
                                 (type typep)
                                 (storspecs stor-spec-listp)
                                 (table valid-tablep)
                                 (uid uidp)
                                 (ienv ienvp))
    :guard (initdeclor-list-unambp initdeclors)
    :returns (mv (erp maybe-msgp)
                 (new-initdeclors initdeclor-listp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of initializer declarators."
    :long
    (xdoc::topstring
     (xdoc::p
      "The type and storage class specifiers come from
       the declaration specifiers that precede the initializer declarators.
       We validate each in turn."))
    (b* (((reterr) nil nil (irr-valid-table) (irr-uid))
         ((when (endp initdeclors))
          (retok nil nil (valid-table-fix table) (uid-fix uid)))
         ((erp new-initdeclor types table uid)
          (valid-initdeclor
            (car initdeclors) type storspecs table uid ienv))
         ((erp new-initdeclors more-types table uid)
          (valid-initdeclor-list
            (cdr initdeclors) type storspecs table uid ienv)))
      (retok (cons new-initdeclor new-initdeclors)
             (set::union types more-types)
             table
             uid))
    :measure (initdeclor-list-count initdeclors))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-decl ((decl declp)
                      (table valid-tablep)
                      (uid uidp)
                      (ienv ienvp))
    :guard (decl-unambp decl)
    :returns (mv (erp maybe-msgp)
                 (new-decl declp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "If it is a static assertion declaration,
       we validate it using a separate validation function.
       Otherwise, we first validate the declaration specifiers
       and then the list of initializer declarators,
       passing information from the former to the latter.
       We ensure that the list of initializer declarators is not empty
       (i.e. there is at least a declarator),
       or the declaration specifiers declare a tag,
       as required in [C17:6.7/2].
       We ignore the GCC extension for now."))
    (b* (((reterr) (irr-decl) nil (irr-valid-table) (irr-uid)))
      (decl-case
       decl
       :decl
       (b* (((erp new-specs type storspecs types table uid)
             (valid-decl-spec-list
               decl.specs nil nil nil table uid ienv))
            ((when (and (endp decl.init)
                        (not (type-case type :struct))
                        (not (type-case type :union))
                        (not (type-case type :enum))))
             (retmsg$ "The declaration ~x0 declares ~
                       neither a declarator nor a tag."
                      (decl-fix decl)))
            ((erp new-init more-types table uid)
             (valid-initdeclor-list
               decl.init type storspecs table uid ienv)))
         (retok (make-decl-decl :extension decl.extension
                                :specs new-specs
                                :init new-init)
                (set::union types more-types)
                table
                uid))
       :statassert
       (b* (((erp new-statassert types table uid)
             (valid-statassert decl.unwrap table uid ienv)))
         (retok (decl-statassert new-statassert)
                types
                table
                uid))))
    :measure (decl-count decl))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-decl-list ((decls decl-listp)
                           (table valid-tablep)
                           (uid uidp)
                           (ienv ienvp))
    :guard (decl-list-unambp decls)
    :returns (mv (erp maybe-msgp)
                 (new-decls decl-listp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of declarations."
    :long
    (xdoc::topstring
     (xdoc::p
      "We validate each one in turn."))
    (b* (((reterr) nil nil (irr-valid-table) (irr-uid))
         ((when (endp decls))
          (retok nil nil (valid-table-fix table) (uid-fix uid)))
         ((erp new-decl types table uid)
          (valid-decl (car decls) table uid ienv))
         ((erp new-decls more-types table uid)
          (valid-decl-list (cdr decls) table uid ienv)))
      (retok (cons new-decl new-decls)
             (set::union types more-types)
             table
             uid))
    :measure (decl-list-count decls))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-label ((label labelp)
                       (table valid-tablep)
                       (uid uidp)
                       (ienv ienvp))
    :guard (label-unambp label)
    :returns (mv (erp maybe-msgp)
                 (new-label labelp)
                 (return-types type-setp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a label."
    :long
    (xdoc::topstring
     (xdoc::p
      "For now this just amounts to validating the constant expression(s),
       for the case of a @('case') label,
       and ensuring it/they has/have integer type [C17:6.8.4.2/3];
       in the future, we should collect labels in the validation table
       so that we can check that referenced labels are in scope.
       Also, for now we do not check that @('case') and @('default') labels
       only appear in @('switch') statements [C17:6.8.1/2]."))
    (b* (((reterr) (irr-label) nil (irr-valid-table) (irr-uid))
         (uid (uid-fix uid)))
      (label-case
       label
       :name
       (retok (label-name label.unwrap) nil (valid-table-fix table) uid)
       :casexpr
       (b* (((erp new-expr type types table uid)
             (valid-const-expr label.expr table uid ienv))
            ((unless (or (type-integerp type)
                         (type-case type :unknown)))
             (retmsg$ "The first or only 'case' expression ~
                       in the label ~x0 has type ~x1."
                      (label-fix label) type))
            ((erp new-range? type? more-types table uid)
             (valid-const-expr-option label.range? table uid ienv))
            ((when (and type?
                        (not (type-integerp type?))
                        (not (type-case type? :unknown))))
             (retmsg$ "The second 'case' expression~
                       in the label ~x0 has type ~x1."
                      (label-fix label) type?)))
         (retok (make-label-casexpr :expr new-expr :range? new-range?)
                (set::union types more-types)
                table
                uid))
       :default
       (retok (label-default) nil (valid-table-fix table) uid)))
    :measure (label-count label))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-stmt ((stmt stmtp)
                      (table valid-tablep)
                      (uid uidp)
                      (ienv ienvp))
    :guard (stmt-unambp stmt)
    :returns (mv (erp maybe-msgp)
                 (new-stmt stmtp)
                 (return-types type-setp)
                 (last-expr-type? type-optionp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a statement."
    :long
    (xdoc::topstring
     (xdoc::p
      "If validation is successful, we return,
       besides an updated validation table,
       also two pieces of type information.")
     (xdoc::p
      "The first piece is the set of types returned by the statement,
       via @('return') statements, with or without expressions.
       This is a set because a statement may contain
       multiple @('return') sub-statements.
       A @('return') statement with an expression
       contributes the type of the expression to the set;
       a @('return') statement without an expression
       contributes the type @('void') to the set.")
     (xdoc::p
      "The second piece of information is as follows.
       If the statement is either a (possibly labeled) expression statement,
       or is a (possibly labeled) compound one
       whose last block item is an expression statement,
       the second piece of information is the type of that expression.
       If the statement is not an expression or compound,
       or it is compound but does not end in an expression statement
       (including the case in which the compound statement has no block items),
       the second piece of information is @('nil').
       The reason for having this second piece of information
       is to support the validation of "
      (xdoc::ahref "https://gcc.gnu.org/onlinedocs/gcc/Statement-Exprs.html"
                   "GCC statement expressions")
      ".")
     (xdoc::p
      "To validate a labeled statement,
       we validate its label, and then the enclosed statement.
       We return the union of the return types,
       and the optional type from the statement.
       For now we do not check the requirements in
       [C17:6.8.1/2] and [C17:6.8.1/3].")
     (xdoc::p
      "To validate a compound statement,
       we push a new scope for the block,
       and we validate the list of block items.
       We pop the scope and we return the same results
       coming from the validation of the block items.")
     (xdoc::p
      "To validate an expression statement,
       we validate the expression if present,
       and return its type as the second result;
       this is @('nil') if there is no expression.
       The return types are the same as the ones of the expression.")
     (xdoc::p
      "A selection statement and its sub-statements are blocks [C17:6.8.4/3],
       so we push and pop scopes accordingly.
       We check that the test of @('if') has scalar type [C17:6.8.4.1/1]
       and that the target of @('switch') has integer type [C17:6.8.4.2/1].
       No type is returned as the @('last-expr-type?') result,
       because a selection statement is not an expression statement
       (see criterion above for that result of this validation function).")
     (xdoc::p
      "An iteration statement and its sub-statements are blocks [C17:6.8.5/5],
       so we push and pop scopes accordingly.
       We check that the test expression has scalar type.
       No type is returned as the @('last-expr-type?') result,
       because an iteraion statement is not an expression statement
       (see criterion above for that result of this validation function).
       For now we do not enforce that the declaration in a @('for')
       only uses the storage class specifiers @('auto') and @('register').")
     (xdoc::p
      "For now we do not check constraints on
       the label of a @('goto') [C17:6.8.6.1/1],
       the occurrence of @('continue') [C17:6.8.6.2/2],
       and the occurrence of @('break') [C17:6.8.6.3/1].")
     (xdoc::p
      "A @('return') statement explicitly adds a type to the return types,
       either the type of the expression,
       or @('void') is there is no expression.
       We check the constraints on occurrences [C17:6.8.6.4/1]
       in the validation function for function definitions.")
     (xdoc::p
      "For now we do not check any constraints on assembler statements."))
    (b* (((reterr) (irr-stmt) nil nil (irr-valid-table) (irr-uid))
         (uid (uid-fix uid)))
      (stmt-case
       stmt
       :labeled
       (b* (((erp new-label types table uid)
             (valid-label stmt.label table uid ienv))
            ((erp new-stmt more-types type? table uid)
             (valid-stmt stmt.stmt table uid ienv)))
         (retok (make-stmt-labeled :label new-label :stmt new-stmt)
                (set::union types more-types)
                type?
                table
                uid))
       :compound
       (b* ((table (valid-push-scope table))
            ((erp new-items types type? table uid)
             (valid-block-item-list stmt.items table uid ienv))
            (table (valid-pop-scope table)))
         (retok (stmt-compound new-items) types type? table uid))
       :expr
       (b* (((erp new-expr? type? types table uid)
             (valid-expr-option stmt.expr? table uid ienv)))
         (retok (make-stmt-expr :expr? new-expr? :info nil)
                types
                type?
                table
                uid))
       :if
       (b* ((table (valid-push-scope table))
            ((erp new-test test-type test-types table uid)
             (valid-expr stmt.test table uid ienv))
            ((unless (or (type-scalarp test-type)
                         (type-case test-type :unknown)))
             (retmsg$ "The test of the statement ~x0 has type ~x1."
                       (stmt-fix stmt) test-type))
            (table (valid-push-scope table))
            ((erp new-then then-types & table uid)
             (valid-stmt stmt.then table uid ienv))
            (table (valid-pop-scope table))
            (table (valid-pop-scope table)))
         (retok (make-stmt-if :test new-test :then new-then)
                (set::union test-types then-types)
                nil
                table
                uid))
       :ifelse
       (b* ((table (valid-push-scope table))
            ((erp new-test test-type test-types table uid)
             (valid-expr stmt.test table uid ienv))
            ((unless (or (type-scalarp test-type)
                         (type-case test-type :unknown)))
             (retmsg$ "The test of the statement ~x0 has type ~x1."
                      (stmt-fix stmt) test-type))
            (table (valid-push-scope table))
            ((erp new-then then-types & table uid)
             (valid-stmt stmt.then table uid ienv))
            (table (valid-pop-scope table))
            (table (valid-push-scope table))
            ((erp new-else else-types & table uid)
             (valid-stmt stmt.else table uid ienv))
            (table (valid-pop-scope table))
            (table (valid-pop-scope table)))
         (retok (make-stmt-ifelse :test new-test :then new-then :else new-else)
                (set::union test-types (set::union then-types else-types))
                nil
                table
                uid))
       :switch
       (b* ((table (valid-push-scope table))
            ((erp new-target target-type target-types table uid)
             (valid-expr stmt.target table uid ienv))
            ((unless (or (type-integerp target-type)
                         (type-case target-type :unknown)))
             (retmsg$ "The target of the statement ~x0 has type ~x1."
                      (stmt-fix stmt) target-type))
            (table (valid-push-scope table))
            ((erp new-body body-types & table uid)
             (valid-stmt stmt.body table uid ienv))
            (table (valid-pop-scope table))
            (table (valid-pop-scope table)))
         (retok (make-stmt-switch :target new-target :body new-body)
                (set::union target-types body-types)
                nil
                table
                uid))
       :while
       (b* ((table (valid-push-scope table))
            ((erp new-test test-type test-types table uid)
             (valid-expr stmt.test table uid ienv))
            ((unless (or (type-scalarp test-type)
                         (type-case test-type :unknown)))
             (retmsg$ "The test of the statement ~x0 has type ~x1."
                      (stmt-fix stmt) test-type))
            (table (valid-push-scope table))
            ((erp new-body  body-types & table uid)
             (valid-stmt stmt.body table uid ienv))
            (table (valid-pop-scope table))
            (table (valid-pop-scope table))
            (types (set::union test-types body-types)))
         (retok (make-stmt-while :test new-test :body new-body)
                types
                nil
                table
                uid))
       :dowhile
       (b* ((table (valid-push-scope table))
            (table (valid-push-scope table))
            ((erp new-body body-types & table uid)
             (valid-stmt stmt.body table uid ienv))
            (table (valid-pop-scope table))
            ((erp new-test test-type test-types table uid)
             (valid-expr stmt.test table uid ienv))
            ((unless (or (type-scalarp test-type)
                         (type-case test-type :unknown)))
             (retmsg$ "The test of the statement ~x0 has type ~x1."
                      (stmt-fix stmt) test-type))
            (table (valid-pop-scope table)))
         (retok (make-stmt-dowhile :body new-body :test new-test)
                (set::union test-types body-types)
                nil
                table
                uid))
       :for-expr
       (b* ((table (valid-push-scope table))
            ((erp new-init & init-types table uid)
             (valid-expr-option stmt.init table uid ienv))
            ((erp new-test test-type? test-types table uid)
             (valid-expr-option stmt.test table uid ienv))
            ((when (and test-type?
                        (not (type-scalarp test-type?))
                        (not (type-case test-type? :unknown))))
             (retmsg$ "The test of the statement ~x0 has type ~x1."
                      (stmt-fix stmt) test-type?))
            ((erp new-next & next-types table uid)
             (valid-expr-option stmt.next table uid ienv))
            (table (valid-push-scope table))
            ((erp new-body body-types & table uid)
             (valid-stmt stmt.body table uid ienv))
            (table (valid-pop-scope table))
            (table (valid-pop-scope table)))
         (retok (make-stmt-for-expr :init new-init
                                    :test new-test
                                    :next new-next
                                    :body new-body)
                (set::union init-types
                            (set::union test-types
                                        (set::union next-types
                                                    body-types)))
                nil
                table
                uid))
       :for-decl
       (b* ((table (valid-push-scope table))
            ((erp new-init init-types table uid)
             (valid-decl stmt.init table uid ienv))
            ((erp new-test test-type? test-types table uid)
             (valid-expr-option stmt.test table uid ienv))
            ((when (and test-type?
                        (not (type-scalarp test-type?))
                        (not (type-case test-type? :unknown))))
             (retmsg$ "The test of the statement ~x0 has type ~x1."
                      (stmt-fix stmt) test-type?))
            ((erp new-next & next-types table uid)
             (valid-expr-option stmt.next table uid ienv))
            (table (valid-push-scope table))
            ((erp new-body body-types & table uid)
             (valid-stmt stmt.body table uid ienv))
            (table (valid-pop-scope table))
            (table (valid-pop-scope table)))
         (retok (make-stmt-for-decl :init new-init
                                    :test new-test
                                    :next new-next
                                    :body new-body)
                (set::union init-types
                            (set::union test-types
                                        (set::union next-types
                                                    body-types)))
                nil
                table
                uid))
       :for-ambig
       (prog2$ (impossible) (retmsg$ ""))
       :goto
       (retok (stmt-goto stmt.label) nil nil (valid-table-fix table) uid)
       :continue
       (retok (stmt-continue) nil nil (valid-table-fix table) uid)
       :break
       (retok (stmt-break) nil nil (valid-table-fix table) uid)
       :return
       (b* (((erp new-expr? type? types table uid)
             (valid-expr-option stmt.expr? table uid ienv))
            (return-type (or type? (type-void))))
         (retok (make-stmt-return :expr? new-expr? :info nil)
                (set::insert return-type types)
                nil
                table
                uid))
       :asm
       (retok (stmt-asm stmt.unwrap) nil nil (valid-table-fix table) uid)))
    :measure (stmt-count stmt))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-block-item ((item block-itemp)
                            (table valid-tablep)
                            (uid uidp)
                            (ienv ienvp))
    :guard (block-item-unambp item)
    :returns (mv (erp maybe-msgp)
                 (new-item block-itemp)
                 (return-types type-setp)
                 (last-expr-type? type-optionp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a block item."
    :long
    (xdoc::topstring
     (xdoc::p
      "If validation is successful, we return the same kind of type results
       as @(tsee valid-stmt) (see that function's documentation),
       with the slight modification that
       the @('last-expr-type?') result is a type exactly when
       the block item is a compound statement
       whose last block item is an expression statement,
       in which case the @('last-expr-type?') result is
       the type of that expression.")
     (xdoc::p
      "If the block item is a declaration,
       the @('last-expr-type?') result is @('nil'),
       because the block item is not a statement of the kind
       described in @(tsee valid-stmt)."))
    (b* (((reterr) (irr-block-item) nil nil (irr-valid-table) (irr-uid))
         (info (make-block-item-info :table-start table)))
      (block-item-case
       item
       :decl (b* (((erp new-decl types table uid)
                   (valid-decl item.decl table uid ienv)))
               (retok (make-block-item-decl :decl new-decl :info info)
                      types
                      nil
                      table
                      uid))
       :stmt (b* (((erp new-stmt types last-expr-type? table uid)
                   (valid-stmt item.stmt table uid ienv)))
               (retok (make-block-item-stmt :stmt new-stmt :info info)
                      types
                      last-expr-type?
                      table
                      uid))
       :ambig (prog2$ (impossible) (retmsg$ ""))))
    :measure (block-item-count item))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define valid-block-item-list ((items block-item-listp)
                                 (table valid-tablep)
                                 (uid uidp)
                                 (ienv ienvp))
    :guard (block-item-list-unambp items)
    :returns (mv (erp maybe-msgp)
                 (new-items block-item-listp)
                 (return-types type-setp)
                 (last-expr-type? type-optionp)
                 (new-table valid-tablep)
                 (new-uid uidp))
    :parents (validator valid-exprs/decls/stmts)
    :short "Validate a list of block items."
    :long
    (xdoc::topstring
     (xdoc::p
      "If validation is successful, we return the same kind of type results
       as @(tsee valid-stmt) (see that function's documentation),
       with the modification that
       the @('last-expr-type?') result is a type exactly when
       the list of block items is not empty
       and the validation of the last block item
       returns a type as that result."))
    (b* (((reterr) nil nil nil (irr-valid-table) (irr-uid))
         (uid (uid-fix uid))
         ((when (endp items))
          (retok nil nil nil (valid-table-fix table) uid))
         ((erp new-item types last-expr-type? table uid)
          (valid-block-item (car items) table uid ienv))
         ((when (endp (cdr items)))
          (retok (list new-item) types last-expr-type? table uid))
         ((erp new-items more-types last-expr-type? table uid)
          (valid-block-item-list (cdr items) table uid ienv)))
      (retok (cons new-item new-items)
             (set::union types more-types)
             last-expr-type?
             table
             uid))
    :measure (block-item-list-count items))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :hints (("Goal" :in-theory (enable o< o-finp)))

  :verify-guards nil ; done below

  :prepwork ((local (in-theory (enable acons))))

  ///

  (verify-guards valid-expr)

  (fty::deffixequiv-mutual valid-exprs/decls/stmts)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual valid-exprs/decls/stmts
    (defret expr-unambp-of-valid-expr
      (implies (not erp)
               (expr-unambp new-expr))
      :hyp (expr-unambp expr)
      :fn valid-expr
      :hints ('(:expand (valid-expr expr table uid ienv))))
    (defret expr-list-unambp-of-valid-expr-list
      (implies (not erp)
               (expr-list-unambp new-exprs))
      :hyp (expr-list-unambp exprs)
      :fn valid-expr-list)
    (defret expr-option-unambp-of-valid-expr-option
      (implies (not erp)
               (expr-option-unambp new-expr?))
      :hyp (expr-option-unambp expr?)
      :fn valid-expr-option)
    (defret const-expr-unambp-of-valid-const-expr
      (implies (not erp)
               (const-expr-unambp new-cexpr))
      :hyp (const-expr-unambp cexpr)
      :fn valid-const-expr)
    (defret const-expr-option-unambp-of-valid-const-expr-option
      (implies (not erp)
               (const-expr-option-unambp new-cexpr?))
      :hyp (const-expr-option-unambp cexpr?)
      :fn valid-const-expr-option)
    (defret genassoc-unambp-of-valid-genassoc
      (implies (not erp)
               (genassoc-unambp new-genassoc))
      :hyp (genassoc-unambp genassoc)
      :fn valid-genassoc)
    (defret genassoc-list-unambp-of-valid-genassoc-list
      (implies (not erp)
               (genassoc-list-unambp new-genassocs))
      :hyp (genassoc-list-unambp genassocs)
      :fn valid-genassoc-list)
    (defret member-designor-unambp-of-valid-member-designor
      (implies (not erp)
               (member-designor-unambp new-memdesign))
      :hyp (member-designor-unambp memdesign)
      :fn valid-member-designor)
    (defret type-spec-unambp-of-valid-type-spec
      (implies (not erp)
               (and (type-spec-unambp new-tyspec)
                    (type-spec-list-unambp new-tyspecs)))
      :hyp (and (type-spec-unambp tyspec)
                (type-spec-list-unambp tyspecs))
      :fn valid-type-spec
      :hints ('(:expand (:free (type?)
                               (valid-type-spec tyspec type? tyspecs table uid ienv)))))
    (defret spec/qual-unambp-of-valid-spec/qual
      (implies (not erp)
               (and (spec/qual-unambp new-specqual)
                    (type-spec-list-unambp new-tyspecs)))
      :hyp (and (spec/qual-unambp specqual)
                (type-spec-list-unambp tyspecs))
      :fn valid-spec/qual
      :hints ('(:expand (valid-spec/qual specqual type? tyspecs table uid ienv))))
    (defret spec/qual-list-unambp-of-valid-spec/qual-list
      (implies (not erp)
               (spec/qual-list-unambp new-specquals))
      :hyp (and (spec/qual-list-unambp specquals)
                (type-spec-list-unambp tyspecs))
      :fn valid-spec/qual-list)
    (defret align-spec-unambp-of-valid-align-spec
      (implies (not erp)
               (align-spec-unambp new-align))
      :hyp (align-spec-unambp align)
      :fn valid-align-spec)
    (defret decl-spec-unambp-of-valid-decl-spec
      (implies (not erp)
               (and (decl-spec-unambp new-declspec)
                    (type-spec-list-unambp new-tyspecs)))
      :hyp (and (decl-spec-unambp declspec)
                (type-spec-list-unambp tyspecs))
      :fn valid-decl-spec
      :hints ('(:expand (valid-decl-spec declspec type? tyspecs storspecs table uid ienv))))
    (defret decl-spec-list-unambp-of-valid-decl-spec-list
      (implies (not erp)
               (decl-spec-list-unambp new-declspecs))
      :hyp (and (decl-spec-list-unambp declspecs)
                (type-spec-list-unambp tyspecs))
      :fn valid-decl-spec-list
      :hints ('(:expand (:free (type?)
                               (valid-decl-spec-list declspecs type? tyspecs storspecs table uid ienv)))))
    (defret initer-unambp-of-valid-initer
      (implies (not erp)
               (initer-unambp new-initer))
      :hyp (initer-unambp initer)
      :fn valid-initer
      :hints ('(:expand (valid-initer initer target-type lifetime table uid ienv))))
    (defret initer-option-unambp-of-valid-initer-option
      (implies (not erp)
               (initer-option-unambp new-initer?))
      :hyp (initer-option-unambp initer?)
      :fn valid-initer-option
      :hints ('(:expand (valid-initer-option initer? target-type lifetime? table uid ienv))))
    (defret desiniter-unambp-of-valid-desiniter
      (implies (not erp)
               (desiniter-unambp new-desiniter))
      :hyp (desiniter-unambp desiniter)
      :fn valid-desiniter)
    (defret desiniter-list-unambp-of-valid-desiniter-list
      (implies (not erp)
               (desiniter-list-unambp new-desiniters))
      :hyp (desiniter-list-unambp desiniters)
      :fn valid-desiniter-list)
    (defret designor-unambp-of-valid-designor
      (implies (not erp)
               (designor-unambp new-designor))
      :hyp (designor-unambp designor)
      :fn valid-designor
      :hints ('(:expand (valid-designor designor target-type table uid ienv))))
    (defret designor-list-unambp-of-valid-designor-list
      (implies (not erp)
               (designor-list-unambp new-designors))
      :hyp (designor-list-unambp designors)
      :fn valid-designor-list)
    (defret declor-unambp-of-valid-declor
      (implies (not erp)
               (declor-unambp new-declor))
      :hyp (declor-unambp declor)
      :fn valid-declor)
    (defret declor-option-unambp-of-valid-declor-option
      (implies (not erp)
               (declor-option-unambp new-declor?))
      :hyp (declor-option-unambp declor?)
      :fn valid-declor-option)
    (defret dirdeclor-unambp-of-valid-dirdeclor
      (implies (not erp)
               (dirdeclor-unambp new-dirdeclor))
      :hyp (dirdeclor-unambp dirdeclor)
      :fn valid-dirdeclor
      :hints ('(:expand (valid-dirdeclor dirdeclor fundef-params-p type table uid ienv))))
    (defret absdeclor-unambp-of-valid-absdeclor
      (implies (not erp)
               (absdeclor-unambp new-absdeclor))
      :hyp (absdeclor-unambp absdeclor)
      :fn valid-absdeclor)
    (defret absdeclor-option-unambp-of-valid-absdeclor-option
      (implies (not erp)
               (absdeclor-option-unambp new-absdeclor?))
      :hyp (absdeclor-option-unambp absdeclor?)
      :fn valid-absdeclor-option)
    (defret dirabsdeclor-unambp-of-valid-dirabsdeclor
      (implies (not erp)
               (dirabsdeclor-unambp new-dirabsdeclor))
      :hyp (dirabsdeclor-unambp dirabsdeclor)
      :fn valid-dirabsdeclor
      :hints ('(:expand (valid-dirabsdeclor dirabsdeclor type table uid ienv))))
    (defret dirabsdeclor-option-unambp-of-valid-dirabsdeclor-option
      (implies (not erp)
               (dirabsdeclor-option-unambp new-dirabsdeclor?))
      :hyp (dirabsdeclor-option-unambp dirabsdeclor?)
      :fn valid-dirabsdeclor-option)
    (defret param-declon-unambp-of-valid-param-declon
      (implies (not erp)
               (param-declon-unambp new-paramdecl))
      :hyp (param-declon-unambp paramdecl)
      :fn valid-param-declon
      :hints ('(:expand (:free (fundef-params-p)
                               (valid-param-declon paramdecl fundef-params-p table uid ienv)))))
    (defret param-declon-list-unambp-of-valid-param-declon-list
      (implies (not erp)
               (param-declon-list-unambp new-paramdecls))
      :hyp (param-declon-list-unambp paramdecls)
      :fn valid-param-declon-list)
    (defret param-declor-unambp-of-valid-param-declor
      (implies (not erp)
               (param-declor-unambp new-paramdeclor))
      :hyp (param-declor-unambp paramdeclor)
      :fn valid-param-declor
      :hints ('(:expand (valid-param-declor paramdeclor type table uid ienv))))
    (defret tyname-unambp-of-valid-tyname
      (implies (not erp)
               (tyname-unambp new-tyname))
      :hyp (tyname-unambp tyname)
      :fn valid-tyname)
    (defret struni-spec-unambp-of-valid-struni-spec
      (implies (not erp)
               (struni-spec-unambp new-struni-spec))
      :hyp (struni-spec-unambp struni-spec)
      :fn valid-struni-spec)
    (defret structdecl-unambp-of-valid-structdecl
      (implies (not erp)
               (structdecl-unambp new-structdecl))
      :hyp (structdecl-unambp structdecl)
      :fn valid-structdecl
      :hints ('(:expand (valid-structdecl structdecl previous table uid ienv))))
    (defret structdecl-list-unambp-of-valid-structdecl-list
      (implies (not erp)
               (structdecl-list-unambp new-structdecls))
      :hyp (structdecl-list-unambp structdecls)
      :fn valid-structdecl-list)
    (defret structdeclor-unambp-of-valid-structdeclor
      (implies (not erp)
               (structdeclor-unambp new-structdeclor))
      :hyp (structdeclor-unambp structdeclor)
      :fn valid-structdeclor)
    (defret structdeclor-list-unambp-of-valid-structdeclor-list
      (implies (not erp)
               (structdeclor-list-unambp new-structdeclors))
      :hyp (structdeclor-list-unambp structdeclors)
      :fn valid-structdeclor-list)
    (defret enumspec-unambp-of-valid-enumspec
      (implies (not erp)
               (enumspec-unambp new-enumspec))
      :hyp (enumspec-unambp enumspec)
      :fn valid-enumspec)
    (defret enumer-unambp-of-valid-enumer
      (implies (not erp)
               (enumer-unambp new-enumer))
      :hyp (enumer-unambp enumer)
      :fn valid-enumer)
    (defret enumer-list-unambp-of-valid-enumer-list
      (implies (not erp)
               (enumer-list-unambp new-enumers))
      :hyp (enumer-list-unambp enumers)
      :fn valid-enumer-list)
    (defret statassert-unambp-of-valid-statassert
      (implies (not erp)
               (statassert-unambp new-statassert))
      :hyp (statassert-unambp statassert)
      :fn valid-statassert)
    (defret initdeclor-unambp-of-valid-initdeclor
      (implies (not erp)
               (initdeclor-unambp new-initdeclor))
      :hyp (initdeclor-unambp initdeclor)
      :fn valid-initdeclor
      :hints ('(:expand (valid-initdeclor initdeclor type storspecs table uid ienv))))
    (defret initdeclor-list-unambp-of-valid-initdeclor-list
      (implies (not erp)
               (initdeclor-list-unambp new-initdeclors))
      :hyp (initdeclor-list-unambp initdeclors)
      :fn valid-initdeclor-list)
    (defret decl-unambp-of-valid-decl
      (implies (not erp)
               (decl-unambp new-decl))
      :hyp (decl-unambp decl)
      :fn valid-decl)
    (defret decl-list-unambp-of-valid-decl-list
      (implies (not erp)
               (decl-list-unambp new-decls))
      :hyp (decl-list-unambp decls)
      :fn valid-decl-list
      :hints ('(:expand (valid-decl-list decls table uid ienv))))
    (defret label-unambp-of-valid-label
      (implies (not erp)
               (label-unambp new-label))
      :hyp (label-unambp label)
      :fn valid-label
      :hints ('(:expand (valid-label label table uid ienv))))
    (defret stmt-unambp-of-valid-stmt
      (implies (not erp)
               (stmt-unambp new-stmt))
      :hyp (stmt-unambp stmt)
      :fn valid-stmt
      :hints ('(:expand (valid-stmt stmt table uid ienv))))
    (defret block-item-unambp-of-valid-block-item
      (implies (not erp)
               (block-item-unambp new-item))
      :hyp (block-item-unambp item)
      :fn valid-block-item)
    (defret block-item-list-unambp-of-valid-block-item-list
      (implies (not erp)
               (block-item-list-unambp new-items))
      :hyp (block-item-list-unambp items)
      :fn valid-block-item-list)
    ;; We disable VALID-DECL-SPEC-LIST in general
    ;; Without this, the proof seems to hang, or at least take a very long time.
    :hints (("Goal" :in-theory (disable valid-decl-spec-list)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-fundef ((fundef fundefp)
                      (table valid-tablep)
                      (uid uidp)
                      (ienv ienvp))
  :guard (fundef-unambp fundef)
  :returns (mv (erp maybe-msgp)
               (new-fundef fundefp)
               (new-table valid-tablep)
               (new-uid uidp))
  :short "Validate a function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we ignore all the GCC extensions.
     We validate the declaration specifiers, then the declarator.
     It is an error if the validation of the declarator
     returns a non-empty set of types,
     because it means that there are statement expressions
     with return statements in them,
     which can only happen inside a function's body.
     We validate the storage class specifiers.
     It is an error if the declaration is for a @('typedef').
     We also ensure that the type is the function type [C17:6.9.1/2].")
   (xdoc::p
    "As with declarations, the scope of the function name
     starts just after its declarator;
     it must be added to the file scope of the validation table.
     However, recall that the validation of the declarator
     pushes a new scope for the outermost block of the function definition.
     Thus, instead of using @(tsee valid-add-ord) to add the function,
     we use @(tsee valid-add-ord-file-scope).
     But before adding it, we need to look it up,
     and again in the file scope, not the block scope
     (it is in fact legal for a function parameter
     to have the same name as the function:
     its scope is the block, and it hides the function name there);
     so we use @(tsee valid-lookup-ord-file-scope)
     instead of the usual @(tsee valid-lookup-ord).")
   (xdoc::p
    "If the name of the function is not found in the file scope,
     we add it to the file scope, with the appropriate information.
     Note that the definition status is defined,
     since we are validating a function definition.
     If the name is found already, and does not denote a function,
     it is an error;
     it is also an error if the linkages do not match.
     And it is an error if the function is alread defined.
     If all the checks pass, we add the function to the table,
     which overwrites the previous entry,
     but the only information actually overwritten
     is the definition status, from undefined to defined,
     which is appropriate.")
   (xdoc::p
    "The declarations between declarator and body should be present
     if and only if the function declarator has a list of identifiers,
     and there should be exactly one declaration per identifier
     [C17:6.9.1/5] [C17:6.9.1/6].
     For now we do not check those constraints,
     but we validate any declarations
     (ensuring they return no types),
     which will add entries to the block scope in the validation table.")
   (xdoc::p
    "We extend the validation table with the identifier @('__func__')
     [C17:6.4.2.2].
     In our currently approximate type system, this has array type.
     If the GCC flag is enabled (i.e. GCC extensions are allowed),
     we further extend the table with the identifiers @('__FUNCTION__') and
     @('__PRETTY_FUNCTION__') (GCC manual, "
    (xdoc::ahref "https://gcc.gnu.org/onlinedocs/gcc/Function-Names.html"
                 "``Function Names''")
    ").")
   (xdoc::p
    "We ensure that the body is a compound statement,
     and we validate directly the block items;
     this way, we do not push an extra scope,
     because the outer scope must include the parameters.
     In our approximate type system,
     the function type alone does not give us enough information
     to check the types returned by the body
     against the return type of the function,
     to enforce the constraints in [C17:6.8.6.4/1];
     so for now we discard the set of return types
     obtained by validating the body.")
   (xdoc::p
    "Finally we pop the scope of the function body.
     Recall that the function itself stays in the validation table,
     because we have added it to the file scope."))
  (b* (((reterr) (irr-fundef) (irr-valid-table) (irr-uid))
       ((fundef fundef) fundef)
       (table-start table)
       ((erp new-spec type storspecs types table uid)
        (valid-decl-spec-list fundef.spec nil nil nil table uid ienv))
       ((erp new-declor & type ident more-types table uid)
        (valid-declor fundef.declor t type table uid ienv))
       ((unless (and (set::emptyp types)
                     (set::emptyp more-types)))
        (retmsg$ "The declarator of the function definition ~x0 ~
                  contains return statements."
                 (fundef-fix fundef)))
       ((erp typedefp linkage &)
        (valid-stor-spec-list storspecs ident type t table))
       ((when typedefp)
        (retmsg$ "The function definition ~x0 ~
                  declares a 'typedef' name instead of a function."
                 (fundef-fix fundef)))
       ((unless (type-case type :function))
        (retmsg$ "The function definition ~x0 has type ~x1."
                 (fundef-fix fundef) type))
       (info? (valid-lookup-ord-file-scope ident table))
       ((erp table uid)
        (b* (((reterr) (irr-valid-table) (irr-uid))
             ((when (not info?))
              (retok
               (valid-add-ord-file-scope ident
                                         (make-valid-ord-info-objfun
                                          :type (type-function)
                                          :linkage linkage
                                          :defstatus (valid-defstatus-defined)
                                          :uid uid)
                                         table)
               (uid-increment uid)))
             (info info?)
             ((unless (valid-ord-info-case info :objfun))
              (retmsg$ "The name of the function definition ~x0 ~
                        is already in the file scope, ~
                        but is not a function; ~
                        its associated information is ~x1."
                       (fundef-fix fundef) info))
             ((valid-ord-info-objfun info) info)
             ((unless (or (type-case info.type :function)
                          (type-case info.type :unknown)))
              (retmsg$ "The name of the function definition ~x0 ~
                        is already in the file scope, ~
                        but it has type ~x1."
                       (fundef-fix fundef) info.type))
             ((unless (equal linkage info.linkage))
              (retmsg$ "The function definition ~x0 has linkage ~s1, ~
                        which is inconsistent with the linkage ~s2 ~
                        already present in the validation table."
                       (fundef-fix fundef)
                       (if (linkage-case linkage :external)
                           "external"
                         "internal")
                       (if (linkage-case info.linkage :external)
                           "external"
                         "internal")))
             ((when (valid-defstatus-case info.defstatus :defined))
              (retmsg$ "The function definition ~x0 ~
                        is a redefinition of the function."
                       (fundef-fix fundef))))
          (retok
           (valid-add-ord-file-scope ident
                                     (make-valid-ord-info-objfun
                                      :type (type-function)
                                      :linkage linkage
                                      :defstatus (valid-defstatus-defined)
                                      :uid uid)
                                     table)
           (uid-increment uid))))
       ((erp new-decls types table uid)
        (valid-decl-list fundef.decls table uid ienv))
       ((unless (set::emptyp types))
        (retmsg$ "The declarations of the function definition ~x0 ~
                  contain return statements."
                 (fundef-fix fundef)))
       (table (valid-add-ord (ident "__func__")
                             (make-valid-ord-info-objfun
                               :type (type-array)
                               :linkage (linkage-none)
                               :defstatus (valid-defstatus-defined)
                               :uid uid)
                             table))
       (uid (uid-increment uid))
       ((mv table uid)
        (if (ienv->gcc ienv)
            (mv (valid-add-ord (ident "__FUNCTION__")
                               (make-valid-ord-info-objfun
                                 :type (type-array)
                                 :linkage (linkage-none)
                                 :defstatus (valid-defstatus-defined)
                                 :uid uid)
                               table)
                (uid-increment uid))
          (mv table uid)))
       ((mv table uid)
        (if (ienv->gcc ienv)
            (mv (valid-add-ord (ident "__PRETTY_FUNCTION__")
                               (make-valid-ord-info-objfun
                                 :type (type-array)
                                 :linkage (linkage-none)
                                 :defstatus (valid-defstatus-defined)
                                 :uid uid)
                               table)
                (uid-increment uid))
          (mv table uid)))
       (table-body-start table)
       ((erp new-body & & table uid)
        (valid-block-item-list fundef.body table uid ienv))
       (table (valid-pop-scope table))
       (info (make-fundef-info :table-start table-start
                               :table-body-start table-body-start)))
    (retok (make-fundef :extension fundef.extension
                        :spec new-spec
                        :declor new-declor
                        :asm? fundef.asm?
                        :attribs fundef.attribs
                        :decls new-decls
                        :body new-body
                        :info info)
           table
           uid))
  :guard-hints (("Goal" :in-theory (disable (:e tau-system)))) ; for speed
  :hooks (:fix)

  ///

  (defret fundef-unambp-of-valid-fundef
    (implies (not erp)
             (fundef-unambp new-fundef))
    :hyp (fundef-unambp fundef)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-extdecl ((edecl extdeclp)
                       (table valid-tablep)
                       (uid uidp)
                       (ienv ienvp))
  :guard (extdecl-unambp edecl)
  :returns (mv (erp maybe-msgp)
               (new-edecl extdeclp)
               (new-table valid-tablep)
               (new-uid uidp))
  :short "Validate an external declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we do not do anything with assembler statements.
     The empty external declaration is always valid.
     We check that declarations contain no return statements."))
  (b* (((reterr) (irr-extdecl) (irr-valid-table) (irr-uid))
       (uid (uid-fix uid)))
    (extdecl-case
     edecl
     :fundef (b* (((erp new-fundef table uid)
                   (valid-fundef edecl.unwrap table uid ienv)))
               (retok (extdecl-fundef new-fundef) table uid))
     :decl (b* (((erp new-decl types table uid)
                 (valid-decl edecl.unwrap table uid ienv))
                ((unless (set::emptyp types))
                 (retmsg$ "The top-level declaration ~x0 ~
                           contains return statements."
                          edecl.unwrap)))
             (retok (extdecl-decl new-decl) table uid))
     :empty (retok (extdecl-empty) (valid-table-fix table) uid)
     :asm (retok (extdecl-fix edecl) (valid-table-fix table) uid)))
  :hooks (:fix)

  ///

  (defret extdecl-unambp-of-valid-extdecl
    (implies (not erp)
             (extdecl-unambp new-edecl))
    :hyp (extdecl-unambp edecl)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-extdecl-list ((edecls extdecl-listp)
                            (table valid-tablep)
                            (uid uidp)
                            (ienv ienvp))
  :guard (extdecl-list-unambp edecls)
  :returns (mv (erp maybe-msgp)
               (new-edecls extdecl-listp)
               (new-table valid-tablep)
               (new-uid uidp))
  :short "Validate a list of external declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "We validate them in order, threading the validation table through."))
  (b* (((reterr) nil (irr-valid-table) (irr-uid))
       (uid (uid-fix uid))
       ((when (endp edecls))
        (retok nil (valid-table-fix table) uid))
       ((erp new-edecl table uid)
        (valid-extdecl (car edecls) table uid ienv))
       ((erp new-edecls table uid)
        (valid-extdecl-list (cdr edecls) table uid ienv)))
    (retok (cons new-edecl new-edecls) table uid))
  :hooks (:fix)

  ///

  (defret extdecl-list-unambp-of-valid-extdecl-list
    (implies (not erp)
             (extdecl-list-unambp new-edecls))
    :hyp (extdecl-list-unambp edecls)
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-transunit ((tunit transunitp) (uid uidp) (ienv ienvp))
  :guard (transunit-unambp tunit)
  :returns (mv (erp maybe-msgp)
               (new-tunit transunitp)
               (new-uid uidp))
  :short "Validate a translation unit."
  :long
  (xdoc::topstring
   (xdoc::p
    "If GCC extensions are not enabled,
     the initial validation table is the one
     returned by @(tsee valid-init-table).
     If GCC extensions are enabled,
     we add a number of objects and functions
     that we have encountered in practical code;
     we should eventually have a comprehensive list here.")
   (xdoc::p
    "Starting with the validation table as just described,
     we validate all the external declarations in the translation unit.
     Since these are translation units after preprocesing,
     all the referenced names must be declared in the translation unit,
     so it is appropriate to start with the initial validation table.")
   (xdoc::p
    "If validation is successful,
     we add the final validation table to
     the information slot of the translation unit,
     i.e. we annotate the translation unit with its final validation table.")
   (xdoc::p
    "For each GCC function, the associated information consists of
     the function type, external linkage, and defined status.
     The latter two seem reasonable, given that these identifiers
     are visible and have the same meaning in every translation unit,
     and have their own (built-in) definitions.
     For each GCC object, the associated information consists of
     the unknown type, external linkage, and defined status;
     the rationale for the latter two is the same as for functions."))
  (b* (((reterr) (irr-transunit) (irr-uid))
       (gcc (ienv->gcc ienv))
       (table (valid-init-table))
       ((mv table uid)
         (if gcc
             (b* (((mv uid table)
                    (valid-add-ord-objfuns-file-scope *gcc-builtin-functions*
                                                      (type-function)
                                                      (linkage-external)
                                                      (valid-defstatus-defined)
                                                      uid
                                                      table))
                  ((mv uid table)
                    (valid-add-ord-objfuns-file-scope *gcc-builtin-vars*
                                                      (type-unknown)
                                                      (linkage-external)
                                                      (valid-defstatus-defined)
                                                      uid
                                                      table)))
               (mv table uid))
           (mv table uid)))
       ((erp new-edecls table uid)
        (valid-extdecl-list (transunit->decls tunit) table uid ienv))
       (info (make-transunit-info :table-end table)))
    (retok (make-transunit :decls new-edecls :info info) uid))
  :hooks (:fix)

  ///

  (defret transunit-unambp-of-valid-transunit
    (implies (not erp)
             (transunit-unambp new-tunit))
    :hyp (transunit-unambp tunit)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define valid-transunit-ensemble ((tunits transunit-ensemblep) (ienv ienvp))
  :guard (transunit-ensemble-unambp tunits)
  :returns (mv (erp maybe-msgp) (new-tunits transunit-ensemblep))
  :short "Validate a translation unit ensemble."
  :long
  (xdoc::topstring
   (xdoc::p
    "We validate each translation unit.
     As mentioned in @(tsee valid-transunit),
     we annotate the translation unit with the finval validation table.
     For now we do no make any use of the returned table,
     but in the future we should use it to validate
     the externally linked identifiers across
     different translation units of a translation unit ensemble."))
  (b* (((reterr) (irr-transunit-ensemble))
       ((erp new-map -)
        (valid-transunit-ensemble-loop
         (transunit-ensemble->unwrap tunits) (uid 0) ienv)))
    (retok (transunit-ensemble new-map)))

  :prepwork
  ((define valid-transunit-ensemble-loop ((map filepath-transunit-mapp)
                                          (uid uidp)
                                          (ienv ienvp))
     :guard (filepath-transunit-map-unambp map)
     :returns (mv (erp maybe-msgp)
                  (new-map filepath-transunit-mapp
                           :hyp (filepath-transunit-mapp map))
                  (new-uid uidp))
     :parents nil
     (b* (((reterr) nil (irr-uid))
          ((when (omap::emptyp map)) (retok nil (uid-fix uid)))
          (path (omap::head-key map))
          ((erp new-tunit uid)
           (valid-transunit (omap::head-val map) uid ienv))
          ((erp new-map uid)
           (valid-transunit-ensemble-loop (omap::tail map) uid ienv)))
       (retok (omap::update path new-tunit new-map) uid))
     :verify-guards :after-returns

     ///

     (fty::deffixequiv valid-transunit-ensemble-loop
       :args ((ienv ienvp)))

     (defret filepath-transunit-map-unambp-of-valid-transunit-ensemble-loop
       (implies (not erp)
                (filepath-transunit-map-unambp new-map))
       :hyp (and (filepath-transunit-mapp map)
                 (filepath-transunit-map-unambp map))
       :hints (("Goal" :induct t)))))

  :hooks (:fix)

  ///

  (defret transunit-ensemble-unambp-of-valid-transunit-ensemble
    (implies (not erp)
             (transunit-ensemble-unambp new-tunits))
    :hyp (transunit-ensemble-unambp tunits)))
