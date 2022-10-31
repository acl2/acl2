; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "primitives-defresult")

(include-book "../grammar-parser/executable")
(include-book "../notation/syntax-abstraction")

(include-book "kestrel/error-checking/ensure-value-is-constant-name" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-string" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-symbol" :dir :system)
(include-book "kestrel/fty/pos-list" :dir :system)
(include-book "kestrel/std/system/constant-value" :dir :system)
(include-book "kestrel/std/system/known-packages-plus" :dir :system)
(include-book "kestrel/std/util/tuple" :dir :system)
(include-book "kestrel/utilities/integers-from-to" :dir :system)
(include-book "std/strings/case-conversion" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/util/defval" :dir :system)

(local (include-book "kestrel/std/system/partition-rest-and-keyword-args" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel alistp-when-symbol-alistp
  (implies (symbol-alistp x)
           (alistp x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel consp-of-cdr-iff-cdr-when-true-listp
  (implies (true-listp x)
           (iff (consp (cdr x))
                (cdr x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 defdefparse

 :items

 (xdoc::*evmac-topic-implementation-item-state*

  xdoc::*evmac-topic-implementation-item-wrld*

  xdoc::*evmac-topic-implementation-item-ctx*

  (xdoc::evmac-topic-implementation-item-input "name")

  (xdoc::evmac-topic-implementation-item-input "package")

  (xdoc::evmac-topic-implementation-item-input "grammar")

  (xdoc::evmac-topic-implementation-item-input "prefix")

  "@('pkg-wit') is the result of
   @(tsee pkg-witness) applied to @('package')."

  "@('rules') is the list of rules that forms the ABNF grammar,
   i.e. the value of the constant specified by @(':grammar')."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing defdefparse)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *defdefparse-allowed-options*
  :short "Keyword options accepted by @(tsee defdefparse)."
  '(:package
    :grammar
    :prefix)
  ///
  (assert-event (keyword-listp *defdefparse-allowed-options*))
  (assert-event (no-duplicatesp-eq *defdefparse-allowed-options*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defdefparse-process-name (name (ctx ctxp) state)
  :returns (mv erp (name acl2::symbolp) state)
  :short "Process the NAME input."
  :long
  (xdoc::topstring
   (xdoc::p
    "If successful, return the name,
     unchanged but with a stronger type.")
   (xdoc::p
    "For now we just check that this is a symbol.
     In the future we should probably also check that
     it and the @(':package') inputs form a unique pair
     in the calls of @(tsee defdefparse) so far."))
  (b* (((er &) (ensure-value-is-symbol$ name "The first input" t nil)))
    (value name))
  :prepwork ((local (in-theory (enable acl2::ensure-value-is-symbol)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defdefparse-process-package (package (ctx ctxp) state)
  :returns (mv erp (pkg-wit acl2::symbolp) state)
  :short "Process the @(':package') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "If successful, return the witness of the package."))
  (b* (((er &)
        (ensure-value-is-string$ package "The :PACKAGE input" t nil))
       (known-packages (known-packages+ state))
       ((unless (member-equal package known-packages))
        (er-soft+ ctx t nil
                  "The :PACKAGE input ~x0 must be ~
                   among the known packages ~&1."
                  package known-packages))
       ((when (equal package ""))
        (value (raise "Internal error: empty package name."))))
    (value (pkg-witness package)))
  :prepwork ((local (in-theory (enable acl2::ensure-value-is-string)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defdefparse-process-grammar (grammar (ctx ctxp) state)
  :returns (mv erp (grammar acl2::symbolp) state)
  :short "Process the @(':grammar') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "Return the grammar (i.e. the constant name) if successful."))
  (b* (((er &)
        (ensure-value-is-constant-name$ grammar "The :GRAMMAR input" t nil))
       (rules (constant-value grammar (w state)))
       ((unless (and (rulelistp rules)
                     (consp rules)))
        (er-soft+ ctx t nil
                  "The :GRAMMAR input is the name of a constant, ~
                   but its value ~x0 is not a non-empty ABNF grammar."
                  rules)))
    (value grammar))
  :prepwork ((local (in-theory (enable acl2::ensure-value-is-constant-name)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defdefparse-process-prefix (prefix (ctx ctxp) state)
  :returns (mv erp (prefix acl2::symbolp) state)
  :short "Process the @(':prefix') input."
  (b* (((er &) (ensure-value-is-symbol$ prefix "The :PREFIX input" t nil)))
    (value prefix))
  :prepwork ((local (in-theory (enable acl2::ensure-value-is-symbol)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defdefparse-process-inputs ((args true-listp) (ctx ctxp) state)
  :returns (mv erp
               (val (std::tuple (name acl2::symbolp)
                                (pkg-wit acl2::symbolp)
                                (grammar acl2::symbolp)
                                (prefix acl2::symbolp)
                                val))
               state)
  :short "Process all the inputs."
  :long
  (xdoc::topstring
   (xdoc::p
    "If successful, we return the inputs,
     except that we return the package witnesss
     instead of the package input."))
  (b* (((fun (irr)) (list nil nil nil nil))
       ((mv erp name options)
        (partition-rest-and-keyword-args args *defdefparse-allowed-options*))
       ((when (or erp
                  (not (consp name))
                  (not (endp (cdr name)))))
        (er-soft+ ctx t (irr)
                  "The inputs must be the name (a symbol) ~
                   followed by the options ~&0."
                  *defdefparse-allowed-options*))
       (name (car name))
       ((er name :iferr (irr))
        (defdefparse-process-name name ctx state))
       (package-option (assoc-eq :package options))
       ((unless (consp package-option))
        (er-soft+ ctx t (irr) "The :PACKAGE input is missing."))
       (package (cdr package-option))
       ((er pkg-wit :iferr (irr))
        (defdefparse-process-package package ctx state))
       (grammar-option (assoc-eq :grammar options))
       ((unless (consp grammar-option))
        (er-soft+ ctx t (irr) "The :GRAMMAR input is missing."))
       (grammar (cdr grammar-option))
       ((er grammar :iferr (irr))
        (defdefparse-process-grammar grammar ctx state))
       (prefix-option (assoc-eq :prefix options))
       ((unless (consp prefix-option))
        (er-soft+ ctx t (irr) "The :PREFIX input is missing."))
       (prefix (cdr prefix-option))
       ((er prefix :iferr (irr))
        (defdefparse-process-prefix prefix ctx state)))
    (value (list name pkg-wit grammar prefix)))
  ///
  (more-returns
   (val true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation defdefparse)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines defdefparse-printing
  :short "Pretty-print ABNF
          elements, alternations, concatenations, and repetitions
          to ACL2 strings."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to generate portions of documentation strings
     in the generated parsing functions.")
   (xdoc::p
    "We print numeric notations in decimal base;
     the abstract syntax has no information about the base.
     We are considering extending our ABNF abstract syntax
     to maintain more information from the concrete syntax,
     including the numeric bases (decimal, hexadecimal, binary),
     also to make this printing more faithful.")
   (xdoc::p
    "We print case-insensitive strings without the @('%i') prefix.
     See previous paragraph about our consideration to
     extend the abstract syntax to preserve more concrete syntax information:
     this could also apply to whether case-insensitive strings
     have the prefix or not.")
   (xdoc::p
    "For the repetition prefix of a repetition,
     we print nothing for it if it is just one.
     If minimum and maximum are the same,
     we just print that.
     If the minimum is 0 and the maximum infinity,
     we just print @('*') (not the equivalent @('0*')).
     In all other cases, we print both minimum and maximum separated by @('*'),
     except that we omit the maximum if it is infinity.
     This is a minimal printing strategy,
     in the sense that it prints the prefix in the shortest possible way;
     noenetheless, if we extend the abstract syntax (as mentioned above)
     to preserve more information from the concrete syntax,
     we might support different printed forms.")
   (xdoc::p
    "Prose elements are not supported,
     because currently we do not generate any paring functions for them.
     (To do that, we would need some external information.)"))

  (define defdefparse-print-element ((elem elementp))
    :returns (string acl2::stringp)
    (element-case
     elem
     :rulename (rulename->get elem.get)
     :group (str::cat "( " (defdefparse-print-alternation elem.get) " )")
     :option (str::cat "[ " (defdefparse-print-alternation elem.get) " ]")
     :char-val (char-val-case
                elem.get
                :insensitive (str::cat
                              "\""
                              (char-val-insensitive->get elem.get)
                              "\"")
                :sensitive (str::cat
                            "%s\""
                            (char-val-sensitive->get elem.get)
                            "\""))
     :num-val (num-val-case
               elem.get
               :direct (str::cat
                        "%d"
                        (defdefparse-print-num-val-direct-numbers
                          (num-val-direct->get elem.get)))
               :range (str::cat
                       "%d"
                       (str::nat-to-dec-string (num-val-range->min elem.get))
                       "-"
                       (str::nat-to-dec-string (num-val-range->max elem.get))))
     :prose-val (prog2$ (raise "Printing of ~x0 not supported." elem.get) ""))
    :measure (element-count elem))

  (define defdefparse-print-alternation ((alt alternationp))
    :returns (string acl2::stringp)
    (cond ((endp alt) "")
          ((endp (cdr alt)) (defdefparse-print-concatenation (car alt)))
          (t (str::cat (defdefparse-print-concatenation (car alt))
                       " / "
                       (defdefparse-print-alternation (cdr alt)))))
    :measure (alternation-count alt))

  (define defdefparse-print-concatenation ((conc concatenationp))
    :returns (string acl2::stringp)
    (cond ((endp conc) "")
          ((endp (cdr conc)) (defdefparse-print-repetition (car conc)))
          (t (str::cat (defdefparse-print-repetition (car conc))
                       " "
                       (defdefparse-print-concatenation (cdr conc)))))
    :measure (concatenation-count conc))

  (define defdefparse-print-repetition ((rep repetitionp))
    :returns (string acl2::stringp)
    (b* (((repetition rep) rep)
         ((repeat-range range) rep.range)
         ((when (and (equal range.min 1)
                     (equal range.max (nati-finite 1))))
          (defdefparse-print-element rep.element))
         ((when (equal range.max
                       (nati-finite range.min)))
          (str::cat (str::nat-to-dec-string range.min)
                    (defdefparse-print-element rep.element))))
      (str::cat (if (equal range.min 0)
                    ""
                  (str::nat-to-dec-string range.min))
                "*"
                (if (nati-case range.max :infinity)
                    ""
                  (str::nat-to-dec-string (nati-finite->get range.max)))
                (defdefparse-print-element rep.element)))
    :measure (repetition-count rep))

  :prepwork
  ((define defdefparse-print-num-val-direct-numbers ((nats nat-listp))
     :returns (string acl2::stringp)
     (cond ((endp nats) "")
           ((endp (cdr nats)) (str::nat-to-dec-string (car nats)))
           (t (str::cat
               (str::nat-to-dec-string (car nats))
               "."
               (defdefparse-print-num-val-direct-numbers (cdr nats))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist defdefparse-alt-symbol-alist
  :short "Fixtype of alists from ABNF alternations to ACL2 symbols."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the alists that specify
     the names of the functions to parse groups and options.
     Both groups and options are defined by alternations."))
  :key-type alternation
  :val-type acl2::symbol
  :true-listp t
  :pred defdefparse-alt-symbol-alistp
  ///

  (defruled symbolp-of-cdr-of-assoc-equal-when-defdefparse-alt-symbol-alistp
    (implies (defdefparse-alt-symbol-alistp alist)
             (acl2::symbolp (cdr (assoc-equal key alist))))))

;;;;;;;;;;;;;;;;;;;;

(fty::defalist defdefparse-rep-symbol-alist
  :short "Fixtype of alists from ABNF repetitions to ACL2 symbols."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the type of the alists that specify
     the names of the functions to parse repetitions."))
  :key-type repetition
  :val-type acl2::symbol
  :true-listp t
  :pred defdefparse-rep-symbol-alistp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-group-alist ((args true-listp)
                                     (prefix acl2::symbolp))
  :returns (alist defdefparse-alt-symbol-alistp)
  :short "Generate an alist from alternations to symbols,
          used for the table of group parsing functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by the @('defparse-name-group-table') macros
     generated by @(tsee defdefparse).")
   (xdoc::p
    "The @('args') parameter of this ACL2 function consists of
     the arguments of the @('defparse-name-group-table'),
     which must be an even number of alternating strings and symbols.
     Each adjacent string-symbol pair specifies an entry in the alist.")
   (xdoc::p
    "The string of the entry must be parsable as an ABNF group,
     from which we extract the alternation (in ABNF abstract syntax).
     The symbol of the entry is used to form a function name,
     together with the prefix given as input to @(tsee defdefparse)."))
  (b* (((when (endp args)) nil)
       ((cons group args) args)
       ((when (endp args))
        (raise "Found an odd number of arguments."))
       ((cons sym args) args)
       ((unless (acl2::stringp group))
        (raise "The ~x0 argument must be a string." group))
       ((mv err tree rest) (parse-group (string=>nats group)))
       ((when err)
        (raise "Cannot parse group ~s0: ~@1." group err))
       ((unless (unsigned-byte-listp 8 rest))
        (raise "Internal error: ~
                rest ~x0 not all consisting of unsigned 8-bit bytes."
               rest))
       ((when (consp rest))
        (raise "Extra parsing ~s0 in group ~s1."
               (nats=>string rest) group))
       (alt (abstract-group/option tree))
       ((unless (acl2::symbolp sym))
        (raise "The ~x0 argument must be a symbol." sym))
       (fn (packn-pos (list prefix '- sym) prefix))
       (alist (defdefparse-gen-group-alist args prefix))
       ((when (member-equal alt (strip-cars alist)))
        (raise "Duplicate group ~s0." group))
       ((when (member-eq fn (strip-cdrs alist)))
        (raise "Duplicate function ~x0." fn)))
    (acons alt fn alist))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-option-alist ((args true-listp)
                                      (prefix acl2::symbolp))
  :returns (alist defdefparse-alt-symbol-alistp)
  :short "Generate an alist from alternations to symbols,
          used for the table of option parsing functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by the @('defparse-name-option-table') macros
     generated by @(tsee defdefparse).")
   (xdoc::p
    "The @('args') parameter of this ACL2 function consists of
     the arguments of the @('defparse-name-option-table'),
     which must be an even number of alternating strings and symbols.
     Each adjacent string-symbol pair specifies an entry in the alist.")
   (xdoc::p
    "The string of the entry must be parsable as an ABNF option,
     from which we extract the alternation (in ABNF abstract syntax).
     The symbol of the entry is used to form a function name,
     together with the prefix given as input to @(tsee defdefparse)."))
  (b* (((when (endp args)) nil)
       ((cons option args) args)
       ((when (endp args))
        (raise "Found an odd number of arguments."))
       ((cons sym args) args)
       ((unless (acl2::stringp option))
        (raise "The ~x0 argument must be a string." option))
       ((mv err tree rest) (parse-option (string=>nats option)))
       ((when err)
        (raise "Cannot parse option ~s0: ~@1." option err))
       ((unless (unsigned-byte-listp 8 rest))
        (raise "Internal error: ~
                rest ~x0 not all consisting of unsigned 8-bit bytes."
               rest))
       ((when (consp rest))
        (raise "Extra parsing ~s0 in option ~s1."
               (nats=>string rest) option))
       (alt (abstract-group/option tree))
       ((unless (acl2::symbolp sym))
        (raise "The ~x0 argument must be a symbol." sym))
       (fn (packn-pos (list prefix '- sym) prefix))
       (alist (defdefparse-gen-option-alist args prefix))
       ((when (member-equal alt (strip-cars alist)))
        (raise "Duplicate option ~s0." option))
       ((when (member-eq fn (strip-cdrs alist)))
        (raise "Duplicate function ~x0." fn)))
    (acons alt fn alist))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-repetition-alist ((args true-listp)
                                          (prefix acl2::symbolp))
  :returns (alist defdefparse-rep-symbol-alistp)
  :short "Generate an alist from alternations to symbols,
          used for the table of repetition parsing functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by the @('defparse-name-repetition-table') macros
     generated by @(tsee defdefparse).")
   (xdoc::p
    "The @('args') parameter of this ACL2 function consists of
     the arguments of the @('defparse-name-repetition-table'),
     which must be an even number of alternating strings and symbols.
     Each adjacent string-symbol pair specifies an entry in the alist.")
   (xdoc::p
    "The string of the entry must be parsable as an ABNF repetition,
     from which we obtain the repetition (in ABNF abstract syntax).
     The symbol of the entry is used to form a function name,
     together with the prefix given as input to @(tsee defdefparse)."))
  (b* (((when (endp args)) nil)
       ((cons repetition args) args)
       ((when (endp args))
        (raise "Found an odd number of arguments."))
       ((cons sym args) args)
       ((unless (acl2::stringp repetition))
        (raise "The ~x0 argument must be a string." repetition))
       ((mv err tree rest) (parse-repetition (string=>nats repetition)))
       ((when err)
        (raise "Cannot parse repetition ~s0: ~@1." repetition err))
       ((unless (unsigned-byte-listp 8 rest))
        (raise "Internal error: ~
                rest ~x0 not all consisting of unsigned 8-bit bytes."
               rest))
       ((when (consp rest))
        (raise "Extra parsing ~s0 in repetition ~s1."
               (nats=>string rest) repetition))
       (rep (abstract-repetition tree))
       ((unless (acl2::symbolp sym))
        (raise "The ~x0 argument must be a symbol." sym))
       (fn (packn-pos (list prefix '- sym) prefix))
       (alist (defdefparse-gen-repetition-alist args prefix))
       ((when (member-equal rep (strip-cars alist)))
        (raise "Duplicate repetition ~s0." repetition))
       ((when (member-eq fn (strip-cdrs alist)))
        (raise "Duplicate function ~x0." fn)))
    (acons rep fn alist))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-group-table-name ((name acl2::symbolp)
                                          (pkg-wit acl2::symbolp))
  :returns (name acl2::symbolp)
  :short "Generate the name of the constant whose value is
          the table of group parsing functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The constant name is in the same package as the generated macros,
     and includes the name passed to @(tsee defdefparse)."))
  (packn-pos (list '*defparse- name '-group-table*) pkg-wit))

;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-option-table-name ((name acl2::symbolp)
                                           (pkg-wit acl2::symbolp))
  :returns (name acl2::symbolp)
  :short "Generate the name of the constant whose value is
          the table of option parsing functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The constant name is in the same package as the generated macros,
     and includes the name passed to @(tsee defdefparse)."))
  (packn-pos (list '*defparse- name '-option-table*) pkg-wit))

;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-repetition-table-name ((name acl2::symbolp)
                                               (pkg-wit acl2::symbolp))
  :returns (name acl2::symbolp)
  :short "Generate the name of the constant whose value is
          the table of repetition parsing functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The constant name is in the same package as the generated macros,
     and includes the name passed to @(tsee defdefparse)."))
  (packn-pos (list '*defparse- name '-repetition-table*) pkg-wit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-group-table ((args true-listp)
                                     (prefix acl2::symbolp)
                                     (table-name acl2::symbolp))
  :returns (event pseudo-event-formp)
  :short "Generate the table of group parsing functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate a named constant defined with the alist
     produced by @(tsee defdefparse-gen-group-alist)."))
  (b* ((alist (defdefparse-gen-group-alist args prefix)))
    `(defval ,table-name
       :short "Table of group parsing functions."
       ',alist
       ///
       (assert-event (defdefparse-alt-symbol-alistp ,table-name))
       (assert-event (no-duplicatesp-equal (strip-cars ,table-name)))
       (assert-event (no-duplicatesp-eq (strip-cdrs ,table-name))))))

;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-option-table ((args true-listp)
                                      (prefix acl2::symbolp)
                                      (table-name acl2::symbolp))
  :returns (event pseudo-event-formp)
  :short "Generate the table of option parsing functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate a named constant defined with the alist
     produced by @(tsee defdefparse-gen-option-alist)."))
  (b* ((alist (defdefparse-gen-option-alist args prefix)))
    `(defval ,table-name
       :short "Table of option parsing functions."
       ',alist
       ///
       (assert-event (defdefparse-alt-symbol-alistp ,table-name))
       (assert-event (no-duplicatesp-equal (strip-cars ,table-name)))
       (assert-event (no-duplicatesp-eq (strip-cdrs ,table-name))))))

;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-repetition-table ((args true-listp)
                                          (prefix acl2::symbolp)
                                          (table-name acl2::symbolp))
  :returns (event pseudo-event-formp)
  :short "Generate the table of repetition parsing functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate a named constant defined with the alist
     produced by @(tsee defdefparse-gen-repetition-alist)."))
  (b* ((alist (defdefparse-gen-repetition-alist args prefix)))
    `(defval ,table-name
       :short "Table of repetition parsing functions."
       ',alist
       ///
       (assert-event (defdefparse-rep-symbol-alistp ,table-name))
       (assert-event (no-duplicatesp-equal (strip-cars ,table-name)))
       (assert-event (no-duplicatesp-eq (strip-cdrs ,table-name))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-group-table-macro ((name acl2::symbolp)
                                           (pkg-wit acl2::symbolp)
                                           (table-name acl2::symbolp)
                                           (prefix acl2::symbolp))
  :returns (event pseudo-event-formp)
  :short "Generate the @('defparse-name-group-table')
          described in the @(tsee defdefparse) user documentation."
  (b* ((macro-name
        (packn-pos (list 'defparse- name '-group-table) pkg-wit)))
    `(defmacro ,macro-name (&rest args)
       `(make-event
         (defdefparse-gen-group-table ',args ',',prefix ',',table-name)))))

;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-option-table-macro ((name acl2::symbolp)
                                            (pkg-wit acl2::symbolp)
                                            (table-name acl2::symbolp)
                                            (prefix acl2::symbolp))
  :returns (event pseudo-event-formp)
  :short "Generate the @('defparse-name-option-table')
          described in the @(tsee defdefparse) user documentation."
  (b* ((macro-name
        (packn-pos (list 'defparse- name '-option-table) pkg-wit)))
    `(defmacro ,macro-name (&rest args)
       `(make-event
         (defdefparse-gen-option-table ',args ',',prefix ',',table-name)))))

;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-repetition-table-macro ((name acl2::symbolp)
                                                (pkg-wit acl2::symbolp)
                                                (table-name acl2::symbolp)
                                                (prefix acl2::symbolp))
  :returns (event pseudo-event-formp)
  :short "Generate the @('defparse-name-repetition-table')
          described in the @(tsee defdefparse) user documentation."
  (b* ((macro-name
        (packn-pos (list 'defparse- name '-repetition-table) pkg-wit)))
    `(defmacro ,macro-name (&rest args)
       `(make-event
         (defdefparse-gen-repetition-table ',args ',',prefix ',',table-name)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-code-for-element
  ((elem elementp)
   (check-error-p booleanp)
   (prefix acl2::symbolp)
   (group-table defdefparse-alt-symbol-alistp)
   (option-table defdefparse-alt-symbol-alistp))
  :returns (code true-listp)
  :short "Generate code to parse an instance of an ABNF element."
  :long
  (xdoc::topstring
   (xdoc::p
    "Numeric and character value notations are parsed directly.
     Rule names are parsed by calling the corresponding functions,
     whose names is derived from the rule names.
     Groups and options are parsed by calling the corresponding functions,
     whose names are looked up in the alists.")
   (xdoc::p
    "We generate a @(tsee b*) binder that binds the parsing results
     to variables @('tree') (for a tree or error)
     and @('input') (for the remaining input).
     If the @('check-error-p') flag is set,
     we also generate a @(tsee b*) to propagate the error,
     if @('tree') is an error."))
  (element-case
   elem
   :num-val
   (num-val-case
    elem.get
    :direct `(((mv tree input)
               (parse-direct (list ,@(num-val-direct->get elem.get))
                             input))
              ,@(and check-error-p
                     '(((when (reserrp tree)) (mv (reserrf-push tree) input)))))
    :range `(((mv tree input)
              (parse-range ,(num-val-range->min elem.get)
                           ,(num-val-range->max elem.get)
                           input))
             ,@(and check-error-p
                    '(((when (reserrp tree)) (mv (reserrf-push tree) input))))))
   :char-val
   (char-val-case
    elem.get
    :insensitive `(((mv tree input)
                    (parse-ichars ,(char-val-insensitive->get elem.get)
                                  input))
                   ,@(and
                      check-error-p
                      '(((when (reserrp tree)) (mv (reserrf-push tree) input)))))
    :sensitive `(((mv tree input)
                  (parse-schars ,(char-val-sensitive->get elem.get)
                                input))
                 ,@(and
                    check-error-p
                    '(((when (reserrp tree)) (mv (reserrf-push tree) input))))))
   :rulename (b* ((parse-rulename-fn
                   (acl2::packn-pos (list prefix
                                          '-
                                          (str::upcase-string
                                           (rulename->get elem.get)))
                                    prefix)))
               `(((mv tree input) (,parse-rulename-fn input))
                 ,@(and
                    check-error-p
                    '(((when (reserrp tree)) (mv (reserrf-push tree) input))))))
   :group (b* ((parse-group-fn (cdr (assoc-equal elem.get group-table))))
            `(((mv tree input) (,parse-group-fn input))
              ,@(and
                 check-error-p
                 '(((when (reserrp tree)) (mv (reserrf-push tree) input))))))
   :option (b* ((parse-option-fn (cdr (assoc-equal elem.get option-table))))
             `(((mv tree input) (,parse-option-fn input))
               ,@(and
                  check-error-p
                  '(((when (reserrp tree)) (mv (reserrf-push tree) input))))))
   :prose-val (raise "Prose value ~x0 not supported." elem.get)))

;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-code-for-repetition
  ((rep repetitionp)
   (index natp)
   (prefix acl2::symbolp)
   (group-table defdefparse-alt-symbol-alistp)
   (option-table defdefparse-alt-symbol-alistp)
   (repetition-table defdefparse-rep-symbol-alistp))
  :returns (mv (code true-listp)
               (var acl2::symbolp))
  :short "Generate code to parse an instance of an ABNF repetition."
  :long
  (xdoc::topstring
   (xdoc::p
    "A repetition is part of a concatenation,
     and a concatenation (see @(tsee defdefparse-gen-code-for-concatenation))
     is parsed by parsing each of its repetitions;
     the results of parsing the repetitions must be put together
     to yield the result of parsing the concatenation.
     The result of parsing each repetition is bound to a different variable,
     called @('trees<index>') where @('<index>') is a numeric index
     that starts with 1 and is incremented as we go through the concatenation.
     The index is passed to this code generation function,
     which generates @(tsee b*) binders and also returns the variable name.")
   (xdoc::p
    "If the repetition is in the alist,
     its parsing function is retrieved from there
     and we generate code to bind its result to @('trees<index>').
     We also propagate any error.")
   (xdoc::p
    "If the repetition is not in the alist,
     it must be a singleton repetition (this is what we support for now),
     in which case we generate code to parse the element,
     and we put the resulting tree into a singleton list if successful.
     Note that we propagate the error when parsing the element,
     i.e. we pass @('t') as the @('check-error-p') flag."))
  (b* ((trees-index (add-suffix 'trees (str::nat-to-dec-string index)))
       (parse-repetition-fn? (cdr (assoc-equal rep repetition-table)))
       ((when parse-repetition-fn?)
        (mv `(((mv ,trees-index input) (,parse-repetition-fn? input))
              ((when (reserrp ,trees-index))
               (mv (reserrf-push ,trees-index) input)))
            trees-index))
       ((repetition rep) rep)
       ((when (equal rep.range
                     (make-repeat-range :min 1
                                        :max (nati-finite 1))))
        (mv `(,@(defdefparse-gen-code-for-element
                  rep.element t prefix group-table option-table)
              (,trees-index (list tree)))
            trees-index)))
    (prog2$ (raise "Repetition ~x0 not supported yet." rep)
            (mv nil nil))))

;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-code-for-concatenation
  ((conc concatenationp)
   (prefix acl2::symbolp)
   (group-table defdefparse-alt-symbol-alistp)
   (option-table defdefparse-alt-symbol-alistp)
   (repetition-table defdefparse-rep-symbol-alistp))
  :returns (code true-listp)
  :short "Generate code to parse an instance of an ABNF concatenation."
  :long
  (xdoc::topstring
   (xdoc::p
    "A concatenation is parsed by parsing each repetition in order.
     We also generate a final @(tsee b*) binder that
     puts all the lists of trees from the repetiitons
     into a list of lists of trees for the concatenation."))
  (b* (((when (endp conc)) (raise "Empty concatenation."))
       ((mv code vars)
        (defdefparse-gen-code-for-concatenation-aux
          conc 1 prefix group-table option-table repetition-table)))
    `(,@code
      (treess (list ,@vars))))
  :prepwork
  ((define defdefparse-gen-code-for-concatenation-aux
     ((conc concatenationp)
      (index natp)
      (prefix acl2::symbolp)
      (group-table defdefparse-alt-symbol-alistp)
      (option-table defdefparse-alt-symbol-alistp)
      (repetition-table defdefparse-rep-symbol-alistp))
     :returns (mv (code true-listp)
                  (vars acl2::symbol-listp))
     :parents nil
     (b* (((when (endp conc)) (mv nil nil))
          ((mv code1 var) (defdefparse-gen-code-for-repetition
                            (car conc)
                            index
                            prefix
                            group-table
                            option-table
                            repetition-table))
          ((mv code2 vars) (defdefparse-gen-code-for-concatenation-aux
                             (cdr conc)
                             (1+ index)
                             prefix
                             group-table
                             option-table
                             repetition-table)))
       (mv (append code1 code2) (cons var vars))))))

;;;;;;;;;;;;;;;;;;;;

(define defdefparse-reorder-alternation ((alt alternationp)
                                         (order pos-listp))
  :returns (new-alt alternationp)
  :short "Reorder the alternatives of an alternation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('order') list must be  a permutation of the list @('(1 ... n)'),
     where @('n') is the number of alternatives in @('alt').
     We return the alternative, permuted according to the list.")
   (xdoc::p
    "This serves to try an alternative before another one,
     in order to satisfy extra-grammatical requirements."))
  (b* (((when (endp order)) nil)
       (index (1- (car order)))
       ((unless (< index (len alt)))
        (raise "Bad position ~x0 in ~x1." (car order) alt)))
    (cons (concatenation-fix (nth index alt))
          (defdefparse-reorder-alternation alt (cdr order)))))

;;;;;;;;;;;;;;;;;;;;

(define defdefparse-order-permutationp ((order pos-listp))
  :returns (yes/no booleanp)
  :short "Check if an @('order') parameter is a valid permutation."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check if a list of length @('n') is a permutation of @('(1 ... n)')."))
  (defdefparse-order-permutationp-aux order (integers-from-to 1 (len order)))
  :guard-hints (("Goal" :in-theory (enable integers-from-to)))
  :prepwork
  ((define defdefparse-order-permutationp-aux ((a pos-listp) (b pos-listp))
     :returns (yes/no booleanp)
     :parents nil
     (cond ((endp a) (endp b))
           (t (and (member (car a) b)
                   (defdefparse-order-permutationp-aux
                     (cdr a)
                     (remove1 (car a) b))))))))

;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-code-for-alternation
  ((alt alternationp)
   (order pos-listp)
   (prefix acl2::symbolp)
   (group-table defdefparse-alt-symbol-alistp)
   (option-table defdefparse-alt-symbol-alistp)
   (repetition-table defdefparse-rep-symbol-alistp))
  :returns (code true-listp)
  :short "Generate code to parse an instance of an ABNF alternation."
  :long
  (xdoc::topstring
   (xdoc::p
    "After possibly reordering the alternatives,
     we generate code that tries every alternative.
     We use variables @('treess<index>') to store
     either the resulting list of lists of trees or an error.
     For each alternative, we generate code for the concatenation
     and bind the result to @('treess<index>'),
     returning as soon as we get a non-error.
     If all the alternatives give an error,
     we return an error that includes all the errors for the alternatives:
     this is the reason for using and incremnting indices,
     i.e. so that we can combine them in case of error,
     not because we want to combine them in case of success.")
   (xdoc::p
    "Note that for each attempt to parse an alternative
     we bind the variable @('input1') to the remaining input,
     not the variable @('input').
     This is because we need to backtrack in case of failure,
     discarding @('input1') and going back to the previous input."))
  (b* (((when (endp alt)) (raise "Empty alternation."))
       ((unless (and (= (len order) (len alt))
                     (defdefparse-order-permutationp order)))
        (raise "Bad permutation ~x0." order))
       (alt (defdefparse-reorder-alternation alt order))
       ((mv code vars)
        (defdefparse-gen-code-for-alternation-aux
          alt 1 prefix group-table option-table repetition-table)))
    `(b* (,@code)
       (mv (reserrf (list :found (list ,@vars) :required ',alt)) input)))
  :prepwork
  ((define defdefparse-gen-code-for-alternation-aux
     ((alt alternationp)
      (index natp)
      (prefix acl2::symbolp)
      (group-table defdefparse-alt-symbol-alistp)
      (option-table defdefparse-alt-symbol-alistp)
      (repetition-table defdefparse-rep-symbol-alistp))
     :returns (mv (code true-listp)
                  (vars acl2::symbol-listp))
     :parents nil
     (b* (((when (endp alt)) (mv nil nil))
          (treess-index (add-suffix 'treess (str::nat-to-dec-string index)))
          (code `(((mv ,treess-index input1)
                   (b* (,@(defdefparse-gen-code-for-concatenation
                            (car alt)
                            prefix group-table option-table repetition-table))
                     (mv treess input)))
                  ((when (not (reserrp ,treess-index)))
                   (mv ,treess-index input1))))
          ((mv more-code vars)
           (defdefparse-gen-code-for-alternation-aux
             (cdr alt) (1+ index)
             prefix group-table option-table repetition-table)))
       (mv (append code more-code) (cons treess-index vars))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum defdefparse-function-spec
  :short "Fixtype of specifications of parsing functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "A value of this type descriptively specifies a parsing function:")
   (xdoc::ul
    (xdoc::li
     "A parsing function for a rule name,
      with a possible reordering of the alternatives
      (or just the list @('(1 2 3 ...)') if there is no reordering.")
    (xdoc::li
     "A parsing function for a group,
      with a possible reordering of the alternatives
      (or just the list @('(1 2 3 ...)') if there is no reordering.")
    (xdoc::li
     "A parsing function for an option,
      with a possible reordering of the alternatives
      (or just the list @('(1 2 3 ...)') if there is no reordering.")
    (xdoc::li
     "A parsing function for a repetition.")))
  (:rulename ((get acl2::stringp)
              (order pos-list)))
  (:group ((get alternation)
           (order pos-list)))
  (:option ((get alternation)
            (order pos-list)))
  (:repetition ((get repetition))))

;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-function-for-rulename
  ((rulename acl2::stringp)
   (order pos-listp)
   (rules rulelistp)
   (prefix acl2::symbolp)
   (group-table defdefparse-alt-symbol-alistp)
   (option-table defdefparse-alt-symbol-alistp)
   (repetition-table defdefparse-rep-symbol-alistp))
  :returns (event pseudo-event-formp)
  :short "Generate a parsing function for a rule name."
  :long
  (xdoc::topstring
   (xdoc::p
    "The name is @('<prefix>-<R>'), if @('<R>') is the rule name.
     We look up the alternation that defines the rule name in the grammar,
     and we generate code to parse that,
     propagating errors,
     and returning a tree for the rule name in case of success.")
   (xdoc::p
    "We also generate linear rules about the remaining input.
     These are needed to prove the termination of recursive functions
     that call this function.")
   (xdoc::p
    "If every concatenation in the alternation that defines the rule name
     is nullable (i.e. can expand to the empty string of natural numbers),
     then the strict inequality linear rule should not be generated;
     otherwise, it should be generated.
     For now we do a very simple and partial test for nullability,
     namely whether the alternation consists of a single concatenation
     of a single repetition with `*`:
     clearly, this is nullable.
     We will extend this eventually;
     the ABNF library should eventually contain operations
     to determine whether grammar rules are nullable,
     using the well-known algorithms found in the literature."))
  (b* ((parse-rulename (acl2::packn-pos (list prefix
                                              '-
                                              (str::upcase-string rulename))
                                        prefix))
       (alt (lookup-rulename (rulename rulename) rules))
       (order (or order (integers-from-to 1 (len alt))))
       (nullablep (and (consp alt)
                       (not (consp (cdr alt)))
                       (b* ((conc (car alt)))
                         (and (consp conc)
                              (not (consp (cdr conc)))
                              (b* ((rep (car conc)))
                                (equal (repetition->range rep)
                                       (make-repeat-range
                                        :min 0
                                        :max (nati-infinity)))))))))
    `(define ,parse-rulename ((input nat-listp))
       :returns (mv (tree tree-resultp)
                    (rest-input nat-listp))
       :short ,(str::cat "Parse a @('" rulename "').")
       (b* (((mv treess input)
             ,(defdefparse-gen-code-for-alternation
                alt order prefix group-table option-table repetition-table))
            ((when (reserrp treess))
             (mv (reserrf-push treess) (nat-list-fix input))))
         (mv (make-tree-nonleaf :rulename? (rulename ,rulename)
                                :branches treess)
             input))
       :hooks (:fix)
       ///
       (defret ,(acl2::packn-pos (list 'len-of- parse-rulename '-<=)
                                 parse-rulename)
         (<= (len rest-input)
             (len input))
         :rule-classes :linear)
       ,@(and
          (not nullablep)
          `((defret ,(acl2::packn-pos (list 'len-of- parse-rulename '-<)
                                      parse-rulename)
              (implies (not (reserrp tree))
                       (< (len rest-input)
                          (len input)))
              :rule-classes :linear))))))

;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-function-for-group
  ((alt alternationp)
   (order pos-listp)
   (prefix acl2::symbolp)
   (group-table defdefparse-alt-symbol-alistp)
   (option-table defdefparse-alt-symbol-alistp)
   (repetition-table defdefparse-rep-symbol-alistp))
  :returns (event pseudo-event-formp)
  :short "Generate a parsing function for an ABNF group."
  :long
  (xdoc::topstring
   (xdoc::p
    "The name is retrieved from the alist for group parsing functions.
     We generate code to attempt to parse the alternation of the group,
     propagating errors,
     and returning a tree without rule name in case of success.")
   (xdoc::p
    "We also generate linear rules about the remaining input.
     These are needed to prove the termination of recursive functions
     that call this function.")
   (xdoc::p
    "If the alternation is nullable,
     we should not generate the strict inequality linear rule:
     see discussion in @(tsee defdefparse-gen-function-for-rulename).
     However, for now we do not support that here,
     i.e. we implicitly assume that the alternation is not nullable."))
  (b* ((parse-group (cdr (assoc-equal alt group-table)))
       (order (or order (integers-from-to 1 (len alt)))))
    `(define ,parse-group ((input nat-listp))
       :returns (mv (tree tree-resultp)
                    (rest-input nat-listp))
       :short ,(str::cat "Parse a @('"
                         (defdefparse-print-element (element-group alt))
                         "').")
       (b* (((mv treess input)
             ,(defdefparse-gen-code-for-alternation
                alt order prefix group-table option-table repetition-table))
            ((when (reserrp treess))
             (mv (reserrf-push treess) (nat-list-fix input))))
         (mv (make-tree-nonleaf :rulename? nil
                                :branches treess)
             input))
       :hooks (:fix)
       ///
       (defret ,(acl2::packn-pos (list 'len-of- parse-group '-<=)
                                 parse-group)
         (<= (len rest-input)
             (len input))
         :rule-classes :linear)
       (defret ,(acl2::packn-pos (list 'len-of- parse-group '-<)
                                 parse-group)
         (implies (not (reserrp tree))
                  (< (len rest-input)
                     (len input)))
         :rule-classes :linear)))
  :guard-hints
  (("Goal"
    :in-theory
    (enable
     symbolp-of-cdr-of-assoc-equal-when-defdefparse-alt-symbol-alistp))))

;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-function-for-option
  ((alt alternationp)
   (order pos-listp)
   (prefix acl2::symbolp)
   (group-table defdefparse-alt-symbol-alistp)
   (option-table defdefparse-alt-symbol-alistp)
   (repetition-table defdefparse-rep-symbol-alistp))
  :returns (event pseudo-event-formp)
  :short "Generate a parsing function for an ABNF option."
  :long
  (xdoc::topstring
   (xdoc::p
    "The name is retrieved from the alist for option parsing functions.
     We generate code to attempt to parse the alternation of the option,
     and returning a tree without rule name in case of success.
     If parsing the alternative fails,
     we succeed and return a tree without branches.")
   (xdoc::p
    "We also generate a linear rule about the remaining input.
     This is needed to prove the termination of recursive functions
     that call this function.")
   (xdoc::p
    "Since an option is always nullable,
     we do not generate the string inequality linear rule:
     see discussion in @(tsee defdefparse-gen-function-for-rulename)."))
  (b* ((parse-option (cdr (assoc-equal alt option-table)))
       (order (or order (integers-from-to 1 (len alt)))))
    `(define ,parse-option ((input nat-listp))
       :returns (mv (tree tree-resultp)
                    (rest-input nat-listp))
       :short ,(str::cat "Parse a @('"
                         (defdefparse-print-element (element-option alt))
                         "').")
       (b* (((mv treess input)
             ,(defdefparse-gen-code-for-alternation
                alt order prefix group-table option-table repetition-table))
            ((when (reserrp treess))
             (mv (make-tree-nonleaf
                  :rulename? nil
                  :branches nil)
                 (nat-list-fix input))))
         (mv (make-tree-nonleaf :rulename? nil
                                :branches treess)
             input))
       :hooks (:fix)
       ///
       (defret ,(acl2::packn-pos (list 'len-of- parse-option '-<=)
                                 parse-option)
         (<= (len rest-input)
             (len input))
         :rule-classes :linear)))
  :guard-hints
  (("Goal"
    :in-theory
    (enable
     symbolp-of-cdr-of-assoc-equal-when-defdefparse-alt-symbol-alistp))))

;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-function-for-repetition
  ((rep repetitionp)
   (prefix acl2::symbolp)
   (group-table defdefparse-alt-symbol-alistp)
   (option-table defdefparse-alt-symbol-alistp)
   (repetition-table defdefparse-rep-symbol-alistp))
  :returns (event acl2::maybe-pseudo-event-formp)
  :short "Generate a parsing function for an ABNF repetition."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is only used for repetitions whose repeat prefix is @('*'),
     i.e. zero or more (i.e. this is all we support for now).
     The name is retrieved from the alist for repetition parsing functions.
     We generate a recursive function that
     repeatedly attempts to parse the underlying element.
     Note that we set the @('check-error-p') flag to @('nil') here,
     because we don't want the error to be returned,
     we just want to stop the recursion."))
  (b* ((parse-repetition (cdr (assoc-equal rep repetition-table)))
       ((repetition rep) rep)
       ((unless (equal rep.range
                       (make-repeat-range :min 0
                                          :max (nati-infinity))))
        (raise "Repetition ~x0 currently not supported." rep)))
    `(define ,parse-repetition ((input nat-listp))
       :returns (mv (trees tree-listp)
                    (rest-input nat-listp))
       :short ,(str::cat "Parse a @('" (defdefparse-print-repetition rep) "').")
       (b* (,@(defdefparse-gen-code-for-element
                rep.element nil prefix group-table option-table)
            ((when (reserrp tree)) (mv nil input))
            ((mv trees input) (,parse-repetition input)))
         (mv (cons tree trees) input))
       :hooks (:fix)
       :measure (len input)
       ///
       (defret ,(acl2::packn-pos (list 'len-of- parse-repetition)
                                 parse-repetition)
         (<= (len rest-input)
             (len input))
         :rule-classes :linear))))

;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-function-for-spec
  ((spec defdefparse-function-spec-p)
   (rules rulelistp)
   (prefix acl2::symbolp)
   (group-table defdefparse-alt-symbol-alistp)
   (option-table defdefparse-alt-symbol-alistp)
   (repetition-table defdefparse-rep-symbol-alistp))
  :returns (event acl2::maybe-pseudo-event-formp)
  :short "Generate a parsing function for a specification."
  (defdefparse-function-spec-case
    spec
    :rulename (defdefparse-gen-function-for-rulename
                spec.get spec.order rules
                prefix group-table option-table repetition-table)
    :group (defdefparse-gen-function-for-group
             spec.get spec.order
             prefix group-table option-table repetition-table)
    :option (defdefparse-gen-function-for-option
              spec.get spec.order
              prefix group-table option-table repetition-table)
    :repetition (defdefparse-gen-function-for-repetition
                  spec.get
                  prefix group-table option-table repetition-table)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-rulename-macro ((name acl2::symbolp)
                                        (pkg-wit acl2::symbolp)
                                        (grammar acl2::symbolp)
                                        (prefix acl2::symbolp)
                                        (group-table-name acl2::symbolp)
                                        (option-table-name acl2::symbolp)
                                        (repetition-table-name acl2::symbolp))
  :returns (event pseudo-event-formp)
  :short "Generate the @('defparse-name-rulename') macro
          described in the @(tsee defdefparse) user documentation."
  (b* ((macro-name
        (packn-pos (list 'defparse- name '-rulename) pkg-wit)))
    `(defmacro ,macro-name (rulename &key order)
       `(make-event (defdefparse-gen-function-for-spec
                      (defdefparse-function-spec-rulename ,rulename ',order)
                      ,',grammar
                      ',',prefix
                      ,',group-table-name
                      ,',option-table-name
                      ,',repetition-table-name)))))

;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-*-rulename-macro ((name acl2::symbolp)
                                          (pkg-wit acl2::symbolp)
                                          (grammar acl2::symbolp)
                                          (prefix acl2::symbolp)
                                          (group-table-name acl2::symbolp)
                                          (option-table-name acl2::symbolp)
                                          (repetition-table-name acl2::symbolp))
  :returns (event pseudo-event-formp)
  :short "Generate the @('defparse-name-*-rulename') macro
          described in the @(tsee defdefparse) user documentation."
  (b* ((macro-name
        (packn-pos (list 'defparse- name '-*-rulename) pkg-wit)))
    `(defmacro ,macro-name (rulename)
       `(make-event (defdefparse-gen-function-for-spec
                      (defdefparse-function-spec-repetition
                        (make-repetition
                         :element (element-rulename
                                   (rulename ,rulename))
                         :range (make-repeat-range
                                 :min 0
                                 :max (nati-infinity))))
                      ,',grammar
                      ',',prefix
                      ,',group-table-name
                      ,',option-table-name
                      ,',repetition-table-name)))))

;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-group-macro ((name acl2::symbolp)
                                     (pkg-wit acl2::symbolp)
                                     (grammar acl2::symbolp)
                                     (prefix acl2::symbolp)
                                     (group-table-name acl2::symbolp)
                                     (option-table-name acl2::symbolp)
                                     (repetition-table-name acl2::symbolp))
  :returns (event pseudo-event-formp)
  :short "Generate the @('defparse-name-group') macro
          described in the @(tsee defdefparse) user documentation."
  (b* ((macro-name
        (packn-pos (list 'defparse- name '-group) pkg-wit)))
    `(defmacro ,macro-name (group &key order)
       (b* (((mv err tree rest) (parse-group (string=>nats group)))
            ((when err) (er hard ',macro-name "~@0" err))
            ((when (consp rest))
             (er hard ',macro-name "Extra: ~s0." (nats=>string rest)))
            (alt (abstract-group/option tree)))
         `(make-event (defdefparse-gen-function-for-spec
                        (defdefparse-function-spec-group ',alt ',order)
                        ,',grammar
                        ',',prefix
                        ,',group-table-name
                        ,',option-table-name
                        ,',repetition-table-name))))))

;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-*-group-macro ((name acl2::symbolp)
                                       (pkg-wit acl2::symbolp)
                                       (grammar acl2::symbolp)
                                       (prefix acl2::symbolp)
                                       (group-table-name acl2::symbolp)
                                       (option-table-name acl2::symbolp)
                                       (repetition-table-name acl2::symbolp))
  :returns (event pseudo-event-formp)
  :short "Generate the @('defparse-name-*-group') macro
          described in the @(tsee defdefparse) user documentation."
  (b* ((macro-name
        (packn-pos (list 'defparse- name '-*-group) pkg-wit)))
    `(defmacro ,macro-name (group)
       (b* (((mv err tree rest) (parse-group (string=>nats group)))
            ((when err) (er hard ',macro-name "~@0" err))
            ((when (consp rest))
             (er hard ',macro-name "Extra: ~s0." (nats=>string rest)))
            (alt (abstract-group/option tree)))
         `(make-event (defdefparse-gen-function-for-spec
                        (defdefparse-function-spec-repetition
                          (make-repetition
                           :element (element-group ',alt)
                           :range (make-repeat-range
                                   :min 0
                                   :max (nati-infinity))))
                        ,',grammar
                        ',',prefix
                        ,',group-table-name
                        ,',option-table-name
                        ,',repetition-table-name))))))

;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-option-macro ((name acl2::symbolp)
                                      (pkg-wit acl2::symbolp)
                                      (grammar acl2::symbolp)
                                      (prefix acl2::symbolp)
                                      (group-table-name acl2::symbolp)
                                      (option-table-name acl2::symbolp)
                                      (repetition-table-name acl2::symbolp))
  :returns (event pseudo-event-formp)
  :short "Generate the @('defparse-name-option') macro
          described in the @(tsee defdefparse) user documentation."
  (b* ((macro-name
        (packn-pos (list 'defparse- name '-option) pkg-wit)))
    `(defmacro ,macro-name (option &key order)
       (b* (((mv err tree rest) (parse-option (string=>nats option)))
            ((when err) (er hard ',macro-name "~@0" err))
            ((when (consp rest))
             (er hard ',macro-name "Extra: ~s0." (nats=>string rest)))
            (alt (abstract-group/option tree)))
         `(make-event (defdefparse-gen-function-for-spec
                        (defdefparse-function-spec-option ',alt ',order)
                        ,',grammar
                        ',',prefix
                        ,',group-table-name
                        ,',option-table-name
                        ,',repetition-table-name))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defdefparse-gen-everything ((name acl2::symbolp)
                                    (pkg-wit acl2::symbolp)
                                    (grammar acl2::symbolp)
                                    (prefix acl2::symbolp))
  :returns (event pseudo-event-formp)
  :short "Generate all the events."
  (b* ((group-table-name (defdefparse-gen-group-table-name name pkg-wit))
       (option-table-name (defdefparse-gen-option-table-name name pkg-wit))
       (repetition-table-name (defdefparse-gen-repetition-table-name
                                name pkg-wit))
       (group-table-macro (defdefparse-gen-group-table-macro
                            name pkg-wit group-table-name prefix))
       (option-table-macro (defdefparse-gen-option-table-macro
                             name pkg-wit option-table-name prefix))
       (repetition-table-macro (defdefparse-gen-repetition-table-macro
                                 name pkg-wit repetition-table-name prefix))
       (rulename-macro (defdefparse-gen-rulename-macro
                         name pkg-wit grammar prefix
                         group-table-name
                         option-table-name
                         repetition-table-name))
       (*-rulename-macro (defdefparse-gen-*-rulename-macro
                           name pkg-wit grammar prefix
                           group-table-name
                           option-table-name
                           repetition-table-name))
       (group-macro (defdefparse-gen-group-macro
                      name pkg-wit grammar prefix
                      group-table-name
                      option-table-name
                      repetition-table-name))
       (*-group-macro (defdefparse-gen-*-group-macro
                        name pkg-wit grammar prefix
                        group-table-name
                        option-table-name
                        repetition-table-name))
       (option-macro (defdefparse-gen-option-macro
                       name pkg-wit grammar prefix
                       group-table-name
                       option-table-name
                       repetition-table-name)))
    `(progn
       ,group-table-macro
       ,option-table-macro
       ,repetition-table-macro
       ,rulename-macro
       ,*-rulename-macro
       ,group-macro
       ,*-group-macro
       ,option-macro)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defdefparse-fn ((args true-listp) (ctx ctxp) state)
  :returns (mv erp
               (even pseudo-event-formp)
               state)
  :parents (defdefparse-implementation)
  :short "Process the inputs and generate the events."
  (b* (((er (list name pkg-wit grammar prefix) :iferr '(_))
        (defdefparse-process-inputs args ctx state))
       (event (defdefparse-gen-everything name pkg-wit grammar prefix)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defdefparse-macro-definition
  :parents (defdefparse-implementation)
  :short "Definition of the @(tsee defdefparse) macro."

  (defmacro defdefparse (&rest args)
    `(make-event (defdefparse-fn ',args 'defdefparse state))))
