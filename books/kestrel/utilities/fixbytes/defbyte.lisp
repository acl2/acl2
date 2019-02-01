; Fixtypes for Unsigned and Signed Bytes -- Macro
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/utilities/event-forms" :dir :system)
(include-book "kestrel/utilities/xdoc/defxdoc-plus" :dir :system)
(include-book "std/util/defaggregate" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/util/defval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defbyte

  :parents (acl2::kestrel-utilities fty)

  :short "Introduce <see topic='@(url fty)'>fixtypes</see> for
          unsigned or signed bytes of a specified size."

  :long

  (xdoc::topapp

   (xdoc::h3 "Introduction")

   (xdoc::p
    "Currently fixtypes can only be associated to unary predicates,
     but @(tsee unsigned-byte-p) and @(tsee signed-byte-p)
     are binary predicates.")

   (xdoc::p
    "This macro introduces unary recognizers, and associated fixtypes,
     for unsigned or signed bytes of specified sizes.
     It also generates various theorems that relate
     the unary recognizers to the binary predicates.")

   (xdoc::h3 "General Form")

   (xdoc::code
    "(defbyte size"
    "         :signed ..."
    "         :type ..."
    "         :pred ..."
    "         :fix ..."
    "         :equiv ..."
    "         :parents ..."
    "         :description ..."
    "         :long ..."
    "  )")

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@('size')"
    (xdoc::p
     "A term that specifies the size of the bytes in bits.
      This must be one of the following:
      (1) an explicit positive integer value;
      (2) a named constant whose value is a positive integer;
      (3) a call of a nullary function (defined or constrained)
      that is guard-verified and provably denotes a positive integer."))

   (xdoc::desc
    "@(':signed')"
    (xdoc::p
     "A boolean that specifies whether the bytes are
      unsigned (@('nil'), the default) or signed (@('t'))."))

   (xdoc::desc
    "@(':type')"
    (xdoc::p
     "A symbol that specifies the name of the fixtype.
      If this is @('nil') (the default),
      the name of the type is @('ubyte<size>') or @('sbyte<size>'),
      based on whether @(':signed') is @('nil') or @('t'),
      where @('<size>') is a decimal representation of the value of @('size').
      If @('size') is a call of a nullary function,
      @(':type') must not be @('nil')."))

   (xdoc::desc
    "@(':pred')"
    (xdoc::p
     "A symbol that specifies the name of the unary recognizer.
      If this is @('nil') (the default),
      the name of the recognizer is @('<type>-p'),
      where @('<type>') is the name of the fixtype,
      as specified via the @(':type') input."))

   (xdoc::desc
    "@(':fix')"
    (xdoc::p
     "A symbol that specifies the name of the fixer.
      If this is @('nil') (the default),
      the name of the fixer is @('<type>-fix'),
      where @('<type>') is the name of the fixtype,
      as specified via the @(':type') input."))

   (xdoc::desc
    "@(':equiv')"
    (xdoc::p
     "A symbol that specifies the name of the equivalence.
      If this is @('nil') (the default),
      the name of the equivalence is @('<type>-equiv'),
      where @('<type>') is the name of the fixtype,
      as specified via the @(':type') input."))

   (xdoc::desc
    "@(':parents')"
    (xdoc::p
     "A list of symbols to use as XDOC parents of
      the generated fixtype.
      The default is @('nil'), i.e. no parents.
      All the other generated XDOC topics are (directly or indirectly)
      under the XDOC topic for this generated fixtype."))

   (xdoc::desc
    "@(':description')"
    (xdoc::p
     "A string that describes the bytes for which the fixtype is generated,
      or @('nil') (the default).
      If this is a string,
      it is inserted into the generated XDOC @(':short');
      the string must start with a lowercase letter
      (because it is used to complete the phrase in the @(':short')),
      must not end with any punctuation
      (because a period is automatically added just after this string),
      and must be plural in number
      (because that matches the rest of the phrase).
      If this is @('nil') instead,
      the @(':short') is entirely generated,
      based on the @('size') and @(':signed') inputs.
      If @('size') is a call of a nullary function,
      @(':description') must not be @('nil').
      See the implementation for the exact details:
      the requirements on this input should be clear from the way it is used."))

   (xdoc::desc
    "@(':long')"
    (xdoc::p
     "A string that provides additional documentation for the fixtype,
      or @('nil') (the default).
      If this is a string,
      it is used as the XDOC @(':long') string
      of the generated fixtype.
      If this is @('nil') instead,
      no @(':long') is generated for the fixtype."))

   (xdoc::p
    "This macro currently does not perform a thorough validation of its inputs.
     In particular, it does not check whether
     the names of the generated events already exists.
     Errors may result in failures of the generated events.
     These errors should be easy to diagnose,
     also since this macro has a very simple and readable implementation.")

   (xdoc::h3 "Generated Functions and Theorems")

   (xdoc::p
    "The following are generated, inclusive of XDOC documentation:")

   (xdoc::ul

    (xdoc::li
     "A unary recognizer, a fixer, an equivalence, and a fixtype
      for unsigned or signed bytes of the specified size.")

    (xdoc::li
     "Forward chaining rules
      from the unary recognizers to the binary predicates
      @(tsee unsigned-byte-p) and @(tsee signed-byte-p).
      These rules can combine with
      forward chaining rules from the binary predicates.")

    (xdoc::li
     "A rule that rewrites the binary predicate to the unary recognizer.
      This rule is disabled by default, but may be useful in some proofs.
      Since this is the converse of the definition of the unary recognizer,
      a theory invariant is also generated preventing the enabling of
      both this rule and the definition of the unary recognizer."))

   (xdoc::p
    "See the implementation, which uses a readable backquote notation,
     for details.")

   (xdoc::h3 "Note about Packages")

   (xdoc::p
    "When using @('defbyte') to define 8-bit bytes
     (the most common size of bytes in modern contexts)
     `@('byte')' could be a reasonable name for the fixtype.
     However, note that the @('\"ACL2\"') package
     imports a symbol with that name from the @('\"COMMON-LISP\"') package;
     that symbol may be then implicitly imported
     in a user-defined package @('\"P\"') where @('defbyte') is used.
     This means that @('p::byte') is actually @('common-lisp::byte'),
     and that function and theorem names derived from it by @('defbyte')
     will end up in the @('\"ACL2\"') package
     rather than in the @('\"P\"') package,
     e.g. @('acl2::byte-fix') instead of @('p::byte-fix').
     Thus, it is recommended to arrange for @('\"P\"')
     to exclude the symbol @('common-lisp::byte'),
     so that @('p::byte') is a different symbol.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::defxdoc+ defbyte-implementation
  :parents (defbyte)
  :short "Implementation of @(tsee defbyte)."
  :order-subtopics t
  :default-parent t)

(std::defaggregate defbyte-info
  :short "Information about a @(tsee defbyte) type,
          recorded as a pair's value in the
          <see topic='@(url defbyte-table)'>@(tsee defbyte) table</see>."
  :long
  "<p>
   The name of the type is the key of the pair in the table.
   </p>"
  ((size "The @('size') input."
         (or (posp size)
             (symbolp size)
             (and (acl2::tuplep 1 size)
                  (symbolp (car size)))))
   (signed "Whether the bytes are signed or not." booleanp)
   (pred "The name of the recognizer." symbolp)
   (fix "The name of the fixer." symbolp)
   (equiv "The name of the equivalence." symbolp)
   (description "The description of the bytes used in the documentation."
                stringp))
  :pred defbyte-infop)

(defval *defbyte-table-name*
  'defbyte-table
  :short "Name of the
          <see topic='@(url defbyte-table)'>@(tsee defbyte) table</see>.")

(defsection defbyte-table
  :short "@(csee table) of @(tsee defbyte) types."
  :long
  (xdoc::topapp
   (xdoc::p
    "For each successful call of @(tsee defbyte),
     this table includes a pair whose key is the name of the type
     and whose value contains other information about the call
     (see @(tsee defbyte-infop)).")
   (xdoc::p
    "This table is used by @(tsee defbytelist)."))

  (make-event
   `(table ,*defbyte-table-name* nil nil
      :guard (and (symbolp acl2::key) ; name of the type
                  (defbyte-infop acl2::val)))))

(define defbyte-check-size (size (wrld plist-worldp))
  :returns (mv (valid "A @(tsee booleanp).")
               (value "A @(tsee acl2::maybe-posp)"))
  :mode :program
  :short "Check if the @('size') input is valid."
  :long
  (xdoc::topapp
   (xdoc::p
    "The first result is @('t') if the input is valid,
     otherwise it is @('nil').
     If the input is a call of a unary function,
     we do not check here that it is guard-verified
     and that it provably denotes a positive integer.
     In these cases, the call to the macro will fail
     (hopefully in a comprehensible way).")
   (xdoc::p
    "If the input is valid and is not a call of a unary function,
     the second result is the value of the input,
     which is known in this case.
     Otherwise, the second result is @('nil')."))
  (b* (((when (posp size)) (mv t size))
       (const? (acl2::defined-constant size wrld))
       ((when const?)
        (b* ((value (unquote const?)))
          (if (posp value)
              (mv t value)
            (mv nil nil))))
       ((unless (acl2::tuplep 1 size)) (mv nil nil))
       (fn (car size)))
    (if (and (function-symbolp fn wrld)
             (= 0 (arity fn wrld)))
        (mv t nil)
      (mv nil nil))))

(define defbyte-fn (size
                    signed
                    type
                    pred
                    fix
                    equiv
                    parents
                    description
                    long
                    (wrld plist-worldp))
  :returns (event "A @(tsee acl2::maybe-pseudo-event-formp).")
  :mode :program
  :short "Event generated by the @(tsee defbyte) macro."
  :long
  (xdoc::topapp
   (xdoc::p
    "When @('size') is a call of a nullary function
     (which is the case iff the local variable @('size-value') is @('nil');
     otherwise, this variable has the numeric value of @('size')),
     the generated event includes two additional theorems.
     The first theorem,
     at the very beginning of the @(tsee encapsulate),
     shows that @('size') is a positive integer,
     as a type prescription rule.
     The second theorem,
     just after the unary recognizer for the bytes is introduced,
     shows that 0 satisfies the recognizer,
     as a rewrite rule:
     this theorem serves to prove the return type theorems of the fixer."))
  (b* (;; validate the SIZE input:
       ((mv size-valid size-value) (defbyte-check-size size wrld))
       ((unless size-valid)
        (raise "The SIZE input must be ~
                (1) an explicit positive integer value, or ~
                (2) a named constant whose value is a positive integer, or ~
                (3) a call of a nullary function (defined or constrained) ~
                that provably denotes a positive integer; ~
                but it is ~x0 instead." size))
       ;; validate the other inputs:
       ((unless (booleanp signed))
        (raise "The :SIGNED input must be a boolean, ~
                but it is ~x0 instead." signed))
       ((unless (symbolp type))
        (raise "The :TYPE input must be a symbol, ~
                but it is ~x0 instead." type))
       ((unless (or size-value type))
        (raise "Since the SIZE input is a call of a nullary function, ~
                the :TYPE input must be supplied and not be NIL."))
       ((unless (symbolp pred))
        (raise "The :PRED input must be a symbol, ~
                but it is ~x0 instead." pred))
       ((unless (symbolp fix))
        (raise "The :FIX input must be a symbol, ~
                but it is ~x0 instead." fix))
       ((unless (symbolp equiv))
        (raise "The :EQUIV input must be a symbol, ~
                but it is ~x0 instead." equiv))
       ((unless (symbol-listp parents))
        (raise "The :PARENTS input must be a true list of symbols, ~
                but it is ~x0 instead." parents))
       ((unless (acl2::maybe-stringp description))
        (raise "The :DESCRIPTION input must be a string or NIL, ~
                but it is ~x0 instead." description))
       ((unless (or size-value description))
        (raise "Since the SIZE input is a call of a nullary function, ~
                the :DESCRIPTION input must be supplied and not be NIL."))
       ((unless (acl2::maybe-stringp long))
        (raise "The :LONG input must be a string or NIL, ~
                but it is ~x0 instead." long))
       ;; name of the binary predicate:
       (binpred (if signed 'acl2::signed-byte-p 'acl2::unsigned-byte-p))
       ;; name of the generated fixtype:
       (type (or type (acl2::packn (list (if signed 'acl2::sbyte 'acl2::ubyte)
                                         size-value))))
       ;; names of the generated functions:
       (pred (or pred (acl2::add-suffix-to-fn type "-P")))
       (fix (or fix (acl2::add-suffix-to-fn type "-FIX")))
       (equiv (or equiv (acl2::add-suffix-to-fn type "-EQUIV")))
       ;; names of the generated theorems:
       (fix-when-pred (acl2::packn (list fix '-when- pred)))
       (pred-forward-binpred (acl2::packn (list pred '-forward- binpred)))
       (binpred-rewrite-pred (acl2::packn-pos (list binpred '-rewrite- pred)
                                              (pkg-witness
                                               (symbol-package-name pred))))
       ;; description of the bytes used in the generated XDOC:
       (description
        (or description
            (concatenate 'string
                         (if signed "signed" "unsigned")
                         " bytes of size "
                         (coerce (explode-nonnegative-integer size-value 10 nil)
                                 'string)))))
    ;; generated events:
    `(encapsulate
       ()
       ,@(and (not size-value)
              `((defrulel posp-of-size
                  (posp ,size)
                  :rule-classes :type-prescription)))
       (define ,pred (x)
         :returns (yes/no booleanp)
         :parents (,type)
         :short ,(concatenate 'string
                              "Recognize "
                              description
                              ".")
         (,binpred ,size x)
         :no-function t
         ///
         (defrule ,pred-forward-binpred
           (implies (,pred x)
                    (,binpred ,size x))
           :rule-classes :forward-chaining)
         (defruled ,binpred-rewrite-pred
           (equal (,binpred ,size x)
                  (,pred x)))
         (theory-invariant
          (incompatible (:rewrite ,binpred-rewrite-pred)
                        (:definition ,pred))))
       ,@(and (not size-value)
              `((defrulel recog-of-0
                  (,pred 0)
                  :enable ,pred
                  :prep-books ((include-book "arithmetic/top" :dir :system)))))
       (define ,fix ((x ,pred))
         :returns (fixed-x ,pred)
         :parents (,type)
         :short ,(concatenate 'string
                              "Fix values to "
                              description
                              ".")
         (mbe :logic (if (,pred x) x 0)
              :exec x)
         :no-function t
         ///
         (defrule ,fix-when-pred
           (implies (,pred x)
                    (equal (,fix x) x))
           :enable ,pred))
       (defsection ,type
         :parents ,parents
         :short ,(concatenate 'string
                              "<see topic='@(url acl2::fty)'>Fixtype</see> of "
                              description
                              ".")
         ,@(and long `(:long ,long))
         (fty::deffixtype ,type
           :pred ,pred
           :fix ,fix
           :equiv ,equiv
           :define t
           :forward t))
       (table ,*defbyte-table-name*
         ',type
         ',(make-defbyte-info :size size
                              :signed signed
                              :pred pred
                              :fix fix
                              :equiv equiv
                              :description description)))))

(defsection defbyte-macro-definition
  :short "Definition of the @(tsee defbyte) macro."
  :long "@(def defbyte)"
  (defmacro defbyte (size
                     &key
                     signed
                     type
                     pred
                     fix
                     equiv
                     parents
                     description
                     long)
    `(make-event (defbyte-fn
                   ',size
                   ',signed
                   ',type
                   ',pred
                   ',fix
                   ',equiv
                   ',parents
                   ,description
                   ,long
                   (w state)))))
