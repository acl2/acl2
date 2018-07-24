; Fixtypes for Unsigned and Signed Bytes -- Macro
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)
(include-book "std/typed-lists/signed-byte-listp" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "kestrel/utilities/event-forms" :dir :system)
(include-book "kestrel/utilities/xdoc-constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defbyte

  :parents (kestrel-utilities fty::fty)

  :short "Introduce <see topic='@(url fty)'>fixtypes</see> for
          unsigned or signed bytes of a specified size,
          and true lists thereof."

  :long

  (xdoc::topapp

   (xdoc::h3 "Introduction")

   (xdoc::p
    "Currently fixtypes can only be associated to unary predicates,
     but @(tsee unsigned-byte-p) and @(tsee signed-byte-p)
     are binary predicates,
     as are @(tsee unsigned-byte-listp) and @(tsee signed-byte-listp).")

   (xdoc::p
    "This macro introduces unary recognizers, and associated fixtypes,
     for unsigned or signed bytes of specified sizes,
     as well as for true lists thereof.
     It also generates various theorems that relate the unary recognizers
     to the binary predicates and to other built-in predicates.")

   (xdoc::h3 "General Form")

   (xdoc::code
    "(defbyte size"
    "         :signed ..."
    "         :type ..."
    "         :pred ..."
    "         :fix ..."
    "         :equiv ..."
    "         :ltype ..."
    "         :lpred ..."
    "         :lfix ..."
    "         :lequiv ..."
    "         :parents ..."
    "         :description ..."
    "         :long ..."
    "         :llong ..."
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
      that provably denotes a positive integer."))

   (xdoc::desc
    "@(':signed')"
    (xdoc::p
     "A boolean that specifies whether the bytes are
      unsigned (@('nil'), the default) or signed (@('t'))."))

   (xdoc::desc
    "@(':type')"
    (xdoc::p
     "A symbol that specifies the name of the fixtype for the bytes.
      If this is @('nil') (the default),
      the name of the type is @('ubyte<size>') or @('sbyte<size>'),
      based on whether @(':signed') is @('nil') or @('t'),
      where @('<size>') is a decimal representation of the value of @('size').
      If @('size') is a call of a nullary function,
      @(':type') must not be @('nil')."))

   (xdoc::desc
    "@(':pred')"
    (xdoc::p
     "A symbol that specifies the name of the unary recognizer for the bytes.
      If this is @('nil') (the default),
      the name of the recognizer is @('<type>-p'),
      where @('<type>') is the name of the fixtype for bytes,
      as specified via the @(':type') input."))

   (xdoc::desc
    "@(':fix')"
    (xdoc::p
     "A symbol that specifies the name of the fixer for the bytes.
      If this is @('nil') (the default),
      the name of the fixer is @('<type>-fix'),
      where @('<type>') is the name of the fixtype for bytes,
      as specified via the @(':type') input."))

   (xdoc::desc
    "@(':equiv')"
    (xdoc::p
     "A symbol that specifies the name of the equivalence for the bytes.
      If this is @('nil') (the default),
      the name of the equivalence is @('<type>-equiv'),
      where @('<type>') is the name of the fixtype for bytes,
      as specified via the @(':type') input."))

   (xdoc::desc
    "@(':ltype')"
    (xdoc::p
     "A symbol that specifies the name of
      the fixtype for the true lists of bytes.
      If this is @('nil') (the default),
      the name of the fixtype is @('<type>-list'),
      where @('<type>') is the name of the fixtype for bytes,
      as specified via the @(':type') input."))

   (xdoc::desc
    "@(':lpred')"
    (xdoc::p
     "A symbol that specifies the name of
      the unary recognizer for the true lists of bytes.
      If this is @('nil') (the default),
      the name of the recognizer is @('<ltype>-p'),
      where @('<ltype>') is the name of the fixtype for lists of bytes,
      as specified via the @(':ltype') input."))

   (xdoc::desc
    "@(':lfix')"
    (xdoc::p
     "A symbol that specifies the name of
      the fixer for the true lists of bytes.
      If this is @('nil') (the default),
      the name of the fixer is @('<ltype>-fix'),
      where @('<ltype>') is the name of the fixtype for lists of bytes,
      as specified via the @(':ltype') input."))

   (xdoc::desc
    "@(':lequiv')"
    (xdoc::p
     "A symbol that specifies the name of
      the equivalence for the true lists of bytes.
      If this is @('nil') (the default),
      the name of the recognizer is @('<ltype>-equiv'),
      where @('<ltype>') is the name of the fixtype for lists of bytes,
      as specified via the @(':ltype') input."))

   (xdoc::desc
    "@(':parents')"
    (xdoc::p
     "A list of symbols to use as XDOC parents of
      the generated fixtype of
      unsigned or signed bytes of the specified size.
      The default is @('nil'), i.e. no parents.
      All the other generated XDOC topics are (directly or indirectly)
      under the XDOC topic for this generated fixtype."))

   (xdoc::desc
    "@(':description')"
    (xdoc::p
     "A string that describes the bytes for which the fixtype is generated,
      or @('nil') (the default).
      If this is a string,
      it is inserted into the generated XDOC @(':short') strings;
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
     "A string that provides additional documentation for the fixtype of bytes,
      or @('nil') (the default).
      If this is a string,
      it is used as the XDOC @(':long') string
      of the generated fixtype of bytes.
      If this is is @('nil') instead,
      no @(':long') is generated for the fixtype of bytes."))

   (xdoc::desc
    "@(':llong')"
    (xdoc::p
     "A string that provides additional documentation for
      the fixtype of lists of bytes,
      or @('nil') (the default).
      If this is a string,
      it is used as the XDOC @(':long') string
      of the generated fixtype of lists of bytes.
      If this is is @('nil') instead,
      no @(':long') is generated for the fixtype of lists of bytes."))

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
     "A unary recognizer, a fixer, an equivalence, and a fixtype
      for true lists of unsigned or signed bytes of the specified size.")

    (xdoc::li
     "Forward chaining rules
      from the unary recognizers to the binary predicates,
      which can combine with
      forward chaining rules from the binary predicates.")

    (xdoc::li
     "A rule that rewrites the binary predicate for unsigned or signed bytes
      to the unary recognizer for unsigned or signed bytes.
      This rule is disabled by default, but may be useful in some proofs.
      Since this is the converse of the definition of the unary recognizer,
      a theory invariant is also generated preventing the enabling of
      both this rule and the definition of the unary recognizer.")

    (xdoc::li
     "Rules that rewrite between
      the binary predicate for lists of unsigned or signed bytes
      and the unary recognizer for lists of unsigned or signed bytes.
      These rules are disabled by default, but may be useful in some proofs.
      Since these are converse rules,
      a theory invariant is also generated preventing the enabling of both.")

    (xdoc::li
     "A rule to prove @(tsee true-listp)
      from the unary recognizer of lists of unsigned or signed bytes.
      Since @(tsee true-listp) is relatively common,
      this rule is disabled by default for efficiency."))

   (xdoc::p
    "See the implementation, which uses a readable backquote notation,
     for details.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defbyte-fn (size
                    signed
                    type
                    pred
                    fix
                    equiv
                    ltype
                    lpred
                    lfix
                    lequiv
                    parents
                    description
                    long
                    llong
                    (wrld plist-worldp))
  :returns (event "A @(tsee maybe-pseudo-event-formp).")
  :mode :program
  :parents (defbyte-macro-definition)
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
       (size-value (b* (((when (posp size)) size)
                        (const-val (unquote (defined-constant size wrld)))
                        ((when (posp const-val)) const-val))
                     nil)) ; SIZE must be a call to a nullary function
       ((unless (or size-value
                    (and (tuplep 1 size)
                         (= 0 (arity (car size) wrld)))))
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
       ((unless (symbolp ltype))
        (raise "The :LTYPE input must be a symbol, ~
                but it is ~x0 instead." ltype))
       ((unless (symbolp lpred))
        (raise "The :LPRED input must be a symbol, ~
                but it is ~x0 instead." lpred))
       ((unless (symbolp lfix))
        (raise "The :LFIX input must be a symbol, ~
                but it is ~x0 instead." lfix))
       ((unless (symbolp lequiv))
        (raise "The :LEQUIV input must be a symbol, ~
                but it is ~x0 instead." lequiv))
       ((unless (symbol-listp parents))
        (raise "The :PARENTS input must be a true list of symbols, ~
                but it is ~x0 instead." parents))
       ((unless (maybe-stringp description))
        (raise "The :DESCRIPTION input must be a string or NIL, ~
                but it is ~x0 instead." description))
       ((unless (or size-value description))
        (raise "Since the SIZE input is a call of a nullary function, ~
                the :DESCRIPTION input must be supplied and not be NIL."))
       ((unless (maybe-stringp long))
        (raise "The :LONG input must be a string or NIL, ~
                but it is ~x0 instead." long))
       ((unless (maybe-stringp llong))
        (raise "The :LLONG input must be a string or NIL, ~
                but it is ~x0 instead." llong))
       ;; names of the binary predicates:
       (binpred (if signed 'signed-byte-p 'unsigned-byte-p))
       (lbinpred (if signed 'signed-byte-listp 'unsigned-byte-listp))
       ;; names of the generated fixtypes:
       (type (or type (packn (list (if signed 'sbyte 'ubyte) size-value))))
       (ltype (or ltype (packn (list type '-list))))
       ;; names of the generated functions:
       (pred (or pred (packn (list type '-p))))
       (fix (or fix (packn (list type '-fix))))
       (equiv (or equiv (packn (list type '-equiv))))
       (lpred (or lpred (packn (list ltype '-p))))
       (lfix (or lfix (packn (list ltype '-fix))))
       (lequiv (or lequiv (packn (list ltype '-equiv))))
       ;; names of the generated theorems:
       (fix-when-pred (packn (list fix '-when- pred)))
       (pred-forward-binpred (packn (list pred '-forward- binpred)))
       (lpred-forward-lbinpred (packn (list lpred '-forward- lbinpred)))
       (binpred-rewrite-pred (packn (list binpred '-rewrite- pred)))
       (lpred-rewrite-lbinpred (packn (list lpred '-rewrite- lbinpred)))
       (lbinpred-rewrite-lpred (packn (list lbinpred '-rewrite- lpred)))
       (true-listp-when-lpred-rewrite (packn (list 'true-listp-when-
                                                   lpred
                                                   '-rewrite)))
       ;; parts of the generated XDOC:
       (ltype-theorems (packn (list ltype '-theorems)))
       (bytes-string
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
                              bytes-string
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
                  :prep-books ((include-book "arithmetic-5/top"
                                             :dir :system)))))
       (define ,fix ((x ,pred))
         :returns (fixed-x ,pred)
         :parents (,type)
         :short ,(concatenate 'string
                              "Fix values to "
                              bytes-string
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
                              "<see topic='@(url fty)'>Fixtype</see> of "
                              bytes-string
                              ".")
         ,@(and long `(:long ,long))
         (fty::deffixtype ,type
           :pred ,pred
           :fix ,fix
           :equiv ,equiv
           :define t
           :forward t))
       (fty::deflist ,ltype
         :elt-type ,type
         :parents (,type)
         :short ,(concatenate 'string
                              "<see topic='@(url fty)'>Fixtype</see> of "
                              "true lists of "
                              bytes-string
                              ".")
         ,@(and llong `(:long ,llong))
         :true-listp t
         :pred ,lpred
         :fix ,lfix
         :equiv ,lequiv)
       (defsection ,ltype-theorems
         :extension ,ltype
         (defrule ,lpred-forward-lbinpred
           (implies (,lpred x)
                    (,lbinpred ,size x))
           :rule-classes :forward-chaining
           :enable (,lpred ,pred))
         (defruled ,lpred-rewrite-lbinpred
           (equal (,lpred x)
                  (,lbinpred ,size x))
           :enable (,lpred ,pred))
         (defruled ,lbinpred-rewrite-lpred
           (equal (,lbinpred ,size x)
                  (,lpred x))
           :enable ,lpred-rewrite-lbinpred)
         (theory-invariant
          (incompatible (:rewrite ,lpred-rewrite-lbinpred)
                        (:rewrite ,lbinpred-rewrite-lpred)))
         (defruled ,true-listp-when-lpred-rewrite
           (implies (,lpred x)
                    (true-listp x)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defbyte-macro-definition
  :parents (defbyte)
  :short "Definition of the @(tsee defbyte) macro."
  :long "@(def defbyte)"
  (defmacro defbyte (size
                     &key
                     signed
                     type
                     pred
                     fix
                     equiv
                     ltype
                     lpred
                     lfix
                     lequiv
                     parents
                     description
                     long
                     llong)
    `(make-event (defbyte-fn
                   ',size
                   ',signed
                   ',type
                   ',pred
                   ',fix
                   ',equiv
                   ',ltype
                   ',lpred
                   ',lfix
                   ',lequiv
                   ',parents
                   ,description
                   ,long
                   ,llong
                   (w state)))))
