; Fixtypes of Unsigned and Signed Bytes -- Generator
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
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

  :parents (acl2::kestrel-utilities
            fty
            unsigned-byte-p
            signed-byte-p)

  :short "Introduce a <see topic='@(url fty)'>fixtype</see> of
          unsigned or signed bytes of a specified size."

  :long

  (xdoc::topstring

   (xdoc::h3 "Introduction")

   (xdoc::p
    "Currently fixtypes can only be associated to unary predicates,
     but @(tsee unsigned-byte-p) and @(tsee signed-byte-p)
     are binary predicates.")

   (xdoc::p
    "This macro introduces unary recognizers, and associated fixtypes,
     of unsigned or signed bytes of specified sizes.
     It also generates various theorems that relate
     the unary recognizers to the binary predicates.")

   (xdoc::p
    "Besides their use in fixtypes,
     the unary recognizers introduced by this macro support
     <see topic='@(url acl2::tau-system)'>tau system</see> reasoning.")

   (xdoc::h3 "General Form")

   (xdoc::@code
    "(defbyte type"
    "         :size ..."
    "         :signed ..."
    "         :pred ..."
    "         :fix ..."
    "         :equiv ..."
    "         :parents ..."
    "         :short ..."
    "         :long ..."
    "  )")

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@(':type')"
    (xdoc::p
     "A symbol that specifies the name of the fixtype."))

   (xdoc::desc
    "@(':size')"
    (xdoc::p
     "A term that specifies the size of the bytes in bits.
      This must be one of the following:
      (1) an explicit positive integer value;
      (2) a named constant whose value is a positive integer;
      (3) a call of a nullary function (defined or constrained)
      that is guard-verified and provably denotes a positive integer.")
    (xdoc::p
     "This input must be supplied; there is no default."))

   (xdoc::desc
    "@(':signed')"
    (xdoc::p
     "A boolean that specifies whether the bytes are
      unsigned (@('nil'), the default) or signed (@('t'))."))

   (xdoc::desc
    "@(':pred')"
    (xdoc::p
     "A symbol that specifies the name of the fixtype's recognizer.
      If this is @('nil') (the default),
      the name of the recognizer is @('type') followed by @('-p')."))

   (xdoc::desc
    "@(':fix')"
    (xdoc::p
     "A symbol that specifies the name of the fixtype's fixer.
      If this is @('nil') (the default),
      the name of the fixer is @('type') followed by @('-fix')."))

   (xdoc::desc
    "@(':equiv')"
    (xdoc::p
     "A symbol that specifies the name of the fixtype's equivalence.
      If this is @('nil') (the default),
      the name of the equivalence is @('type') followed by @('-equiv')."))

   (xdoc::desc
    (list
     "@(':parents')"
     "@(':short')"
     "@(':long')")
    (xdoc::p
     "These, if present, are added to
      the XDOC topic generated for the fixtype."))

   (xdoc::h3 "Generated Events")

   (xdoc::desc
    "@('pred')"
    (xdoc::p
     "The recognizer for the fixtype, guard-verified."))

   (xdoc::desc
    "@('booleanp-of-pred')"
    (xdoc::p
     "A rewrite rule saying that @('pred') is boolean-valued."))

   (xdoc::desc
    "@('pred-forward-binpred')"
    (xdoc::p
     "A forward chaining rule from @('pred')
      to the corresponding binary predicate
      @(tsee unsigned-byte-p) or @(tsee signed-byte-p)."))

   (xdoc::desc
    "@('binpred-rewrite-pred')"
    (xdoc::p
     "A rule that rewrites the binary predicate
      @(tsee unsigned-byte-p) or @(tsee signed-byte-p)
      to @('pred').
      This rule is disabled by default, but may be useful in some proofs.
      Since this is the converse of the definition of the unary recognizer,
      a theory invariant is also generated preventing the enabling of
      both this rule and the definition of the unary recognizer."))

   (xdoc::desc
    "@('fix')"
    (xdoc::p
     "The fixer for the fixtype, guard-verified.")
    (xdoc::p
     "It fixes values outside of @('pred') to 0."))

   (xdoc::desc
    "@('pred-of-fix')"
    (xdoc::p
     "A rewrite rule saying that @('fix') always returns
      a value that satisfies @('pred')."))

   (xdoc::desc
    "@('fix-when-pred')"
    (xdoc::p
     "A rewrite rule saying that @('fix') disappears
      when its argument satisfies @('pred')."))

   (xdoc::desc
    "@('type')
     <br/>
     @('equiv')"
    (xdoc::p
     "The fixtype, via a call of @(tsee fty::deffixtype)
      that also introduces the equivalence @('equiv')."))

   (xdoc::desc
    "@('type-size-is-posp')"
    (xdoc::p
     "When the @('size') input is a unary function call,
      we also generate a rewrite and type prescription rule saying that
      the unary function call satisfies @(tsee posp)."))

   (xdoc::p
    "The above items are generated with XDOC documentation.")

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
   (signed "Whether the bytes are signed or not." booleanp))
  :pred defbyte-infop)

(defval *defbyte-table-name*
  'defbyte-table
  :short "Name of the
          <see topic='@(url defbyte-table)'>@(tsee defbyte) table</see>.")

(defsection defbyte-table
  :short "@(csee table) of @(tsee defbyte) types."
  :long
  (xdoc::topstring
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
  (xdoc::topstring
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

(defrule defbyte-fix-support-lemma
  :short "Support lemma for generated fixing theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the events generated by @(tsee defbyte),
     proving that the fixer returns a value that satisfies the recognizer
     boils down to proving that 0 satisfies the recognizer.
     This is easy when the size of the bytes is known:
     the proof is done via the executable counterparts of the functions.
     When the size of the bytes is a nullary function call,
     we need a bit of arithmetic reasoning,
     based on the fact that the size must be provably positive.")
   (xdoc::p
    "The following general lemma is referenced in
     the hints generated by @(tsee defbyte)."))
  (implies (posp z)
           (and (<= (- (expt 2 (1- z))) 0)
                (< 0 (expt 2 (1- z)))
                (< 0 (expt 2 z))))
  :rule-classes nil
  :prep-books ((include-book "arithmetic/top" :dir :system)))

(define defbyte-fn (type
                    size
                    signed
                    pred
                    fix
                    equiv
                    parents
                    short
                    long
                    (wrld plist-worldp))
  :returns (event "A @(tsee acl2::maybe-pseudo-event-formp).")
  :mode :program
  :short "Events generated by @(tsee defbyte)."
  :long
  (xdoc::toppstring
   "For now we only perform partial validation of the inputs.
    Future implementations may perform a more thorough validation.")
  (b* (;; validate the TYPE input:
       ((unless (symbolp type))
        (raise "The TYPE input must be a symbol, ~
                but it is ~x0 instead." type))
       ;; validate the SIZE input:
       ((mv size-valid size-value) (defbyte-check-size size wrld))
       ((unless size-valid)
        (raise "The SIZE input must be ~
                (1) an explicit positive integer value, or ~
                (2) a named constant whose value is a positive integer, or ~
                (3) a call of a nullary function (defined or constrained) ~
                that provably denotes a positive integer; ~
                but it is ~x0 instead." size))
       ;; validate the :SIGNED input:
       ((unless (booleanp signed))
        (raise "The :SIGNED input must be a boolean, ~
                but it is ~x0 instead." signed))
       ;; validate the :PRED input:
       ((unless (symbolp pred))
        (raise "The :PRED input must be a symbol, ~
                but it is ~x0 instead." pred))
       ;; validate the :FIX input:
       ((unless (symbolp fix))
        (raise "The :FIX input must be a symbol, ~
                but it is ~x0 instead." fix))
       ;; validate the :EQUIV input:
       ((unless (symbolp equiv))
        (raise "The :EQUIV input must be a symbol, ~
                but it is ~x0 instead." equiv))
       ;; name of the binary predicate:
       (binpred (if signed 'acl2::signed-byte-p 'acl2::unsigned-byte-p))
       ;; package for the generated theorem and variable names:
       (pkg (symbol-package-name type))
       (pkg (if (equal pkg *main-lisp-package-name*) "ACL2" pkg))
       (pkg-witness (pkg-witness pkg))
       ;; names of the generated functions:
       (pred (or pred (acl2::add-suffix-to-fn type "-P")))
       (fix (or fix (acl2::add-suffix-to-fn type "-FIX")))
       (equiv (or equiv (acl2::add-suffix-to-fn type "-EQUIV")))
       ;; names of the generated theorems:
       (booleanp-of-pred (acl2::packn-pos (list 'booleanp-of- pred)
                                          pkg-witness))
       (pred-forward-binpred (acl2::packn-pos (list pred '-forward- binpred)
                                              pkg-witness))
       (binpred-rewrite-pred (acl2::packn-pos (list binpred '-rewrite- pred)
                                              pkg-witness))
       (pred-of-fix (acl2::packn-pos (list pred '-of- fix)
                                     pkg-witness))
       (fix-when-pred (acl2::packn-pos (list fix '-when- pred)
                                       pkg-witness))
       (type-size-is-posp (if size-value
                              nil
                            (acl2::packn-pos (list type '-is-posp)
                                             pkg-witness)))
       ;; variable to use in the generated functions and theorems:
       (x (intern-in-package-of-symbol "X" pkg-witness))
       ;; reference to the fixtype for the generated XDOC documentation:
       (type-ref (concatenate 'string
                              "@(tsee "
                              (acl2::string-downcase (symbol-package-name type))
                              "::"
                              (acl2::string-downcase (symbol-name type))
                              ")"))
       ;; generated events:
       (type-size-is-posp-event?
        (and type-size-is-posp
             `((defrule ,type-size-is-posp
                 (posp ,size)
                 :rule-classes (:rewrite :type-prescription)))))
       (pred-event
        `(define ,pred (,x)
           :parents (,type)
           :short ,(concatenate 'string "Recognizer for " type-ref ".")
           (,binpred ,size ,x)
           :no-function t
           ///
           (defrule ,booleanp-of-pred
             (booleanp (,pred ,x))
             :in-theory '(,pred
                          (:t ,binpred)
                          acl2::booleanp-compound-recognizer))
           (defrule ,pred-forward-binpred
             (implies (,pred ,x)
                      (,binpred ,size ,x))
             :rule-classes :forward-chaining
             :in-theory '(,pred))
           (defruled ,binpred-rewrite-pred
             (equal (,binpred ,size ,x)
                    (,pred ,x))
             :in-theory '(,pred))
           (theory-invariant
            (incompatible (:rewrite ,binpred-rewrite-pred)
                          (:definition ,pred)))))
       (fix-event
        `(define ,fix ((,x ,pred))
           :parents (,type)
           :short ,(concatenate 'string "Fixer for " type-ref ".")
           (mbe :logic (if (,pred ,x) ,x 0)
                :exec ,x)
           :no-function t
           ///
           (defrule ,pred-of-fix
             (,pred (,fix ,x))
             :in-theory '(,pred ,fix ,binpred
                                posp integer-range-p expt (:e expt) fix zip)
             ,@(and type-size-is-posp
                    `(:use (,type-size-is-posp
                            (:instance defbyte-fix-support-lemma (z ,size))))))
           (defrule ,fix-when-pred
             (implies (,pred ,x)
                      (equal (,fix ,x) ,x))
             :in-theory '(,fix))))
       (type-event
        `(defsection ,type
           ,@(and parents (list :parents parents))
           ,@(and short (list :short short))
           ,@(and long (list :long long))
           (fty::deffixtype ,type
             :pred ,pred
             :fix ,fix
             :equiv ,equiv
             :define t
             :forward t)))
       (table-event
        `(table ,*defbyte-table-name*
           ',type
           ',(make-defbyte-info :size size :signed signed))))
    ;; top-level event:
    `(encapsulate
       ()
       (logic)
       ,@type-size-is-posp-event?
       (set-default-hints nil)
       (set-override-hints nil)
       ,pred-event
       ,fix-event
       ,type-event
       ,table-event)))

(defsection defbyte-macro-definition
  :short "Definition of the @(tsee defbyte) macro."
  :long "@(def defbyte)"
  (defmacro defbyte (type
                     &key
                     size
                     signed
                     pred
                     fix
                     equiv
                     parents
                     short
                     long)
    `(make-event (defbyte-fn
                   ',type
                   ',size
                   ',signed
                   ',pred
                   ',fix
                   ',equiv
                   ',parents
                   ,short
                   ,long
                   (w state)))))
