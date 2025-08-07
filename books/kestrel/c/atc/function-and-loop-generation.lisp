; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "statement-generation")

(include-book "../language/static-semantics")
(include-book "../language/function-environments")
(include-book "../language/computation-states")

(include-book "kestrel/event-macros/screen-printing" :dir :system)
(include-book "std/system/add-suffix-to-fn-lst" :dir :system)
(include-book "std/system/genvar-dollar" :dir :system)
(include-book "std/system/get-measure-plus" :dir :system)
(include-book "std/system/install-not-normalized-event" :dir :system)
(include-book "std/system/one-way-unify-dollar" :dir :system)
(include-book "std/system/termination-theorem-dollar" :dir :system)
(include-book "std/system/ubody-plus" :dir :system)
(include-book "std/system/uguard-plus" :dir :system)
(include-book "std/typed-alists/keyword-symbol-alistp" :dir :system)
(include-book "std/typed-alists/symbol-symbol-alistp" :dir :system)

(local (include-book "std/system/all-fnnames" :dir :system))
(local (include-book "std/system/all-vars" :dir :system))
(local (include-book "std/system/flatten-ands-in-lit" :dir :system))
(local (include-book "std/system/w" :dir :system))
(local (include-book "std/alists/top" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/lists/true-listp" :dir :system))
(local (include-book "std/typed-lists/atom-listp" :dir :system))
(local (include-book "std/typed-lists/pseudo-term-listp" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (include-book "projects/apply/loop" :dir :system))
(local (in-theory (disable acl2::loop-book-theory)))

(local (in-theory (disable pseudo-event-form-listp)))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; move to a more general library:

(defrulel pseudo-term-list-count-of-pseudo-term-call->args
  (implies (pseudo-term-case term :call)
           (< (pseudo-term-list-count (pseudo-term-call->args term))
              (pseudo-term-count term)))
  :rule-classes :linear)

(defrulel pseudo-term-count-of-pseudo-lambda->body
  (implies (and (not (member-eq (pseudo-term-kind term)
                                '(:null :var :quote)))
                (pseudo-lambda-p (pseudo-term-call->fn term)))
           (< (pseudo-term-count
               (pseudo-lambda->body (pseudo-term-call->fn term)))
              (pseudo-term-count term)))
  :expand ((pseudo-term-count term))
  :rule-classes :linear)

(defrulel doublet-listp-of-cons
  (equal (doublet-listp (cons a b))
         (and (true-listp a)
              (equal (len a) 2)
              (doublet-listp b)))
  :enable (doublet-listp length))

(defruledl iff-consp-when-true-listp
  (implies (true-listp x)
           (iff (consp x)
                x)))

(defruledl symbolp-of-car-of-pseudo-termp
  (implies (and (pseudo-termp term)
                (consp term)
                (not (consp (car term))))
           (symbolp (car term)))
  :enable pseudo-termp)

(defruledl pseudo-term-listp-of-cdr-of-pseudo-termp
  (implies (and (pseudo-termp term)
                (consp term)
                (not (equal (car term) 'quote)))
           (pseudo-term-listp (cdr term)))
  :enable pseudo-termp)

(defrulel symbol-listp-when-keyword-listp
  (implies (keyword-listp x)
           (symbol-listp x))
  :induct t
  :enable keyword-listp)

(defruledl alistp-when-symbol-symbol-alistp
  (implies (symbol-symbol-alistp x)
           (alistp x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-function-and-loop-generation
  :parents (atc-event-and-code-generation)
  :short "Generation of C functions and loops."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-guard-conjunct ((conjunct pseudo-termp)
                                  (prec-tags atc-string-taginfo-alistp)
                                  (prec-objs atc-string-objinfo-alistp))
  :returns (mv (type type-optionp)
               (defobj-pred symbolp)
               (arg symbolp))
  :short "C type and argument derived from a guard conjunct, if any."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to determine the types of the formal parameters of functions
     from the conjuncts used in the guard,
     as explained in the user documentation.")
   (xdoc::p
    "The conjunct must have the form
     @('(recognizer var)') or @('(star (recognizer var))'),
     where @('recognizer') is a recognizer of a C type
     and @('var') is a variable.
     If the recognizer is a known one for integer array types,
     the @(tsee star) wrapper is disallowed,
     and the integer array type is readily determined.
     If the recognizer is a known one for integer types,
     the @(tsee star) wrapper may be present or not,
     and distinguishes between the integer type
     and the pointer type to the integer type.
     Otherwise, there are two possibilities.
     One is that the recognizer is the one of a @(tsee defstruct),
     of the form @('struct-<tag>-p'):
     in this case, the type is the structure type or a pointer type to it,
     depending on the absence or presence of the @(tsee star) wrapper.
     The other possibility is that
     the recognizer is the one of a @(tsee defobject),
     of the form @('object-<name>-p'):
     in this case, the @(tsee star) wrapper is disallowed,
     and the type is the one of the object.
     In this last case,
     we also return the @('object-<name>-p') name;
     in all other cases, this result is @('nil').")
   (xdoc::p
    "If the recognizer does not have any of the above forms,
     we return @('nil') as all results.
     If the argument is not a variable,
     we also return @('nil') as all results.")
   (xdoc::p
    "As explained in the user documentation,
     we also allow the conjuncts to be wrapped with @(tsee mbt).
     To handle these, we preliminarily conditionally unwrap the conjuncts."))
  (b* ((conjunct (b* (((mv mbtp arg) (check-mbt-call conjunct))
                      ((when mbtp) arg))
                   conjunct))
       ((when (or (variablep conjunct)
                  (fquotep conjunct)
                  (flambda-applicationp conjunct)))
        (mv nil nil nil))
       (fn (ffn-symb conjunct))
       (arg (fargn conjunct 1))
       ((mv okp pointerp recog arg)
        (if (eq fn 'star)
            (if (or (variablep arg)
                    (fquotep arg)
                    (flambda-applicationp arg))
                (mv nil nil nil nil)
              (mv t t (ffn-symb arg) (fargn arg 1)))
          (mv t nil fn arg)))
       ((when (not okp)) (mv nil nil nil))
       ((unless (symbolp arg)) (mv nil nil nil))
       ((mv type defobj-pred)
        (b* (((when (eq recog 'scharp)) (mv (type-schar) nil))
             ((when (eq recog 'ucharp)) (mv (type-uchar) nil))
             ((when (eq recog 'sshortp)) (mv (type-sshort) nil))
             ((when (eq recog 'ushortp)) (mv (type-ushort) nil))
             ((when (eq recog 'sintp)) (mv (type-sint) nil))
             ((when (eq recog 'uintp)) (mv (type-uint) nil))
             ((when (eq recog 'slongp)) (mv (type-slong) nil))
             ((when (eq recog 'ulongp)) (mv (type-ulong) nil))
             ((when (eq recog 'sllongp)) (mv (type-sllong) nil))
             ((when (eq recog 'ullongp)) (mv (type-ullong) nil))
             ((when (eq recog 'schar-arrayp)) (mv (type-array (type-schar)
                                                              nil)
                                                  nil))
             ((when (eq recog 'uchar-arrayp)) (mv (type-array (type-uchar)
                                                              nil)
                                                  nil))
             ((when (eq recog 'sshort-arrayp)) (mv (type-array (type-sshort)
                                                               nil)
                                                   nil))
             ((when (eq recog 'ushort-arrayp)) (mv (type-array (type-ushort)
                                                               nil)
                                                   nil))
             ((when (eq recog 'sint-arrayp)) (mv (type-array (type-sint)
                                                             nil)
                                                 nil))
             ((when (eq recog 'uint-arrayp)) (mv (type-array (type-uint)
                                                             nil)
                                                 nil))
             ((when (eq recog 'slong-arrayp)) (mv (type-array (type-slong)
                                                              nil)
                                                  nil))
             ((when (eq recog 'ulong-arrayp)) (mv (type-array (type-ulong)
                                                              nil)
                                                  nil))
             ((when (eq recog 'sllong-arrayp)) (mv (type-array (type-sllong)
                                                               nil)
                                                   nil))
             ((when (eq recog 'ullong-arrayp)) (mv (type-array (type-ullong)
                                                               nil)
                                                   nil))
             ((mv okp struct/object tag/name p) (atc-check-symbol-3part recog))
             ((unless (and okp
                           (equal (symbol-name p) "P")))
              (mv nil nil))
             ((when (equal (symbol-name struct/object) "STRUCT"))
              (b* ((tag (symbol-name tag/name))
                   (info (cdr (assoc-equal tag prec-tags)))
                   ((unless info) (mv nil nil))
                   ((unless (atc-tag-infop info))
                    (raise "Internal error: malformed ATC-TAG-INFO ~x0." info)
                    (mv nil nil))
                   (info (atc-tag-info->defstruct info))
                   ((unless (eq recog (defstruct-info->recognizer info)))
                    (mv nil nil))
                   ((when (and (defstruct-info->flexiblep info)
                               (not pointerp)))
                    (mv nil nil)))
                (mv (type-struct (defstruct-info->tag info)) nil)))
             ((when (equal (symbol-name struct/object) "OBJECT"))
              (b* ((name (symbol-name tag/name))
                   (info (cdr (assoc-equal name prec-objs)))
                   ((unless info) (mv nil nil))
                   ((unless (atc-obj-infop info))
                    (raise "Internal error: malformed ATC-OBJ-INFO ~x0." info)
                    (mv nil nil))
                   (info (atc-obj-info->defobject info))
                   ((unless (eq recog (defobject-info->recognizer info)))
                    (mv nil nil)))
                (mv (defobject-info->type info)
                    (defobject-info->recognizer info)))))
          (mv nil nil)))
       ((unless type) (mv nil nil nil))
       ((when (and pointerp
                   (type-case type :array)))
        (mv nil nil nil))
       (type (if pointerp
                 (type-pointer type)
               type)))
    (mv type defobj-pred arg))
  :guard-hints
  (("Goal" :in-theory (e/d (acl2::true-listp-when-pseudo-term-listp
                            iff-consp-when-true-listp
                            symbolp-of-car-of-pseudo-termp
                            pseudo-term-listp-of-cdr-of-pseudo-termp
                            alistp-when-atc-string-objinfo-alistp-rewrite
                            alistp-when-atc-string-taginfo-alistp-rewrite)
                           ((:e tau-system)))))) ; for speed

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-formal-thm ((fn symbolp)
                            (fn-guard symbolp)
                            (fn-formals symbol-listp)
                            (formal symbolp)
                            (type typep)
                            (defobj-pred symbolp)
                            (prec-tags atc-string-taginfo-alistp)
                            (names-to-avoid symbol-listp)
                            (wrld plist-worldp))
  :returns (mv (event pseudo-event-formp)
               (name symbolp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate the theorem about a formal parameter of a target function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorem asserts that, under the guard, the formal satisfies
     the type recognizer from the shallow embedding (e.g. @(tsee sintp)).
     This property is used in proofs that build on this theorem.")
   (xdoc::p
    "The theorem is proved in the theory that consists of just
     the guard function,
     the @(tsee star) wrapper,
     and the @(tsee defobject) predicate
     if the formal refers to an external object.
     This is because the recognizer predicate is
     either directly in a conjunct in the guard,
     possibly wrapped by @(tsee star),
     or in the definition of the @(tsee defobject) predicate
     that is in a conjunct of the guard."))
  (b* ((name (pack fn '- formal))
       ((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix name nil names-to-avoid wrld))
       (pred (atc-type-to-recognizer type prec-tags))
       (formula `(implies (,fn-guard ,@fn-formals)
                          (,pred ,formal)))
       (hints `(("Goal" :in-theory '(,fn-guard
                                     star
                                     ,@(and defobj-pred
                                            (list defobj-pred))))))
       ((mv event &) (evmac-generate-defthm name
                                            :formula formula
                                            :hints hints
                                            :enable nil)))
    (mv event name names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-typed-formals ((fn symbolp)
                           (fn-guard symbolp)
                           (prec-tags atc-string-taginfo-alistp)
                           (prec-objs atc-string-objinfo-alistp)
                           (names-to-avoid symbol-listp)
                           (wrld plist-worldp))
  :returns (mv erp
               (typed-formals atc-symbol-varinfo-alistp)
               (events pseudo-event-form-listp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Calculate the C types of the formal parameters of a target function."
  :long
  (xdoc::topstring
   (xdoc::p
    "We look for conjuncts from which we derive,
     according to @(tsee atc-check-guard-conjunct),
     types for the formals of @('fn').
     We ensure that there is exactly one such term for each formal.")
   (xdoc::p
    "We also generate theorems about the formals.")
   (xdoc::p
    "If we find types for all the formals,
     we return an alist from the formals to their variable information.
     The alist has unique keys, in the order of the formals.")
   (xdoc::p
    "We first extract the guard's conjuncts,
     then we go through the conjuncts, looking for the pattern,
     and we extend an alist from formals to types as we find patterns;
     this preliminary alist may not have the keys in order,
     because it goes according to the order of the guard's conjuncts.
     As we construct this preliminary alist,
     we check for multiple terms for the same formal,
     rejecting them even if they are identical.
     Then we construct the final alist by going through the formals in order,
     and looking up their types in the preliminary alist;
     here we detect when a formal has no corresponding conjunct in the guard.")
   (xdoc::p
    "We also consult the @(tsee defobject) alist
     to set the @('externalp') flag of the information about the formal."))
  (b* (((reterr) nil nil nil)
       (formals (formals+ fn wrld))
       (guard (uguard+ fn wrld))
       (guard-conjuncts (flatten-ands-in-lit guard))
       ((erp prelim-alist events names-to-avoid)
        (atc-typed-formals-prelim-alist fn
                                        fn-guard
                                        formals
                                        guard
                                        guard-conjuncts
                                        prec-tags
                                        prec-objs
                                        names-to-avoid
                                        wrld))
       ((erp typed-formals)
        (atc-typed-formals-final-alist fn formals guard prelim-alist wrld)))
    (retok typed-formals events names-to-avoid))

  :prepwork

  ((local (in-theory (enable acons)))

   (define atc-typed-formals-prelim-alist ((fn symbolp)
                                           (fn-guard symbolp)
                                           (formals symbol-listp)
                                           (guard pseudo-termp)
                                           (guard-conjuncts pseudo-term-listp)
                                           (prec-tags atc-string-taginfo-alistp)
                                           (prec-objs atc-string-objinfo-alistp)
                                           (names-to-avoid symbol-listp)
                                           (wrld plist-worldp))
     :returns (mv erp
                  (prelim-alist-final atc-symbol-varinfo-alistp)
                  (events pseudo-event-form-listp)
                  (updated-names-to-avoid symbol-listp
                                          :hyp (symbol-listp names-to-avoid)))
     :parents nil
     (b* (((reterr) nil nil nil)
          ((when (endp guard-conjuncts)) (retok nil nil names-to-avoid))
          (conjunct (car guard-conjuncts))
          ((mv type defobj-pred arg) (atc-check-guard-conjunct conjunct
                                                               prec-tags
                                                               prec-objs))
          ((unless type)
           (atc-typed-formals-prelim-alist fn
                                           fn-guard
                                           formals
                                           guard
                                           (cdr guard-conjuncts)
                                           prec-tags
                                           prec-objs
                                           names-to-avoid
                                           wrld))
          ((unless (member-eq arg formals))
           (atc-typed-formals-prelim-alist fn
                                           fn-guard
                                           formals
                                           guard
                                           (cdr guard-conjuncts)
                                           prec-tags
                                           prec-objs
                                           names-to-avoid
                                           wrld))
          ((erp prelim-alist events names-to-avoid)
           (atc-typed-formals-prelim-alist fn
                                           fn-guard
                                           formals
                                           guard
                                           (cdr guard-conjuncts)
                                           prec-tags
                                           prec-objs
                                           names-to-avoid
                                           wrld))
          ((when (consp (assoc-eq arg prelim-alist)))
           (reterr (msg "The guard ~x0 of the target function ~x1 ~
                         includes multiple type predicates ~
                         for the formal parameter ~x2. ~
                         This is disallowed: every formal parameter ~
                         must have exactly one type predicate in the guard, ~
                         even when the multiple predicates are the same."
                        guard fn arg)))
          ((mv event name names-to-avoid)
           (atc-gen-formal-thm fn fn-guard formals arg type defobj-pred
                               prec-tags names-to-avoid wrld))
          (events (cons event events))
          (externalp
           (b* ((info? (cdr (assoc-equal (symbol-name arg) prec-objs))))
             (and info? t)))
          (info (make-atc-var-info :type type :thm name :externalp externalp))
          (prelim-alist (acons arg info prelim-alist)))
       (retok prelim-alist events names-to-avoid))
     :prepwork ((local (in-theory (enable acons))))
     :verify-guards nil ; done below
     ///
     (verify-guards atc-typed-formals-prelim-alist
       :hints
       (("Goal"
         :in-theory (enable alistp-when-atc-symbol-varinfo-alistp-rewrite)))))

   (define atc-typed-formals-final-alist ((fn symbolp)
                                          (formals symbol-listp)
                                          (guard pseudo-termp)
                                          (prelim-alist atc-symbol-varinfo-alistp)
                                          (wrld plist-worldp))
     :returns (mv erp
                  (typed-formals atc-symbol-varinfo-alistp))
     :parents nil
     (b* (((reterr) nil)
          ((when (endp formals)) (retok nil))
          (formal (car formals))
          (formal (mbe :logic (symbol-fix formal) :exec formal))
          (formal+info (assoc-eq formal
                                 (atc-symbol-varinfo-alist-fix prelim-alist)))
          ((when (not (consp formal+info)))
           (reterr (msg "The guard ~x0 of the target function ~x1 ~
                         has no type predicate for the formal parameter ~x2. ~
                         Every formal parameter must have a type predicate."
                        guard fn formal)))
          (info (cdr formal+info))
          ((erp typed-formals) (atc-typed-formals-final-alist fn
                                                              (cdr formals)
                                                              guard
                                                              prelim-alist
                                                              wrld)))
       (retok (acons formal info typed-formals)))
     :verify-guards :after-returns)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-param-declon-list ((typed-formals atc-symbol-varinfo-alistp)
                                   (fn symbolp)
                                   (prec-objs atc-string-objinfo-alistp))
  :returns (mv erp
               (params param-declon-listp))
  :short "Generate a list of C parameter declarations
          from a list of ACL2 formal parameters."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ACL2 formal parameters are actually passed as an alist,
     from the formals to their information,
     as calculated by @(tsee atc-typed-formals).")
   (xdoc::p
    "We check that the name of each parameter is a portable C identifier,
     and distinct from the names of the other parameters.")
   (xdoc::p
    "If a parameter represents an access to an external object,
     we skip it, i.e. we do not generate a declaration for it."))
  (b* (((reterr) nil)
       ((when (endp typed-formals)) (retok nil))
       ((cons formal info) (car typed-formals))
       (type (atc-var-info->type info))
       (name (symbol-name formal))
       ((unless (paident-stringp name))
        (reterr
         (msg "The symbol name ~s0 of ~
               the formal parameter ~x1 of the function ~x2 ~
               must be a portable ASCII C identifier, but it is not."
              name formal fn)))
       (cdr-formals (strip-cars (cdr typed-formals)))
       ((when (member-equal name (symbol-name-lst cdr-formals)))
        (reterr
         (msg "The formal parameter ~x0 of the function ~x1 ~
               has the same symbol name as ~
               another formal parameter among ~x2; ~
               this is disallowed, even if the package names differ."
              formal fn cdr-formals)))
       ((when (b* ((info (cdr (assoc-equal (symbol-name formal) prec-objs)))
                   ((unless info) nil)
                   ((unless (atc-obj-infop info))
                    (raise "Internal error: ~
                            malformed ATC-OBJ-INFO ~x0."
                           info))
                   (info (atc-obj-info->defobject info)))
                (eq (defobject-info->name-symbol info) formal)))
        (atc-gen-param-declon-list (cdr typed-formals) fn prec-objs))
       ((mv tyspec declor) (ident+type-to-tyspec+declor (make-ident :name name)
                                                        type))
       (param (make-param-declon :tyspec tyspec
                                 :declor declor))
       ((erp params)
        (atc-gen-param-declon-list (cdr typed-formals) fn prec-objs)))
    (retok (cons param params)))
  :prepwork ((local
              (in-theory
               (enable
                symbol-listp-of-strip-cars-when-atc-symbol-varinfo-alistp
                alistp-when-atc-string-objinfo-alistp-rewrite)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-fn-guard ((fn symbolp)
                          (names-to-avoid symbol-listp)
                          state)
  :returns (mv (local-event pseudo-event-formp)
               (name symbolp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate a local function for the guard of @('fn')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used only in theorems,
     so there is no need to guard-verify it."))
  (b* ((wrld (w state))
       (name (pack fn "-GUARD"))
       ((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix name
                                           'function
                                           names-to-avoid
                                           wrld))
       (guard (uguard+ fn wrld))
       ((mv event &)
        (evmac-generate-defun name
                              :formals (formals+ fn wrld)
                              :body (untranslate$ guard t state)
                              :verify-guards nil
                              :enable nil)))
    (mv event name names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-fn-def* ((fn symbolp)
                         (names-to-avoid symbol-listp)
                         (wrld plist-worldp))
  :returns (mv (events pseudo-event-form-listp)
               (name symbolp)
               (names-to-avoid symbol-listp :hyp (symbol-listp names-to-avoid)))
  :short "Generate a local theorem that defines @('fn') using @(tsee if*)."
  :long
  (xdoc::topstring
   (xdoc::p
    "In order to have more control on case splitting,
     in our new modular proof generation approach,
     we use @(tsee if*) instead of @(tsee if).
     The target functions use @(tsee if) of course,
     so we need to convert their definitions to use @(tsee if*).
     We do so by generating, for each target function,
     a rule that expands it to its body
     but with @(tsee if) replaced with @(tsee if*)."))
  (b* (((mv event-def fn-def names-to-avoid)
        (install-not-normalized-event fn t names-to-avoid wrld))
       (fn-def* (pack fn "-DEF*"))
       ((mv fn-def* names-to-avoid)
        (fresh-logical-name-with-$s-suffix fn-def* nil names-to-avoid wrld))
       (body (ubody+ fn wrld))
       (body* (fty-if-to-if* body))
       (formula `(equal (,fn ,@(formals+ fn wrld))
                        ,body*))
       (hints `(("Goal" :in-theory '(,fn-def if*))))
       ((mv event-def* &) (evmac-generate-defthm fn-def*
                                                 :formula formula
                                                 :hints hints
                                                 :enable nil)))
    (mv (list event-def event-def*)
        fn-def*
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-cfun-fun-env-thm-name ((fn symbolp)
                                       (names-to-avoid symbol-listp)
                                       (wrld plist-worldp))
  :returns (mv (name symbolp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate the name of the theorem saying that
          looking up a certain C function in the function environment
          yields the information for that function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The actual theorem is generated in @(tsee atc-gen-cfun-fun-env-thm).
     We separate out the generation of the theorem name
     because we need to use it in events that are computed
     before the actual theorem can be computed
     (see @(tsee atc-gen-fundef))."))
  (fresh-logical-name-with-$s-suffix (add-suffix-to-fn fn "-FUN-ENV")
                                     nil
                                     names-to-avoid
                                     wrld))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-cfun-fun-env-thm ((fn symbolp)
                                  (thm-name symbolp)
                                  (prog-const symbolp)
                                  (finfo fun-infop)
                                  (init-fun-env-thm symbolp))
  :returns (event pseudo-event-formp)
  :short "Generate the theorem saying that
          looking up a certain C function in the function environment
          yields the information for that function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This serves to speed up the proofs
     when there is a large number of functions involved.
     A previous version of ATC was generating proofs
     that were executing function lookups,
     which worked fine for small C programs,
     but was slow for larger C programs."))
  (b* ((fn-name (symbol-name fn))
       (formula `(equal (fun-env-lookup (ident ,fn-name)
                                        (init-fun-env (preprocess ,prog-const)))
                        ',finfo))
       (hints `(("Goal" :in-theory '((:e fun-env-lookup)
                                     (:e ident)
                                     ,init-fun-env-thm))))
       ((mv event &)
        (evmac-generate-defthm thm-name
                               :formula formula
                               :hints hints
                               :enable nil)))
    event))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-fn-result-thm ((fn symbolp)
                               (type? type-optionp)
                               (affect symbol-listp)
                               (typed-formals atc-symbol-varinfo-alistp)
                               (prec-fns atc-symbol-fninfo-alistp)
                               (prec-tags atc-string-taginfo-alistp)
                               (prec-objs atc-string-objinfo-alistp)
                               (names-to-avoid symbol-listp)
                               state)
  :guard (not (eq fn 'quote))
  :returns (mv (events pseudo-event-form-listp)
               (name symbolp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate the theorem about the result(s) of @('fn')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a local theorem for now.")
   (xdoc::p
    "The restrictions on the form of the functions that ATC translates to C
     ensures that, under the guard, these functions always return C values.
     This is fairly easy to see,
     thinking of the different allowed forms of these functions' bodies:")
   (xdoc::ul
    (xdoc::li
     "A formal parameter is constrained to be a C value by the guard.")
    (xdoc::li
     "Calls of @(tsee sint-dec-const), @(tsee add-sint-sint), etc.
      are known to return C values.")
    (xdoc::li
     "Calls of array and structure readers and writers
      are known to return C values.")
    (xdoc::li
     "A @(tsee let) or @(tsee mv-let) variable is equal to a term that,
      recursively, always returns a C value.")
    (xdoc::li
     "A call of a preceding function returns (a) C value(s),
      as proved by the same theorems for the preceding functions.")
    (xdoc::li
     "An @(tsee if) returns the same as its branches,
      when the test is not @(tsee mbt).")
    (xdoc::li
     "An @(tsee if) return the same as its `then' branch,
      when the test is @(tsee mbt),
      because the guard excludes the `else' branch from consideration.")
    (xdoc::li
     "An @(tsee mv) returns C values,
      because either they are parameters or bound variables,
      or they are terms that recursively return C values
      (the latter case is for non-recursive functions
      that return a non-@('void') result
      and also affect arrays and structures)."))
   (xdoc::p
    "This suggests a coarse but adequate proof strategy:
     We use the theory consisting of
     the definition of @('fn'),
     the return type theorems of @(tsee sint-dec-const) and related functions,
     the return type theorems for array and structure readers and writers,
     and the theorems about the preceding functions.
     We also include the definitions of the recognizers
     of the external objects that precede @('fn'),
     which certainly include any external object used in @('fn'):
     this is needed if @('fn') returns the external object,
     because the guard uses its recognizer,
     which implies but differs from a type predicate.
     We also add a @(':use') hint for the guard theorem of @('fn').
     The theorems about structure readers and writers
     are taken from the alist of the preceding structure tags.")
   (xdoc::p
    "In the absence of @(tsee mbt),
     we would not need all of the guard as hypothesis,
     but only the part that constrains the formal parameters to be C values.
     These hypotheses are needed when the function returns them;
     when instead the function returns a representation of some operation,
     e.g. a call of @(tsee sint-dec-const) or @(tsee add-sint-sint),
     these return C values unconditionally, so no hypotheses are needed.
     This is because ATC, when generating C code,
     ensures that the ACL2 terms follow the C typing rules,
     whether the terms are reachable under the guards or not.
     However, in the presence of @(tsee mbt),
     we need the guard to exclude the `else' branches,
     which are otherwise unconstrained.")
   (xdoc::p
    "As explained in the user documentation,
     an ACL2 function may return a combination of
     an optional C result
     and zero or more affected variables or arrays or structures.
     We collect all of them.
     The C result is determined from the optional C type of the function,
     which is @('nil') for recursive functions,
     and may or may not be @('void') for non-recursive functions.
     The affected variables are also considered as results.
     We concatenate zero or one types from @('type?')
     with zero or more types from @('affect') and @('typed-formals').
     More precisely, we make an alist instead of a list,
     whose values are the types in question
     and whose keys are @('nil') for the C result (if present)
     and the names in @('affect') for the other ones.
     Then we operate on the resulting alist,
     which forms all the results of the function
     with their names (and @('nil') for the result, if present).
     The alist is never empty (an ACL2 function must always return something).
     If the alist is a singleton,
     we generate assertions about the function call.
     If the list has multiple elements,
     we generate assertions for the @(tsee mv-nth)s of the function call.")
   (xdoc::p
    "If @('fn') is recursive, we generate a hint to induct on the function.
     Since ACL2 disallows @(':use') and @(':induct') hints on the goal,
     we make the @(':use') hint a computed hint;
     we do that whether @('fn') is recursive or not, for simplicity.")
   (xdoc::p
    "Terms may appear during the proof of this theorem, where
     @(tsee mv-nth)s are applied to @(tsee list)s (i.e. @(tsee cons) nests).
     So we add the rule" (xdoc::@def "mv-nth-of-cons") " to the theory,
     in order to simplify those terms.
     We also enable the executable counterpart of @(tsee zp)
     to simplify the test in the right-hand side of that rule.")
   (xdoc::p
    "For each result of the function,
     we always generate an assertion about its C type.")
   (xdoc::p
    "We also generate assertions saying that the results are not @('nil').
     Without this, some proofs fail with a subgoal saying that
     a function result is @('nil'), which is false.
     This seems to happen only with functions returning multiple results,
     where the results in question have the form @('(mv-nth ...)').
     So we generate these non-@('nil') theorems only for multiple results.
     These theorems have to be rewrite rules:
     with type prescription rules,
     the example theorems mentioned above still fail.
     To prove these non-@('nil') theorems,
     it seems sufficient to enable
     the executable counterparts of the type recognizers;
     the subgoals that arise without them have the form
     @('(<recognizer> nil)').")
   (xdoc::p
    "We also generate assertions saying that
     each array returned by the function
     has the same length as the corresponding input array.
     This is necessary for the correctness proofs of
     functions that call this function."))
  (b* ((wrld (w state))
       (results1 (and type?
                      (not (type-case type? :void))
                      (list (cons nil type?))))
       (results2 (atc-gen-fn-result-thm-aux1 affect typed-formals))
       (results (append results1 results2))
       ((unless (consp results))
        (raise "Internal error: the function ~x0 has no results." fn)
        (mv nil nil names-to-avoid))
       (formals (formals+ fn wrld))
       (fn-call `(,fn ,@formals))
       (conjuncts (atc-gen-fn-result-thm-aux2 results
                                              (if (consp (cdr results))
                                                  0
                                                nil)
                                              fn-call
                                              prec-tags))
       (conclusion
        (if (and (consp conjuncts)
                 (not (consp (cdr conjuncts))))
            (car conjuncts)
          `(and ,@conjuncts)))
       (name (add-suffix-to-fn fn
                               (if (consp (cdr results))
                                   "-RESULTS"
                                 "-RESULT")))
       ((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix name nil names-to-avoid wrld))
       (guard (untranslate$ (uguard+ fn wrld) t state))
       (formula `(implies ,guard ,conclusion))
       (hints `(("Goal"
                 ,@(and (irecursivep+ fn wrld)
                        `(:induct ,fn-call))
                 :in-theory
                 (append
                  *atc-integer-ops-1-return-rewrite-rules*
                  *atc-integer-ops-2-return-rewrite-rules*
                  *atc-integer-convs-return-rewrite-rules*
                  *atc-array-read-return-rewrite-rules*
                  *atc-array-write-return-rewrite-rules*
                  *atc-integer-ops-1-type-prescription-rules*
                  *atc-integer-ops-2-type-prescription-rules*
                  *atc-integer-convs-type-prescription-rules*
                  *atc-array-read-type-prescription-rules*
                  *atc-array-write-type-prescription-rules*
                  *atc-pointed-integers-type-prescription-rules*
                  *atc-array-length-write-rules*
                  *atc-wrapper-rules*
                  '((:e tau-system)
                    ,fn
                    ,@(atc-symbol-fninfo-alist-to-result-thms
                       prec-fns (all-fnnames (ubody+ fn wrld)))
                    ,@(atc-string-taginfo-alist-to-reader-return-thms prec-tags)
                    ,@(atc-string-taginfo-alist-to-writer-return-thms prec-tags)
                    ,@(atc-string-objinfo-alist-to-recognizers prec-objs)
                    sintp-of-sint-dec-const
                    sintp-of-sint-oct-const
                    sintp-of-sint-hex-const
                    uintp-of-uint-dec-const
                    uintp-of-uint-oct-const
                    uintp-of-uint-hex-const
                    slongp-of-slong-dec-const
                    slongp-of-slong-oct-const
                    slongp-of-slong-hex-const
                    ulongp-of-ulong-dec-const
                    ulongp-of-ulong-oct-const
                    ulongp-of-ulong-hex-const
                    sllongp-of-sllong-dec-const
                    sllongp-of-sllong-oct-const
                    sllongp-of-sllong-hex-const
                    ullongp-of-ullong-dec-const
                    ullongp-of-ullong-oct-const
                    ullongp-of-ullong-hex-const
                    scharp-of-schar-read
                    ucharp-of-uchar-read
                    sshortp-of-sshort-read
                    ushortp-of-ushort-read
                    sintp-of-sint-read
                    uintp-of-uint-read
                    slongp-of-slong-read
                    ulongp-of-ulong-read
                    sllongp-of-sllong-read
                    ullongp-of-ullong-read
                    scharp-of-schar-write
                    ucharp-of-uchar-write
                    sshortp-of-sshort-write
                    ushortp-of-ushort-write
                    sintp-of-sint-write
                    uintp-of-uint-write
                    slongp-of-slong-write
                    ulongp-of-ulong-write
                    sllongp-of-sllong-write
                    ullongp-of-ullong-write
                    (:t sint-dec-const)
                    (:t sint-oct-const)
                    (:t sint-hex-const)
                    (:t uint-dec-const)
                    (:t uint-oct-const)
                    (:t uint-hex-const)
                    (:t slong-dec-const)
                    (:t slong-oct-const)
                    (:t slong-hex-const)
                    (:t ulong-dec-const)
                    (:t ulong-oct-const)
                    (:t ulong-hex-const)
                    (:t sllong-dec-const)
                    (:t sllong-oct-const)
                    (:t sllong-hex-const)
                    (:t ullong-dec-const)
                    (:t ullong-oct-const)
                    (:t ullong-hex-const)
                    ,@(loop$ for reader
                             in (atc-string-taginfo-alist-to-readers prec-tags)
                             collect `(:t ,reader))
                    ,@(loop$ for writer
                             in (atc-string-taginfo-alist-to-writers prec-tags)
                             collect `(:t ,writer))
                    sintp-of-sint-from-boolean
                    mv-nth-of-cons
                    (:e zp)
                    (:e ucharp)
                    (:e scharp)
                    (:e ushortp)
                    (:e sshortp)
                    (:e uintp)
                    (:e sintp)
                    (:e ulongp)
                    (:e slongp)
                    (:e ullongp)
                    (:e sllongp)
                    (:e uchar-arrayp)
                    (:e schar-arrayp)
                    (:e ushort-arrayp)
                    (:e sshort-arrayp)
                    (:e uint-arrayp)
                    (:e sint-arrayp)
                    (:e ulong-arrayp)
                    (:e slong-arrayp)
                    (:e ullong-arrayp)
                    (:e sllong-arrayp)
                    ,@(loop$ for recog
                             in (atc-string-taginfo-alist-to-recognizers
                                 prec-tags)
                             collect `(:e ,recog)))))
                '(:use (:guard-theorem ,fn))))
       ((mv event &) (evmac-generate-defthm name
                                            :formula formula
                                            :hints hints
                                            :enable nil)))
    (mv (list event) name names-to-avoid))

  :prepwork

  ((define atc-gen-fn-result-thm-aux1 ((affect symbol-listp)
                                       (typed-formals atc-symbol-varinfo-alistp))
     :returns (results symbol-type-alistp :hyp (symbol-listp affect))
     :parents nil
     (cond ((endp affect) nil)
           (t (b* ((info (cdr (assoc-eq (car affect)
                                        typed-formals))))
                (if (atc-var-infop info)
                    (acons (car affect)
                           (atc-var-info->type info)
                           (atc-gen-fn-result-thm-aux1 (cdr affect)
                                                       typed-formals))
                  (raise "Internal error: variable ~x0 not found in ~x1."
                         (car affect) typed-formals)))))
     :verify-guards :after-returns
     :prepwork
     ((local
       (in-theory (enable alistp-when-atc-symbol-varinfo-alistp-rewrite
                          alistp-when-symbol-type-alistp-rewrite
                          acons)))))

   (define atc-gen-fn-result-thm-aux2 ((results symbol-type-alistp)
                                       (index? maybe-natp)
                                       (fn-call pseudo-termp)
                                       (prec-tags atc-string-taginfo-alistp))
     :returns conjuncts
     :parents nil
     (b* (((when (endp results)) nil)
          (theresult (if index?
                         `(mv-nth ,index? ,fn-call)
                       fn-call))
          ((cons name type) (car results))
          (type-conjunct `(,(atc-type-to-recognizer type prec-tags) ,theresult))
          (nonnil-conjunct? (and index? (list theresult)))
          (arraylength-conjunct?
           (b* (((unless (type-case type :array)) nil)
                (elemtype (type-array->of type))
                ((unless (type-nonchar-integerp elemtype)) nil)
                (elemtype-array-length (pack (integer-type-to-fixtype elemtype)
                                            '-array-length)))
             (list `(equal (,elemtype-array-length ,theresult)
                           (,elemtype-array-length ,name))))))
       (append (list type-conjunct)
               nonnil-conjunct?
               arraylength-conjunct?
               (atc-gen-fn-result-thm-aux2 (cdr results)
                                           (and index? (1+ index?))
                                           fn-call
                                           prec-tags))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-outer-bindings-and-hyps ((typed-formals atc-symbol-varinfo-alistp)
                                         (compst-var symbolp)
                                         (fn-recursivep booleanp)
                                         (prec-objs atc-string-objinfo-alistp))
  :returns (mv (bindings doublet-listp)
               (hyps true-listp)
               (subst symbol-symbol-alistp
                      :hyp (atc-symbol-varinfo-alistp typed-formals))
               (instantiation symbol-pseudoterm-alistp
                              :hyp (and (atc-symbol-varinfo-alistp typed-formals)
                                        (symbolp compst-var))))
  :short "Generate the outer bindings,
          pointer hypotheses,
          pointer substitutions,
          and lemma instantiation,
          for a correctness theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "Both C functions and C loops have correctness theorems of the form
     @('(b* (<bindings>) ...)').
     Here we generate the @('<bindings>'),
     which we designate as `outer' since they are
     at the outermost level of the theorem's formula.
     We also generate some of the hypotheses
     used in the correctness theorems
     that relate to the bindings,
     explained below.
     We also generate a variable substitution, explained below.
     We also generate an instantiation
     for lemmas used in the hints of generated theorems;
     the instantiation is in alist form,
     so that we can use a readily available stronger type for it.")
   (xdoc::p
    "The (outer) bindings can be determined from
     the formals of the ACL2 function @('fn') that represents
     the C function or C loop.
     The bindings differ between C functions and loops,
     but there is also commonality,
     which justifies having this one ACL2 code generation function
     that handles both cases.")
   (xdoc::p
    "Consider a non-recursive @('fn'), which represents a C function.
     Its correctness theorem equates (roughly speaking)
     a call of @(tsee exec-fun) with a call of @('fn').
     However, while @('fn') takes arrays and structures in the heap
     as arguments,
     @(tsee exec-fun) takes pointers to those arrays and structures
     as arguments.
     So we introduce variables for the pointers,
     named after the formals of @('fn') that are arrays or structures:
     we add @('-PTR') to the formals of @('fn'),
     which should not cause name conflicts because
     the names of the formals must be portable C identifiers.
     For each array or structure formal @('a') of @('fn'),
     we generate a pointer variable @('a-ptr') as explained,
     along with a binding
     @('(a (read-object (value-pointer->designator a-ptr) compst))'):
     this binding relates the two variables,
     and lets us use the guard of @('fn') as hypothesis in the theorem,
     which uses @('a'),
     which the binding replaces with the array or structure
     pointed to by @('a-ptr').
     Along with this binding, we also generate hypotheses saying that
     @('a-ptr') is a top-level pointer of the appropriate type;
     the type is determined from the type of the formal @('a').
     Along with the binding and the hypotheses,
     we also generate an alist element @('(a . a-ptr)'),
     returned as part of the @('subst') result,
     that is used to generate the argument list of @(tsee exec-fun),
     by applying the substitution @('subst') to the formals of @('fn'):
     this way, @('a') gets substituted with @('a-ptr'),
     which is what we want since @(tsee exec-fun) takes pointers, not arrays.
     The substitution is also used to calculate the final computation state,
     in @(tsee atc-gen-cfun-final-compustate).")
   (xdoc::p
    "The treatment of arrays that are external objects is different.
     Similarly to heap arrays,
     @('fn') takes the whole external arrays as arguments.
     But @(tsee exec-fun) takes nothing for these as arguments:
     those arrays are found in the static storage of the computation state.
     We still need to generate a binding that relates
     the variables passed to @('fn') that contain these arrays
     to the computation state:
     we do it via bindings of the form
     @('((a (read-static-var (ident ...) compst)))'),
     which we generate here.
     We generate no hypotheses in this case:
     we do not introduce a pointer variable,
     so there is no need for hypotheses about it;
     the pointer is generated internally during symbolic execution,
     with an object designator for the variable in static storage.
     We generate no pointer substitution in this case:
     again, there is no pointer variable introduced here.
     Finally, we generate an instantiation pair consisting of
     the formal and the @('(read-static-var (ident ...) compst)') call.")
   (xdoc::p
    "For a non-array that is an external object,
     the situation is similar to the external object array case,
     but we do not introduce any pointer variable.")
   (xdoc::p
    "The non-array non-structure formals of a non-recursive @('fn')
     do not cause any bindings, hypotheses, or substitutions to be generated.
     They are passed to both @(tsee exec-fun) and @('fn') in the theorem,
     and it is the guard of @('fn') that constrains them
     in the hypotheses of the theorem.")
   (xdoc::p
    "The treatment of a recursive @('fn') is a bit more complicated.
     The correctness theorem for the loop represented by @('fn')
     equates (roughly speaking)
     a call of @(tsee exec-stmt) with a call of @('fn').
     However, @(tsee exec-stmt) is called on a computation state,
     not on anything that corresponds to the formals of @('fn'),
     as is the case for a non-recursive @('fn') as explained above.
     There is still a correspondence, of course:
     the formals of @('fn') correspond to variables in the computation state.
     We consider separately
     the case of arrays or structures in the heap,
     the case of arrays in static storage,
     and the case of non-arrays and non-structures.")
   (xdoc::p
    "If @('a') is a non-array non-structure formal of a recursive @('fn'),
     it corresponds to @('(read-var <a> compst)'),
     where @('<a>') is the identifier derived from the name of @('a').
     Thus, in this case we generate the binding @('(a (read-var <a> compst))').
     Since no pointers are involved, in this case we generate
     no hypotheses and no substitutions;
     we generate an instantiation that instantiates
     the formal with @('(read-var <a> compst)').")
   (xdoc::p
    "If @('a') is a heap array or structure formal of a recursive @('fn'),
     we introduce an additional @('a-ptr') variable,
     similarly to the case of non-recursive @('fn').
     We generate two bindings @('(a-ptr (read-var <a> compst))')
     and @('(a (read-object (value-pointer->designator a-ptr) compst))'),
     in that order.
     The first binding serves to tie @('a-ptr')
     to the corresponding variable in the computation state,
     which has the name of @('a'), but it holds a pointer.
     The second binding is analogous in purpose
     to the case of a non-recursive @('fn') explained above:
     it lets us use the guard of @('fn'), which references @('a'),
     in the hypotheses of the generated theorem
     without having to make an explicit substitution,
     because the bindings are in fact doing the substitution.
     It should be clear why the two bindings have to be in that order;
     the bindings are put into a @(tsee b*),
     which enforces the order.
     We generate a substitution of @('a') with @('a-ptr'),
     for use by @(tsee atc-gen-loop-final-compustate)
     (not to calculate the arguments of @(tsee exec-fun),
     because no @(tsee exec-fun) call is involved in the theorem for loops.
     The instantiation combines @(tsee read-var) and @(tsee read-object).")
   (xdoc::p
    "If @('a') is an array in static storage,
     things are more similar to the case in which @('fn') is not recursive.
     The binding is with @(tsee read-static-var), i.e. the same.
     We generate a different hypothesis from all other cases:
     the hypothesis is that the variable is not in automatic storage,
     i.e. that it is found in static storage.
     This is necessary for theorems for C loops,
     because a @(tsee read-var) during execution cannot reach @(tsee add-frame)
     and be turned into @(tsee read-static-var) as done for C functions.
     This hypothesis is relieved in the correctness theorem
     of the non-recursive function that calls the recursive one:
     the symbolic execution for the non-recursive one
     can have @(tsee read-var) reach @(tsee add-frame)
     and turn that into @(tsee read-static-var).
     We generate no substitution, since there are no pointer variables.
     We generate an instantiation that instantiates the formal
     with the @(tsee read-static-var) call.")
   (xdoc::p
    "The reason for generating and using the described bindings in the theorems,
     as opposed to making the substitutions in the theorem's formula,
     is greater readability of the theorems.
     Particularly in the case of loop theorems,
     if @('a') occurs a few times in the guard,
     the guard with just @('a') in those occurrences is more readable than
     if all those occurrences are replaced with @('(read-var <a> compst)').")
   (xdoc::p
    "The lemma instantiation is similar to the bindings,
     but it only concerns the formals of @('fn'), not the @('a-ptr') variables.
     The instantiation is used on the guard and termination theorems of @('fn'),
     and therefore it can only concern the formals of @('fn').")
   (xdoc::p
    "There is an intentional discrepancy between the fact that
     an array pointer points to the whole array
     while the type of the pointer is the array element type.
     The reason is the approximate, but correct in our C subset,
     treatment of arrays and pointers discussed in @(tsee exec-arrsub)."))
  (b* (((when (endp typed-formals)) (mv nil nil nil nil))
       ((cons formal info) (car typed-formals))
       (type (atc-var-info->type info))
       (formal-ptr (add-suffix-to-fn formal "-PTR"))
       (formal-objdes `(value-pointer->designator ,formal-ptr))
       (formal-id `(ident ',(symbol-name formal)))
       (pointerp (or (type-case type :pointer)
                     (type-case type :array)))
       (extobjp (assoc-equal (symbol-name formal) prec-objs))
       (bindings
        (if fn-recursivep
            (if pointerp
                (if extobjp
                    (list `(,formal
                            (read-static-var ,formal-id ,compst-var)))
                  (list `(,formal-ptr
                          (read-var ,formal-id ,compst-var))
                        `(,formal
                          (read-object ,formal-objdes ,compst-var))))
              (if extobjp
                  (list `(,formal
                          (read-static-var ,formal-id ,compst-var)))
                (list `(,formal
                        (read-var ,formal-id ,compst-var)))))
          (if pointerp
              (if extobjp
                  (list `(,formal
                          (read-static-var ,formal-id ,compst-var)))
                (list `(,formal
                        (read-object ,formal-objdes ,compst-var))))
            (if extobjp
                (list `(,formal
                        (read-static-var ,formal-id ,compst-var)))
              nil))))
       (subst (and pointerp
                   (not extobjp)
                   (list (cons formal formal-ptr))))
       (hyps (and pointerp
                  (if extobjp
                      (list `(not (var-autop ,formal-id ,compst-var)))
                    (list `(valuep ,formal-ptr)
                          `(value-case ,formal-ptr :pointer)
                          `(value-pointer-validp ,formal-ptr)
                          `(equal (objdesign-kind
                                   (value-pointer->designator ,formal-ptr))
                                  :alloc)
                          (if (type-case type :pointer)
                              `(equal (value-pointer->reftype ,formal-ptr)
                                      ,(type-to-maker
                                        (type-pointer->to type)))
                            `(equal (value-pointer->reftype ,formal-ptr)
                                    ,(type-to-maker
                                      (type-array->of type))))))))
       (inst (if fn-recursivep
                 (if pointerp
                     (if extobjp
                         (list
                          (cons formal
                                `(read-static-var ,formal-id ,compst-var)))
                       (list
                        (cons formal
                              `(read-object (value-pointer->designator
                                             (read-var ,formal-id ,compst-var))
                                            ,compst-var))))
                   (if extobjp
                       (list (cons formal
                                   `(read-static-var ,formal-id ,compst-var)))
                     (list
                      (cons formal
                            `(read-var ,formal-id ,compst-var)))))
               (if pointerp
                   (if extobjp
                       (list
                        (cons formal
                              `(read-static-var ,formal-id ,compst-var)))
                     (list
                      (cons formal
                            `(read-object ,formal-objdes ,compst-var))))
                 (if extobjp
                     (list (cons formal
                                 `(read-static-var ,formal-id ,compst-var)))
                   nil))))
       ((mv more-bindings more-hyps more-subst more-inst)
        (atc-gen-outer-bindings-and-hyps (cdr typed-formals)
                                         compst-var
                                         fn-recursivep
                                         prec-objs)))
    (mv (append bindings more-bindings)
        (append hyps more-hyps)
        (append subst more-subst)
        (append inst more-inst)))
  :prepwork ((local (in-theory (enable pseudo-termp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-object-disjoint-hyps ((pointer-vars symbol-listp))
  :returns (hyps true-listp)
  :short "Generate hypotheses saying that the pointers
          designate disjoint objects."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ACL2 functions that represent C functions and loops
     take and return whole arrays and structured as inputs:
     thus, the possible modification to each array or structure
     only applies to that array or structure.
     In the generated C code,
     arrays and structures are passed as pointers instead.
     If two of these pointers, for different arrays or structures in ACL2,
     were equal, then the C code would not be correct in general,
     because modifying one array or structure would also modify the other one:
     there is, in fact, just one array or structure,
     which both pointers point to,
     but here we are talking about the two different arrays or structures
     in the ACL2 representation.
     It is thus critical that the generated correctness theorems
     include the assumption that all the pointers are distinct.
     This is the case
     not only for the arrays and structures that may be modified,
     but also for the ones that may not:
     otherwise, we could not rely on the latter to be unmodified,
     during the symbolic execution proof.")
   (xdoc::p
    "We generate these hypotheses here,
     by going through the pointer variables involved in
     the correctness theorem of the C function or loop.
     More precisely, we generate hypotheses saying that
     the object designated by the pointers are pairwise disjoint."))
  (b* (((when (endp pointer-vars)) nil)
       (var (car pointer-vars))
       (hyps (loop$ for var2 in (cdr pointer-vars)
                    collect `(object-disjointp
                              (value-pointer->designator ,var)
                              (value-pointer->designator ,var2))))
       (more-hyps (atc-gen-object-disjoint-hyps (cdr pointer-vars))))
    (append hyps more-hyps))
  :prepwork ((local (in-theory (enable acl2::loop-book-theory)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-filter-exec-fun-args ((formals symbol-listp)
                                  (prec-objs atc-string-objinfo-alistp))
  :returns (args symbol-listp :hyp (symbol-listp formals))
  :short "Filter external objects out of the formals,
          for passing to @(tsee exec-fun)."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the generated correctness theorem for each non-recursive function,
     we generally pass to @(tsee exec-fun)
     an argument for each formal of the function.
     Except for formals that represent external objects:
     those are accessed in the computation state.
     Thus, here we filter, out of a list of formals,
     the ones that represent external objects."))
  (b* (((when (endp formals)) nil)
       (formal (car formals)))
    (if (assoc-equal (symbol-name formal) prec-objs)
        (atc-filter-exec-fun-args (cdr formals) prec-objs)
      (cons formal (atc-filter-exec-fun-args (cdr formals) prec-objs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-cfun-final-compustate ((affect symbol-listp)
                                       (typed-formals atc-symbol-varinfo-alistp)
                                       (subst symbol-symbol-alistp)
                                       (compst-var symbolp)
                                       (prec-objs atc-string-objinfo-alistp))
  :returns (term "An untranslated term.")
  :short "Generate a term representing the final computation state
          after the execution of a C function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The correctness theorem of a C function says that
     executing the function on a generic computation state
     (satisfying conditions in the hypotheses of the theorem)
     and on generic arguments
     yields an optional result (absent if the function is @('void'))
     and a computation state obtained by modifying
     zero or more arrays and structures in the computation state.
     These are the arrays and structures affected by the C function,
     which the correctness theorem binds to the results of
     the ACL2 function that represents the C function.
     The modified computation state is expressed as
     a nest of @(tsee write-object) and @(tsee write-static-var) calls,
     based on whether the affected object are in the heap or in static storage.
     This ACL2 code here generates that nest.")
   (xdoc::p
    "The parameter @('affect') passed to this code
     consists of the formals of @('fn') that represent arrays and structures
     affected by the body of the ACL2 function that represents the C function.
     The parameter @('subst') is
     the result of @(tsee atc-gen-outer-bindings-and-hyps)
     that maps array and structure formals of the ACL2 function
     to the corresponding pointer variables used by the correctness theorems.
     Thus, we go through @('affect'),
     looking up the corresponding pointer variables in @('subst'),
     and we construct
     each nested @(tsee write-object) call,
     which needs both a pointer and an array or structure;
     we distinguish between arrays and structures
     via the types of the formals.
     This is the case for arrays and structures in the heap;
     for arrays in static storage,
     we generate a call of @(tsee write-static-var),
     and there are no pointers involved.")
   (xdoc::p
    "Note that, in the correctness theorem,
     the new array and structure variables are bound to
     the possibly modified arrays and structures returned by the ACL2 function:
     these new array and structure variables are obtained by adding @('-NEW')
     to the corresponding formals of the ACL2 function;
     these new names should not cause any conflicts,
     because the names of the formals must be portable C identifiers."))
  (b* (((when (endp affect)) compst-var)
       (formal (car affect))
       (info (cdr (assoc-eq formal typed-formals)))
       ((when (not info))
        (raise "Internal error: formal ~x0 not found." formal))
       (type (atc-var-info->type info))
       ((unless (or (type-case type :pointer)
                    (type-case type :array)
                    (atc-var-info->externalp info)))
        (raise "Internal error:
                affected formal ~x0 has type ~x1 and is not an external object."
               formal type)))
    (if (consp (assoc-equal (symbol-name formal) prec-objs))
        `(write-static-var (ident ,(symbol-name formal))
                           ,(add-suffix-to-fn formal "-NEW")
                           ,(atc-gen-cfun-final-compustate (cdr affect)
                                                           typed-formals
                                                           subst
                                                           compst-var
                                                           prec-objs))
      `(write-object (value-pointer->designator ,(cdr (assoc-eq formal subst)))
                     ,(add-suffix-to-fn formal "-NEW")
                     ,(atc-gen-cfun-final-compustate (cdr affect)
                                                     typed-formals
                                                     subst
                                                     compst-var
                                                     prec-objs))))
  :prepwork ((local (in-theory (enable alistp-when-symbol-symbol-alistp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-cfun-correct-thm ((fn symbolp)
                                  (typed-formals atc-symbol-varinfo-alistp)
                                  (type typep)
                                  (affect symbol-listp)
                                  (prec-fns atc-symbol-fninfo-alistp)
                                  (prec-tags atc-string-taginfo-alistp)
                                  (prec-objs atc-string-objinfo-alistp)
                                  (prog-const symbolp)
                                  (compst-var symbolp)
                                  (fenv-var symbolp)
                                  (limit-var symbolp)
                                  (fn-thms symbol-symbol-alistp)
                                  (fn-fun-env-thm symbolp)
                                  (limit pseudo-termp)
                                  state)
  :returns (mv (events pseudo-event-form-listp)
               (print-event pseudo-event-formp)
               (name symbolp :hyp (symbol-symbol-alistp fn-thms)))
  :short "Generate the correctness theorem for a C function."
  :long
  (xdoc::topstring
   (xdoc::p
    "In a computation state @('compst'),
     the execution of the C function is expressed by calling @(tsee exec-fun)
     on the name of @('fn'),
     the formals of @('fn'),
     the computation state @('compst'),
     the function environment for the translation unit,
     and a suitably large limit (more on this below).
     In this generated theorem,
     the first result of @(tsee exec-fun) is equated to
     either (i) the first (possibly only) result of
     a call of @('fn') when it represents a non-@('void') C function,
     or (ii) @('nil') when @('fn') represents a @('void') C function.
     The second result of @(tsee exec-fun) is equated to
     the computation state
     calculated by @(tsee atc-gen-cfun-final-compustate).")
   (xdoc::p
    "The function @('fn') returns
     an optional C result and zero or more modified arrays and structures.
     If it returns a C result (i.e. if the C function is not @('void')),
     we bind a result variable to it;
     the value is @('nil') if the C function is @('void').
     We also bind the formals that are arrays or structures
     to the (other or only) results of @('fn') (if any).
     We actually use new variables for the latter,
     for greater clarity in the theorem formulation:
     the new variables are obtained by adding @('-NEW')
     to the corresponding array and structure formals of @('fn');
     these new names should not cause any conflicts,
     because the names of the formals must be portable C identifiers.")
   (xdoc::p
    "The guard of @('fn') is used as hypothesis,
     along with the fact that @('compst') is a computation state.")
   (xdoc::p
    "We use a variable for the function environment,
     which we equate to the translation unit's function environment
     in a hypothesis.
     Note that, when we execute the ACL2 code in this function,
     we do not have the function environment
     of the generated translation unit yet,
     because we generate these correctness theorems
     along with the function definitions that form the translation unit
     (currently we could generate these theorems after the translation unit,
     but we prefer to do them at the same time for easier future extensions,
     in which we may generate ``smaller'' theorems,
     possibly for subterms/subexpressions/substatements).
     Thus, we cannot use a quoted constant for the function environment here.
     The reason why we introduce a variable and equate it in the hypothesis,
     as opposed to using @('(init-fun-env <program>)')
     directly as argument of @(tsee exec-fun),
     is that we want to use this theorem as a rewrite rule,
     and using a variable makes the rule easier to match with,
     in particular since the @(tsee init-fun-env) call gets rewritten
     via the theorem about @(tsee init-fun-env).")
   (xdoc::p
    "The limit passed to @(tsee exec-fun) is a variable,
     which is assumed (in a hypothesis of the generated theorem)
     to be no smaller than a value
     that is calculated by the code generation code
     as sufficient to run @(tsee exec-fun) to completion.")
   (xdoc::p
    "The proof is a symbolic execution of the generated translation unit,
     which is a constant: see @(see atc-symbolic-execution-rules).
     The proof is carried out in the theory that consists of exactly
     the general rules in @(tsee *atc-all-rules*),
     some structure-specific rules that are similar to
     rules for arrays in @(tsee *atc-all-rules*),
     plus the definition of @(tsee not) (more on this below),
     plus the definition of @('fn') (clearly),
     plus the theorems about the results of the functions called by @('fn'),
     plust the type prescriptions of the functions called by @('fn'),
     plus the correctness theorems of the functions called by @('fn'),
     plus the theorems asserting that
     the measures of all the preceding recursive functions are naturals
     (we take all the measures,
     not just the ones of the directly called functions,
     because the limit bound may include a measure
     from an indirectly called function),
     plus the theorem about the current function in the function environment;
     here `called' means `directly called'.
     During symbolic execution, the initial limit for @('fn')
     is progressively decremented,
     so by the time we get to functions called by @('fn')
     it will have different symbolic values from the initial variable;
     thus, we need to match that to the variable @('limit')
     in the correctness theorems for the callees,
     which are used as rewrite rules to turn calls of @(tsee exec-fun)
     into calls of the corresponding ACL2 functions.
     These will thus match the calls in the definition of @('fn'),
     and the called functions can stay disabled in the proof.
     The theorems about the called functions' results
     are needed to exclude, in the proof, the case that
     these functions return errors.
     The type prescriptions of the callable functions
     are needed to discharge some proof subgoal that arise.
     We enable @(tsee not) because, without it,
     we have found at least one case in which some ACL2 heuristic defeats
     what should be a propositional inference;
     the issue is related to clausification,
     and enabling @(tsee not) seems to overcome the issue,
     at least in that case we found.")
   (xdoc::p
    "Furthermore, we generate a @(':use') hint
     to augment the theorem's formula with the guard theorem of @('fn'),
     with the pointer arguments replaced by
     the dereferenced arrays and structures.
     This is critical to ensure that the symbolic execution of the C operators
     does not split on the error cases:
     the fact that @('fn') is guard-verified
     ensures that @(tsee add-sint-sint) and similar functions are always called
     on values such that the exact result fit into the type,
     which is the same condition under which the dynamic semantics
     does not error on the corresponding operators.")
   (xdoc::p
    "We also generate a hint to expand all lambdas (i.e. beta reduction).
     We found at least one instance in which ACL2's heuristics
     were preventing a lambda expansion that was preventing a proof.")
   (xdoc::p
    "Given that we pass correctness theorems for the called functions,
     we expect that the opener rule for @(tsee exec-fun)
     only applies to the call of the function that this theorem refers to,
     because the correctness theorems come later in the ACL2 history
     and thus are tried first.")
   (xdoc::p
    "We use @(tsee b*) bindings in parts of the theorem
     to make certain variable substitution.
     Using bindings results in more readable formulas, in general,
     than generating terms with the substitutions applied,
     particularly if the same substituted variable occurs more than once.
     With the bindings, we let ACL2 perform the substitution at proof time.")
   (xdoc::p
    "If @('fn') has conditional (i.e. @(tsee if)s),
     the C function has corresponding (expression and statement) conditionals.
     During the proof, all these condtionals, in @('fn') and in the C function,
     may cause case splits, which make the proof slow.
     In an attempt to improve speed,
     we perform the symbolic execution execution of the C function
     while keeping @('fn') closed,
     so that @('fn') does not cause case splits during the symbolic execution.
     Then, once we reach stability (see @(tsee stable-under-simplificationp)),
     we open @('fn'), which may cause case splits, and complete the proof.
     The second part of the proof probably does not need
     all the rules from the first part, which for now we use for simplicity;
     so we should be able to use simpler hints there eventually.")
   (xdoc::p
    "This theorem is not generated if @(':proofs') is @('nil')."))
  (b* ((wrld (w state))
       (name (cdr (assoc-eq fn fn-thms)))
       (formals (strip-cars typed-formals))
       (result-var (if (type-case type :void)
                       nil
                     (genvar$ 'atc "RESULT" nil formals state)))
       ((mv formals-bindings hyps subst instantiation)
        (atc-gen-outer-bindings-and-hyps typed-formals
                                         compst-var
                                         nil
                                         prec-objs))
       (diff-pointer-hyps
        (atc-gen-object-disjoint-hyps (strip-cdrs subst)))
       (hyps `(and (compustatep ,compst-var)
                   (equal ,fenv-var
                          (init-fun-env (preprocess ,prog-const)))
                   (integerp ,limit-var)
                   (>= ,limit-var ,limit)
                   ,@hyps
                   ,@diff-pointer-hyps
                   ,(untranslate$ (uguard+ fn wrld) nil state)))
       (exec-fun-args (fsublis-var-lst subst
                                       (atc-filter-exec-fun-args formals
                                                                 prec-objs)))
       (affect-new (acl2::add-suffix-to-fn-lst affect "-NEW"))
       (fn-results (append (if (type-case type :void)
                               nil
                             (list result-var))
                           affect-new))
       (fn-binder (if (endp (cdr fn-results))
                      (car fn-results)
                    `(mv ,@fn-results)))
       (final-compst
        (atc-gen-cfun-final-compustate affect
                                       typed-formals
                                       subst
                                       compst-var
                                       prec-objs))
       (concl `(equal (exec-fun (ident ,(symbol-name fn))
                                (list ,@exec-fun-args)
                                ,compst-var
                                ,fenv-var
                                ,limit-var)
                      (b* ((,fn-binder (,fn ,@formals)))
                        (mv ,result-var ,final-compst))))
       (formula `(b* (,@formals-bindings) (implies ,hyps ,concl)))
       (called-fns (all-fnnames (ubody+ fn wrld)))
       (not-error-thms (atc-string-taginfo-alist-to-not-error-thms prec-tags))
       (valuep-thms (atc-string-taginfo-alist-to-valuep-thms prec-tags))
       (value-kind-thms (atc-string-taginfo-alist-to-value-kind-thms prec-tags))
       (result-thms
        (atc-symbol-fninfo-alist-to-result-thms prec-fns called-fns))
       (struct-reader-return-thms
        (atc-string-taginfo-alist-to-reader-return-thms prec-tags))
       (struct-writer-return-thms
        (atc-string-taginfo-alist-to-writer-return-thms prec-tags))
       (correct-thms
        (atc-symbol-fninfo-alist-to-correct-thms prec-fns called-fns))
       (measure-thms
        (atc-symbol-fninfo-alist-to-measure-nat-thms
         prec-fns (strip-cars prec-fns)))
       (type-prescriptions-called
        (loop$ for called in (strip-cars prec-fns)
               collect `(:t ,called)))
       (type-prescriptions-struct-readers
        (loop$ for reader in (atc-string-taginfo-alist-to-readers prec-tags)
               collect `(:t ,reader)))
       (type-of-value-thms
        (atc-string-taginfo-alist-to-type-of-value-thms prec-tags))
       (flexiblep-thms
        (atc-string-taginfo-alist-to-flexiblep-thms prec-tags))
       (member-read-thms
        (atc-string-taginfo-alist-to-member-read-thms prec-tags))
       (member-write-thms
        (atc-string-taginfo-alist-to-member-write-thms prec-tags))
       (extobj-recognizers (atc-string-objinfo-alist-to-recognizers prec-objs))
       (hints `(("Goal"
                 :in-theory (union-theories
                             (theory 'atc-all-rules)
                             '(not-errorp-when-expr-valuep
                               ,@not-error-thms
                               ,@valuep-thms
                               ,@value-kind-thms
                               not
                               ,@result-thms
                               ,@struct-reader-return-thms
                               ,@struct-writer-return-thms
                               ,@type-of-value-thms
                               ,@flexiblep-thms
                               ,@member-read-thms
                               ,@member-write-thms
                               ,@type-prescriptions-called
                               ,@type-prescriptions-struct-readers
                               ,@extobj-recognizers
                               ,@correct-thms
                               ,@measure-thms
                               ,fn-fun-env-thm))
                 :use (:instance (:guard-theorem ,fn)
                                 :extra-bindings-ok
                                 ,@(alist-to-doublets instantiation))
                 :expand (:lambdas))
                (and stable-under-simplificationp
                     '(:in-theory
                       (union-theories
                        (theory 'atc-all-rules)
                        '(,fn
                          not-errorp-when-expr-valuep
                          ,@not-error-thms
                          ,@valuep-thms
                          ,@value-kind-thms
                          not
                          return-type-of-stmt-value-return
                          return-type-of-stmt-value-none
                          stmt-value-return->value?-of-stmt-value-return
                          value-option-fix-when-value-optionp
                          ,@result-thms
                          ,@struct-reader-return-thms
                          ,@struct-writer-return-thms
                          ,@type-of-value-thms
                          ,@flexiblep-thms
                          ,@member-read-thms
                          ,@member-write-thms
                          ,@type-prescriptions-called
                          ,@type-prescriptions-struct-readers
                          ,@extobj-recognizers
                          ,@correct-thms
                          ,@measure-thms
                          ,fn-fun-env-thm))))))
       ((mv local-event exported-event)
        (evmac-generate-defthm name
                               :formula formula
                               :hints hints
                               :enable nil))
       (print-event `(cw-event "~%~x0~|" ',exported-event)))
    (mv (list local-event
              exported-event)
        print-event
        name))
  :guard-hints
  (("Goal"
    :in-theory
    (enable acl2::symbol-listp-of-strip-cdrs-when-symbol-symbol-alistp
            acl2::symbol-alistp-when-symbol-symbol-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-formal-affectablep ((formal symbolp)
                                (typed-formals atc-symbol-varinfo-alistp))
  :returns (yes/no booleanp)
  :short "Check if a formal parameter is a affectable."
  :long
  (xdoc::topstring
   (xdoc::p
    "By this we mean that the formal parameter
     either has pointer or array type or refers to an external object.
     That is, it is the kind of parameter that may be affected in a function,
     and that therefore must be returned by the function if affected."))
  (b* ((pair (assoc-eq (symbol-fix formal)
                       (atc-symbol-varinfo-alist-fix typed-formals))))
    (and (consp pair)
         (b* ((info (cdr pair))
              (type (atc-var-info->type info)))
           (or (type-case type :pointer)
               (type-case type :array)
               (atc-var-info->externalp info)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist atc-formal-affectable-listp (x typed-formals)
  :guard (and (symbol-listp x)
              (atc-symbol-varinfo-alistp typed-formals))
  :short "Lift @(tsee atc-formal-affectablep) to lists."
  (atc-formal-affectablep x typed-formals)
  :true-listp t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-find-affected ((fn symbolp)
                           (term pseudo-termp)
                           (typed-formals atc-symbol-varinfo-alistp)
                           (prec-fns atc-symbol-fninfo-alistp)
                           (wrld plist-worldp))
  :returns (mv erp
               (affected symbol-listp
                         :hyp (atc-symbol-varinfo-alistp typed-formals)))
  :short "Find the variables affected by a term."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used on the body of each non-recursive target function @('fn'),
     in order to determine the variables affected by it,
     according to the nomenclature in the user documentation.
     We visit the leaves of the term
     according to the @(tsee if) and @(tsee let) structure,
     and ensure that they all have the same form,
     which must be one of the following forms:")
   (xdoc::ul
    (xdoc::li
     "A call of a (recursive or non-recursive) target function @('fn0')
      that precedes @('fn') in the list of targets.
      In this case, @('term') affects the same variables as @('fn0').
      We use @(tsee atc-check-cfun-call) and @(tsee atc-check-loop-call)
      to check if the term is a call of a target function
      and to retrieve that function's affected variables:
      we pass @('nil') as the variable-term alist,
      because it does not change the returned affected variables,
      which is the only thing we care about here,
      ignoring all the other results.")
    (xdoc::li
     "A formal parameter @('var') of @('fn') that
      either has pointer or array type or refers to an external object.
      In this case, @('term') affects the list of variables @('(var)').")
    (xdoc::li
     "A term @('ret') that is not a call of @('fn0') as above
      and is not a formal parameter of @('fn') that
      either has pointer or array type or refers to an external object.
      In this case, @('term') affects no variables.")
    (xdoc::li
     "A term @('(mv var1 ... varn)') where each @('vari') is
      a formal parameter of the function that
      either has pointer or array type or refers to an external object.
      In this case, @('term') affects
      the list of variables @('(var1 ... varn)').")
    (xdoc::li
     "A term @('(mv ret var1 ... varn)') where each @('vari') is
      a formal parameter of the function that
      either has pointer or array type or refers to an external object,
      and @('ret') is not.
      In this case, @('term') affects
      the list of variables @('(var1 ... varn)')."))
   (xdoc::p
    "In checking that the terms at the leaves have the same form,
     we allow @('ret') to vary, but the other parts must coincide.")
   (xdoc::p
    "When we encounter @(tsee if)s with @(tsee mbt) tests,
     we recursively process the `then' branch, skipping the `else' branch.
     This is because only the `then' branch represents C code."))
  (b* (((reterr) nil)
       ((mv okp test then else) (fty-check-if-call term))
       ((when okp)
        (b* (((mv mbtp &) (check-mbt-call test))
             ((when mbtp) (atc-find-affected fn
                                             then
                                             typed-formals
                                             prec-fns
                                             wrld))
             ((erp then-affected) (atc-find-affected fn
                                                     then
                                                     typed-formals
                                                     prec-fns
                                                     wrld))
             ((erp else-affected) (atc-find-affected fn
                                                     else
                                                     typed-formals
                                                     prec-fns
                                                     wrld)))
          (if (equal then-affected else-affected)
              (retok then-affected)
            (reterr
             (msg "When generating code for function ~x0, ~
                   an IF branch affects variables ~x1, ~
                   while the other branch affects variables ~x2: ~
                   this is disallowed."
                  fn then-affected else-affected)))))
       ((mv okp & body &) (fty-check-lambda-call term))
       ((when okp) (atc-find-affected fn
                                      body
                                      typed-formals
                                      prec-fns
                                      wrld))
       ((erp okp & & & & affected & & &)
        (atc-check-cfun-call term nil prec-fns wrld))
       ((when okp) (retok affected))
       ((mv okp & & & affected & &)
        (atc-check-loop-call term nil prec-fns))
       ((when okp) (retok affected))
       ((when (pseudo-term-case term :var))
        (b* ((var (pseudo-term-var->name term)))
          (if (atc-formal-affectablep var typed-formals)
              (retok (list var))
            (retok nil))))
       ((mv okp terms) (fty-check-list-call term))
       ((when okp)
        (cond ((and (symbol-listp terms)
                    (atc-formal-affectable-listp terms typed-formals))
               (retok terms))
              ((and (symbol-listp (cdr terms))
                    (atc-formal-affectable-listp (cdr terms) typed-formals))
               (retok (cdr terms)))
              (t (reterr
                  (msg "When generating code for function ~x0, ~
                        a term ~x1 was encountered that ~
                        returns multiple values but they, ~
                        or at least all of them except the first one, ~
                        are not all formal parameters of ~x0 ~
                        of pointer or array type."
                       fn term))))))
    (retok nil))
  :measure (pseudo-term-count term)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :prepwork
  ((local (in-theory
           (enable symbol-listp-of-strip-cars-when-atc-symbol-varinfo-alistp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-omap-update-formals ((typed-formals atc-symbol-varinfo-alistp))
  :returns (mv (term "An untranslated term.")
               (init-formals symbol-listp
                             :hyp (atc-symbol-varinfo-alistp typed-formals)))
  :short "Generate a term that is an @(tsee omap::update) nest
          for the formals of a function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in the generated theorem that describes
     the initial scope for a function execution.
     It has the form")
   (xdoc::codeblock
    "(omap::update (ident <string>) <symbol> (omap::update ... nil) ...)")
   (xdoc::p
    "where @('<string>') is the string for the name of the C formal
     and @('<symbol>') is the symbol that is
     either the corresponding ACL2 formal
     or the corresponding ACL2 formal with the @('-ptr') suffix.
     The latter is for formals of pointer or array type:
     as explained in @(tsee atc-gen-context-preamble),
     the C values are represented by ACL2 variables of the form @('x-ptr'):
     these are the values that go into the initial scope,
     not the deferenced objects.")
   (xdoc::p
    "However, formals that represent external objects are skipped.
     This is because in C these are not function parameters.")
   (xdoc::p
    "We also return the list of the @('<symbol>')s,
     some of which are the formals,
     while the others are the formals suffixed by @('-ptr').
     See explanation just above."))
  (b* (((when (endp typed-formals)) (mv nil nil))
       ((cons var info) (car typed-formals))
       ((mv omap-rest init-formals-rest)
        (atc-gen-omap-update-formals (cdr typed-formals)))
       (type (atc-var-info->type info))
       (externalp (atc-var-info->externalp info))
       (var/varptr (if (or (type-case type :pointer)
                           (type-case type :array))
                       (add-suffix-to-fn var "-PTR")
                     var)))
    (if externalp
        (mv omap-rest init-formals-rest)
      (mv `(omap::update (ident ,(symbol-name var)) ,var/varptr ,omap-rest)
          (cons var/varptr init-formals-rest)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-add-var-formals ((fn symbolp)
                                 (typed-formals atc-symbol-varinfo-alistp)
                                 (compst-var symbolp))
  :returns (term "An untranslated term.")
  :short "Generate a term that is an @(tsee add-var) nest
          for the formals of a function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in the generated theorem that describes
     the initial computation state for a function execution.
     It has the form")
   (xdoc::codeblock
    "(add-var  (ident <string>)"
    "          <symbol>"
    "          (add-var ... (add-frame (ident <fn>) compst)...))")
   (xdoc::p
    "where @('<string>') is the string for the name of the C formal,
     @('<symbol>') is the symbol that is
     either the corresponding ACL2 formal
     or the corresponding ACL2 formal with the @('-ptr') suffix
     (according to the criterion in @(tsee atc-gen-omap-update-formals)),
     and the nest ends with @('(add-frame (ident <fn>) compst)'),
     where @('<fn>') is the string for the function name."))
  (b* (((when (endp typed-formals))
        `(add-frame (ident ,(symbol-name fn)) ,compst-var))
       ((cons var info) (car typed-formals))
       (type (atc-var-info->type info))
       (externalp (atc-var-info->externalp info))
       (add-var-rest (atc-gen-add-var-formals fn
                                              (cdr typed-formals)
                                              compst-var))
       (var/varptr (if (or (type-case type :pointer)
                           (type-case type :array))
                       (add-suffix-to-fn var "-PTR")
                     var)))
    (if externalp
        add-var-rest
      `(add-var (ident ,(symbol-name var)) ,var/varptr ,add-var-rest))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-context-preamble ((typed-formals atc-symbol-varinfo-alistp)
                                  (compst-var symbolp)
                                  (fenv-var symbolp)
                                  (prog-const symbolp))
  :returns (terms true-listp)
  :short "Generate a context preamble from the formals of a function."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee atc-context),
     the logical contexts for the generated theorems
     includes a preamble of premises that is a list of untranslated terms.
     This is calculated from the typed formals of
     the ACL2 function that is translated to a C function.")
   (xdoc::p
    "For each formal @('x') not representing an external object
     and whose C type is pointer or array,
     we generate a portion of the preamble saying that
     @('x-ptr') is a valid pointer value of the right type,
     the pointer's object designator is in allocated memory
     (for now; this will be generalized later),
     and reading the object yields @('x').
     Thus, a formal that is a pointer or array
     is represented by two variables in the generated theorems:
     this is necessary because the ACL2 function
     takes integers and structures and arrays (not pointers),
     but the C function takes pointers that point to integers and structures,
     and pointers that point to the beginning of arrays.
     In the theorems, we use the name of the formal
     as the integer or structure or array,
     and we introduce a new name, with a @('-ptr') suffix, for the pointer.
     Note that, because of the restriction on portable ASCII C identifiers,
     dashes cannot occur in names of formals,
     and thus something ending in @('-ptr') cannot cause conflicts.
     The terms generated in the preamble constrain @('x-ptr') to be the pointer,
     and include a binding hypothesis that sets @('x') to be
     the integer or structure or array to which @('x-ptr') points to.
     There is also a binding hypothesis for a variable @('x-objdes')
     that is the object designator in @('x-ptr');
     note that it cannot conflict with other variables,
     for the same reason as @('x-ptr').")
   (xdoc::p
    "In addition, for each formal @('x') not representing an external object
     and whose C type is a pointer or array,
     we generate a portion of the preamble saying that
     the designated object is disjoint from
     the objects designated by other formal parameters.
     We collect these disjointness hypotheses separately,
     so that we can put them all at the end of the final list of preamble terms,
     instead of interspersed with other preamble terms, for readability.")
   (xdoc::p
    "For each formal @('x') not representing an external object
     and whose C type is not pointer or array (i.e. is integer of structure),
     we generate no preamble terms.
     This is because the ACL2 formal directly represents the C formal.")
   (xdoc::p
    "For each formal @('x') that represents an external object,
     we generate a binding hypothesis saying that
     @('x') equals @(tsee read-object) applied to
     the object designator for the variable in static storage.
     This is adequate whether the external object is an integer or an array."))
  (b* (((mv terms-about-single-formals
            terms-about-formal-pairs)
        (atc-gen-context-preamble-aux typed-formals compst-var)))
    (append (list `(equal ,fenv-var (init-fun-env (preprocess ,prog-const))))
            terms-about-single-formals
            terms-about-formal-pairs))

  :prepwork
  ((define atc-gen-context-preamble-aux
     ((typed-formals atc-symbol-varinfo-alistp)
      (compst-var symbolp))
     :returns (mv (terms-about-single-formals true-listp)
                  (terms-about-formal-pairs true-listp))
     :parents nil
     (b* (((when (endp typed-formals)) (mv nil nil))
          ((cons var info) (car typed-formals))
          (type (atc-var-info->type info))
          (externalp (atc-var-info->externalp info))
          ((mv terms-about-this-formal
               terms-about-this-and-other-formals)
           (if externalp
               (mv `((equal ,var
                            (read-object (objdesign-static (ident
                                                            ,(symbol-name var)))
                                         ,compst-var)))
                   nil)
             (if (member-eq (type-kind type) '(:pointer :array))
                 (b* ((var-ptr (add-suffix-to-fn var "-PTR"))
                      (var-objdes (add-suffix-to-fn var "-OBJDES"))
                      (reftype (if (type-case type :pointer)
                                   (type-pointer->to type)
                                 (type-array->of type)))
                      (terms-about-this-formal
                       `((valuep ,var-ptr)
                         (equal (value-kind ,var-ptr) :pointer)
                         (value-pointer-validp ,var-ptr)
                         (equal ,var-objdes
                                (value-pointer->designator ,var-ptr))
                         (equal (objdesign-kind ,var-objdes) :alloc)
                         (equal (value-pointer->reftype ,var-ptr)
                                ,(type-to-maker reftype))
                         (equal ,var (read-object ,var-objdes ,compst-var))))
                      (terms-about-this-and-other-formals
                       (atc-gen-context-preamble-aux-aux var-ptr
                                                         (cdr typed-formals))))
                   (mv terms-about-this-formal
                       terms-about-this-and-other-formals))
               (mv nil nil))))
          ((mv more-terms-about-single-formals
               more-terms-about-formal-pairs)
           (atc-gen-context-preamble-aux (cdr typed-formals) compst-var)))
       (mv (append terms-about-this-formal
                   more-terms-about-single-formals)
           (append terms-about-this-and-other-formals
                   more-terms-about-formal-pairs)))

     :prepwork
     ((define atc-gen-context-preamble-aux-aux
        ((this-var-ptr symbolp)
         (typed-formals-rest atc-symbol-varinfo-alistp))
        :returns (terms true-listp)
        (b* (((when (endp typed-formals-rest)) nil)
             ((cons other-var other-info) (car typed-formals-rest)))
          (if (and (member-equal (type-kind (atc-var-info->type other-info))
                                 '(:pointer :array))
                   (not (atc-var-info->externalp other-info)))
              (cons `(object-disjointp
                      (value-pointer->designator ,this-var-ptr)
                      (value-pointer->designator ,(add-suffix-to-fn other-var
                                                                    "-PTR")))
                    (atc-gen-context-preamble-aux-aux this-var-ptr
                                                      (cdr typed-formals-rest)))
            (atc-gen-context-preamble-aux-aux this-var-ptr
                                              (cdr typed-formals-rest)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-init-scope-thms ((fn symbolp)
                                 (fn-guard symbolp)
                                 (typed-formals atc-symbol-varinfo-alistp)
                                 (prec-tags atc-string-taginfo-alistp)
                                 (context-preamble true-listp)
                                 (prog-const symbolp)
                                 (fn-fun-env-thm symbolp)
                                 (compst-var symbolp)
                                 (fenv-var symbolp)
                                 (names-to-avoid symbol-listp)
                                 state)
  :returns (mv (expand-event pseudo-event-formp)
               (expand-thm symbolp)
               (scopep-event pseudo-event-formp)
               (scopep-thm symbolp)
               (omap-update-nest "An untranslated term.")
               (init-formals symbol-listp
                             :hyp (atc-symbol-varinfo-alistp typed-formals))
               (names-to-avoid symbol-listp :hyp (symbol-listp names-to-avoid)))
  :short "Generate the theorems about
          the initial scope of a function execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate one theorem saying what the initial scope expands to,
     and one theorem saying that the expansion satisfies @(tsee scopep).")
   (xdoc::p
    "We also return the @(tsee omap::update) nest term
     that describes the initial scope, for use in subsequent theorems."))
  (b* ((wrld (w state))
       ((mv omap-update-nest init-formals)
        (atc-gen-omap-update-formals typed-formals))
       (formals (strip-cars typed-formals))
       (expand-thm (pack fn '-init-scope-expand))
       ((mv expand-thm names-to-avoid)
        (fresh-logical-name-with-$s-suffix expand-thm nil names-to-avoid wrld))
       (info-var (genvar$ 'atc "INFO" nil formals state))
       (formal-thms (atc-var-info-list->thm-list (strip-cdrs typed-formals)))
       (expand-formula
        `(implies (and (compustatep ,compst-var)
                       (equal ,fenv-var
                              (init-fun-env (preprocess ,prog-const)))
                       (equal ,info-var
                              (fun-env-lookup (ident ,(symbol-name fn))
                                              ,fenv-var))
                       ,@context-preamble
                       (,fn-guard ,@formals))
                  (equal (init-scope (fun-info->params ,info-var)
                                     (list ,@init-formals))
                         ,omap-update-nest)))
       (flexible-thms (atc-string-taginfo-alist-to-flexiblep-thms prec-tags))
       (value-kind-thms (atc-string-taginfo-alist-to-value-kind-thms prec-tags))
       (valuep-thms (atc-string-taginfo-alist-to-valuep-thms prec-tags))
       (type-of-value-thms
        (atc-string-taginfo-alist-to-type-of-value-thms prec-tags))
       (type-to-quoted-thms
        (atc-string-taginfo-alist-to-type-to-quoted-thms prec-tags))
       (pointer-type-to-quoted-thms
        (atc-string-taginfo-alist-to-pointer-type-to-quoted-thms prec-tags))
       (expand-hints
        `(("Goal" :in-theory '(,fn-fun-env-thm
                               (:e fun-info->params)
                               init-scope-when-consp
                               (:e param-declonp)
                               ,@formal-thms
                               valuep-when-ucharp
                               valuep-when-scharp
                               valuep-when-ushortp
                               valuep-when-sshortp
                               valuep-when-uintp
                               valuep-when-sintp
                               valuep-when-ulongp
                               valuep-when-slongp
                               valuep-when-ullongp
                               valuep-when-sllongp
                               ,@valuep-thms
                               value-kind-when-ucharp
                               value-kind-when-scharp
                               value-kind-when-ushortp
                               value-kind-when-sshortp
                               value-kind-when-uintp
                               value-kind-when-sintp
                               value-kind-when-ulongp
                               value-kind-when-slongp
                               value-kind-when-ullongp
                               value-kind-when-sllongp
                               ,@value-kind-thms
                               type-of-value-when-ucharp
                               type-of-value-when-scharp
                               type-of-value-when-ushortp
                               type-of-value-when-sshortp
                               type-of-value-when-uintp
                               type-of-value-when-sintp
                               type-of-value-when-ulongp
                               type-of-value-when-slongp
                               type-of-value-when-ullongp
                               type-of-value-when-sllongp
                               type-of-value-when-value-pointer
                               ,@type-of-value-thms
                               ,@type-to-quoted-thms
                               ,@pointer-type-to-quoted-thms
                               not-flexible-array-member-p-when-ucharp
                               not-flexible-array-member-p-when-scharp
                               not-flexible-array-member-p-when-ushortp
                               not-flexible-array-member-p-when-sshortp
                               not-flexible-array-member-p-when-uintp
                               not-flexible-array-member-p-when-sintp
                               not-flexible-array-member-p-when-ulongp
                               not-flexible-array-member-p-when-slongp
                               not-flexible-array-member-p-when-ullongp
                               not-flexible-array-member-p-when-sllongp
                               not-flexible-array-member-p-when-value-pointer
                               not-flexible-array-member-p-when-value-struct
                               ,@flexible-thms
                               remove-flexible-array-member-when-absent
                               value-fix-when-valuep
                               (:e param-declon-to-ident+tyname)
                               mv-nth-of-cons
                               (:e zp)
                               (:e tyname-to-type)
                               (:e adjust-type)
                               value-listp-of-cons
                               (:e value-listp)
                               (:e init-scope)
                               (:e scopep)
                               (:e type-uchar)
                               (:e type-schar)
                               (:e type-ushort)
                               (:e type-sshort)
                               (:e type-uint)
                               (:e type-sint)
                               (:e type-ulong)
                               (:e type-slong)
                               (:e type-ullong)
                               (:e type-sllong)
                               (:e type-pointer)
                               omap::assoc-of-update
                               (:e omap::assoc)
                               scopep-of-update
                               omap-update-of-const-identifier
                               (:e identp)
                               (:e ident->name)
                               identp-of-ident
                               equal-of-ident
                               (:e str-fix)))))
       ((mv expand-event &)
        (evmac-generate-defthm expand-thm
                               :formula expand-formula
                               :hints expand-hints
                               :enable nil))
       (scopep-thm (pack fn '-init-scope-scopep))
       ((mv scopep-thm names-to-avoid)
        (fresh-logical-name-with-$s-suffix scopep-thm nil names-to-avoid wrld))
       (scopep-formula
        `(implies (and (compustatep ,compst-var)
                       ,@context-preamble
                       (,fn-guard ,@formals))
                  (scopep ,omap-update-nest)))
       (valuep-thms (atc-string-taginfo-alist-to-valuep-thms prec-tags))
       (scopep-hints
        `(("Goal" :in-theory '(scopep-of-update
                               (:e scopep)
                               identp-of-ident
                               ,@formal-thms
                               valuep-when-ucharp
                               valuep-when-scharp
                               valuep-when-ushortp
                               valuep-when-sshortp
                               valuep-when-uintp
                               valuep-when-sintp
                               valuep-when-ulongp
                               valuep-when-slongp
                               valuep-when-ullongp
                               valuep-when-sllongp
                               ,@valuep-thms))))
       ((mv scopep-event &)
        (evmac-generate-defthm scopep-thm
                               :formula scopep-formula
                               :hints scopep-hints
                               :enable nil)))
    (mv expand-event
        expand-thm
        scopep-event
        scopep-thm
        omap-update-nest
        init-formals
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-push-init-thm ((fn symbolp)
                               (fn-guard symbolp)
                               (typed-formals atc-symbol-varinfo-alistp)
                               (prec-tags atc-string-taginfo-alistp)
                               (context-preamble true-listp)
                               (omap-update-nest "An untranslated term.")
                               (compst-var symbolp)
                               (names-to-avoid symbol-listp)
                               (wrld plist-worldp))
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp)
               (add-var-nest "An untranslated term.")
               (names-to-avoid symbol-listp
                               :hyp (symbol-listp names-to-avoid)))
  :short "Generate the theorem about
          the initial computation state of a function execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "This theorem says that pushing onto the frame stack
     a new frame with the initial scope for the function
     yields a computation state expressed as
     an @(tsee add-var) nest ended by an @(tsee add-frame).")
   (xdoc::p
    "We also return that computation state term,
     since it is used in subsequent theorems."))
  (b* ((add-var-nest (atc-gen-add-var-formals fn typed-formals compst-var))
       (formals (strip-cars typed-formals))
       (name (pack fn '-push-init))
       ((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix name nil names-to-avoid wrld))
       (formal-thms (atc-var-info-list->thm-list (strip-cdrs typed-formals)))
       (formula
        `(implies (and (compustatep ,compst-var)
                       ,@context-preamble
                       (,fn-guard ,@formals))
                  (equal (push-frame
                          (make-frame :function (ident ,(symbol-name fn))
                                      :scopes (list ,omap-update-nest))
                          ,compst-var)
                         ,add-var-nest)))
       (flexible-thms (atc-string-taginfo-alist-to-flexiblep-thms prec-tags))
       (valuep-thms (atc-string-taginfo-alist-to-valuep-thms prec-tags))
       (value-kind-thms (atc-string-taginfo-alist-to-value-kind-thms prec-tags))
       (hints
        `(("Goal" :in-theory '(push-frame-of-one-nonempty-scope
                               push-frame-of-one-empty-scope
                               ,@formal-thms
                               valuep-when-ucharp
                               valuep-when-scharp
                               valuep-when-ushortp
                               valuep-when-sshortp
                               valuep-when-uintp
                               valuep-when-sintp
                               valuep-when-ulongp
                               valuep-when-slongp
                               valuep-when-ullongp
                               valuep-when-sllongp
                               ,@valuep-thms
                               not-flexible-array-member-p-when-ucharp
                               not-flexible-array-member-p-when-scharp
                               not-flexible-array-member-p-when-ushortp
                               not-flexible-array-member-p-when-sshortp
                               not-flexible-array-member-p-when-uintp
                               not-flexible-array-member-p-when-sintp
                               not-flexible-array-member-p-when-ulongp
                               not-flexible-array-member-p-when-slongp
                               not-flexible-array-member-p-when-ullongp
                               not-flexible-array-member-p-when-sllongp
                               not-flexible-array-member-p-when-value-pointer
                               not-flexible-array-member-p-when-value-struct
                               ,@flexible-thms
                               ,@value-kind-thms
                               scopep-of-update
                               (:e scopep)
                               identp-of-ident))))
       ((mv event &)
        (evmac-generate-defthm name
                               :formula formula
                               :hints hints
                               :enable nil)))
    (mv event name add-var-nest names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-init-inscope-static ((fn symbolp)
                                     (fn-guard symbolp)
                                     (typed-formals atc-symbol-varinfo-alistp)
                                     (prec-tags atc-string-taginfo-alistp)
                                     (compst-var symbolp)
                                     (context atc-contextp)
                                     (names-to-avoid symbol-listp)
                                     (wrld plist-worldp))
  :returns (mv (scope atc-symbol-varinfo-alistp
                      :hyp (atc-symbol-varinfo-alistp typed-formals))
               (events pseudo-event-form-listp)
               (names-to-avoid symbol-listp :hyp (symbol-listp names-to-avoid)))
  :short "Generate the static storage scope of
          the initial symbol table for a C function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The initial symbol table consists of
     a scope for static storage and a scope for automatic storage.
     The former consists of the external objects passed as parameters
     to the ACL2 function that represents the C function
     (which in general is a subset of the external object in the program).")
   (xdoc::p
    "We go through the typed formals,
     and we select the ones representing external objects,
     generating an entry in the scope (alist) for each.")
   (xdoc::p
    "The @('-0') suffix that we use for the generated theorem name
     is motivated by the fact that these are the theorems
     for the initial symbol table;
     as we update the symbol table in the course of generating code,
     we use positive indices as suffixes."))
  (b* (((when (endp typed-formals)) (mv nil nil names-to-avoid))
       ((cons var info) (car typed-formals))
       (type (atc-var-info->type info))
       (var-thm (atc-var-info->thm info))
       (externalp (atc-var-info->externalp info))
       ((when (not externalp))
        (atc-gen-init-inscope-static fn fn-guard (cdr typed-formals)
                                     prec-tags compst-var context
                                     names-to-avoid wrld))
       (type-pred (atc-type-to-recognizer type prec-tags))
       (name (pack fn '- var '-in-scope-0))
       ((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix name nil names-to-avoid wrld))
       (formula1 `(and (objdesign-of-var (ident ,(symbol-name var))
                                         ,compst-var)
                       (equal (read-object (objdesign-of-var
                                            (ident ,(symbol-name var))
                                            ,compst-var)
                                           ,compst-var)
                              ,var)))
       (formula1 (atc-contextualize formula1
                                    context
                                    fn
                                    fn-guard
                                    compst-var
                                    nil
                                    nil
                                    t
                                    wrld))
       (formula2 `(,type-pred ,var))
       (formula2 (atc-contextualize formula2
                                    context
                                    fn
                                    fn-guard
                                    nil
                                    nil
                                    nil
                                    nil
                                    wrld))
       (formula `(and ,formula1 ,formula2))
       (valuep-when-type-pred (atc-type-to-valuep-thm type prec-tags))
       (hints
        `(("Goal"
           :in-theory
           '(objdesign-of-var-of-add-var-iff
             read-object-of-objdesign-of-var-of-add-var
             ,var-thm
             ident-fix-when-identp
             identp-of-ident
             equal-of-ident-and-ident
             (:e str-fix)
             ,valuep-when-type-pred
             objdesign-of-var-of-add-frame-when-read-object-static
             (:t objdesign-static)
             read-object-of-add-frame
             return-type-of-objdesign-static))))
       ((mv event &) (evmac-generate-defthm name
                                            :formula formula
                                            :hints hints
                                            :enable nil))
       ((mv scope-rest events-rest names-to-avoid)
        (atc-gen-init-inscope-static fn fn-guard (cdr typed-formals)
                                     prec-tags compst-var context
                                     names-to-avoid wrld)))
    (mv (cons (cons var
                    (make-atc-var-info :type type
                                       :thm name
                                       :externalp t))
              scope-rest)
        (cons event events-rest)
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-init-inscope-auto ((fn symbolp)
                                   (fn-guard symbolp)
                                   (typed-formals atc-symbol-varinfo-alistp)
                                   (prec-tags atc-string-taginfo-alistp)
                                   (compst-var symbolp)
                                   (context atc-contextp)
                                   (names-to-avoid symbol-listp)
                                   (wrld plist-worldp))
  :returns (mv (scope atc-symbol-varinfo-alistp
                      :hyp (atc-symbol-varinfo-alistp typed-formals))
               (events pseudo-event-form-listp)
               (names-to-avoid symbol-listp :hyp (symbol-listp names-to-avoid)))
  :short "Generate the automatic storage scope of
          the initial symbol tale for a C function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The initial symbol table consists of
     a scope for static storage and a scope for automatic storage.
     The latter consists of the ACL2 function parameters
     that represent C function parameters (i.e. not external objects).")
   (xdoc::p
    "We go through the typed formals,
     and we select the ones not representing external objects,
     generating an entry in the scope (alist) for each.")
   (xdoc::p
    "The @('-0') suffix that we use for the generated theorem name
     is motivated by the fact that these are the theorems
     for the initial symbol table;
     as we update the symbol table in the course of generating code,
     we use positive indices as suffixes."))
  (b* (((when (endp typed-formals)) (mv nil nil names-to-avoid))
       ((cons var info) (car typed-formals))
       (type (atc-var-info->type info))
       (var-thm (atc-var-info->thm info))
       (externalp (atc-var-info->externalp info))
       ((when externalp)
        (atc-gen-init-inscope-auto fn fn-guard (cdr typed-formals)
                                   prec-tags compst-var context
                                   names-to-avoid wrld))
       (type-pred (atc-type-to-recognizer type prec-tags))
       (name (pack fn '- var '-in-scope-0))
       ((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix name nil names-to-avoid wrld))
       (var/varptr (if (or (type-case type :pointer)
                           (type-case type :array))
                       (add-suffix-to-fn var "-PTR")
                     var))
       (formula1 `(and (objdesign-of-var (ident ,(symbol-name var))
                                         ,compst-var)
                       (equal (read-object (objdesign-of-var
                                            (ident ,(symbol-name var))
                                            ,compst-var)
                                           ,compst-var)
                              ,var/varptr)
                       ,@(and (or (type-case type :pointer)
                                  (type-case type :array))
                              `((equal (read-object
                                        ,(add-suffix-to-fn var "-OBJDES")
                                        ,compst-var)
                                       ,var)))))
       (formula1 (atc-contextualize formula1
                                    context
                                    fn
                                    fn-guard
                                    compst-var
                                    nil
                                    nil
                                    t
                                    wrld))
       (formula2 `(,type-pred ,var))
       (formula2 (atc-contextualize formula2
                                    context
                                    fn
                                    fn-guard
                                    nil
                                    nil
                                    nil
                                    nil
                                    wrld))
       (formula `(and ,formula1 ,formula2))
       (not-flexiblep-thms (atc-type-to-notflexarrmem-thms type prec-tags))
       (valuep-when-type-pred (atc-type-to-valuep-thm type prec-tags))
       (value-kind-when-type-pred
        (atc-type-to-value-kind-thm type prec-tags))
       (hints
        `(("Goal"
           :in-theory
           '(objdesign-of-var-of-add-var-iff
             read-object-of-objdesign-of-var-of-add-var
             ,var-thm
             ident-fix-when-identp
             identp-of-ident
             equal-of-ident-and-ident
             (:e str-fix)
             ,@not-flexiblep-thms
             remove-flexible-array-member-when-absent
             value-fix-when-valuep
             ,@(and (or (type-case type :pointer)
                        (type-case type :array))
                    '(read-object-of-add-var
                      read-object-of-add-frame))
             ,valuep-when-type-pred
             ,value-kind-when-type-pred))))
       ((mv event &) (evmac-generate-defthm name
                                            :formula formula
                                            :hints hints
                                            :enable nil))
       ((mv scope-rest events-rest names-to-avoid)
        (atc-gen-init-inscope-auto fn fn-guard (cdr typed-formals)
                                   prec-tags compst-var context
                                   names-to-avoid wrld)))
    (mv (cons (cons var
                    (make-atc-var-info :type type
                                       :thm name
                                       :externalp nil))
              scope-rest)
        (cons event events-rest)
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-init-inscope ((fn symbolp)
                              (fn-guard symbolp)
                              (typed-formals atc-symbol-varinfo-alistp)
                              (prec-tags atc-string-taginfo-alistp)
                              (compst-var symbolp)
                              (context atc-contextp)
                              (names-to-avoid symbol-listp)
                              (wrld plist-worldp))
  :returns (mv (inscope atc-symbol-varinfo-alist-listp
                        :hyp (atc-symbol-varinfo-alistp typed-formals))
               (events pseudo-event-form-listp)
               (names-to-avoid symbol-listp :hyp (symbol-listp names-to-avoid)))
  :short "Generate the initial symbol table for a C function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The initial symbol table consists of
     a scope for static storage and a scope for automatic storage."))
  (b* (((mv scope-static events-static names-to-avoid)
        (atc-gen-init-inscope-static fn fn-guard typed-formals prec-tags
                                     compst-var context names-to-avoid wrld))
       ((mv scope-auto events-auto names-to-avoid)
        (atc-gen-init-inscope-auto fn fn-guard typed-formals prec-tags
                                   compst-var context names-to-avoid wrld)))
    (mv (list scope-auto scope-static)
        (append events-static events-auto)
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-fun-endstate ((affect symbol-listp)
                              (typed-formals atc-symbol-varinfo-alistp)
                              (compst-var symbolp)
                              (prec-objs atc-string-objinfo-alistp))
  :returns (term "An untranslated term.")
  :short "Generate a term representing the ending computation state
          after the execution of a C function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee atc-gen-cfun-final-compustate),
     which eventually will be removed in favor of this one,
     once the new modular proof approach works
     for every C function generated by ATC.")
   (xdoc::p
    "The correctness theorem of a C function says that
     executing the function on a generic computation state
     (satisfying conditions in the hypotheses of the theorem)
     and on generic arguments
     yields an optional result (absent if the function is @('void'))
     and a computation state obtained by modifying
     zero or more objects in the computation state.
     These are the objects affected by the C function,
     which the correctness theorem binds to the results of
     the ACL2 function that represents the C function.
     The modified computation state is expressed as
     a nest of @(tsee write-object) and @(tsee write-static-var) calls,
     based on whether the affected objects are in the heap or in static storage.
     This ACL2 code here generates that nest.")
   (xdoc::p
    "The parameter @('affect') passed to this code
     consists of the formals of @('fn') that represent objects
     affected by the body of the ACL2 function that represents the C function.
     We go through @('affect') and we construct
     each nested @(tsee write-object) call,
     which needs both a pointer and an object.
     This is the case for objects in the heap;
     for objects in static storage,
     we generate a call of @(tsee write-static-var),
     and there are no pointers involved.")
   (xdoc::p
    "We add the suffix @('-new') to each variable
     because these will be bound to the final values of the variables
     in the theorems generated by the callers of this ACL2 function."))
  (b* (((when (endp affect)) compst-var)
       (formal (car affect))
       (info (cdr (assoc-eq formal typed-formals)))
       ((when (not info))
        (raise "Internal error: formal ~x0 not found." formal))
       (type (atc-var-info->type info))
       ((unless (or (type-case type :pointer)
                    (type-case type :array)
                    (atc-var-info->externalp info)))
        (raise "Internal error:
                affected formal ~x0 has type ~x1 and is not an external object."
               formal type))
       (var (add-suffix-to-fn formal "-NEW")))
    (if (consp (assoc-equal (symbol-name formal) prec-objs))
        `(write-static-var (ident ,(symbol-name formal))
                           ,var
                           ,(atc-gen-fun-endstate (cdr affect)
                                                  typed-formals
                                                  compst-var
                                                  prec-objs))
      `(write-object ,(add-suffix-to-fn formal "-OBJDES")
                     ,var
                     ,(atc-gen-fun-endstate (cdr affect)
                                            typed-formals
                                            compst-var
                                            prec-objs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-pop-frame-thm ((fn symbolp)
                               (fn-guard symbolp)
                               (body-term "An untranslated term.")
                               (body-type typep)
                               (body-correct-thm symbolp)
                               (affect symbol-listp)
                               (typed-formals atc-symbol-varinfo-alistp)
                               (compst-var symbolp)
                               (prec-objs atc-string-objinfo-alistp)
                               (prec-tags atc-string-taginfo-alistp)
                               (context atc-contextp)
                               (names-to-avoid symbol-listp)
                               (wrld plist-worldp))
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp)
               (names-to-avoid symbol-listp :hyp (symbol-listp names-to-avoid)))
  :short "Generate the theorem about
          popping the frame at the end of a function execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "This theorem says that popping the (top) frame
     in the computation state at the end of the function execution
     yields the initial computation state;
     this is only the case for the functions
     for which we support the generation of this theorem, of course;
     it is not true in general, and we will generalize this.")
   (xdoc::p
    "we ``save'' the initial computation state
     in a variable that we obtain by adding @('-init')
     at the end of the symbol of the variable for the computation state.
     This does not interfere with any other variables,
     because of the dash which is disallowed in C variable names.")
   (xdoc::p
    "The @('context') parameter of this ACL2 function is
     the context at the end of the function body;
     this is used to contextualize the computation state
     from where the frame is popped."))
  (b* ((compst-init-var (pack compst-var '-init))
       (name (pack fn '-pop-frame))
       ((mv name names-to-avoid) (fresh-logical-name-with-$s-suffix
                                  name nil names-to-avoid wrld))
       (new-compst (atc-gen-fun-endstate affect
                                         typed-formals
                                         compst-init-var
                                         prec-objs))
       (binder (if (type-case body-type :void)
                   (if (consp (cdr affect))
                       `(mv ,@(acl2::add-suffix-to-fn-lst affect "-NEW"))
                     (acl2::add-suffix-to-fn (car affect) "-NEW"))
                 (if (consp affect)
                     `(mv & ,@(acl2::add-suffix-to-fn-lst affect "-NEW"))
                   nil)))
       (formula `(equal (pop-frame ,compst-var) ,new-compst))
       (formula (atc-contextualize formula
                                   context
                                   fn
                                   fn-guard
                                   compst-var
                                   nil
                                   nil
                                   t
                                   wrld))
       (formula `(let ((,compst-init-var ,compst-var)) ,formula))
       (formula (if binder
                    `(b* ((,binder ,body-term)) ,formula)
                  formula))
       (formals-thms (atc-gen-pop-frame-thm-aux typed-formals))
       (hints
        `(("Goal"
           :in-theory
           '(pop-frame-of-if*
             update-var-of-enter-scope
             update-var-of-add-var
             exit-scope-of-enter-scope
             exit-scope-of-add-var
             compustate-frames-number-of-add-var-not-zero
             compustate-frames-number-of-enter-scope-not-zero
             compustate-frames-number-of-add-frame-not-zero
             compustatep-of-add-var
             compustatep-of-enter-scope
             pop-frame-of-add-var
             pop-frame-of-add-frame
             acl2::if*-when-same
             update-object-of-enter-scope
             compustatep-of-update-object
             compustate-frames-number-of-update-object
             update-object-of-add-var
             update-object-of-add-frame
             write-object-to-update-object
             write-object-okp-of-update-object-same
             write-object-okp-of-update-object-disjoint
             write-object-okp-when-valuep-of-read-object-no-syntaxp
             write-object-okp-of-if*-val
             ,@formals-thms
             valuep-when-ucharp
             valuep-when-scharp
             valuep-when-ushortp
             valuep-when-sshortp
             valuep-when-uintp
             valuep-when-sintp
             valuep-when-ulongp
             valuep-when-slongp
             valuep-when-ullongp
             valuep-when-sllongp
             valuep-when-uchar-arrayp
             valuep-when-schar-arrayp
             valuep-when-ushort-arrayp
             valuep-when-sshort-arrayp
             valuep-when-uint-arrayp
             valuep-when-sint-arrayp
             valuep-when-ulong-arrayp
             valuep-when-slong-arrayp
             valuep-when-ullong-arrayp
             valuep-when-sllong-arrayp
             ,@(atc-string-taginfo-alist-to-valuep-thms prec-tags)
             type-of-value-when-ucharp
             type-of-value-when-scharp
             type-of-value-when-ushortp
             type-of-value-when-sshortp
             type-of-value-when-uintp
             type-of-value-when-sintp
             type-of-value-when-ulongp
             type-of-value-when-slongp
             type-of-value-when-ullongp
             type-of-value-when-sllongp
             type-of-value-when-uchar-arrayp
             type-of-value-when-schar-arrayp
             type-of-value-when-ushort-arrayp
             type-of-value-when-sshort-arrayp
             type-of-value-when-uint-arrayp
             type-of-value-when-sint-arrayp
             type-of-value-when-ulong-arrayp
             type-of-value-when-slong-arrayp
             type-of-value-when-ullong-arrayp
             type-of-value-when-sllong-arrayp
             ,@(atc-string-taginfo-alist-to-type-of-value-thms prec-tags)
             uchar-arrayp-of-uchar-array-write
             schar-arrayp-of-schar-array-write
             ushort-arrayp-of-ushort-array-write
             sshort-arrayp-of-sshort-array-write
             uint-arrayp-of-uint-array-write
             sint-arrayp-of-sint-array-write
             ulong-arrayp-of-ulong-array-write
             slong-arrayp-of-slong-array-write
             ullong-arrayp-of-ullong-array-write
             sllong-arrayp-of-sllong-array-write
             value-array->length-when-uchar-arrayp
             value-array->length-when-schar-arrayp
             value-array->length-when-ushort-arrayp
             value-array->length-when-sshort-arrayp
             value-array->length-when-uint-arrayp
             value-array->length-when-sint-arrayp
             value-array->length-when-ulong-arrayp
             value-array->length-when-slong-arrayp
             value-array->length-when-ullong-arrayp
             value-array->length-when-sllong-arrayp
             uchar-array-length-of-uchar-array-write
             schar-array-length-of-schar-array-write
             ushort-array-length-of-ushort-array-write
             sshort-array-length-of-sshort-array-write
             uint-array-length-of-uint-array-write
             sint-array-length-of-sint-array-write
             ulong-array-length-of-ulong-array-write
             slong-array-length-of-slong-array-write
             ullong-array-length-of-ullong-array-write
             sllong-array-length-of-sllong-array-write
             update-object-of-if*-val
             update-object-of-read-object-same
             update-object-of-update-object-same
             update-object-of-update-object-less-symbol
             update-object-of-update-object-less-ident
             update-object-of-update-var
             update-object-of-update-static-var
             update-static-var-of-add-var
             update-static-var-of-add-frame
             compustatep-of-update-static-var
             write-static-var-to-update-static-var
             write-static-var-okp-when-valuep-of-read-static-var
             read-object-of-objdesign-static
             exit-scope-of-if*
             write-static-var-to-update-static-var
             update-static-var-of-enter-scope
             compustatep-of-add-frame
             update-static-var-of-if*-val
             object-disjointp-commutative
             mv-nth-of-cons
             (:e zp)
             ,body-correct-thm))
          (and stable-under-simplificationp
               '(:in-theory '(if*
                              mv-nth-of-cons
                              (:e zp))))))
       ((mv event &) (evmac-generate-defthm name
                                            :formula formula
                                            :hints hints
                                            :enable nil)))
    (mv event name names-to-avoid))
  :prepwork
  ((define atc-gen-pop-frame-thm-aux ((typed-formals atc-symbol-varinfo-alistp))
     :returns (thms symbol-listp)
     :parents nil
     (cond ((endp typed-formals) nil)
           (t (cons (atc-var-info->thm (cdar typed-formals))
                    (atc-gen-pop-frame-thm-aux (cdr typed-formals))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-fun-correct-thm ((fn symbolp)
                                 (fn-guard symbolp)
                                 (fn-def* symbolp)
                                 (init-formals symbol-listp)
                                 (affect symbol-listp)
                                 (typed-formals atc-symbol-varinfo-alistp)
                                 (context-preamble true-listp)
                                 (compst-var symbolp)
                                 (fenv-var symbolp)
                                 (limit-var symbolp)
                                 (fn-thms symbol-symbol-alistp)
                                 (fn-fun-env-thm symbolp)
                                 (init-scope-expand-thm symbolp)
                                 (init-scope-scopep-thm symbolp)
                                 (push-init-thm symbolp)
                                 (pop-frame-thm symbolp)
                                 (body-thm symbolp)
                                 (body-type typep)
                                 (body-limit pseudo-termp)
                                 (prec-tags atc-string-taginfo-alistp)
                                 (prec-objs atc-string-objinfo-alistp)
                                 (names-to-avoid symbol-listp)
                                 state)
  :returns (mv (events pseudo-event-form-listp)
               (print-event pseudo-event-formp)
               (name symbolp :hyp (symbol-symbol-alistp fn-thms))
               (lemma-name symbolp)
               (names-to-avoid symbol-listp :hyp (symbol-listp names-to-avoid)))
  :short "Generate the correctness theorem for a C function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This will eventually replace @(tsee atc-gen-cfun-correct-thm),
     once the modular proof generation approach is completed.")
   (xdoc::p
    "We make use of other modular theorems,
     whose names are passed to this ACL2 function.
     We use 1 more than the limit for the body as limit bound,
     because we need 1 to go from @(tsee exec-fun)
     to @(tsee exec-block-item-list),
     which is what the body's theorem refers to.")
   (xdoc::p
    "We enable @(tsee declar) and @(tsee assign) in the generated hints
     because the correctness theorem generated about the body of the function
     (i.e. @('body-thm')) does not that have that wrapper.
     We will need to add other wrappers like @(tsee assign) here,
     when we extend modular proofs to handle those.
     An alternative could be to include the wrappers
     in the theorems about the statements that form the body,
     and then we will not need to include them here."))
  (b* ((wrld (w state))
       (lemma-name (pack fn '-correct))
       ((mv lemma-name names-to-avoid) (fresh-logical-name-with-$s-suffix
                                        lemma-name nil names-to-avoid wrld))
       (formals (formals+ fn wrld))
       (result-var (if (type-case body-type :void)
                       nil
                     (genvar$ 'atc "RESULT" nil formals state)))
       (limit `(binary-+ '1 ,body-limit))
       (affect-new (acl2::add-suffix-to-fn-lst affect "-NEW"))
       (fn-results (append (and result-var
                                (list result-var))
                           affect-new))
       (fn-binder (if (endp (cdr fn-results))
                      (car fn-results)
                    `(mv ,@fn-results)))
       (new-compst (atc-gen-fun-endstate affect
                                         typed-formals
                                         compst-var
                                         prec-objs))
       (exec-hyps `(and (compustatep ,compst-var)
                        ,@context-preamble
                        (,fn-guard ,@formals)
                        (integerp ,limit-var)
                        (>= ,limit-var ,limit)))
       (exec-concl `(equal (exec-fun (ident ,(symbol-name fn))
                                     (list ,@init-formals)
                                     ,compst-var
                                     ,fenv-var
                                     ,limit-var)
                           (mv ,result-var ,new-compst)))
       (type-hyps `(,fn-guard ,@formals))
       ((mv type-concl &) (atc-gen-term-type-formula `(,fn ,@formals)
                                                     body-type
                                                     affect
                                                     (list typed-formals)
                                                     prec-tags))
       (exec-formula `(implies ,exec-hyps
                               (b* ((,fn-binder (,fn ,@formals)))
                                 ,exec-concl)))
       (type-formula `(implies ,type-hyps
                               ,type-concl))
       (lemma-formula `(and ,exec-formula ,type-formula))
       (valuep-when-type-pred
        (and result-var
             (atc-type-to-valuep-thm body-type prec-tags)))
       (type-of-value-when-type-pred
        (and result-var
             (atc-type-to-type-of-value-thm body-type prec-tags)))
       (type-to-quoted-thm?
        (and result-var
             (atc-type-to-type-to-quoted-thms body-type prec-tags)))
       (lemma-hints
        `(("Goal" :in-theory '(exec-fun-open-return
                               exec-fun-open-noreturn
                               (:e type-void)
                               not-zp-of-limit-variable
                               ,fn-fun-env-thm
                               ,init-scope-expand-thm
                               ,init-scope-scopep-thm
                               ,push-init-thm
                               ,body-thm
                               (:e fun-info->body)
                               mv-nth-of-cons
                               (:e zp)
                               return-type-of-stmt-value-return
                               return-type-of-stmt-value-none
                               stmt-value-return->value?-of-stmt-value-return
                               value-option-fix-when-value-optionp
                               value-optionp-when-valuep
                               (:e value-optionp)
                               (:e type-of-value-option)
                               ,@(and result-var
                                      (list* valuep-when-type-pred
                                             type-of-value-when-type-pred
                                             type-to-quoted-thm?))
                               type-of-value-option-when-valuep
                               (:e fun-info->result)
                               (:e tyname-to-type)
                               ,@(and result-var
                                      (type-integerp body-type)
                                      `((:e ,(pack 'type-
                                                   (type-kind body-type)))))
                               ,pop-frame-thm
                               ,fn-def*
                               declar
                               assign))))
       ((mv lemma-event &) (evmac-generate-defthm lemma-name
                                                  :formula lemma-formula
                                                  :hints lemma-hints
                                                  :enable nil))
       (name (cdr (assoc-eq fn fn-thms)))
       (formula
        `(implies (and (compustatep ,compst-var)
                       ,@context-preamble
                       ,(untranslate$ (uguard+ fn wrld) nil state)
                       (integerp ,limit-var)
                       (>= ,limit-var ,limit))
                  (b* ((,fn-binder (,fn ,@formals)))
                    ,exec-concl)))
       (hints `(("Goal"
                 :use ,lemma-name
                 :in-theory '(,fn-guard))))
       ((mv local-event exported-event)
        (evmac-generate-defthm name
                               :formula formula
                               :hints hints
                               :enable nil))
       (print-event `(cw-event "~%~x0~|" ',exported-event)))
    (mv (list lemma-event
              local-event
              exported-event)
        print-event
        name
        lemma-name
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-typed-formals-to-extobjs ((typed-formals atc-symbol-varinfo-alistp))
  :returns (extobjs symbol-listp :hyp (atc-symbol-varinfo-alistp typed-formals))
  :short "List of the formals of a function that represent external objects."
  (b* (((when (endp typed-formals)) nil)
       ((cons formal info) (car typed-formals)))
    (if (atc-var-info->externalp info)
        (cons formal (atc-typed-formals-to-extobjs (cdr typed-formals)))
      (atc-typed-formals-to-extobjs (cdr typed-formals)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-fundef ((fn symbolp)
                        (prec-fns atc-symbol-fninfo-alistp)
                        (prec-tags atc-string-taginfo-alistp)
                        (prec-objs atc-string-objinfo-alistp)
                        (proofs booleanp)
                        (prog-const symbolp)
                        (init-fun-env-thm symbolp)
                        (fn-thms symbol-symbol-alistp)
                        (print evmac-input-print-p)
                        (names-to-avoid symbol-listp)
                        state)
  :guard (not (eq fn 'quote))
  :returns (mv erp
               (fundef fundefp)
               (events pseudo-event-form-listp)
               (updated-prec-fns atc-symbol-fninfo-alistp
                                 :hyp (atc-symbol-fninfo-alistp prec-fns)
                                 :hints (("Goal" :in-theory (enable acons))))
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate a C function definition
          from a non-recursive ACL2 function, with accompanying theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "We ensure that all the formals affected by the function body
     have pointer or array types, as required in the user documentation.")
   (xdoc::p
    "We return local and exported events for the theorems about
     the correctness of the C function definition.")
   (xdoc::p
    "We extend the alist @('prec-fns') with information about the function.")
   (xdoc::p
    "We use the type of the value returned by the statement for the body
     as the result type of the C function.")
   (xdoc::p
    "For the limit, we need 1 to go from @(tsee exec-fun) to @(tsee exec-stmt),
     another 1 from there to @(tsee exec-block-item-list)
     in the @(':compound') case,
     and then we use the limit for the block."))
  (b* (((reterr) (irr-fundef) nil nil nil)
       (wrld (w state))
       (name (symbol-name fn))
       ((unless (paident-stringp name))
        (reterr
         (msg "The symbol name ~s0 of the function ~x1 ~
               must be a portable ASCII C identifier, but it is not."
              name fn)))
       ((mv fn-guard-event
            fn-guard
            names-to-avoid)
        (atc-gen-fn-guard fn names-to-avoid state))
       ((mv fn-def*-events
            fn-def*
            names-to-avoid)
        (atc-gen-fn-def* fn names-to-avoid wrld))
       ((erp typed-formals formals-events names-to-avoid)
        (atc-typed-formals fn fn-guard prec-tags prec-objs names-to-avoid wrld))
       ((erp params) (atc-gen-param-declon-list typed-formals fn prec-objs))
       (formals (strip-cars typed-formals))
       (compst-var (genvar$ 'atc "COMPST" nil formals state))
       (fenv-var (genvar$ 'atc "FENV" nil formals state))
       (limit-var (genvar$ 'atc "LIMIT" nil formals state))
       (context-preamble (atc-gen-context-preamble typed-formals
                                                   compst-var
                                                   fenv-var
                                                   prog-const))
       ((mv fn-fun-env-thm names-to-avoid)
        (atc-gen-cfun-fun-env-thm-name fn names-to-avoid wrld))
       ((mv init-scope-expand-event
            init-scope-expand-thm
            init-scope-scopep-event
            init-scope-scopep-thm
            omap-update-nest
            init-formals
            names-to-avoid)
        (atc-gen-init-scope-thms fn
                                 fn-guard
                                 typed-formals
                                 prec-tags
                                 context-preamble
                                 prog-const
                                 fn-fun-env-thm
                                 compst-var
                                 fenv-var
                                 names-to-avoid
                                 state))
       ((mv push-init-thm-event
            push-init-thm
            add-var-nest
            names-to-avoid)
        (atc-gen-push-init-thm fn
                               fn-guard
                               typed-formals
                               prec-tags
                               context-preamble
                               omap-update-nest
                               compst-var
                               names-to-avoid
                               wrld))
       (premises (list (make-atc-premise-compustate :var compst-var
                                                    :term add-var-nest)))
       (context (make-atc-context :preamble context-preamble
                                  :premises premises))
       ((mv inscope
            init-inscope-events
            names-to-avoid)
        (atc-gen-init-inscope fn fn-guard typed-formals prec-tags
                              compst-var context names-to-avoid wrld))
       (body (ubody+ fn wrld))
       ((erp affect) (atc-find-affected fn body typed-formals prec-fns wrld))
       ((unless (atc-formal-affectable-listp affect typed-formals))
        (reterr
         (msg "At least one of the formals of ~x0 ~
               that are affected by its body has a non-pointer non-array type, ~
               or does not refer to an external object. ~
               This is currently disallowed: ~
               only pointer or array variables,
               or variables that refer to external objects, ~
               may be affected by a non-recursive target function."
              fn)))
       ((erp (stmt-gout body))
        (atc-gen-stmt body
                      (make-stmt-gin
                       :context context
                       :var-term-alist nil
                       :typed-formals typed-formals
                       :inscope inscope
                       :loop-flag nil
                       :affect affect
                       :fn fn
                       :fn-guard fn-guard
                       :compst-var compst-var
                       :fenv-var fenv-var
                       :limit-var limit-var
                       :prec-fns prec-fns
                       :prec-tags prec-tags
                       :prec-objs prec-objs
                       :thm-index 1
                       :names-to-avoid names-to-avoid
                       :proofs proofs)
                      state))
       (names-to-avoid body.names-to-avoid)
       ((when (and (type-case body.type :void)
                   (not affect)))
        (reterr
         (raise "Internal error: ~
                 the function ~x0 returns void and affects no variables."
                fn)))
       ((unless (or (type-nonchar-integerp body.type)
                    (type-case body.type :struct)
                    (type-case body.type :void)))
        (reterr
         (raise "Internal error: ~
                 the function ~x0 has return type ~x1."
                fn body.type)))
       ((mv pop-frame-event
            pop-frame-thm
            names-to-avoid)
        (atc-gen-pop-frame-thm fn
                               fn-guard
                               (untranslate$ body.term nil state)
                               body.type
                               body.thm-name
                               affect
                               typed-formals
                               compst-var
                               prec-objs
                               prec-tags
                               body.context
                               names-to-avoid
                               wrld))
       (id (make-ident :name name))
       ((mv tyspec &) (ident+type-to-tyspec+declor id body.type))
       (fundef (make-fundef :tyspec tyspec
                            :declor (make-fun-declor-base :name id
                                                          :params params)
                            :body body.items))
       (finfo (fun-info-from-fundef fundef))
       (limit `(binary-+ '2 ,body.limit))
       (fn-fun-env-event
        (atc-gen-cfun-fun-env-thm fn
                                  fn-fun-env-thm
                                  prog-const
                                  finfo
                                  init-fun-env-thm))
       ((mv fn-result-events
            fn-result-thm
            names-to-avoid)
        (atc-gen-fn-result-thm fn
                               body.type
                               affect
                               typed-formals
                               prec-fns
                               prec-tags
                               prec-objs
                               names-to-avoid
                               state))
       ((mv fn-correct-events
            fn-correct-print-event
            fn-correct-thm
            fn-correct-lemma-thm
            names-to-avoid)
        (if body.thm-name
            (atc-gen-fun-correct-thm fn
                                     fn-guard
                                     fn-def*
                                     init-formals
                                     affect
                                     typed-formals
                                     context-preamble
                                     compst-var
                                     fenv-var
                                     limit-var
                                     fn-thms
                                     fn-fun-env-thm
                                     init-scope-expand-thm
                                     init-scope-scopep-thm
                                     push-init-thm
                                     pop-frame-thm
                                     body.thm-name
                                     body.type
                                     body.limit
                                     prec-tags
                                     prec-objs
                                     names-to-avoid
                                     state)
          (b* (((mv events print-event name)
                (atc-gen-cfun-correct-thm fn
                                          typed-formals
                                          body.type
                                          affect
                                          prec-fns
                                          prec-tags
                                          prec-objs
                                          prog-const
                                          compst-var
                                          fenv-var
                                          limit-var
                                          fn-thms
                                          fn-fun-env-thm
                                          limit
                                          state)))
            (mv events print-event name nil names-to-avoid))))
       (progress-start?
        (and (evmac-input-print->= print :info)
             `((cw-event "~%Generating the proofs for ~x0..." ',fn))))
       (progress-end? (and (evmac-input-print->= print :info)
                           `((cw-event " done.~%"))))
       (print-result? (and (evmac-input-print->= print :result)
                           (list fn-correct-print-event)))
       (local-events
        (append
         progress-start?
         (list fn-fun-env-event)
         (list fn-guard-event)
         fn-def*-events
         formals-events
         (list init-scope-expand-event)
         (list init-scope-scopep-event)
         (list push-init-thm-event)
         init-inscope-events
         body.events
         (and body.thm-name
              (list pop-frame-event))
         fn-result-events
         fn-correct-events
         progress-end?
         print-result?))
       (info (make-atc-fn-info
              :out-type body.type
              :in-types (atc-var-info-list->type-list
                         (strip-cdrs typed-formals))
              :loop? nil
              :affect affect
              :extobjs (atc-typed-formals-to-extobjs typed-formals)
              :result-thm fn-result-thm
              :correct-thm fn-correct-thm
              :correct-mod-thm fn-correct-lemma-thm
              :measure-nat-thm nil
              :fun-env-thm fn-fun-env-thm
              :limit limit
              :guard fn-guard)))
    (retok fundef
           (and proofs local-events)
           (acons fn info prec-fns)
           names-to-avoid))
  :guard-hints
  (("Goal"
    :do-not '(preprocess)
    :in-theory
    (e/d (acl2::true-listp-when-pseudo-event-form-listp-rewrite
          alistp-when-atc-symbol-varinfo-alistp-rewrite
          atc-var-info-listp-of-strip-cdrs-when-atc-symbol-varinfo-alistp
          true-listp-when-atc-symbol-varinfo-alist-listp-rewrite
          symbol-listp-of-strip-cars-when-atc-symbol-varinfo-alistp
          alistp-when-atc-symbol-fninfo-alistp-rewrite)
         ((:e tau-system)
          acl2::strip-cars-when-atom
          acl2::list-fix-when-len-zero)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop-measure-fn ((fn symbolp)
                                 (names-to-avoid symbol-listp)
                                 state)
  :guard (irecursivep+ fn (w state))
  :returns (mv (event pseudo-event-formp)
               (name symbolp)
               (formals symbol-listp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate a measure function for a recursive target function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The correctness theorem for a loop involves
     the measure of the loop function.
     The measure may be a complex term.
     An early version of ATC was using the measure terms
     directly in the generated theorems,
     but that caused proof failures sometimes,
     due to ACL2 sometimes modifying those measure terms during a proof
     (e.g. due to equalities involving measure subterms
     arising from case analyses):
     after the terms were modified,
     some of the generated theorems about the measure terms
     no longer apply, making the proof fail.
     Thus, we ``protect'' the measure terms from modifications
     by generating functions for them,
     and using those functions in the generated theorems.")
   (xdoc::p
    "The code of this ACL2 function generates a measure function
     for the recursive target function @('fn').
     The funcion is not guard-verified,
     because its is only logical.
     It is important that we take,
     as formal parameters of the generated measure function,
     only the variables that occur in the measure term.
     This facilitates the generation of
     the loop function's termination theorem
     expressed over the  generated measure function."))
  (b* ((wrld (w state))
       (name (packn-pos (list 'measure-of- fn) fn))
       ((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix name 'function names-to-avoid wrld))
       ((when (eq name 'quote))
        (raise "Internal error: name is QUOTE.")
        (mv '(_) nil nil nil))
       (measure-term (get-measure+ fn wrld))
       (measure-vars (all-vars measure-term))
       ((mv & event)
        (evmac-generate-defun
         name
         :formals measure-vars
         :body (untranslate$ measure-term nil state)
         :verify-guards nil
         :enable nil)))
    (mv event name measure-vars names-to-avoid))
  ///

  (defret atc-gen-loop-measure-fn-name-not-quote
    (not (equal name 'quote))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atc-gen-loop-tthm-formula
  :short "Generate the formula for the loop termination theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is obtained from the loop function's termination theorem,
     transformed as follows.")
   (xdoc::p
    "The @(tsee o<) relation is replaced with @(tsee <).
     This is justified by the fact that the measure yields a natural number,
     as guaranteed by the applicability condition.")
   (xdoc::p
    "Furthermore, the measure term is replaced
     with a call of the generated measure function.
     More precisely, this is done in every term of the form @('(o< A B)')
     (at the same replacing @(tsee o<) with @(tsee <) as mentioned above),
     where we expect @('B') to be the measure term,
     and @('A') to be the instantiation of the measure term
     to one of the recursive calls of the loop function.
     We replace @('B') with a generic call of the measure function,
     and @('A') with an instantiated call of the measure function;
     we obtain the instantiation by matching @('B') to @('A').
     It is not yet clear whether this approach will work in all cases."))

  (define atc-gen-loop-tthm-formula ((term pseudo-termp)
                                     (fn symbolp)
                                     (measure-of-fn symbolp)
                                     (measure-formals symbol-listp)
                                     state)
    :guard (not (eq measure-of-fn 'quote))
    :returns (mv erp
                 new-term) ; PSEUDO-TERMP proved below
    (b* (((reterr) nil)
         ((when (variablep term)) (retok term))
         ((when (fquotep term)) (retok term))
         (term-fn (ffn-symb term))
         ((when (eq term-fn 'o<))
          (b* ((meas-gen (fargn term 2))
               (meas-inst (fargn term 1))
               ((mv okp subst) (one-way-unify$ meas-gen meas-inst state))
               ((when (not okp))
                (reterr
                 (msg "Failed to match istantiated measure ~x0 ~
                       to general measure ~x1 of function ~x2."
                      meas-inst meas-gen fn)))
               (measure-args (fty-fsublis-var-lst subst measure-formals)))
            (retok
             `(< (,measure-of-fn ,@measure-args)
                 (,measure-of-fn ,@measure-formals)))))
         ((erp new-args)
          (atc-gen-loop-tthm-formula-lst (fargs term)
                                         fn
                                         measure-of-fn
                                         measure-formals
                                         state)))
      (retok (fcons-term term-fn new-args))))

  (define atc-gen-loop-tthm-formula-lst ((terms pseudo-term-listp)
                                         (fn symbolp)
                                         (measure-of-fn symbolp)
                                         (measure-formals symbol-listp)
                                         state)
    :guard (not (eq measure-of-fn 'quote))
    :returns (mv erp
                 new-terms) ; PSEUDO-TERM-LISTP proved below
    (b* (((reterr) nil)
         ((when (endp terms)) (retok nil))
         ((erp new-term)
          (atc-gen-loop-tthm-formula (car terms)
                                     fn
                                     measure-of-fn
                                     measure-formals
                                     state))
         ((erp new-terms) (atc-gen-loop-tthm-formula-lst (cdr terms)
                                                         fn
                                                         measure-of-fn
                                                         measure-formals
                                                         state)))
      (retok (cons new-term new-terms))))

  :prepwork ((local (in-theory (enable pseudo-termp
                                       length))))

  :verify-guards nil ; done below
  ///
  (verify-guards atc-gen-loop-tthm-formula
    :hints (("Goal" :in-theory (enable pseudo-termp))))

  (defret-mutual len-of-atc-gen-loop-tthm-formula/lst
    (defret len-of-atc-gen-loop-tthm-formula
      t
      :rule-classes nil
      :fn atc-gen-loop-tthm-formula)
    (defret len-of-atc-gen-loop-tthm-formula-lst
      (implies (not erp)
               (equal (len new-terms)
                      (len terms)))
      :fn atc-gen-loop-tthm-formula-lst))

  (defret-mutual return-types-of-atc-gen-loop-tthm-formula/lst
    (defret pseudo-termp-of-atc-gen-loop-tthm-formula
      (pseudo-termp new-term)
      :hyp (and (pseudo-termp term)
                (symbolp measure-of-fn)
                (not (eq measure-of-fn 'quote))
                (symbol-listp measure-formals))
      :fn atc-gen-loop-tthm-formula)
    (defret pseudo-termp-of-atc-gen-loop-tthm-formula-lst
      (pseudo-term-listp new-terms)
      :hyp (and (pseudo-term-listp terms)
                (symbolp measure-of-fn)
                (not (eq measure-of-fn 'quote))
                (symbol-listp measure-formals))
      :fn atc-gen-loop-tthm-formula-lst)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-exec-stmt-while-for-loop ((fn symbolp)
                                          (loop-stmt stmtp)
                                          (prog-const symbolp)
                                          (names-to-avoid symbol-listp)
                                          (wrld plist-worldp))
  :guard (and (irecursivep+ fn wrld)
              (stmt-case loop-stmt :while))
  :returns (mv (events pseudo-event-form-listp)
               (exec-stmt-while-for-fn symbolp)
               (exec-stmt-while-for-fn-thm symbolp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate a version of @(tsee exec-stmt-while)
          specialized to the loop represented by @('fn')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The correctness theorem for a loop says that
     the execution of the loop (via @(tsee exec-stmt-while))
     is suitably equivalent to
     the corresponding ACL2 recursive function @('fn').
     The theorem is proved by induction, unsurprisingly.
     However, due to the form in which the function appears in the theorem,
     namely that the function is not applied to ACL2 variables,
     we cannot use the function's induction scheme.
     But we cannot readily use
     the induction scheme of the execution functions
     of the C dynamic semantics,
     or at least it looks cumbersome to do so,
     because there are several of them, mutually recursive.")
   (xdoc::p
    "What we really need is an induction scheme related to the loop.
     Thus we introduce a local function that is like @(tsee exec-stmt-while)
     but specialized to the loop generated from @('fn');
     this function is singly recursive, providing the needed induction scheme.
     The function does not need to be guard-verified,
     because it is only used for logic.
     We also generate a theorem saying that this new function
     is equivalent to @(tsee exec-stmt-while) applied to the loop;
     this is critical, because eventually the proof must be
     about the execution functions of the C dynamic semantics.
     For robustness, the termination proof for this new function,
     and the proof of the associated theorem,
     are carried out in exactly specified theories
     that should always work."))
  (b* ((loop-test (stmt-while->test loop-stmt))
       (loop-body (stmt-while->body loop-stmt))
       (exec-stmt-while-for-fn
        (packn-pos (list 'exec-stmt-while-for- fn) fn))
       ((mv exec-stmt-while-for-fn names-to-avoid)
        (fresh-logical-name-with-$s-suffix exec-stmt-while-for-fn
                                           'function
                                           names-to-avoid
                                           wrld))
       (exec-stmt-while-for-fn-body
        `(b* ((fenv (init-fun-env (preprocess ,prog-const)))
              ((when (zp limit)) (mv (error :limit) (compustate-fix compst)))
              (test-eval (exec-expr-pure ',loop-test compst))
              ((when (errorp test-eval)) (mv test-eval (compustate-fix compst)))
              (test-eval (apconvert-expr-value test-eval))
              ((when (errorp test-eval)) (mv test-eval (compustate-fix compst)))
              (test-val (expr-value->value test-eval))
              (continuep (test-value test-val))
              ((when (errorp continuep)) (mv continuep (compustate-fix compst)))
              ((when (not continuep))
               (mv (stmt-value-none) (compustate-fix compst)))
              ((mv sval compst) (exec-stmt ',loop-body compst fenv (1- limit)))
              ((when (errorp sval)) (mv sval compst))
              ((when (stmt-value-case sval :return)) (mv sval compst)))
           (,exec-stmt-while-for-fn compst (1- limit))))
       (exec-stmt-while-for-fn-hints
        '(("Goal" :in-theory '(acl2::zp-compound-recognizer
                               nfix
                               natp
                               o-p
                               o-finp
                               o<))))
       ((mv exec-stmt-while-for-fn-event &)
        (evmac-generate-defun
         exec-stmt-while-for-fn
         :formals (list 'compst 'limit)
         :body exec-stmt-while-for-fn-body
         :measure '(nfix limit)
         :well-founded-relation 'o<
         :hints exec-stmt-while-for-fn-hints
         :verify-guards nil
         :enable nil))
       (exec-stmt-while-for-fn-thm
        (add-suffix-to-fn exec-stmt-while-for-fn "-TO-EXEC-STMT-WHILE"))
       ((mv exec-stmt-while-for-fn-thm names-to-avoid)
        (fresh-logical-name-with-$s-suffix exec-stmt-while-for-fn-thm
                                           nil
                                           names-to-avoid
                                           wrld))
       ((mv exec-stmt-while-for-fn-thm-event &)
        (evmac-generate-defthm
         exec-stmt-while-for-fn-thm
         :formula `(equal (,exec-stmt-while-for-fn compst limit)
                          (exec-stmt-while ',loop-test
                                           ',loop-body
                                           compst
                                           (init-fun-env
                                            (preprocess ,prog-const))
                                           limit))
         :rule-classes nil
         :hints `(("Goal"
                   :induct (,exec-stmt-while-for-fn compst limit)
                   :in-theory '(,exec-stmt-while-for-fn
                                exec-stmt-while
                                valuep-when-value-optionp
                                value-optionp-of-stmt-value-return->value?
                                (:e valuep)))))))
    (mv (list exec-stmt-while-for-fn-event
              exec-stmt-while-for-fn-thm-event)
        exec-stmt-while-for-fn
        exec-stmt-while-for-fn-thm
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop-measure-thm ((fn symbolp)
                                  (fn-appconds symbol-symbol-alistp)
                                  (appcond-thms keyword-symbol-alistp)
                                  (measure-of-fn symbolp)
                                  (measure-formals symbol-listp)
                                  (names-to-avoid symbol-listp)
                                  (wrld plist-worldp))
  :guard (irecursivep+ fn wrld)
  :returns (mv (event pseudo-event-formp)
               (name symbolp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate type prescription theorem asserting that
          the measure of the recursive function @('fn')
          yields a natural number."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like the applicability condition,
     except that it uses the generated measure function
     (to treat the measure as a black box,
     as discussed in @(tsee atc-gen-loop-measure-fn)),
     and that it is a type prescription rule
     (which seems needed, as opposed a rewrite rule,
     based on proof experiments)."))
  (b* ((appcond-thm
        (cdr (assoc-eq (cdr (assoc-eq fn fn-appconds)) appcond-thms)))
       (natp-of-measure-of-fn-thm
        (packn-pos (list 'natp-of-measure-of- fn) fn))
       ((mv natp-of-measure-of-fn-thm names-to-avoid)
        (fresh-logical-name-with-$s-suffix natp-of-measure-of-fn-thm
                                           nil
                                           names-to-avoid
                                           wrld))
       ((mv natp-of-measure-of-fn-thm-event &)
        (evmac-generate-defthm
         natp-of-measure-of-fn-thm
         :formula `(natp (,measure-of-fn ,@measure-formals))
         :rule-classes :type-prescription
         :enable nil
         :hints `(("Goal"
                   :in-theory '(,measure-of-fn)
                   :use ,appcond-thm)))))
    (mv natp-of-measure-of-fn-thm-event
        natp-of-measure-of-fn-thm
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop-termination-thm ((fn symbolp)
                                      (measure-of-fn symbolp)
                                      (measure-formals symbol-listp)
                                      (natp-of-measure-of-fn-thm symbolp)
                                      (names-to-avoid symbol-listp)
                                      state)
  :guard (and (function-symbolp fn (w state))
              (logicp fn (w state))
              (irecursivep+ fn (w state))
              (not (eq measure-of-fn 'quote)))
  :returns (mv erp
               (event pseudo-event-formp)
               (name symbolp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate the version of the termination theorem
          tailored to the limits and measure function."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate a local theorem that is
     just like the termination theorem of the function
     except that @(tsee o<) is replaced with @(tsee <),
     and that the measure terms are abstracted to
     calls of the generated measure functions.
     The theorem is proved using the fact that
     the measure yields a natural number,
     which means that @(tsee o<) reduces to @(tsee <) (see above).
     The purpose of this variant of the termination theorem
     is to help establish the induction hypothesis
     in the loop correctness theorem, as explained below."))
  (b* (((reterr) '(_) nil nil)
       (wrld (w state))
       (termination-of-fn-thm
        (packn-pos (list 'termination-of- fn) fn))
       ((mv termination-of-fn-thm names-to-avoid)
        (fresh-logical-name-with-$s-suffix termination-of-fn-thm
                                           nil
                                           names-to-avoid
                                           wrld))
       (tthm (termination-theorem$ fn state))
       ((when (eq (car tthm) :failed))
        (reterr
         (raise "Internal error: cannot find termination theorem of ~x0." fn)))
       ((erp tthm-formula)
        (atc-gen-loop-tthm-formula tthm
                                   fn
                                   measure-of-fn
                                   measure-formals
                                   state))
       ((mv termination-of-fn-thm-event &)
        (evmac-generate-defthm
         termination-of-fn-thm
         :formula tthm-formula
         :rule-classes nil
         :hints `(("Goal"
                   :use ((:termination-theorem ,fn)
                         ,natp-of-measure-of-fn-thm)
                   :in-theory '(,measure-of-fn
                                acl2::natp-compound-recognizer
                                o-p
                                o-finp
                                o<))))))
    (retok termination-of-fn-thm-event
           termination-of-fn-thm
           names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atc-loop-body-term-subst
  :short "In a term that represents the body of a loop,
          replace each recursive call with
          a term that returns the affected variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is needed to express the correctness theorem for the loop body.
     The theorem needs to relate the execution of the loop body statement
     to the ACL2 term that represents it.
     However, the latter has recursive calls in it,
     which we therefore replace with terms
     that just return the affected variables.
     This ACL2 function does that.
     This gives us the appropriate ACL2 term
     to relate to the execution of the loop body statement,
     because the execution of the loop body statement
     just ends with the affected variables,
     i.e. it does not go back to the loop,
     which would be the equivalent of making the recursive call.")
   (xdoc::p
    "Note that we apply the substitution without regard to lambda variables,
     because we only use this ACL2 function on terms
     that satisfy the restrictions for loop body terms
     described in the user documentation.
     In particular, this means that the recursive calls
     are always on the formals of the loop function,
     and the affected variables also always have the same meaning."))

  (define atc-loop-body-term-subst ((term pseudo-termp)
                                    (fn symbolp)
                                    (affect symbol-listp))
    :returns (new-term pseudo-termp)
    :parents nil
    (b* (((when (member-eq (pseudo-term-kind term) '(:null :quote :var)))
          (pseudo-term-fix term))
         (fn/lam (pseudo-term-call->fn term))
         ((when (eq fn/lam fn))
          (if (consp (cdr affect))
              `(mv ,@(symbol-list-fix affect))
            (symbol-fix (car affect))))
         (args (pseudo-term-call->args term))
         (new-args (atc-loop-body-term-subst-lst args fn affect))
         (new-fn/lam (if (pseudo-lambda-p fn/lam)
                         (pseudo-lambda (pseudo-lambda->formals fn/lam)
                                        (atc-loop-body-term-subst
                                         (pseudo-lambda->body fn/lam)
                                         fn affect))
                       fn/lam)))
      (pseudo-term-call new-fn/lam new-args))
    :measure (pseudo-term-count term))

  (define atc-loop-body-term-subst-lst ((terms pseudo-term-listp)
                                        (fn symbolp)
                                        (affect symbol-listp))
    :returns (new-terms pseudo-term-listp)
    :parents nil
    (cond ((endp terms) nil)
          (t (cons (atc-loop-body-term-subst (car terms) fn affect)
                   (atc-loop-body-term-subst-lst (cdr terms) fn affect))))
    :measure (pseudo-term-list-count terms)
    ///
    (defret len-of-atc-loop-body-term-subst-lst
      (equal (len new-terms)
             (len terms))
      :hints (("Goal" :induct (len terms) :in-theory (enable len)))))

  :ruler-extenders :all

  :hints (("Goal" :in-theory (enable o< o-finp)))

  :returns-hints (("Goal" :in-theory (enable symbol-fix
                                             pseudo-termp)))

  :verify-guards nil ; done below
  ///
  (verify-guards atc-loop-body-term-subst
    :hints (("Goal" :in-theory (enable pseudo-fn-args-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop-test-correct-thm ((fn symbolp)
                                       (typed-formals atc-symbol-varinfo-alistp)
                                       (loop-test exprp)
                                       (test-term pseudo-termp)
                                       (fn-thms symbol-symbol-alistp)
                                       (prec-tags atc-string-taginfo-alistp)
                                       (prec-objs atc-string-objinfo-alistp)
                                       (names-to-avoid symbol-listp)
                                       state)
  :returns (mv (local-events pseudo-event-form-listp)
               (correct-test-thm symbolp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate the correctness theorem for the test of a loop."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a step towards generating more modular and controlled loop proofs.
     The hints are more than needed for now,
     as they include rules about statement execution,
     which does not apply here.
     We will make the hints more nuanced later.")
   (xdoc::p
    "We generate two conjuncts in the conclusion.
     One conjunct, as expected, says that
     executing the test yields the same as
     the ACL2 term @('test-term') that represents the test.
     Note that we need to wrap @(tsee exec-expr-pure) into @(tsee test-value),
     because the ACL2 term is boolean,
     and so we need to convert the C value to a boolean.
     The other conjunct says that @(tsee exec-expr-pure)
     does not return an error.
     This is needed in the generated proof for the whole loop,
     which equates the function generated
     by @(tsee atc-gen-exec-stmt-while-for-loop)
     to the execution of the loop:
     that function's body includes a check that @(tsee exec-expr-pure)
     does not yield an error,
     and so this other conjunct here serves to
     eliminate the case that that check fails."))
  (b* ((wrld (w state))
       (correct-thm (cdr (assoc-eq fn fn-thms)))
       (correct-test-thm (add-suffix-to-fn correct-thm "-TEST"))
       ((mv correct-test-thm names-to-avoid)
        (fresh-logical-name-with-$s-suffix correct-test-thm
                                           nil
                                           names-to-avoid
                                           wrld))
       (formals (strip-cars typed-formals))
       (compst-var (genvar$ 'atc "COMPST" nil formals state))
       ((mv formals-bindings hyps & instantiation)
        (atc-gen-outer-bindings-and-hyps typed-formals compst-var t prec-objs))
       (hyps `(and (compustatep ,compst-var)
                   (> (compustate-frames-number ,compst-var) 0)
                   ,@hyps
                   ,(untranslate$ (uguard+ fn wrld) nil state)))
       (concl `(and (not (errorp (exec-expr-pure ',loop-test ,compst-var)))
                    (not (errorp (apconvert-expr-value
                                  (exec-expr-pure ',loop-test ,compst-var))))
                    (equal (test-value
                            (expr-value->value
                             (apconvert-expr-value
                              (exec-expr-pure ',loop-test ,compst-var))))
                           ,test-term)))
       (formula `(b* (,@formals-bindings) (implies ,hyps ,concl)))
       (not-error-thms (atc-string-taginfo-alist-to-not-error-thms prec-tags))
       (valuep-thms (atc-string-taginfo-alist-to-valuep-thms prec-tags))
       (value-kind-thms (atc-string-taginfo-alist-to-value-kind-thms prec-tags))
       (struct-reader-return-thms
        (atc-string-taginfo-alist-to-reader-return-thms prec-tags))
       (member-read-thms
        (atc-string-taginfo-alist-to-member-read-thms prec-tags))
       (extobj-recognizers (atc-string-objinfo-alist-to-recognizers prec-objs))
       (hints `(("Goal"
                 :do-not-induct t
                 :in-theory (union-theories
                             (theory 'atc-all-rules)
                             '(not
                               not-errorp-when-expr-valuep
                               ,@not-error-thms
                               ,@valuep-thms
                               ,@value-kind-thms
                               ,@struct-reader-return-thms
                               ,@member-read-thms
                               ,@extobj-recognizers))
                 :use ((:instance (:guard-theorem ,fn)
                                  :extra-bindings-ok ,@(alist-to-doublets
                                                        instantiation)))
                 :expand :lambdas)))
       ((mv correct-test-thm-event &)
        (evmac-generate-defthm correct-test-thm
                               :formula formula
                               :hints hints
                               :enable nil)))
    (mv (list correct-test-thm-event)
        correct-test-thm
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop-final-compustate ((mod-vars symbol-listp)
                                       (typed-formals atc-symbol-varinfo-alistp)
                                       (subst symbol-symbol-alistp)
                                       (compst-var symbolp)
                                       (prec-objs atc-string-objinfo-alistp))
  :returns (term "An untranslated term.")
  :short "Generate a term representing the final computation state
          after the execution of a C loop."
  :long
  (xdoc::topstring
   (xdoc::p
    "The correctness theorem of a C loop says that
     executing the loop on a generic computation state
     (satisfying conditions in the hypotheses of the theorem)
     yields a computation state obtained by modifying
     one or more variables and zero or more arrays in the computation state.
     These are the variables and arrays affected by the loop,
     which the correctness theorem binds to the results of the loop function,
     and which have corresponding named variables and heap arrays
     in the computation state.
     The modified computation state is expressed as
     a nest of @(tsee write-var),
     @(tsee write-static-var),
     and @(tsee write-object) calls.
     This ACL2 code here generates that nest.")
   (xdoc::p
    "Note that, in the correctness theorem,
     the new array variables are bound to
     the possibly modified arrays returned by the ACL2 function:
     these new array variables are obtained by adding @('-NEW')
     to the corresponding formals of the ACL2 function;
     these new names should not cause any conflicts,
     because the names of the formals must be portable C identifiers."))
  (b* (((when (endp mod-vars)) compst-var)
       (mod-var (car mod-vars))
       (info (cdr (assoc-eq mod-var typed-formals)))
       ((when (not info))
        (raise "Internal error: formal ~x0 not found." mod-var))
       (type (atc-var-info->type info))
       (ptrp (or (type-case type :pointer)
                 (type-case type :array)))
       (ptr (cdr (assoc-eq mod-var subst))))
    (if ptrp
        (if (consp (assoc-equal (symbol-name mod-var) prec-objs))
            `(write-static-var (ident ,(symbol-name mod-var))
                               ,(add-suffix-to-fn mod-var "-NEW")
                               ,(atc-gen-loop-final-compustate (cdr mod-vars)
                                                               typed-formals
                                                               subst
                                                               compst-var
                                                               prec-objs))
          `(write-object (value-pointer->designator ,ptr)
                         ,(add-suffix-to-fn mod-var "-NEW")
                         ,(atc-gen-loop-final-compustate (cdr mod-vars)
                                                         typed-formals
                                                         subst
                                                         compst-var
                                                         prec-objs)))
      `(write-var (ident ,(symbol-name (car mod-vars)))
                  ,(add-suffix-to-fn (car mod-vars) "-NEW")
                  ,(atc-gen-loop-final-compustate (cdr mod-vars)
                                                  typed-formals
                                                  subst
                                                  compst-var
                                                  prec-objs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop-body-correct-thm ((fn symbolp)
                                       (typed-formals atc-symbol-varinfo-alistp)
                                       (affect symbol-listp)
                                       (loop-body stmtp)
                                       (test-term pseudo-termp)
                                       (body-term pseudo-termp)
                                       (prec-fns atc-symbol-fninfo-alistp)
                                       (prec-tags atc-string-taginfo-alistp)
                                       (prec-objs atc-string-objinfo-alistp)
                                       (prog-const symbolp)
                                       (fn-thms symbol-symbol-alistp)
                                       (limit pseudo-termp)
                                       (names-to-avoid symbol-listp)
                                       state)
  :returns (mv (local-events pseudo-event-form-listp)
               (correct-body-thm symbolp)
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate the correctness theorem for the body of a loop."
  :long
  (xdoc::topstring
   (xdoc::p
    "For the purpose of making the proofs generated by ATC more modular,
     we generate a separate local theorem for
     the correctness of each generated loop body;
     we plan to change the loop correctness theorem
     to make use of this theorem,
     instead of proving the whole loop, including its body."))
  (b* ((wrld (w state))
       (correct-thm (cdr (assoc-eq fn fn-thms)))
       (correct-body-thm (add-suffix-to-fn correct-thm "-BODY"))
       ((mv correct-body-thm names-to-avoid)
        (fresh-logical-name-with-$s-suffix correct-body-thm
                                           nil
                                           names-to-avoid
                                           wrld))
       (formals (formals+ fn wrld))
       (compst-var (genvar$ 'atc "COMPST" nil formals state))
       (fenv-var (genvar$ 'atc "FENV" nil formals state))
       (limit-var (genvar$ 'atc "LIMIT" nil formals state))
       ((mv formals-bindings hyps subst instantiation)
        (atc-gen-outer-bindings-and-hyps typed-formals compst-var t prec-objs))
       (diff-pointer-hyps
        (atc-gen-object-disjoint-hyps (strip-cdrs subst)))
       (hyps `(and (compustatep ,compst-var)
                   (> (compustate-frames-number ,compst-var) 0)
                   (equal ,fenv-var (init-fun-env (preprocess ,prog-const)))
                   (integerp ,limit-var)
                   (>= ,limit-var ,limit)
                   ,@hyps
                   ,@diff-pointer-hyps
                   ,(untranslate$ (uguard+ fn wrld) nil state)
                   ,(untranslate$ test-term nil state)))
       (affect-new (acl2::add-suffix-to-fn-lst affect "-NEW"))
       (affect-binder (if (endp (cdr affect-new))
                          (car affect-new)
                        `(mv ,@affect-new)))
       (final-compst (atc-gen-loop-final-compustate affect
                                                    typed-formals
                                                    subst
                                                    compst-var
                                                    prec-objs))
       (body-term (atc-loop-body-term-subst body-term fn affect))
       (concl `(equal (exec-stmt ',loop-body ,compst-var ,fenv-var ,limit-var)
                      (b* ((,affect-binder ,body-term))
                        (mv (stmt-value-none) ,final-compst))))
       (formula `(b* (,@formals-bindings) (implies ,hyps ,concl)))
       (called-fns (all-fnnames (ubody+ fn wrld)))
       (not-error-thms (atc-string-taginfo-alist-to-not-error-thms prec-tags))
       (valuep-thms (atc-string-taginfo-alist-to-valuep-thms prec-tags))
       (value-kind-thms (atc-string-taginfo-alist-to-value-kind-thms prec-tags))
       (result-thms
        (atc-symbol-fninfo-alist-to-result-thms prec-fns called-fns))
       (struct-reader-return-thms
        (atc-string-taginfo-alist-to-reader-return-thms prec-tags))
       (struct-writer-return-thms
        (atc-string-taginfo-alist-to-writer-return-thms prec-tags))
       (correct-thms
        (atc-symbol-fninfo-alist-to-correct-thms prec-fns called-fns))
       (measure-thms
        (atc-symbol-fninfo-alist-to-measure-nat-thms
         prec-fns (strip-cars prec-fns)))
       (type-prescriptions-called
        (loop$ for callable in (strip-cars prec-fns)
               collect `(:t ,callable)))
       (type-prescriptions-struct-readers
        (loop$ for reader in (atc-string-taginfo-alist-to-readers prec-tags)
               collect `(:t ,reader)))
       (type-of-value-thms
        (atc-string-taginfo-alist-to-type-of-value-thms prec-tags))
       (flexiblep-thms
        (atc-string-taginfo-alist-to-flexiblep-thms prec-tags))
       (member-read-thms
        (atc-string-taginfo-alist-to-member-read-thms prec-tags))
       (member-write-thms
        (atc-string-taginfo-alist-to-member-write-thms prec-tags))
       (extobj-recognizers (atc-string-objinfo-alist-to-recognizers prec-objs))
       (hints `(("Goal"
                 :do-not-induct t
                 :in-theory (union-theories
                             (theory 'atc-all-rules)
                             '(,@not-error-thms
                               ,@valuep-thms
                               ,@value-kind-thms
                               not
                               return-type-of-stmt-value-return
                               return-type-of-stmt-value-none
                               stmt-value-return->value?-of-stmt-value-return
                               stmt-value-return-of-value-option-fix-value?
                               (:e c::value-option-fix)
                               ,@struct-reader-return-thms
                               ,@struct-writer-return-thms
                               ,@type-of-value-thms
                               ,@flexiblep-thms
                               ,@member-read-thms
                               ,@member-write-thms
                               ,@type-prescriptions-called
                               ,@type-prescriptions-struct-readers
                               ,@extobj-recognizers
                               ,@result-thms
                               ,@correct-thms
                               ,@measure-thms))
                 :use ((:instance (:guard-theorem ,fn)
                                  :extra-bindings-ok
                                  ,@(alist-to-doublets instantiation)))
                 :expand :lambdas)))
       ((mv correct-body-thm-event &)
        (evmac-generate-defthm correct-body-thm
                               :formula formula
                               :hints hints
                               :enable nil)))
    (mv (list correct-body-thm-event)
        correct-body-thm
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop-correct-thm ((fn symbolp)
                                  (typed-formals atc-symbol-varinfo-alistp)
                                  (affect symbol-listp)
                                  (loop-test exprp)
                                  (loop-body stmtp)
                                  (prec-fns atc-symbol-fninfo-alistp)
                                  (prec-tags atc-string-taginfo-alistp)
                                  (prec-objs atc-string-objinfo-alistp)
                                  (prog-const symbolp)
                                  (fn-thms symbol-symbol-alistp)
                                  (fn-result-thm symbolp)
                                  (exec-stmt-while-for-fn symbolp)
                                  (exec-stmt-while-for-fn-thm symbolp)
                                  (termination-of-fn-thm symbolp)
                                  (natp-of-measure-of-fn-thm symbolp)
                                  (correct-test-thm symbolp)
                                  (correct-body-thm symbolp)
                                  (limit pseudo-termp)
                                  (names-to-avoid symbol-listp)
                                  state)
  :guard (irecursivep+ fn (w state))
  :returns (mv (events pseudo-event-form-listp)
               (print-event pseudo-event-formp)
               (fn-correct-thm symbolp :hyp (symbol-symbol-alistp fn-thms))
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate the correctness theorem for a C loop."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate the correctness theorem as a lemma first,
     then the actual theorem.
     The only difference between the two is that
     the lemma uses the specialization of @(tsee exec-stmt-while)
     that is generated as discussed above,
     while the theorem uses the general @(tsee exec-stmt-while);
     the reason is so we can have the right induction, as discussed above.
     As explained shortly,
     the formula involves (some of) the loop function's formals,
     so we take those into account to generate variables for
     the computation state, the function environment, and the limit.
     The hypotheses include the guard of the loop function,
     but we need to replace any pointers with their dereferenced arrays,
     and in addition we need to replace the parameters of the loop function
     with @(tsee read-var) calls that read the corresponding variables.
     The other hypotheses are the same as in @(tsee atc-gen-cfun-correct-thm),
     with the addition of a hypothesis that
     the number of frames in the computation state is not zero;
     this is always the case when executing a loop.
     The arguments of the loop function call are obtained by
     replacing its formals with the corresponding @(tsee read-var) calls.
     The lemma is proved via proof builder instructions,
     by first applying induction
     and then calling the prover on all the induction subgoals.
     For robustness, first we set the theory to contain
     just the specialized @(tsee exec-stmt-while),
     then we apply induction, which therefore must be on that function.
     The theory for the subgoal includes
     fewer rules than the ones for the full symbolic execution,
     because we use the correctness theorems for the loop test and body
     as rewrite rules instead, which take care of most of the execution.
     The @(':expand') hint applies to the loop function,
     for robustness (as ACL2's heuristics sometimes prevent
     the opening of recursive function definitions,
     but here we know that we always want to open it).
     The hints also include:
     (i) the return value theorem of the loop function,
     which is reasonable since the function is recursive,
     and so it is called inside its body;
     (ii) the definition of the specialized @(tsee exec-stmt-while);
     (iii) the rule saying that the measure yields a natural number; and
     (iv) the termination theorem of the loop function, suitably instantiated.
     Given the correctness lemma, the correctness theorem is easily proved,
     via the lemma and the generate theorem that equates
     the specialized @(tsee exec-stmt-while) to the general one.")
   (xdoc::p
    "Similarly to @(tsee atc-gen-cfun-correct-thm),
     we stage the proof of the lemma in two phases:
     see the documentation of that function for motivation."))
  (b* ((wrld (w state))
       (correct-thm (cdr (assoc-eq fn fn-thms)))
       (correct-lemma (add-suffix-to-fn correct-thm "-LEMMA"))
       ((mv correct-lemma names-to-avoid)
        (fresh-logical-name-with-$s-suffix correct-lemma
                                           nil
                                           names-to-avoid
                                           wrld))
       (formals (formals+ fn wrld))
       (compst-var (genvar$ 'atc "COMPST" nil formals state))
       (fenv-var (genvar$ 'atc "FENV" nil formals state))
       (limit-var (genvar$ 'atc "LIMIT" nil formals state))
       ((mv formals-bindings hyps subst instantiation)
        (atc-gen-outer-bindings-and-hyps typed-formals compst-var t prec-objs))
       (diff-pointer-hyps
        (atc-gen-object-disjoint-hyps (strip-cdrs subst)))
       (hyps `(and (compustatep ,compst-var)
                   (> (compustate-frames-number ,compst-var) 0)
                   (equal ,fenv-var
                          (init-fun-env (preprocess ,prog-const)))
                   (integerp ,limit-var)
                   (>= ,limit-var ,limit)
                   ,@hyps
                   ,@diff-pointer-hyps
                   ,(untranslate$ (uguard+ fn wrld) nil state)))
       (affect-new (acl2::add-suffix-to-fn-lst affect "-NEW"))
       (affect-binder (if (endp (cdr affect-new))
                          (car affect-new)
                        `(mv ,@affect-new)))
       (final-compst (atc-gen-loop-final-compustate affect
                                                    typed-formals
                                                    subst
                                                    compst-var
                                                    prec-objs))
       (concl-lemma `(equal (,exec-stmt-while-for-fn ,compst-var ,limit-var)
                            (b* ((,affect-binder (,fn ,@formals)))
                              (mv (stmt-value-none) ,final-compst))))
       (concl-thm `(equal (exec-stmt-while ',loop-test
                                           ',loop-body
                                           ,compst-var
                                           ,fenv-var
                                           ,limit-var)
                          (b* ((,affect-binder (,fn ,@formals)))
                            (mv (stmt-value-none) ,final-compst))))
       (formula-lemma `(b* (,@formals-bindings) (implies ,hyps ,concl-lemma)))
       (formula-thm `(b* (,@formals-bindings) (implies ,hyps ,concl-thm)))
       (called-fns (all-fnnames (ubody+ fn wrld)))
       (not-error-thms (atc-string-taginfo-alist-to-not-error-thms prec-tags))
       (valuep-thms (atc-string-taginfo-alist-to-valuep-thms prec-tags))
       (result-thms
        (atc-symbol-fninfo-alist-to-result-thms prec-fns called-fns))
       (result-thms (cons fn-result-thm result-thms))
       (struct-reader-return-thms
        (atc-string-taginfo-alist-to-reader-return-thms prec-tags))
       (struct-writer-return-thms
        (atc-string-taginfo-alist-to-writer-return-thms prec-tags))
       (correct-thms
        (atc-symbol-fninfo-alist-to-correct-thms prec-fns called-fns))
       (measure-thms
        (atc-symbol-fninfo-alist-to-measure-nat-thms
         prec-fns (strip-cars prec-fns)))
       (type-prescriptions-called
        (loop$ for callable in (strip-cars prec-fns)
               collect `(:t ,callable)))
       (type-prescriptions-struct-readers
        (loop$ for reader in (atc-string-taginfo-alist-to-readers prec-tags)
               collect `(:t ,reader)))
       (value-kind-thms (atc-string-taginfo-alist-to-value-kind-thms prec-tags))
       (type-of-value-thms
        (atc-string-taginfo-alist-to-type-of-value-thms prec-tags))
       (flexiblep-thms
        (atc-string-taginfo-alist-to-flexiblep-thms prec-tags))
       (member-read-thms
        (atc-string-taginfo-alist-to-member-read-thms prec-tags))
       (member-write-thms
        (atc-string-taginfo-alist-to-member-write-thms prec-tags))
       (extobj-recognizers (atc-string-objinfo-alist-to-recognizers prec-objs))
       (lemma-hints `(("Goal"
                       :do-not-induct t
                       :in-theory (append
                                   *atc-symbolic-computation-state-rules*
                                   *atc-valuep-rules*
                                   *atc-value-listp-rules*
                                   *atc-value-optionp-rules*
                                   *atc-type-of-value-rules*
                                   *atc-type-of-value-option-rules*
                                   *atc-value-array->elemtype-rules*
                                   *atc-array-length-rules*
                                   *atc-array-length-write-rules*
                                   *atc-other-executable-counterpart-rules*
                                   *atc-wrapper-rules*
                                   *atc-distributivity-over-if-rewrite-rules*
                                   *atc-identifier-rules*
                                   *atc-integer-size-rules*
                                   *atc-limit-rules*
                                   *atc-not-error-rules*
                                   *atc-integer-ops-1-return-rewrite-rules*
                                   *atc-integer-ops-2-return-rewrite-rules*
                                   *atc-integer-convs-return-rewrite-rules*
                                   *atc-array-read-return-rewrite-rules*
                                   *atc-array-write-return-rewrite-rules*
                                   *atc-misc-rewrite-rules*
                                   *atc-computation-state-return-rules*
                                   *atc-boolean-from-integer-return-rules*
                                   *atc-type-prescription-rules*
                                   *atc-compound-recognizer-rules*
                                   *integer-value-disjoint-rules*
                                   *array-value-disjoint-rules*
                                   *atc-value-fix-rules*
                                   *atc-flexible-array-member-rules*
                                   '(,@not-error-thms
                                     ,@valuep-thms
                                     ,@value-kind-thms
                                     not
                                     ,exec-stmt-while-for-fn
                                     ,@struct-reader-return-thms
                                     ,@struct-writer-return-thms
                                     ,@type-of-value-thms
                                     ,@flexiblep-thms
                                     ,@member-read-thms
                                     ,@member-write-thms
                                     ,@type-prescriptions-called
                                     ,@type-prescriptions-struct-readers
                                     ,@result-thms
                                     ,@correct-thms
                                     ,@measure-thms
                                     ,natp-of-measure-of-fn-thm
                                     ,@extobj-recognizers
                                     ,correct-test-thm
                                     ,correct-body-thm
                                     apconvert-expr-value-when-not-value-array
                                     value-kind-when-ucharp
                                     value-kind-when-scharp
                                     value-kind-when-ushortp
                                     value-kind-when-sshortp
                                     value-kind-when-uintp
                                     value-kind-when-sintp
                                     value-kind-when-ulongp
                                     value-kind-when-slongp
                                     value-kind-when-ullongp
                                     value-kind-when-sllongp
                                     expr-value-fix-when-expr-valuep))
                       :use ((:instance (:guard-theorem ,fn)
                                        :extra-bindings-ok ,@(alist-to-doublets
                                                              instantiation))
                             (:instance ,termination-of-fn-thm
                                        :extra-bindings-ok ,@(alist-to-doublets
                                                              instantiation))))
                      (and stable-under-simplificationp
                           '(:in-theory
                             (append
                              *atc-symbolic-computation-state-rules*
                              *atc-valuep-rules*
                              *atc-value-listp-rules*
                              *atc-value-optionp-rules*
                              *atc-type-of-value-rules*
                              *atc-type-of-value-option-rules*
                              *atc-value-array->elemtype-rules*
                              *atc-array-length-rules*
                              *atc-array-length-write-rules*
                              *atc-other-executable-counterpart-rules*
                              *atc-wrapper-rules*
                              *atc-distributivity-over-if-rewrite-rules*
                              *atc-identifier-rules*
                              *atc-integer-size-rules*
                              *atc-limit-rules*
                              *atc-not-error-rules*
                              *atc-integer-ops-1-return-rewrite-rules*
                              *atc-integer-ops-2-return-rewrite-rules*
                              *atc-integer-convs-return-rewrite-rules*
                              *atc-array-read-return-rewrite-rules*
                              *atc-array-write-return-rewrite-rules*
                              *atc-misc-rewrite-rules*
                              *atc-computation-state-return-rules*
                              *atc-boolean-from-integer-return-rules*
                              *atc-type-prescription-rules*
                              *atc-compound-recognizer-rules*
                              *integer-value-disjoint-rules*
                              *array-value-disjoint-rules*
                              *atc-value-fix-rules*
                              *atc-flexible-array-member-rules*
                              '(,@not-error-thms
                                ,@valuep-thms
                                ,@value-kind-thms
                                not
                                stmt-value-return->value?-of-stmt-value-return
                                (:e value-option-fix)
                                not-errorp-when-stmt-valuep
                                return-type-of-stmt-value-return
                                return-type-of-stmt-value-none
                                ,exec-stmt-while-for-fn
                                ,@struct-reader-return-thms
                                ,@struct-writer-return-thms
                                ,@type-of-value-thms
                                ,@flexiblep-thms
                                ,@member-read-thms
                                ,@member-write-thms
                                ,@type-prescriptions-called
                                ,@type-prescriptions-struct-readers
                                ,@result-thms
                                ,@correct-thms
                                ,@measure-thms
                                ,natp-of-measure-of-fn-thm
                                ,@extobj-recognizers
                                ,correct-test-thm
                                ,correct-body-thm
                                apconvert-expr-value-when-not-value-array
                                value-kind-when-ucharp
                                value-kind-when-scharp
                                value-kind-when-ushortp
                                value-kind-when-sshortp
                                value-kind-when-uintp
                                value-kind-when-sintp
                                value-kind-when-ulongp
                                value-kind-when-slongp
                                value-kind-when-ullongp
                                value-kind-when-sllongp
                                expr-value-fix-when-expr-valuep))
                             :expand (:lambdas
                                      (,fn ,@(fsublis-var-lst
                                              instantiation
                                              formals)))))))
       (lemma-instructions
        `((:in-theory '(,exec-stmt-while-for-fn))
          (:induct (,exec-stmt-while-for-fn ,compst-var ,limit-var))
          (:repeat (:prove :hints ,lemma-hints))))
       (thm-hints `(("Goal"
                     :in-theory nil
                     :use (,correct-lemma ,exec-stmt-while-for-fn-thm))))
       ((mv correct-lemma-event &)
        (evmac-generate-defthm correct-lemma
                               :formula formula-lemma
                               :instructions lemma-instructions
                               :enable nil))
       ((mv correct-thm-local-event correct-thm-exported-event)
        (evmac-generate-defthm correct-thm
                               :formula formula-thm
                               :hints thm-hints
                               :enable nil))
       (print-event `(cw-event "~%~x0~|" ',correct-thm-exported-event)))
    (mv (list correct-lemma-event
              correct-thm-local-event
              correct-thm-exported-event)
        print-event
        correct-thm
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-loop ((fn symbolp)
                      (prec-fns atc-symbol-fninfo-alistp)
                      (prec-tags atc-string-taginfo-alistp)
                      (prec-objs atc-string-objinfo-alistp)
                      (proofs booleanp)
                      (prog-const symbolp)
                      (fn-thms symbol-symbol-alistp)
                      (fn-appconds symbol-symbol-alistp)
                      (appcond-thms keyword-symbol-alistp)
                      (print evmac-input-print-p)
                      (names-to-avoid symbol-listp)
                      state)
  :guard (and (function-symbolp fn (w state))
              (logicp fn (w state))
              (irecursivep+ fn (w state))
              (not (eq fn 'quote)))
  :returns (mv erp
               (events pseudo-event-form-listp)
               (updated-prec-fns atc-symbol-fninfo-alistp
                                 :hyp (and (symbolp fn)
                                           (atc-symbol-fninfo-alistp prec-fns))
                                 :hints (("Goal" :in-theory (enable acons))))
               (updated-names-to-avoid symbol-listp
                                       :hyp (symbol-listp names-to-avoid)))
  :short "Generate a C loop from a recursive ACL2 function,
          with accompanying theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called if @('fn') is a recursive target function.
     We process the function body as a loop term,
     and update the @('prec-fns') alist with information about the function.")
   (xdoc::p
    "We also generate the measure function for @('fn') here.
     See @(tsee atc-gen-loop-measure-fn).")
   (xdoc::p
    "No C external declaration is generated for this function,
     because this function just represents a loop used in oher functions.")
   (xdoc::p
    "For now we do not generate a guard function for the guard of @('fn');
     also, we do not generate theorems for the formal parameters for now.
     We will change this soon."))
  (b* (((reterr) nil nil nil)
       (wrld (w state))
       ((mv measure-of-fn-event
            measure-of-fn
            measure-formals
            names-to-avoid)
        (if proofs
            (atc-gen-loop-measure-fn fn names-to-avoid state)
          (mv '(_) nil nil names-to-avoid)))
       ((mv fn-guard-event
            fn-guard
            names-to-avoid)
        (atc-gen-fn-guard fn names-to-avoid state))
       ((erp typed-formals formals-events names-to-avoid)
        (atc-typed-formals fn fn-guard prec-tags prec-objs names-to-avoid wrld))
       (body (ubody+ fn wrld))
       ((erp (lstmt-gout loop))
        (atc-gen-loop-stmt body
                           (make-lstmt-gin :context (make-atc-context
                                                     :preamble nil
                                                     :premises nil)
                                           :typed-formals typed-formals
                                           :inscope (list typed-formals)
                                           :fn fn
                                           :fn-guard nil
                                           :compst-var nil
                                           :fenv-var nil
                                           :limit-var nil
                                           :measure-for-fn measure-of-fn
                                           :measure-formals measure-formals
                                           :prec-fns prec-fns
                                           :prec-tags prec-tags
                                           :prec-objs prec-objs
                                           :thm-index 1
                                           :names-to-avoid names-to-avoid
                                           :proofs nil)
                           state))
       (names-to-avoid loop.names-to-avoid)
       ((erp events
             natp-of-measure-of-fn-thm
             fn-result-thm
             fn-correct-thm
             names-to-avoid)
        (if proofs
            (b* (((reterr) nil nil nil nil nil)
                 ((mv fn-result-events
                      fn-result-thm
                      names-to-avoid)
                  (atc-gen-fn-result-thm fn
                                         nil
                                         loop.affect
                                         typed-formals
                                         prec-fns
                                         prec-tags
                                         prec-objs
                                         names-to-avoid
                                         state))
                 (loop-test (stmt-while->test loop.stmt))
                 (loop-body (stmt-while->body loop.stmt))
                 ((mv exec-stmt-while-events
                      exec-stmt-while-for-fn
                      exec-stmt-while-for-fn-thm
                      names-to-avoid)
                  (atc-gen-exec-stmt-while-for-loop fn
                                                    loop.stmt
                                                    prog-const
                                                    names-to-avoid
                                                    wrld))
                 ((mv natp-of-measure-of-fn-thm-event
                      natp-of-measure-of-fn-thm
                      names-to-avoid)
                  (atc-gen-loop-measure-thm fn
                                            fn-appconds
                                            appcond-thms
                                            measure-of-fn
                                            measure-formals
                                            names-to-avoid
                                            wrld))
                 ((erp termination-of-fn-thm-event
                       termination-of-fn-thm
                       names-to-avoid)
                  (atc-gen-loop-termination-thm fn
                                                measure-of-fn
                                                measure-formals
                                                natp-of-measure-of-fn-thm
                                                names-to-avoid
                                                state))
                 ((mv test-local-events
                      correct-test-thm
                      names-to-avoid)
                  (atc-gen-loop-test-correct-thm fn
                                                 typed-formals
                                                 loop-test
                                                 loop.test-term
                                                 fn-thms
                                                 prec-tags
                                                 prec-objs
                                                 names-to-avoid
                                                 state))
                 ((mv body-local-events
                      correct-body-thm
                      names-to-avoid)
                  (atc-gen-loop-body-correct-thm fn
                                                 typed-formals
                                                 loop.affect
                                                 loop-body
                                                 loop.test-term
                                                 loop.body-term
                                                 prec-fns
                                                 prec-tags
                                                 prec-objs
                                                 prog-const
                                                 fn-thms
                                                 loop.limit-body
                                                 names-to-avoid
                                                 state))
                 ((mv correct-events
                      print-event
                      fn-correct-thm
                      names-to-avoid)
                  (atc-gen-loop-correct-thm fn
                                            typed-formals
                                            loop.affect
                                            loop-test
                                            loop-body
                                            prec-fns
                                            prec-tags
                                            prec-objs
                                            prog-const
                                            fn-thms
                                            fn-result-thm
                                            exec-stmt-while-for-fn
                                            exec-stmt-while-for-fn-thm
                                            termination-of-fn-thm
                                            natp-of-measure-of-fn-thm
                                            correct-test-thm
                                            correct-body-thm
                                            loop.limit-all
                                            names-to-avoid
                                            state))
                 (progress-start?
                  (and (evmac-input-print->= print :info)
                       `((cw-event "~%Generating the proofs for ~x0..." ',fn))))
                 (progress-end? (and (evmac-input-print->= print :info)
                                     `((cw-event " done.~%"))))
                 (print-result?
                  (and (evmac-input-print->= print :result)
                       (list print-event)))
                 (events (append progress-start?
                                 (list fn-guard-event)
                                 formals-events
                                 loop.events
                                 (and measure-of-fn
                                      (list measure-of-fn-event))
                                 fn-result-events
                                 exec-stmt-while-events
                                 (list natp-of-measure-of-fn-thm-event)
                                 (list termination-of-fn-thm-event)
                                 test-local-events
                                 body-local-events
                                 correct-events
                                 progress-end?
                                 print-result?)))
              (retok events
                     natp-of-measure-of-fn-thm
                     fn-result-thm
                     fn-correct-thm
                     names-to-avoid))
          (retok nil nil nil nil names-to-avoid)))
       (info (make-atc-fn-info :out-type nil
                               :in-types (atc-var-info-list->type-list
                                          (strip-cdrs typed-formals))
                               :loop? loop.stmt
                               :affect loop.affect
                               :extobjs nil ; TODO
                               :result-thm fn-result-thm
                               :correct-thm fn-correct-thm
                               :correct-mod-thm nil
                               :measure-nat-thm natp-of-measure-of-fn-thm
                               :fun-env-thm nil
                               :limit loop.limit-all
                               :guard nil))) ; <- not used for now
    (retok events
           (acons fn info prec-fns)
           names-to-avoid))
  :prepwork
  ((local
    (in-theory
     (enable
      acl2::true-listp-when-pseudo-event-form-listp-rewrite
      alistp-when-atc-symbol-varinfo-alistp-rewrite
      atc-var-info-listp-of-strip-cdrs-when-atc-symbol-varinfo-alistp
      iff-consp-when-true-listp)))))
