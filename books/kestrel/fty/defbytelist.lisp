; FTY -- Byte List Fixtype Generator
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)
(include-book "std/typed-lists/signed-byte-listp" :dir :system)
(include-book "std/util/deflist" :dir :system)

(include-book "defbyte")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defbytelist

  :parents (fty-extensions
            fty
            defbyte
            acl2::unsigned-byte-listp
            acl2::signed-byte-p)

  :short "Introduce a <see topic='@(url fty)'>fixtype</see> of
          true lists of unsigned or signed bytes of a specified size."

  :long

  (xdoc::topstring

   (xdoc::h3 "Introduction")

   (xdoc::p
    "Currently fixtypes can only be associated to unary predicates,
     but @(tsee acl2::unsigned-byte-listp) and @(tsee acl2::signed-byte-listp)
     are binary predicates.")

   (xdoc::p
    "This macro introduces unary recognizers, and associated fixtypes,
     of true lists of values
     of fixtypes previously introduced via @(tsee defbyte).
     This macro uses @(tsee fty::deflist) to introduce the list fixtype,
     but it also generates various theorems,
     including some that relate
     the unary recognizers for lists of bytes
     to the aforementioned binary predicates for lists of bytes.")

   (xdoc::p
    "Besides their use in fixtypes,
     the unary recognizers introduced by this macro support
     <see topic='@(url acl2::tau-system)'>tau system</see> reasoning.")

   (xdoc::h3 "General Form")

   (xdoc::codeblock
    "(defbytelist type"
    "             :elt-type"
    "             :pred ..."
    "             :fix ..."
    "             :equiv ..."
    "             :parents ..."
    "             :short ..."
    "             :long ..."
    "  )")

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@('type')"
    (xdoc::p
     "A symbol that specifies the name of the fixtype."))

   (xdoc::desc
    "@(':elt-type')"
    (xdoc::p
     "A symbol that names a fixtype previously introduced via @(tsee defbyte).
      This is the fixtype of the elements of the generated list fixtype.")
    (xdoc::p
     "This input must be supplied; there is no default."))

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
    "@('type')"
    (xdoc::p
     "A call of @(tsee fty::deflist) to generate the fixtype."))

   (xdoc::desc
    "@('pred-forward-binpred')"
    (xdoc::p
     "A forward chaining rule from @('pred')
      to the corresponding binary predicate
      @(tsee acl2::unsigned-byte-listp) or @(tsee acl2::signed-byte-listp)."))

   (xdoc::desc
    "@('binpred-rewrite-pred')
     <br/>
     @('pred-rewrite-binpred')"
    (xdoc::p
     "Rule that rewrite between @('pred') and
      the corresponding binary predicate
      @(tsee acl2::unsigned-byte-listp) or @(tsee acl2::signed-byte-listp).
      These rules are disabled by default, but may be useful in some proofs.
      Since these are converse rules,
      a theory invariant is also generated preventing the enabling of both."))

   (xdoc::desc
    "@('true-listp-when-pred')"
    (xdoc::p
     "A rule to prove @(tsee true-listp) from @('pred').
      Since @(tsee true-listp) is relatively common,
      this rule is disabled by default for efficiency."))

   (xdoc::desc
    "@('fix-of-take')"
    (xdoc::p
     "A rule to rewrite @('fix') applied to @(tsee take)."))

   (xdoc::desc
    "@('fix-of-rcons')"
    (xdoc::p
     "A rule to rewrite @('fix') applied to @(tsee rcons)."))

   (xdoc::p
    "The above items are generated with XDOC documentation.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::defxdoc+ defbytelist-implementation
  :parents (defbytelist)
  :short "Implementation of @(tsee defbytelist)."
  :order-subtopics t
  :default-parent t)

(define defbytelist-fn (type
                        elt-type
                        pred
                        fix
                        equiv
                        parents
                        short
                        long
                        (wrld plist-worldp))
  :returns (event "A @(tsee acl2::maybe-pseudo-event-formp).")
  :mode :program
  :short "Events generated by @(tsee defbytelist)."
  :long
  (xdoc::topstring-p
   "For now we only perform partial validation of the inputs.
    Future implementations may perform a more thorough validation.")
  (b* (;; validate the TYPE input:
       ((unless (symbolp type))
        (raise "The TYPE input must be a symbol, ~
                but it is ~x0 instead." type))
       ;; validate the :ELT-TYPE input:
       ((unless (symbolp elt-type))
        (raise "The :ELT-TYPE input must be a symbol,
                but it is ~x0 instead." elt-type))
       (defbyte-table (table-alist *defbyte-table-name* wrld))
       (defbyte-pair (assoc-eq elt-type defbyte-table))
       ((unless defbyte-pair)
        (raise "The :ELT-TYPE input ~x0 must name a type ~
                previously introduced via DEFBYTE, ~
                but this is not the case." elt-type))
       ;; retrieve size and signedness from the DEFBYTE table:
       (defbyte-info (cdr defbyte-pair))
       (size (defbyte-info->size defbyte-info))
       (signed (defbyte-info->signed defbyte-info))
       ;; retrieve element type recognizer and fixer from the fixtype table:
       (fty-table (get-fixtypes-alist wrld))
       (fty-info (find-fixtype elt-type fty-table))
       (bytep (fixtype->pred fty-info))
       (byte-fix (fixtype->fix fty-info))
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
       (binpred (if signed 'acl2::signed-byte-listp 'acl2::unsigned-byte-listp))
       ;; package for the generated theorem and variable names:
       (pkg (symbol-package-name type))
       (pkg (if (equal pkg *main-lisp-package-name*) "ACL2" pkg))
       (pkg-witness (pkg-witness pkg))
       ;; names of the generated functions:
       (pred (or pred (acl2::add-suffix-to-fn type "-P")))
       (fix (or fix (acl2::add-suffix-to-fn type "-FIX")))
       (equiv (or equiv (acl2::add-suffix-to-fn type "-EQUIV")))
       ;; names of the generated theorems:
       (pred-forward-binpred (acl2::packn-pos (list pred '-forward- binpred)
                                              pkg-witness))
       (pred-rewrite-binpred (acl2::packn-pos (list pred '-rewrite- binpred)
                                              pkg-witness))
       (binpred-rewrite-pred (acl2::packn-pos (list binpred '-rewrite- pred)
                                              pkg-witness))
       (true-listp-when-pred-rewrite (acl2::packn-pos (list 'true-listp-when-
                                                            pred
                                                            '-rewrite)
                                                      pkg-witness))
       (fix-of-take (acl2::packn-pos (list fix '-of-take) pkg-witness))
       (fix-of-rcons (acl2::packn-pos (list fix '-of-rcons) pkg-witness))
       ;; variables to use in the generated functions and theorems:
       (x (intern-in-package-of-symbol "X" pkg-witness))
       (a (intern-in-package-of-symbol "A" pkg-witness))
       (n (intern-in-package-of-symbol "N" pkg-witness))
       ;; XDOC topic for the generated theorems:
       (type-theorems (acl2::add-suffix-to-fn type "-THEOREMS"))
       ;; generated events:
       (deflist-event
         `(fty::deflist ,type
            :elt-type ,elt-type
            ,@(and parents (list :parents parents))
            ,@(and short (list :short short))
            ,@(and long (list :long long))
            :true-listp t
            :elementp-of-nil nil
            :pred ,pred
            :fix ,fix
            :equiv ,equiv))
       (theorems-event
        `(defsection ,type-theorems
           :extension ,type
           (defrule ,pred-forward-binpred
             (implies (,pred ,x)
                      (,binpred ,size ,x))
             :rule-classes :forward-chaining
             :in-theory '(,pred ,bytep ,binpred))
           (defruled ,pred-rewrite-binpred
             (equal (,pred ,x)
                    (,binpred ,size ,x))
             :in-theory '(,pred ,bytep ,binpred))
           (defruled ,binpred-rewrite-pred
             (equal (,binpred ,size ,x)
                    (,pred ,x))
             :in-theory '(,pred-rewrite-binpred))
           (theory-invariant
            (incompatible (:rewrite ,pred-rewrite-binpred)
                          (:rewrite ,binpred-rewrite-pred)))
           (defruled ,true-listp-when-pred-rewrite
             (implies (,pred ,x)
                      (true-listp ,x))
             :in-theory '(,pred true-listp))
           (defrule ,fix-of-take
             (implies (<= (nfix ,n) (len ,x))
                      (equal (,fix (take ,n ,x))
                             (take ,n (,fix ,x))))
             :in-theory '(,fix
                          ,(acl2::add-suffix-to-fn fix "-OF-CONS")
                          nfix
                          zp
                          len
                          take
                          acl2::take-of-cons))
           (defrule ,fix-of-rcons
             (equal (,fix (rcons ,a ,x))
                    (rcons (,byte-fix ,a) (,fix ,x)))
             :in-theory '(,fix
                          ,(acl2::add-suffix-to-fn fix "-OF-CONS")
                          ,(acl2::add-suffix-to-fn fix "-OF-APPEND")
                          acl2::binary-append-without-guard
                          rcons)))))
    ;; top-level event:
    `(encapsulate
       ()
       (logic)
       ,deflist-event
       (set-default-hints nil)
       (set-override-hints nil)
       ,theorems-event)))

(defsection defbytelist-macro-definition
  :short "Definition of the @(tsee defbytelist) macro."
  :long "@(def defbytelist)"
  (defmacro defbytelist (type
                         &key
                         elt-type
                         pred
                         fix
                         equiv
                         parents
                         short
                         long)
    `(make-event (defbytelist-fn
                   ',type
                   ',elt-type
                   ',pred
                   ',fix
                   ',equiv
                   ',parents
                   ,short
                   ,long
                   (w state)))))
