; Fixtypes of Unsigned and Signed Byte Lists -- Generator
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
(include-book "defbyte")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defbytelist

  :parents (acl2::kestrel-utilities
            fty
            defbyte
            acl2::unsigned-byte-listp
            acl2::signed-byte-p)

  :short "Introduce <see topic='@(url fty)'>fixtypes</see> for
          true lists of unsigned or signed bytes of a specified size."

  :long

  (xdoc::topapp

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
     but it also generates various theorems that relate
     the unary recognizers for lists of bytes
     to the aforementioned binary predicates for lists of bytes,
     and to other built-in predicates.")

   (xdoc::p
    "Besides their use in fixtypes,
     the unary recognizers introduced by this macro support
     <see topic='@(url acl2::tau-system)'>tau system</see> reasoning.")

   (xdoc::h3 "General Form")

   (xdoc::code
    "(defbytelist byte"
    "             :type ..."
    "             :pred ..."
    "             :fix ..."
    "             :equiv ..."
    "             :parents ..."
    "             :long ..."
    "  )")

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@('byte')"
    (xdoc::p
     "A symbol that names a fixtype previously introduced via @(tsee defbyte).
      This is the type of the elements of the generated list type."))

   (xdoc::desc
    "@(':type')"
    (xdoc::p
     "A symbol that specifies the name of the fixtype.
      If this is @('nil') (the default),
      the name of the type is @('<byte>-list'),
      where @('<byte>') is the name of the element type,
      as specified via the @('byte') input."))

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
     "A list of symbols to use as XDOC parents of the generated fixtype,
      in addition to the XDOC topic for the element type.
      The default is @('nil'), i.e. just the XDOC topic for the element type.
      All the other generated XDOC topics are (directly or indirectly)
      under the XDOC topic for this generated fixtype."))

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

   (xdoc::h3 "Generated Events")

   (xdoc::p
    "The following are generated, inclusive of XDOC documentation:")

   (xdoc::ul

    (xdoc::li
     "A call of @(tsee fty::deflist) to generate the fixtype.")

    (xdoc::li
     "Forward chaining rules
      from the unary recognizers to the binary predicates
      @(tsee acl2::unsigned-byte-listp) and @(tsee acl2::signed-byte-listp).
      These rules can combine with
      forward chaining rules from the binary predicates.")

    (xdoc::li
     "Rules that rewrite between the binary predicate and the unary recognizer.
      These rules are disabled by default, but may be useful in some proofs.
      Since these are converse rules,
      a theory invariant is also generated preventing the enabling of both.")

    (xdoc::li
     "A rule to prove @(tsee true-listp) from the unary recognizer.
      Since @(tsee true-listp) is relatively common,
      this rule is disabled by default for efficiency."))

   (xdoc::p
    "See the implementation, which uses a readable backquote notation,
     for details.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::defxdoc+ defbytelist-implementation
  :parents (defbytelist)
  :short "Implementation of @(tsee defbytelist)."
  :order-subtopics t
  :default-parent t)

(define defbytelist-fn (byte
                        type
                        pred
                        fix
                        equiv
                        parents
                        long
                        (wrld plist-worldp))
  :returns (event "A @(tsee acl2::maybe-pseudo-event-formp).")
  :mode :program
  :short "Event generated by the @(tsee defbytelist) macro."
  (b* (;; validate the BYTE input:
       ((unless (symbolp byte))
        (raise "The BYTE input must be a symbol,
                but it is ~x0 instead." byte))
       (table (table-alist *defbyte-table-name* wrld))
       (pair (assoc-eq byte table))
       ((unless pair)
        (raise "The ~x0 input must name a type ~
                previously introduced via DEFBYTE, ~
                but this is not the case." byte))
       ;; retrieve the necessary information from the DEFBYTE table:
       (info (cdr pair))
       (size (defbyte-info->size info))
       (signed (defbyte-info->signed info))
       (bytep (defbyte-info->pred info))
       (description (defbyte-info->description info))
       ;; validate the other inputs:
       ((unless (symbolp type))
        (raise "The :TYPE input must be a symbol, ~
                but it is ~x0 instead." type))
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
       ((unless (acl2::maybe-stringp long))
        (raise "The :LONG input must be a string or NIL, ~
                but it is ~x0 instead." long))
       ;; name of the binary predicate:
       (binpred (if signed 'acl2::signed-byte-listp 'acl2::unsigned-byte-listp))
       ;; name of the generated fixtype:
       (type (or type (acl2::add-suffix-to-fn byte "-LIST")))
       ;; names of the generated functions:
       (pred (or pred (acl2::add-suffix-to-fn type "-P")))
       (fix (or fix (acl2::add-suffix-to-fn type "-FIX")))
       (equiv (or equiv (acl2::add-suffix-to-fn type "-EQUIV")))
       ;; names of the generated theorems:
       (pred-forward-binpred (acl2::packn (list pred '-forward- binpred)))
       (pred-rewrite-binpred (acl2::packn (list pred '-rewrite- binpred)))
       (binpred-rewrite-pred (acl2::packn-pos (list binpred '-rewrite- pred)
                                              (pkg-witness
                                               (symbol-package-name pred))))
       (true-listp-when-pred-rewrite (acl2::packn-pos (list 'true-listp-when-
                                                            pred
                                                            '-rewrite)
                                                      (pkg-witness
                                                       (symbol-package-name
                                                        pred))))
       ;; XDOC topic name for the generated theorems:
       (type-theorems (acl2::add-suffix-to-fn type "-THEOREMS")))
    ;; generated events:
    `(encapsulate
       ()
       (fty::deflist ,type
         :elt-type ,byte
         :parents (,@parents ,byte)
         :short ,(concatenate 'string
                              "<see topic='@(url acl2::fty)'>Fixtype</see> of "
                              "true lists of "
                              description
                              ".")
         ,@(and long `(:long ,long))
         :true-listp t
         :pred ,pred
         :fix ,fix
         :equiv ,equiv)
       (defsection ,type-theorems
         :extension ,type
         (defrule ,pred-forward-binpred
           (implies (,pred x)
                    (,binpred ,size x))
           :rule-classes :forward-chaining
           :enable (,pred ,bytep))
         (defruled ,pred-rewrite-binpred
           (equal (,pred x)
                  (,binpred ,size x))
           :enable (,pred ,bytep))
         (defruled ,binpred-rewrite-pred
           (equal (,binpred ,size x)
                  (,pred x))
           :enable ,pred-rewrite-binpred)
         (theory-invariant
          (incompatible (:rewrite ,pred-rewrite-binpred)
                        (:rewrite ,binpred-rewrite-pred)))
         (defruled ,true-listp-when-pred-rewrite
           (implies (,pred x)
                    (true-listp x)))))))

(defsection defbytelist-macro-definition
  :short "Definition of the @(tsee defbytelist) macro."
  :long "@(def defbytelist)"
  (defmacro defbytelist (byte
                         &key
                         type
                         pred
                         fix
                         equiv
                         parents
                         long)
    `(make-event (defbytelist-fn
                   ',byte
                   ',type
                   ',pred
                   ',fix
                   ',equiv
                   ',parents
                   ,long
                   (w state)))))
