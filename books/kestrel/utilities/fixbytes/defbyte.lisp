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
          unsigned or signed bytes of a given size and true lists thereof."

  :long

  (xdoc::topapp

   (xdoc::h3 "Introduction")

   (xdoc::p
    "Currently fixtypes can only be associated to unary predicates,
     but @(tsee unsigned-byte-p) and @(tsee signed-byte-p) are binary predicates
     (as are @(tsee unsigned-byte-listp) and @(tsee signed-byte-listp)).")

   (xdoc::p
    "This macro introduces unary predicates, and associated fixtypes,
     for unsigned or signed bytes of specified sizes,
     as well as for true lists thereof.
     It also generates various theorems that relate the unary predicates
     to the binary predicates and to other built-in predicates.")

   (xdoc::h3 "General Form")

   (xdoc::code "(defbyte size")
   (xdoc::code "         :signed ...")
   (xdoc::code "  )")

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@('size')"
    (xdoc::p
     "A positive integer that specifies the bit size of the bytes."))

   (xdoc::desc
    "@(':signed')"
    (xdoc::p
     "A boolean that specifies whether the bytes are
      unsigned (@('nil'), the default) or signed (@('t'))."))

   (xdoc::h3 "Generated Functions and Theorems")

   (xdoc::p
    "The following are generated, inclusive of XDOC documentation:")

   (xdoc::ul

    (xdoc::li
     "A unary recognizer, a fixer, an equivalence, and a fixtype
      for unsigned or signed bytes of the specified size.")

    (xdoc::li
     "A recognizer, a fixer, an equivalence, and a fixtype
      for true lists of unsigned or signed bytes of the specified size.")

    (xdoc::li
     "Forward chaining rules from the unary predicates to the binary predicates,
      which can combine with
      forward chaining rules from the binary predicates.")

    (xdoc::li
     "A rule that rewrites the binary predicate for unsigned or signed bytes
      to the unary predicate for unsigned or signed bytes.
      This rule is disabled by default, but may be useful in some proofs.
      Since this is the converse of the definition of the unary predicate,
      a theory invariant is also generated preventing the enabling of
      both this rule and the definition of the unary predicate.")

    (xdoc::li
     "Rules that rewrite between
      the binary predicate for lists of unsigned or signed bytes
      and the unary predicate for lists of unsigned or signed bytes.
      These rules are disabled by default, but may be useful in some proofs.
      Since these are converse rules,
      a theory invariant is also generated preventing the enabling of both.")

    (xdoc::li
     "A rule to prove @(tsee true-listp)
      from the unary predicate of lists of unsigned or signed bytes.
      Since @(tsee true-listp) is relatively common,
      this rule is disabled by default for efficiency."))

   (xdoc::p
    "See the implementation, which uses a readable backquote notation,
     for details.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defbyte-fn (size signed)
  :returns (event (or (pseudo-event-formp event)
                      (null event))
                  ;; just to speed up the proof:
                  :hints (("Goal" :in-theory (disable packn))))
  :parents nil
  :verify-guards nil
  (b* (((unless (posp size))
        (raise "The first argument must be a positive integer, ~
                but it is ~x0 instead." size))
       ((unless (booleanp signed))
        (raise "The :SIGNED argument must be a boolean, ~
                but it is ~x0 instead." signed))
       (n size) ; shorter
       (byte (if signed 'sbyte 'ubyte))
       (byte-p (if signed 'signed-byte-p 'unsigned-byte-p))
       (byte-listp (if signed 'signed-byte-listp 'unsigned-byte-listp))
       (byte<n> (packn (list byte n)))
       (byte<n>p (packn (list byte<n> 'p)))
       (byte<n>-fix (packn (list byte<n> '-fix)))
       (byte<n>-equiv (packn (list byte<n> '-equiv)))
       (byte<n>-fix-when-byte<n>p (packn (list byte<n>-fix
                                               '-when-
                                               byte<n>p)))
       (byte<n>-list (packn (list byte<n> '-list)))
       (byte<n>-listp (packn (list byte<n>-list 'p)))
       (byte<n>p-forward-byte-p (packn (list byte<n>p
                                             '-forward-
                                             byte-p)))
       (byte<n>-listp-forward-byte-listp (packn (list byte<n>-listp
                                                      '-forward-
                                                      byte-listp)))
       (byte-p-rewrite-byte<n>p (packn (list byte-p '-rewrite- byte<n>p)))
       (byte<n>-listp-rewrite-byte-listp (packn (list byte<n>-listp
                                                      '-rewrite-
                                                      byte-listp)))
       (byte-listp-rewrite-byte<n>-listp (packn (list byte-listp
                                                      '-rewrite-
                                                      byte<n>-listp)))
       (true-listp-when-byte<n>-listp-rewrite (packn (list 'true-listp-when-
                                                           byte<n>-listp
                                                           '-rewrite)))
       (byte<n>-list-theorems (packn (list byte<n>-list '-theorems)))
       (<n>string (coerce (explode-nonnegative-integer n 10 nil) 'string))
       (unsigned/signed-string (if signed "signed" "unsigned"))
       (ubyte/sbyte-string (if signed "sbyte" "ubyte")))
    `(progn
       (define ,byte<n>p (x)
         :returns (yes/no booleanp)
         :parents (defbyte)
         :short ,(concatenate 'string
                              "Recognize "
                              unsigned/signed-string
                              " bytes of size "
                              <n>string
                              ".")
         (,byte-p ,n x)
         :no-function t
         ///
         (defrule ,byte<n>p-forward-byte-p
           (implies (,byte<n>p x)
                    (,byte-p ,n x))
           :rule-classes :forward-chaining)
         (defruled ,byte-p-rewrite-byte<n>p
           (equal (,byte-p ,n x)
                  (,byte<n>p x)))
         (theory-invariant
          (incompatible (:rewrite ,byte-p-rewrite-byte<n>p)
                        (:definition ,byte<n>p))))
       (define ,byte<n>-fix ((x ,byte<n>p))
         :returns (fixed-x ,byte<n>p)
         :parents (defbyte)
         :short ,(concatenate 'string
                              "Fixing function for @(tsee "
                              ubyte/sbyte-string
                              <n>string
                              "p).")
         (mbe :logic (if (,byte<n>p x) x 0)
              :exec x)
         :no-function t
         ///
         (defrule ,byte<n>-fix-when-byte<n>p
           (implies (,byte<n>p x)
                    (equal (,byte<n>-fix x) x))
           :enable ,byte<n>p))
       (defsection ,byte<n>
         :parents (defbyte)
         :short ,(concatenate 'string
                              "<see topic='@(url fty)'>Fixtype</see> of "
                              unsigned/signed-string
                              " bytes of size "
                              <n>string
                              ".")
         (fty::deffixtype ,byte<n>
           :pred ,byte<n>p
           :fix ,byte<n>-fix
           :equiv ,byte<n>-equiv
           :define t
           :forward t))
       (fty::deflist ,byte<n>-list
         :elt-type ,byte<n>
         :parents (defbyte)
         :short ,(concatenate 'string
                              "<see topic='@(url fty)'>Fixtype</see> of "
                              "true lists of "
                              unsigned/signed-string
                              " bytes of size "
                              <n>string
                              ".")
         :true-listp t
         :pred ,byte<n>-listp)
       (defsection ,byte<n>-list-theorems
         :extension ,byte<n>-list
         (defrule ,byte<n>-listp-forward-byte-listp
           (implies (,byte<n>-listp x)
                    (,byte-listp ,n x))
           :rule-classes :forward-chaining
           :enable (,byte<n>-listp ,byte<n>p))
         (defruled ,byte<n>-listp-rewrite-byte-listp
           (equal (,byte<n>-listp x)
                  (,byte-listp ,n x))
           :enable (,byte<n>-listp ,byte<n>p))
         (defruled ,byte-listp-rewrite-byte<n>-listp
           (equal (,byte-listp ,n x)
                  (,byte<n>-listp x))
           :enable ,byte<n>-listp-rewrite-byte-listp)
         (theory-invariant
          (incompatible (:rewrite ,byte<n>-listp-rewrite-byte-listp)
                        (:rewrite ,byte-listp-rewrite-byte<n>-listp)))
         (defruled ,true-listp-when-byte<n>-listp-rewrite
           (implies (,byte<n>-listp x)
                    (true-listp x)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro defbyte (n &key signed)
  `(make-event (defbyte-fn ',n ',signed)))
