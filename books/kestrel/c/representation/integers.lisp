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

(include-book "../language/integer-ranges")

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/typed-lists/atom-listp" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

;; to have FTY::DEFLIST generate theorems about NTH:
(local (include-book "std/lists/nth" :dir :system))

;; to have FTY::DEFLIST generate theorems about UPDATE-NTH:
(local (include-book "std/lists/update-nth" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ representation-of-integers
  :parents (representation)
  :short "A representation of C integers in ACL2."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is part of the "
    (xdoc::seetopic "representation" "shallow embedding")
    ".")
   (xdoc::p
    "We define a representation of
     the C standard signed and unsigned integer values,
     except @('_Bool') for now,
     based on their "
    (xdoc::seetopic "integer-formats-definitions" "format definitions")
    " and "
    (xdoc::seetopic "integer-ranges" "range definitions")
    ". As mentioned in the documentation of the integer formats,
     the definitions of values we give here
     should still work if the format definitions are changed.")
   (xdoc::p
    "For each C integer type covered by our representation,
     we define the C values as wrappers of ACL2 integers in appropriate ranges.
     We also define lists of these C values,
     and some operations between these lists
     and lists of ACL2 integers in the corresponding ranges.")
   (xdoc::p
    "For the unsigned types,
     we also introduce ACL2 functions
     to turn ACL2 integers into values of those types
     by reducing them modulo one plus the maximum value of the type.
     These functions are used
     to define certain C integer conversions and operations,
     which are modular for unsigned integer types.")
   (xdoc::p
    "This representation of C integers in ACL2 should be treated like
     abstract data types whose definition is opaque.
     Consider the representation of @('unsigned char'), for instance.
     The exact definition of @(tsee ucharp) does not matter.
     What matters is that the set of ACL2 values that satisfy that predicate
     is isomorphic to the set of ACL2 integers
     that satisfy @(tsee uchar-integerp);
     the isomorphisms between the two sets are
     @(tsee integer-from-uchar) and @(tsee uchar-from-integer).
     The fixer @(tsee uchar-fix) should be treated opaquely too.
     There should be sufficient theorems
     that capture the isomorphism property
     and that support reasoning about these C integers in ACL2
     independently from their representation.
     On the other hand, @(tsee uchar-integerp) is not opaque:
     it is a known set of ACL2 integers, and that matters for reasoning.
     As a practical issue, @(tsee uchar-integerp-alt-def),
     which as the name suggests is like an alternative definition,
     is generally more convenient than the actual definition,
     because the latter involves powers of two and bit sizes,
     while the alternate definition involves minima and maxima.
     As another practical issue, it is generally unnecessary
     to enable the fixer @(tsee uchar-integer-fix),
     which exposes @(tsee uchar-integerp),
     which therefore needs to be enabled anyways;
     there is a theorem that simplifies away @(tsee uchar-integer-fix)
     when @(tsee uchar-integerp) holds,
     so enabling @(tsee uchar-integerp-alt-def) should normally suffice.
     Even with the aforementioned isomorphisms disabled,
     their executable counterparts are enabled (per ACL2's defaults),
     exposing the internal representation in some constant cases;
     we may consider keeping those executable counterparts disabled too."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *nonchar-integer-fixtypes*
  :short "List of the fixtype names of
          the (supported) C integer types except plain @('char')."
  (list 'schar
        'uchar
        'sshort
        'ushort
        'sint
        'uint
        'slong
        'ulong
        'sllong
        'ullong)
  ///
  (assert-event (no-duplicatesp-eq *nonchar-integer-fixtypes*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-type-to-fixtype ((type typep))
  :guard (type-nonchar-integerp type)
  :returns (fixtype symbolp)
  :short "Name of the fixtype of the values of a C integer type."
  :long
  (xdoc::topstring-p
   "This is the symbol in the @('\"C\"') package
    with the same name as the keyword kind of the type
    (e.g. it is @('uchar') for @('(type-uchar)')).")
  (intern$ (symbol-name (type-kind type)) "C")
  :hooks (:fix)
  ///

  (defret integer-type-to-fixtype-in-list-or-nil
    (or (member-eq fixtype *nonchar-integer-fixtypes*)
        (null fixtype))
    :hyp (type-nonchar-integerp type)
    :rule-classes nil
    :hints (("Goal" :in-theory (enable type-nonchar-integerp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fixtype-to-integer-type ((fixtype symbolp))
  :returns (type type-optionp)
  :short "Integer type corresponding to a fixtype name, if any."
  (case fixtype
    (schar (type-schar))
    (uchar (type-uchar))
    (sshort (type-sshort))
    (ushort (type-ushort))
    (sint (type-sint))
    (uint (type-uint))
    (slong (type-slong))
    (ulong (type-ulong))
    (sllong (type-sllong))
    (ullong (type-ullong))
    (t nil))
  ///

  (defret type-nonchar-integerp-of-fixtype-to-integer-type
    (implies type
             (type-nonchar-integerp type)))

  (defret type-arithmeticp-of-fixtype-to-integer-type
    (implies type
             (type-arithmeticp type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection integer-type-to/from-fixtype-theorems
  :short "Inversion theorems about the mappings between
          integer types and fixtype symbols."

  (defrule fixtype-to-integer-type-of-integer-type-to-fixtype
    (implies (type-nonchar-integerp type)
             (equal (fixtype-to-integer-type (integer-type-to-fixtype type))
                    (type-fix type)))
    :enable (fixtype-to-integer-type
             integer-type-to-fixtype
             type-nonchar-integerp))

  (defrule integer-type-to-fixtype-of-fixtype-to-integer-type
    (implies (member-eq fixtype *nonchar-integer-fixtypes*)
             (equal (integer-type-to-fixtype (fixtype-to-integer-type fixtype))
                    fixtype))
    :enable (fixtype-to-integer-type
             integer-type-to-fixtype)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-integer-values ((type typep))
  :guard (type-nonchar-integerp type)
  :returns (event pseudo-event-formp)
  :short "Event to generate the model of the values of a C integer type."

  (b* ((type-string (integer-type-xdoc-string type))
       (signedp (type-signed-integerp type))
       (<type> (integer-type-to-fixtype type))
       (<type>p (pack <type> 'p))
       (<type>-fix (pack <type> '-fix))
       (<type>-fix-when-<type>p (pack <type>-fix '-when- <type>p))
       (<type>-equiv (pack <type> '-equiv))
       (<type>-integer (pack <type> '-integer))
       (<type>-integerp (pack <type>-integer 'p))
       (<type>-integerp-alt-def (pack <type>-integerp '-alt-def))
       (<type>-integer-list (pack <type>-integer '-list))
       (<type>-integer-listp (pack <type>-integer-list 'p))
       (<type>-integer-list-fix (pack <type>-integer-list '-fix))
       (<type>-integer-fix (pack <type>-integer '-fix))
       (<type>-max (pack <type> '-max))
       (<type>-min (pack <type> '-min))
       (integer-from-<type> (pack 'integer-from- <type>))
       (<type>-from-integer (pack <type> '-from-integer))
       (<type>-from-integer-of-integer-from-<type>
        (pack <type>-from-integer '-of- integer-from-<type>))
       (integer-from-<type>-of-<type>-from-integer
        (pack integer-from-<type> '-of- <type>-from-integer))
       (equal-of-<type>-from-integer (pack 'equal-of- <type>-from-integer))
       (consp-when-<type>p (pack 'consp-when- <type>p))
       (<type>-list (pack <type> '-list))
       (<type>-listp (pack <type>-list 'p))
       (<type>-list-fix (pack <type>-list '-fix))
       (integer-list-from-<type>-list (pack 'integer-list-from- <type>-list))
       (<type>-list-from-integer-list (pack <type>-list '-from-integer-list))
       (<type>-list-from-integer-list-of-integer-list-from-<type>-list
        (pack <type>-list-from-integer-list
              '-of-
              integer-list-from-<type>-list))
       (integer-list-from-<type>-list-of-<type>-list-from-integer-list
        (pack integer-list-from-<type>-list
              '-of-
              <type>-list-from-integer-list))
       (<type>-from-integer-mod (pack <type>-from-integer '-mod))
       (true-listp-when-<type>-listp-rewrite (pack 'true-listp-when-
                                                   <type>-listp
                                                   '-rewrite)))

    `(progn

       ,@(and (type-case type :char)
              (raise "Type ~x0 not supported." type))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (define ,<type>p (x)
         :returns (yes/no booleanp)
         :short ,(str::cat "Recognizer of values of " type-string ".")
         (and (consp x)
              (eq (car x) ,(type-kind type))
              (true-listp (cdr x))
              (eql (len (cdr x)) 1)
              (b* ((get (std::da-nth 0 (cdr x))))
                (,<type>-integerp get)))
         ///
         (defrule ,consp-when-<type>p
           (implies (,<type>p x)
                    (consp x))
           :rule-classes :compound-recognizer))

       (define ,<type>-fix ((x ,<type>p))
         :returns (fixed-x ,<type>p)
         :short ,(str::cat "Fixer for values of " type-string ".")
         (mbe :logic (b* ((get (,<type>-integer-fix (std::da-nth 0 (cdr x)))))
                       (cons ,(type-kind type) (list get)))
              :exec x)
         :prepwork ((local (in-theory (enable ,<type>p))))
         ///
         (defrule ,<type>-fix-when-<type>p
           (implies (,<type>p x)
                    (equal (,<type>-fix x)
                           x))))

       (defsection ,<type>
         :short ,(str::cat "Fixtype of values of " type-string ".")
         (fty::deffixtype ,<type>
           :pred ,<type>p
           :fix ,<type>-fix
           :equiv ,<type>-equiv
           :define t
           :topic ,<type>p))

       (define ,<type>-from-integer ((get ,<type>-integerp))
         :returns (y ,<type>p
                     :hints (("Goal" :in-theory (enable ,<type>p))))
         :short ,(str::cat "Constructor for values of " type-string ".")
         (b* ((get (mbe :logic (,<type>-integer-fix get)
                        :exec get)))
           (cons ,(type-kind type) (list get)))
         :hooks (:fix))

       (define ,integer-from-<type> ((x ,<type>p))
         :returns (y ,<type>-integerp)
         :short ,(str::cat "Accessor for values of " type-string ".")
         (mbe :logic (b* ((x (and t x)))
                       (,<type>-integer-fix (std::da-nth 0 (cdr x))))
              :exec (std::da-nth 0 (cdr x)))
         :prepwork ((local (in-theory (enable ,<type>p ,<type>-fix))))
         :hooks (:fix)
         ///

         (defrule ,<type>-from-integer-of-integer-from-<type>
           (equal (,<type>-from-integer (,integer-from-<type> x))
                  (,<type>-fix x))
           :enable (,<type>-from-integer ,<type>-fix))

         (defrule ,integer-from-<type>-of-<type>-from-integer
           (equal (,integer-from-<type> (,<type>-from-integer get))
                  (,<type>-integer-fix get))
           :enable ,<type>-from-integer)

         (defrule ,(pack integer-from-<type> '-upper-bound)
           (<= (,integer-from-<type> x) (,<type>-max))
           :rule-classes :linear
           :enable (,integer-from-<type>
                    ,<type>-integer-fix
                    ,<type>-integerp-alt-def))

         ,@(and
            signedp
            `((defrule ,(pack integer-from-<type> '-lower-bound)
                (>= (,integer-from-<type> x) (,<type>-min))
                :rule-classes :linear
                :enable (,integer-from-<type>
                         ,<type>-integer-fix
                         ,<type>-integerp-alt-def)))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defruled ,equal-of-<type>-from-integer
         (equal (equal (,<type>-from-integer get) x)
                (and (,<type>p x)
                     (equal (,integer-from-<type> x)
                            (,<type>-integer-fix get))))
         :enable (,<type>-from-integer ,<type>p ,integer-from-<type>))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       ,@(and
          (not signedp)
          `((define ,<type>-from-integer-mod ((x integerp))
              :returns (result ,<type>p)
              :short ,(str::cat "Reduce modularly ACL2 integers to values of "
                                type-string
                                ".")
              (,<type>-from-integer (mod (ifix x) (1+ (,<type>-max))))
              :guard-hints (("Goal"
                             :in-theory (enable ,<type>-integerp-alt-def)))
              :hooks (:fix))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (fty::deflist ,<type>-list
         :short ,(str::cat "Fixtype of lists of values of " type-string ".")
         :elt-type ,<type>
         :true-listp t
         :elementp-of-nil nil
         :pred ,<type>-listp
         :prepwork ((local (in-theory (enable nfix))))
         ///
         (defruled ,true-listp-when-<type>-listp-rewrite
           (implies (,<type>-listp x)
                    (true-listp x))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (std::defprojection ,integer-list-from-<type>-list
         ((x ,<type>-listp))
         :returns (result ,<type>-integer-listp)
         :short ,(str::cat "Lift @(tsee "
                           (str::downcase-string
                            (symbol-name integer-from-<type>))
                           ") to lists.")
         (,integer-from-<type> x)
         ///
         (fty::deffixequiv ,integer-list-from-<type>-list))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (std::defprojection ,<type>-list-from-integer-list
         ((x ,<type>-integer-listp))
         :returns (result ,<type>-listp)
         :short ,(str::cat "Lift @(tsee "
                           (str::downcase-string (symbol-name <type>))
                           ") to lists.")
         (,<type>-from-integer x)
         ///
         (fty::deffixequiv ,<type>-list-from-integer-list))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defrule ,<type>-list-from-integer-list-of-integer-list-from-<type>-list
         (equal (,<type>-list-from-integer-list
                 (,integer-list-from-<type>-list x))
                (,<type>-list-fix x))
         :induct t
         :enable (,integer-list-from-<type>-list
                  ,<type>-list-from-integer-list))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defrule ,integer-list-from-<type>-list-of-<type>-list-from-integer-list
         (equal (,integer-list-from-<type>-list
                 (,<type>-list-from-integer-list x))
                (,<type>-integer-list-fix x))
         :induct t
         :enable (,integer-list-from-<type>-list
                  ,<type>-list-from-integer-list))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       ))

  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-integer-values-loop ((types type-listp))
  :guard (type-nonchar-integer-listp types)
  :returns (events pseudo-event-form-listp)
  :short "Events to generate the models of the values of some C integer types."
  (cond ((endp types) nil)
        (t (cons (def-integer-values (car types))
                 (def-integer-values-loop (cdr types)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(progn ,@(def-integer-values-loop *nonchar-integer-types*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defflatsum cinteger
  :short "Fixtype of all the supported C integer types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the union of
     the C integer types listed in @(tsee *nonchar-integer-fixtypes*)."))
  (:schar schar)
  (:uchar uchar)
  (:sshort sshort)
  (:ushort ushort)
  (:sint sint)
  (:uint uint)
  (:slong slong)
  (:ulong ulong)
  (:sllong sllong)
  (:ullong ullong)
  :pred cintegerp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-from-cinteger ((cint cintegerp))
  :returns (int integerp)
  :short "ACL2 integer corresponding to the C integer."
  (cinteger-case cint
                 :schar (integer-from-schar cint.get)
                 :uchar (integer-from-uchar cint.get)
                 :sshort (integer-from-sshort cint.get)
                 :ushort (integer-from-ushort cint.get)
                 :sint (integer-from-sint cint.get)
                 :uint (integer-from-uint cint.get)
                 :slong (integer-from-slong cint.get)
                 :ulong (integer-from-ulong cint.get)
                 :sllong (integer-from-sllong cint.get)
                 :ullong (integer-from-ullong cint.get))
  :hooks (:fix)
  ///

  (defruled integer-from-cinteger-alt-def
    (equal (integer-from-cinteger x)
           (cond ((scharp x) (integer-from-schar x))
                 ((ucharp x) (integer-from-uchar x))
                 ((sshortp x) (integer-from-sshort x))
                 ((ushortp x) (integer-from-ushort x))
                 ((sintp x) (integer-from-sint x))
                 ((uintp x) (integer-from-uint x))
                 ((slongp x) (integer-from-slong x))
                 ((ulongp x) (integer-from-ulong x))
                 ((sllongp x) (integer-from-sllong x))
                 (t (integer-from-ullong x))))
    :enable (integer-from-cinteger
             cinteger-kind
             cinteger-schar->get
             cinteger-uchar->get
             cinteger-sshort->get
             cinteger-ushort->get
             cinteger-sint->get
             cinteger-uint->get
             cinteger-slong->get
             cinteger-ulong->get
             cinteger-sllong->get
             cinteger-ullong->get)))
