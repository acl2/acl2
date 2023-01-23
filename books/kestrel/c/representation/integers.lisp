; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../language/integer-ranges")

(local (include-book "arithmetic-3/top" :dir :system))
(local (include-book "std/lists/len" :dir :system))

;; to have FTY::DEFLIST generate theorems about NTH:
(local (include-book "std/lists/nth" :dir :system))

;; to have FTY::DEFLIST generate theorems about UPDATE-NTH:
(local (include-book "std/lists/update-nth" :dir :system))

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
    (xdoc::seetopic "integer-formats" "format definitions")
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
     which are modular for unsigned integer types."))
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
       (<type>->get (pack <type> '->get))
       (<type>-of-fields (pack <type> '-of-fields))
       (<type>->get-of-<type> (pack <type>->get '-of- <type>))
       (equal-of-<type> (pack 'equal-of- <type>))
       (consp-when-<type>p (pack 'consp-when- <type>p))
       (<type>-list (pack <type> '-list))
       (<type>-listp (pack <type>-list 'p))
       (<type>-list-fix (pack <type>-list '-fix))
       (<type>-integer-list-from-<type>-list (pack <type>-integer-list
                                                   '-from-
                                                   <type>-list))
       (<type>-list-from-<type>-integer-list (pack <type>-list
                                                   '-from-
                                                   <type>-integer-list))
       (<type>-list-from-<type>-integer-list-from-<type>-list
        (pack <type>
              '-list-from-
              <type>
              '-integer-list-from-
              <type>
              '-list))
       (<type>-integer-list-from-<type>-list-from-<type>-integer-list
        (pack <type>
              '-integer-list-from-
              <type>
              '-list-from-
              <type>
              '-integer-list))
       (<type>-mod (pack <type> '-mod))
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

       (fty::deffixtype ,<type>
         :pred ,<type>p
         :fix ,<type>-fix
         :equiv ,<type>-equiv
         :define t
         :topic ,<type>p)

       (define ,<type> ((get ,<type>-integerp))
         :returns (y ,<type>p
                     :hints (("Goal" :in-theory (enable ,<type>p))))
         :short ,(str::cat "Constructor for values of " type-string ".")
         :long
         (xdoc::topstring
          (xdoc::p
           ,(str::cat
             "This is also the name of the fixtype of values of "
             type-string ".")))
         (b* ((get (mbe :logic (,<type>-integer-fix get)
                        :exec get)))
           (cons ,(type-kind type) (list get)))
         :hooks (:fix))

       (define ,<type>->get ((x ,<type>p))
         :returns (y ,<type>-integerp)
         :short ,(str::cat "Accessor for values of " type-string ".")
         (mbe :logic (b* ((x (and t x)))
                       (,<type>-integer-fix (std::da-nth 0 (cdr x))))
              :exec (std::da-nth 0 (cdr x)))
         :prepwork ((local (in-theory (enable ,<type>p ,<type>-fix))))
         :hooks (:fix)
         ///

         (defrule ,<type>-of-fields
           (equal (,<type> (,<type>->get x))
                  (,<type>-fix x))
           :enable (,<type> ,<type>-fix))

         (defrule ,<type>->get-of-<type>
           (equal (,<type>->get (,<type> get))
                  (,<type>-integer-fix get))
           :enable ,<type>)

         (defrule ,(pack <type>->get '-upper-bound)
           (<= (,<type>->get x) (,<type>-max))
           :rule-classes :linear
           :enable (,<type>->get
                    ,<type>-integer-fix
                    ,<type>-integerp-alt-def))

         ,@(and
            signedp
            `((defrule ,(pack <type>->get '-lower-bound)
                (>= (,<type>->get x) (,<type>-min))
                :rule-classes :linear
                :enable (,<type>->get
                         ,<type>-integer-fix
                         ,<type>-integerp-alt-def)))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defruled ,equal-of-<type>
         (equal (equal (,<type> get) x)
                (and (,<type>p x)
                     (equal (,<type>->get x)
                            (,<type>-integer-fix get))))
         :enable (,<type> ,<type>p ,<type>->get))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       ,@(and
          (not signedp)
          `((define ,<type>-mod ((x integerp))
              :returns (result ,<type>p)
              :short ,(str::cat "Reduce modularly ACL2 integers to values of "
                                type-string
                                ".")
              (,<type> (mod (ifix x) (1+ (,<type>-max))))
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
         ///
         (defruled ,true-listp-when-<type>-listp-rewrite
           (implies (,<type>-listp x)
                    (true-listp x))))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (std::defprojection ,<type>-integer-list-from-<type>-list
         ((x ,<type>-listp))
         :returns (result ,<type>-integer-listp)
         :short ,(str::cat "Lift @(tsee "
                           (str::downcase-string (symbol-name <type>->get))
                           ") to lists.")
         (,<type>->get x)
         ///
         (fty::deffixequiv ,<type>-integer-list-from-<type>-list))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (std::defprojection ,<type>-list-from-<type>-integer-list
         ((x ,<type>-integer-listp))
         :returns (result ,<type>-listp)
         :short ,(str::cat "Lift @(tsee "
                           (str::downcase-string (symbol-name <type>))
                           ") to lists.")
         (,<type> x)
         ///
         (fty::deffixequiv ,<type>-list-from-<type>-integer-list))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defrule ,<type>-list-from-<type>-integer-list-from-<type>-list
         (equal (,<type>-list-from-<type>-integer-list
                 (,<type>-integer-list-from-<type>-list x))
                (,<type>-list-fix x))
         :enable (,<type>-integer-list-from-<type>-list
                  ,<type>-list-from-<type>-integer-list))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (defrule ,<type>-integer-list-from-<type>-list-from-<type>-integer-list
         (equal (,<type>-integer-list-from-<type>-list
                 (,<type>-list-from-<type>-integer-list x))
                (,<type>-integer-list-fix x))
         :enable (,<type>-integer-list-from-<type>-list
                  ,<type>-list-from-<type>-integer-list))

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
