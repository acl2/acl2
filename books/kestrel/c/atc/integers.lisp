; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../language/integer-ranges")

(local (include-book "arithmetic-3/top" :dir :system))

;; to have FTY::DEFLIST generate theorems about NTH:
(local (include-book "std/lists/nth" :dir :system))

;; to have FTY::DEFLIST generate theorems about UPDATE-NTH:
(local (include-book "std/lists/update-nth" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-integers
  :parents (atc-shallow-embedding)
  :short "A model of C integers for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a model of the C standard signed and unsigned integer values,
     except @('_Bool') for now,
     based on their "
    (xdoc::seetopic "integer-formats" "format definitions")
    " and "
    (xdoc::seetopic "integer-ranges" "range definitions")
    ". As mentioned in the documentation of the integer formats,
     the definitions of values we give here
     should still work if the format definitions are changed.")
   (xdoc::p
    "For each C integer type covered by our model,
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-type-to-fixtype ((type typep))
  :guard (type-integerp type)
  :returns (fixtype symbolp)
  :short "Name of the fixtype of the values of a C integer type."
  :long
  (xdoc::topstring-p
   "This is the symbol in the @('\"C\"') package
    with the same name as the keyword kind of the type
    (e.g. it is @('uchar') for @('(type-uchar)')).")
  (intern$ (symbol-name (type-kind type)) "C")
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-def-integer-values ((type typep))
  :guard (type-integerp type)
  :returns (event pseudo-event-formp)
  :short "Event to generate the model of the values of a C integer type."

  (b* ((type-string (integer-type-xdoc-string type))
       (signedp (type-signed-integerp type))
       (<type> (integer-type-to-fixtype type))
       (<type>p (pack <type> 'p))
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
       (<type>-mod (pack <type> '-mod)))

    `(progn

       ,@(and (type-case type :char)
              (raise "Type ~x0 not supported." type))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (fty::defprod ,<type>
         :short ,(str::cat "Fixtype of values of " type-string ".")
         ((get ,<type>-integer))
         :tag ,(type-kind type)
         :layout :list
         :pred ,<type>p
         ///

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

       (define ,<type>-mod ((x integerp))
         :returns (result ,<type>p)
         :short ,(str::cat "Reduce modularly ACL2 integers to values of "
                           type-string
                           ".")
         (,<type> (mod (ifix x) (1+ (,<type>-max))))
         :guard-hints (("Goal" :in-theory (enable ,<type>-integerp-alt-def)))
         :hooks (:fix))

       ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

       (fty::deflist ,<type>-list
         :short ,(str::cat "Fixtype of lists of values of " type-string ".")
         :elt-type ,<type>
         :true-listp t
         :elementp-of-nil nil
         :pred ,<type>-listp)

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

(define atc-def-integer-values-loop ((types type-listp))
  :guard (type-integer-listp types)
  :returns (events pseudo-event-form-listp)
  :short "Events to generate the models of the values of some C integer types."
  (cond ((endp types) nil)
        (t (cons (atc-def-integer-values (car types))
                 (atc-def-integer-values-loop (cdr types)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(progn ,@(atc-def-integer-values-loop *integer-nonbool-nonchar-types*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

  (defret type-integerp-of-fixtype-to-integer-type
    (implies type
             (type-integerp type)))

  (defret type-arithmeticp-of-fixtype-to-integer-type
    (implies type
             (type-arithmeticp type))))
