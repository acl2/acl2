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

(include-book "../representation/integers")
(include-book "pointer-types")

(local (include-book "std/typed-lists/atom-listp" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ pointed-integers
  :parents (shallow-embedding)
  :short "An ACL2 representation of C integers manipulated by pointers."
  :long
  (xdoc::topstring
   (xdoc::p
    "The "
    (xdoc::seetopic "representation-of-integers" "representation of C integers")
    " in the shallow embedding
     is for C integers manipulated as values.
     In C, integers may also be manipulated by pointers:
     that is, given a pointer to an integer,
     it is possible to read and write that integer,
     via the indirection operator @('*').")
   (xdoc::p
    "Pointed-to-integers are represented in the same way as by-value integers,
     in our shallow embedding of C in ACL2.
     However, we introduce specific ACL2 operations
     to read and write pointed-to integers,
     which represent C code that accesses those integers by pointer.")
   (xdoc::p
    "We define a family of functions to read pointed-to integers.
     These are identities in ACL2,
     but they represent applications of indirection @('*') to pointers in C.")
   (xdoc::p
    "We also define a family of functions to write pointed-to integers.
     They are also identity functions,
     but, as explained in the ATC user documentation,
     they are actually applied to the term that represents the expression
     whose value is being assigned to the pointed-to integer.")
   (xdoc::p
    "To support some level of type checking
     in the ACL2 representation of C code that uses pointed-to integers,
     we use the @(tsee star) wrapper (see @(see pointer-types))
     in the guards of the readers
     and in the return theorems of the writers:
     each reader takes a pointed-to integer and returns an integer,
     and each writer takes an integer and returns a pointed-to integer.
     The @(tsee star) wrappers are all identities,
     but by keeping them disabled,
     one can enforce some type checking at the ACL2 level.
     (ATC makes all the necessary type checking anyhow,
     but these additional checks may be useful before calling ATC,
     when manipulating ACL2 representations of C code.)"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-pointed-integer-operations ((type typep))
  :guard (type-nonchar-integerp type)
  :returns (event pseudo-event-formp)
  :short "Event to generate operations on pointed integers of a given type."
  :long
  (xdoc::topstring
   (xdoc::p
    "The enabled return type theorem for each writer
     has the @(tsee star) wrapper,
     because this is the kind of rule we want enabled
     for more strictly typed reasoning.
     We also add a disabled return type theorem without the wrapper,
     which may be useful for other purposes,
     namely when the @(tsee star) wrapper is enabled."))

  (b* ((type-string (integer-type-xdoc-string type))
       (<type> (integer-type-to-fixtype type))
       (<type>p (pack <type> 'p))
       (<type>-fix (pack <type> '-fix))
       (<type>-read (pack <type> '-read))
       (<type>-write (pack <type> '-write))
       (<type>p-of-<type>-write (pack <type> 'p-of- <type> '-write)))

    `(progn

       (define ,<type>-read ((x (star (,<type>p x))))
         :returns (x ,<type>p)
         :short ,(str::cat "Representation of a read of a pointed "
                           type-string
                           ".")
         (,<type>-fix x)
         :prepwork ((local (in-theory (enable star))))
         :hooks (:fix))

       (define ,<type>-write ((x ,<type>p))
         :returns (x (star (,<type>p x)))
         :short ,(str::cat "Representation of a write of a pointed "
                           type-string
                           ".")
         (,<type>-fix x)
         :prepwork ((local (in-theory (enable star))))
         :hooks (:fix)
         ///
         (more-returns (x ,<type>p))
         (in-theory (disable ,<type>p-of-<type>-write)))))

  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-pointed-integer-operations-loop ((types type-listp))
  :guard (type-nonchar-integer-listp types)
  :returns (events pseudo-event-form-listp)
  :short "Events to generate the operations on pointed integers of give types."
  (cond ((endp types) nil)
        (t (cons (def-pointed-integer-operations (car types))
                 (def-pointed-integer-operations-loop (cdr types)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 `(progn ,@(def-pointed-integer-operations-loop *nonchar-integer-types*)))
