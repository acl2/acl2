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

(local (include-book "kestrel/std/system/good-atom-listp" :dir :system))
(local (include-book "std/typed-lists/string-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

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
     whose value is being assigned to the pointed-to integer."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-pointed-integer-operations ((type typep))
  :guard (type-nonchar-integerp type)
  :returns (event pseudo-event-formp)
  :short "Event to generate operations on pointed integers of a given type."

  (b* ((type-string (integer-type-xdoc-string type))
       (<type> (integer-type-to-fixtype type))
       (<type>p (pack <type> 'p))
       (<type>-fix (pack <type> '-fix))
       (<type>-read (pack <type> '-read))
       (<type>-write (pack <type> '-write)))

    `(progn

       (define ,<type>-read ((x ,<type>p))
         :returns (x ,<type>p)
         :short ,(str::cat "Representation of a read of a pointed "
                           type-string
                           ".")
         (,<type>-fix x)
         :hooks (:fix))

       (define ,<type>-write ((x ,<type>p))
         :returns (x ,<type>p)
         :short ,(str::cat "Representation of a write of a pointed "
                           type-string
                           ".")
         (,<type>-fix x)
         :hooks (:fix))))

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
