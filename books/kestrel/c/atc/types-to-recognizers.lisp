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

(include-book "../language/types")
(include-book "defstruct")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ types-to-recognizers
  :parents (shallow-embedding)
  :short "Mapping from C types to their recognizers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This mapping connects the C types from the deep embeddings
     to the recognizers that represent those types in the shallow embedding."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-to-recognizer ((type typep) (wrld plist-worldp))
  :returns (recognizer symbolp)
  :short "ACL2 recognizer corresponding to a C type."
  :long
  (xdoc::topstring
   (xdoc::p
    "For a supported integer type,
     the predicate is the recognizer of values of that type.
     For a structure type,
     the predicate is the recognizer of structures of that type.
     For a pointer to integer type,
     the predicate is the recognizer of that referenced type.
     For a pointer to structure type,
     the predicate is the recognizer of structures of that type.
     For an array of integer type,
     the predicate is the recognizer of arrays of that element type.")
   (xdoc::p
    "This is based on our current ACL2 representation of C types,
     which may be extended in the future.
     Note that, in the current representation,
     the predicate corresponding to each type
     is never a recognizer of pointer values."))
  (type-case
   type
   :void (raise "Internal error: type ~x0." type)
   :char (raise "Internal error: type ~x0." type)
   :schar 'scharp
   :uchar 'ucharp
   :sshort 'sshortp
   :ushort 'ushortp
   :sint 'sintp
   :uint 'uintp
   :slong 'slongp
   :ulong 'ulongp
   :sllong 'sllongp
   :ullong 'ullongp
   :struct (b* ((info (defstruct-table-lookup (ident->name type.tag) wrld))
                ((unless info)
                 (raise "Internal error: no recognizer for ~x0." type)))
             (defstruct-info->recognizer info))
   :pointer (type-case
             type.to
             :void (raise "Internal error: type ~x0." type)
             :char (raise "Internal error: type ~x0." type)
             :schar 'scharp
             :uchar 'ucharp
             :sshort 'sshortp
             :ushort 'ushortp
             :sint 'sintp
             :uint 'uintp
             :slong 'slongp
             :ulong 'ulongp
             :sllong 'sllongp
             :ullong 'ullongp
             :struct (b* ((info (defstruct-table-lookup
                                  (ident->name type.to.tag)
                                  wrld))
                          ((unless info)
                           (raise "Internal error: no recognizer for ~x0."
                                  type)))
                       (defstruct-info->recognizer info))
             :pointer (raise "Internal error: type ~x0." type)
             :array (raise "Internal error: type ~x0." type))
   :array (type-case
           type.of
           :void (raise "Internal error: type ~x0." type)
           :char (raise "Internal error: type ~x0." type)
           :schar 'schar-arrayp
           :uchar 'uchar-arrayp
           :sshort 'sshort-arrayp
           :ushort 'ushort-arrayp
           :sint 'sint-arrayp
           :uint 'uint-arrayp
           :slong 'slong-arrayp
           :ulong 'ulong-arrayp
           :sllong 'sllong-arrayp
           :ullong 'ullong-arrayp
           :struct (raise "Internal error: type ~x0." type)
           :pointer (raise "Internal error: type ~x0." type)
           :array (raise "Internal error: type ~x0." type)))
  :hooks (:fix))
