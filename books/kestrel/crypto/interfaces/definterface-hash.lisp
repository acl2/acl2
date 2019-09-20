; Cryptographic Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CRYPTO")

(include-book "kestrel/fty/bit-list" :dir :system)
(include-book "kestrel/fty/byte-list" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc definterface-hash

  :parents (interfaces)
  :short (xdoc::topstring
          "Introduce an "
          (xdoc::seetopic "interfaces" "interface")
          " for a cryptographic hash function.")

  :long

  (xdoc::topstring

   (xdoc::h3 "Introduction")

   (xdoc::p
    "A cryptographic hash function
     takes as input a sequence of bits
     of arbitrary size
     or of a size bounded by a large limit,
     and returns a sequence of bits
     of a fixed size.
     Given an endianness convention to covert between bit and byte sequences,
     the hash function can be also regarded as
     operating on byte sequences.")

   (xdoc::p
    "This macro introduces weakly constrained ACL2 functions
     for a cryptographic hash function:
     one that operates on bits and one that operates on bytes.
     Both functions have guards that require
     the input to be bit or byte lists
     and its length to be bounded (if applicable).
     The functions are constrained
     to return bit or byte lists of the appropriate fixed lengths,
     and also to fix their inputs to bit or byte lists.")

   (xdoc::p
    "This macro also introduces a few theorems
     that follow from the constraints.
     It also introduces an XDOC topic for the generated
     functions, constraints, and theorems.")

   (xdoc::h3 "General Form")

   (xdoc::codeblock
    "(definterface-hash name"
    "                   :input-size-limit ..."
    "                   :output-size ..."
    "                   :name-bits ..."
    "                   :name-bytes ..."
    "                   :topic ..."
    "                   :parents ..."
    "                   :short ..."
    "                   :long ..."
    "  )")

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@('name')"
    (xdoc::p
     "A symbol that names the hash function."))

   (xdoc::desc
    "@(':input-size-limit')"
    (xdoc::p
     "One of the following:")
    (xdoc::ul
     (xdoc::li
      "A constant expression whose value is a positive integer multiple of 8.
       This is the limit of the input size in bits:
       the size of the input must be strictly less than this limit.
       This is for hash functions that have a bound on the size of the input.")
     (xdoc::li
      "@('nil'), if the hash function accepts inputs of arbitrary size.")))

   (xdoc::desc
    "@(':output-size')"
    (xdoc::p
     "A constant expression whose value is a positive integer multiple of 8.
      This is the fixed size of the output, in bits."))

   (xdoc::desc
    "@(':name-bits')"
    (xdoc::p
     "A symbol that names the generated constrained function
      that operates on bits.")
    (xdoc::p
     "If not supplied, it defaults to @('name') followed by @('-bits')."))

   (xdoc::desc
    "@(':name-bytes')"
    (xdoc::p
     "A symbol that names the generated constrained function
      that operates on bytes.")
    (xdoc::p
     "If not supplied, it defaults to @('name') followed by @('-bytes')."))

   (xdoc::desc
    "@(':topic')"
    (xdoc::p
     "A symbol that names the generated XDOC topic
      that surrounds the generated functions and theorems.")
    (xdoc::p
     "If not supplied, it defaults to @('name') followed by @('-interface')."))

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
    "@('name-bits')"
    (xdoc::p
     "A constrained function that operates on bits.")
    (xdoc::p
     "Its guard consists of @(tsee bit-listp) and,
      if applicable, the limit on the input size
      specified by @(':input-size-limit').")
    (xdoc::p
     "The function is constrained to:")
    (xdoc::ul
     (xdoc::li
      "Return a @(tsee bit-listp)
       of the length specified by @(':output-size').")
     (xdoc::li
      "Fix its input to a @(tsee bit-listp)."))
    (xdoc::p
     "The following additional theorems are also generated:")
    (xdoc::ul
     (xdoc::li
      "A type prescription rules saying that
        the function returns a @(tsee true-listp).")
     (xdoc::li
      "A type prescription rule saying that
        the function returns a @(tsee consp).")))

   (xdoc::desc
    "@('name-bytes')"
    (xdoc::p
     "A constrained function that operates on bytes.")
    (xdoc::p
     "Its guard consists of @(tsee byte-listp) and,
      if applicable, the limit on the input size
      specified by @(':input-size-limit') and divided by 8.")
    (xdoc::p
     "The function is constrained to:")
    (xdoc::ul
     (xdoc::li
      "Return a @(tsee byte-listp)
       of the length specified by @(':output-size') divided by 8.")
     (xdoc::li
      "Fix its input to a @(tsee byte-listp)."))
    (xdoc::p
     "The following additional theorems are also generated:")
    (xdoc::ul
     (xdoc::li
      "A type prescription rules saying that
       the function returns a @(tsee true-listp).")
     (xdoc::li
      "A type prescription rule saying that
       the function returns a @(tsee consp).")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ definterface-hash-implementation
  :parents (definterface-hash)
  :short "Implementation of @(tsee definterface-hash)."
  :order-subtopics t
  :default-parent t)

(std::defaggregate definterface-hash-info
  :short "Information about a @(tsee definterface-hash) interface,
          recorded as a pair's value in the
          <see topic='@(url definterface-hash-table)'
          >@(tsee definterface-hash) table</see>."
  :long
  (xdoc::topstring-p
   "The name of the interface is the key of the pair in the table.")
  ((input-size-limit "The @(':input-size-limit') input." maybe-posp)
   (output-size "The @(':output-size') input." posp))
  :pred definterface-hash-infop)

(defval *definterface-hash-table-name*
  'definterface-hash-table
  :short "Name of the
          <see topic='@(url definterface-hash-table)'
          >@(tsee definterface-hash) table</see>.")

(defsection definterface-hash-table
  :short "@(csee table) of @(tsee definterface-hash) interfaces."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each successful call of @(tsee definterface-hash),
     this table includes a pair whose key is the name of the interface
     and whose value contains other information about the call
     (see @(tsee definterface-hash-infop))."))

  (make-event
   `(table ,*definterface-hash-table-name* nil nil
      :guard (and (symbolp acl2::key) ; name of the interface
                  (definterface-hash-infop acl2::val)))))

(define definterface-hash-fn (name
                              input-size-limit
                              output-size
                              name-bits
                              name-bytes
                              topic
                              parents
                              short
                              long)
  :returns (event? "A @(tsee acl2::maybe-pseudo-event-formp).")
  :short "Events generated by @(tsee definterface-hash)."
  (b* (;; validate the NAME input:
       ((unless (symbolp name))
        (raise "The NAME input must be a symbol, ~
                but it is ~x0 instead." name))
       ;; validate the :INPUT-SIZE-LIMIT input:
       ((unless (or (null input-size-limit)
                    (and (posp input-size-limit)
                         (integerp (/ input-size-limit 8)))))
        (raise "The :INPUT-SIZE-LIMIT must be NIL or ~
                a positive integer multiple of 8, ~
                but it is ~x0 instead." input-size-limit))
       (input-size-limit-/-8 (if input-size-limit
                                 (/ input-size-limit 8)
                               nil))
       ;; validate the :OUTPUT-SIZE input:
       ((unless (and (posp output-size)
                     (integerp (/ output-size 8))))
        (raise "The :OUTPUT-SIZE must be ~
                a positive integer multiple of 8, ~
                but it is ~x0 instead." output-size))
       (output-size-/-8 (/ output-size 8))
       ;; validate the :NAME-BITS input:
       ((unless (symbolp name-bits))
        (raise "The :NAME-BITS input must be a symbol, ~
                but it is ~x0 instead." name-bits))
       ;; validate the :NAME-BYTES input:
       ((unless (symbolp name-bytes))
        (raise "The :NAME-BITS input must be a symbol, ~
                but it is ~x0 instead." name-bits))
       ;; validate the :TOPIC input:
       ((unless (symbolp topic))
        (raise "The :TOPIC input must be a symbol, ~
                but it is ~x0 instead." topic))
       ;; package for the generated theorem names:
       (pkg (symbol-package-name name))
       (pkg (if (equal pkg *main-lisp-package-name*) "ACL2" pkg))
       (pkg-witness (pkg-witness pkg))
       ;; name of the generated XDOC topic:
       (topic (or topic (acl2::add-suffix-to-fn name "-INTERFACE")))
       ;; names of the generated functions:
       (name-bits (or name-bits
                      (acl2::add-suffix-to-fn name "-BITS")))
       (name-bytes (or name-bytes
                       (acl2::add-suffix-to-fn name "-BYTES")))
       ;; names of the generated theorems:
       (bit-listp-bits (acl2::packn-pos (list 'bit-list-of- name-bits)
                                        pkg-witness))
       (byte-listp-bytes (acl2::packn-pos (list 'byte-list-of- name-bytes)
                                          pkg-witness))
       (len-bits (acl2::packn-pos (list 'len-of- name-bits)
                                  pkg-witness))
       (len-bytes (acl2::packn-pos (list 'len-of- name-bytes)
                                   pkg-witness))
       (true-listp-bits (acl2::packn-pos (list 'true-listp-of- name-bits)
                                         pkg-witness))
       (true-listp-bytes (acl2::packn-pos (list 'true-listp-of- name-bytes)
                                          pkg-witness))
       (consp-bits (acl2::packn-pos (list 'consp-of- name-bits)
                                    pkg-witness))
       (consp-bytes (acl2::packn-pos (list 'consp-of- name-bytes)
                                     pkg-witness))
       ;; guards of the generated functions:
       (guard-bits (if input-size-limit
                       `(and (bit-listp bits)
                             (< (len bits) ,input-size-limit))
                     '(bit-listp bits)))
       (guard-bytes (if input-size-limit
                        `(and (byte-listp bytes)
                              (< (len bytes) ,input-size-limit-/-8))
                      '(byte-listp bytes)))
       ;; function signatures:
       (sig-bits `((,name-bits *) => * :formals (bits) :guard ,guard-bits))
       (sig-bytes `((,name-bytes *) => * :formals (bytes) :guard ,guard-bytes))
       ;; generated events:
       (wit-bits `(local
                   (defun ,name-bits (bits)
                     (declare (ignore bits))
                     (make-list ,output-size :initial-element 0))))
       (wit-bytes `(local
                    (defun ,name-bytes (bytes)
                      (declare (ignore bytes))
                      (make-list ,output-size-/-8 :initial-element 0))))
       (bit-listp-thm `(defrule ,bit-listp-bits
                         (bit-listp (,name-bits bits))))
       (byte-listp-thm `(defrule ,byte-listp-bytes
                          (byte-listp (,name-bytes bytes))))
       (len-bits-thm `(defrule ,len-bits
                        (equal (len (,name-bits bits))
                               ,output-size)))
       (len-bytes-thm `(defrule ,len-bytes
                         (equal (len (,name-bytes bytes))
                                ,output-size-/-8)))
       (fix-bits-thms `(fty::deffixequiv ,name-bits
                         :args ((bits bit-listp))))
       (fix-bytes-thms `(fty::deffixequiv ,name-bytes
                          :args ((bytes byte-listp))))
       (true-listp-bits-thm `(defrule ,true-listp-bits
                               (true-listp (,name-bits bits))
                               :rule-classes :type-prescription
                               :enable acl2::true-listp-when-bit-listp))
       (true-listp-bytes-thm `(defrule ,true-listp-bytes
                                (true-listp (,name-bytes bytes))
                                :rule-classes :type-prescription
                                :enable acl2::true-listp-when-byte-listp))
       (consp-bits-thm `(defrule ,consp-bits
                          (consp (,name-bits bits))
                          :rule-classes :type-prescription
                          :use ,len-bits
                          :disable ,len-bits))
       (consp-bytes-thm `(defrule ,consp-bytes
                           (consp (,name-bytes bytes))
                           :rule-classes :type-prescription
                           :use ,len-bytes
                           :disable ,len-bytes))
       (table-event `(table ,*definterface-hash-table-name*
                       ',name
                       ',(make-definterface-hash-info
                          :input-size-limit input-size-limit
                          :output-size output-size))))
    ;; top-level event:
    `(encapsulate
       ()
       (logic)
       (defsection ,topic
         ,@(and parents (list :parents parents))
         ,@(and short (list :short short))
         ,@(and long (list :long long))
         (encapsulate
           (,sig-bits
            ,sig-bytes)
           ,wit-bits
           ,wit-bytes
           ,bit-listp-thm
           ,byte-listp-thm
           ,len-bits-thm
           ,len-bytes-thm
           ,fix-bits-thms
           ,fix-bytes-thms)
         ,true-listp-bits-thm
         ,true-listp-bytes-thm
         ,consp-bits-thm
         ,consp-bytes-thm)
       ,table-event)))

(defsection definterface-hash-macro-definition
  :short "Definition of the @(tsee definterface-hash) macro."
  :long (xdoc::topstring-@def "definterface-hash")
  (defmacro definterface-hash (name
                               &key
                               input-size-limit
                               output-size
                               name-bits
                               name-bytes
                               topic
                               parents
                               short
                               long)
    `(make-event (definterface-hash-fn
                   ',name
                   ,input-size-limit
                   ,output-size
                   ',name-bits
                   ',name-bytes
                   ',topic
                   ',parents
                   ,short
                   ,long))))
