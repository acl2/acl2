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

(defxdoc definterface-encrypt-init

  :parents (interfaces)

  :short (xdoc::topstring
          "Introduce an "
          (xdoc::seetopic "interfaces" "interface")
          " for a cryptographic encryption function
           with an initialization vector.")

  :long

  (xdoc::topstring

   (xdoc::h3 "Introduction")

   (xdoc::p
    "Block encryption functions
     (whose interfaces may be generated via @(tsee definterface-encrypt-block))
     may be used to encrypt data larger than single blocks
     by combining multiple block encryptions
     according to various schemes (e.g. CBC).
     Some of these schemes require an initialization vector as additional input.
     This also applies to the inverse decryption functions.")

   (xdoc::p
    "This macro introduces weakly constrained ACL2 functions
     for two pairs of cryptographic encryption and decryption functions
     that use an initialization vector:
     one that operates on bits and one that operates on bytes.
     Each of these four functions takes as inputs
     a key, an initialization vector, and some arbitrary data,
     and has a guard requiring all three to be bit or byte lists
     and the first two to have the right key and block sizes.
     These functions are constrained to return sequences of bits or bytes,
     and also to fix their inputs to bit or byte lists.
     We may extend this macro to generate additional constraints,
     such as the fact that encryption and decryption are mutual inverses,
     or that the size of the ouput data
     is suitably related to the input data.
     These functions are meant to also pad the input data to the block size;
     then the size of the output data consist of as many blocks as
     the padded input blocks.")

   (xdoc::p
    "This macro also introduces a few theorems
     that follow from the constraints.
     It also introduces an XDOC topic for the generated
     functions, constraints, and theorems.")

   (xdoc::h3 "General Form")

   (xdoc::codeblock
    "(definterface-encrypt-init name"
    "                           :key-size ..."
    "                           :init-size ..."
    "                           :name-encrypt-bits ..."
    "                           :name-decrypt-bits ..."
    "                           :name-encrypt-bytes ..."
    "                           :name-decrypt-bytes ..."
    "                           :topic ..."
    "                           :parents ..."
    "                           :short ..."
    "                           :long ..."
    "  )")

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@('name')"
    (xdoc::p
     "A symbol that names the encryption algorithm."))

   (xdoc::desc
    "@(':key-size')"
    (xdoc::p
     "A constant expression whose value is a positive integer multiple of 8.
      This is the size of the key, in bits."))

   (xdoc::desc
    "@(':init-size')"
    (xdoc::p
     "A constant expression whose value is a positive integer multiple of 8.
      This is the size of the initialization vector, in bits."))

   (xdoc::desc
    "@(':name-encrypt-bits')"
    (xdoc::p
     "A symbol that names the generated constrained encryption function
      that operates on bits.")
    (xdoc::p
     "If not supplied, it defaults to @('name')
      followed by @('-encrypt-bits')."))

   (xdoc::desc
    "@(':name-decrypt-bits')"
    (xdoc::p
     "A symbol that names the generated constrained decryption function
      that operates on bits.")
    (xdoc::p
     "If not supplied, it defaults to @('name')
      followed by @('-decrypt-bits')."))

   (xdoc::desc
    "@(':name-encrypt-bytes')"
    (xdoc::p
     "A symbol that names the generated constrained encryption function
      that operates on bytes.")
    (xdoc::p
     "If not supplied, it defaults to @('name')
      followed by @('-encrypt-bytes')."))

   (xdoc::desc
    "@(':name-decrypt-bytes')"
    (xdoc::p
     "A symbol that names the generated constrained decryption function
      that operates on bytes.")
    (xdoc::p
     "If not supplied, it defaults to @('name')
      followed by @('-decrypt-bytes')."))

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
    (list
     "@('name-encrypt-bits')"
     "@('name-decrypt-bits')")
    (xdoc::p
     "Constrained encryption and decryption functions that operate on bits.")
    (xdoc::p
     "Their guard consists of @(tsee bit-listp) for all arguments and
      requires the length of the first argument to be the key size
      (specified by @(':key-size')
      and the length of the second argument to be the initialization vector size
      (specified by @(':init-size').")
    (xdoc::p
     "Each function is constrained to:")
    (xdoc::ul
     (xdoc::li
      "Return a @(tsee bit-listp).")
     (xdoc::li
      "Fix its input to a @(tsee bit-listp)."))
    (xdoc::p
     "The following additional theorems are also generated:")
    (xdoc::ul
     (xdoc::li
      "A type prescription rules saying that
       each function returns a @(tsee true-listp).")
     (xdoc::li
      "A type prescription rule saying that
       each function returns a @(tsee consp).")))

   (xdoc::desc
    (list
     "@('name-encrypt-bytes')"
     "@('name-decrypt-bytes')")
    (xdoc::p
     "Constrained encryption and decryption functions that operate on bytes.")
    (xdoc::p
     "Their guard consists of @(tsee byte-listp) for both arguments and
      requires the length of the first argument to be the key size
      (specified by @(':key-size')) divided by 8
      and the length of the second argument to be the initialization vector size
      (specified by @(':init-size')) divided by 8.")
    (xdoc::p
     "Each function is constrained to:")
    (xdoc::ul
     (xdoc::li
      "Return a @(tsee byte-listp).")
     (xdoc::li
      "Fix its input to a @(tsee byte-listp)."))
    (xdoc::p
     "The following additional theorems are also generated:")
    (xdoc::ul
     (xdoc::li
      "A type prescription rules saying that
       each function returns a @(tsee true-listp).")
     (xdoc::li
      "A type prescription rule saying that
       each function returns a @(tsee consp).")))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define definterface-encrypt-init-fn (name
                                      key-size
                                      init-size
                                      name-encrypt-bits
                                      name-decrypt-bits
                                      name-encrypt-bytes
                                      name-decrypt-bytes
                                      topic
                                      parents
                                      short
                                      long)
  :returns (event? "A @(tsee acl2::maybe-pseudo-event-formp).")
  :verify-guards nil
  :short "Events generated by @(tsee definterface-encrypt-init)."
  (b* (;; validate the NAME input:
       ((unless (symbolp name))
        (raise "The NAME input must be a symbol, ~
                but is it ~x0 instead." name))
       ;; validate the :KEY-SIZE input:
       ((unless (and (posp key-size)
                     (integerp (/ key-size 8))))
        (raise "The :KEY-SIZE input must be ~
                a positive integer multiple of 8, ~
                but it is ~x0 instead." key-size))
       (key-size-/-8 (/ key-size 8))
       ;; validate the :INIT-SIZE input:
       ((unless (and (posp init-size)
                     (integerp (/ init-size 8))))
        (raise "The :INIT-SIZE input must be ~
                a positive integer multiple of 8, ~
                but it is ~x0 instead." init-size))
       (init-size-/-8 (/ init-size 8))
       ;; validate the :NAME-ENCRYPT-BITS input:
       ((unless (symbolp name-encrypt-bits))
        (raise "The :NAME-ENCRYPT-BITS input must be a symbol, ~
                but it is ~x0 instead." name-encrypt-bits))
       ;; validate the :NAME-DECRYPT-BITS input:
       ((unless (symbolp name-decrypt-bits))
        (raise "The :NAME-DECRYPT-BITS input must be a symbol, ~
                but it is ~x0 instead." name-decrypt-bits))
       ;; validate the :NAME-ENCRYPT-BYTES input:
       ((unless (symbolp name-encrypt-bytes))
        (raise "The :NAME-ENCRYPT-BYTES input must be a symbol, ~
                but it is ~x0 instead." name-encrypt-bytes))
       ;; validate the :NAME-DECRYPT-BYTES input:
       ((unless (symbolp name-decrypt-bytes))
        (raise "The :NAME-DECRYPT-BYTES input must be a symbol, ~
                but it is ~x0 instead." name-decrypt-bytes))
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
       (name-encrypt-bits (or name-encrypt-bits
                              (acl2::add-suffix-to-fn name "-ENCRYPT-BITS")))
       (name-decrypt-bits (or name-decrypt-bits
                              (acl2::add-suffix-to-fn name "-DECRYPT-BITS")))
       (name-encrypt-bytes (or name-encrypt-bytes
                               (acl2::add-suffix-to-fn name "-ENCRYPT-BYTES")))
       (name-decrypt-bytes (or name-decrypt-bytes
                               (acl2::add-suffix-to-fn name "-DECRYPT-BYTES")))
       ;; names of the generated theorems:
       (bit-listp-encrypt-bits (acl2::packn-pos (list 'bit-list-of-
                                                      name-encrypt-bits)
                                                pkg-witness))
       (bit-listp-decrypt-bits (acl2::packn-pos (list 'bit-list-of-
                                                      name-decrypt-bits)
                                                pkg-witness))
       (byte-listp-encrypt-bytes (acl2::packn-pos (list 'byte-list-of-
                                                        name-encrypt-bytes)
                                                  pkg-witness))
       (byte-listp-decrypt-bytes (acl2::packn-pos (list 'byte-list-of-
                                                        name-decrypt-bytes)
                                                  pkg-witness))
       (true-listp-encrypt-bits (acl2::packn-pos (list 'true-listp-of-
                                                       name-encrypt-bits)
                                                 pkg-witness))
       (true-listp-decrypt-bits (acl2::packn-pos (list 'true-listp-of-
                                                       name-decrypt-bits)
                                                 pkg-witness))
       (true-listp-encrypt-bytes (acl2::packn-pos (list 'true-listp-of-
                                                        name-encrypt-bytes)
                                                  pkg-witness))
       (true-listp-decrypt-bytes (acl2::packn-pos (list 'true-listp-of-
                                                        name-decrypt-bytes)
                                                  pkg-witness))
       ;; guards of the generated functions:
       (guard-bits `(and (bit-listp key)
                         (equal (len key) ,key-size)
                         (bit-listp init)
                         (equal (len init) ,init-size)
                         (bit-listp data)))
       (guard-bytes `(and (byte-listp key)
                          (equal (len key) ,key-size-/-8)
                          (byte-listp init)
                          (equal (len init) ,init-size-/-8)
                          (byte-listp data)))
       ;; function signatures:
       (sig-encrypt-bits `((,name-encrypt-bits * * *) => *
                           :formals (key init data)
                           :guard ,guard-bits))
       (sig-decrypt-bits `((,name-decrypt-bits * * *) => *
                           :formals (key init data)
                           :guard ,guard-bits))
       (sig-encrypt-bytes `((,name-encrypt-bytes * * *) => *
                            :formals (key init data)
                            :guard ,guard-bytes))
       (sig-decrypt-bytes `((,name-decrypt-bytes * * *) => *
                            :formals (key init data)
                            :guard ,guard-bytes))
       ;; generated events:
       (wit-encrypt-bits `(local
                           (defun ,name-encrypt-bits (key init data)
                             (declare (ignore key init data))
                             (make-list ,init-size :initial-element 0))))
       (wit-decrypt-bits `(local
                           (defun ,name-decrypt-bits (key init data)
                             (declare (ignore key init data))
                             (make-list ,init-size :initial-element 0))))
       (wit-encrypt-bytes `(local
                            (defun ,name-encrypt-bytes (key init data)
                              (declare (ignore key init data))
                              (make-list ,init-size-/-8 :initial-element 0))))
       (wit-decrypt-bytes `(local
                            (defun ,name-decrypt-bytes (key init data)
                              (declare (ignore key init data))
                              (make-list ,init-size-/-8 :initial-element 0))))
       (bit-listp-encrypt-bits-thm `(defrule ,bit-listp-encrypt-bits
                                      (bit-listp
                                       (,name-encrypt-bits key init data))))
       (bit-listp-decrypt-bits-thm `(defrule ,bit-listp-decrypt-bits
                                      (bit-listp
                                       (,name-decrypt-bits key init data))))
       (byte-listp-encrypt-bytes-thm `(defrule ,byte-listp-encrypt-bytes
                                        (byte-listp
                                         (,name-encrypt-bytes key init data))))
       (byte-listp-decrypt-bytes-thm `(defrule ,byte-listp-decrypt-bytes
                                        (byte-listp
                                         (,name-decrypt-bytes key init data))))
       (fix-encrypt-bits-thms `(fty::deffixequiv ,name-encrypt-bits
                                 :args ((key bit-listp)
                                        (init bit-listp)
                                        (data bit-listp))))
       (fix-decrypt-bits-thms `(fty::deffixequiv ,name-decrypt-bits
                                 :args ((key bit-listp)
                                        (init bit-listp)
                                        (data bit-listp))))
       (fix-encrypt-bytes-thms `(fty::deffixequiv ,name-encrypt-bytes
                                  :args ((key byte-listp)
                                         (init byte-listp)
                                         (data byte-listp))))
       (fix-decrypt-bytes-thms `(fty::deffixequiv ,name-decrypt-bytes
                                  :args ((key byte-listp)
                                         (init byte-listp)
                                         (data byte-listp))))
       (true-listp-encrypt-bits-thm `(defrule ,true-listp-encrypt-bits
                                       (true-listp
                                        (,name-encrypt-bits key init data))
                                       :rule-classes :type-prescription
                                       :enable acl2::true-listp-when-bit-listp))
       (true-listp-decrypt-bits-thm `(defrule ,true-listp-decrypt-bits
                                       (true-listp
                                        (,name-decrypt-bits key init data))
                                       :rule-classes :type-prescription
                                       :enable acl2::true-listp-when-bit-listp))
       (true-listp-encrypt-bytes-thm `(defrule ,true-listp-encrypt-bytes
                                        (true-listp
                                         (,name-encrypt-bytes key init data))
                                        :rule-classes :type-prescription
                                        :enable
                                        acl2::true-listp-when-byte-listp))
       (true-listp-decrypt-bytes-thm `(defrule ,true-listp-decrypt-bytes
                                        (true-listp
                                         (,name-decrypt-bytes key init data))
                                        :rule-classes :type-prescription
                                        :enable
                                        acl2::true-listp-when-byte-listp)))
    ;; top-level event:
    `(encapsulate
       ()
       (logic)
       (defsection ,topic
         ,@(and parents (list :parents parents))
         ,@(and short (list :short short))
         ,@(and long (list :long long))
         (encapsulate
           (,sig-encrypt-bits
            ,sig-decrypt-bits
            ,sig-encrypt-bytes
            ,sig-decrypt-bytes)
           ,wit-encrypt-bits
           ,wit-decrypt-bits
           ,wit-encrypt-bytes
           ,wit-decrypt-bytes
           ,bit-listp-encrypt-bits-thm
           ,bit-listp-decrypt-bits-thm
           ,byte-listp-encrypt-bytes-thm
           ,byte-listp-decrypt-bytes-thm
           ,fix-encrypt-bits-thms
           ,fix-decrypt-bits-thms
           ,fix-encrypt-bytes-thms
           ,fix-decrypt-bytes-thms)
         ,true-listp-encrypt-bits-thm
         ,true-listp-decrypt-bits-thm
         ,true-listp-encrypt-bytes-thm
         ,true-listp-decrypt-bytes-thm))))

(defsection definterface-encrypt-init-macro-definition
  :short "Definition of the @(tsee definterface-encrypt-init) macro."
  :long (xdoc::topstring-@def "definterface-encrypt-init")
  (defmacro definterface-encrypt-init (name
                                       &key
                                       key-size
                                       init-size
                                       name-encrypt-bits
                                       name-decrypt-bits
                                       name-encrypt-bytes
                                       name-decrypt-bytes
                                       topic
                                       parents
                                       short
                                       long)
    `(make-event (definterface-encrypt-init-fn
                   ',name
                   ,key-size
                   ,init-size
                   ',name-encrypt-bits
                   ',name-decrypt-bits
                   ',name-encrypt-bytes
                   ',name-decrypt-bytes
                   ',topic
                   ',parents
                   ,short
                   ,long))))
