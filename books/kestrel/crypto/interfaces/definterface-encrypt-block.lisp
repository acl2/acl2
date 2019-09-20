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

(defxdoc definterface-encrypt-block

  :parents (interfaces)

  :short (xdoc::topstring
          "Introduce an "
          (xdoc::seetopic "interfaces" "interface")
          " for a cryptographic block encryption function.")

  :long

  (xdoc::topstring

   (xdoc::h3 "Introduction")

   (xdoc::p
    "A cryptographic block encryption function
     turns a block of plaintext into a block of ciphertext, given a key.
     Its inverse, a cryptographic block decryption function,
     turns a block of ciphertext into a block of plaintext, given the same key.
     Blocks and keys have known sizes in bits.
     Given an endianness convention to covert between bit and byte sequences,
     the encryption and decryption functions can be regarded as
     operating on byte sequences instead of bit sequences.")

   (xdoc::p
    "This macro introduces weakly constrained ACL2 functions
     for two pairs of cryptographic block encryption and decryption functions:
     one that operates on bits and one that operates on bytes.
     Each of these four functions takes as inputs a key and a block,
     and has a guard requiring them to be bit or byte lists
     of the right key and block sizes.
     These functions are constrained to return blocks of the right sizes,
     and also to fix their inputs to bit or byte lists.
     We may extend this macro to generate additional constraints,
     such as the fact that encryption and decryption are mutual inverses.")

   (xdoc::p
    "This macro also introduces a few theorems
     that follow from the constraints.
     It also introduces an XDOC topic for the generated
     functions, constraints, and theorems.")

   (xdoc::h3 "General Form")

   (xdoc::codeblock
    "(definterface-encrypt-block name"
    "                            :key-size ..."
    "                            :block-size ..."
    "                            :name-encrypt-bits ..."
    "                            :name-decrypt-bits ..."
    "                            :name-encrypt-bytes ..."
    "                            :name-decrypt-bytes ..."
    "                            :topic ..."
    "                            :parents ..."
    "                            :short ..."
    "                            :long ..."
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
    "@(':block-size')"
    (xdoc::p
     "A constant expression whose value is a positive integer multiple of 8.
      This is the size of the block, in bits."))

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
     "Their guard consists of @(tsee bit-listp) for both arguments and
      requires the length of the first argument to be the key size
      (specified by @(':key-size')
      and the length of the second argument to be the block size
      (specified by @(':block-size').")
    (xdoc::p
     "Each function is constrained to:")
    (xdoc::ul
     (xdoc::li
      "Return a @(tsee bit-listp)
       of the length specified by @(':block-size').")
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
      requires the length of the first argument to be the key size divided by 8
      (specified by @(':key-size'))
      and the length of the second argument to be the block size divided by 8
      (specified by @(':block-size')).")
    (xdoc::p
     "Each function is constrained to:")
    (xdoc::ul
     (xdoc::li
      "Return a @(tsee byte-listp)
       of the length specified by @(':block-size') divided by 8.")
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

(define definterface-encrypt-block-fn (name
                                       key-size
                                       block-size
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
  :short "Events generated by @(tsee definterface-encrypt-block)."
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
       ;; validate the :BLOCK-SIZE input:
       ((unless (and (posp block-size)
                     (integerp (/ block-size 8))))
        (raise "The :BLOCK-SIZE input must be ~
                a positive integer multiple of 8, ~
                but it is ~x0 instead." block-size))
       (block-size-/-8 (/ block-size 8))
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
       (len-encrypt-bits (acl2::packn-pos (list 'len-of- name-encrypt-bits)
                                          pkg-witness))
       (len-decrypt-bits (acl2::packn-pos (list 'len-of- name-decrypt-bits)
                                          pkg-witness))
       (len-encrypt-bytes (acl2::packn-pos (list 'len-of- name-encrypt-bytes)
                                           pkg-witness))
       (len-decrypt-bytes (acl2::packn-pos (list 'len-of- name-decrypt-bytes)
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
       (consp-encrypt-bits (acl2::packn-pos (list 'consp-of-
                                                  name-encrypt-bits)
                                            pkg-witness))
       (consp-decrypt-bits (acl2::packn-pos (list 'consp-of-
                                                  name-decrypt-bits)
                                            pkg-witness))
       (consp-encrypt-bytes (acl2::packn-pos (list 'consp-of-
                                                   name-encrypt-bytes)
                                             pkg-witness))
       (consp-decrypt-bytes (acl2::packn-pos (list 'consp-of-
                                                   name-decrypt-bytes)
                                             pkg-witness))
       ;; guards of the generated functions:
       (guard-bits `(and (bit-listp key)
                         (equal (len key) ,key-size)
                         (bit-listp block)
                         (equal (len block) ,block-size)))
       (guard-bytes `(and (byte-listp key)
                          (equal (len key) ,key-size-/-8)
                          (byte-listp block)
                          (equal (len block) ,block-size-/-8)))
       ;; function signatures:
       (sig-encrypt-bits `((,name-encrypt-bits * *) => *
                           :formals (key block)
                           :guard ,guard-bits))
       (sig-decrypt-bits `((,name-decrypt-bits * *) => *
                           :formals (key block)
                           :guard ,guard-bits))
       (sig-encrypt-bytes `((,name-encrypt-bytes * *) => *
                            :formals (key block)
                            :guard ,guard-bytes))
       (sig-decrypt-bytes `((,name-decrypt-bytes * *) => *
                            :formals (key block)
                            :guard ,guard-bytes))
       ;; generated events:
       (wit-encrypt-bits `(local
                           (defun ,name-encrypt-bits (key block)
                             (declare (ignore key block))
                             (make-list ,block-size :initial-element 0))))
       (wit-decrypt-bits `(local
                           (defun ,name-decrypt-bits (key block)
                             (declare (ignore key block))
                             (make-list ,block-size :initial-element 0))))
       (wit-encrypt-bytes `(local
                            (defun ,name-encrypt-bytes (key block)
                              (declare (ignore key block))
                              (make-list ,block-size-/-8 :initial-element 0))))
       (wit-decrypt-bytes `(local
                            (defun ,name-decrypt-bytes (key block)
                              (declare (ignore key block))
                              (make-list ,block-size-/-8 :initial-element 0))))
       (bit-listp-encrypt-bits-thm `(defrule ,bit-listp-encrypt-bits
                                      (bit-listp
                                       (,name-encrypt-bits key block))))
       (bit-listp-decrypt-bits-thm `(defrule ,bit-listp-decrypt-bits
                                      (bit-listp
                                       (,name-decrypt-bits key block))))
       (byte-listp-encrypt-bytes-thm `(defrule ,byte-listp-encrypt-bytes
                                        (byte-listp
                                         (,name-encrypt-bytes key block))))
       (byte-listp-decrypt-bytes-thm `(defrule ,byte-listp-decrypt-bytes
                                        (byte-listp
                                         (,name-decrypt-bytes key block))))
       (len-encrypt-bits-thm `(defrule ,len-encrypt-bits
                                (equal (len (,name-encrypt-bits key block))
                                       ,block-size)))
       (len-decrypt-bits-thm `(defrule ,len-decrypt-bits
                                (equal (len (,name-decrypt-bits key block))
                                       ,block-size)))
       (len-encrypt-bytes-thm `(defrule ,len-encrypt-bytes
                                 (equal (len (,name-encrypt-bytes key block))
                                        ,block-size-/-8)))
       (len-decrypt-bytes-thm `(defrule ,len-decrypt-bytes
                                 (equal (len (,name-decrypt-bytes key block))
                                        ,block-size-/-8)))
       (fix-encrypt-bits-thms `(fty::deffixequiv ,name-encrypt-bits
                                 :args ((key bit-listp) (block bit-listp))))
       (fix-decrypt-bits-thms `(fty::deffixequiv ,name-decrypt-bits
                                 :args ((key bit-listp) (block bit-listp))))
       (fix-encrypt-bytes-thms `(fty::deffixequiv ,name-encrypt-bytes
                                  :args ((key byte-listp) (block byte-listp))))
       (fix-decrypt-bytes-thms `(fty::deffixequiv ,name-decrypt-bytes
                                  :args ((key byte-listp) (block byte-listp))))
       (true-listp-encrypt-bits-thm `(defrule ,true-listp-encrypt-bits
                                       (true-listp
                                        (,name-encrypt-bits key block))
                                       :rule-classes :type-prescription
                                       :enable acl2::true-listp-when-bit-listp))
       (true-listp-decrypt-bits-thm `(defrule ,true-listp-decrypt-bits
                                       (true-listp
                                        (,name-decrypt-bits key block))
                                       :rule-classes :type-prescription
                                       :enable acl2::true-listp-when-bit-listp))
       (true-listp-encrypt-bytes-thm `(defrule ,true-listp-encrypt-bytes
                                        (true-listp
                                         (,name-encrypt-bytes key block))
                                        :rule-classes :type-prescription
                                        :enable
                                        acl2::true-listp-when-byte-listp))
       (true-listp-decrypt-bytes-thm `(defrule ,true-listp-decrypt-bytes
                                        (true-listp
                                         (,name-decrypt-bytes key block))
                                        :rule-classes :type-prescription
                                        :enable
                                        acl2::true-listp-when-byte-listp))
       (consp-encrypt-bits-thm `(defrule ,consp-encrypt-bits
                                  (consp (,name-encrypt-bits key block))
                                  :rule-classes :type-prescription
                                  :use ,len-encrypt-bits
                                  :disable ,len-encrypt-bits))
       (consp-decrypt-bits-thm `(defrule ,consp-decrypt-bits
                                  (consp (,name-decrypt-bits key block))
                                  :rule-classes :type-prescription
                                  :use ,len-decrypt-bits
                                  :disable ,len-decrypt-bits))
       (consp-encrypt-bytes-thm `(defrule ,consp-encrypt-bytes
                                   (consp (,name-encrypt-bytes key block))
                                   :rule-classes :type-prescription
                                   :use ,len-encrypt-bytes
                                   :disable ,len-encrypt-bytes))
       (consp-decrypt-bytes-thm `(defrule ,consp-decrypt-bytes
                                   (consp (,name-decrypt-bytes key block))
                                   :rule-classes :type-prescription
                                   :use ,len-decrypt-bytes
                                   :disable ,len-decrypt-bytes)))
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
           ,len-encrypt-bits-thm
           ,len-decrypt-bits-thm
           ,len-encrypt-bytes-thm
           ,len-decrypt-bytes-thm
           ,fix-encrypt-bits-thms
           ,fix-decrypt-bits-thms
           ,fix-encrypt-bytes-thms
           ,fix-decrypt-bytes-thms)
         ,true-listp-encrypt-bits-thm
         ,true-listp-decrypt-bits-thm
         ,true-listp-encrypt-bytes-thm
         ,true-listp-decrypt-bytes-thm
         ,consp-encrypt-bits-thm
         ,consp-decrypt-bits-thm
         ,consp-encrypt-bytes-thm
         ,consp-decrypt-bytes-thm))))

(defsection definterface-encrypt-block-macro-definition
  :short "Definition of the @(tsee definterface-encrypt-block) macro."
  :long (xdoc::topstring-@def "definterface-encrypt-block")
  (defmacro definterface-encrypt-block (name
                                        &key
                                        key-size
                                        block-size
                                        name-encrypt-bits
                                        name-decrypt-bits
                                        name-encrypt-bytes
                                        name-decrypt-bytes
                                        topic
                                        parents
                                        short
                                        long)
    `(make-event (definterface-encrypt-block-fn
                   ',name
                   ,key-size
                   ,block-size
                   ',name-encrypt-bits
                   ',name-decrypt-bits
                   ',name-encrypt-bytes
                   ',name-decrypt-bytes
                   ',topic
                   ',parents
                   ,short
                   ,long))))
