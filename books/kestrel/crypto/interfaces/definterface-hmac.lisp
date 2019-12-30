; Cryptographic Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CRYPTO")

(include-book "definterface-hash")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc definterface-hmac

  :parents (interfaces)
  :short (xdoc::topstring
          "Introduce an "
          (xdoc::seetopic "interfaces" "interface")
          " for a cryptographic
           hash-based message authentication (HMAC) function.")

  :long

  (xdoc::topstring

   (xdoc::h3 "Introduction")

   (xdoc::p
    "HMAC is specified in the "
    (xdoc::a :href "https://tools.ietf.org/html/rfc2104" "RFC 2104 standard")
    ". It is parameterized over a hash function,
     i.e. there is an HMAC variant for each choice of the hash function.")

   (xdoc::p
    "This macro introduces a weakly constrained ACL2 function
     for an HMAC function;
     the underlying hash function is specified via a reference to
     the name of an existing @(tsee definterface-hash).
     The HMAC function
     takes two byte lists as arguments (the key and the text),
     and returns a byte list;
     the use of bytes (vs. bits) is consistent with RFC 2104.
     The guard of the function requires the arguments to be byte lists.
     The function is constrained to fix its arguments to byte lists,
     and to return a byte list whose size is
     the output size of the hash function.")

   (xdoc::p
    "If the referenced hash function has no limit on its input size,
     the HMAC function has no limit on the sizes of its inputs either.
     Otherwise, limits are derived as follows,
     and included in the guard of the generated constrained function.
     RFC 2104 says that the key size
     must not exceed the hash function's block size
     in order for the key to be used ``directly'',
     otherwise the key is hashed and its hash used:
     either way, the key or its hash is padded to the block size.
     RFC 2104 says that an inner hash is taken
     of the concatenation of
     (i) the (xor'd) padded key or key hash and (ii) the text,
     whose total size must therefore not exceed
     the hash function's maximum input size:
     it follows that the size of the text must not exceed
     the hash function's maximum input size dimished by
     the hash function's block size.
     Note that @(tsee definterface-hash) has no information about
     the hash function's block size,
     which is therefore supplied directly to @('definterface-hmac').
     RFC 2104 then takes an outer hash of the concatenation of
     the (xor'd) key and the inner hash output,
     but that is always well below the hash function's input size limit.")

   (xdoc::p
    "This macro also introduces a few theorems
     that follow from the constraints.
     It also introduces an XDOC topic for the generated
     function, constraints, and theorems.")

   (xdoc::h3 "General Form")

   (xdoc::codeblock
    "(definterface-hmac name"
    "                   :hash ..."
    "                   :block-size ..."
    "                   :topic ..."
    "                   :parents ..."
    "                   :short ..."
    "                   :long ..."
    "  )")

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@('name')"
    (xdoc::p
     "A symbol that names the HMAC function."))

   (xdoc::desc
    "@(':hash')"
    (xdoc::p
     "The name of an existing @(tsee definterface-hash)."))

   (xdoc::desc
    "@(':block-size')"
    (xdoc::p
     "A constant expression whose value is a positive integer.
      This is the hash function's block size in bytes.
      This input must be present if the hash function
      has an input size limit;
      otherwise, this input must be absent."))

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
    "@('name')"
    (xdoc::p
     "A constrained function that represents the HMAC function.")
    (xdoc::p
     "Its guard consists of @(tsee byte-listp) for both arguments and,
      if applicable, conditions on their lengths as explained above.")
    (xdoc::p
     "This funcion is constrained to:")
    (xdoc::ul
     (xdoc::li
      "Return a @(tsee byte-listp)
       of length equal to the output size of the hash function.")
     (xdoc::li
      "Fix its inputs to @(tsee byte-listp)."))
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

(defxdoc+ definterface-hmac-implementation
  :parents (definterface-hmac)
  :short "Implementation of @(tsee definterface-hmac)."
  :order-subtopics t
  :default-parent t)

(std::defaggregate definterface-hmac-info
  :short "Information about a @(tsee definterface-hmac) interface,
          recorded as a pair's value in the
          <see topic='@(url definterface-hmac-table)'
          >@(tsee definterface-hmac) table</see>."
  :long
  (xdoc::topstring-p
   "The name of the interface is the key of the pair in the table.")
  ((key-size-limit "The limit on the key size in bytes,
                    equal to the @(':input-size-limit') input, divided by 8,
                    of the @(tsee definterface-hash)
                    referenced by the @(tsee definterface-hmac)."
                   maybe-posp)
   (block-size "The @(':block-size') input." maybe-posp)
   (output-size "The size of the output in bytes,
                 equal to the @(':output-size') input, divided by 8,
                 of the @(tsee definterface-hash)
                    referenced by the @(tsee definterface-hmac)."
                posp))
  :pred definterface-hmac-infop)

(defval *definterface-hmac-table-name*
  'definterface-hmac-table
  :short "Name of the
          <see topic='@(url definterface-hmac-table)'
          >@(tsee definterface-hmac) table</see>.")

(defsection definterface-hmac-table
  :short "@(csee table) of @(tsee definterface-hmac) interfaces."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each successful call of @(tsee definterface-hmac),
     this table includes a pair whose key is the name of the interface
     and whose value contains other information about the call
     (see @(tsee definterface-hmac-infop))."))

  (make-event
   `(table ,*definterface-hmac-table-name* nil nil
      :guard (and (symbolp acl2::key) ; name of the interface
                  (definterface-hmac-infop acl2::val)))))

(define definterface-hmac-fn (name
                              hash
                              block-size
                              topic
                              parents
                              short
                              long
                              (wrld plist-worldp))
  :returns (event? "A @(tsee acl2::maybe-pseudo-event-formp).")
  :verify-guards nil
  :short "Events generated by @(tsee definterface-hmac)."
  (b* (;; validate the NAME input:
       ((unless (symbolp name))
        (raise "The NAME input must be a symbol, ~
                but is it ~x0 instead." name))
       ;; validate the :HASH input:
       ((unless (symbolp hash))
        (raise "The :HASH input must be a symbol, ~
                but it is ~x0 instead." hash))
       (table (table-alist *definterface-hash-table-name* wrld))
       (pair (assoc-eq hash table))
       ((unless pair)
        (raise "The :HASH input ~x0 must name ~
                an existing hash function interface ~
                introduced via DEFINTERFACE-HASH, ~
                but this is not the case." hash))
       ;; retrieve input size limit and output size of the hash function:
       (info (cdr pair))
       (input-size-limit (definterface-hash-info->input-size-limit info))
       (input-size-limit-/-8 (and input-size-limit
                                  (/ input-size-limit 8)))
       (output-size (definterface-hash-info->output-size info))
       (output-size-/-8 (/ output-size 8))
       ;; validate the :BLOCK-SIZE input:
       ((when (and input-size-limit
                   (not (posp block-size))))
        (raise "Since the hash function ~x0 has an input size limit, ~
                the :BLOCK-SIZE input must be a positive integer, ~
                but it is ~x1 instead." hash block-size))
       ((when (and (not input-size-limit)
                   block-size))
        (raise "Since the hash function ~x0 has no input size limit, ~
                the :BLOCK-SIZE input must be absent, ~
                but it is ~x1 instead." hash block-size))
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
       ;; names of the generated theorems:
       (byte-listp-thm-name (acl2::packn-pos (list 'byte-list-of- name)
                                             pkg-witness))
       (len-thm-name (acl2::packn-pos (list 'len-of- name)
                                      pkg-witness))
       (true-listp-thm-name (acl2::packn-pos (list 'true-listp-of- name)
                                             pkg-witness))
       (consp-thm-name (acl2::packn-pos (list 'consp-of- name)
                                        pkg-witness))
       ;; guard of the generated function:
       (guard (if input-size-limit
                  `(and (byte-listp key)
                        (< (len key) ,input-size-limit-/-8)
                        (byte-listp text)
                        (< (len text) (- ,input-size-limit-/-8
                                         ,block-size)))
                '(and (byte-listp key)
                      (byte-listp text))))
       ;; function signature:
       (sig `((,name * *) => * :formals (key text) :guard ,guard))
       ;; generated events:
       (wit `(local
              (defun ,name (key text)
                (declare (ignore key text))
                (make-list ,output-size-/-8 :initial-element 0))))
       (byte-listp-thm `(defrule ,byte-listp-thm-name
                          (byte-listp (,name key text))))
       (len-thm `(defrule ,len-thm-name
                   (equal (len (,name key text))
                          ,output-size-/-8)))
       (fix-thms `(fty::deffixequiv ,name
                    :args ((key byte-listp) (text byte-listp))))
       (true-listp-thm `(defrule ,true-listp-thm-name
                          (true-listp (,name key text))
                          :rule-classes :type-prescription
                          :enable acl2::true-listp-when-byte-listp))
       (consp-thm `(defrule ,consp-thm-name
                     (consp (,name key text))
                     :rule-classes :type-prescription
                     :use ,len-thm-name
                     :disable ,len-thm-name))
       (table-event `(table ,*definterface-hmac-table-name*
                       ',name
                       ',(make-definterface-hmac-info
                          :key-size-limit input-size-limit-/-8
                          :block-size block-size
                          :output-size output-size-/-8))))
    ;; top-level event:
    `(encapsulate
       ()
       (logic)
       (defsection ,topic
         ,@(and parents (list :parents parents))
         ,@(and short (list :short short))
         ,@(and long (list :long long))
         (encapsulate
           (,sig)
           ,wit
           ,byte-listp-thm
           ,len-thm
           ,fix-thms)
         ,true-listp-thm
         ,consp-thm)
       ,table-event)))

(defsection definterface-hmac-macro-definition
  :short "Definition of the @(tsee definterface-hmac) macro."
  :long (xdoc::topstring-@def "definterface-hmac")
  (defmacro definterface-hmac (name
                               &key
                               hash
                               block-size
                               topic
                               parents
                               short
                               long)
    `(make-event (definterface-hmac-fn
                   ',name
                   ',hash
                   ,block-size
                   ',topic
                   ',parents
                   ,short
                   ,long
                   (w state)))))
