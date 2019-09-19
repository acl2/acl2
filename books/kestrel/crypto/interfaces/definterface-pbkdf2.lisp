; Cryptographic Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CRYPTO")

(include-book "definterface-hmac")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc definterface-pbkdf2

  :parents (interfaces)

  :short (xdoc::topstring
          "Introduce an "
          (xdoc::seetopic "interfaces" "interface")
          " for a password-based key derivation function 2 (PBKDF2).")

  :long

  (xdoc::topstring

   (xdoc::h3 "Introduction")

   (xdoc::p
    "PBKDF2 is specified in the "
    (xdoc::a :href "https://tools.ietf.org/html/rfc8018" "RFC 8018 standard")
    ". It is parameterized over a pseudorandom function,
     i.e. there is a PBKDF2 variant
     for each choice of the pseudorandom function.
     RFC 8018 assumes the pseudorandom function to be a binary function,
     since it is applied to two arguments (see Section 5.2 of RFC 8018).")

   (xdoc::p
    "This macro introduces a weakly constrained ACL2 function
     for a PBKDF2 function;
     the underlying pseudorandom function is specified via a reference to
     the name of an existing @(tsee definterface-hmac).
     For now, only HMAC functions are supported
     as choices for the PBKDF2's pseudorandom function.
     The PBKDF2 function takes as arguments
     two byte lists (the password and the salt)
     and two positive integers (the iteration count and the key length);
     the use of bytes (vs. bits, or strings) is consistent with RFC 8108.
     The guard of the function requires the arguments
     to be byte lists and positive integers.
     The function is constrained to fix its arguments
     to byte lists and positive integers,
     and to return a byte list whose size is
     the key length specified by the argument.")

   (xdoc::p
    "The password of the PBKDF2 function
     is used as the key of the underlying HMAC function
     according to RFC 8108.
     Thus, if the HMAC function has a limit (derived from the hash function)
     on the size of the keys it accepts,
     the same limit applies to the password of the PBKDF2 function
     and is added to the guard of the PBKDF2 function.")

   (xdoc::p
    "If the hash function has an input size limit,
     the limit on the size of the HMAC function's text input
     is as explained in @(tsee definterface-hmac).
     RFC 8108 says that the text passed to the HMAC function is
     either (i) the salt concatenated with 4 bytes
     or (ii) an output of the HMAC function:
     while the latter is always well below the HMAC text size limit,
     the former induces the constraint that the salt
     must be below the limit for the HMAC text (see @(tsee definterface-hmac))
     diminished by 4.
     The guard of the PBKDF2 function includes this constraint,
     if applicable.")

   (xdoc::p
    "RFC 8108 says that the desired key length must not exceed
     @($(2^{32}-1)$) times the output size of the HMAC function.
     This is part of the guard of the PBKDF2 function.")

   (xdoc::p
    "This macro also introduces a few theorems
     that follow from the constraints.
     It also introduces an XDOC topic for the generated
     function, constraints, and theorems.")

   (xdoc::h3 "General Form")

   (xdoc::codeblock
    "(definterface-pbkdf2 name  "
    "                     :hmac ..."
    "                     :topic ..."
    "                     :parents ..."
    "                     :short ..."
    "                     :long ..."
    "  )")

   (xdoc::h3 "Inputs")

   (xdoc::desc
    "@('name')"
    (xdoc::p
     "A symbol that names the PBKDF2 function."))

   (xdoc::desc
    "@(':hmac')"
    (xdoc::p
     "The name of an existing @(tsee definterface-hmac)."))

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
     "A constrained function that represents the PBKDF2 function.")
    (xdoc::p
     "Its guard consists of
      @(tsee byte-listp) for the password and salt arguments,
      @(tsee posp) for the iteration and length arguments, and
      if applicable, conditions on the length of the password and salt
      derived as explained above.")
    (xdoc::p
     "This funcion is constrained to:")
    (xdoc::ul
     (xdoc::li
      "Return a @(tsee byte-listp)
       of length equal to the length argument.")
     (xdoc::li
      "Fix its inputs to @(tsee byte-listp) and @(tsee posp) as appropriate."))
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

(defxdoc+ definterface-pbkdf2-implementation
  :parents (definterface-pbkdf2)
  :short "Implementation of @(tsee definterface-pbkdf2)."
  :order-subtopics t
  :default-parent t)

(define definterface-pbkdf2-fn (name
                                hmac
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
       ;; validate the :HMAC input:
       ((unless (symbolp hmac))
        (raise "The :HMAC input must be a symbol, ~
                but it is ~x0 instead." hmac))
       (table (table-alist *definterface-hmac-table-name* wrld))
       (pair (assoc-eq hmac table))
       ((unless pair)
        (raise "The :HMAC input ~x0 must name ~
                an existing HMAC function interface ~
                introduced via DEFINTERFACE-HMAC, ~
                but this is not the case." hmac))
       ;; retrieve key size limit, block size, and output size
       ;; of the HMAC function:
       (info (cdr pair))
       (key-size-limit (definterface-hmac-info->key-size-limit info))
       (block-size (definterface-hmac-info->block-size info))
       (output-size (definterface-hmac-info->output-size info))
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
       (guard (if key-size-limit
                  `(and (byte-listp password)
                        (< (len password) ,key-size-limit)
                        (byte-listp salt)
                        (< (len salt) (- (- ,key-size-limit
                                            ,block-size)
                                         4))
                        (posp iterations)
                        (posp length)
                        (<= length (* (1- (expt 2 32)) ,output-size)))
                `(and (byte-listp password)
                      (byte-listp salt)
                      (posp iterations)
                      (posp length)
                      (<= length (* (1- (expt 2 32)) ,output-size)))))
       ;; function signature:
       (sig `((,name * * * *) => *
              :formals (password salt iterations length)
              :guard ,guard))
       ;; generated events:
       (wit `(local
              (defun ,name (password salt iterations length)
                (declare (ignore password salt iterations))
                (make-list (pos-fix length) :initial-element 0))))
       (byte-listp-thm `(defrule ,byte-listp-thm-name
                          (byte-listp (,name password salt iterations length))))
       (len-thm `(defrule ,len-thm-name
                   (equal (len (,name password salt iterations length))
                          (pos-fix length))))
       (fix-thms `(fty::deffixequiv ,name
                    :args ((password byte-listp)
                           (salt byte-listp)
                           (iterations posp)
                           (length posp))))
       (true-listp-thm `(defrule ,true-listp-thm-name
                          (true-listp (,name password salt iterations length))
                          :rule-classes :type-prescription
                          :enable acl2::true-listp-when-byte-listp))
       (consp-thm `(defrule ,consp-thm-name
                     (consp (,name password salt iterations length))
                     :rule-classes :type-prescription
                     :use ,len-thm-name
                     :disable ,len-thm-name)))
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
         ,consp-thm))))

(defsection definterface-pbkdf2-macro-definition
  :short "Definition of the @(tsee definterface-pbkdf2) macro."
  :long (xdoc::topstring-@def "definterface-pbkdf2")
  (defmacro definterface-pbkdf2 (name
                                 &key
                                 hmac
                                 topic
                                 parents
                                 short
                                 long)
    `(make-event (definterface-pbkdf2-fn
                   ',name
                   ',hmac
                   ',topic
                   ',parents
                   ,short
                   ,long
                   (w state)))))
