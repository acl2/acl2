; A tool to introduce a prime number and prove various properties
;
; Copyright (C) 2019-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)
; Contributing Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PRIMES")

;; This utility defines a constant, a 0-ary function, and several rules about
;; the given prime number.  It is intended to be used for large primes for
;; which calling primep takes too long.  It requires a Pratt certificate to
;; prove primality.

;; TODO: Add xdoc.

(include-book "projects/quadratic-reciprocity/euclid" :dir :system) ;for rtl::primep
(include-book "kestrel/utilities/pack" :dir :system)
(include-book "kestrel/utilities/doc" :dir :system)
(include-book "kestrel/strings-light/downcase" :dir :system)
(include-book "std/util/add-io-pairs" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;; Prevent very expensive calls to primep:
(in-theory (disable (:e rtl::primep)))

(defund defprime-fn (name
                     number
                     pratt-cert
                     existing-prime-name ;; nil, of the name of existing prime (created using defprime) equal to this prime
                     evisc
                     parents
                     short
                     long
                     wrld)
  (declare (xargs :guard (and (symbolp name)
                              (if existing-prime-name
                                  (eq :none number)
                                (posp number))
                              (if existing-prime-name
                                  (eq :none pratt-cert)
                                (true-listp pratt-cert)) ;; todo: strengthen?
                              (booleanp evisc)
                              (or (eq :auto parents)
                                  (symbol-listp parents))
                              (or (eq :auto short)
                                  (stringp short))
                              (or (eq :auto long)
                                  (stringp long))
                              (symbolp existing-prime-name) ; may be nil, for none
                              (plist-worldp wrld))))
  (b* ((defprime-alist (table-alist 'defprime-table wrld))
       ((when (not (alistp defprime-alist)))
        (er hard? 'defprime "Ill-formed defprime-alist:." defprime-alist))
       ((when (and existing-prime-name
                   (not (assoc-eq existing-prime-name defprime-alist))))
        (er hard? 'defprime "No existing prime found for name ~x0." existing-prime-name))
       (number (if existing-prime-name
                   (cdr (assoc-eq existing-prime-name defprime-alist))
                 number))
       ((when (not (natp number)))
        (er hard? 'defprime "Bad value for existing prime: ~x0." number))
       (defconst-name (acl2::pack-in-package-of-symbol name '* name '*))
       (pratt-cert-defconst-name (acl2::pack-in-package-of-symbol name '* name '-pratt-cert*))
       (parents (if (eq :auto parents)
                    (list 'acl2::number-theory) ;todo: use something better here, perhaps acl2::primes?
                  parents))
       (short (if (eq :auto short)
                  "A prime defined by @(tsee defprime)."
                short))
       (long (if (eq :auto long)
                 ;; Default :long documentation:
                 (concatenate 'string "<p>The value of " (acl2::string-downcase-gen (symbol-name name)) " is " (acl2::nat-to-string number) ".</p>")
               long)))
    `(encapsulate ()

       ,@(and (not existing-prime-name)
              '((local (include-book "projects/quadratic-reciprocity/pratt" :dir :system))))

       ;; Prevent very expensive calls to primep.
       (local (in-theory (disable (:e rtl::primep))))

       ;; A defconst representing the prime.
       (defconst ,defconst-name ,number)

       ;; A 0-ary function.  Using this instead of the defconst can make things
       ;; more readable, since the defconst will be turned into a number when
       ;; terms are translated.  Also, this allows us to disable concrete
       ;; executions involving the prime by disabling the
       ;; :executable-counterpart.
       (defund ,name ()
         (declare (xargs :guard t))
         ,defconst-name)

       ;; (in-theory (disable (:e ,name)))

       ;; Macro to turn on evisceration (printing of the prime using its symbolic name):
       (defmacro ,(acl2::pack-in-package-of-symbol name 'eviscerate- name) ()
         `(table acl2::evisc-table ,,number ,,(concatenate 'string "#.*" (symbol-name name) "*")))

       ;; Macro to turn off evisceration (printing of the prime using its symbolic name):
       (defmacro ,(acl2::pack-in-package-of-symbol name 'uneviscerate- name) ()
         `(table acl2::evisc-table ,,number nil))

       ,@(and evisc
              ;; Actually turn on the evisceration:
              `((,(acl2::pack-in-package-of-symbol name 'eviscerate- name))))

       ;; We use Russinoff's algorithm from "Pratt certification and the primality of 2^255 - 19"
       ;; where a Pratt certificate of n is a tree
       ;; (r (p1 ... pn) (e1 ... en) (c1 ... cn))
       ;; such that
       ;; 1. r is primitive root of n
       ;; 2. n - 1 = (p1^e1)...(pn^en)
       ;; 3. ci is a pratt certificate of pi.

       (defconst ,pratt-cert-defconst-name ',pratt-cert)

       ;; Primality theorem for the constant.
       ;; Since primep may often be disabled and this cannot be efficiently executed.
       (defthm ,(acl2::pack-in-package-of-symbol name 'primep-of- name '-constant)
         (rtl::primep ,defconst-name)
         ,@(if existing-prime-name
               `(:hints (("Goal" :use (:instance ,(acl2::pack-in-package-of-symbol existing-prime-name 'primep-of- existing-prime-name '-constant))
                          :in-theory nil)))
             `(:hints (("Goal" :in-theory (enable (:e rtl::certify-prime))
                        :use (:instance rtl::certification-theorem
                                        (p ,defconst-name)
                                        (c ,pratt-cert-defconst-name)))))))

       ;; Primality theorem for the 0-ary function.
       (defthm ,(acl2::pack-in-package-of-symbol name 'primep-of- name)
         (rtl::primep (,name))
         :hints (("Goal" :in-theory '(,name)
                  :use (:instance ,(acl2::pack-in-package-of-symbol name 'primep-of- name '-constant)))))

       ;; To allow the :linear rule to be created.
       (local (in-theory (disable (:e ,name))))

       ;; A fairly strong linear rule.  Should allow ACL2 to prove that a call
       ;; of the 0-ary function is greater than 2, etc.
       (defthm ,(acl2::pack-in-package-of-symbol name name '-linear)
         (= (,name) ,defconst-name)
         ;; The :trigger-terms here allow the rule to be included in worlds
         ;; where (:e ,name) is enabled.
         :rule-classes ((:linear :trigger-terms ((,name))))
         :hints (("Goal" :in-theory (enable (:e ,name)))))

       ;; Avoid expensive calls of primep by building in the fact that it is
       ;; true for this prime:
       ,@(and (not existing-prime-name)
              `((acl2::add-io-pairs (((rtl::primep (,name)) t)))))

       (defxdoc ,name :parents ,parents :short ,short :long ,long)

       ;; record the prime in the table of primes
       (table defprime-table ',name ,number))))

;; Introduce a prime (as a constant and as a 0-ary function) and prove helpful
;; properties of it.
(acl2::defmacrodoc defprime (name number pratt-cert
                                  &key
                                  (evisc 't)
                                  (parents ':auto)
                                  (short ':auto)
                                  (long ':auto))
  `(make-event (defprime-fn ',name ',number ',pratt-cert nil ',evisc
                 ',parents ,short ,long
                 (w state)))
  :parents (acl2::number-theory)
  :short "Introduce a prime and related machinery."
  :inputs (name "Name of the prime to introduce, a symbol."
           number "Numeric value of the prime, a natural number."
           pratt-cert "Pratt certificate for the prime."
           :evisc "Whether to print occurrences of the prime using its symbolic name."
           :parents "Xdoc :parents for the prime."
           :short "Xdoc :short description for the prime."
           :long "Xdoc :long section for the prime.")
  :long (xdoc::topstring
         (xdoc::p "Defprime generates, for a prime named FOO:")
         (xdoc::ul
           (xdoc::li "A constant, *FOO*, representing the prime.")
           (xdoc::li "A theorem that *FOO* is prime.")
           (xdoc::li "A 0-ary function, FOO, representing the prime.  This is disabled but its :executable-counterpart is not (disable the :executable-counterpart to prevent execution during proofs).")
           (xdoc::li "A theorem that the function FOO always returns a prime.")
           (xdoc::li "A :linear rule stating that the function FOO is equal to the prime (i.e., its integer value).")
           (xdoc::li "A utility, eviscerate-FOO, to cause the prime to be printed using a symbolic name.  This is in turn invoked by defprime to turn on evisceration, unless the :evisc argument is nil.")
           (xdoc::li "A utility, uneviscerate-FOO, to turn off the evisceration mentioned just above.")
           (xdoc::li "A constant, *FOO-pratt-cert*, for the Pratt certificate supplied for FOO.")
           (xdoc::li "A @(tsee defxdoc) form for the prime, using the supplied :short, :long, and :parents, or suitable defaults for each.")
           (xdoc::li "A call of @(tsee acl2::add-io-pairs) to cause rtl::primep to be fast when called on the prime.")
           (xdoc::li "A @(tsee table) event that records the call of defprime."))))

;; Variant of defprime that defines a prime that is numerically equal to an existng prime.
(acl2::defmacrodoc defprime-alias (name existing-prime-name &key
                                        (evisc 't)
                                        (parents ':auto)
                                        (short ':auto)
                                        (long ':auto))
  `(make-event (defprime-fn ',name ',:none ':none ',existing-prime-name ',evisc
                 ',parents ,short ,long
                 (w state)))
  :parents (acl2::number-theory)
  :short "Introduce an alias of an existing prime introduced with defprime."
  :inputs (name "Name of the prime to introduce, a symbol."
           existing-prime-name "Name of the existing prime, a symbol."
           :evisc "Whether to print occurrences of the prime using its symbolic name."
           :parents "Xdoc :parents for the prime."
           :short "Xdoc :short description for the prime."
           :long "Xdoc :long section for the prime.")
  :long "Defprime-alias generates all of the things generated by @(tsee defprime), except that it omits the call to @(tsee acl2::add-io-pairs), since that has already been done for the existing prime, which has the same numeric value as the new prime.")
