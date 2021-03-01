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
(include-book "std/util/add-io-pairs" :dir :system)

(defund defprime-fn (name number pratt-cert
                          existing-prime-name ;; nil, of the name of existing prime (created using defprime) equal to this prime
                          evisc
                          wrld)
  (declare (xargs :guard (and (symbolp name)
                              (if existing-prime-name
                                  (eq :none number)
                                (posp number))
                              (if existing-prime-name
                                  (eq :none pratt-cert)
                                (true-listp pratt-cert)) ;; todo: strengthen?
                              (booleanp evisc)
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
       (defconst-name (acl2::pack-in-package-of-symbol 'defprime '* name '*))
       (pratt-cert-defconst-name (acl2::pack-in-package-of-symbol 'defprime '* name '-pratt-cert*)))
    `(encapsulate ()

       ,@(and (not existing-prime-name)
              '((local (include-book "projects/quadratic-reciprocity/pratt" :dir :system))))

       ;; Prevent very expensive calls to primep.
       ;; TODO: Should we drop this?
       (in-theory (disable (:e rtl::primep)))

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

       ,@(and (not existing-prime-name)
              `((defconst ,pratt-cert-defconst-name
                  ',pratt-cert)))

       ;; Primality theorem for the constant.
       ;; Since primep may often be disabled and this cannot be efficiently executed.
       (defthm ,(acl2::pack-in-package-of-symbol 'defprime 'primep-of- name '-constant)
         (rtl::primep ,defconst-name)
         ,@(if existing-prime-name
               `(:hints (("Goal" :use (:instance ,(acl2::pack-in-package-of-symbol 'defprime 'primep-of- existing-prime-name '-constant))
                          :in-theory nil)))
             `(:hints (("Goal" :in-theory (enable (:e rtl::certify-prime))
                        :use (:instance rtl::certification-theorem
                                        (p ,defconst-name)
                                        (c ,pratt-cert-defconst-name)))))))

       ;; Primality theorem for the 0-ary function.
       (defthm ,(acl2::pack-in-package-of-symbol 'defprime 'primep-of- name)
         (rtl::primep (,name))
         :hints (("Goal" :in-theory '(,name)
                  :use (:instance ,(acl2::pack-in-package-of-symbol 'defprime 'primep-of- name '-constant)))))

       ;; To allow the :linear rule to be created.
       (local (in-theory (disable (:e ,name))))

       ;; A fairly strong linear rule.  Should allow ACL2 to prove that a call
       ;; of the 0-ary function is greater than 2, etc.
       (defthm ,(acl2::pack-in-package-of-symbol 'defprime name '-linear)
         (= (,name) ,defconst-name)
         :rule-classes :linear
         :hints (("Goal" :in-theory (enable (:e ,name)))))

       ;; Avoid expensive calls of primep by building in the fact that it is
       ;; true for this prime:
       ,@(and (not existing-prime-name)
              `((acl2::add-io-pairs (((rtl::primep (,name)) t)))))

       ;; record the prime in the table of primes
       (table defprime-table ',name ,number)
       )))

;; Introduce a prime (as a constant and as a 0-ary function) and prove helpful
;; properties of it.
(defmacro defprime (name number pratt-cert &key (evisc 't))
  `(make-event (defprime-fn ',name ',number ',pratt-cert nil ',evisc (w state))))

;; Variant of defprime that defines a prime that is numerically equal to an existng prime.
(defmacro defprime-alias (name existing-prime-name &key (evisc 't))
  `(make-event (defprime-fn ',name ',:none ':none ',existing-prime-name ',evisc (w state))))
