; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "kestrel/fty/string-set" :dir :system)

(include-book "../../syntax/abstract-syntax-operations")
(include-book "collect-idents")

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ fresh-ident-utility
  :parents (utilities)
  :short "A utility to create a globally fresh C identifier."
  :long
  (xdoc::topstring
    (xdoc::p
      "This utility generates fresh new identifiers using a base identifier and
       adding a numeric suffix. It is similar to @(see acl2::numbered-names),
       but operating over C ASTs instead of the ACL2 world.")
    (xdoc::p
      "Fresh identifiers are created with respect to a \"blacklist\"
       representing identifiers in use. A blacklist may be obtained using the
      @(see collect-idents) utility."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-numbered-string
  ((base stringp)
   (number-prefix stringp)
   (number natp)
   (number-suffix stringp))
  :returns (string stringp)
  (concatenate 'string
               (mbe :logic (acl2::str-fix base) :exec base)
               (mbe :logic (acl2::str-fix number-prefix) :exec number-prefix)
               (acl2::implode (explode-nonnegative-integer
                                (mbe :logic (nfix number) :exec number) 10 nil))
               (mbe :logic (acl2::str-fix number-suffix) :exec number-suffix))
  :guard-hints (("Goal" :in-theory (enable string-listp)))
  :prepwork
  ((defrulel character-listp-of-explode-nonnegative-integer
     (implies (character-listp acc)
              (character-listp (explode-nonnegative-integer n print-base acc)))
     :induct t
     :enable (explode-nonnegative-integer
               character-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: remove the internal "steps" argument and prove termination based on
;; the difference of the blacklist and its implicit subset of already tried
;; names.
(define fresh-numbered-string-wrt
  ((base stringp)
   (number-prefix stringp)
   (number natp)
   (number-suffix stringp)
   (blacklist acl2::string-setp))
  :returns (string stringp)
  (fresh-numbered-string-wrt0
     base
     number-prefix
     number
     number-suffix
     blacklist
     (acl2::the-fixnat (- (expt 2 acl2::*fixnat-bits*) 1)))
  :hooks ((:fix :omit (blacklist)))
  :prepwork
  ((local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
   (define fresh-numbered-string-wrt0
     ((base stringp)
      (number-prefix stringp)
      (number natp)
      (number-suffix stringp)
      (blacklist acl2::string-setp)
      (steps :type #.acl2::*fixnat-type*))
     :returns (string stringp)
     (b* ((number (mbe :logic (nfix number) :exec number))
          (steps (mbe :logic (nfix steps) :exec (acl2::the-fixnat steps)))
          (blacklist (acl2::string-sfix blacklist))
          ((when (= 0 steps))
           (mbe :logic (acl2::str-fix base) :exec base))
          (numbered-string
            (make-numbered-string base number-prefix number number-suffix)))
       (if (in numbered-string blacklist)
           (fresh-numbered-string-wrt0 base
                                       number-prefix
                                       (+ number 1)
                                       number-suffix
                                       blacklist
                                       (- steps 1))
         numbered-string))
     :measure (nfix steps))))

(define fresh-string-wrt
  ((base stringp)
   (number-prefix stringp)
   (number-suffix stringp)
   (blacklist acl2::string-setp))
  :returns (string stringp)
  (let ((base (mbe :logic (acl2::str-fix base) :exec base))
        (blacklist (acl2::string-sfix blacklist)))
    (if (in base blacklist)
        (fresh-numbered-string-wrt base number-prefix 0 number-suffix blacklist)
      base)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define map-ident->unwrap
  ((idents ident-setp))
  :returns (strings acl2::string-setp)
  (b* ((idents (ident-set-fix idents))
       ((when (emptyp idents))
        nil)
       (unwrapped-head (ident->unwrap (head idents))))
    (if (stringp unwrapped-head)
        (insert unwrapped-head
                (map-ident->unwrap (tail idents)))
      (map-ident->unwrap (tail idents))))
  :measure (acl2-count (ident-set-fix idents))
  :verify-guards :after-returns)

(define fresh-ident
  ((ident identp)
   (blacklist ident-setp)
   &key
   ((number-prefix stringp) '"_")
   ((number-suffix stringp) '""))
  :returns (ident$ identp)
  (b* ((ident-string (ident->unwrap ident))
       ((unless (stringp ident-string))
        (raise "Identifier ~x0 does not contain a string."
               ident)
        (c$::irr-ident))
       (string-blacklist (map-ident->unwrap blacklist)))
    (ident
      (fresh-string-wrt ident-string
                        number-prefix
                        number-suffix
                        string-blacklist)))
  :no-function nil)

(define fresh-idents
  ((idents ident-listp)
   (blacklist ident-setp)
   &key
   ((number-prefix stringp) '"_")
   ((number-suffix stringp) '""))
  :returns (idents$ ident-listp)
  (b* ((idents (c$::ident-list-fix idents))
       (blacklist (ident-set-fix blacklist))
       (number-prefix (mbe :logic (acl2::str-fix number-prefix)
                           :exec number-prefix))
       (number-suffix (mbe :logic (acl2::str-fix number-suffix)
                           :exec number-suffix))
       ((when (endp idents))
        nil)
       (ident$ (fresh-ident (first idents)
                            blacklist
                            :number-prefix number-prefix
                            :number-suffix number-suffix)))
    (cons ident$
          (fresh-idents (rest idents)
                        (insert ident$ blacklist)
                        :number-prefix number-prefix
                        :number-suffix number-suffix)))
  :measure (acl2-count (c$::ident-list-fix idents))
  :hints (("Goal" :in-theory (enable c$::ident-list-fix)))
  :hooks ((:fix
           :hints (("Goal"
                     :expand ((fresh-idents idents blacklist
                                            :number-prefix number-prefix
                                            :number-suffix (acl2::str-fix number-suffix))
                              (fresh-idents idents blacklist
                                            :number-prefix number-prefix
                                            :number-suffix number-suffix)))))))

(defrule len-of-fresh-idents
  (equal (len (fresh-idents idents
                            blacklist
                            :number-prefix number-prefix
                            :number-suffix number-suffix))
         (len idents))
  :induct t
  :enable (fresh-idents
           len
           endp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: add tests
(define transunit-ensemble-fresh-ident
  ((ident identp)
   (transunits transunit-ensemblep)
   &key
   ((number-prefix stringp) '"_")
   ((number-suffix stringp) '""))
  :returns (ident$ identp)
  (fresh-ident ident
               (transunit-ensemble-collect-idents transunits)
               :number-prefix number-prefix
               :number-suffix number-suffix))
