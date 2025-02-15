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

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

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
               base
               number-prefix
               (acl2::implode (explode-nonnegative-integer number 10 nil))
               number-suffix)
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
     (b* (((when (eql 0 (mbe :logic (nfix steps)
                             :exec (acl2::the-fixnat steps))))
           (mbe :logic (if (stringp base)
                           base
                         "")
                :exec base))
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
     :measure (nfix steps)
     :hints (("Goal" :in-theory (enable o< o-finp nfix)))
     :guard-hints (("Goal" :in-theory (enable nfix))))))

(define fresh-string-wrt
  ((base stringp)
   (number-prefix stringp)
   (number-suffix stringp)
   (blacklist acl2::string-setp))
  :returns (string stringp)
  (if (in base blacklist)
      (fresh-numbered-string-wrt base number-prefix 0 number-suffix blacklist)
    (mbe :logic (if (stringp base)
                    base
                  "")
         :exec base)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define map-ident->unwrap
  ((idents ident-setp))
  :returns (strings acl2::string-setp)
  (b* (((when (emptyp idents))
        nil)
       (unwrapped-head (ident->unwrap (head idents))))
    (if (stringp unwrapped-head)
        (insert unwrapped-head
                (map-ident->unwrap (tail idents)))
      (map-ident->unwrap (tail idents))))
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
                        string-blacklist))))

(define fresh-idents
  ((idents ident-listp)
   (blacklist ident-setp)
   &key
   ((number-prefix stringp) '"_")
   ((number-suffix stringp) '""))
  :returns (idents$ ident-listp)
  (b* (((when (endp idents))
        nil)
       (ident$ (fresh-ident (first idents)
                            blacklist
                            :number-prefix number-prefix
                            :number-suffix number-suffix)))
    (cons ident$
          (fresh-idents (rest idents)
                        (insert ident$ blacklist)
                        :number-prefix number-prefix
                        :number-suffix number-suffix))))

(defrule len-of-fresh-idents
  (equal (len (fresh-idents idents
                            blacklist
                            :number-prefix number-prefix
                            :number-suffix number-suffix))
         (len idents))
  :induct t
  :enable (fresh-idents
           len))

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
