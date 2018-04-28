; Character Utilities
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/deflist" :dir :system)
(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)

(local (include-book "std/lists/top" :dir :system))
(local (include-book "std/typed-lists/character-listp" :dir :system))
(local (include-book "typed-list-theorems"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc character-utilities
  :parents (kestrel-utilities)
  :short "Utilities for @(see characters).")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define alpha/digit/dash-char-p ((char characterp))
  :returns (yes/no booleanp)
  :parents (character-utilities)
  :short "Check if a character is a letter, a (decimal) digit, or a dash."
  (or (and (standard-char-p char)
           (alpha-char-p char))
      (if (digit-char-p char) t nil)
      (eql char #\-)))

(std::deflist alpha/digit/dash-char-listp (x)
  (alpha/digit/dash-char-p x)
  :guard (character-listp x)
  :parents (character-utilities)
  :short "Check if a true list of characters
          includes only letters, (decimal) digits, and dashes."
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nondigit-char-p ((char characterp))
  :returns (yes/no booleanp)
  :parents (character-utilities)
  :short "Check if a character is not a (decimal) digit."
  (not (digit-char-p char)))

(std::deflist nondigit-char-listp (x)
  (nondigit-char-p x)
  :guard (character-listp x)
  :parents (character-utilities)
  :short "Check if a true list of characters includes no (decimal) digits."
  :true-listp t
  :elementp-of-nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nats=>chars ((nats (unsigned-byte-listp 8 nats)))
  :returns (chars character-listp)
  :parents (character-utilities)
  :short "Convert a true list of natural numbers below 256
          to the corresponding true list of characters."
  (mbe :logic (cond ((endp nats) nil)
                    (t (cons (code-char (car nats))
                             (nats=>chars (cdr nats)))))
       :exec (nats=>chars-aux nats nil))
  :verify-guards nil ; done below

  :prepwork
  ((define nats=>chars-aux ((nats (unsigned-byte-listp 8 nats))
                            (rev-chars character-listp))
     (cond ((endp nats) (rev rev-chars))
           (t (nats=>chars-aux (cdr nats)
                               (cons (code-char (car nats))
                                     rev-chars))))
     :enabled t))

  ///

  (more-returns
   (chars true-listp
          :name true-listp-of-nats=>chars
          :rule-classes :type-prescription))

  (local
   (defrule verify-guards-lemma-1
     (equal (nats=>chars-aux nats rev-chars)
            (revappend rev-chars (nats=>chars nats)))))

  (local
   (defrule verify-guards-lemma-2
     (equal (nats=>chars-aux nats nil)
            (nats=>chars nats))))

  (verify-guards nats=>chars))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define chars=>nats ((chars character-listp))
  :returns (nats (unsigned-byte-listp 8 nats))
  :parents (character-utilities)
  :short "Convert a true list of characters
          to the corresponding true list of natural numbers below 256."
  (mbe :logic (cond ((endp chars) nil)
                    (t (cons (char-code (car chars))
                             (chars=>nats (cdr chars)))))
       :exec (chars=>nats-aux chars nil))
  :verify-guards nil ; done below

  :prepwork
  ((define chars=>nats-aux ((chars character-listp)
                            (rev-nats (unsigned-byte-listp 8 rev-nats)))
     (cond ((endp chars) (rev rev-nats))
           (t (chars=>nats-aux (cdr chars)
                               (cons (char-code (car chars))
                                     rev-nats))))
     :enabled t))

  ///

  (more-returns
   (nats true-listp
         :name true-listp-of-chars=>nats
         :rule-classes :type-prescription)
   (nats nat-listp
         :name nat-listp-of-chars=>nats))

  (local
   (defrule verify-guards-lemma-1
     (equal (chars=>nats-aux chars rev-nats)
            (revappend rev-nats (chars=>nats chars)))))

  (local
   (defrule verify-guards-lemma-2
     (equal (chars=>nats-aux chars nil)
            (chars=>nats chars))))

  (verify-guards chars=>nats))
