; Character Utilities
;
; Copyright (C) 2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file provides some utilities for characters.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "typed-list-theorems")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc character-utilities
  :parents (kestrel-utilities)
  :short "Some utilities for @(see characters).")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define alpha/digit/dash-char-p ((char characterp))
  :returns (yes/no booleanp)
  :parents (character-utilities)
  :short "True iff the character @('char') is
          a letter, a (decimal) digit, or a dash."
  (or (and (standard-char-p char)
           (alpha-char-p char))
      (if (digit-char-p char) t nil)
      (eql char #\-)))

(std::deflist alpha/digit/dash-char-listp (x)
  (alpha/digit/dash-char-p x)
  :guard (character-listp x)
  :parents (character-utilities)
  :short "True iff all the characters in @('x') are
          letters, (decimal) digits, or dashes."
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nondigit-char-p ((char characterp))
  :returns (yes/no booleanp)
  :parents (character-utilities)
  :short "True iff the character @('char') is not a (decimal) digit."
  (not (digit-char-p char)))

(std::deflist nondigit-char-listp (x)
  (nondigit-char-p x)
  :guard (character-listp x)
  :parents (character-utilities)
  :short "True iff all the characters in @('x') are not (decimal) digits."
  :true-listp t
  :elementp-of-nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nats=>chars ((nats (unsigned-byte-listp 8 nats)))
  :returns (chars character-listp)
  :parents (character-utilities)
  :short "Convert a list of natural numbers below 256
          to the corresponding list of characters."
  (reverse (nats=>chars-aux nats nil))

  :prepwork
  ((define nats=>chars-aux ((nats (unsigned-byte-listp 8 nats))
                            (rev-chars character-listp))
     :returns (final-rev-chars character-listp :hyp (character-listp rev-chars))
     (cond ((endp nats) rev-chars)
           (t (nats=>chars-aux (cdr nats)
                               (cons (code-char (car nats))
                                     rev-chars))))
     ///
     (more-returns
      (final-rev-chars true-listp
                       :hyp (true-listp rev-chars)
                       :name true-listp-of-nats=>chars-aux
                       :rule-classes :type-prescription))))
  ///

  (more-returns
   (chars true-listp
          :name true-listp-of-nats=>chars
          :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define chars=>nats ((chars character-listp))
  :returns (nats (unsigned-byte-listp 8 nats))
  :parents (character-utilities)
  :short "Convert a list of characters
          to the corresponding list of natural numbers below 256."
  (reverse (chars=>nats-aux chars nil))

  :prepwork
  ((define chars=>nats-aux ((chars character-listp)
                            (rev-nats (unsigned-byte-listp 8 rev-nats)))
     :returns (final-rev-nats (unsigned-byte-listp 8 final-rev-nats)
                              :hyp (unsigned-byte-listp 8 rev-nats))
     (cond ((endp chars) rev-nats)
           (t (chars=>nats-aux (cdr chars)
                               (cons (char-code (car chars))
                                     rev-nats))))
     ///
     (more-returns
      (final-rev-nats true-listp
                      :hyp (true-listp rev-nats)
                      :name true-listp-of-chars=>nats-aux
                      :rule-classes :type-prescription)
      (final-rev-nats nat-listp
                      :hyp (nat-listp rev-nats)
                      :name nat-listp-of-chars=>nats-aux))))
  ///

  (more-returns
   (nats true-listp
         :name true-listp-of-chars=>nats
         :rule-classes :type-prescription)
   (nats nat-listp
         :name nat-listp-of-chars=>nats)))
