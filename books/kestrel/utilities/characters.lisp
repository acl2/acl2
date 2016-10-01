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

(std::deflist alpha/digit/dash-char-list-p (x)
  (alpha/digit/dash-char-p x)
  :guard (character-listp x)
  :parents (character-utilities)
  :short "True iff all the characters in @('chars') are
          letters, (decimal) digits, or dashes."
  :true-listp nil
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nats=>chars ((nats (unsigned-byte-listp 8 nats)))
  :returns (chars character-listp)
  :parents (character-utilities)
  :short "Convert a list of natural numbers below 256
          to the corresponding list of characters."
  (cond ((endp nats) nil)
        (t (cons (code-char (car nats))
                 (nats=>chars (cdr nats)))))
  ///

  (more-returns
   (chars true-listp
          :name true-listp-of-nats=>chars
          :rule-classes :type-prescription)))

(define chars=>nats ((chars character-listp))
  :returns (nats (unsigned-byte-listp 8 nats))
  :parents (character-utilities)
  :short "Convert a list of characters
          to the corresponding list of natural numbers below 256."
  (cond ((endp chars) nil)
        (t (cons (char-code (car chars))
                 (chars=>nats (cdr chars)))))
  ///

  (more-returns
   (nats true-listp
         :name true-listp-of-chars=>nats
         :rule-classes :type-prescription)
   (nats nat-listp
         :name nat-listp-of-chars=>nats)))
