; String Utilities -- Conversions between Characters and Codes
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/xdoc/constructors" :dir :system)
(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc charlist-codelist-conversions
  :parents (string-utilities)
  :short "Conversions between lists of characters and lists of codes.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nats=>chars ((nats (unsigned-byte-listp 8 nats)))
  :returns (chars character-listp)
  :parents (charlist-codelist-conversions)
  :short "Convert a true list of natural numbers below 256
          to the corresponding true list of characters."
  :long
  (xdoc::topp
   "This operation has
    a natural-recursive definition for logic reasoning
    and a tail-recursive executional for execution.")
  (mbe :logic (cond ((endp nats) nil)
                    (t (cons (code-char (car nats))
                             (nats=>chars (cdr nats)))))
       :exec (nats=>chars-exec nats nil))
  :verify-guards nil ; done below

  :prepwork
  ((define nats=>chars-exec ((nats (unsigned-byte-listp 8 nats))
                             (rev-chars character-listp))
     (cond ((endp nats) (rev rev-chars))
           (t (nats=>chars-exec (cdr nats)
                                (cons (code-char (car nats))
                                      rev-chars))))
     :enabled t))

  ///

  (defrulel verify-guards-lemma-1
    (equal (nats=>chars-exec nats rev-chars)
           (revappend rev-chars (nats=>chars nats))))

  (defrulel verify-guards-lemma-2
    (equal (nats=>chars-exec nats nil)
           (nats=>chars nats)))

  (verify-guards nats=>chars)

  (defrule len-of-nats=>chars
    (equal (len (nats=>chars nats))
           (len nats)))

  (defrule nats=>chars-of-cons
    (equal (nats=>chars (cons nat nats))
           (cons (code-char nat)
                 (nats=>chars nats))))

  (defrule nats=>chars-of-append
    (equal (nats=>chars (append nats1 nats2))
           (append (nats=>chars nats1)
                   (nats=>chars nats2))))

  (defrule nats=>chars-of-repeat
    (equal (nats=>chars (repeat n char))
           (repeat n (code-char char)))
    :enable repeat)

  (defrule nth-of-nats=>chars
    (equal (nth i (nats=>chars nats))
           (if (< (nfix i) (len nats))
               (code-char (nth i nats))
             nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define chars=>nats ((chars character-listp))
  :returns (nats (unsigned-byte-listp 8 nats))
  :parents (charlist-codelist-conversions)
  :short "Convert a true list of characters
          to the corresponding true list of natural numbers below 256."
  :long
  (xdoc::topp
   "This operation has
    a natural-recursive definition for logic reasoning
    and a tail-recursive executional for execution.")
  (mbe :logic (cond ((endp chars) nil)
                    (t (cons (char-code (car chars))
                             (chars=>nats (cdr chars)))))
       :exec (chars=>nats-exec chars nil))
  :verify-guards nil ; done below

  :prepwork
  ((define chars=>nats-exec ((chars character-listp)
                             (rev-nats (unsigned-byte-listp 8 rev-nats)))
     (cond ((endp chars) (rev rev-nats))
           (t (chars=>nats-exec (cdr chars)
                                (cons (char-code (car chars))
                                      rev-nats))))
     :enabled t))

  ///

  (more-returns
   (nats nat-listp
         :name nat-listp-of-chars=>nats)
   (nats integer-listp))

  (defrulel verify-guards-lemma-1
    (equal (chars=>nats-exec chars rev-nats)
           (revappend rev-nats (chars=>nats chars))))

  (defrulel verify-guards-lemma-2
    (equal (chars=>nats-exec chars nil)
           (chars=>nats chars)))

  (verify-guards chars=>nats)

  (defrule len-of-chars=>nats
    (equal (len (chars=>nats chars))
           (len chars)))

  (defrule chars=>nats-of-cons
    (equal (chars=>nats (cons char chars))
           (cons (char-code char)
                 (chars=>nats chars))))

  (defrule chars=>nats-of-append
    (equal (chars=>nats (append chars1 chars2))
           (append (chars=>nats chars1)
                   (chars=>nats chars2))))

  (defrule chars=>nats-of-repeat
    (equal (chars=>nats (repeat n char))
           (repeat n (char-code char)))
    :enable repeat)

  (defrule nth-of-chars=>nats
    (equal (nth i (chars=>nats chars))
           (if (< (nfix i) (len chars))
               (char-code (nth i chars))
             nil)))

  (defrule
    chars=>nats-of-nats=>chars
    (implies (unsigned-byte-listp 8 (fix-true-list nats))
             (equal (chars=>nats (nats=>chars nats))
                    (fix-true-list nats)))
    :enable nats=>chars
    :rule-classes
    ((:rewrite
      :corollary (implies (unsigned-byte-listp 8 nats)
                          (equal (chars=>nats (nats=>chars nats))
                                 nats))))))
