; String Utilities -- Conversions between Characters and Codes
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Alessandro Coglio (coglio@kestrel.edu)
; Contributing Author: Mihir Mehta (mihir@cs.utexas.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)
(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "std/strings/make-character-list" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc charlist-codelist-conversions
  :parents (string-utilities)
  :short "Conversions between lists of characters and lists of codes.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This rule, taken from the filesystem books, is needed in two different
;; sections below.
(defrulel nthcdr-of-nil (equal (nthcdr n nil) nil))

(define nats=>chars ((nats (unsigned-byte-listp 8 nats)))
  :returns (chars character-listp)
  :parents (charlist-codelist-conversions)
  :short "Convert a true list of natural numbers below 256
          to the corresponding true list of characters."
  :long
  (xdoc::topstring-p
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
             nil)))

  (defruled nats=>chars-of-revappend
    (equal (nats=>chars (revappend x y))
           (revappend (nats=>chars x) (nats=>chars y)))
    :disable revappend-removal)

  (defrule nats=>chars-of-nthcdr
    (equal (nats=>chars (nthcdr n nats))
           (nthcdr n (nats=>chars nats)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define chars=>nats ((chars character-listp))
  :returns (nats (unsigned-byte-listp 8 nats))
  :parents (charlist-codelist-conversions)
  :short "Convert a true list of characters
          to the corresponding true list of natural numbers below 256."
  :long
  (xdoc::topstring-p
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

  (defrule chars=>nats-of-make-character-list
    (equal (chars=>nats (make-character-list x))
           (chars=>nats x)))

  (defrule consp-of-chars=>nats
    (iff (consp (chars=>nats chars))
         (consp chars)))

  (defrule chars=>nats-of-make-list-ac
    (equal (chars=>nats (make-list-ac n val ac))
           (make-list-ac n (char-code val)
                         (chars=>nats ac))))

  (defrule chars=>nats-of-take
    (implies (<= (nfix n) (len chars))
             (equal (chars=>nats (take n chars))
                    (take n (chars=>nats chars)))))

  (defrule chars=>nats-of-nthcdr
    (equal (chars=>nats (nthcdr n chars))
           (nthcdr n (chars=>nats chars))))

  (defruled chars=>nats-of-revappend
    (equal (chars=>nats (revappend x y))
           (revappend (chars=>nats x) (chars=>nats y)))
    :disable revappend-removal))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection nats<=>chars-inverses-theorems
  :parents (nats=>chars chars=>nats)
  :short "@(tsee nats=>chars) and @(tsee chars=>nats)
          are mutual inverses."

  (defrule chars=>nats-of-nats=>chars
    (implies (unsigned-byte-listp 8 (true-list-fix nats))
             (equal (chars=>nats (nats=>chars nats))
                    (true-list-fix nats)))
    :enable (chars=>nats nats=>chars)
    :rule-classes
    ((:rewrite
      :corollary (implies (unsigned-byte-listp 8 nats)
                          (equal (chars=>nats (nats=>chars nats))
                                 nats)))))

  (defrule nats=>chars-of-chars=>nats
    (equal (nats=>chars (chars=>nats chars))
           (make-character-list chars))
    :prep-lemmas
    ((defruled
       nats=>chars-of-chars=>nats-when-character-listp
       (implies (character-listp chars)
                (equal (nats=>chars (chars=>nats chars))
                       chars))
       :enable (nats=>chars chars=>nats)
       :induct (chars=>nats chars)))
    :use
    (:instance nats=>chars-of-chars=>nats-when-character-listp
               (chars (make-character-list chars)))))
