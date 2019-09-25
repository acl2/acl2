; String Utilities -- Conversions between Strings and Character Codes
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Alessandro Coglio (coglio@kestrel.edu)
; Contributing Author: Mihir Mehta (mihir@cs.utexas.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/strings/coerce" :dir :system)

(include-book "chars-codes")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc string-codelist-conversions
  :parents (string-utilities)
  :short "Conversions between strings and lists of character codes.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nats=>string ((nats (unsigned-byte-listp 8 nats)))
  :returns (string stringp)
  :parents (string-codelist-conversions)
  :short "Convert a true list of natural numbers below 256
          to the corresponding string."
  (implode (nats=>chars nats))
  ///

  (defrule nth-of-explode-of-nats=>string
    (equal (nth i (explode (nats=>string nats)))
           (if (< (nfix i) (len nats))
               (code-char (nth i nats))
             nil)))

  (defrule len-of-explode-of-nats=>string
    (equal (len (explode (nats=>string nats)))
           (len nats)))

  (defrule explode-of-nats=>string
    (equal (explode (nats=>string nats))
           (nats=>chars nats))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define string=>nats ((string stringp))
  :returns (nats (unsigned-byte-listp 8 nats))
  :parents (string-codelist-conversions)
  :short "Convert a string
          to the corresponding true list of natural numbers below 256."
  (chars=>nats (explode string))
  ///

  (more-returns
   (nats nat-listp
         :name nat-listp-of-string=>nats))

  (defrule len-of-string=>nats
    (implies (stringp string)
             (equal (len (string=>nats string))
                    (length string))))

  (defrule nth-of-string=>nats
    (equal (nth n (string=>nats string))
           (if (< (nfix n) (len (explode string)))
               (char-code (char string n))
             nil)))

  (defrule consp-of-string=>nats
    (iff (consp (string=>nats string))
         (consp (explode string))))

  (defrule string=>nats-of-implode
    (implies (character-listp chars)
             (equal (string=>nats (implode chars))
                    (chars=>nats chars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection nats<=>string-inverses-theorems
  :parents (nats=>string string=>nats)
  :short "@(tsee nats=>string) and @(tsee string=>nats)
          are mutual inverses."

  (defrule nats=>string-of-string=>nats
    (equal (nats=>string (string=>nats string))
           (str-fix string))
    :enable (nats=>string string=>nats))

  (defrule string=>nats-of-nats=>string
    (implies (unsigned-byte-listp 8 (true-list-fix nats))
             (equal (string=>nats (nats=>string nats))
                    (true-list-fix nats)))
    :rule-classes
    ((:rewrite
      :corollary (implies (unsigned-byte-listp 8 nats)
                          (equal (string=>nats (nats=>string nats))
                                 nats))))
    :enable (string=>nats nats=>string)
    :use chars=>nats-of-nats=>chars))
