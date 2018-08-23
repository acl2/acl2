; String Utilities
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "system/kestrel" :dir :system)

(include-book "char-kinds")
(include-book "chars-codes")
(include-book "hexchars")
(include-book "hexstrings")
(include-book "string-kinds")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc string-utilities
  :parents (kestrel-utilities)
  :short "Utilities for @(see strings).")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nats=>string ((nats (unsigned-byte-listp 8 nats)))
  :returns (string stringp)
  :parents (string-utilities)
  :short "Convert a true list of natural numbers below 256
          to the corresponding string."
  (implode (nats=>chars nats)))

(define string=>nats ((string stringp))
  :returns (nats (unsigned-byte-listp 8 nats))
  :parents (string-utilities)
  :short "Convert a string
          to the corresponding true list of natural numbers below 256."
  (chars=>nats (explode string))
  ///

  (more-returns
   (nats nat-listp
         :name nat-listp-of-string=>nats)
   (nats integer-listp))

  (defrule len-of-string=>nats
    (implies (stringp string)
             (equal (len (string=>nats string))
                    (length string)))))
