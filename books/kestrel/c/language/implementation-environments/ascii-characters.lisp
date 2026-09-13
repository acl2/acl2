; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "../../portcullis")

(include-book "kestrel/utilities/integers-from-to-as-set" :dir :system)
(include-book "kestrel/utilities/strings/char-code-map" :dir :system)
(include-book "kestrel/utilities/strings/chars-codes" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ascii-characters
  :parents (character-sets)
  :short "ASCII characters represented by ACL2 characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "[C17] and [C23] do not require ASCII, and our "
    (xdoc::seetopic "character-sets" "model of character sets")
    " is more general than ASCII.
     Our model admits ASCII as a possibility,
     and @(tsee charset-ascii) is a utility to facilitate
     the definition of implementation environments that use ASCII.")
   (xdoc::p
    "We represent ASCII characters by the ACL2 characters
     with codes from 0 to 127.
     The constructors @(tsee source-charset-ascii) and
     @(tsee exec-charset-ascii) share this representation
     and the map from characters to their codes."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ascii-chars ()
  :returns (chars character-setp)
  :short "Set of all ASCII characters."
  (set::mergesort (acl2::nats=>chars (acl2::integers-from-to 0 127)))

  ///

  (defruled char-code-set-of-ascii-chars
    (equal (acl2::char-code-set (ascii-chars))
           (acl2::integers-from-to 0 127)))

  (in-theory (disable (:e ascii-chars)))

  (defret in-of-ascii-chars
    (equal (set::in char chars)
           (and (characterp char)
                (< (char-code char) 128)))
    :hints
    (("Goal"
      :use ((:instance acl2::code-in-char-code-set-when-char-in-char-set
                       (acl2::chs (ascii-chars))
                       (acl2::ch char))
            (:instance acl2::not-in-char-code-set-when-not-in-char-set
                       (acl2::chars (ascii-chars))
                       (acl2::char char)))
      :in-theory (e/d (char-code-set-of-ascii-chars)
                      (ascii-chars
                       (:e acl2::integers-from-to)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ascii-code-map ()
  :returns (map acl2::character-nat-mapp)
  :short "Map from ASCII characters to their codes."
  (acl2::char-code-map (ascii-chars))

  ///

  (in-theory (disable (:e ascii-code-map)))

  (defret keys-of-ascii-code-map
    (equal (omap::keys map) (ascii-chars)))

  (defret values-of-ascii-code-map
    (equal (omap::values map) (acl2::char-code-set (ascii-chars))))

  (defret injectivep-of-ascii-code-map
    (omap::injectivep map))

  (defret lookup-of-ascii-code-map
    (implies (set::in char (ascii-chars))
             (equal (omap::lookup char map) (char-code char))))

  (defret lookup-inverse-of-ascii-code-map
    (implies (set::in char (ascii-chars))
             (equal (omap::lookup (char-code char) (omap::inverse map))
                    char))))
