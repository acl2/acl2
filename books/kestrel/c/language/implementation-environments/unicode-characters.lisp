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

(include-book "kestrel/fty/any-nat-map" :dir :system)
(include-book "kestrel/utilities/integers-from-to-as-set" :dir :system)
(include-book "kestrel/utilities/strings/char-code-set" :dir :system)
(include-book "std/omaps/injectivep" :dir :system)
(include-book "std/omaps/inverse" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable (:e acl2::integers-from-to))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unicode-characters
  :parents (character-sets)
  :short "Unicode characters represented by their codes."
  :long
  (xdoc::topstring
   (xdoc::p
    "[C17] and [C23] do not require Unicode, and our "
    (xdoc::seetopic "character-sets" "model of character sets")
    " is more general that Unicode.
     Our model admits Unicode as a possibility,
     and indeed we define a Unicode character set
     in @(tsee charset-unicode),
     but just as a utility to facilitate the definition
     of implementation environments that use Unicode.")
   (xdoc::p
    "We identify Unicode characters with Unicode scalar values:
     the codes from 0 to @('#x10ffff'), excluding the surrogate range
     from @('#xd800') to @('#xdfff').
     The source and execution character sets share this representation."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unicode-chars ()
  :returns (chars nat-setp
                  :hints (("Goal"
                           :in-theory
                           (enable unicode-chars
                                   acl2::nat-setp-of-integers-from-to))))
  :short "Set of all Unicode scalar values."
  (set::union (acl2::integers-from-to 0 #xd7ff)
              (acl2::integers-from-to #xe000 #x10ffff))

  ///

  ; Keep the full set symbolic in subsequent proofs.
  (in-theory (disable (:e unicode-chars)))

  (defret in-of-unicode-chars
    (equal (set::in code chars)
           (and (integerp code)
                (or (and (<= 0 code) (<= code #xd7ff))
                    (and (<= #xe000 code) (<= code #x10ffff))))))

  (defrule char-code-in-unicode-chars
    (set::in (char-code char) (unicode-chars)))

  (defruled char-code-set-subset-unicode-chars
    (set::subset (acl2::char-code-set chars) (unicode-chars))
    :induct (acl2::char-code-set chars)
    :enable acl2::char-code-set))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unicode-code-map ()
  :returns (map any-nat-mapp
                :hints (("Goal"
                         :in-theory
                         (enable unicode-code-map
                                 acl2::any-nat-mapp-of-identity))))
  :short "Identity map on Unicode character codes."
  (omap::identity (unicode-chars))

  ///

  ; Keep the full map symbolic in subsequent proofs.
  (in-theory (disable (:e unicode-code-map)))

  (defret identityp-of-unicode-code-map
    (omap::identityp map))

  (defret keys-of-unicode-code-map
    (equal (omap::keys map) (unicode-chars)))

  (defret values-of-unicode-code-map
    (equal (omap::values map) (unicode-chars))
    :hints (("Goal" :in-theory (enable omap::values-is-keys-when-identityp))))

  (defret injectivep-of-unicode-code-map
    (omap::injectivep map)
    :hints (("Goal" :in-theory (enable omap::injectivep-when-identityp))))

  (defret lookup-of-unicode-code-map
    (implies (set::in code (unicode-chars))
             (equal (omap::lookup code map) code))
    :hints (("Goal" :in-theory (enable omap::lookup-when-identityp))))

  (defret lookup-inverse-of-unicode-code-map
    (implies (set::in code (unicode-chars))
             (equal (omap::lookup code (omap::inverse map)) code))
    :hints
    (("Goal"
      :use ((:instance omap::lookup-of-lookup-of-inverse
                       (omap::map (unicode-code-map))
                       (omap::val code))
            (:instance omap::lookup-inverse-in-keys-when-in-values-and-injective
                       (omap::map (unicode-code-map))
                       (omap::y code)))
      :in-theory (disable unicode-code-map)))))
