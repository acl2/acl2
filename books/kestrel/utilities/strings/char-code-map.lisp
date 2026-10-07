; String Utilities
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "char-code-set")

(include-book "kestrel/fty/character-nat-map" :dir :system)
(include-book "std/omaps/injectivep" :dir :system)
(include-book "std/omaps/inverse" :dir :system)

(local (include-book "std/omaps/extensionality" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-code-map ((chars character-setp))
  :returns (map character-nat-mapp)
  :parents (string-utilities)
  :short "Omap from a set of characters to their character codes."
  :long
  (xdoc::topstring-p
   "The keys are exactly the given characters,
    and each character maps to its code.
    Thus, the values form the set returned by @(tsee char-code-set).")
  (b* (((when (set::emptyp (character-sfix chars))) nil)
       (char (set::head chars)))
    (omap::update char
                  (char-code char)
                  (char-code-map (set::tail chars))))
  :prepwork ((local (in-theory (enable emptyp-of-character-sfix))))
  :verify-guards :after-returns

  ///

  (defret keys-of-char-code-map
    (equal (omap::keys map)
           (character-sfix chars))
    :hints (("Goal"
             :induct t
             :in-theory (enable set::emptyp
                                character-sfix))))

  (defret values-of-char-code-map
    (equal (omap::values map)
           (char-code-set chars))
    :hints (("Goal"
             :induct t
             :in-theory (enable char-code-set
                                omap::assoc-to-in-of-keys))))

  (defret lookup-of-char-code-map
    (implies (and (character-setp chars)
                  (set::in char chars))
             (equal (omap::lookup char map)
                    (char-code char)))
    :hints (("Goal"
             :induct t
             :in-theory (enable omap::lookup-of-update))))

  (defruled assoc-of-char-code-map
    (implies (character-setp chars)
             (equal (omap::assoc char (char-code-map chars))
                    (and (set::in char chars)
                         (cons char (char-code char)))))
    :induct t)

  (defruled restrict-of-char-code-map
    (implies (and (character-setp chars)
                  (character-setp keys)
                  (set::subset keys chars))
             (equal (omap::restrict keys (char-code-map chars))
                    (char-code-map keys)))
    :enable (omap::assoc-of-restrict
             assoc-of-char-code-map
             set::expensive-rules)
    :disable char-code-map
    :use (:instance omap::extensionality
                    (omap::x (omap::restrict keys (char-code-map chars)))
                    (omap::y (char-code-map keys))))

  (defret injectivep-of-char-code-map
    (omap::injectivep map)
    :hints (("Goal"
             :induct t
             :in-theory (enable not-in-char-code-set-when-not-in-char-set))))

  (defret lookup-inverse-of-char-code-map
    (implies (and (character-setp chars)
                  (set::in char chars))
             (equal (omap::lookup (char-code char) (omap::inverse map))
                    char))
    :hints
    (("Goal"
      :use (:instance omap::lookup-of-lookup-of-inverse
                      (omap::map (omap::inverse (char-code-map chars)))
                      (omap::val char))
      :in-theory (disable char-code-map)))))
