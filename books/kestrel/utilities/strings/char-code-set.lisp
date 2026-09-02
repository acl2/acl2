; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/fty/character-set" :dir :system)
(include-book "kestrel/fty/nat-set" :dir :system)

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define char-code-set ((chars character-setp))
  :returns (codes nat-setp)
  :parents (string-utilities)
  :short "Map a set of characters to the set of corresponding codes."
  (cond ((set::emptyp (character-sfix chars)) nil)
        (t (set::insert (char-code (set::head chars))
                        (char-code-set (set::tail chars)))))
  :prepwork ((local (in-theory (enable emptyp-of-character-sfix))))
  :verify-guards :after-returns

  ///

  (defruled code-in-char-code-set-when-char-in-char-set
    (implies (and (character-setp chs)
                  (set::in ch chs))
             (set::in (char-code ch) (char-code-set chs)))
    :induct t
    :enable char-code-set)

  (defruled not-in-char-code-set-when-not-in-char-set
    (implies (and (character-setp chars)
                  (characterp char)
                  (not (set::in char chars)))
             (not (set::in (char-code char)
                           (char-code-set chars))))
    :induct t
    :enable str::equal-of-char-codes)

  (defruled char-code-set-monotone
    (implies (and (character-setp chars1)
                  (character-setp chars2)
                  (set::subset chars1 chars2))
             (set::subset (char-code-set chars1)
                          (char-code-set chars2)))
    :induct t
    :enable (code-in-char-code-set-when-char-in-char-set
             set::in-head
             set::subset-in
             set::subset-transitive))

  (defruled char-code-set-upper-bound
    (implies (set::in code (char-code-set chars))
             (<= code 255))
    :induct (char-code-set chars)
    :enable (char-code-set
             set::in)))
