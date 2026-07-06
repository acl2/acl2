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
    :enable char-code-set))
