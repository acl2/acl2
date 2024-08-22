; Standard Strings Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "STR")

(include-book "std/strings/coerce" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection explode-implode-equalities
  :parents (std/strings explode implode)
  :short "Theorems about equalities involving
          @(tsee explode) and @(tsee implode)."

  (defthmd equal-of-implode-left-to-equal-of-explode-right
    (implies (and (character-listp a)
                  (stringp b))
             (equal (equal (implode a) b)
                    (equal a (explode b)))))

  (defthmd equal-of-implode-right-to-equal-of-explode-left
    (implies (and (character-listp a)
                  (stringp b))
             (equal (equal a (implode b))
                    (equal (explode a) b))))

  (defthmd equal-of-explode-left-to-equal-of-implode-right
    (implies (and (character-listp a)
                  (stringp b))
             (equal (equal (explode a) b)
                    (equal a (implode b)))))

  (defthmd equal-of-explode-right-to-equal-of-implode-left
    (implies (and (character-listp a)
                  (stringp b))
             (equal (equal a (explode b))
                    (equal (implode a) b))))

  (theory-invariant
   (incompatible (:rewrite equal-of-implode-left-to-equal-of-explode-right)
                 (:rewrite equal-of-explode-right-to-equal-of-implode-left)))

  (theory-invariant
   (incompatible (:rewrite equal-of-implode-right-to-equal-of-explode-left)
                 (:rewrite equal-of-explode-left-to-equal-of-implode-right))))
