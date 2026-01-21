; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

(include-book "kestrel/fty/bit-list" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled bit-list-fix-of-last
  (equal (bit-list-fix (last bits))
         (last (bit-list-fix bits))))

(defruled last-of-bit-list-fix
  (equal (last (bit-list-fix bits))
         (bit-list-fix (last bits))))

(theory-invariant
 (incompatible (:rewrite bit-list-fix-of-last)
               (:rewrite last-of-bit-list-fix)))
