; Proofs about simple-untranslate-in-term
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "simple-untranslate-in-term")
(include-book "tools/flag" :dir :system)

;; The untranslate pass leaves atoms alone.
(defthm simple-untranslate-in-term-when-atom
  (implies (atom term)
           (equal (simple-untranslate-in-term term) term))
  :hints (("Goal" :in-theory (enable simple-untranslate-in-term))))

;; Length preservation on the -in-terms walker (used when proving theorems
;; about callers that walk argument lists).
(make-flag simple-untranslate-in-term)

(defthm-flag-simple-untranslate-in-term
  (defthm len-of-simple-untranslate-in-terms
    (equal (len (simple-untranslate-in-terms terms))
           (len terms))
    :flag simple-untranslate-in-terms)
  :skip-others t
  :hints (("Goal" :in-theory (enable simple-untranslate-in-terms))))

;; True-listp preservation on the -in-terms walker.
(defthm-flag-simple-untranslate-in-term
  (defthm true-listp-of-simple-untranslate-in-terms
    (equal (true-listp (simple-untranslate-in-terms terms))
           (true-listp terms))
    :flag simple-untranslate-in-terms)
  :skip-others t
  :hints (("Goal" :in-theory (enable simple-untranslate-in-terms))))
