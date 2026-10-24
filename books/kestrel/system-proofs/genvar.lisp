; Correctness of the ACL2 system function genvar
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; GENVAR (in basis-b.lisp) is "THE function that ACL2 uses to generate new
;; variable names" (from its comments).  It is used, for example, by
;; generalization and destructor elimination, which are sound only if the
;; variables they introduce are new.  We prove that, given its guard, it
;; returns a legal variable that is not in AVOID-LST.

;; Note: The comments in genvar say that it generates a variable "in the same
;; package as pkg-witness", but the result can be a symbol imported into that
;; package.  For example, (genvar 'foo "LIST" nil nil) is COMMON-LISP::LIST
;; (see genvar-tests.lisp).

(defthm genvar1-correct
  (implies (genvar1-guardp pkg-witness char-lst avoid-lst cnt)
           (and (legal-variablep (genvar1 pkg-witness char-lst avoid-lst cnt))
                (not (member-equal (genvar1 pkg-witness char-lst avoid-lst cnt) avoid-lst))))
  :hints (("Goal" :induct (genvar1 pkg-witness char-lst avoid-lst cnt)
           :in-theory (enable genvar1))))

(defthm legal-variablep-of-genvar
  (implies (genvar-guardp pkg-witness prefix n avoid-lst)
           (legal-variablep (genvar pkg-witness prefix n avoid-lst)))
  :hints (("Goal" :in-theory (e/d (genvar) (legal-variablep)))))

(defthm not-member-equal-of-genvar
  (implies (genvar-guardp pkg-witness prefix n avoid-lst)
           (not (member-equal (genvar pkg-witness prefix n avoid-lst) avoid-lst)))
  :hints (("Goal" :in-theory (e/d (genvar) (legal-variablep)))))
