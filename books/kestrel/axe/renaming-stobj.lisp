; A stobj to track results of rewriting
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-dargp")

(local (in-theory (disable dargp)))

;; Either a darg or nil
(defund maybe-dargp (x)
  (declare (xargs :guard t))
  (or (null x)
      (dargp x)))

;; The renaming-stobj is a stobj that stores a "renaming", that is, a map from
;; some initial segment of the natural numbers (nodenums) to dargs.  Perhaps we
;; could choose some darg as the initial value, but using nil ensures that we
;; have to prove values are valid when we use them.
(defstobj renaming-stobj
  (renaming :type (array (satisfies maybe-dargp) (10000)) :resizable t :initially nil))

(in-theory (disable renaming-stobjp renamingi renaming-length update-renamingi)) ; todo: better names?

(defthm renaming-length-of-update-renamingi
  (implies (and (renaming-stobjp renaming-stobj)
                (< i (renaming-length renaming-stobj))
                (natp i)
                )
           (equal (renaming-length (update-renamingi i darg renaming-stobj))
                  (renaming-length renaming-stobj)))
  :hints (("Goal" :in-theory (enable renaming-length update-renamingi renamingp))))

(defthm renamingi-of-update-renamingi-same
  (implies (and; (renaming-stobjp renaming-stobj)
;                (< i (renaming-length renaming-stobj))
                (natp i)
                )
           (equal (renamingi i (update-renamingi i darg renaming-stobj))
                  darg))
  :hints (("Goal" :in-theory (enable renamingi renaming-length update-renamingi renamingp))))

(defthm renamingi-of-update-renamingi-diff
  (implies (and (not (equal i j))
          ;      (renaming-stobjp renaming-stobj)
        ;        (< i (renaming-length renaming-stobj))
                (natp i)
       ;         (< j (renaming-length renaming-stobj))
                (natp j)
                )
           (equal (renamingi i (update-renamingi j darg renaming-stobj))
                  (renamingi i renaming-stobj)))
  :hints (("Goal" :in-theory (enable renamingi renaming-length update-renamingi renamingp))))

;;;
;;; renaming-entries-good-through
;;;

;; That that all the entries from 0 through i are dargs, not nil.
(defun renaming-entries-good-through (i renaming-stobj)
  (declare (xargs :guard (and (integerp i)
                              (< i (renaming-length renaming-stobj)))
                  :stobjs renaming-stobj
                  :measure (nfix (+ 1 i))))
  (if (not (natp i))
      t
    (and (dargp (renamingi i renaming-stobj))
         (renaming-entries-good-through (+ -1 i) renaming-stobj))))

(defthm renaming-entries-good-through-monotone
  (implies (and (renaming-entries-good-through n renaming-stobj) ;n is a free var
                (<= m n)
                (integerp n)
                (integerp m))
           (renaming-entries-good-through m renaming-stobj))
  :hints (("Goal" :in-theory (enable renaming-entries-good-through))))

(defthm RENAMING-ENTRIES-GOOD-THROUGH-of-update-renamingi-irrel
  (implies (and (< i j)
                (natp i)
                (natp j)
  ;              (< i (renaming-length renaming-stobj))
 ;               (< j (renaming-length renaming-stobj))
;                (renaming-stobjp renaming-stobj)
;                (RENAMING-ENTRIES-GOOD-THROUGH (+ -1 I) RENAMING-STOBJ)
                )
           (equal (RENAMING-ENTRIES-GOOD-THROUGH I (UPDATE-RENAMINGI j DARG RENAMING-STOBJ))
                  (RENAMING-ENTRIES-GOOD-THROUGH I RENAMING-STOBJ)))
  :hints (("Goal" :expand ((RENAMING-ENTRIES-GOOD-THROUGH 0 RENAMING-STOBJ)
                           (RENAMING-ENTRIES-GOOD-THROUGH 0
                                                         (UPDATE-RENAMINGI J DARG RENAMING-STOBJ)))
           :in-theory (enable RENAMING-ENTRIES-GOOD-THROUGH))))

;;;
;;; good-renaming-stobj-through
;;;

;; If i is negative, this makes no real claim
(defund good-renaming-stobj-through (i renaming-stobj)
  (declare (xargs :guard (integerp i)
                  :stobjs renaming-stobj))
  (and (< i (renaming-length renaming-stobj))
       (renaming-entries-good-through i renaming-stobj)))

(defthm good-renaming-stobj-through-of-if
  (equal (good-renaming-stobj-through (if test i1 i2) renaming-stobj)
         (if test
             (good-renaming-stobj-through i1 renaming-stobj)
           (good-renaming-stobj-through i2 renaming-stobj))))

(defthm good-renaming-stobj-through-monotone
  (implies (and (good-renaming-stobj-through n renaming-stobj) ;n is a free var
                (<= m n)
                (integerp n)
                (integerp m))
           (good-renaming-stobj-through m renaming-stobj))
  :hints (("Goal" :in-theory (enable good-renaming-stobj-through))))

(defthm good-renaming-stobj-through-of--1
  (good-renaming-stobj-through -1 renaming-stobj)
  :hints (("Goal" :in-theory (enable good-renaming-stobj-through))))

;;;
;;; rename-darg-with-stobj
;;;

(defund-inline rename-darg-with-stobj (darg renaming-stobj)
  (declare (xargs :guard (and (dargp darg)
                              (good-renaming-stobj-through (if (consp darg) -1 darg) renaming-stobj))
                  :guard-hints (("Goal" :in-theory (enable renaming-stobjp
                                                           GOOD-RENAMING-STOBJ-THROUGH)))
                  :stobjs renaming-stobj))
  (if (consp darg)
      darg ; quoted constant, do nothing
    ;; nodenum to fixup:
    (renamingi darg renaming-stobj)))

(defthm dargp-of-rename-darg-with-stobj
  (implies (and (dargp darg)
                (good-renaming-stobj-through (if (consp darg) -1 darg) renaming-stobj))
           (dargp (rename-darg-with-stobj darg renaming-stobj)))
  :hints (("Goal" :in-theory (e/d (rename-darg-with-stobj GOOD-RENAMING-STOBJ-THROUGH)
                                  (dargp natp)))))

; use "not consp" as the normal form for dargs
(defthm natp-of-rename-darg-with-stobj
  (implies (and (dargp darg)
                (good-renaming-stobj-through (if (consp darg) -1 darg) renaming-stobj))
           (equal (natp (rename-darg-with-stobj darg renaming-stobj))
                  (not (consp (rename-darg-with-stobj darg renaming-stobj)))))
  :hints (("Goal" :in-theory (e/d (rename-darg-with-stobj GOOD-RENAMING-STOBJ-THROUGH) (dargp natp)))))

; use "not consp" as the normal form for dargs
(defthm integerp-of-rename-darg-with-stobj
  (implies (and (dargp darg)
                (good-renaming-stobj-through (if (consp darg) -1 darg) renaming-stobj))
           (equal (integerp (rename-darg-with-stobj darg renaming-stobj))
                  (not (consp (rename-darg-with-stobj darg renaming-stobj)))))
  :hints (("Goal" :in-theory (e/d (rename-darg-with-stobj GOOD-RENAMING-STOBJ-THROUGH) (dargp natp)))))

(include-book "bounded-dag-exprs") ; todo: reduce

;;;
;;; rename-dargs-with-stobj
;;;

;; Renames any of the DARGS that are nodenums according to the RENAMING-STOBJ.
(defund rename-dargs-with-stobj (dargs renaming-stobj)
  (declare (xargs :guard (and (all-dargp dargs)
                              (true-listp dargs)
                              (good-renaming-stobj-through (largest-non-quotep dargs) renaming-stobj))
                  :stobjs renaming-stobj))
  (if (endp dargs)
      nil
    (cons (rename-darg-with-stobj (first dargs) renaming-stobj)
          (rename-dargs-with-stobj (rest dargs) renaming-stobj))))

(defthm all-dargp-of-rename-dargs-with-stobj
  (implies (and (good-renaming-stobj-through (largest-non-quotep dargs) renaming-stobj)
                (all-dargp dargs))
           (all-dargp (rename-dargs-with-stobj dargs renaming-stobj)))
  :hints (("Goal" :in-theory (e/d (rename-dargs-with-stobj all-dargp) (myquotep))
           :expand ((all-dargp dargs)
                    (dargp (car dargs)))
           :do-not '(generalize eliminate-destructors))))

;; TODO: Add notion of bounded renaming

(defthm good-renaming-stobj-through-after-update-renamingi
  (implies (and (renaming-stobjp renaming-stobj)
                (good-renaming-stobj-through i renaming-stobj)
                (natp i)
                (< (+ 1 i) (RENAMING-LENGTH RENAMING-STOBJ))
                (dargp darg))
           (good-renaming-stobj-through (+ 1 i) (update-renamingi (+ 1 i) darg renaming-stobj)))
  :hints (("Goal" :in-theory (enable good-renaming-stobj-through))))
