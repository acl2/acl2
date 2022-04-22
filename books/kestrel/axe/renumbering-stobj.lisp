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

;; When rewritng a DAG, this stobj tracks the mapping from nodenums in the old
;; DAG to the new nodenums or quoteps to which they rewrote.

(include-book "all-dargp")
(include-book "dargp-less-than")
(include-book "bounded-dag-exprs") ; todo: reduce, for largest-non-quotep
(include-book "kestrel/utilities/defstobj-plus" :dir :system)
(local (include-book "kestrel/lists-light/resize-list" :dir :system))

(local (in-theory (disable dargp myquotep natp)))

;; Either a darg or nil
(defund maybe-dargp (x)
  (declare (xargs :guard t))
  (or (null x)
      (dargp x)))

(defthmd maybe-dargp-when-dargp
  (implies (dargp darg)
           (maybe-dargp darg))
  :hints (("Goal" :in-theory (enable maybe-dargp))))

;; The renumbering-stobj is a stobj that stores a "renumbering", that is, a map
;; from node numbers (up to some limit) to dargs (see dargp).  Entries beyond
;; the initial region of valid elements will be nil (since nil is not a darg,
;; this ensures that we have to prove values are valid when we use them).
(defstobj+ renumbering-stobj
  (renumbering :type (array (satisfies maybe-dargp) (10000)) :resizable t :initially nil)
  ;; :inline t ;; TODO: Try this
  :renaming ((renumberingp renumbering-entriesp)))

;; Disabled since hung on natp.
(defthmd natp-of-renumberingi
  (implies (and (renumbering-stobjp renumbering-stobj)
                ;(natp i)
                ;(< i (renumbering-length renumbering-stobj))
                )
           (equal (natp (renumberingi i renumbering-stobj))
                  (and (renumberingi i renumbering-stobj)
                       (not (consp (renumberingi i renumbering-stobj))))))
  :hints (("Goal" :use maybe-dargp-of-renumberingi
           :in-theory (e/d (maybe-dargp) (maybe-dargp-of-renumberingi)))))

;; Disabled since hung on integerp.
(defthmd integerp-of-renumberingi
  (implies (renumbering-stobjp renumbering-stobj)
           (equal (integerp (renumberingi i renumbering-stobj))
                  (and (renumberingi i renumbering-stobj)
                       (not (consp (renumberingi i renumbering-stobj))))))
  :hints (("Goal" :use maybe-dargp-of-renumberingi
           :in-theory (e/d (maybe-dargp)
                           (maybe-dargp-of-renumberingi
                            natp-of-renumberingi)))))

(defthm equal-of-car-of-renumberingi-and-quote
  (implies (and (renumbering-stobjp renumbering-stobj)
                ;;(natp i)
                ;;(< i (renumbering-length renumbering-stobj))
                )
           (equal (equal (car (renumberingi i renumbering-stobj)) 'quote)
                  (consp (renumberingi i renumbering-stobj))))
  :hints (("Goal" :use maybe-dargp-of-renumberingi
           :in-theory (e/d (maybe-dargp)
                           (maybe-dargp-of-renumberingi)))))

;;;
;;; good-renumbering-stobj-aux
;;;

;; Checks that all the entries from 0 through i are dargs
(defun good-renumbering-stobj-aux (i renumbering-stobj)
  (declare (xargs :guard (and (integerp i) ; might be -1
                              (< i (renumbering-length renumbering-stobj)))
                   :stobjs renumbering-stobj
                   :measure (nfix (+ 1 i))))
  (if (not (natp i))
      t
    (and (dargp (renumberingi i renumbering-stobj))
         (good-renumbering-stobj-aux (+ -1 i) renumbering-stobj))))

(local
 (defthm good-renumbering-stobj-aux-monotone
   (implies (and (good-renumbering-stobj-aux i2 renumbering-stobj) ;n is a free var
                 (<= i1 i2)
                 (integerp i1)
                 (integerp i2))
            (good-renumbering-stobj-aux i1 renumbering-stobj))
   :hints (("Goal" :in-theory (enable good-renumbering-stobj-aux)))))

(local
 (defthm good-renumbering-stobj-aux-of-update-renumberingi-irrel
   (implies (and (< i j)
                 (natp i)
                 (natp j)
;              (< i (renumbering-length renumbering-stobj))
;               (< j (renumbering-length renumbering-stobj))
;                (renumbering-stobjp renumbering-stobj)
;                (good-renumbering-stobj-aux (+ -1 i) renumbering-stobj)
                 )
            (equal (good-renumbering-stobj-aux i (update-renumberingi j darg renumbering-stobj))
                   (good-renumbering-stobj-aux i renumbering-stobj)))
   :hints (("Goal" :expand ((good-renumbering-stobj-aux 0 renumbering-stobj)
                            (good-renumbering-stobj-aux 0 (update-renumberingi j darg renumbering-stobj)))
            :in-theory (enable good-renumbering-stobj-aux)))))

(local
 (defthm renumberingi-when-good-renumbering-stobj-aux-iff
   (implies (and (good-renumbering-stobj-aux i renumbering-stobj)
                 (natp i))
            (renumberingi i renumbering-stobj))
   :hints (("Goal" :in-theory (enable good-renumbering-stobj-aux)))))

;;;
;;; good-renumbering-stobj
;;;

;; If i is negative, this makes no real claim
(defund good-renumbering-stobj (i renumbering-stobj)
  (declare (xargs :guard (integerp i)
                  :stobjs renumbering-stobj))
  (and (< i (renumbering-length renumbering-stobj))
       (good-renumbering-stobj-aux i renumbering-stobj)))

(defthm good-renumbering-stobj-of-if
  (equal (good-renumbering-stobj (if test i1 i2) renumbering-stobj)
         (if test
             (good-renumbering-stobj i1 renumbering-stobj)
           (good-renumbering-stobj i2 renumbering-stobj))))

(defthm good-renumbering-stobj-monotone
  (implies (and (good-renumbering-stobj i2 renumbering-stobj) ;n is a free var
                (<= i1 i2)
                (integerp i1)
                (integerp i2))
           (good-renumbering-stobj i1 renumbering-stobj))
  :hints (("Goal" :in-theory (enable good-renumbering-stobj))))

(defthm good-renumbering-stobj-of--1
  (good-renumbering-stobj -1 renumbering-stobj)
  :hints (("Goal" :in-theory (enable good-renumbering-stobj))))

(defthm good-renumbering-stobj-after-update-renumberingi
  (implies (and; (renumbering-stobjp renumbering-stobj)
                (good-renumbering-stobj i renumbering-stobj)
                (natp i)
                (< (+ 1 i) (renumbering-length renumbering-stobj))
                (dargp darg))
           (good-renumbering-stobj (+ 1 i) (update-renumberingi (+ 1 i) darg renumbering-stobj)))
  :hints (("Goal" :in-theory (enable good-renumbering-stobj))))

(defthm renumberingi-when-good-renumbering-stobj-iff
  (implies (and (good-renumbering-stobj i renumbering-stobj)
                (natp i))
           (renumberingi i renumbering-stobj))
  :hints (("Goal" :in-theory (enable good-renumbering-stobj))))

;;;
;;; bounded-good-renumbering-stobj-aux
;;;

;; Checks that all the entries from 0 through i are dargs less than bound
(defun bounded-good-renumbering-stobj-aux (i bound renumbering-stobj)
  (declare (xargs :guard (and (integerp i) ; might be -1
                              (natp bound)
                              (< i (renumbering-length renumbering-stobj)))
                  :stobjs renumbering-stobj
                  :measure (nfix (+ 1 i))))
  (if (not (natp i))
      t
    (and (dargp-less-than (renumberingi i renumbering-stobj) bound)
         (bounded-good-renumbering-stobj-aux (+ -1 i) bound renumbering-stobj))))

(local
 (defthm bounded-good-renumbering-stobj-aux-monotone
   (implies (and (bounded-good-renumbering-stobj-aux i2 bound2 renumbering-stobj) ;n is a free var
                 (<= i1 i2)
                 (<= bound2 bound1)
                 (integerp i1)
                 (integerp i2))
            (bounded-good-renumbering-stobj-aux i1 bound1 renumbering-stobj))
   :hints (("Goal" :in-theory (enable bounded-good-renumbering-stobj-aux)))))

(local
 (defthm bounded-good-renumbering-stobj-aux-of-update-renumberingi-irrel
   (implies (and (< i j)
                 (integerp i)
                 (integerp j)
;              (< i (renumbering-length renumbering-stobj))
;               (< j (renumbering-length renumbering-stobj))
;                (renumbering-stobjp renumbering-stobj)
;                (bounded-good-renumbering-stobj-aux (+ -1 i) renumbering-stobj)
                 )
            (equal (bounded-good-renumbering-stobj-aux i bound (update-renumberingi j darg renumbering-stobj))
                   (bounded-good-renumbering-stobj-aux i bound renumbering-stobj)))
   :hints (("Goal" :expand ((bounded-good-renumbering-stobj-aux 0 bound renumbering-stobj)
                            (bounded-good-renumbering-stobj-aux 0 bound (update-renumberingi j darg renumbering-stobj)))
            :in-theory (enable bounded-good-renumbering-stobj-aux)))))

(local
 (defthm bounded-good-renumbering-stobj-aux-of-update-renumberingi
   (implies (and (bounded-good-renumbering-stobj-aux (+ -1 i) bound renumbering-stobj)
                 (dargp-less-than darg bound)
                 (integerp i)
;              (< i (renumbering-length renumbering-stobj))
;               (< j (renumbering-length renumbering-stobj))
;                (renumbering-stobjp renumbering-stobj)
                 )
            (bounded-good-renumbering-stobj-aux i bound (update-renumberingi i darg renumbering-stobj)))
   :hints (("Goal" :expand ((BOUNDED-GOOD-RENUMBERING-STOBJ-AUX 0 BOUND
                                                             (UPDATE-RENUMBERINGI 0 DARG RENUMBERING-STOBJ)))
            :induct (bounded-good-renumbering-stobj-aux i bound renumbering-stobj)
            :in-theory (enable bounded-good-renumbering-stobj-aux)))))

;maybe drop?
(local
 (defthm bounded-good-renumbering-stobj-aux-of-update-renumberingi-gen
   (implies (and (bounded-good-renumbering-stobj-aux i bound renumbering-stobj)
                 (dargp-less-than darg bound)
                 (<= j i)
                 (natp j)
                 (natp i)
;              (< i (renumbering-length renumbering-stobj))
;               (< j (renumbering-length renumbering-stobj))
;                (renumbering-stobjp renumbering-stobj)
                 )
            (bounded-good-renumbering-stobj-aux i bound (update-renumberingi j darg renumbering-stobj)))
   :hints (("Goal" :expand ((BOUNDED-GOOD-RENUMBERING-STOBJ-AUX 0 BOUND
                                                             (UPDATE-RENUMBERINGI 0 DARG RENUMBERING-STOBJ)))
            :induct (bounded-good-renumbering-stobj-aux i bound renumbering-stobj)
            :in-theory (enable bounded-good-renumbering-stobj-aux
                               renumberingi-of-update-renumberingi-split)))))

(local
 (defthm <-of-renumberingi-when-bounded-good-renumbering-stobj-aux
   (implies (and (bounded-good-renumbering-stobj-aux i bound renumbering-stobj)
                 (not (consp (renumberingi i renumbering-stobj))) ; not a quotep
                 (natp i)
                 (< i (renumbering-length renumbering-stobj)))
            (< (renumberingi i renumbering-stobj) bound))
   :hints (("Goal" :in-theory (enable bounded-good-renumbering-stobj-aux)))))

;;;
;;; bounded-good-renumbering-stobj
;;;

;; If i is negative, this makes no real claim
(defund bounded-good-renumbering-stobj (i bound renumbering-stobj)
  (declare (xargs :guard (and (integerp i)
                              (natp bound))
                  :stobjs renumbering-stobj))
  (and (< i (renumbering-length renumbering-stobj))
       (bounded-good-renumbering-stobj-aux i bound renumbering-stobj)))

(defthm bounded-good-renumbering-stobj-forward
  (implies (bounded-good-renumbering-stobj i bound renumbering-stobj)
           (< i (renumbering-length renumbering-stobj)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-good-renumbering-stobj))))

(defthm bounded-good-renumbering-stobj-forward-to-good-renumbering-stobj
  (implies (bounded-good-renumbering-stobj i bound renumbering-stobj)
           (good-renumbering-stobj i renumbering-stobj))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-good-renumbering-stobj
                                     good-renumbering-stobj))))

(defthm bounded-good-renumbering-stobj-of-if
  (equal (bounded-good-renumbering-stobj (if test i1 i2) bound renumbering-stobj)
         (if test
             (bounded-good-renumbering-stobj i1 bound renumbering-stobj)
           (bounded-good-renumbering-stobj i2 bound renumbering-stobj))))

(defthm bounded-good-renumbering-stobj-monotone
  (implies (and (bounded-good-renumbering-stobj i2 bound2 renumbering-stobj) ;n is a free var
                (<= i1 i2)
                (<= bound2 bound1)
                (integerp i1)
                (integerp i2))
           (bounded-good-renumbering-stobj i1 bound1 renumbering-stobj))
  :hints (("Goal" :in-theory (enable bounded-good-renumbering-stobj))))

(defthm bounded-good-renumbering-stobj-of--1
  (bounded-good-renumbering-stobj -1 bound renumbering-stobj)
  :hints (("Goal" :in-theory (enable bounded-good-renumbering-stobj))))

(defthm bounded-good-renumbering-stobj-of-update-renumberingi
  (implies (and ;(renumbering-stobjp renumbering-stobj)
                (bounded-good-renumbering-stobj (+ -1 i) bound renumbering-stobj)
                (natp i)
                (< i (renumbering-length renumbering-stobj))
                (dargp-less-than darg bound))
           (bounded-good-renumbering-stobj i bound (update-renumberingi i darg renumbering-stobj)))
  :hints (("Goal" :in-theory (enable bounded-good-renumbering-stobj))))

(defthm bounded-good-renumbering-stobj-of-update-renumberingi-gen
  (implies (and (bounded-good-renumbering-stobj i bound renumbering-stobj)
                (dargp-less-than darg bound)
                (<= j i)
                (natp j)
                (natp i)
;              (< i (renumbering-length renumbering-stobj))
;               (< j (renumbering-length renumbering-stobj))
;                (renumbering-stobjp renumbering-stobj)
                )
           (bounded-good-renumbering-stobj i bound (update-renumberingi j darg renumbering-stobj)))
  :hints (("Goal" :in-theory (enable bounded-good-renumbering-stobj))))

(defthm <-of-renumberingi-when-bounded-good-renumbering-stobj
  (implies (and (bounded-good-renumbering-stobj i bound renumbering-stobj)
                (not (consp (renumberingi i renumbering-stobj))) ; not a quotep
                (natp i)
                (< i (renumbering-length renumbering-stobj)))
           (< (renumberingi i renumbering-stobj) bound))
  :hints (("Goal" :in-theory (enable bounded-good-renumbering-stobj))))


;;;
;;; renumber-darg-with-stobj
;;;

(defund-inline renumber-darg-with-stobj (darg renumbering-stobj)
  (declare (xargs :guard (and (dargp darg) ; in fact, it should always be in the valid region:
                              (good-renumbering-stobj (if (consp darg) -1 darg) renumbering-stobj))
                  :guard-hints (("Goal" :in-theory (enable renumbering-stobjp
                                                           good-renumbering-stobj)))
                  :stobjs renumbering-stobj))
  (if (consp darg)
      darg ; quoted constant, do nothing
    ;; nodenum to fixup:
    (renumberingi darg renumbering-stobj)))

(defthm dargp-of-renumber-darg-with-stobj
  (implies (and (dargp darg)
                (good-renumbering-stobj (if (consp darg) -1 darg) renumbering-stobj))
           (dargp (renumber-darg-with-stobj darg renumbering-stobj)))
  :hints (("Goal" :in-theory (e/d (renumber-darg-with-stobj good-renumbering-stobj)
                                  ()))))

(defthm dargp-less-than-of-renumber-darg-with-stobj
  (implies (and (dargp darg)
                (bounded-good-renumbering-stobj (if (consp darg) -1 darg) bound renumbering-stobj))
           (dargp-less-than (renumber-darg-with-stobj darg renumbering-stobj) bound))
  :hints (("Goal" :in-theory (enable renumber-darg-with-stobj
                                     good-renumbering-stobj
                                     bounded-good-renumbering-stobj))))

; use "not consp" as the normal form for dargs
;; Disabled since hung on integerp.
(defthmd natp-of-renumber-darg-with-stobj
  (implies (and (good-renumbering-stobj (if (consp darg) -1 darg) renumbering-stobj)
                (dargp darg))
           (equal (natp (renumber-darg-with-stobj darg renumbering-stobj))
                  (not (consp (renumber-darg-with-stobj darg renumbering-stobj)))))
  :hints (("Goal" :in-theory (e/d (renumber-darg-with-stobj GOOD-RENUMBERING-STOBJ) ()))))

; use "not consp" as the normal form for dargs
;; Disabled since hung on natp.
(defthmd integerp-of-renumber-darg-with-stobj
  (implies (and (good-renumbering-stobj (if (consp darg) -1 darg) renumbering-stobj)
                (dargp darg))
           (equal (integerp (renumber-darg-with-stobj darg renumbering-stobj))
                  (not (consp (renumber-darg-with-stobj darg renumbering-stobj)))))
  :hints (("Goal" :in-theory (e/d (renumber-darg-with-stobj GOOD-RENUMBERING-STOBJ) ()))))

;;;
;;; renumber-dargs-with-stobj
;;;

;; Renames any of the DARGS that are nodenums according to the RENUMBERING-STOBJ.
(defund renumber-dargs-with-stobj (dargs renumbering-stobj)
  (declare (xargs :guard (and (all-dargp dargs)
                              (true-listp dargs)
                              (good-renumbering-stobj (largest-non-quotep dargs) renumbering-stobj))
                  :stobjs renumbering-stobj))
  (if (endp dargs)
      nil
    (cons (renumber-darg-with-stobj (first dargs) renumbering-stobj)
          (renumber-dargs-with-stobj (rest dargs) renumbering-stobj))))

(defthm all-dargp-of-renumber-dargs-with-stobj
  (implies (and (good-renumbering-stobj (largest-non-quotep dargs) renumbering-stobj)
                (all-dargp dargs))
           (all-dargp (renumber-dargs-with-stobj dargs renumbering-stobj)))
  :hints (("Goal" :in-theory (enable renumber-dargs-with-stobj all-dargp natp-of-renumber-darg-with-stobj)
           :expand ((all-dargp dargs)
                    (dargp (car dargs)))
           :do-not '(generalize eliminate-destructors))))

(defthm bounded-darg-listp-of-renumber-dargs-with-stobj
  (implies (and (bounded-good-renumbering-stobj (largest-non-quotep dargs) bound renumbering-stobj)
                (all-dargp dargs))
           (bounded-darg-listp (renumber-dargs-with-stobj dargs renumbering-stobj) bound))
  :hints (("Goal" :in-theory (enable renumber-dargs-with-stobj all-dargp largest-non-quotep)
           :expand ((all-dargp dargs)
                    (dargp (car dargs)))
           :do-not '(generalize eliminate-destructors))))
