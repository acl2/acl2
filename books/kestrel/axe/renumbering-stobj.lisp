; A stobj to track results of rewriting
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; When rewriting a DAG, this stobj tracks the mapping from nodenums in the old
;; DAG to the new nodenums or quoteps to which they rewrote.

(include-book "darg-listp")
(include-book "dargp-less-than")
(include-book "largest-non-quotep")
(include-book "bounded-darg-listp")
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

; Matt K. mod 6/25/2024:
; The following seemed necessary for a run based on Allegro CL.
(set-compile-fns t)

;; The renumbering-stobj is a stobj that stores a "renumbering", that is, a map
;; from node numbers (up to some limit) to dargs (see dargp).  Entries beyond
;; the initial region of valid elements will be nil (since nil is not a darg,
;; this ensures that we have to prove values are valid when we use them).
(defstobj+ renumbering-stobj
  (renumbering :type (array (satisfies maybe-dargp) (10000)) :resizable t :initially nil)
  ;; :inline t ;; TODO: Try this
  :renaming ((renumberingp renumbering-entriesp))
  :inline t)

;better guard than UPDATE-RENUMBERINGi (requires dargp, not maybe-dargp) -- use this one instead
(defund-inline update-renumbering (i darg renumbering-stobj)
  (declare (xargs :guard (and (natp i)
                              (< i (renumbering-length renumbering-stobj))
                              (dargp darg))
                  :stobjs renumbering-stobj))
  (update-renumberingi i darg renumbering-stobj))

(defthm renumbering-length-of-update-renumbering
  (implies (and (< i (renumbering-length renumbering-stobj))
                (natp i))
           (equal (renumbering-length (update-renumbering i darg renumbering-stobj))
                  (renumbering-length renumbering-stobj)))
  :hints (("Goal" :in-theory (enable update-renumbering))))

(defthm renumbering-stobjp-of-update-renumbering
  (implies (and (renumbering-stobjp renumbering-stobj)
                (< i (renumbering-length renumbering-stobj))
                (natp i)
                (dargp darg))
           (renumbering-stobjp (update-renumbering i darg renumbering-stobj)))
  :hints (("Goal":in-theory (enable update-renumbering))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;; We use consp as the normal form for dargs.
(defthm myquotep-of-renumberingi
  (implies (and (renumbering-stobjp renumbering-stobj)
                ;;(natp i)
                ;;(< i (renumbering-length renumbering-stobj))
                )
           (equal (myquotep (renumberingi i renumbering-stobj))
                  (consp (renumberingi i renumbering-stobj))))
  :hints (("Goal" :use maybe-dargp-of-renumberingi
           :in-theory (e/d (maybe-dargp dargp)
                           (maybe-dargp-of-renumberingi)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Checks that all the entries from 0 through I are dargs.
(defun good-renumbering-stobjp-aux (i renumbering-stobj)
  (declare (xargs :guard (and (integerp i) ; might be -1
                              (< i (renumbering-length renumbering-stobj)))
                   :stobjs renumbering-stobj
                   :measure (nfix (+ 1 i))))
  (if (not (natp i))
      t
    (and (dargp (renumberingi i renumbering-stobj))
         (good-renumbering-stobjp-aux (+ -1 i) renumbering-stobj))))

(local
 (defthm good-renumbering-stobjp-aux-monotone
   (implies (and (good-renumbering-stobjp-aux i2 renumbering-stobj) ;n is a free var
                 (<= i1 i2)
                 (integerp i1)
                 (integerp i2))
            (good-renumbering-stobjp-aux i1 renumbering-stobj))
   :hints (("Goal" :in-theory (enable good-renumbering-stobjp-aux)))))

(local
 (defthm good-renumbering-stobjp-aux-of-update-renumberingi-irrel
   (implies (and (< i j)
                 (natp i)
                 (natp j)
;              (< i (renumbering-length renumbering-stobj))
;               (< j (renumbering-length renumbering-stobj))
;                (renumbering-stobjp renumbering-stobj)
;                (good-renumbering-stobjp-aux (+ -1 i) renumbering-stobj)
                 )
            (equal (good-renumbering-stobjp-aux i (update-renumberingi j darg renumbering-stobj))
                   (good-renumbering-stobjp-aux i renumbering-stobj)))
   :hints (("Goal" :expand ((good-renumbering-stobjp-aux 0 renumbering-stobj)
                            (good-renumbering-stobjp-aux 0 (update-renumberingi j darg renumbering-stobj)))
            :in-theory (enable good-renumbering-stobjp-aux)))))

(local
 (defthm renumberingi-when-good-renumbering-stobjp-aux-iff
   (implies (and (good-renumbering-stobjp-aux i renumbering-stobj)
                 (natp i))
            (renumberingi i renumbering-stobj))
   :hints (("Goal" :in-theory (enable good-renumbering-stobjp-aux)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; If i is negative, this makes no real claim
(defund good-renumbering-stobjp (i renumbering-stobj)
  (declare (xargs :guard (integerp i)
                  :stobjs renumbering-stobj))
  (and (< i (renumbering-length renumbering-stobj))
       (good-renumbering-stobjp-aux i renumbering-stobj)))

(defthm good-renumbering-stobjp-of-if
  (equal (good-renumbering-stobjp (if test i1 i2) renumbering-stobj)
         (if test
             (good-renumbering-stobjp i1 renumbering-stobj)
           (good-renumbering-stobjp i2 renumbering-stobj))))

(defthm good-renumbering-stobjp-monotone
  (implies (and (good-renumbering-stobjp i2 renumbering-stobj) ;n is a free var
                (<= i1 i2)
                (integerp i1)
                (integerp i2))
           (good-renumbering-stobjp i1 renumbering-stobj))
  :hints (("Goal" :in-theory (enable good-renumbering-stobjp))))

(defthm good-renumbering-stobjp-of--1
  (good-renumbering-stobjp -1 renumbering-stobj)
  :hints (("Goal" :in-theory (enable good-renumbering-stobjp))))

(local
  (defthm good-renumbering-stobjp-of-update-renumberingi
    (implies (and ; (renumbering-stobjp renumbering-stobj)
               (good-renumbering-stobjp i renumbering-stobj)
               (natp i)
               (< (+ 1 i) (renumbering-length renumbering-stobj))
               (dargp darg))
             (good-renumbering-stobjp (+ 1 i) (update-renumberingi (+ 1 i) darg renumbering-stobj)))
    :hints (("Goal" :in-theory (enable good-renumbering-stobjp)))))

(defthm good-renumbering-stobjp-of-update-renumbering
  (implies (and; (renumbering-stobjp renumbering-stobj)
                (good-renumbering-stobjp i renumbering-stobj)
                (natp i)
                (< (+ 1 i) (renumbering-length renumbering-stobj))
                (dargp darg))
           (good-renumbering-stobjp (+ 1 i) (update-renumbering (+ 1 i) darg renumbering-stobj)))
  :hints (("Goal" :in-theory (enable update-renumbering))))

(defthm renumberingi-when-good-renumbering-stobjp-iff
  (implies (and (good-renumbering-stobjp i renumbering-stobj)
                (natp i))
           (renumberingi i renumbering-stobj))
  :hints (("Goal" :in-theory (enable good-renumbering-stobjp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Checks that all the entries from 0 through I are dargs less than BOUND
(defun bounded-good-renumbering-stobjp-aux (i bound renumbering-stobj)
  (declare (xargs :guard (and (integerp i) ; might be -1
                              (natp bound)
                              (< i (renumbering-length renumbering-stobj)))
                  :stobjs renumbering-stobj
                  :measure (nfix (+ 1 i))))
  (if (not (natp i))
      t
    (and (dargp-less-than (renumberingi i renumbering-stobj) bound)
         (bounded-good-renumbering-stobjp-aux (+ -1 i) bound renumbering-stobj))))

(local
 (defthm bounded-good-renumbering-stobjp-aux-monotone
   (implies (and (bounded-good-renumbering-stobjp-aux i2 bound2 renumbering-stobj) ;n is a free var
                 (<= i1 i2)
                 (<= bound2 bound1)
                 (integerp i1)
                 (integerp i2))
            (bounded-good-renumbering-stobjp-aux i1 bound1 renumbering-stobj))
   :hints (("Goal" :in-theory (enable bounded-good-renumbering-stobjp-aux)))))

(local
 (defthm bounded-good-renumbering-stobjp-aux-of-update-renumberingi-irrel
   (implies (and (< i j)
                 (integerp i)
                 (integerp j)
;              (< i (renumbering-length renumbering-stobj))
;               (< j (renumbering-length renumbering-stobj))
;                (renumbering-stobjp renumbering-stobj)
;                (bounded-good-renumbering-stobjp-aux (+ -1 i) renumbering-stobj)
                 )
            (equal (bounded-good-renumbering-stobjp-aux i bound (update-renumberingi j darg renumbering-stobj))
                   (bounded-good-renumbering-stobjp-aux i bound renumbering-stobj)))
   :hints (("Goal" :expand ((bounded-good-renumbering-stobjp-aux 0 bound renumbering-stobj)
                            (bounded-good-renumbering-stobjp-aux 0 bound (update-renumberingi j darg renumbering-stobj)))
            :in-theory (enable bounded-good-renumbering-stobjp-aux)))))

(local
 (defthm bounded-good-renumbering-stobjp-aux-of-update-renumberingi
   (implies (and (bounded-good-renumbering-stobjp-aux (+ -1 i) bound renumbering-stobj)
                 (dargp-less-than darg bound)
                 (integerp i)
;              (< i (renumbering-length renumbering-stobj))
;               (< j (renumbering-length renumbering-stobj))
;                (renumbering-stobjp renumbering-stobj)
                 )
            (bounded-good-renumbering-stobjp-aux i bound (update-renumberingi i darg renumbering-stobj)))
   :hints (("Goal" :expand ((BOUNDED-GOOD-RENUMBERING-STOBJP-AUX 0 BOUND
                                                             (UPDATE-RENUMBERINGI 0 DARG RENUMBERING-STOBJ)))
            :induct (bounded-good-renumbering-stobjp-aux i bound renumbering-stobj)
            :in-theory (enable bounded-good-renumbering-stobjp-aux)))))

;maybe drop?
(local
 (defthm bounded-good-renumbering-stobjp-aux-of-update-renumberingi-gen
   (implies (and (bounded-good-renumbering-stobjp-aux i bound renumbering-stobj)
                 (dargp-less-than darg bound)
                 (<= j i)
                 (natp j)
                 (natp i)
;              (< i (renumbering-length renumbering-stobj))
;               (< j (renumbering-length renumbering-stobj))
;                (renumbering-stobjp renumbering-stobj)
                 )
            (bounded-good-renumbering-stobjp-aux i bound (update-renumberingi j darg renumbering-stobj)))
   :hints (("Goal" :expand ((BOUNDED-GOOD-RENUMBERING-STOBJP-AUX 0 BOUND
                                                             (UPDATE-RENUMBERINGI 0 DARG RENUMBERING-STOBJ)))
            :induct (bounded-good-renumbering-stobjp-aux i bound renumbering-stobj)
            :in-theory (enable bounded-good-renumbering-stobjp-aux
                               renumberingi-of-update-renumberingi-split)))))

(local
 (defthm <-of-renumberingi-when-bounded-good-renumbering-stobjp-aux
   (implies (and (bounded-good-renumbering-stobjp-aux i bound renumbering-stobj)
                 (not (consp (renumberingi i renumbering-stobj))) ; not a quotep
                 (natp i)
                 (< i (renumbering-length renumbering-stobj)))
            (< (renumberingi i renumbering-stobj) bound))
   :hints (("Goal" :in-theory (enable bounded-good-renumbering-stobjp-aux)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Checks that all the entries from 0 through I are dargs less than BOUND.
;; If i is negative, this makes no real claim
(defund bounded-good-renumbering-stobjp (i bound renumbering-stobj)
  (declare (xargs :guard (and (integerp i)
                              (natp bound))
                  :stobjs renumbering-stobj))
  (and (< i (renumbering-length renumbering-stobj))
       (bounded-good-renumbering-stobjp-aux i bound renumbering-stobj)))

(defthm bounded-good-renumbering-stobjp-forward
  (implies (bounded-good-renumbering-stobjp i bound renumbering-stobj)
           (< i (renumbering-length renumbering-stobj)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-good-renumbering-stobjp))))

(defthm bounded-good-renumbering-stobjp-forward-to-good-renumbering-stobjp
  (implies (bounded-good-renumbering-stobjp i bound renumbering-stobj)
           (good-renumbering-stobjp i renumbering-stobj))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-good-renumbering-stobjp
                                     good-renumbering-stobjp))))

(defthm bounded-good-renumbering-stobjp-of-if
  (equal (bounded-good-renumbering-stobjp (if test i1 i2) bound renumbering-stobj)
         (if test
             (bounded-good-renumbering-stobjp i1 bound renumbering-stobj)
           (bounded-good-renumbering-stobjp i2 bound renumbering-stobj))))

(defthm bounded-good-renumbering-stobjp-monotone
  (implies (and (bounded-good-renumbering-stobjp i2 bound2 renumbering-stobj) ;n is a free var
                (<= i1 i2)
                (<= bound2 bound1)
                (integerp i1)
                (integerp i2))
           (bounded-good-renumbering-stobjp i1 bound1 renumbering-stobj))
  :hints (("Goal" :in-theory (enable bounded-good-renumbering-stobjp))))

(defthm bounded-good-renumbering-stobjp-of--1
  (bounded-good-renumbering-stobjp -1 bound renumbering-stobj)
  :hints (("Goal" :in-theory (enable bounded-good-renumbering-stobjp))))

(local
  (defthm bounded-good-renumbering-stobjp-of-update-renumberingi
    (implies (and ;(renumbering-stobjp renumbering-stobj)
               (bounded-good-renumbering-stobjp (+ -1 i) bound renumbering-stobj)
               (natp i)
               (< i (renumbering-length renumbering-stobj)))
             (equal (bounded-good-renumbering-stobjp i bound (update-renumberingi i darg renumbering-stobj))
                    (dargp-less-than darg bound)))
    :hints (("Goal" :in-theory (enable bounded-good-renumbering-stobjp)))))

(defthm bounded-good-renumbering-stobjp-of-update-renumbering
  (implies (and ;(renumbering-stobjp renumbering-stobj)
                (bounded-good-renumbering-stobjp (+ -1 i) bound renumbering-stobj)
                (natp i)
                (< i (renumbering-length renumbering-stobj)))
           (equal (bounded-good-renumbering-stobjp i bound (update-renumbering i darg renumbering-stobj))
                  (dargp-less-than darg bound)))
  :hints (("Goal" :in-theory (enable update-renumbering))))

(local
  (defthm bounded-good-renumbering-stobjp-of-update-renumberingi-gen
    (implies (and (bounded-good-renumbering-stobjp i bound renumbering-stobj)
                  (dargp-less-than darg bound)
                  (<= j i)
                  (natp j)
                  (natp i)
;              (< i (renumbering-length renumbering-stobj))
;               (< j (renumbering-length renumbering-stobj))
;                (renumbering-stobjp renumbering-stobj)
                  )
             (bounded-good-renumbering-stobjp i bound (update-renumberingi j darg renumbering-stobj)))
    :hints (("Goal" :in-theory (enable bounded-good-renumbering-stobjp)))))

(defthm bounded-good-renumbering-stobjp-of-update-renumbering-gen
  (implies (and (bounded-good-renumbering-stobjp i bound renumbering-stobj)
                (dargp-less-than darg bound)
                (<= j i)
                (natp j)
                (natp i)
;              (< i (renumbering-length renumbering-stobj))
;               (< j (renumbering-length renumbering-stobj))
;                (renumbering-stobjp renumbering-stobj)
                )
           (bounded-good-renumbering-stobjp i bound (update-renumbering j darg renumbering-stobj)))
  :hints (("Goal" :in-theory (enable update-renumbering))))

(defthm <-of-renumberingi-when-bounded-good-renumbering-stobjp
  (implies (and (bounded-good-renumbering-stobjp i bound renumbering-stobj)
                (not (consp (renumberingi i renumbering-stobj))) ; not a quotep
                (natp i)
                (< i (renumbering-length renumbering-stobj)))
           (< (renumberingi i renumbering-stobj) bound))
  :hints (("Goal" :in-theory (enable bounded-good-renumbering-stobjp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Renames DARG, if it is a nodenum, according to the RENUMBERING-STOBJ.
(defund-inline renumber-darg-with-stobj (darg renumbering-stobj)
  (declare (xargs :guard (and (dargp darg) ; in fact, it should always be in the valid region:
                              (good-renumbering-stobjp (if (consp darg) -1 darg) renumbering-stobj))
                  :guard-hints (("Goal" :in-theory (enable renumbering-stobjp
                                                           good-renumbering-stobjp)))
                  :stobjs renumbering-stobj))
  (if (consp darg)
      darg ; quoted constant, do nothing
    ;; nodenum to fixup:
    (renumberingi darg renumbering-stobj)))

(defthm dargp-of-renumber-darg-with-stobj
  (implies (and (dargp darg)
                (good-renumbering-stobjp (if (consp darg) -1 darg) renumbering-stobj))
           (dargp (renumber-darg-with-stobj darg renumbering-stobj)))
  :hints (("Goal" :in-theory (enable renumber-darg-with-stobj good-renumbering-stobjp))))

(defthm dargp-less-than-of-renumber-darg-with-stobj
  (implies (and (dargp darg)
                (bounded-good-renumbering-stobjp (if (consp darg) -1 darg) bound renumbering-stobj))
           (dargp-less-than (renumber-darg-with-stobj darg renumbering-stobj) bound))
  :hints (("Goal" :in-theory (enable renumber-darg-with-stobj
                                     good-renumbering-stobjp
                                     bounded-good-renumbering-stobjp))))

;; Disabled since hung on <
(defthmd <-of-renumber-darg-with-stobj
  (implies (and (dargp darg)
                (bounded-good-renumbering-stobjp (if (consp darg) -1 darg) bound renumbering-stobj)
                (not (consp (renumber-darg-with-stobj darg renumbering-stobj))) ; it's a nodenum
                )
           (< (renumber-darg-with-stobj darg renumbering-stobj) bound))
  :hints (("Goal" :in-theory (enable renumber-darg-with-stobj
                                     good-renumbering-stobjp
                                     bounded-good-renumbering-stobjp))))

; use "not consp" as the normal form for dargs
;; Disabled since hung on natp.
(defthmd natp-of-renumber-darg-with-stobj
  (implies (and (good-renumbering-stobjp (if (consp darg) -1 darg) renumbering-stobj)
                (dargp darg))
           (equal (natp (renumber-darg-with-stobj darg renumbering-stobj))
                  (not (consp (renumber-darg-with-stobj darg renumbering-stobj)))))
  :hints (("Goal" :in-theory (enable renumber-darg-with-stobj good-renumbering-stobjp))))

; use "not consp" as the normal form for dargs
;; Disabled since hung on integerp.
(defthmd integerp-of-renumber-darg-with-stobj
  (implies (and (good-renumbering-stobjp (if (consp darg) -1 darg) renumbering-stobj)
                (dargp darg))
           (equal (integerp (renumber-darg-with-stobj darg renumbering-stobj))
                  (not (consp (renumber-darg-with-stobj darg renumbering-stobj)))))
  :hints (("Goal" :in-theory (enable renumber-darg-with-stobj good-renumbering-stobjp))))

;; Use consp as the normal form
;; Disabled since hung on true-listp
(defthmd true-listp-of-renumber-darg-with-stobj
  (implies (and (good-renumbering-stobjp (if (consp darg) -1 darg) renumbering-stobj)
                (dargp darg))
           (equal (true-listp (renumber-darg-with-stobj darg renumbering-stobj))
                  (consp (renumber-darg-with-stobj darg renumbering-stobj))))
  :hints (("Goal" :in-theory (enable renumber-darg-with-stobj good-renumbering-stobjp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Renames any of the DARGS that are nodenums according to the RENUMBERING-STOBJ.
(defund renumber-dargs-with-stobj (dargs renumbering-stobj)
  (declare (xargs :guard (and (darg-listp dargs)
                              (good-renumbering-stobjp (largest-non-quotep dargs) renumbering-stobj))
                  :stobjs renumbering-stobj))
  (if (endp dargs)
      nil
    (cons (renumber-darg-with-stobj (first dargs) renumbering-stobj)
          (renumber-dargs-with-stobj (rest dargs) renumbering-stobj))))

(defthm darg-listp-of-renumber-dargs-with-stobj
  (implies (and (good-renumbering-stobjp (largest-non-quotep dargs) renumbering-stobj)
                (darg-listp dargs))
           (darg-listp (renumber-dargs-with-stobj dargs renumbering-stobj)))
  :hints (("Goal" :in-theory (enable renumber-dargs-with-stobj darg-listp natp-of-renumber-darg-with-stobj)
           :expand ((darg-listp dargs)
                    (dargp (car dargs)))
           :do-not '(generalize eliminate-destructors))))

(defthm bounded-darg-listp-of-renumber-dargs-with-stobj
  (implies (and (bounded-good-renumbering-stobjp (largest-non-quotep dargs) bound renumbering-stobj)
                (darg-listp dargs))
           (bounded-darg-listp (renumber-dargs-with-stobj dargs renumbering-stobj) bound))
  :hints (("Goal" :in-theory (enable renumber-dargs-with-stobj darg-listp largest-non-quotep)
           :expand ((darg-listp dargs)
                    (dargp (car dargs)))
           :do-not '(generalize eliminate-destructors))))
