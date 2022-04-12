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
(include-book "dargp-less-than")

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

;; The renaming-stobj is a stobj that stores a "renaming", that is, a map from
;; some initial segment of the natural numbers (nodenums) to dargs.  Perhaps we
;; could choose some darg as the initial value, but using nil ensures that we
;; have to prove values are valid when we use them.
(defstobj renaming-stobj
  (renaming :type (array (satisfies maybe-dargp) (10000)) :resizable t :initially nil))

 ; todo: better names?
(in-theory (disable renaming-stobjp renamingi renaming-length update-renamingi resize-renaming
                    create-renaming-stobj ; reasoning about this involves a list of 10000 nils!
                    ))

;dup
;; param names match std
(defthm len-of-resize-list
  (equal (len (resize-list lst n default))
         (nfix n))
  :hints (("Goal" :in-theory (enable resize-list))))

(defthm renaming-of-resize-list
  (implies (and (renamingp lst)
                (maybe-dargp default-value))
           (renamingp (resize-list lst n default-value)))
  :hints (("Goal" :in-theory (enable resize-list renamingp))))

(defthm renaming-length-of-resize-renaming
  (equal (renaming-length (resize-renaming i renaming-stobj))
         (nfix i))
  :hints (("Goal" :in-theory (enable resize-renaming renaming-length))))

(defthm renaming-stobjp-of-resize-renaming
  (implies (renaming-stobjp renaming-stobj)
           (renaming-stobjp (resize-renaming i renaming-stobj)))
  :hints (("Goal" :in-theory (enable resize-renaming renaming-stobjp))))

(defthm renaming-length-of-update-renamingi
  (implies (and (< i (renaming-length renaming-stobj))
                (natp i))
           (equal (renaming-length (update-renamingi i darg renaming-stobj))
                  (renaming-length renaming-stobj)))
  :hints (("Goal" :in-theory (enable renaming-length update-renamingi renamingp))))

(defthm renaming-of-update-nth
  (implies (and (renamingp renaming)
                (natp i)
                (< i (len renaming))
                (maybe-dargp darg))
           (renamingp (update-nth i darg renaming)))
  :hints (("Goal" :in-theory (enable update-nth renamingp))))

(defthm renaming-stobjp-of-update-renamingi
  (implies (and (renaming-stobjp renaming-stobj)
                (< i (renaming-length renaming-stobj))
                (natp i)
                (maybe-dargp darg))
           (renaming-stobjp (update-renamingi i darg renaming-stobj)))
  :hints (("Goal" :in-theory (enable renaming-stobjp update-renamingi renamingp RENAMING-LENGTH))))

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

(defthm renamingi-of-update-renamingi
  (implies (and (natp i)
                (natp j))
           (equal (renamingi i (update-renamingi j darg renaming-stobj))
                  (if (equal i j)
                      darg
                    (renamingi i renaming-stobj))))
  :hints (("Goal" :in-theory (enable renamingi renaming-length update-renamingi renamingp))))

(defthm renaming-stobjp-of-create-renaming-stobj
  (renaming-stobjp (create-renaming-stobj))
  :hints (("Goal" :in-theory (enable renaming-stobjp create-renaming-stobj))))

(defthm maybe-dargp-of-nth-when-renamingp
  (implies (renamingp renaming)
           (maybe-dargp (nth i renaming)))
  :hints (("Goal" :in-theory (enable nth renaming-length))))

(defthm maybe-dargp-of-renamingi
  (implies (and (renaming-stobjp renaming-stobj)
                ;(natp i)
                ;(< i (renaming-length renaming-stobj))
                )
           (maybe-dargp (renamingi i renaming-stobj)))
  :hints (("Goal" :in-theory (enable renaming-stobjp renamingi renaming-length))))

;; Disabled since hung on natp.
(defthmd natp-of-renamingi
  (implies (and (renaming-stobjp renaming-stobj)
                ;(natp i)
                ;(< i (renaming-length renaming-stobj))
                )
           (equal (natp (renamingi i renaming-stobj))
                  (and (renamingi i renaming-stobj)
                       (not (consp (renamingi i renaming-stobj))))))
  :hints (("Goal" :use maybe-dargp-of-renamingi
           :in-theory (e/d (maybe-dargp) (maybe-dargp-of-renamingi)))))

;; Disabled since hung on integerp.
(defthmd integerp-of-renamingi
  (implies (renaming-stobjp renaming-stobj)
           (equal (integerp (renamingi i renaming-stobj))
                  (and (renamingi i renaming-stobj)
                       (not (consp (renamingi i renaming-stobj))))))
  :hints (("Goal" :use maybe-dargp-of-renamingi
           :in-theory (e/d (maybe-dargp)
                           (maybe-dargp-of-renamingi
                            natp-of-renamingi)))))

(defthm equal-of-car-of-renamingi-and-quote
  (implies (and (renaming-stobjp renaming-stobj)
;(natp i)
;(< i (renaming-length renaming-stobj))
                )
           (equal (equal (car (renamingi i renaming-stobj)) 'quote)
                  (consp (renamingi i renaming-stobj))))
  :hints (("Goal" :use maybe-dargp-of-renamingi
           :in-theory (e/d (maybe-dargp)
                           (maybe-dargp-of-renamingi)))))

;;;
;;; good-renaming-stobj-aux
;;;

;; Checks that all the entries from 0 through i are dargs
(defun good-renaming-stobj-aux (i renaming-stobj)
  (declare (xargs :guard (and (integerp i) ; might be -1
                              (< i (renaming-length renaming-stobj)))
                   :stobjs renaming-stobj
                   :measure (nfix (+ 1 i))))
  (if (not (natp i))
      t
    (and (dargp (renamingi i renaming-stobj))
         (good-renaming-stobj-aux (+ -1 i) renaming-stobj))))

(local
 (defthm good-renaming-stobj-aux-monotone
   (implies (and (good-renaming-stobj-aux i2 renaming-stobj) ;n is a free var
                 (<= i1 i2)
                 (integerp i1)
                 (integerp i2))
            (good-renaming-stobj-aux i1 renaming-stobj))
   :hints (("Goal" :in-theory (enable good-renaming-stobj-aux)))))

(local
 (defthm good-renaming-stobj-aux-of-update-renamingi-irrel
   (implies (and (< i j)
                 (natp i)
                 (natp j)
;              (< i (renaming-length renaming-stobj))
;               (< j (renaming-length renaming-stobj))
;                (renaming-stobjp renaming-stobj)
;                (good-renaming-stobj-aux (+ -1 i) renaming-stobj)
                 )
            (equal (good-renaming-stobj-aux i (update-renamingi j darg renaming-stobj))
                   (good-renaming-stobj-aux i renaming-stobj)))
   :hints (("Goal" :expand ((good-renaming-stobj-aux 0 renaming-stobj)
                            (good-renaming-stobj-aux 0 (update-renamingi j darg renaming-stobj)))
            :in-theory (enable good-renaming-stobj-aux)))))

(local
 (defthm renamingi-when-good-renaming-stobj-aux-iff
   (implies (and (good-renaming-stobj-aux i renaming-stobj)
                 (natp i))
            (renamingi i renaming-stobj))
   :hints (("Goal" :in-theory (enable good-renaming-stobj-aux)))))

;;;
;;; good-renaming-stobj
;;;

;; If i is negative, this makes no real claim
(defund good-renaming-stobj (i renaming-stobj)
  (declare (xargs :guard (integerp i)
                  :stobjs renaming-stobj))
  (and (< i (renaming-length renaming-stobj))
       (good-renaming-stobj-aux i renaming-stobj)))

(defthm good-renaming-stobj-of-if
  (equal (good-renaming-stobj (if test i1 i2) renaming-stobj)
         (if test
             (good-renaming-stobj i1 renaming-stobj)
           (good-renaming-stobj i2 renaming-stobj))))

(defthm good-renaming-stobj-monotone
  (implies (and (good-renaming-stobj i2 renaming-stobj) ;n is a free var
                (<= i1 i2)
                (integerp i1)
                (integerp i2))
           (good-renaming-stobj i1 renaming-stobj))
  :hints (("Goal" :in-theory (enable good-renaming-stobj))))

(defthm good-renaming-stobj-of--1
  (good-renaming-stobj -1 renaming-stobj)
  :hints (("Goal" :in-theory (enable good-renaming-stobj))))

(defthm good-renaming-stobj-after-update-renamingi
  (implies (and; (renaming-stobjp renaming-stobj)
                (good-renaming-stobj i renaming-stobj)
                (natp i)
                (< (+ 1 i) (renaming-length renaming-stobj))
                (dargp darg))
           (good-renaming-stobj (+ 1 i) (update-renamingi (+ 1 i) darg renaming-stobj)))
  :hints (("Goal" :in-theory (enable good-renaming-stobj))))

(defthm renamingi-when-good-renaming-stobj-iff
  (implies (and (good-renaming-stobj i renaming-stobj)
                (natp i))
           (renamingi i renaming-stobj))
  :hints (("Goal" :in-theory (enable good-renaming-stobj))))

;;;
;;; bounded-good-renaming-stobj-aux
;;;

;; Checks that all the entries from 0 through i are dargs less than bound
(defun bounded-good-renaming-stobj-aux (i bound renaming-stobj)
  (declare (xargs :guard (and (integerp i) ; might be -1
                              (natp bound)
                              (< i (renaming-length renaming-stobj)))
                  :stobjs renaming-stobj
                  :measure (nfix (+ 1 i))))
  (if (not (natp i))
      t
    (and (dargp-less-than (renamingi i renaming-stobj) bound)
         (bounded-good-renaming-stobj-aux (+ -1 i) bound renaming-stobj))))

(local
 (defthm bounded-good-renaming-stobj-aux-monotone
   (implies (and (bounded-good-renaming-stobj-aux i2 bound2 renaming-stobj) ;n is a free var
                 (<= i1 i2)
                 (<= bound2 bound1)
                 (integerp i1)
                 (integerp i2))
            (bounded-good-renaming-stobj-aux i1 bound1 renaming-stobj))
   :hints (("Goal" :in-theory (enable bounded-good-renaming-stobj-aux)))))

(local
 (defthm bounded-good-renaming-stobj-aux-of-update-renamingi-irrel
   (implies (and (< i j)
                 (integerp i)
                 (integerp j)
;              (< i (renaming-length renaming-stobj))
;               (< j (renaming-length renaming-stobj))
;                (renaming-stobjp renaming-stobj)
;                (bounded-good-renaming-stobj-aux (+ -1 i) renaming-stobj)
                 )
            (equal (bounded-good-renaming-stobj-aux i bound (update-renamingi j darg renaming-stobj))
                   (bounded-good-renaming-stobj-aux i bound renaming-stobj)))
   :hints (("Goal" :expand ((bounded-good-renaming-stobj-aux 0 bound renaming-stobj)
                            (bounded-good-renaming-stobj-aux 0 bound (update-renamingi j darg renaming-stobj)))
            :in-theory (enable bounded-good-renaming-stobj-aux)))))

(local
 (defthm bounded-good-renaming-stobj-aux-of-update-renamingi
   (implies (and (bounded-good-renaming-stobj-aux (+ -1 i) bound renaming-stobj)
                 (dargp-less-than darg bound)
                 (integerp i)
;              (< i (renaming-length renaming-stobj))
;               (< j (renaming-length renaming-stobj))
;                (renaming-stobjp renaming-stobj)
                 )
            (bounded-good-renaming-stobj-aux i bound (update-renamingi i darg renaming-stobj)))
   :hints (("Goal" :expand ((BOUNDED-GOOD-RENAMING-STOBJ-AUX 0 BOUND
                                                             (UPDATE-RENAMINGI 0 DARG RENAMING-STOBJ)))
            :induct (bounded-good-renaming-stobj-aux i bound renaming-stobj)
            :in-theory (enable bounded-good-renaming-stobj-aux)))))

;maybe drop?
(local
 (defthm bounded-good-renaming-stobj-aux-of-update-renamingi-gen
   (implies (and (bounded-good-renaming-stobj-aux i bound renaming-stobj)
                 (dargp-less-than darg bound)
                 (<= j i)
                 (natp j)
                 (natp i)
;              (< i (renaming-length renaming-stobj))
;               (< j (renaming-length renaming-stobj))
;                (renaming-stobjp renaming-stobj)
                 )
            (bounded-good-renaming-stobj-aux i bound (update-renamingi j darg renaming-stobj)))
   :hints (("Goal" :expand ((BOUNDED-GOOD-RENAMING-STOBJ-AUX 0 BOUND
                                                             (UPDATE-RENAMINGI 0 DARG RENAMING-STOBJ)))
            :induct (bounded-good-renaming-stobj-aux i bound renaming-stobj)
            :in-theory (enable bounded-good-renaming-stobj-aux)))))

(local
 (defthm <-of-renamingi-when-bounded-good-renaming-stobj-aux
   (implies (and (bounded-good-renaming-stobj-aux i bound renaming-stobj)
                 (not (consp (renamingi i renaming-stobj))) ; not a quotep
                 (natp i)
                 (< i (renaming-length renaming-stobj)))
            (< (renamingi i renaming-stobj) bound))
   :hints (("Goal" :in-theory (enable bounded-good-renaming-stobj-aux)))))

;;;
;;; bounded-good-renaming-stobj
;;;

;; If i is negative, this makes no real claim
(defund bounded-good-renaming-stobj (i bound renaming-stobj)
  (declare (xargs :guard (and (integerp i)
                              (natp bound))
                  :stobjs renaming-stobj))
  (and (< i (renaming-length renaming-stobj))
       (bounded-good-renaming-stobj-aux i bound renaming-stobj)))

(defthm bounded-good-renaming-stobj-forward
  (implies (bounded-good-renaming-stobj i bound renaming-stobj)
           (< i (renaming-length renaming-stobj)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-good-renaming-stobj))))

(defthm bounded-good-renaming-stobj-forward-to-good-renaming-stobj
  (implies (bounded-good-renaming-stobj i bound renaming-stobj)
           (good-renaming-stobj i renaming-stobj))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-good-renaming-stobj
                                     good-renaming-stobj))))

(defthm bounded-good-renaming-stobj-of-if
  (equal (bounded-good-renaming-stobj (if test i1 i2) bound renaming-stobj)
         (if test
             (bounded-good-renaming-stobj i1 bound renaming-stobj)
           (bounded-good-renaming-stobj i2 bound renaming-stobj))))

(defthm bounded-good-renaming-stobj-monotone
  (implies (and (bounded-good-renaming-stobj i2 bound2 renaming-stobj) ;n is a free var
                (<= i1 i2)
                (<= bound2 bound1)
                (integerp i1)
                (integerp i2))
           (bounded-good-renaming-stobj i1 bound1 renaming-stobj))
  :hints (("Goal" :in-theory (enable bounded-good-renaming-stobj))))

(defthm bounded-good-renaming-stobj-of--1
  (bounded-good-renaming-stobj -1 bound renaming-stobj)
  :hints (("Goal" :in-theory (enable bounded-good-renaming-stobj))))

(defthm bounded-good-renaming-stobj-of-update-renamingi
  (implies (and ;(renaming-stobjp renaming-stobj)
                (bounded-good-renaming-stobj (+ -1 i) bound renaming-stobj)
                (natp i)
                (< i (renaming-length renaming-stobj))
                (dargp-less-than darg bound))
           (bounded-good-renaming-stobj i bound (update-renamingi i darg renaming-stobj)))
  :hints (("Goal" :in-theory (enable bounded-good-renaming-stobj))))

(defthm bounded-good-renaming-stobj-of-update-renamingi-gen
  (implies (and (bounded-good-renaming-stobj i bound renaming-stobj)
                (dargp-less-than darg bound)
                (<= j i)
                (natp j)
                (natp i)
;              (< i (renaming-length renaming-stobj))
;               (< j (renaming-length renaming-stobj))
;                (renaming-stobjp renaming-stobj)
                )
           (bounded-good-renaming-stobj i bound (update-renamingi j darg renaming-stobj)))
  :hints (("Goal" :in-theory (enable bounded-good-renaming-stobj))))

(defthm <-of-renamingi-when-bounded-good-renaming-stobj
  (implies (and (bounded-good-renaming-stobj i bound renaming-stobj)
                (not (consp (renamingi i renaming-stobj))) ; not a quotep
                (natp i)
                (< i (renaming-length renaming-stobj)))
           (< (renamingi i renaming-stobj) bound))
  :hints (("Goal" :in-theory (enable bounded-good-renaming-stobj))))


;;;
;;; rename-darg-with-stobj
;;;

(defund-inline rename-darg-with-stobj (darg renaming-stobj)
  (declare (xargs :guard (and (dargp darg) ; in fact, it should always be in the valid region:
                              (good-renaming-stobj (if (consp darg) -1 darg) renaming-stobj))
                  :guard-hints (("Goal" :in-theory (enable renaming-stobjp
                                                           good-renaming-stobj)))
                  :stobjs renaming-stobj))
  (if (consp darg)
      darg ; quoted constant, do nothing
    ;; nodenum to fixup:
    (renamingi darg renaming-stobj)))

(defthm dargp-of-rename-darg-with-stobj
  (implies (and (dargp darg)
                (good-renaming-stobj (if (consp darg) -1 darg) renaming-stobj))
           (dargp (rename-darg-with-stobj darg renaming-stobj)))
  :hints (("Goal" :in-theory (e/d (rename-darg-with-stobj good-renaming-stobj)
                                  ()))))

(defthm dargp-less-than-of-rename-darg-with-stobj
  (implies (and (dargp darg)
                (bounded-good-renaming-stobj (if (consp darg) -1 darg) bound renaming-stobj))
           (dargp-less-than (rename-darg-with-stobj darg renaming-stobj) bound))
  :hints (("Goal" :in-theory (e/d (rename-darg-with-stobj good-renaming-stobj
                                                          BOUNDED-GOOD-RENAMING-STOBJ)
                                  ()))))

;; todo: disable some of these:

; use "not consp" as the normal form for dargs
;; Disabled since hung on integerp.
(defthmd natp-of-rename-darg-with-stobj
  (implies (and (good-renaming-stobj (if (consp darg) -1 darg) renaming-stobj)
                (dargp darg))
           (equal (natp (rename-darg-with-stobj darg renaming-stobj))
                  (not (consp (rename-darg-with-stobj darg renaming-stobj)))))
  :hints (("Goal" :in-theory (e/d (rename-darg-with-stobj GOOD-RENAMING-STOBJ) ()))))

; use "not consp" as the normal form for dargs
;; Disabled since hung on natp.
(defthmd integerp-of-rename-darg-with-stobj
  (implies (and (good-renaming-stobj (if (consp darg) -1 darg) renaming-stobj)
                (dargp darg))
           (equal (integerp (rename-darg-with-stobj darg renaming-stobj))
                  (not (consp (rename-darg-with-stobj darg renaming-stobj)))))
  :hints (("Goal" :in-theory (e/d (rename-darg-with-stobj GOOD-RENAMING-STOBJ) ()))))

(include-book "bounded-dag-exprs") ; todo: reduce

;;;
;;; rename-dargs-with-stobj
;;;

;; Renames any of the DARGS that are nodenums according to the RENAMING-STOBJ.
(defund rename-dargs-with-stobj (dargs renaming-stobj)
  (declare (xargs :guard (and (all-dargp dargs)
                              (true-listp dargs)
                              (good-renaming-stobj (largest-non-quotep dargs) renaming-stobj))
                  :stobjs renaming-stobj))
  (if (endp dargs)
      nil
    (cons (rename-darg-with-stobj (first dargs) renaming-stobj)
          (rename-dargs-with-stobj (rest dargs) renaming-stobj))))

(defthm all-dargp-of-rename-dargs-with-stobj
  (implies (and (good-renaming-stobj (largest-non-quotep dargs) renaming-stobj)
                (all-dargp dargs))
           (all-dargp (rename-dargs-with-stobj dargs renaming-stobj)))
  :hints (("Goal" :in-theory (e/d (rename-dargs-with-stobj all-dargp natp-of-rename-darg-with-stobj)
                                  ())
           :expand ((all-dargp dargs)
                    (dargp (car dargs)))
           :do-not '(generalize eliminate-destructors))))

(defthm all-dargp-less-than-of-rename-dargs-with-stobj
  (implies (and (bounded-good-renaming-stobj (largest-non-quotep dargs) bound renaming-stobj)
                (all-dargp dargs))
           (all-dargp-less-than (rename-dargs-with-stobj dargs renaming-stobj) bound))
  :hints (("Goal" :in-theory (e/d (rename-dargs-with-stobj all-dargp LARGEST-NON-QUOTEP)
                                  ())
           :expand ((all-dargp dargs)
                    (dargp (car dargs)))
           :do-not '(generalize eliminate-destructors))))
