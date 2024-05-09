
; sra-vw-flat-sim.lsp                                  Vivek & Warren

; Copyright (C) 2020-2022, ForrestHunt, Inc.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; See file ``README'' for additional information.

; The forms in this file are defined in raw lisp and not guard
; verified.  We hope to guard verify these forms when the dz-solver is
; written in ACL2 and guard-verified.

(in-package "ACL2")

(include-book "sra-vw-flat-sim-help")
(include-book "dz-unc/fake-dz-unc" :skip-proofs-okp t)
(include-book "read-float")

;; Some extra theorems we need when fake-dz-unc is guard-verified.
(skip-proofs
 (defthm all-dz-lengths-dz-unc-decomp
   (let* ((dim (dim dz)) (dim*dim (* dim dim)))
     (implies (and (equal (dim*dim dz) dim*dim)
                   (equal (a-length dz) dim*dim)
                   (equal (z-length dz) dim*dim)
                   (equal (b-length dz) dim)
                   (equal (x-length dz) dim)
                   (equal (nx-row-length dz) dim)
                   (equal (nx-blk-length dz) dim))
              (and (equal (a-length (mv-nth 1 (dz-unc-decomp dz)))
                          (a-length dz))
                   (equal (z-length (mv-nth 1 (dz-unc-decomp dz)))
                          (z-length dz))
                   (equal (b-length (mv-nth 1 (dz-unc-decomp dz)))
                          (b-length dz))
                   (equal (x-length (mv-nth 1 (dz-unc-decomp dz)))
                          (x-length dz))
                   (equal (nx-row-length (mv-nth 1 (dz-unc-decomp dz)))
                          (nx-row-length dz))
                   (equal (nx-blk-length (mv-nth 1 (dz-unc-decomp dz)))
                          (nx-blk-length dz))
                   (equal (dim (mv-nth 1 (dz-unc-decomp dz)))
                          (dim dz))
                   (equal (dim*dim (mv-nth 1 (dz-unc-decomp dz)))
                          (dim*dim dz)))))
   :hints
   (("Goal" :in-theory (enable nth-theory-lemmas)))))

(skip-proofs
 (defthm all-dz-lengths-dz-unc-solve
   (and (equal (a-length (dz-unc-solve dz))
               (a-length dz))
        (equal (z-length (dz-unc-solve dz))
               (z-length dz))
        (equal (b-length (dz-unc-solve dz))
               (b-length dz))
        (equal (x-length (dz-unc-solve dz))
               (x-length dz))
        (equal (nx-row-length (dz-unc-solve dz))
               (nx-row-length dz))
        (equal (nx-blk-length (dz-unc-solve dz))
               (nx-blk-length dz))
        (equal (dim (dz-unc-solve dz))
               (dim dz))
        (equal (dim*dim (dz-unc-solve dz))
               (dim*dim dz)))
   :hints
   (("Goal" :in-theory (enable nth-theory-lemmas)))))

(skip-proofs
 (defthm dzp-dz-unc-solve
   (dzp (dz-unc-solve dz))))

(defthm nth-xp
  (implies (and (xp l)
                (natp i)
                (< i (len l)))
           (rationalp (nth i l)))
  :hints
  (("Goal" :in-theory (enable nth-theory-defuns))))

(defthm rationalp-xi
  (implies (and (dzp dz)
                (natp i)
                (< i (x-length dz)))
           (rationalp (xi i dz))))

(defthm x-length-update-xi
  (implies (and (natp i)
                (< i (x-length dz)))
           (equal (x-length (update-xi i v dz))
                  (x-length dz)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm b-length-update-bi
  (implies (and (natp i)
                (< i (b-length dz)))
           (equal (b-length (update-bi i v dz))
                  (b-length dz)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm a-length-update-ai
  (implies (and (natp i)
                (< i (a-length dz)))
           (equal (a-length (update-ai i v dz))
                  (a-length dz)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(defthm clear-dz-a-other-dz-props-unchanged
  (and (equal (z-length (clear-dz-a i n dz))
              (z-length dz))
       (equal (b-length (clear-dz-a i n dz))
              (b-length dz))
       (equal (x-length (clear-dz-a i n dz))
              (x-length dz))
       (equal (nx-row-length (clear-dz-a i n dz))
              (nx-row-length dz))
       (equal (nx-blk-length (clear-dz-a i n dz))
              (nx-blk-length dz))
       (equal (dim (clear-dz-a i n dz))
              (dim dz))
       (equal (dim*dim (clear-dz-a i n dz))
              (dim*dim dz)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas))))

(in-theory (disable dzp
                    xi x-length update-xi
                    bi b-length update-bi
                    ai a-length update-ai
                    z-length
                    nx-row-length
                    nx-blk-length
                    dim
                    dim*dim))



(in-theory (disable dz-unc-decomp dz-unc-solve))

(defthm a-length-clear-dz-a
  (implies (and (natp i)
                (= n (a-length dz)))
           (equal (a-length (clear-dz-a i n dz))
                  (a-length dz)))
  :hints
  (("Goal" :in-theory (enable a-length nth-theory-lemmas
                              update-ai))))


(defun update-rec-x-names (dz-i x-names-offset len-x cycle nvars rec dz)
; This function updates rec with x-names at the given positive cycle.
  ;; We expect rec-i to be initialized with the index of the first
  ;; x-name entry in the record (rec).
  "Update time-value records; expected usage with ~
   (no-duplicatesp names)."
  (declare (type (unsigned-byte 60) dz-i x-names-offset len-x cycle nvars)
           (xargs :measure (nfix (- len-x dz-i))
                  :guard (and (= len-x (x-length dz))
                              (<= dz-i len-x)
                              (<= len-x nvars)
                              (<= (+ x-names-offset len-x)
                                  nvars)
                              (<= (* (1+ cycle) nvars)
                                  (arl rec))
                              (< 0 cycle)
                              (<= (arl rec) *2^60*))
                  :guard-hints (("Goal" :in-theory (enable ar-theory-lemmas)))
                  :stobjs (rec dz)))
  (if (zp (- len-x dz-i))
      rec
    (b* ((dz-value (xi dz-i dz))
         (rec-i (+ dz-i x-names-offset))
         (rec (!ari rec-i cycle nvars dz-value rec)))
      (update-rec-x-names (u60 (1+ dz-i))
                          x-names-offset len-x cycle nvars rec dz))))

(defun b-sym-fold-to-stv-good-map (i n max Abr)
  (declare (xargs :measure (nfix (- n i))
                  :guard (and (natp i)
                              (natp n)
                              (natp max)
                              (= n (b-sym-fold-to-stv-length Abr))
                              (<= i n))
                  :stobjs Abr))
  (if (zp (- n i))
      t
    (let ((stv-index (b-sym-fold-to-stvi i Abr)))
      (and (< stv-index max)
           (b-sym-fold-to-stv-good-map (1+ i) n max Abr)))))

(defun load-b-sym-fold-into-dz (i n Abr st-vals dz)
  (declare (xargs :measure (nfix (- n i))
                  :guard (and (natp i)
                              (natp n)
                              (= n (b-sym-fold-to-stv-length Abr))
                              (= n (b-length dz))
                              (<= i n)
                              (b-sym-fold-to-stv-good-map i n (stvl st-vals) Abr))
                  :guard-hints (("Goal" :in-theory (enable stv-theory-lemmas)))
                  :stobjs (Abr st-vals dz)))
  (if (mbe :logic (zp (- n i)) :exec (>= i n))
      dz
    (let* ((stv-i (b-sym-fold-to-stvi i Abr))
           (val (stvi stv-i st-vals))
           (dz (update-bi i val dz)))
      (load-b-sym-fold-into-dz (1+ i) n Abr st-vals dz))))

(defthm bp-update-bi
  (implies (and (bp b)
                (<= i (len b))
                (rationalp v))
           (bp (!nth i v b)))
  :hints
  (("Goal" :in-theory (enable nth-theory-defuns))))

(defthm dzp-update-bi
  (implies (and (force (dzp dz))
                (force (<= i (b-length dz)))
                (force (rationalp v)))
           (dzp (update-bi i v dz)))
  :hints
  (("Goal" :in-theory (enable nth-theory-lemmas b-length update-bi dzp))))

(defthm dzp-load-b-sym-fold-into-dz
  (implies (and (dzp dz)
                (Abrp Abr)
                (st-valsp st-vals)
                (natp i)
                (= n (b-sym-fold-to-stv-length Abr))
                (= n (b-length dz))
                (b-sym-fold-to-stv-good-map i n (stvl st-vals) Abr))
           (dzp (load-b-sym-fold-into-dz i n Abr st-vals dz)))
  :hints
  (("Goal" :induct (load-b-sym-fold-into-dz i n Abr st-vals dz)
    :in-theory (enable stv-theory-lemmas))))

(defthm load-b-sym-into-dz-dz-props
  (and (equal (z-length (load-b-sym-fold-into-dz i n Abr st-vals dz))
              (z-length dz))
       (equal (a-length (load-b-sym-fold-into-dz i n Abr st-vals dz))
              (a-length dz))
       (equal (x-length (load-b-sym-fold-into-dz i n Abr st-vals dz))
              (x-length dz))
       (equal (nx-row-length (load-b-sym-fold-into-dz i n Abr st-vals dz))
              (nx-row-length dz))
       (equal (nx-blk-length (load-b-sym-fold-into-dz i n Abr st-vals dz))
              (nx-blk-length dz))
       (equal (dim (load-b-sym-fold-into-dz i n Abr st-vals dz))
              (dim dz))
       (equal (dim*dim (load-b-sym-fold-into-dz i n Abr st-vals dz))
              (dim*dim dz)))
  :hints
  (("Goal" :in-theory (enable z-length
                              a-length
                              x-length
                              nx-row-length
                              nx-blk-length
                              dim dim*dim
                              nth-theory-lemmas
                              update-bi
                              ))))

(defthm b-length-load-b-sym-fold-into-dz
  (implies (and (natp i)
                (= n (b-sym-fold-to-stv-length Abr))
                (= n (b-length dz)))
           (equal (b-length (load-b-sym-fold-into-dz i n Abr st-vals dz))
                  (b-length dz))))

(defun load-A-num-row-into-dz (addri       ;; absolute address of row
                                           ;; i, which is i * dim-Abr
                               row         ;; sparse row from A-num
                                           ;; matrix
                               dz          ;; STOBJ solver
                               )
  (declare (xargs :guard (and (natp addri)
                              (sra-rational-rowp row)
                              ;; this is NOT strong enough. We need to
                              ;; know the column indices in row are
                              ;; bounded!
                              ;; (< addri (a-length dz))
                              )
                  :guard-hints (("Goal" :in-theory (enable sra-rational-rowp)))
                  :stobjs dz))
  (if (atom row)
      dz
    (b* ((pair (car row))
           (col  (car pair))
           (val  (cdr pair))
           ((unless (< (+ addri col) (a-length dz)))
            (prog2$ (er hard? 'load-A-num-row-into-dz
                        "attempting to write to an index out of bounds!")
                    dz))
           (dz (update-ai (+ addri col) val dz)))
      (load-A-num-row-into-dz addri (cdr row) dz))))

(defthm load-a-num-row-into-dz-dz-props
  (and (equal (z-length (load-A-num-row-into-dz addri row dz))
              (z-length dz))
       (equal (b-length (load-A-num-row-into-dz addri row dz))
              (b-length dz))
       (equal (x-length (load-A-num-row-into-dz addri row dz))
              (x-length dz))
       (equal (nx-row-length (load-A-num-row-into-dz addri row dz))
              (nx-row-length dz))
       (equal (nx-blk-length (load-A-num-row-into-dz addri row dz))
              (nx-blk-length dz))
       (equal (dim (load-A-num-row-into-dz addri row dz))
              (dim dz))
       (equal (dim*dim (load-A-num-row-into-dz addri row dz))
              (dim*dim dz)))
  :hints
  (("Goal" :in-theory (enable z-length
                              b-length
                              x-length
                              nx-row-length
                              nx-blk-length
                              dim dim*dim
                              nth-theory-lemmas
                              update-ai
                              ))))

(defthm a-num-length-load-a-num-row
  (implies (and (natp addri)
                ;; we must know that the column indices are natural
                ;; numbers.
                (sra-rational-rowp row))
           (equal (a-length (load-A-num-row-into-dz addri row dz))
                  (a-length dz)))
  :hints
  (("Goal" :in-theory (enable sra-rational-rowp))))

(defun load-A-num-into-dz (i addri dim-Abr Abr dz)
  (declare (xargs :measure (nfix (- dim-Abr i))
                  :guard (and (natp i)
                              (natp addri)
                              (natp dim-Abr)
                              (= dim-Abr (A-num-length Abr)))
                  :stobjs (Abr dz)))
  (if (mbe :logic (zp (- dim-Abr i)) :exec (>= i dim-Abr))
      dz
    (b* ((row (A-numi i Abr))
         ;; we assume A (in dz STOBJ) is cleared.
         (dz (load-A-num-row-into-dz addri row dz)))
      (load-A-num-into-dz (1+ i) (+ addri dim-Abr) dim-Abr Abr dz))))

(defthm load-a-num-into-dz-dz-props
  (and (equal (z-length (load-A-num-into-dz i addri dim-Abr Abr dz))
              (z-length dz))
       (equal (b-length (load-A-num-into-dz i addri dim-Abr Abr dz))
              (b-length dz))
       (equal (x-length (load-A-num-into-dz i addri dim-Abr Abr dz))
              (x-length dz))
       (equal (nx-row-length (load-A-num-into-dz i addri dim-Abr Abr dz))
              (nx-row-length dz))
       (equal (nx-blk-length (load-A-num-into-dz i addri dim-Abr Abr dz))
              (nx-blk-length dz))
       (equal (dim (load-A-num-into-dz i addri dim-Abr Abr dz))
              (dim dz))
       (equal (dim*dim (load-A-num-into-dz i addri dim-Abr Abr dz))
              (dim*dim dz))))

(defthm a-num-length-load-a-num-into-dz
  (implies (and (natp addri)
                (= dim-Abr (A-num-length Abr))
                ;; we must know that the column indices are natural
                ;; numbers.
                (Abrp Abr))
           (equal (a-length (load-A-num-into-dz i addri dim-Abr Abr dz))
                  (a-length dz))))

(defthm all-sra-rows-columns-samep-A-sym-fold-to-stvi-A-numi-!current-time
  (implies
   (all-sra-rows-columns-samep-a-sym-fold-to-stvi-a-numi
    i a-num-length abr)
   (all-sra-rows-columns-samep-a-sym-fold-to-stvi-a-numi
    i a-num-length (!current-time new-time abr))))

(defthm a-sym-fold-to-stv-good-map-help-stv-vals-to-A-num-!current-time
   (implies (a-sym-fold-to-stv-good-map-help
             i n Abr (stvl st-vals))
            (a-sym-fold-to-stv-good-map-help
             i n (!current-time new-time Abr)
             (stvl st-vals))))

(defun-inline rec-time-hn-updates (r2f-time r2f-hn cycle nvars rec)
  (declare (xargs :guard (and (nump r2f-time)
                              (nump r2f-hn)
                              (posp cycle)
                              (natp nvars)
                              (<= (len *initial-vars*) nvars)
                              (<= (* (1+ cycle) nvars) (arl rec))
                              (<= (arl rec) *2^60*))
                  :guard-hints (("Goal"
                                 :in-theory (enable ar-theory-lemmas)
                                 :nonlinearp t))
                  :stobjs rec))
  (b* ((rec (!ari *$time$-index* cycle nvars r2f-time rec))
       (rec (!ari *$hn$-index* cycle nvars r2f-hn rec)))
    rec))

(defthm recp-rec-time-hn-updates
  (implies (and (recp rec)
                (nump r2f-time)
                (nump r2f-hn)
                (natp nvars)
                (natp cycle)
                (<= (len *initial-vars*) nvars)
                (<= (* (1+ cycle) nvars) (arl rec)))
           (recp (rec-time-hn-updates r2f-time r2f-hn cycle nvars rec)))
  :hints
  (("Goal" :in-theory (enable ar-theory-lemmas))))

(defthm ari-non-time-index-rec-time-hn-updates
  (implies (and (natp i)
                (natp nvars)
                (< i nvars)
                (natp cycle)
                (<= (len *initial-vars*) nvars))
           (equal (ari i cycle nvars
                       (rec-time-hn-updates r2f-time r2f-hn cycle nvars rec))
                  (if (equal i *$time$-index*)
                      r2f-time
                    (if (equal i *$hn$-index*)
                        r2f-hn
                      (ari i cycle nvars rec)))))
  :hints
  (("Goal" :in-theory (enable ar-theory-lemmas))))

(defthm arl-rec-time-hn-updates
  (implies (and (force (natp nvars))
                (force (natp cycle))
                (force (<= (len *initial-vars*) nvars))
                (force (<= (* (1+ cycle) nvars) (arl rec))))
           (equal (arl (rec-time-hn-updates r2f-time r2f-hn cycle nvars rec))
                  (arl rec)))
  :hints
  (("Goal" :in-theory (enable ar-theory-lemmas))))

(in-theory (disable rec-time-hn-updates))

(defthm b-sym-fold-to-stv-good-map-!current-time
  (implies (b-sym-fold-to-stv-good-map i n stvl Abr)
           (b-sym-fold-to-stv-good-map i n stvl (!current-time new-time Abr)))
  :hints
  (("Goal" :in-theory (enable !current-time b-sym-fold-to-stvi nth-theory-lemmas))))

(defthm b-sym-fold-to-stvi-!A-numi
  (equal (b-sym-fold-to-stvi i (!A-numi j v Abr))
         (b-sym-fold-to-stvi i Abr))
  :hints
  (("Goal" :in-theory (enable b-sym-fold-to-stvi !A-numi nth-theory-lemmas))))

(defthm b-sym-fold-to-stvi-stv-vals-to-A-num
  (equal (b-sym-fold-to-stvi i (car (stv-vals-to-A-num j n LU-redo-p Abr st-vals)))
         (b-sym-fold-to-stvi i Abr))
  :hints
  (("Goal" :in-theory (enable stv-vals-to-A-num))))

(defthm b-sym-fold-to-stv-good-map-stv-vals-to-A-num
  (implies (b-sym-fold-to-stv-good-map i n stvl Abr)
           (b-sym-fold-to-stv-good-map
            i n stvl (car (stv-vals-to-A-num j n2 LU-redo-p Abr st-vals))))
  :hints
  (("Goal" :in-theory (enable stv-vals-to-A-num))))

(defun simulate-step-Abr-dz-lengths-guard (Abr dz)
  (declare (xargs :guard t
                  :stobjs (Abr dz)))
  (and
   ;; Abr b fields used by simulate-step
   (= (b-length dz) (b-sym-fold-to-stv-length Abr))

   ;; Abr A fields used by simulate-step
   (= (A-num-length Abr) (A-sym-fold-to-stv-length Abr))
   ;; (= (A-num-length Abr) (a-length dz))
   (= (* (A-num-length Abr) (A-num-length Abr)) (a-length dz))

   ;; DZ fields
   (natp (dim dz))     ;; add to DZ stobj definition
   (natp (dim*dim dz)) ;; add to DZ stobj definition
   (= (dim*dim dz) (* (dim dz) (dim dz)))
   (= (dim*dim dz) (a-length dz))
   (= (dim*dim dz) (z-length dz))
   (= (dim dz) (b-length dz))
   (= (dim dz) (x-length dz))
   (= (dim dz) (nx-row-length dz))
   (= (dim dz) (nx-blk-length dz))))

(in-theory (disable all-sra-rows-columns-samep-A-sym-fold-to-stvi-A-numi))

(defthm key-bound-under-arl
  (implies (and (posp nvars)
                (posp cycle)
                (equal arl (* ncycles nvars))
                (natp ncycles)
                (< cycle ncycles))
           (<= (+ nvars (* cycle nvars))
               arl))
  :hints (("Goal" :nonlinearp t))
  :rule-classes :linear)

; The following lemmas, up to the encapsulate below them, are intended to
; assist in admitting (verify-guards simulate-step ...) below.

(defthm times-ok-update-rec-x-names
  (implies (and (force (natp dz-i))
                (force (natp x-names-offset))
                (force (natp nvars))
                (force (natp cycle))
                (force (<= (+ len-x x-names-offset) nvars))
                (force (<= (len *initial-vars*) x-names-offset)))
           (and (equal (ari *$time$-index* cycle nvars
                            (update-rec-x-names dz-i x-names-offset len-x
                                                cycle nvars rec dz))
                       (ari *$time$-index* cycle nvars rec))
                (equal (ari *$hn$-index* cycle nvars
                            (update-rec-x-names dz-i x-names-offset len-x
                                                cycle nvars rec dz))
                       (ari *$hn$-index* cycle nvars rec))))
  :hints
  (("Goal" :in-theory (enable ar-theory-lemmas))))

(defthm arl-update-rec-x-names
  (implies (and (force (natp dz-i))
                (force (natp x-names-offset))
                (force (natp nvars))
                (force (natp cycle))
                (force (<= (+ x-names-offset len-x) nvars))
                (force (<= (* (1+ cycle) nvars) (arl rec))))
           (equal (arl (update-rec-x-names dz-i x-names-offset len-x
                                           cycle nvars rec dz))
                  (arl rec)))
  :hints
  (("Goal" :in-theory (enable ar-theory-lemmas))))

(defthm times-ok-xp-rec-updates
  (implies (and (force (natp x-i))
                (force (natp nvars))
                (force (natp cycle))
                (force (< x-i dp-x-i))
                (force (<= (len *initial-vars*) x-i)))
           (and (equal (ari *$time$-index* cycle nvars
                            (xp-rec-updates x-i dp-x-i cycle nvars hn rec))
                       (ari *$time$-index* cycle nvars rec))
                (equal (ari *$hn$-index* cycle nvars
                            (xp-rec-updates x-i dp-x-i cycle nvars hn rec))
                       (ari *$hn$-index* cycle nvars rec))))
  :hints
  (("Goal" :induct (xp-rec-updates x-i dp-x-i cycle nvars hn rec)
    :in-theory (enable ar-theory-lemmas))))

(defthm arl-xp-rec-updates
  (implies (and (force (natp nvars))
                (force (natp cycle))
                (force (< x-i dp-x-i))
                (force (<= (len *initial-vars*) x-i))
                (force (<= (* (1+ cycle) nvars) (arl rec))))
           (equal (arl (xp-rec-updates x-i dp-x-i cycle nvars hn rec))
                  (arl rec)))
  :hints
  (("Goal" :in-theory (enable ar-theory-lemmas))))

(defthm Abrp-stv-vals-to-A-num
  (implies (and (force (Abrp Abr))
                (force ; to expose where this is a problem
                 (st-valsp st-vals))
                (force (natp i))
                (force (natp n))
                (force (<= i n))
                (force (= n (A-sym-fold-to-stv-length Abr)))
                (force (= n (A-num-length Abr)))
                (force (a-sym-fold-to-stv-good-map-help i n Abr (stvl st-vals)))
                )
           (Abrp (car (stv-vals-to-A-num i n LU-redo-p Abr st-vals))))
  :hints (("Goal" :induct (stv-vals-to-A-num i n LU-redo-p Abr st-vals))))

(defthm recp-xp-rec-updates
  (implies (and (force (recp rec))
                (force (natp nvars))
                (force (posp cycle))
                (force (natp x-i))
                (force (< x-i dp-x-i))
                (force (rationalp hn))
                (force (<= (* (1+ cycle) nvars) (arl rec))))
           (recp (xp-rec-updates x-i dp-x-i cycle nvars hn rec)))
  :hints
  (("Goal" :in-theory (enable ar-theory-lemmas))))

(defthm st-valsp-init-st-vals
  (implies (and (force (st-valsp st-vals))
                (force (recp rec))
                (force (natp i))
                (force (natp cycle))
                (force (natp nvars))
                (force (<= (* (1+ cycle) nvars) (arl rec)))
                (force (<= nvars (stvl st-vals))))
           (st-valsp (init-st-vals i cycle nvars rec st-vals)))
  :hints
  (("Goal" :in-theory (enable stv-theory-lemmas ar-theory-lemmas))))

(defthm recp-update-rec-x-names
  (implies (and (force (force (recp rec)))
                (force (force (dzp dz)))
                (force (natp dz-i))
                (force (natp x-names-offset))
                (force (natp cycle))
                (force (natp nvars))
                (force (<= len-x (x-length dz)))
                (force (<= (+ x-names-offset len-x) nvars))
                (force (<= (* (1+ cycle) nvars) (arl rec))))
           (recp (update-rec-x-names dz-i x-names-offset len-x
                                     cycle nvars rec dz)))
  :hints
  (("goal" :in-theory (enable ar-theory-lemmas))))

(defthm all-rec-names-car-stv-vals-to-a-num
  (equal (nth *all-rec-names*
              (car (stv-vals-to-a-num i n lu-redo-p abr st-vals)))
         (nth *all-rec-names* abr))
  :hints (("Goal" :in-theory (enable nth-theory-lemmas
                                     !a-numi))))

(defthm nth-all-rec-names-!current-time
  (implies (abrp abr)
           (equal (nth *all-rec-names*
                       (!current-time current-time abr))
                  (nth *all-rec-names* abr)))
  :hints (("Goal" :in-theory (enable nth-theory-lemmas !current-time))))

(encapsulate
  ()

(defun simulate-measure-mbt (current-time hn time-stop)
  (declare (xargs :guard t))
  (and (rationalp current-time)
       (rationalp hn)
       (rationalp time-stop)
       (< 0 current-time)
       (< 0 hn)
       (< 0 time-stop)))

; Use the following during debugging, in place of AND, if you want an error
; when a conjunct is false.
 #|
 (defmacro my-and (&rest args)
   (cond ((endp args) t)
         (t `(and (or ,(car args)
                      (er hard 'my-and
                          "Failed: ~x0"
                          ',(car args)))
                  (my-and ,@(cdr args))))))
 |#

(defun simulate-step-guard (x-names-offset ; node & branch names starting position in REC
                            x-names-len ; number of node & branch names in REC
                            dp-x-names-offset ; node & branch derivatives starting position in REC
                            ref-node-offset ; reference node (zero volts/phase) position in REC
                            dp-ref-node-offset ; reference node derivative position in REC
                            current-time       ; a rational
                            hn                 ; a rational
                            time-stop          ; a rational
                            cycle              ; a posp
                            first-step-p
                            subterms ; list of all subterms that must be evaluated.
                            nvars ; (len (all-rec-names Abr))
                            Abr st-vals dz rtime rec ncycles)
  (declare (ignorable dz first-step-p))
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable ar-theory-lemmas)))
                  :stobjs (Abr st-vals dz rtime rec)))
  (and (natp x-names-offset)
       (natp x-names-len)
       (natp dp-x-names-offset)
       (natp ref-node-offset)
       (natp dp-ref-node-offset)
       (rationalp time-stop)
       (natp ncycles)
       (posp cycle)
       (equal nvars (len (all-rec-names Abr)))
       (<= (len *initial-vars*) x-names-offset)
       (<= (len *initial-vars*) ref-node-offset)
       (<= (len *initial-vars*) dp-ref-node-offset)
       (< (+ x-names-offset x-names-len) nvars)
       (< x-names-offset dp-x-names-offset)
       (< dp-x-names-offset nvars)
       (< ref-node-offset nvars)
       (< dp-ref-node-offset nvars)
       (< nvars *2^60*)
       (<= (arl rec) *2^60*)
       (<= nvars (stvl st-vals))
       (< (stvl st-vals) *2^60*)
       (simulate-measure-mbt current-time hn time-stop)
       (<= hn current-time)
       (= (+ (len subterms) nvars) (stvl st-vals))
       (vw-eval-subterm-listp subterms nvars (stvl st-vals))
       (= x-names-len (x-length dz))

       (simulate-step-Abr-dz-lengths-guard Abr dz)
       (all-sra-rows-columns-samep-A-sym-fold-to-stvi-A-numi 0 (A-num-length Abr) Abr)
       (a-sym-fold-to-stv-good-map-help 0 (A-num-length Abr) Abr (stvl st-vals))
       (b-sym-fold-to-stv-good-map 0 (b-sym-fold-to-stv-length Abr) (stvl st-vals) Abr)
       (<= cycle ncycles)
       (= (* ncycles nvars) (arl rec))
       (equal (len (time-list rtime)) cycle)
       (equal (len (hn-list rtime)) cycle)
       (<= 0 (car (hn-list rtime)))
       (<= (car (hn-list rtime))
           (car (time-list rtime)))))

(defun simulate-step (x-names-offset ; node & branch names starting position in REC
                      x-names-len    ; number of node & branch
; names in REC
                      dp-x-names-offset ; node & branch derivatives starting position in REC
                      ref-node-offset ; reference node (zero volts/phase) position in REC
                      dp-ref-node-offset ; reference node derivative position in REC
                      current-time       ; a rational
                      hn                 ; a rational
                      time-stop          ; a rational
                      cycle              ; a natp
                      first-step-p       ; boolean
                      subterms  ; list of all subterms that must be evaluated.
                      nvars     ; (len (all-rec-names Abr))
                      Abr       ; STOBJ for VWSIM matrices and record
                      st-vals   ; STOBJ for storing evaluated subterms results.
                      dz        ; STOBJ for matrix equation solving
                      rtime     ; STOBJ for list of times and their deltas
                      rec       ; STOBJ for storing VWSIM
                      ncycles)  ; total number of steps (0, 1, ... ncycles-1)
; simulation record
  (declare (ignorable x-names-offset ; node & branch names starting position in REC
                      x-names-len    ; number of node & branch
; names in REC
                      dp-x-names-offset ; node & branch derivatives starting position in REC
                      ref-node-offset ; reference node (zero volts/phase) position in REC
                      dp-ref-node-offset ; reference node derivative position in REC
                      current-time       ; a rational
                      hn                 ; a rational
                      time-stop          ; a rational
                      cycle              ; a natp
                      subterms  ; list of all subterms that must be evaluated.
                      first-step-p
                      nvars     ; (len (all-rec-names Abr))
                      Abr       ; STOBJ for VWSIM matrices and record
                      st-vals   ; STOBJ for storing evaluated subterms results.
                      dz        ; STOBJ for matrix equation solving
                      rtime
                      rec))
  (declare
   (xargs :guard
          (simulate-step-guard x-names-offset
                               x-names-len
                               dp-x-names-offset
                               ref-node-offset
                               dp-ref-node-offset
                               current-time
                               hn
                               time-stop
                               cycle
                               first-step-p
                               subterms
                               nvars
                               Abr
                               st-vals
                               dz
                               rtime
                               rec
                               ncycles
                               )
          ;;(simulate-step-guard x-names dp-x-names ref-node
          ;;current-time hn time-stop Abr)
          :verify-guards nil
          :stobjs (Abr st-vals dz rtime rec)
          :guard-hints (("Goal" :in-theory (enable ar-theory-lemmas
                                                   stv-theory-lemmas)))
          :measure (nfix (- (1+ ncycles) cycle))
          ))
  (b* (((unless (mbt (simulate-measure-mbt current-time hn time-stop)))
        (mv Abr st-vals dz rtime rec))
       ;; Termination test
       ((when (or (not (mbt (and (natp ncycles) (natp cycle))))
                  (>= cycle ncycles)))
        (mv Abr st-vals dz rtime rec))

       ;; save the current, rational simulation time in the Abr
       ;; STOBJ
       (Abr (!current-time current-time Abr))

       (pcycle (1- cycle)) ; previous cycle

       ;; Record new time hn and current-time as rational numbers.
       (r2f-time (r2f current-time))
       (r2f-hn (r2f hn))
       (rec (rec-time-hn-updates r2f-time r2f-hn cycle nvars rec))

       ;; We use the current values (at current-time) of the input
       ;; sources and the previous values of the nodes, branches,
       ;; and derivatives to solve (approximately) for the current
       ;; values for the nodes, branches, and derivatives by solving
       ;; for x given matrices A and b.

       (st-vals (!stvi *$time$-index* (r2f current-time) st-vals))
       (st-vals (!stvi *$hn$-index* (r2f hn) st-vals))
       (st-vals (init-st-vals ref-node-offset pcycle nvars rec st-vals))

       ;; This calculation attempts to reconcile the previous state
       ;; of the system with a new state that is consistent with the
       ;; currently-provided, input-source, values.

       ;; The transmission line looks back from the current time to
       ;; the values at the current time minus the delay time.

       ;; Evaluate symbolic matrices A and b given current input
       ;; source (voltage, current, phase) values and previous node,
       ;; branch, and derivative values.

       ;; Perform one-pass evaluation of all subterms and store in
       ;; STV array.
       (rtime (update-rtime current-time hn rtime))
       (st-vals (vw-eval-subterm-list subterms nvars pcycle nvars rtime rec
                                      st-vals))

       ;; Call st-vals-to-A-num. If LU-redo-p flag is set, clear dz
       ;; A array and call load-A-num-into-dz.

       ((mv Abr ?LU-redo-p) (stv-vals-to-A-num 0 (A-num-length Abr)
                                               nil Abr st-vals))

       ;; LU-redo-p is set either by load-A-jj-sym-into-A-num or if
       ;; this is the first simulation step!
       (LU-redo-p (or LU-redo-p
                      first-step-p))

       ;; if the matrix decomposition of A must be performed, clear
       ;; dz's A matrix
       (dz (if LU-redo-p
               (clear-dz-a 0 (a-length dz) dz)
             dz))

       ;; non-zero entries in Abr's A-num are stored in dz's A
       ;; matrix.
       (dz (if LU-redo-p
               (load-A-num-into-dz 0 0 (A-num-length Abr) Abr dz)
             dz))

       ;; we don't need to clear dz's b array since we write to
       ;; every entry.
       (dz
        (load-b-sym-fold-into-dz 0 (b-sym-fold-to-stv-length Abr) Abr st-vals dz))

       ;; Decompose A if it changed from the previous simulation
       ;; step.
       ((mv ?flg dz)
        (if LU-redo-p
            (dz-unc-decomp dz)
          (mv nil dz)))

       ((when flg)
        (prog2$
         (cw "simulate-step: a singular matrix was generated!~%")
         (mv Abr st-vals dz rtime rec)))

       ;; Solve for x
       (dz (dz-unc-solve dz))

       ;; Update the node and branch variables
       (rec (update-rec-x-names 0 x-names-offset x-names-len cycle nvars rec
                                dz))

       ;; Update the node and branch derivative variables
       (rec (xp-rec-updates x-names-offset dp-x-names-offset cycle nvars r2f-hn
                            rec))

       ;; Set next values of reference node and its derivative to zero
       (rec (!ari ref-node-offset cycle nvars (r2f 0) rec))

       (rec (!ari dp-ref-node-offset cycle nvars (r2f 0) rec))

       ;; Advance simulator time
       (current-time (+ current-time hn))

       )

    (simulate-step x-names-offset ; node & branch names starting position in REC
                   x-names-len    ; number of node & branch names in REC
                   dp-x-names-offset ; node & branch derivatives starting position in REC
                   ref-node-offset ; reference node (zero volts/phase) position in REC
                   dp-ref-node-offset ; reference node derivative position in REC
                   current-time       ; a rational
                   hn                 ; a rational
                   time-stop          ; a rational
                   (1+ cycle)         ; a natural
                   nil ; first-step-p
                   subterms  ; list of all subterms that must be evaluated.
                   nvars ; (len (all-rec-names Abr))
                   Abr       ; STOBJ for VWSIM matrices and record
                   st-vals   ; STOBJ for storing evaluated subterms results.
                   dz        ; STOBJ for matrix equation solving
                   rtime
                   rec
                   ncycles)))

)

(verify-guards simulate-step
  :otf-flg t
  :hints
  (("Goal" :in-theory (e/d (ar-theory-lemmas nth-theory-lemmas
                                             stvl-!stvi
                                             st-valsp-!stvi)
                           (vw-eval-subterm-listp
                            a-sym-fold-to-stv-good-map-help
                            b-sym-fold-to-stv-good-map))
    :do-not-induct t)
   (and stable-under-simplificationp
        '(:nonlinearp t))))

(defthm symbol-listp-remove-equal
  (implies (symbol-listp l)
           (symbol-listp (remove-equal x l))))

(defthm symbolp-last-syml-listp
  (implies (and (consp l)
                (symbol-listp l))
           (symbolp (car (last l)))))

(defthm symlp-last-syml-listp
  (implies (and (consp l)
                (syml-listp l))
           (symlp (car (last l)))))

(defthm syml-listp-last
  (implies (syml-listp l)
           (syml-listp (last l))))

(defthm syml-listp-remove-equal
  (implies (syml-listp l)
           (syml-listp (remove-equal x l))))

(defthm len-append
  (equal (len (append l1 l2))
         (+ (len l1)
            (len l2))))

(defthm len-remove
  (implies (no-duplicatesp-equal l)
           (equal (len (remove x l))
                  (if (member-equal x l)
                      (1- (len l))
                    (len l)))))

(defthm len-remove-append
  (implies (and (member-equal x l)
                (no-duplicatesp-equal l))
           (equal (len (append (remove x l)
                               (list x)))
                  (len l))))

(defthm not-member-equal-append
  (implies (and (not (member-equal x l1))
                (not (member-equal x l2)))
           (not (member-equal x (append l1 l2)))))

(defthm no-intersection-preserved-by-remove-duplicates
  (implies (not (intersection-equal l1 l2))
           (not (intersection-equal l1 (remove-duplicates-equal l2)))))

(defthm no-duplicatesp-equal-no-intersection
  (implies (and (no-duplicatesp-equal l1)
                (no-duplicatesp-equal l2)
                (not (intersection-equal l1 l2)))
           (no-duplicatesp-equal (append l1 l2))))

(defthm no-duplicatesp-equal-remove-duplicates-equal-2
  (no-duplicatesp-equal (remove-duplicates-equal l)))

(defthm help-len
  (implies (and (force (member-equal x (append l1 l2)))
                (force (no-duplicatesp-equal (append l1 l2))))
           (equal
            (+ (len (list x)) (len (remove-equal x (append l1 l2))))
            (+ (len l1) (len l2)))))

(defun create-x-names (ref-node occs)
  (declare (xargs :guard (and (symlp ref-node)
                              (occurrencesp occs))))
  (b* ((all-ios (all-node-names occs))
       (all-ios-no-dups (remove-duplicates all-ios :test 'eq))

        ;; Resistor branch names are not returned by all-branch-names
        ;; as we do not want to include these variables in our x
        ;; vector (please see the VWSIM builders manual).
        (all-branch-names (all-branch-names occs))

        ;; Note: the branch names are first in ``x-names'' (the names
        ;; of the entries in the x vector), followed by the node names.
        ;; This can't be changed without consideration of the method we
        ;; use to select the reference node: if the reference node does
        ;; not exist in ``x-names'', we select, arbitrarily, the LAST
        ;; entry in ``x-names'' to be the reference node.  Again, we
        ;; can do this since the nodes follow the branch names in
        ;; ``x-names''.
        (x-names (append all-branch-names
                         all-ios-no-dups))

        (len-x-names (len x-names))

        ;; Require matrices A and b to have at least two nodes
        ((unless (< 1 len-x-names))
         (prog2$
          (cw "create-x-names: x-names is empty.~%")
          nil))

        ;; If REF-NODE exists, move to the end of the list
        (x-names (if (member ref-node x-names)
                     (append (remove ref-node x-names)
                             (list ref-node))
                   x-names)))
    x-names))

(defthm syml-listp-create-x-names
  (implies (and (symlp ref-node)
                (occurrencesp occs))
           (syml-listp (create-x-names ref-node occs))))

(defthm symbol-listp-create-x-names
  (implies (and (symlp ref-node)
                (occurrencesp occs))
           (symbol-listp (create-x-names ref-node occs)))
  :hints
  (("Goal" :use syml-listp-create-x-names)))

(encapsulate
  ()
  (local
   (defthm vw-eval-term-listp-symbol-listp
     (implies (symbol-listp l)
              (vw-eval-term-listp l))))

  (defthm vw-eval-term-listp-create-x-names
    (implies (and (symlp ref-node)
                  (occurrencesp occs))
             (vw-eval-term-listp (create-x-names ref-node occs)))
    :hints
    (("Goal" :in-theory (disable occurrencesp)))))

(in-theory (disable create-x-names))

(local
 (defthm occurrencesp-is-occurrence-listp
   (implies (occurrencesp occs)
            (occurrence-listp occs))))

(defthm symbol-listp-make-dp-list-2
  (symbol-listp (make-dp-list l))
  :rule-classes :type-prescription)

(defthm symbol-listp-append
  (implies (and (symbol-listp l1)
                (symbol-listp l2))
           (symbol-listp (append l1 l2))))

(defthm true-listp-make-list-ac
  (implies (true-listp ac)
           (true-listp (make-list-ac n val ac))))

(defthm alistp-number-list
  (alistp (number-list l i)))

(defthm vw-eval-term-nat-alistp-number-list
  (implies (and (vw-eval-term-listp l)
                (natp i))
           (vw-eval-term-nat-alistp (number-list l i))))

(defun ncycles (time-start time-stop hn)

; Cycles are at time-start, time-start+hn, time-start+2hn, ...,
; time-start+(k-1)hn where k is least such that:
; time-start + k*hn >= time-stop.
; I.e., k is the least integer such that:
; k >= (time-stop - time-start) / hn,
; which is the ceiling of that quotient.
; But k is the number of cycles so we have the expression below.

  (declare (type rational time-start time-stop hn)
           (xargs :guard (not (= hn 0))))
  (nfix (ceiling (- time-stop time-start) hn)))

(defthm len-cons
  (equal (len (cons x y))
         (1+ (len y))))

(local
 (defthm rec-arp-!nth
   (implies (and (rec-arp a)
                 (<= i (len a))
                 (rationalp v))
            (rec-arp (!nth i v a)))
   :hints
   (("Goal" :in-theory (enable nth-theory-defuns)))))

(defthm recp-!nth
  (implies (and (recp rec)
                (<= i (arl rec))
                (rationalp v))
           (recp (!nth 0 (!nth i v (nth 0 rec)) rec)))
  :hints (("Goal" :in-theory (enable recp arl nth-!nth))))

(defthm arl-!nth
  (implies (and (force (natp i))
                (force (< i (arl rec))))
           (equal (arl (!nth 0 (!nth i v (nth 0 rec)) rec))
                  (arl rec)))
  :hints (("Goal" :in-theory (enable recp arl nth-!nth len-!nth))))

(defthm arl-clear-rec
  (implies (and (natp i)
                (<= i n)
                (<= n (arl rec)))
           (equal (arl (clear-rec i n rec))
                  (arl rec)))
  :hints (("Goal" :induct (clear-rec i n rec))))

(defthm alist-entry-consp-pairlis$
  (implies (and (<= (len l1) (len l2))
                (alistp l2))
           (alist-entry-consp (pairlis$ l1 l2))))

(defthm alistp-make-list-ac
  (implies (and (consp l)
                (alistp ac))
           (alistp (make-list-ac n l ac))))

(defthm alistp-make-list
  (implies (consp l)
           (alistp (make-list n :initial-element l))))

(defthm alist-entry-consp-append
  (implies (and (alist-entry-consp al1)
                (alist-entry-consp al2))
           (alist-entry-consp (append al1 al2))))

(defthm symbol-rational-list-alistp-append
  (implies (and (symbol-rational-list-alistp al1)
                (symbol-rational-list-alistp al2))
           (symbol-rational-list-alistp (append al1 al2))))

(defun rational-list-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (rational-listp (car x))
         (rational-list-listp (cdr x)))))

(defthm symbol-rational-list-alistp-pairlis$
  (implies (and (symbol-listp l1)
                (rational-list-listp l2))
           (symbol-rational-list-alistp (pairlis$ l1 l2))))

(defthm rational-list-listp-make-list-ac
  (implies (and (rational-listp l)
                (rational-list-listp ac))
           (rational-list-listp (make-list-ac n l ac))))

(defthm rational-list-listp-make-list
  (implies (rational-listp l)
           (rational-list-listp (make-list n :initial-element l))))

(defthm vw-eval-termp-remove
  (implies (vw-eval-term-listp l)
           (vw-eval-term-listp (remove x l))))

(defun simulate (Abr st-vals dz rtime rec)
  (declare
   (xargs :guard t
          :guard-hints (("Goal"
; The following :expand hint helped by expanding LETs more aggressively.
                         :expand :lambdas
                         :in-theory
                         (e/d (ar-theory-lemmas
                               arl-!ari
                               ar-length-is-resize
                               arl-clear-rec)
                              (true-listp len member-equal pairlis$
                                          hons-assoc-equal all-hons-assoc-equal
                                          cdr-true-list-alistp
                                          occurrencesp
                                          number-list
                                          r2f-term-list
                                          floor ceiling
                                          ))))
          :stobjs (Abr st-vals dz rtime rec)))
  ;; Need to add r and module if we want to continue a saved simulation
  (b* (;; unchanged by simulate
       (occs (flat-occs Abr))
       ;; changed by simulate
       (Abr-ref-node (ref-node Abr))
       ;; unchanged by simulate
       (time-start (time-start Abr))
       ;; unchanged by simulate
       (hn (hn Abr))
       ;; unchanged by simulate
       (time-stop (time-stop Abr))
       ((unless (and (rationalp time-start)
                     (<= 0 time-start)
                     (rationalp hn)
                     (< 0 hn)
                     (rationalp time-stop)
                     (< 0 time-stop)))
        (prog2$
         (cw "simulate: TIME-START, STEP (hn), or TIME-STOP problem.~%")
         (mv Abr st-vals dz rtime rec)))
       ;; unchanged by simulate
       (sim-type (sim-type Abr))
       ;; unchanged by simulate
       (equations (equations Abr))
       ;; unchanged by simulate
       (alter-values-alist (alter-values-alist Abr))
       (load-sim (load-sim Abr))
       (ncycles0 (ncycles time-start time-stop hn)))

    ;; We assume that the Abr STOBJ has been initialized with all of
    ;; the simulation arguments.
    (if load-sim
        (b* ((start-cycle (length (time-list rtime)))
             (ncycles (+ start-cycle ncycles0))
             (nvars (len (all-rec-names Abr)))
             (- (cw "simulate: ~x0 simulation variables.~%" nvars))
             (x-names-offset (x-names-offset Abr))
             (x-names-len (len (x-names Abr)))
             (dp-x-names-offset (dp-x-names-offset Abr))
             (ref-node-offset (ref-node-offset Abr))
             (dp-ref-node-offset (dp-ref-node-offset Abr))
             (all-stv-subterms (all-stv-subterms Abr))
             (dz (right-size-dz (dim-Abr Abr) dz))
             ((unless (simulate-step-guard x-names-offset
                                           x-names-len
                                           dp-x-names-offset
                                           ref-node-offset
                                           dp-ref-node-offset
                                           time-start ;; current-time
                                           hn
                                           time-stop
                                           start-cycle
                                           t ; first-step-p
                                           all-stv-subterms
                                           nvars
                                           Abr
                                           st-vals
                                           dz
                                           rtime
                                           rec
                                           ncycles))
              (prog2$ (cw "simulate: simulate-step guard not ~
              satisfied while attempting to resume simulation!~%")
                      (mv Abr st-vals dz rtime rec))))
          (simulate-step x-names-offset
                         x-names-len
                         dp-x-names-offset
                         ref-node-offset
                         dp-ref-node-offset
                         time-start
                         ;; Time step
                         hn
                         time-stop
                         start-cycle
                         t ; first-step-p
                         all-stv-subterms
                         nvars
                         Abr
                         st-vals
                         dz
                         rtime
                         rec
                         ncycles))

      (b* ((ncycles ncycles0) ; don't add 1, even though starting cycle is 1
           ((unless (occurrencesp occs))
            (prog2$
             (cw "simulate: Input not a occurrencesp.~%")
             (mv Abr st-vals dz rtime rec)))
           ((unless (symlp Abr-ref-node))
            (prog2$
             (cw "simulate: Input reference node not a symlp.~%")
             (mv Abr st-vals dz rtime rec)))
           ((unless (rationalp time-start))
            (prog2$
             (cw "simulate: Input time not a rational number.~%")
             (mv Abr st-vals dz rtime rec)))

           (x-names (create-x-names Abr-ref-node occs))

           (ref-node (car (last x-names)))

           ;; maybe prove this away???
           ((unless (symlp ref-node)) ;; for later (DP-NAME REF-NODE)
            (prog2$
             (cw "simulate: bad reference node name: ~p0.~%" ref-node)
             (mv Abr st-vals dz rtime rec)))

           (Abr (!ref-node ref-node Abr))

           (len-x-names (len x-names))

           ;; maybe prove this away???
           ((unless (< len-x-names *2^60*))
            (prog2$
             (cw "simulate: x-names has more than 2^60 elements!~%")
             (mv Abr st-vals dz rtime rec)))

           ;; Initialize matrices Abr STOBJ
           (Abr (Abr-size-and-init len-x-names Abr))

           ;; Initialize the symbolic A and b matrices with appropriate
           ;; tags
           (Abr (create-symbolic-Ab x-names occs occs sim-type
                                    Abr))

           ;; REF-NODE has been placed last; thus, remove last row and
           ;; column from A and last row from b
           (dim-no-ref-node (1- (b-sym-length Abr)))
           ;; remove last row
           (Abr (resize-Abr-arrays dim-no-ref-node Abr))
           ;; remove last column in A-sym.
           (Abr (remove-last-col-A-sym 0 dim-no-ref-node Abr))

           ;; resize the DZ STOBJ fields as well
           (dz (right-size-dz dim-no-ref-node dz))

           ;; the new dimension of all matrices
           (dim-Abr dim-no-ref-node)
           (Abr (!dim-Abr dim-Abr Abr))

           ;; initialize column indices in A-num
           (Abr (init-A-num 0 (A-num-length Abr) Abr))

           ;; remove reference node from x-names
           (x-names (remove ref-node x-names))
           (Abr (!x-names x-names Abr))

           ;; Create names for derivative variables
           (dp-x-names (make-dp-list x-names))
           (Abr (!dp-x-names dp-x-names Abr))

           (ref-node-names (list ref-node (dp ref-node)))

           ;; all of the names in the record
           (all-rec-names (append
                           ;; $time$, $hn$
                           *initial-vars*
                           ;; ref-node, dp-ref-node
                           ref-node-names
                           x-names
                           dp-x-names))
           (nvars (len all-rec-names))
           (- (cw "simulate: ~x0 simulation variables.~%" nvars))
           (Abr (!all-rec-names all-rec-names Abr))

           ;; Get starting positions of each group of variable names
           ;; in the record
           ;; Reference node
           (ref-node-offset      (len *initial-vars*))
           (Abr (!ref-node-offset ref-node-offset Abr))
           (dp-ref-node-offset   (1+ ref-node-offset))
           (Abr (!dp-ref-node-offset dp-ref-node-offset Abr))

           ;; Record variables
           (x-names-offset     (+ ref-node-offset
                                  (len ref-node-names)))
           (Abr (!x-names-offset x-names-offset Abr))

           ;; Derivatives of record variables
           (dp-x-names-offset  (+ x-names-offset
                                  (len x-names)))
           (Abr (!dp-x-names-offset dp-x-names-offset Abr))

           ;; To see the names and the raw equations, set equations
           ;; to t
           ((when equations)
            (mv Abr st-vals dz rtime rec))

           (constant-alist
            (make-fast-alist
             (append ;; multiplier constants used in circuit
                     ;; descriptions will be folded away.
                     *multiplier-constants*
                     *f-constants*
                     (pairlis$
                      ref-node-names
                      ;; The reference node and its
                      ;; derivative are zero, thus we
                      ;; fold them away.
                      (make-list (len ref-node-names)
                                 :initial-element '(0)))
                     alter-values-alist)))

           ;; Maybe prove this away???
           ((unless (and (= (b-sym-length Abr)
                            (b-sym-fold-length Abr))))
            (prog2$ (cw "simulate: vw-eval-fold-b-sym Abr stobj ~
            fields not appropriately sized or constant alist bad.~%")
                    (mv Abr st-vals dz rtime rec)))

           ;; Initialize b-sym-fold and A-sym-fold

           ;; Simplify the terms in b-sym and A-sym by evaluating all
           ;; of the expressions that contain only quoted numbers and
           ;; symbols in constant-alist

           ;; Note: we perform this simplification after the equations
           ;; check since vw-eval-fold may return either quoted rationals
           ;; or double-floats

           (Abr (vw-eval-fold-b-sym 0 (b-sym-length Abr) constant-alist
                                    Abr))

           ;; Maybe prove this away???
           ((unless (= (A-sym-length Abr)
                       (A-sym-fold-length Abr)))
            (prog2$ (cw "simulate: A-sym-length and ~
            A-sym-fold-length not same before vw-eval-fold-A-sym!.~%")
                    (mv Abr st-vals dz rtime rec)))

           (Abr (vw-eval-fold-A-sym 0 (A-sym-length Abr) constant-alist
                                    Abr))

           ;; Gather all terms in b-sym-fold and A-sym-fold.
           (A-sym-terms (gather-terms-A-sym-fold 0 (A-sym-fold-length Abr) Abr))

           (b-sym-terms (gather-terms-b-sym-fold 0 (b-sym-fold-length Abr) Abr))
           (all-terms (append b-sym-terms A-sym-terms))

           ;; Maybe prove this away???
           ((unless (vw-eval-term-listp all-terms)
              )
            (prog2$ (cw "simulate: all-terms is not a vw-eval-term-listp!~%")
                    (mv Abr st-vals dz rtime rec)))

           ;; Generate all unique subterms from all-terms
           (all-subterms (all-subterms-list all-terms))

           ;; Add all record variable names to the list of subterms
           (all-subterms-with-all-rec-names
            (append all-rec-names all-subterms))

           ;; Create an alist that pairs each subterm with the
           ;; location of its evaluation result in the STV array.
           (subterms-to-stv-alist
            (make-fast-alist
             (number-list all-subterms-with-all-rec-names 0)))

           (Abr (!subterms-to-stv-alist subterms-to-stv-alist Abr))

           ;; Initialize b-sym-fold-to-stv, A-sym-fold-to-stv

           ;; Maybe prove this away???
           ((unless (= (b-sym-fold-to-stv-length Abr)
                       (b-sym-fold-length Abr)))
            (prog2$ (cw "simulate: b-sym-fold-to-stv-length not ~
            equal to b-sym-fold-length before init-b-sym-fold-to-stv.~%")
                    (mv Abr st-vals dz rtime rec)))

           (Abr (init-b-sym-fold-to-stv 0 (b-sym-fold-to-stv-length Abr)
                                        subterms-to-stv-alist
                                        Abr))

           ;; Maybe prove this away???
           ((unless (= (A-sym-fold-to-stv-length Abr)
                       (A-sym-fold-length Abr)))
            (prog2$ (cw "simulate: A-sym-fold-to-stv-length not ~
            equal to A-sym-fold-length before init-A-sym-fold-to-stv.~%")
                    (mv Abr st-vals dz rtime rec)))

           (Abr (init-A-sym-fold-to-stv 0 (A-sym-fold-to-stv-length Abr)
                                        subterms-to-stv-alist
                                        Abr))

           ;; If used, setup symbolic terms for floating-point
           ;; evaluation.
           (r2f-all-subterms (r2f-term-list all-subterms))
           (r2f-all-subterms-with-all-rec-names
            (r2f-term-list all-subterms-with-all-rec-names))
           (r2f-subterms-to-stv-alist
            (make-fast-alist
             (number-list r2f-all-subterms-with-all-rec-names 0)))

           ((unless (< (len all-subterms-with-all-rec-names) *2^60*))
            (prog2$ (cw "simulate: storage for the simulation ~
                         requested is too big!~%")
                    (mv Abr st-vals dz rtime rec)))

           ;; Maybe prove this away???
           ((unless (vw-eval-subterm-list-lookup-okp
                      r2f-all-subterms
                      r2f-subterms-to-stv-alist
                      nvars
                      (len all-subterms-with-all-rec-names)))
            (prog2$ (cw "simulate: vw-eval-term-list-to-subterm-list ~
                         guards not satisfied.~% r2f-all-subterms: ~
                         ~p0~% r2f-subterms-to-stv-alist: ~p0.~%"
                        r2f-all-subterms r2f-subterms-to-stv-alist)
                    (mv Abr st-vals dz rtime rec)))

           ;; Convert list of fully-symbolic subterms to a compressed
           ;; format for fast evaluation using the STV array.
           (all-stv-subterms
            (vw-eval-term-list-to-subterm-list
             ;; we only compress the subterms that are not variable
             ;; names.
             r2f-all-subterms
             r2f-subterms-to-stv-alist
             nvars
             (len all-subterms-with-all-rec-names) ;; (stvl st-vals)
             ))

           (- (fast-alist-free r2f-subterms-to-stv-alist))

           (Abr (!all-stv-subterms all-stv-subterms Abr))


           ;; Resize STV array
           (st-vals (resize-stv (len all-subterms-with-all-rec-names)
                                st-vals))

           ;; Initialize the record

           ((unless (< (* nvars ncycles) *2^60*))
            (prog2$ (cw "simulate: storage for the simulation ~
                         requested is too big!~%")
                    (mv Abr st-vals dz rtime rec)))

           ((when (= 0 ncycles))
            (prog2$ (cw "simulate: returning after 0 cycles!~%")
                    (mv Abr st-vals dz rtime rec)))

           ;; First, resize the AR array
           (rec (resize-ar ncycles nvars rec))
           (rec (clear-rec 0 (arl rec) rec))

           (rtime (init-rtime time-start rtime))
           (rec (!ari *$time$-index* 0 nvars (r2f time-start) rec))
           ;; Note: hn = the difference between the n and (n-1) time
           ;; steps. At the first step, there was no previous value
           ;; and thus the time step (hn) is 0.
           (rec (!ari *$hn$-index* 0 nvars (r2f 0) rec))

           (x-names-len (len x-names))
           ((unless (simulate-step-guard x-names-offset
                                         x-names-len
                                         dp-x-names-offset
                                         ref-node-offset
                                         dp-ref-node-offset
                                         hn ;; current-time
                                         hn
                                         time-stop
                                         1 ; starting cycle
                                         t ; first-step-p
                                         all-stv-subterms
                                         nvars
                                         abr
                                         st-vals
                                         dz
                                         rtime
                                         rec
                                         ncycles))
            (prog2$ (cw "simulate: simulate-step guard not satisfied!~%")
                    (mv Abr st-vals dz rtime rec)))

           ;; Run the simulator
           ((mv Abr st-vals dz rtime rec)
            (simulate-step x-names-offset
                           x-names-len
                           dp-x-names-offset
                           ref-node-offset
                           dp-ref-node-offset
                           ;; At time zero, all values, are 0
                           ;; Simulation starts at hn (the first
                           ;; non-zero time)
                           hn
                           ;; Time step
                           hn
                           time-stop
                           1 ; starting cycle
                           t ; first-step-p
                           all-stv-subterms
                           nvars
                           Abr
                           st-vals
                           dz
                           rtime
                           rec
                           ncycles
                           )))
        (mv Abr st-vals dz rtime rec)))))

;; The following events are used for loading and saving simulation
;; state (stored in Abr STOBJ) from/to a file

;; The following functions are used for VWSIM I/O. Can we admit the
;; next few events into ACL2 in :logic mode???

#+(and rec-stobj rec-dcls (not simple-vectors))
(declaim (ftype (function (double-float t t)
                          (values t))
                print-df$inline print-df-shortp$inline))

(defun-inline print-df (x channel state)
; Keep this in sync with print-df-shortp.
  (declare (xargs :mode :program :stobjs (state))
           #+rec-dcls (type double-float x))
  (princ$ x channel state))

(defun-inline print-df-shortp (x channel state)
; Keep this in sync with print-df.
  (declare (xargs :mode :program :stobjs (state))
           #+rec-dcls (type double-float x))
  #-raw (print-df x channel state)
  #+raw (princ$ (float x 1.0s0) channel state))

#+(and rec-stobj rec-dcls (not simple-vectors))
(declaim (ftype (function ((unsigned-byte 60)
                           (unsigned-byte 60)
                           (simple-array double-float (*))
                           t t)
                          (values t))
                write-rec-ar-1 write-rec-ar-1-shortp))

(defun write-rec-ar-1 (i len rec channel state)
; Keep this in sync with write-rec-ar-1-shortp.
  (declare (xargs :stobjs (rec state)
                  :mode :program)
           (type (unsigned-byte 60) i len)
           #+(and rec-stobj rec-dcls (not simple-vectors))
           (type (simple-array double-float (*)) rec))
  (cond ((= i len) state)
        (t (pprogn
            (print-df (rec-ari i rec) channel state)
            (princ$ #\Space channel state)
            (write-rec-ar-1 (1+ i) len rec channel state)))))

(defun write-rec-ar-1-shortp (i len rec channel state)
; Keep this in sync with write-rec-ar-1.
  (declare (xargs :stobjs (rec state)
                  :mode :program)
           (type (unsigned-byte 60) i len)
           #+(and rec-stobj rec-dcls (not simple-vectors))
           (type (simple-array double-float (*)) rec))
  (cond ((= i len) state)
        (t (pprogn
            (print-df-shortp (rec-ari i rec) channel state)
            (princ$ #\Space channel state)
            (write-rec-ar-1-shortp (1+ i) len rec channel state)))))

#+(and rec-stobj rec-dcls (not simple-vectors))
(declaim (ftype (function ((simple-array double-float (*)) t t t)
                          (values t))
                write-rec-ar))

(defun write-rec-ar (rec shortp channel state)
  (declare (xargs :stobjs (rec state)
                  :mode :program)
           #+(and rec-stobj rec-dcls (not simple-vectors))
           (type (simple-array double-float (*)) rec))
  (pprogn (princ$ #\( channel state)
          (cond
           (shortp
            #-raw
            (write-rec-ar-1-shortp 0 (arl rec) rec channel state)
            #+raw
            (let ((*read-default-float-format* 'single-float))
              (write-rec-ar-1-shortp 0 (arl rec) rec channel state)))
           (t
            (write-rec-ar-1 0 (arl rec) rec channel state)))
          (princ$ #\) channel state)
          (newline channel state)))

#+(and rec-stobj rec-dcls (not simple-vectors))
(declaim (ftype (function ((unsigned-byte 60)
                           (unsigned-byte 60)
                           (simple-array double-float (*))
                           t t)
                          (values t))
                write-stv-1 write-stv-1-shortp))

(defun write-stv-1 (i len st-vals channel state)
; Keep this in sync with write-rec-ar-1.
  (declare (xargs :stobjs (st-vals state)
                  :mode :program)
           (type (unsigned-byte 60) i len)
           #+(and st-vals-stobj st-vals-dcls (not simple-vectors))
           (type (simple-array double-float (*)) st-vals))
  (cond ((= i len) state)
        (t (pprogn
            (print-df (stvi i st-vals) channel state)
            (princ$ #\Space channel state)
            (write-stv-1 (1+ i) len st-vals channel state)))))

#+(and st-vals-stobj st-vals-dcls (not simple-vectors))
(declaim (ftype (function ((simple-array double-float (*)) t t)
                          (values t))
                write-stv))

(defun write-stv (st-vals channel state)
; Keep this in sync with write-rec-ar.
  (declare (xargs :stobjs (st-vals state)
                  :mode :program)
           #+(and st-vals-stobj st-vals-dcls (not simple-vectors))
           (type (simple-array double-float (*)) st-vals))
  (pprogn (princ$ #\( channel state)
          (write-stv-1 0 (stvl st-vals) st-vals channel state)
          (princ$ #\) channel state)
          (newline channel state)))

(defun write-Abr-to-file (filename shortp Abr rtime rec st-vals state)
  (declare (xargs :stobjs (Abr rtime rec st-vals state)
                  :guard (stringp filename)
                  :mode :program))
  (mv-let
    (channel state)
    (open-output-channel filename :character state)
    (cond ((null channel) ; open failed (e.g., read-only directory)
           (prog2$ (cw "write-Abr-to-file: unable to open file for output: ~x0.~%"
                       filename)
                   (mv Abr rtime rec st-vals state)))
          (t (pprogn
              ;; Abr STOBJ
              (fms ";dim-Abr:~|~y0"
                   (list (cons #\0 (dim-Abr Abr)))
                   channel state nil)
              (fms ";b-sym:~|~y0"
                   (list (cons #\0 (b-sym Abr)))
                   channel state nil)
              (fms ";b-sym-fold:~|~y0"
                   (list (cons #\0 (b-sym-fold Abr)))
                   channel state nil)
              (fms ";b-sym-fold-to-stv:~|~y0"
                   (list (cons #\0 (b-sym-fold-to-stv Abr)))
                   channel state nil)
              (fms ";A-sym:~|~y0"
                   (list (cons #\0 (A-sym Abr)))
                   channel state nil)
              (fms ";A-sym-fold:~|~y0"
                   (list (cons #\0 (A-sym-fold Abr)))
                   channel state nil)
              (fms ";A-sym-fold-to-stv:~|~y0"
                   (list (cons #\0 (A-sym-fold-to-stv Abr)))
                   channel state nil)
              (fms ";A-num:~|~y0"
                   (list (cons #\0 (A-num Abr)))
                   channel state nil)
              (fms ";flat-occs:~|~y0"
                   (list (cons #\0 (flat-occs Abr)))
                   channel state nil)
              (fms ";ref-node:~|~y0"
                   (list (cons #\0 (ref-node Abr)))
                   channel state nil)
              (fms ";time-start:~|~y0"
                   (list (cons #\0 (time-start Abr)))
                   channel state nil)
              (fms ";hn:~|~y0"
                   (list (cons #\0 (hn Abr)))
                   channel state nil)
              (fms ";time-stop:~|~y0"
                   (list (cons #\0 (time-stop Abr)))
                   channel state nil)
              (fms ";sim-type:~|~y0"
                   (list (cons #\0 (sim-type Abr)))
                   channel state nil)
              (fms ";equations:~|~y0"
                   (list (cons #\0 (equations Abr)))
                   channel state nil)
              (fms ";alter-values-alist:~|~y0"
                   (list (cons #\0 (alter-values-alist Abr)))
                   channel state nil)
              (fms ";hrchl-netlist:~|~y0"
                   (list (cons #\0 (hrchl-netlist Abr)))
                   channel state nil)
              (fms ";x-names:~|~y0"
                   (list (cons #\0 (x-names Abr)))
                   channel state nil)
              (fms ";dp-x-names:~|~y0"
                   (list (cons #\0 (dp-x-names Abr)))
                   channel state nil)
              ;; should we save this value?
              (fms ";load-sim:~|~y0"
                   (list (cons #\0 (load-sim Abr)))
                   channel state nil)
              (fms ";prints:~|~y0"
                   (list (cons #\0 (prints Abr)))
                   channel state nil)
              (fms ";cir-concat-char:~|~y0"
                   (list (cons #\0 (cir-concat-char Abr)))
                   channel state nil)
              (fms ";vw-concat-char:~|~y0"
                   (list (cons #\0 (vw-concat-char Abr)))
                   channel state nil)
              (fms ";current-time:~|~y0"
                   (list (cons #\0 (current-time Abr)))
                   channel state nil)
              (fms ";all-rec-names:~|~y0"
                   (list (cons #\0 (all-rec-names Abr)))
                   channel state nil)
              (fms ";subterms-to-stv-alist:~|~y0"
                   (list (cons #\0 (subterms-to-stv-alist Abr)))
                   channel state nil)
              (fms ";all-stv-subterms:~|~y0"
                   (list (cons #\0 (all-stv-subterms Abr)))
                   channel state nil)
              (fms ";x-names-offset:~|~y0"
                   (list (cons #\0 (x-names-offset Abr)))
                   channel state nil)
              (fms ";dp-x-names-offset:~|~y0"
                   (list (cons #\0 (dp-x-names-offset Abr)))
                   channel state nil)
              (fms ";ref-node-offset:~|~y0"
                   (list (cons #\0 (ref-node-offset Abr)))
                   channel state nil)
              (fms ";dp-ref-node-offset:~|~y0"
                   (list (cons #\0 (dp-ref-node-offset Abr)))
                   channel state nil)
              ;; Other STOBJs
              (fms ";rtime STOBJ:~|~y0"
                   (list (cons #\0 (output-rtime rtime)))
                   channel state nil)
              (fms ";rec STOBJ:~|~y0"
; Warning: Do not change this call without considering the call of search in
; read-rec-ar.
                   (list (cons #\0 (arl rec))) channel state nil)
              (time$ (write-rec-ar rec shortp channel state))
              (fms ";st-vals STOBJ values:~|~y0"
                   (list (cons #\0 (stvl st-vals))) channel state nil)
              (write-stv st-vals channel state)
              (close-output-channel channel state)
              (mv Abr rtime rec st-vals state))))))

(defun read-dim-Abr (channel Abr state)
  (declare (xargs :mode :program
                  :stobjs (Abr state)))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-dim-Abr
                      "Unable to read dim-Abr from file (presumably ~
                      end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!dim-Abr obj Abr)))
               (mv nil Abr state))))))

(defun read-b-sym (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-b-sym
                      "Unable to read b-sym from file (presumably end ~
                      of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!b-sym obj Abr)))
               (mv nil Abr state))))))

(defun read-b-sym-fold (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-b-sym-fold
                      "Unable to read b-sym-fold from file (presumably end ~
                      of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!b-sym-fold obj Abr)))
               (mv nil Abr state))))))

(defun read-b-sym-fold-to-stv (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-b-sym-fold-to-stv
                      "Unable to read b-sym-fold-to-stv from file (presumably end ~
                      of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!b-sym-fold-to-stv obj Abr)))
               (mv nil Abr state))))))

(defun read-A-sym (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-A-sym
                      "Unable to read A-sym from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!A-sym obj Abr)))
               (mv nil Abr state))))))

(defun read-A-sym-fold (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-A-sym-fold
                      "Unable to read A-sym-fold from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!A-sym-fold obj Abr)))
               (mv nil Abr state))))))

(defun read-A-sym-fold-to-stv (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-A-sym-fold-to-stv
                      "Unable to read A-sym-fold-to-stv from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!A-sym-fold-to-stv obj Abr)))
               (mv nil Abr state))))))

(defun read-A-num (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-A-num
                      "Unable to read A-num from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!A-num obj Abr)))
               (mv nil Abr state))))))

(defun read-flat-occs (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-flat-occs
                      "Unable to read flat-occs from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!flat-occs obj Abr)))
               (mv nil Abr state))))))

(defun read-ref-node (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-ref-node
                      "Unable to read ref-node from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!ref-node obj Abr)))
               (mv nil Abr state))))))

(defun read-time-start (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-time-start
                      "Unable to read time-start from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!time-start obj Abr)))
               (mv nil Abr state))))))

(defun read-hn (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-hn
                      "Unable to read hn from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!hn obj Abr)))
               (mv nil Abr state))))))

(defun read-time-stop (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-time-stop
                      "Unable to read time-stop from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!time-stop obj Abr)))
               (mv nil Abr state))))))

(defun read-sim-type (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-sim-type
                      "Unable to read sim-type from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!sim-type obj Abr)))
               (mv nil Abr state))))))

(defun read-equations (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-equations
                      "Unable to read equations from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!equations obj Abr)))
               (mv nil Abr state))))))

(defun read-alter-values-alist (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-alter-values-alist
                      "Unable to read alter-values-alist from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!alter-values-alist obj Abr)))
               (mv nil Abr state))))))

(defun read-hrchl-netlist (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-hrchl-netlist
                      "Unable to read hrchl-netlist from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!hrchl-netlist obj Abr)))
               (mv nil Abr state))))))

(defun read-x-names (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-x-names
                      "Unable to read x-names from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!x-names obj Abr)))
               (mv nil Abr state))))))

(defun read-dp-x-names (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-dp-x-names
                      "Unable to read dp-x-names from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!dp-x-names obj Abr)))
               (mv nil Abr state))))))

(defun read-load-sim (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-load-sim
                      "Unable to read load-sim from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!load-sim obj Abr)))
               (mv nil Abr state))))))

(defun read-prints (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-prints
                      "Unable to read prints from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!prints obj Abr)))
               (mv nil Abr state))))))

(defun read-cir-concat-char (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-cir-concat-char
                      "Unable to read cir-concat-char from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!cir-concat-char obj Abr)))
               (mv nil Abr state))))))

(defun read-vw-concat-char (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-vw-concat-char
                      "Unable to read vw-concat-char from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!vw-concat-char obj Abr)))
               (mv nil Abr state))))))

(defun read-current-time (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-current-time
                      "Unable to read current-time from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!current-time obj Abr)))
               (mv nil Abr state))))))

(defun read-all-rec-names (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-all-rec-names
                      "Unable to read all-rec-names from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!all-rec-names obj Abr)))
               (mv nil Abr state))))))

(defun read-subterms-to-stv-alist (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-subterms-to-stv-alist
                      "Unable to read subterms-to-stv-alist from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!subterms-to-stv-alist obj Abr)))
               (mv nil Abr state))))))

(defun read-all-stv-subterms (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-all-stv-subterms
                      "Unable to read all-stv-subterms from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!all-stv-subterms obj Abr)))
               (mv nil Abr state))))))

(defun read-x-names-offset (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-x-names-offset
                      "Unable to read x-names-offset from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!x-names-offset obj Abr)))
               (mv nil Abr state))))))

(defun read-dp-x-names-offset (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-dp-x-names-offset
                      "Unable to read dp-x-names-offset from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!dp-x-names-offset obj Abr)))
               (mv nil Abr state))))))

(defun read-ref-node-offset (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-ref-node-offset
                      "Unable to read ref-node-offset from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!ref-node-offset obj Abr)))
               (mv nil Abr state))))))

(defun read-dp-ref-node-offset (channel Abr state)
  (declare (xargs :stobjs (Abr state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-dp-ref-node-offset
                      "Unable to read dp-ref-node-offset from file ~
                                  (presumably end of file)")
                  (declare (ignore erp val))
                  (mv t Abr state)))
          (t (let ((Abr (!dp-ref-node-offset obj Abr)))
               (mv nil Abr state))))))

(defun read-rtime (channel rtime state)
  (declare (xargs :stobjs (rtime state)
                  :mode :program))
  (mv-let (eofp obj state)
    (read-object channel state)
    (cond (eofp (mv-let (erp val state)
                  (er soft 'read-rtime
                      "Unable to read rtime STOBJ from file (presumably end ~
                       of file)")
                  (declare (ignore erp val))
                  (mv t rtime state)))
          ;; obj is an alist of symbol keys and list of numbers
          ;; values.
          ((not (and (consp obj)
                     (consp (cdr obj))
                     (null (cddr obj))
                     (rational-listp (car obj))
                     (rational-listp (cadr obj))
                     (pointwise-<= (cadr obj) (car obj))))
           (mv-let (erp val state)
             (er soft 'read-rtime
                 "Ill-formed object for rtime stobj:~|~x0"
                 obj)
             (declare (ignore erp val))
             (mv t rtime state)))
          (t (let ((rtime (init-rtime-with-lists (car obj) (cadr obj) rtime)))
               (mv nil rtime state))))))

#+(and rec-stobj rec-dcls (not simple-vectors))
(declaim (ftype (function ((unsigned-byte 60)
                           (unsigned-byte 60)
                           string
                           (simple-array double-float (*)))
                          (values (unsigned-byte 60)
                                  (simple-array double-float (*))))
                read-rec-ar-1))

(defun read-rec-ar-1 (pos count str rec)
; Keep this in sync with read-stv-1.
  (declare #+raw (type (simple-array double-float (*)) rec)
           (type string str)
           (type (unsigned-byte 60) pos count)
           (xargs :stobjs (rec)
                  :mode :program))
  (b* (((the character c)
        (the character (char str pos)))
       ((when (eql c #\)))
        (mv pos rec))
       ((mv (the (unsigned-byte 60) pos)
            #-raw val #+raw (the double-float val))
        (read-float pos str))
       (#-raw
        rec
        #+raw
        (the (simple-array double-float (*)) rec)

; Comment from Matt K.: I tried replacing (update-rec-ari count val rec) with
; its macroexpansion, but deleting the top-level binding (rec rec) in the hopes
; that the lack of a subsidiary type declaration for rec was slowing things
; down.  But that didn't seem to make a difference.

        (update-rec-ari count val rec)))
    (read-rec-ar-1 pos (the (unsigned-byte 60) (1+ count)) str rec)))

#+(and rec-stobj rec-dcls (not simple-vectors))
(declaim (ftype (function (string string
                                  (simple-array double-float (*)))
                          (values (unsigned-byte 60)
                                  (simple-array double-float (*))))
                read-rec-ar))

(defun read-rec-ar (filename str rec)
; Keep this in sync with read-stv.
  (declare (type string filename str)
           #+raw (type (simple-array double-float (*)) rec)
           (xargs :stobjs (rec)
                  :mode :program))
  (b* (((when (null str))
        (prog2$ (er hard 'read-rec-ar
                    "Unable to read rec STOBJ from file ~x0 (perhaps end of ~
                     file)"
                    filename)
                (mv 0 rec)))
       (pos (search ";rec STOBJ" str))
       (pos (and pos (search *newline-string* str :start2 pos)))
       ((when (null pos))
        (prog2$ (er hard 'read-rec-ar
                    "Unable to find the string ~x0 followed by a newline in ~
                     file ~x1"
                    ";rec STOBJ"
                    filename)
                (mv 0 rec)))
       (pos (1+ pos)) ; step past newline
       ((mv pos arl) (read-nat pos str 0))
;      (- (cw "~%arl = ~x0~%" arl))
       (pos (1+ pos)) ; step past newline
       (len (length str))
       ((when (= pos len))
        (prog2$ (er hard 'read-rec-ar
                    "Premature end of file (expected #\\( ) in ~x0"
                    filename)
                (mv pos rec)))
       ((when (not (eql (char str pos) #\()))
        (prog2$ (er hard 'read-rec-ar
                    "Unexpected first character ~x0 at position ~x1 after ~
                     \";rec STOBJ\" and the following newline -- expected ~
                     #\\( -- in file ~x2."
                    (char str pos)
                    pos
                    filename)
                (mv pos rec)))
       (pos (1+ pos)) ; step past left parenthesis
       (#-raw rec #+raw (the (simple-array double-float (*)) rec)
        (resize-rec-ar arl rec))
       ((mv pos
            #-raw rec #+raw (the (simple-array double-float (*)) rec))
        (read-rec-ar-1 pos 0 str rec)))
    (mv pos rec)))

#+(and rec-stobj rec-dcls (not simple-vectors))
(declaim (ftype (function ((unsigned-byte 60)
                           (unsigned-byte 60)
                           string
                           (simple-array double-float (*)))
                          (values (simple-array double-float (*))))
                read-stv-1))

(defun read-stv-1 (pos count str st-vals)
; Keep this in sync with read-rec-ar-1.
  (declare #+raw (type (simple-array double-float (*)) st-vals)
           (type string str)
           (type (unsigned-byte 60) pos count)
           (xargs :stobjs (st-vals)
                  :mode :program))
  (b* (((the character c)
        (the character (char str pos)))
       ((when (eql c #\)))
        st-vals)
       ((mv (the (unsigned-byte 60) pos)
            #-raw val #+raw (the double-float val))
        (read-float pos str))
       (#-raw
        st-vals 
        #+raw
        (the (simple-array double-float (*)) st-vals)
        (!stvi count val st-vals)))
    (read-stv-1 pos (the (unsigned-byte 60) (1+ count)) str st-vals)))

#+(and stv-stobj stv-dcls (not simple-vectors))
(declaim (ftype (function ((unsigned-byte 60)
                           string
                           string
                           (simple-array double-float (*)))
                          (values (simple-array double-float (*))))
                read-stv))

(defun read-stv (pos filename str st-vals)
; Keep this in sync with read-rec-ar.
  (declare (xargs :stobjs (st-vals)
                  :mode :program)
           #+raw (type (simple-array double-float (*)) st-vals))
  (b* ((pos (search ";st-vals STOBJ" str :start2 pos))
       (pos (and pos (search *newline-string* str :start2 pos)))
       ((when (null pos))
        (prog2$ (er hard 'read-stv
                    "Unable to find the string ~x0 followed by a newline in ~
                     file ~x1"
                    ";st-vals STOBJ"
                    filename)
                st-vals))
       (pos (1+ pos)) ; step past newline
       ((mv pos stvl) (read-nat pos str 0))
       (pos (1+ pos)) ; step past newline
       (len (length str))
       ((when (= pos len))
        (prog2$ (er hard 'read-stv
                    "Premature end of file (expected #\\( ) in ~x0"
                    filename)
                st-vals))
       ((when (not (eql (char str pos) #\()))
        (prog2$ (er hard 'read-rec-ar
                    "Unexpected first character of line after \";st-vals ~
                     STOBJ\", ~x0 (expected #\\( ) in file ~x1."
                    (char str pos)
                    filename)
                st-vals))
       (pos (1+ pos)) ; step past left parenthesis
       (#-raw st-vals #+raw (the (simple-array double-float (*)) st-vals)
              (resize-stv stvl st-vals))
       (#-raw st-vals #+raw (the (simple-array double-float (*)) st-vals)
              (read-stv-1 pos 0 str st-vals)))
    st-vals))

(defun read-Abr-objects (channel filename Abr rtime rec st-vals state)
  (declare (xargs :stobjs (Abr rtime rec st-vals state)
                  :mode :program))
  (b* (((mv ?flg Abr state) (read-dim-Abr channel Abr state))
       ((mv ?flg Abr state) (read-b-sym channel Abr state))
       ((mv ?flg Abr state) (read-b-sym-fold channel Abr state))
       ((mv ?flg Abr state) (read-b-sym-fold-to-stv channel Abr state))
       ((mv ?flg Abr state) (read-A-sym channel Abr state))
       ((mv ?flg Abr state) (read-A-sym-fold channel Abr state))
       ((mv ?flg Abr state) (read-A-sym-fold-to-stv channel Abr state))
       ((mv ?flg Abr state) (read-A-num channel Abr state))
       ((mv ?flg Abr state) (read-flat-occs channel Abr state))
       ((mv ?flg Abr state) (read-ref-node channel Abr state))
       ((mv ?flg Abr state) (read-time-start channel Abr state))
       ((mv ?flg Abr state) (read-hn channel Abr state))
       ((mv ?flg Abr state) (read-time-stop channel Abr state))
       ((mv ?flg Abr state) (read-sim-type channel Abr state))
       ((mv ?flg Abr state) (read-equations channel Abr state))
       ((mv ?flg Abr state) (read-alter-values-alist channel Abr state))
       ((mv ?flg Abr state) (read-hrchl-netlist channel Abr state))
       ((mv ?flg Abr state) (read-x-names channel Abr state))
       ((mv ?flg Abr state) (read-dp-x-names channel Abr state))
       ((mv ?flg Abr state) (read-load-sim channel Abr state))
       ((mv ?flg Abr state) (read-prints channel Abr state))
       ((mv ?flg Abr state) (read-cir-concat-char channel Abr state))
       ((mv ?flg Abr state) (read-vw-concat-char channel Abr state))
       ((mv ?flg Abr state) (read-current-time channel Abr state))
       ((mv ?flg Abr state) (read-all-rec-names channel Abr state))
       ((mv ?flg Abr state) (read-subterms-to-stv-alist channel Abr state))
       ((mv ?flg Abr state) (read-all-stv-subterms channel Abr state))
       ((mv ?flg Abr state) (read-x-names-offset channel Abr state))
       ((mv ?flg Abr state) (read-dp-x-names-offset channel Abr state))
       ((mv ?flg Abr state) (read-ref-node-offset channel Abr state))
       ((mv ?flg Abr state) (read-dp-ref-node-offset channel Abr state))
       ((mv ?flg rtime state) (read-rtime channel rtime state))
       (str (read-file-into-string filename))
       ((mv pos rec) (read-rec-ar filename str rec))
       (st-vals (read-stv pos filename str st-vals)))
    (mv Abr rtime rec st-vals state)))

(defun load-Abr-from-file (filename Abr rtime rec st-vals state)
  (declare (xargs :stobjs (Abr rtime rec st-vals state)
                  :guard (stringp filename)
                  :mode :program))
  (mv-let
    (channel state)
    (open-input-channel filename :object state)
    (cond ((null channel) ; open failed (e.g., read-only directory)
           (mv-let (erp val state)
             (er soft 'load-Abr-from-file
                 "Unable to open file for input: ~x0"
                 filename)
             (declare (ignore erp val))
             (mv t Abr rtime rec st-vals state)))
          (t (b* (((mv Abr rtime rec st-vals state)
                   (read-Abr-objects channel filename Abr rtime rec st-vals
                                     state))
                  (state (close-input-channel channel state)))
               (mv t Abr rtime rec st-vals state))))))

