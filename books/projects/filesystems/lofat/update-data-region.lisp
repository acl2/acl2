(in-package "ACL2")

;  update-data-region.lisp                              Mihir Mehta

; This is optimised code for updating the data region from a string, along with
; necessary basic definitions.

(include-book "fat32-in-memory")
(include-book "../utilities/cluster-listp")
(include-book "../utilities/member-intersectp")

(local (include-book "rtl/rel9/arithmetic/top" :dir :system))

;; These are some rules from other books which are either interacting badly
;; with the theory I've built up so far, or else causing a lot of unnecessary
;; frames and tries.
(local
 (in-theory (disable take-of-too-many make-list-ac-removal
                     revappend-removal)))

(local
 (in-theory (disable read-file-into-string1 nth update-nth ceiling floor
                     mod true-listp)))

(defund
  cluster-size (fat32$c)
  (declare (xargs :stobjs fat32$c
                  :guard (fat32$c-p fat32$c)))
  (mbe :exec (* (bpb_secperclus fat32$c)
                (bpb_bytspersec fat32$c))
       :logic (nfix (* (bpb_secperclus fat32$c)
                       (bpb_bytspersec fat32$c)))))

(defthm natp-of-cluster-size
  (implies (fat32$c-p fat32$c)
           (natp (cluster-size fat32$c)))
  :hints (("goal" :in-theory (enable fat32$c-p cluster-size
                                     bpb_bytspersec bpb_secperclus)))
  :rule-classes ((:rewrite
                  :corollary
                  (implies (fat32$c-p fat32$c)
                           (integerp (cluster-size fat32$c))))
                 (:rewrite
                  :corollary
                  (implies (fat32$c-p fat32$c)
                           (rationalp (cluster-size fat32$c))))
                 (:linear
                  :corollary
                  (implies (fat32$c-p fat32$c)
                           (<= 0 (cluster-size fat32$c))))
                 (:rewrite
                  :corollary
                  (implies (fat32$c-p fat32$c)
                           (equal
                           (nfix (cluster-size fat32$c))
                           (cluster-size fat32$c))))))

(defthm
  cluster-size-of-update-nth
  (implies
   (not (member-equal key
                      (list *bpb_secperclus* *bpb_bytspersec*)))
   (equal (cluster-size (update-nth key val fat32$c))
          (cluster-size fat32$c)))
  :hints (("goal" :in-theory (enable cluster-size))))

(defthm
  cluster-size-of-resize-data-region
  (equal (cluster-size (resize-data-region i fat32$c))
         (cluster-size fat32$c))
  :hints (("goal" :in-theory (enable resize-data-region))))

(defthm
  cluster-size-of-resize-fat
  (equal (cluster-size (resize-fat i fat32$c))
         (cluster-size fat32$c))
  :hints (("goal" :in-theory (enable resize-fat))))

(defund
  count-of-clusters (fat32$c)
  (declare
   (xargs :stobjs fat32$c
          :guard (and (fat32$c-p fat32$c)
                      (>= (bpb_secperclus fat32$c) 1))
          :guard-debug t))
  (floor (- (bpb_totsec32 fat32$c)
            (+ (bpb_rsvdseccnt fat32$c)
               (* (bpb_numfats fat32$c)
                  (bpb_fatsz32 fat32$c))))
         (bpb_secperclus fat32$c)))

(defthm
  count-of-clusters-of-resize-fat
  (equal (count-of-clusters (resize-fat i fat32$c))
         (count-of-clusters fat32$c))
  :hints (("goal" :in-theory (enable count-of-clusters))))

(defthm
  count-of-clusters-of-update-nth
  (implies
   (not (member key
                (list *bpb_totsec32*
                      *bpb_rsvdseccnt* *bpb_numfats*
                      *bpb_fatsz32* *bpb_secperclus*)))
   (equal
    (count-of-clusters (update-nth key val fat32$c))
    (count-of-clusters fat32$c)))
  :hints (("goal" :in-theory (enable count-of-clusters))))

(defthm
  count-of-clusters-of-update-data-regioni
  (equal
   (count-of-clusters (update-data-regioni i v fat32$c))
   (count-of-clusters fat32$c))
  :hints
  (("goal"
    :in-theory (enable update-data-regioni))))

(defun
  stobj-cluster-listp-helper
  (fat32$c n)
  (declare
   (xargs
    :stobjs fat32$c
    :guard (and (fat32$c-p fat32$c)
                (natp n)
                (<= n (data-region-length fat32$c)))
    :guard-hints
    (("goal" :in-theory (disable fat32$c-p)))))
  (or
   (zp n)
   (let
    ((current-cluster
      (data-regioni (- (data-region-length fat32$c)
                       n)
                    fat32$c)))
    (and
     (cluster-p current-cluster
                (cluster-size fat32$c))
     (stobj-cluster-listp-helper fat32$c (- n 1))))))

(defthm
  stobj-cluster-listp-helper-correctness-1
  (implies
   (and (natp n)
        (<= n (data-region-length fat32$c)))
   (equal
    (stobj-cluster-listp-helper fat32$c n)
    (cluster-listp
     (nthcdr
      (- (data-region-length fat32$c)
         n)
      (true-list-fix (nth *data-regioni* fat32$c)))
     (cluster-size fat32$c))))
  :hints
  (("goal"
    :in-theory (e/d (data-regioni data-region-length
                                  nth)
                    ;; Try disabling rules until the proof works again...
                    ((:rewrite a1)
                     (:rewrite a2)
                     (:rewrite a4)
                     (:rewrite a9)))
    :induct (stobj-cluster-listp-helper fat32$c n)
    :expand
    ((true-list-fix (nth *data-regioni* fat32$c))
     (cluster-listp
      (nthcdr
       (+ (- n)
          (len (nth *data-regioni* fat32$c)))
       (true-list-fix (nth *data-regioni* fat32$c)))
      (cluster-size fat32$c))
     (cluster-listp
      (nthcdr
       (+ (- n)
          (len (cdr (nth *data-regioni* fat32$c))))
       (true-list-fix
        (cdr (nth *data-regioni* fat32$c))))
      (cluster-size fat32$c)))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (natp n)
          (<= n (data-region-length fat32$c))
          (fat32$c-p fat32$c))
     (equal (stobj-cluster-listp-helper fat32$c n)
            (cluster-listp
             (nthcdr (- (data-region-length fat32$c)
                        n)
                     (nth *data-regioni* fat32$c))
             (cluster-size fat32$c))))
    :hints (("goal" :in-theory (enable fat32$c-p))))))

(defund
  fat-entry-count (fat32$c)
  (declare (xargs :guard (fat32$c-p fat32$c)
                  :stobjs fat32$c))
  (floor (* (bpb_fatsz32 fat32$c)
            (bpb_bytspersec fat32$c))
         4))

(defthm
  fat-entry-count-of-update-nth
  (implies
   (not (member-equal key
                      (list *bpb_fatsz32* *bpb_bytspersec*)))
   (equal (fat-entry-count (update-nth key val fat32$c))
          (fat-entry-count fat32$c)))
  :hints
  (("goal" :in-theory (enable fat-entry-count
                              bpb_bytspersec bpb_fatsz32))))

(defthm
  fat-entry-count-of-resize-data-region
  (equal (fat-entry-count
          (resize-data-region i fat32$c))
         (fat-entry-count fat32$c))
  :hints (("goal" :in-theory (enable resize-data-region))))

(defthm
  fat32-entry-p-of-bpb_rootclus-when-fat32$c-p
  (implies (fat32$c-p fat32$c)
           (fat32-entry-p (bpb_rootclus fat32$c)))
  :hints (("goal" :in-theory (enable fat32-entry-p))))

(defthm
  fat-entry-count-of-update-fati
  (equal (fat-entry-count (update-fati i v fat32$c))
         (fat-entry-count fat32$c))
  :hints
  (("goal" :in-theory (enable fat-entry-count update-fati))))

(encapsulate
  ()

  ;; Trying to remove this is hazardous, even though it doesn't seem to be used
  ;; anywhere!
  (local
   (defthm
     lemma-1
     (implies (and
               (fat32$c-p fat32$c)
               (>= (bpb_bytspersec fat32$c) *ms-min-bytes-per-sector*)
               (>= (bpb_secperclus fat32$c) 1))
              (not (equal (cluster-size fat32$c)
                          0)))
     :hints (("goal" :in-theory (enable cluster-size)))))

  (defund lofat-fs-p (fat32$c)
    (declare (xargs :stobjs fat32$c :guard t))
    (and (fat32$c-p fat32$c)
         (>= (bpb_bytspersec fat32$c)
             *ms-min-bytes-per-sector*)
         (>= (bpb_secperclus fat32$c) 1)
         (>= (count-of-clusters fat32$c)
             *ms-min-count-of-clusters*)
         (<= (+ *ms-first-data-cluster*
                (count-of-clusters fat32$c))
             *ms-bad-cluster*)
         (>= (bpb_rsvdseccnt fat32$c) 1)
         (>= (bpb_numfats fat32$c) 1)
         (>= (bpb_fatsz32 fat32$c) 1)
         ;; These constraints on bpb_rootclus aren't in the spec, but they are
         ;; clearly implied
         (>= (fat32-entry-mask (bpb_rootclus fat32$c))
             *ms-first-data-cluster*)
         (< (fat32-entry-mask (bpb_rootclus fat32$c))
            (+ *ms-first-data-cluster*
               (count-of-clusters fat32$c)))
         (<= (+ (count-of-clusters fat32$c)
                *ms-first-data-cluster*)
             (fat-entry-count fat32$c))
         ;; The spec (page 9) imposes both hard and soft limits on the legal
         ;; values of the cluster size, limiting it to being a power of 2 from
         ;; 512 through 32768. The following two clauses, however, are less
         ;; stringent - they allow values of cluster size which are powers of 2
         ;; going up to 2097152, although the lower bound of 512 is retained
         ;; thanks to the lower bounds on bpb_bytspersec and bpb_secperclus
         ;; above.
         (equal (mod (cluster-size fat32$c)
                     *ms-d-e-length*)
                0)
         (equal (mod *ms-max-dir-size*
                     (cluster-size fat32$c))
                0)
         ;; Some array properties in addition to the scalar properties
         (stobj-cluster-listp-helper
          fat32$c
          (data-region-length fat32$c))
         (equal (data-region-length fat32$c)
                (count-of-clusters fat32$c))
         (equal (* 4 (fat-length fat32$c))
                (* (bpb_fatsz32 fat32$c)
                   (bpb_bytspersec fat32$c)))))

  (local
   (defthm
     lemma-2
     (implies (and (fat32$c-p fat32$c)
                   (< 0 (bpb_bytspersec fat32$c)))
              (< (fat-entry-count fat32$c)
                 (ash 1 48)))
     :rule-classes ()
     :hints (("goal"
              :do-not-induct t
              :in-theory
              (enable fat32$c-p fat-entry-count
                      bpb_bytspersec bpb_fatsz32)))))

  (defthm
    lofat-fs-p-correctness-1
    (implies (lofat-fs-p fat32$c)
             (and (fat32$c-p fat32$c)
                  (integerp (cluster-size fat32$c))
                  (>= (cluster-size fat32$c)
                      *ms-min-bytes-per-sector*)
                  (>= (count-of-clusters fat32$c)
                      *ms-min-count-of-clusters*)
                  (equal (mod (cluster-size fat32$c)
                              *ms-d-e-length*)
                         0)
                  (equal (mod *ms-max-dir-size*
                              (cluster-size fat32$c))
                         0)
                  (<= (+ *ms-first-data-cluster*
                         (count-of-clusters fat32$c))
                      *ms-bad-cluster*)
                  (>= (bpb_secperclus fat32$c) 1)
                  (>= (bpb_rsvdseccnt fat32$c) 1)
                  (>= (bpb_numfats fat32$c) 1)
                  (>= (bpb_fatsz32 fat32$c) 1)
                  (>= (fat32-entry-mask (bpb_rootclus fat32$c))
                      *ms-first-data-cluster*)
                  ;; There was a bug here, which we fixed - previously,
                  ;; bpb_rootclus was only allowed to point at clusters up to
                  ;; but not including (count-of-clusters fat32$c),
                  ;; which causes two clusters (up to but not including
                  ;; (+ 2 (count-of-clusters fat32$c))) to be left out.
                  (< (fat32-entry-mask (bpb_rootclus fat32$c))
                     (+ *ms-first-data-cluster*
                        (count-of-clusters fat32$c)))
                  (>= (bpb_bytspersec fat32$c)
                      *ms-min-bytes-per-sector*)
                  (equal (data-region-length fat32$c)
                         (count-of-clusters fat32$c))
                  (<= (+ (count-of-clusters fat32$c)
                         *ms-first-data-cluster*)
                      (fat-length fat32$c))
                  (equal (fat-length fat32$c)
                         (fat-entry-count fat32$c))
                  ;; This also represents a fixed bug - earlier, we were going
                  ;; to return an error for all filesystems with fat-length
                  ;; greater than *ms-bad-cluster*. The upper limit is actually
                  ;; (ash 1 28) - only slightly greater than *ms-bad-cluster* -
                  ;; derived from bpb_fatsz32 being up to (ash 1 16) and
                  ;; bpb_bytspersec being up to 4096.
                  (< (fat-entry-count fat32$c)
                     (ash 1 48))))
    :hints
    (("goal"
      :in-theory
      (e/d
       (lofat-fs-p cluster-size fat-entry-count)
       (fat32$c-p))
      :use
      lemma-2))
    :rule-classes
    ((:rewrite
      :corollary
      (implies (lofat-fs-p fat32$c)
               (and (fat32$c-p fat32$c)
                    (integerp (cluster-size fat32$c))
                    (equal (mod (cluster-size fat32$c)
                                *ms-d-e-length*)
                           0)
                    (equal (mod *ms-max-dir-size*
                                (cluster-size fat32$c))
                           0)
                    (equal (data-region-length fat32$c)
                           (count-of-clusters fat32$c))
                    (equal (fat-length fat32$c)
                           (fat-entry-count fat32$c)))))
     (:forward-chaining
      :corollary
      (implies (lofat-fs-p fat32$c)
               (integerp (cluster-size fat32$c))))
     (:linear
      :corollary
      (implies
       (lofat-fs-p fat32$c)
       (and (>= (cluster-size fat32$c)
                *ms-min-bytes-per-sector*)
            (>= (count-of-clusters fat32$c)
                *ms-min-count-of-clusters*)
            (<= (+ *ms-first-data-cluster*
                   (count-of-clusters fat32$c))
                *ms-bad-cluster*)
            (>= (bpb_secperclus fat32$c) 1)
            (>= (bpb_rsvdseccnt fat32$c) 1)
            (>= (bpb_numfats fat32$c) 1)
            (>= (bpb_fatsz32 fat32$c) 1)
            (>= (fat32-entry-mask (bpb_rootclus fat32$c))
                *ms-first-data-cluster*)
            (< (fat32-entry-mask (bpb_rootclus fat32$c))
               (+ *ms-first-data-cluster*
                  (count-of-clusters fat32$c)))
            (>= (bpb_bytspersec fat32$c)
                *ms-min-bytes-per-sector*)
            (>= (* (cluster-size fat32$c)
                   (count-of-clusters fat32$c))
                (* *ms-min-bytes-per-sector*
                   *ms-min-count-of-clusters*))
            (<= (+ (count-of-clusters fat32$c)
                   *ms-first-data-cluster*)
                (fat-entry-count fat32$c))
            (< (fat-entry-count fat32$c)
               (ash 1 48))))))))

(defthm
  fati-when-lofat-fs-p
  (implies (lofat-fs-p fat32$c)
           (equal (fat32-entry-p (fati i fat32$c))
                  (< (nfix i) (fat-length fat32$c))))
  :hints (("goal" :in-theory (enable lofat-fs-p fat32$c-p fati fat-length)))
  :rule-classes
  (:rewrite
   (:rewrite :corollary (implies (lofat-fs-p fat32$c)
                                 (equal (unsigned-byte-p 32 (fati i fat32$c))
                                        (< (nfix i) (fat-length fat32$c))))
             :hints (("goal" :do-not-induct t
                      :in-theory (enable fat32-entry-p))))))

(defthm
  cluster-size-of-update-fati
  (equal (cluster-size (update-fati i v fat32$c))
         (cluster-size fat32$c))
  :hints
  (("goal" :in-theory (enable cluster-size update-fati))))

(defthm
  count-of-clusters-of-update-fati
  (equal (count-of-clusters (update-fati i v fat32$c))
         (count-of-clusters fat32$c))
  :hints
  (("goal"
    :in-theory (enable count-of-clusters update-fati bpb_totsec32))))

;; After disabling, this function used to cause  9419883 frames and 76526
;; tries. So we went back to leaving it enabled and those numbers are now
;; 9446133 and 82621 respectively.
(defthm
  lofat-fs-p-of-update-fati
  (implies (and (lofat-fs-p fat32$c)
                (case-split (< i (fat-length fat32$c))))
           (equal (lofat-fs-p (update-fati i v fat32$c))
                  (fat32-entry-p v)))
  :hints
  (("goal"
    :in-theory
    '((:compound-recognizer natp-compound-recognizer)
      (:compound-recognizer true-listp-when-fat32-entry-list-p)
      (:definition bpb_bkbootsecp)
      (:definition bpb_bytspersecp)
      (:definition bpb_extflagsp)
      (:definition bpb_fatsz16p)
      (:definition bpb_fatsz32p)
      (:definition bpb_fsinfop)
      (:definition bpb_fsver_majorp)
      (:definition bpb_fsver_minorp)
      (:definition bpb_hiddsecp)
      (:definition bpb_mediap)
      (:definition bpb_numfatsp)
      (:definition bpb_numheadsp)
      (:definition bpb_reservedp-alt)
      (:definition bpb_rootclusp)
      (:definition bpb_rootentcntp)
      (:definition bpb_rsvdseccntp)
      (:definition bpb_secperclusp)
      (:definition bpb_secpertrkp)
      (:definition bpb_totsec16p)
      (:definition bpb_totsec32p)
      (:definition bs_bootsigp)
      (:definition bs_drvnump)
      (:definition bs_filsystypep-alt)
      (:definition bs_jmpbootp-alt)
      (:definition bs_oemnamep-alt)
      (:definition bs_reserved1p)
      (:definition bs_volidp)
      (:definition bs_vollabp-alt)
      (:definition count-of-clusters)
      (:definition data-region-length)
      (:definition data-regionp-alt)
      (:definition fat-length)
      (:definition fat32$c-p)
      (:definition fatp-alt)
      (:definition force)
      (:definition integer-range-p)
      (:definition length)
      (:definition lofat-fs-p)
      (:definition max)
      (:definition nfix)
      (:definition not)
      (:definition nthcdr)
      (:definition unsigned-byte-p)
      (:definition update-fati)
      (:definition update-nth-array)
      (:executable-counterpart binary-+)
      (:executable-counterpart equal)
      (:executable-counterpart expt)
      (:executable-counterpart integerp)
      (:executable-counterpart max)
      (:executable-counterpart member-equal)
      (:executable-counterpart nfix)
      (:executable-counterpart not)
      (:executable-counterpart zp)
      (:rewrite bpb_bytspersec-of-update-nth . 23)
      (:rewrite bpb_fatsz32-of-update-nth . 23)
      (:rewrite bpb_numfats-of-update-nth . 23)
      (:rewrite bpb_rootclus-of-update-nth . 23)
      (:rewrite bpb_rsvdseccnt-of-update-nth . 23)
      (:rewrite bpb_secperclus-of-update-nth . 23)
      (:rewrite cluster-size-of-update-nth)
      (:rewrite commutativity-2-of-+)
      (:rewrite commutativity-of-*)
      (:rewrite commutativity-of-+)
      (:rewrite count-of-clusters-of-update-nth)
      (:rewrite distributivity-of-minus-over-+)
      (:rewrite fat-entry-count-of-update-nth)
      (:rewrite fat32-entry-list-p-of-update-nth)
      (:rewrite inverse-of-+)
      (:rewrite len-update-nth)
      (:rewrite nth-update-nth)
      (:rewrite stobj-cluster-listp-helper-correctness-1)
      (:type-prescription cluster-listp)
      (:type-prescription count-of-clusters)
      (:type-prescription fat-entry-count)
      (:type-prescription fat32-entry-mask)
      (:type-prescription fat32-entry-p)
      (:type-prescription floor)
      (:type-prescription len)
      (:type-prescription string-listp)
      (:type-prescription true-listp-update-nth)
      (:type-prescription unsigned-byte-listp)
      (:type-prescription update-nth))
    :use cluster-size-of-update-fati)))

(defthm
  data-regioni-when-lofat-fs-p
  (implies (and (lofat-fs-p fat32$c)
                (< (nfix i)
                   (data-region-length fat32$c)))
           (cluster-p (data-regioni i fat32$c)
                      (cluster-size fat32$c)))
  :hints
  (("goal" :in-theory (e/d (lofat-fs-p
                            fat32$c-p
                            data-regioni data-region-length)
                           (unsigned-byte-p))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (lofat-fs-p fat32$c)
          (< (nfix i)
             (data-region-length fat32$c)))
     (and
      (stringp (data-regioni i fat32$c))
      (equal (len (explode (data-regioni i fat32$c)))
             (cluster-size fat32$c))))
    :hints (("goal" :in-theory (enable cluster-p))))))

(defthm
  cluster-size-of-update-data-regioni
  (equal
   (cluster-size (update-data-regioni i v fat32$c))
   (cluster-size fat32$c))
  :hints
  (("goal"
    :in-theory (enable cluster-size update-data-regioni))))

(defthm
  lofat-fs-p-of-update-data-regioni
  (implies
   (and (lofat-fs-p fat32$c)
        (< i (data-region-length fat32$c)))
   (equal (lofat-fs-p (update-data-regioni i v fat32$c))
          (cluster-p v (cluster-size fat32$c))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    '((:compound-recognizer natp-compound-recognizer)
      (:compound-recognizer true-listp-when-fat32-entry-list-p)
      (:definition bpb_bkbootsecp)
      (:definition bpb_bytspersecp)
      (:definition bpb_extflagsp)
      (:definition bpb_fatsz16p)
      (:definition bpb_fatsz32p)
      (:definition bpb_fsinfop)
      (:definition bpb_fsver_majorp)
      (:definition bpb_fsver_minorp)
      (:definition bpb_hiddsecp)
      (:definition bpb_mediap)
      (:definition bpb_numfatsp)
      (:definition bpb_numheadsp)
      (:definition bpb_reservedp-alt)
      (:definition bpb_rootclusp)
      (:definition bpb_rootentcntp)
      (:definition bpb_rsvdseccntp)
      (:definition bpb_secperclusp)
      (:definition bpb_secpertrkp)
      (:definition bpb_totsec16p)
      (:definition bpb_totsec32p)
      (:definition bs_bootsigp)
      (:definition bs_drvnump)
      (:definition bs_filsystypep-alt)
      (:definition bs_jmpbootp-alt)
      (:definition bs_oemnamep-alt)
      (:definition bs_reserved1p)
      (:definition bs_volidp)
      (:definition bs_vollabp-alt)
      (:definition count-of-clusters)
      (:definition data-region-length)
      (:definition data-regionp-alt)
      (:definition fat-length)
      (:definition fat32$c-p)
      (:definition fatp-alt)
      (:definition fix)
      (:definition integer-range-p)
      (:definition length)
      (:definition lofat-fs-p)
      (:definition max)
      (:definition nfix)
      (:definition not)
      (:definition nthcdr)
      (:definition unsigned-byte-p)
      (:definition update-data-regioni)
      (:definition update-nth-array)
      (:executable-counterpart binary-+)
      (:executable-counterpart equal)
      (:executable-counterpart expt)
      (:executable-counterpart integerp)
      (:executable-counterpart max)
      (:executable-counterpart member-equal)
      (:executable-counterpart nfix)
      (:executable-counterpart not)
      (:executable-counterpart unary--)
      (:executable-counterpart zp)
      (:rewrite bpb_bytspersec-of-update-nth . 23)
      (:rewrite bpb_fatsz32-of-update-nth . 23)
      (:rewrite bpb_numfats-of-update-nth . 23)
      (:rewrite bpb_rootclus-of-update-nth . 23)
      (:rewrite bpb_rsvdseccnt-of-update-nth . 23)
      (:rewrite bpb_secperclus-of-update-nth . 23)
      (:rewrite cluster-listp-of-update-nth)
      (:rewrite cluster-p-correctness-1)
      (:rewrite cluster-size-of-update-nth)
      (:rewrite commutativity-2-of-+)
      (:rewrite commutativity-of-*)
      (:rewrite commutativity-of-+)
      (:rewrite count-of-clusters-of-update-nth)
      (:rewrite distributivity-of-minus-over-+)
      (:rewrite fat-entry-count-of-update-nth)
      (:rewrite fat-length-of-update-nth)
      (:rewrite inverse-of-+)
      (:rewrite len-update-nth)
      (:rewrite nth-update-nth)
      (:rewrite nthcdr-of-update-nth)
      (:rewrite stobj-cluster-listp-helper-correctness-1)
      (:rewrite string-listp-of-update-nth)
      (:rewrite unicity-of-0)
      (:type-prescription cluster-listp)
      (:type-prescription cluster-p)
      (:type-prescription count-of-clusters)
      (:type-prescription fat-entry-count)
      (:type-prescription fat32-entry-mask)
      (:type-prescription floor)
      (:type-prescription len)
      (:type-prescription max)
      (:type-prescription string-listp)
      (:type-prescription true-listp-update-nth)
      (:type-prescription unsigned-byte-listp)
      (:type-prescription update-nth))
    :use cluster-size-of-update-data-regioni)))

(defun
    update-data-region
    (fat32$c str len)
  (declare
   (xargs
    :guard (and (stringp str)
                (natp len)
                (<= len
                    (data-region-length fat32$c))
                (>= (length str)
                    (* (- (data-region-length fat32$c)
                          len)
                       (cluster-size fat32$c)))
                (<= len
                    (- *ms-bad-cluster*
                       *ms-first-data-cluster*)))
    :stobjs fat32$c
    :measure (nfix len)))
  (b*
      ((len (the (unsigned-byte 28) len))
       ((when (zp len)) (mv fat32$c 0))
       (cluster-size (cluster-size fat32$c))
       (index (- (data-region-length fat32$c)
                 len)))
    (if
        (<= (* (+ index 1) cluster-size)
            (length str))
        (b*
            ((current-cluster (subseq str (* index cluster-size)
                                      (* (+ index 1) cluster-size)))
             (fat32$c
              (update-data-regioni
               index current-cluster fat32$c)))
          (update-data-region
           fat32$c
           str (the (unsigned-byte 28) (- len 1))))
      (b*
          ((current-cluster (subseq str (* index cluster-size) nil))
           (fat32$c
            (update-data-regioni
             index current-cluster fat32$c)))
        (mv fat32$c *eio*)))))

(defun
    update-data-region-from-disk-image
    (fat32$c len state tmp_init image-path)
  (declare
   (xargs
    :guard
    (and (natp tmp_init)
         (stringp image-path)
         (stringp (read-file-into-string image-path))
         (natp len)
         (<= len
             (data-region-length fat32$c))
         (>= (length (read-file-into-string image-path))
             (+ tmp_init
                (* (- (data-region-length fat32$c)
                      len)
                   (cluster-size fat32$c))))
         (<= len
             (- *ms-bad-cluster*
                *ms-first-data-cluster*)))
    :stobjs (fat32$c state)
    :measure (nfix len)))
  (b*
      ((len (the (unsigned-byte 28) len))
       ((when (zp len)) (mv fat32$c 0))
       (cluster-size (cluster-size fat32$c))
       (index (- (data-region-length fat32$c)
                 len))
       (fat32$c
        (update-data-regioni
         index
         (read-file-into-string
          image-path
          :start (+ tmp_init (* index cluster-size))
          :bytes cluster-size)
         fat32$c)))
    (if (equal (length (data-regioni index fat32$c))
               cluster-size)
        (update-data-region-from-disk-image
         fat32$c
         (the (unsigned-byte 28) (- len 1))
         state tmp_init image-path)
      (mv fat32$c *eio*))))

(defthm
  update-data-region-from-disk-image-correctness-1
  (implies
   (and (natp tmp_init)
        (<= len
            (data-region-length fat32$c))
        (>= (length (read-file-into-string image-path))
            (+ tmp_init
               (* (- (data-region-length fat32$c)
                     len)
                  (cluster-size fat32$c))))
        (not (zp (cluster-size fat32$c))))
   (equal (update-data-region-from-disk-image fat32$c
                                              len state tmp_init image-path)
          (update-data-region fat32$c
                              (subseq (read-file-into-string image-path)
                                      tmp_init nil)
                              len)))
  :hints
  (("goal"
    :induct (update-data-region-from-disk-image fat32$c
                                                len state tmp_init image-path)
    :in-theory (enable take-of-nthcdr)
    :expand (:free (fat32$c str)
                   (update-data-region fat32$c str len)))))

(defthm
  fat32$c-p-of-update-data-regioni
  (implies
   (fat32$c-p fat32$c)
   (equal
    (fat32$c-p (update-data-regioni i v fat32$c))
    (and (stringp v)
         (<= (nfix i)
             (data-region-length fat32$c)))))
  :hints
  (("goal"
    :in-theory (enable fat32$c-p update-data-regioni
                       data-region-length))))

(defthm
  fat32$c-p-of-update-data-region
  (implies (and (fat32$c-p fat32$c)
                (stringp str))
           (fat32$c-p
            (mv-nth 0
                    (update-data-region fat32$c str len)))))

(defthm
  bpb_bytspersec-of-update-data-region
  (equal
   (bpb_bytspersec (mv-nth 0 (update-data-region fat32$c str len)))
   (bpb_bytspersec fat32$c)))

(defthm
  bpb_secperclus-of-update-data-region
  (equal
   (bpb_secperclus (mv-nth 0 (update-data-region fat32$c str len)))
   (bpb_secperclus fat32$c)))

(defthm
  bpb_rsvdseccnt-of-update-data-region
  (equal
   (bpb_rsvdseccnt (mv-nth 0 (update-data-region fat32$c str len)))
   (bpb_rsvdseccnt fat32$c)))

(defthm
  bpb_totsec32-of-update-data-region
  (equal
   (bpb_totsec32 (mv-nth 0 (update-data-region fat32$c str len)))
   (bpb_totsec32 fat32$c)))

(defthm
  bpb_fatsz32-of-update-data-region
  (equal
   (bpb_fatsz32 (mv-nth 0 (update-data-region fat32$c str len)))
   (bpb_fatsz32 fat32$c)))

(defthm
  bpb_numfats-of-update-data-region
  (equal
   (bpb_numfats (mv-nth 0 (update-data-region fat32$c str len)))
   (bpb_numfats fat32$c)))

(defthm
  bpb_rootclus-of-update-data-region
  (equal
   (bpb_rootclus (mv-nth 0 (update-data-region fat32$c str len)))
   (bpb_rootclus fat32$c)))

(defthm
  fat-length-of-update-data-region
  (equal
   (fat-length (mv-nth 0 (update-data-region fat32$c str len)))
   (fat-length fat32$c)))

(defthm
  fat-entry-count-of-update-data-region
  (equal (fat-entry-count
          (mv-nth 0 (update-data-region fat32$c str len)))
         (fat-entry-count fat32$c))
  :hints (("goal" :in-theory (enable fat-entry-count))))

(defthm
  data-region-length-of-update-data-region
  (implies
   (<= len
       (data-region-length fat32$c))
   (equal (data-region-length
           (mv-nth 0 (update-data-region fat32$c str len)))
          (data-region-length fat32$c)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (<= len
         (data-region-length fat32$c))
     (equal
      (consp (nth *data-regioni*
                  (mv-nth 0 (update-data-region fat32$c str len))))
      (consp (nth *data-regioni* fat32$c))))
    :hints
    (("goal"
      :in-theory (enable data-region-length)
      :do-not-induct t
      :expand
      ((len (nth *data-regioni*
                 (mv-nth 0 (update-data-region fat32$c str len))))
       (len (nth *data-regioni* fat32$c))))))))

(defthmd
  update-data-region-correctness-2
  (equal
   (update-data-region fat32$c str len)
   (mv (mv-nth 0
               (update-data-region fat32$c str len))
       (mv-nth 1
               (update-data-region fat32$c str len)))))

(local
 (defthm
   update-data-region-correctness-1-lemma-1
   (implies (and (not (zp len))
                 (<= (* cluster-size
                        data-region-length)
                     (+ length-str
                        (* len cluster-size)))
                 (< (+ length-str
                       (* len cluster-size))
                    (+ cluster-size
                       (* cluster-size
                          data-region-length))))
            (< length-str
               (* cluster-size
                  data-region-length)))
   :hints (("goal" :in-theory (disable (:rewrite product-less-than-zero))
            :use ((:instance (:rewrite product-less-than-zero)
                             (y cluster-size)
                             (x (+ -1 len))))))))

;; It would be nice to make this a rule that just rewrites the inner (mv-nth
;; 1 ...) subexpression rather than the (equal (mv-nth 1 ...) ...)
;; expression, but that causes trouble with
;; string-to-lofat-ignore-lemma-14 in another book.
(defthm
  update-data-region-correctness-1
  (implies (and (natp len)
                (<= len
                    (data-region-length fat32$c))
                (>= (length str)
                    (* (- (data-region-length fat32$c)
                          len)
                       (cluster-size fat32$c))))
           (iff
            (equal (mv-nth 1
                           (update-data-region fat32$c str len))
                   0)
            (>= (length str)
                (* (data-region-length fat32$c)
                   (cluster-size fat32$c))))))

(encapsulate
  ()

  (local
   (defthm
     update-data-region-alt-lemma-1
     (equal (update-nth *data-regioni* val
                        (update-data-regioni i v fat32$c))
            (update-nth *data-regioni* val fat32$c))
     :hints (("goal" :in-theory (enable update-data-regioni)))))

  (local
   (defthm
     update-data-region-alt-lemma-2
     (implies (fat32$c-p fat32$c)
              (and
               (true-listp (nth *data-regioni* fat32$c))
               (equal
                (update-nth *data-regioni*
                            (nth *data-regioni* fat32$c)
                            fat32$c)
                fat32$c)))
     :hints (("goal" :in-theory (enable fat32$c-p)))))

  (local
   (defthm
     update-data-region-alt-lemma-3
     (equal
      (nth *data-regioni*
           (update-data-regioni i v fat32$c))
      (update-nth i v
                  (nth *data-regioni* fat32$c)))
     :hints (("goal" :in-theory (enable update-data-regioni)) )))

  (defthm
    update-data-region-alt-lemma-4
    (implies (and (not (zp len))
                  (< (len (explode str))
                     (+ (cluster-size fat32$c)
                        (* -1 len (cluster-size fat32$c))
                        (* (cluster-size fat32$c)
                           (len (nth *data-regioni* fat32$c)))))
                  (fat32$c-p fat32$c))
             (< (len (explode str))
                (* (cluster-size fat32$c)
                   (len (nth *data-regioni* fat32$c)))))
    :hints (("goal" :cases ((<= (+ (cluster-size fat32$c)
                                   (* -1 len (cluster-size fat32$c)))
                                0)))))

  (defthmd
    update-data-region-alt
    (implies
     (and (stringp str)
          (natp len)
          (>= (data-region-length fat32$c)
              len)
          (fat32$c-p fat32$c)
          (< 0 (cluster-size fat32$c))
          (>= (length str)
              (* (data-region-length fat32$c)
                 (cluster-size fat32$c))))
     (equal
      (update-data-region fat32$c str len)
      (mv
       (update-nth
        *data-regioni*
        (append
         (take (- (data-region-length fat32$c)
                  len)
               (nth *data-regioni* fat32$c))
         (make-clusters
          (subseq str
                  (* (- (data-region-length fat32$c)
                        len)
                     (cluster-size fat32$c))
                  (* (data-region-length fat32$c)
                     (cluster-size fat32$c)))
          (cluster-size fat32$c)))
        fat32$c)
       0)))
    :hints
    (("goal"
      :in-theory
      (e/d (data-region-length make-clusters
                               remember-that-time-with-update-nth
                               take-of-nthcdr)
           (append take))
      :induct (update-data-region fat32$c str len)))))

(defthm
  cluster-listp-after-update-data-region
  (implies
   (and
    (fat32$c-p fat32$c)
    (stringp str)
    (natp len)
    (>= (len (explode str))
        (* (cluster-size fat32$c)
           (data-region-length fat32$c)))
    (< 0 (cluster-size fat32$c))
    (cluster-listp (take (- (data-region-length fat32$c)
                            len)
                         (nth *data-regioni* fat32$c))
                   (cluster-size fat32$c))
    (>= (data-region-length fat32$c)
        len))
   (cluster-listp
    (nth *data-regioni*
         (mv-nth 0
                 (update-data-region fat32$c str len)))
    (cluster-size fat32$c)))
  :hints (("goal" :use update-data-region-alt))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (fat32$c-p fat32$c)
          (stringp str)
          (natp len)
          (>= (len (explode str))
              (* (cluster-size fat32$c)
                 (data-region-length fat32$c)))
          (< 0 (cluster-size fat32$c))
          (cluster-listp
           (take (- (data-region-length fat32$c)
                    len)
                 (nth *data-regioni* fat32$c))
           cluster-size)
          (>= (data-region-length fat32$c)
              len)
          (equal cluster-size
                 (cluster-size fat32$c)))
     (cluster-listp
      (nth
       *data-regioni*
       (mv-nth 0
               (update-data-region fat32$c str len)))
      cluster-size))
    :hints
    (("goal"
      :in-theory (e/d (fat32$c-p)
                      (fat32$c-p-of-update-data-region
                       (:definition update-data-region)
                       (:rewrite
                        update-data-region-correctness-1-lemma-1)
                       (:definition nthcdr)
                       (:rewrite cancel-common-factors-in-<)
                       (:rewrite rationalp-prod)
                       (:rewrite rationalp-sum)
                       (:rewrite integerp-prod)))
      :use fat32$c-p-of-update-data-region
      :do-not-induct t)))))
