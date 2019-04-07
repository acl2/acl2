(in-package "ACL2")

;  lofat.lisp                                           Mihir Mehta

; This is a stobj model of the FAT32 filesystem.

(include-book "generate-index-list")
;; (include-book "hifat")
;; (include-book "hifat-equiv")
(include-book "m1-entry-count")
(include-book "fat32-in-memory")
(include-book "cluster-listp")
(include-book "flatten-lemmas")

;; These are some rules from other books which are either interacting badly
;; with the theory I've built up so far, or else causing a lot of unnecessary
;; frames and tries.
(local
 (in-theory (disable take-of-too-many take-of-len-free make-list-ac-removal
                     revappend-removal str::hex-digit-listp-of-cons
                     loghead logtail)))

(local
 (in-theory (disable nth update-nth floor mod
                     true-listp)))

(defund
  cluster-size (fat32-in-memory)
  (declare (xargs :stobjs fat32-in-memory
                  :guard (fat32-in-memoryp fat32-in-memory)))
  (* (bpb_secperclus fat32-in-memory)
     (bpb_bytspersec fat32-in-memory)))

(defthm natp-of-cluster-size
  (implies (fat32-in-memoryp fat32-in-memory)
           (natp (cluster-size fat32-in-memory)))
  :hints (("goal" :in-theory (enable fat32-in-memoryp cluster-size
                                     bpb_bytspersec bpb_secperclus)))
  :rule-classes ((:rewrite
                  :corollary
                  (implies (fat32-in-memoryp fat32-in-memory)
                           (integerp (cluster-size fat32-in-memory))))
                 (:rewrite
                  :corollary
                  (implies (fat32-in-memoryp fat32-in-memory)
                           (rationalp (cluster-size fat32-in-memory))))
                 (:linear
                  :corollary
                  (implies (fat32-in-memoryp fat32-in-memory)
                           (<= 0 (cluster-size fat32-in-memory))))
                 (:rewrite
                  :corollary
                  (implies (fat32-in-memoryp fat32-in-memory)
                           (equal
                           (nfix (cluster-size fat32-in-memory))
                           (cluster-size fat32-in-memory))))))

(defthm
  cluster-size-of-update-nth
  (implies
   (not (member-equal key
                      (list *bpb_secperclus* *bpb_bytspersec*)))
   (equal (cluster-size (update-nth key val fat32-in-memory))
          (cluster-size fat32-in-memory)))
  :hints (("goal" :in-theory (enable cluster-size))))

(defthm
  cluster-size-of-resize-data-region
  (equal (cluster-size (resize-data-region i fat32-in-memory))
         (cluster-size fat32-in-memory))
  :hints (("goal" :in-theory (enable resize-data-region))))

(defthm
  cluster-size-of-resize-fat
  (equal (cluster-size (resize-fat i fat32-in-memory))
         (cluster-size fat32-in-memory))
  :hints (("goal" :in-theory (enable resize-fat))))

(defund
  count-of-clusters (fat32-in-memory)
  (declare
   (xargs :stobjs fat32-in-memory
          :guard (and (fat32-in-memoryp fat32-in-memory)
                      (>= (bpb_secperclus fat32-in-memory) 1))
          :guard-debug t))
  (floor (- (bpb_totsec32 fat32-in-memory)
            (+ (bpb_rsvdseccnt fat32-in-memory)
               (* (bpb_numfats fat32-in-memory)
                  (bpb_fatsz32 fat32-in-memory))))
         (bpb_secperclus fat32-in-memory)))

(defthm
  count-of-clusters-of-resize-fat
  (equal (count-of-clusters (resize-fat i fat32-in-memory))
         (count-of-clusters fat32-in-memory))
  :hints (("goal" :in-theory (enable count-of-clusters))))

(defthm
  count-of-clusters-of-update-nth
  (implies
   (not (member key
                (list *bpb_totsec32*
                      *bpb_rsvdseccnt* *bpb_numfats*
                      *bpb_fatsz32* *bpb_secperclus*)))
   (equal
    (count-of-clusters (update-nth key val fat32-in-memory))
    (count-of-clusters fat32-in-memory)))
  :hints (("goal" :in-theory (enable count-of-clusters))))

(defthm
  count-of-clusters-of-update-data-regioni
  (equal
   (count-of-clusters (update-data-regioni i v fat32-in-memory))
   (count-of-clusters fat32-in-memory))
  :hints
  (("goal"
    :in-theory (enable update-data-regioni))))

(defun
  stobj-cluster-listp-helper
  (fat32-in-memory n)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (and (fat32-in-memoryp fat32-in-memory)
                (natp n)
                (<= n (data-region-length fat32-in-memory)))
    :guard-hints
    (("goal" :in-theory (disable fat32-in-memoryp)))))
  (or
   (zp n)
   (let
    ((current-cluster
      (data-regioni (- (data-region-length fat32-in-memory)
                       n)
                    fat32-in-memory)))
    (and
     (cluster-p current-cluster
                (cluster-size fat32-in-memory))
     (stobj-cluster-listp-helper fat32-in-memory (- n 1))))))

(defthm
  stobj-cluster-listp-helper-correctness-1
  (implies
   (and (natp n)
        (<= n (data-region-length fat32-in-memory)))
   (equal
    (stobj-cluster-listp-helper fat32-in-memory n)
    (cluster-listp
     (nthcdr
      (- (data-region-length fat32-in-memory)
         n)
      (true-list-fix (nth *data-regioni* fat32-in-memory)))
     (cluster-size fat32-in-memory))))
  :hints
  (("goal"
    :in-theory (enable data-regioni data-region-length
                       nth nthcdr-when->=-n-len-l)
    :induct (stobj-cluster-listp-helper fat32-in-memory n)
    :expand
    ((true-list-fix (nth *data-regioni* fat32-in-memory))
     (cluster-listp
      (nthcdr
       (+ (- n)
          (len (nth *data-regioni* fat32-in-memory)))
       (true-list-fix (nth *data-regioni* fat32-in-memory)))
      (cluster-size fat32-in-memory))
     (cluster-listp
      (nthcdr
       (+ (- n)
          (len (cdr (nth *data-regioni* fat32-in-memory))))
       (true-list-fix
        (cdr (nth *data-regioni* fat32-in-memory))))
      (cluster-size fat32-in-memory)))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (natp n)
          (<= n (data-region-length fat32-in-memory))
          (fat32-in-memoryp fat32-in-memory))
     (equal (stobj-cluster-listp-helper fat32-in-memory n)
            (cluster-listp
             (nthcdr (- (data-region-length fat32-in-memory)
                        n)
                     (nth *data-regioni* fat32-in-memory))
             (cluster-size fat32-in-memory))))
    :hints (("goal" :in-theory (enable fat32-in-memoryp))))))

(defund
  fat-entry-count (fat32-in-memory)
  (declare (xargs :guard (fat32-in-memoryp fat32-in-memory)
                  :stobjs fat32-in-memory))
  (floor (* (bpb_fatsz32 fat32-in-memory)
            (bpb_bytspersec fat32-in-memory))
         4))

(defthm
  fat-entry-count-of-update-nth
  (implies
   (not (member-equal key
                      (list *bpb_fatsz32* *bpb_bytspersec*)))
   (equal (fat-entry-count (update-nth key val fat32-in-memory))
          (fat-entry-count fat32-in-memory)))
  :hints
  (("goal" :in-theory (enable fat-entry-count
                              bpb_bytspersec bpb_fatsz32))))

(defthm
  fat-entry-count-of-resize-data-region
  (equal (fat-entry-count
          (resize-data-region i fat32-in-memory))
         (fat-entry-count fat32-in-memory))
  :hints (("goal" :in-theory (enable resize-data-region))))

(defthm
  fat32-entry-p-of-bpb_rootclus-when-fat32-in-memoryp
  (implies (fat32-in-memoryp fat32-in-memory)
           (fat32-entry-p (bpb_rootclus fat32-in-memory)))
  :hints (("goal" :in-theory (enable fat32-entry-p))))

(encapsulate
  ()

  (local
   (defthm
     lofat-fs-p-guard-lemma-2
     (implies (and
               (fat32-in-memoryp fat32-in-memory)
               (>= (bpb_bytspersec fat32-in-memory) *ms-min-bytes-per-sector*)
               (>= (bpb_secperclus fat32-in-memory) 1))
              (not (equal (cluster-size fat32-in-memory)
                          0)))
     :hints (("goal" :in-theory (enable cluster-size)))))

  (defund lofat-fs-p (fat32-in-memory)
    (declare (xargs :stobjs fat32-in-memory :guard t))
    (and (fat32-in-memoryp fat32-in-memory)
         (>= (bpb_bytspersec fat32-in-memory)
             *ms-min-bytes-per-sector*)
         (>= (bpb_secperclus fat32-in-memory) 1)
         (>= (count-of-clusters fat32-in-memory)
             *ms-min-count-of-clusters*)
         (<= (+ *ms-first-data-cluster*
                (count-of-clusters fat32-in-memory))
             *ms-bad-cluster*)
         (>= (bpb_rsvdseccnt fat32-in-memory) 1)
         (>= (bpb_numfats fat32-in-memory) 1)
         (>= (bpb_fatsz32 fat32-in-memory) 1)
         ;; These constraints on bpb_rootclus aren't in the spec, but they are
         ;; clearly implied
         (>= (fat32-entry-mask (bpb_rootclus fat32-in-memory))
             *ms-first-data-cluster*)
         (< (fat32-entry-mask (bpb_rootclus fat32-in-memory))
            (+ *ms-first-data-cluster*
               (count-of-clusters fat32-in-memory)))
         (<= (+ (count-of-clusters fat32-in-memory)
                *ms-first-data-cluster*)
             (fat-entry-count fat32-in-memory))
         ;; The spec (page 9) imposes both hard and soft limits on the legal
         ;; values of the cluster size, limiting it to being a power of 2 from
         ;; 512 through 32768. The following two clauses, however, are less
         ;; stringent - they allow value of cluster size which are powers of 2
         ;; going up to 2097152, although the lower bound of 512 is retained
         ;; thanks to the lower bounds on bpb_bytspersec and bpb_secperclus
         ;; above.
         (equal (mod (cluster-size fat32-in-memory)
                     *ms-dir-ent-length*)
                0)
         (equal (mod *ms-max-dir-size*
                     (cluster-size fat32-in-memory))
                0)
         ;; Some array properties in addition to the scalar properties
         (stobj-cluster-listp-helper
          fat32-in-memory
          (data-region-length fat32-in-memory))
         (equal (data-region-length fat32-in-memory)
                (count-of-clusters fat32-in-memory))
         (equal (* 4 (fat-length fat32-in-memory))
                (* (bpb_fatsz32 fat32-in-memory)
                   (bpb_bytspersec fat32-in-memory)))))

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (local
   (defthm
     lofat-fs-p-guard-lemma-3
     (implies (and (fat32-in-memoryp fat32-in-memory)
                   (< 0 (bpb_bytspersec fat32-in-memory)))
              (< (fat-entry-count fat32-in-memory)
                 (ash 1 48)))
     :rule-classes ()
     :hints (("goal"
              :do-not-induct t
              :in-theory
              (enable fat32-in-memoryp fat-entry-count
                      bpb_bytspersec bpb_fatsz32)))))

  (defthm
    lofat-fs-p-correctness-1
    (implies (lofat-fs-p fat32-in-memory)
             (and (fat32-in-memoryp fat32-in-memory)
                  (integerp (cluster-size fat32-in-memory))
                  (>= (cluster-size fat32-in-memory)
                      *ms-min-bytes-per-sector*)
                  (>= (count-of-clusters fat32-in-memory)
                      *ms-min-count-of-clusters*)
                  (equal (mod (cluster-size fat32-in-memory)
                              *ms-dir-ent-length*)
                         0)
                  (equal (mod *ms-max-dir-size*
                              (cluster-size fat32-in-memory))
                         0)
                  (<= (+ *ms-first-data-cluster*
                         (count-of-clusters fat32-in-memory))
                      *ms-bad-cluster*)
                  (>= (bpb_secperclus fat32-in-memory) 1)
                  (>= (bpb_rsvdseccnt fat32-in-memory) 1)
                  (>= (bpb_numfats fat32-in-memory) 1)
                  (>= (bpb_fatsz32 fat32-in-memory) 1)
                  (>= (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                      *ms-first-data-cluster*)
                  ;; There was a bug here, which we fixed - previously,
                  ;; bpb_rootclus was only allowed to point at clusters up to
                  ;; but not including (count-of-clusters fat32-in-memory),
                  ;; which causes two clusters (up to but not including
                  ;; (+ 2 (count-of-clusters fat32-in-memory))) to be left out.
                  (< (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                     (+ *ms-first-data-cluster*
                        (count-of-clusters fat32-in-memory)))
                  (>= (bpb_bytspersec fat32-in-memory)
                      *ms-min-bytes-per-sector*)
                  (equal (data-region-length fat32-in-memory)
                         (count-of-clusters fat32-in-memory))
                  (<= (+ (count-of-clusters fat32-in-memory)
                         *ms-first-data-cluster*)
                      (fat-length fat32-in-memory))
                  (equal (fat-length fat32-in-memory)
                         (fat-entry-count fat32-in-memory))
                  ;; This also represents a fixed bug - earlier, we were going
                  ;; to return an error for all filesystems with fat-length
                  ;; greater than *ms-bad-cluster*. The upper limit is actually
                  ;; (ash 1 28) - only slightly greater than *ms-bad-cluster* -
                  ;; derived from bpb_fatsz32 being up to (ash 1 16) and
                  ;; bpb_bytspersec being up to 4096.
                  (< (fat-entry-count fat32-in-memory)
                     (ash 1 48))))
    :hints
    (("goal"
      :in-theory
      (e/d
       (lofat-fs-p cluster-size fat-entry-count)
       (fat32-in-memoryp))
      :use
      lofat-fs-p-guard-lemma-3))
    :rule-classes
    ((:rewrite
      :corollary
      (implies (lofat-fs-p fat32-in-memory)
               (and (fat32-in-memoryp fat32-in-memory)
                    (integerp (cluster-size fat32-in-memory))
                    (equal (mod (cluster-size fat32-in-memory)
                                *ms-dir-ent-length*)
                           0)
                    (equal (mod *ms-max-dir-size*
                                (cluster-size fat32-in-memory))
                           0)
                    (equal (data-region-length fat32-in-memory)
                           (count-of-clusters fat32-in-memory))
                    (equal (fat-length fat32-in-memory)
                           (fat-entry-count fat32-in-memory)))))
     (:forward-chaining
      :corollary
      (implies (lofat-fs-p fat32-in-memory)
               (integerp (cluster-size fat32-in-memory))))
     (:linear
      :corollary
      (implies
       (lofat-fs-p fat32-in-memory)
       (and (>= (cluster-size fat32-in-memory)
                *ms-min-bytes-per-sector*)
            (>= (count-of-clusters fat32-in-memory)
                *ms-min-count-of-clusters*)
            (<= (+ *ms-first-data-cluster*
                   (count-of-clusters fat32-in-memory))
                *ms-bad-cluster*)
            (>= (bpb_secperclus fat32-in-memory) 1)
            (>= (bpb_rsvdseccnt fat32-in-memory) 1)
            (>= (bpb_numfats fat32-in-memory) 1)
            (>= (bpb_fatsz32 fat32-in-memory) 1)
            (>= (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                *ms-first-data-cluster*)
            (< (fat32-entry-mask (bpb_rootclus fat32-in-memory))
               (+ *ms-first-data-cluster*
                  (count-of-clusters fat32-in-memory)))
            (>= (bpb_bytspersec fat32-in-memory)
                *ms-min-bytes-per-sector*)
            (>= (* (cluster-size fat32-in-memory)
                   (count-of-clusters fat32-in-memory))
                (* *ms-min-bytes-per-sector*
                   *ms-min-count-of-clusters*))
            (<= (+ (count-of-clusters fat32-in-memory)
                   *ms-first-data-cluster*)
                (fat-entry-count fat32-in-memory))
            (< (fat-entry-count fat32-in-memory)
               (ash 1 48))))))))

(defthm
  fati-when-lofat-fs-p
  (implies (and (lofat-fs-p fat32-in-memory)
                (< (nfix i) (fat-length fat32-in-memory)))
           (fat32-entry-p (fati i fat32-in-memory)))
  :hints (("goal" :in-theory (enable lofat-fs-p
                                     fat32-in-memoryp fati fat-length))))

(defthm
  cluster-size-of-update-fati
  (equal (cluster-size (update-fati i v fat32-in-memory))
         (cluster-size fat32-in-memory))
  :hints
  (("goal" :in-theory (enable cluster-size update-fati))))

(defthm
  count-of-clusters-of-update-fati
  (equal (count-of-clusters (update-fati i v fat32-in-memory))
         (count-of-clusters fat32-in-memory))
  :hints
  (("goal"
    :in-theory (enable count-of-clusters update-fati bpb_totsec32))))

;; Before disabling, this function used to cause 11030904 frames and 95410
;; tries in this book; after disabling those numbers are 4919970 and 33324
;; respectively.
(defthmd
  lofat-fs-p-of-update-fati
  (implies (and (lofat-fs-p fat32-in-memory)
                (< i (fat-length fat32-in-memory)))
           (equal
            (lofat-fs-p
             (update-fati i v fat32-in-memory))
            (fat32-entry-p v)))
  :hints
  (("goal"
    :in-theory (e/d (lofat-fs-p
                     fat32-in-memoryp
                     update-fati fat-length count-of-clusters
                     data-region-length)
                    (cluster-size-of-update-fati))
    :use cluster-size-of-update-fati)))

(defthm
  data-regioni-when-lofat-fs-p
  (implies (and (lofat-fs-p fat32-in-memory)
                (< (nfix i)
                   (data-region-length fat32-in-memory)))
           (cluster-p (data-regioni i fat32-in-memory)
                      (cluster-size fat32-in-memory)))
  :hints
  (("goal" :in-theory (e/d (lofat-fs-p
                            fat32-in-memoryp
                            data-regioni data-region-length)
                           (unsigned-byte-p))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (< (nfix i)
             (data-region-length fat32-in-memory)))
     (and
      (stringp (data-regioni i fat32-in-memory))
      (equal (len (explode (data-regioni i fat32-in-memory)))
             (cluster-size fat32-in-memory))))
    :hints (("goal" :in-theory (enable cluster-p))))))

(defthm
  cluster-size-of-update-data-regioni
  (equal
   (cluster-size (update-data-regioni i v fat32-in-memory))
   (cluster-size fat32-in-memory))
  :hints
  (("goal"
    :in-theory (enable cluster-size update-data-regioni))))

(defthm
  lofat-fs-p-of-update-data-regioni
  (implies (and (lofat-fs-p fat32-in-memory)
                (< i (data-region-length fat32-in-memory)))
           (equal
            (lofat-fs-p
             (update-data-regioni i v fat32-in-memory))
            (cluster-p v (cluster-size fat32-in-memory))))
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d (lofat-fs-p
                     fat32-in-memoryp
                     update-data-regioni
                     data-region-length count-of-clusters
                     fat-length)
                    (cluster-size-of-update-data-regioni))
    :use
    cluster-size-of-update-data-regioni)))

(defconst *initialbytcnt* 16)

(defund get-initial-bytes (str)
  (declare (xargs :guard (and (stringp str)
                              (>= (length str) *initialbytcnt*))))
  (string=>nats (subseq str 0 *initialbytcnt*)))

(defthm
  len-of-get-initial-bytes
  (implies (stringp str)
           (equal (len (get-initial-bytes str))
                  *initialbytcnt*))
  :hints (("goal" :in-theory (enable get-initial-bytes))))

(defthm
  unsigned-byte-listp-of-get-initial-bytes
  (unsigned-byte-listp 8 (get-initial-bytes str))
  :hints (("goal" :in-theory (enable get-initial-bytes))))

(defthm
  nth-of-get-initial-bytes
  (equal (integerp (nth n (get-initial-bytes str)))
         (< (nfix n)
            (len (get-initial-bytes str))))
  :hints (("goal" :in-theory (enable get-initial-bytes)))
  :rule-classes
  (:rewrite
   (:linear
    :corollary
    (implies
     (< (nfix n)
        (len (get-initial-bytes str)))
     (<= 0 (nth n (get-initial-bytes str))))
    :hints (("goal" :in-theory (enable get-initial-bytes))))
   (:rewrite
    :corollary
    (not
     (complex-rationalp (nth n (get-initial-bytes str))))
    :hints (("goal" :in-theory (enable get-initial-bytes))))))

(defund
  get-remaining-rsvdbyts (str)
  (declare
   (xargs
    :guard
    (and
     (stringp str)
     (>= (length str) *initialbytcnt*)
     (<= (* (combine16u (nth 12 (get-initial-bytes str))
                        (nth 11 (get-initial-bytes str)))
            (combine16u (nth 15 (get-initial-bytes str))
                        (nth 14 (get-initial-bytes str))))
         (length str))
     (<= *initialbytcnt*
         (* (combine16u (nth 12 (get-initial-bytes str))
                        (nth 11 (get-initial-bytes str)))
            (combine16u (nth 15 (get-initial-bytes str))
                        (nth 14 (get-initial-bytes str))))))))
  (b*
      ((initial-bytes (get-initial-bytes str))
       (tmp_bytspersec (combine16u (nth (+ 11 1) initial-bytes)
                                   (nth (+ 11 0) initial-bytes)))
       (tmp_rsvdseccnt (combine16u (nth (+ 14 1) initial-bytes)
                                   (nth (+ 14 0) initial-bytes)))
       (tmp_rsvdbytcnt (* tmp_rsvdseccnt tmp_bytspersec)))
    (string=>nats (subseq str *initialbytcnt* tmp_rsvdbytcnt))))

(defthm
  len-of-get-remaining-rsvdbyts
  (implies
   (stringp str)
   (equal
    (len (get-remaining-rsvdbyts str))
    (nfix
     (-
      (* (combine16u (nth 12 (get-initial-bytes str))
                     (nth 11 (get-initial-bytes str)))
         (combine16u (nth 15 (get-initial-bytes str))
                     (nth 14 (get-initial-bytes str))))
      *initialbytcnt*))))
  :hints (("goal" :in-theory (enable get-remaining-rsvdbyts))))

(defthm
  consp-of-get-remaining-rsvdbyts
  (implies
   (stringp str)
   (iff
    (consp (get-remaining-rsvdbyts str))
    (not (zp
          (-
           (* (combine16u (nth 12 (get-initial-bytes str))
                          (nth 11 (get-initial-bytes str)))
              (combine16u (nth 15 (get-initial-bytes str))
                          (nth 14 (get-initial-bytes str))))
           *initialbytcnt*)))))
  :hints (("goal" :in-theory (disable
                              len-of-get-remaining-rsvdbyts)
           :use len-of-get-remaining-rsvdbyts
           :expand (len (get-remaining-rsvdbyts str)))))

(defthm
  unsigned-byte-listp-of-get-remaining-rsvdbyts
  (unsigned-byte-listp 8 (get-remaining-rsvdbyts str))
  :hints (("goal" :in-theory (enable get-remaining-rsvdbyts)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary (integer-listp (get-remaining-rsvdbyts str))
    :hints
    (("goal"
      :in-theory
      (enable integer-listp-when-unsigned-byte-listp))))))

(defthm nth-of-get-remaining-rsvdbyts
  (and
   (equal
    (unsigned-byte-p 8  (nth n
                             (get-remaining-rsvdbyts str)))
    (< (nfix n) (len (get-remaining-rsvdbyts str))))
  (not (complex-rationalp (nth n
                               (get-remaining-rsvdbyts str)))))
  :hints (("goal" :in-theory (enable get-remaining-rsvdbyts))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm lofat-to-string-inversion-lemma-29
    (implies (and (not (zp j)) (integerp i) (> i j))
             (> (floor i j) 0))
    :rule-classes :linear)

  (local
   (defthm read-reserved-area-guard-lemma-5
     (implies (and (unsigned-byte-listp 8 l)
                   (natp n)
                   (< n (len l)))
              (rationalp (nth n l)))
     :hints (("Goal" :in-theory (enable nth)) )))

  ;; This must be called after the file is opened.
  (defund
      read-reserved-area (fat32-in-memory str)
    (declare
     (xargs
      :guard (and (stringp str)
                  (>= (length str) *initialbytcnt*)
                  (fat32-in-memoryp fat32-in-memory))
      :guard-hints
      (("goal"
        :in-theory (e/d (cluster-size)
                        (unsigned-byte-p nth))))
      :stobjs (fat32-in-memory)))
    (b*
        (;; We want to do this unconditionally, in order to prove a strong linear
         ;; rule.
         (fat32-in-memory
          (update-bpb_secperclus 1
                                 fat32-in-memory))
         ;; This too needs to be unconditional.
         (fat32-in-memory
          (update-bpb_rsvdseccnt 1
                                 fat32-in-memory))
         ;; This too needs to be unconditional.
         (fat32-in-memory
          (update-bpb_numfats 1
                              fat32-in-memory))
         ;; I feel weird about stipulating this, but the FAT size has to be at
         ;; least 1 sector if we're going to have at least 65536 clusters of
         ;; data, as required by the FAT specification at the place where it
         ;; specifies how to distinguish between volumes formatted with FAT12,
         ;; FAT16 and FAT32.
         (fat32-in-memory
          (update-bpb_fatsz32 1
                              fat32-in-memory))
         ;; This needs to be at least 512, per the spec.
         (fat32-in-memory
          (update-bpb_bytspersec 512
                                 fat32-in-memory))
         ;; One final bit of fixing.
         (str (str-fix str))
         ;; common stuff for fat filesystems
         (initial-bytes
          (get-initial-bytes str))
         (tmp_bytspersec (combine16u (nth (+ 11 1) initial-bytes)
                                     (nth (+ 11 0) initial-bytes)))
         (tmp_rsvdseccnt (combine16u (nth (+ 14 1) initial-bytes)
                                     (nth (+ 14 0) initial-bytes)))
         (tmp_rsvdbytcnt (* tmp_rsvdseccnt tmp_bytspersec))
         ((unless (and (>= tmp_bytspersec 512)
                       (>= tmp_rsvdseccnt 1)
                       (>= tmp_rsvdbytcnt *initialbytcnt*)
                       (>= (length str) tmp_rsvdbytcnt)))
          (mv fat32-in-memory *EIO*))
         (fat32-in-memory
          (update-bs_jmpboot (subseq initial-bytes 0 3) fat32-in-memory))
         (fat32-in-memory
          (update-bs_oemname (subseq initial-bytes 3 11) fat32-in-memory))
         (fat32-in-memory
          (update-bpb_bytspersec tmp_bytspersec fat32-in-memory))
         (tmp_secperclus (nth 13 initial-bytes))
         ;; this is actually a proxy for testing membership in the set {1, 2, 4,
         ;; 8, 16, 32, 64, 128}
         ((unless (>= tmp_secperclus 1))
          (mv fat32-in-memory *EIO*))
         (fat32-in-memory
          (update-bpb_secperclus tmp_secperclus
                                 fat32-in-memory))
         ((unless (and
                   (equal (mod (cluster-size fat32-in-memory)
                               *ms-dir-ent-length*)
                          0)
                   (equal (mod *ms-max-dir-size*
                               (cluster-size fat32-in-memory))
                          0)))
          (mv fat32-in-memory *EIO*))
         (fat32-in-memory
          (update-bpb_rsvdseccnt tmp_rsvdseccnt fat32-in-memory))
         (remaining-rsvdbyts
          (get-remaining-rsvdbyts str))
         (tmp_numfats (nth (- 16 *initialbytcnt*) remaining-rsvdbyts))
         ((unless (and (mbt (integerp tmp_numfats)) (>= tmp_numfats 1)))
          (mv fat32-in-memory *EIO*))
         (fat32-in-memory
          (update-bpb_numfats tmp_numfats
                              fat32-in-memory))
         (fat32-in-memory
          (update-bpb_rootentcnt
           (combine16u (nth (+ 17 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 17 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_totsec16
           (combine16u (nth (+ 19 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 19 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_media (nth (- 21 *initialbytcnt*) remaining-rsvdbyts)
                            fat32-in-memory))
         (fat32-in-memory
          (update-bpb_fatsz16
           (combine16u (nth (+ 22 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 22 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_secpertrk
           (combine16u (nth (+ 24 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 24 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_numheads
           (combine16u (nth (+ 26 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 26 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_hiddsec
           (combine32u (nth (+ 28 3 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 28 2 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 28 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 28 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_totsec32
           (combine32u (nth (+ 32 3 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 32 2 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 32 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 32 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         ;; fat32-specific stuff
         (tmp_fatsz32
          (combine32u (nth (+ 36 3 (- *initialbytcnt*)) remaining-rsvdbyts)
                      (nth (+ 36 2 (- *initialbytcnt*)) remaining-rsvdbyts)
                      (nth (+ 36 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                      (nth (+ 36 0 (- *initialbytcnt*)) remaining-rsvdbyts)))
         ((unless (>= tmp_fatsz32 1))
          (mv fat32-in-memory *EIO*))
         (fat32-in-memory
          (update-bpb_fatsz32
           tmp_fatsz32
           fat32-in-memory))
         ((unless
              (and
               (>= (count-of-clusters fat32-in-memory)
                   *ms-min-count-of-clusters*)
               (<= (+ (count-of-clusters fat32-in-memory)
                      *ms-first-data-cluster*)
                   (fat-entry-count fat32-in-memory))))
          (mv fat32-in-memory *EIO*))
         (fat32-in-memory
          (update-bpb_extflags
           (combine16u (nth (+ 40 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 40 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_fsver_minor (nth (- 42 *initialbytcnt*) remaining-rsvdbyts)
                                  fat32-in-memory))
         (fat32-in-memory
          (update-bpb_fsver_major (nth (- 43 *initialbytcnt*) remaining-rsvdbyts)
                                  fat32-in-memory))
         (fat32-in-memory
          (update-bpb_rootclus
           (combine32u (nth (+ 44 3 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 44 2 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 44 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 44 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         ((unless
              (and
               (>= (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                   *ms-first-data-cluster*)
               (< (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                  (+ *ms-first-data-cluster*
                     (count-of-clusters fat32-in-memory)))))
          (mv fat32-in-memory *EIO*))
         (fat32-in-memory
          (update-bpb_fsinfo
           (combine16u (nth (+ 48 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 48 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_bkbootsec
           (combine16u (nth (+ 50 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 50 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         ;; no longer skipping bpb_reserved
         (fat32-in-memory
          (update-bpb_reserved (subseq remaining-rsvdbyts
                                       (+ 52 (- *initialbytcnt*) 0)
                                       (+ 52 (- *initialbytcnt*) 12)) fat32-in-memory))
         (fat32-in-memory
          (update-bs_drvnum (nth (- 64 *initialbytcnt*) remaining-rsvdbyts)
                            fat32-in-memory))
         (fat32-in-memory
          (update-bs_reserved1 (nth (- 65 *initialbytcnt*) remaining-rsvdbyts)
                               fat32-in-memory))
         (fat32-in-memory
          (update-bs_bootsig (nth (- 66 *initialbytcnt*) remaining-rsvdbyts)
                             fat32-in-memory))
         (fat32-in-memory
          (update-bs_volid
           (combine32u (nth (+ 67 3 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 67 2 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 67 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 67 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bs_vollab (subseq remaining-rsvdbyts
                                    (+ 71 (- *initialbytcnt*) 0)
                                    (+ 71 (- *initialbytcnt*) 11)) fat32-in-memory))
         (fat32-in-memory
          (update-bs_filsystype (subseq remaining-rsvdbyts
                                        (+ 82 (- *initialbytcnt*) 0)
                                        (+ 82 (- *initialbytcnt*) 8)) fat32-in-memory)))
      (mv fat32-in-memory 0))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    read-reserved-area-correctness-1-lemma-1
    (implies
     (and (>= (length str) *initialbytcnt*)
          (>= (combine16u (nth 12 (get-initial-bytes (str-fix str)))
                          (nth 11 (get-initial-bytes (str-fix str))))
              512)
          (>= (combine16u (nth 15 (get-initial-bytes (str-fix str)))
                          (nth 14 (get-initial-bytes (str-fix str))))
              1))
     (equal
      (get-initial-bytes
       (implode (take (* (combine16u (nth 12 (get-initial-bytes str))
                                     (nth 11 (get-initial-bytes str)))
                         (combine16u (nth 15 (get-initial-bytes str))
                                     (nth 14 (get-initial-bytes str))))
                      (explode str))))
      (get-initial-bytes str)))
    :hints (("goal" :in-theory (enable get-initial-bytes))))

  (defthm
    read-reserved-area-correctness-1-lemma-2
    (implies
     (and (>= (length str) *initialbytcnt*)
          (>= (combine16u (nth 12 (get-initial-bytes (str-fix str)))
                          (nth 11 (get-initial-bytes (str-fix str))))
              512)
          (>= (combine16u (nth 15 (get-initial-bytes (str-fix str)))
                          (nth 14 (get-initial-bytes (str-fix str))))
              1)
          (<= (* (combine16u (nth 15 (get-initial-bytes (str-fix str)))
                             (nth 14 (get-initial-bytes (str-fix str))))
                 (combine16u (nth 12 (get-initial-bytes (str-fix str)))
                             (nth 11 (get-initial-bytes (str-fix str)))))
              (length (str-fix str))))
     (equal
      (get-remaining-rsvdbyts
       (implode (take (* (combine16u (nth 12 (get-initial-bytes str))
                                     (nth 11 (get-initial-bytes str)))
                         (combine16u (nth 15 (get-initial-bytes str))
                                     (nth 14 (get-initial-bytes str))))
                      (explode str))))
      (get-remaining-rsvdbyts str)))
    :hints (("goal" :in-theory (enable get-remaining-rsvdbyts take-of-nthcdr)
             :do-not-induct t))))

(defthm
  read-reserved-area-correctness-1
  (implies
   (and (>= (length str) *initialbytcnt*)
        (>= (combine16u (char-code (nth 12 (explode str)))
                        (char-code (nth 11 (explode str))))
            512)
        (>= (combine16u (char-code (nth 15 (explode str)))
                        (char-code (nth 14 (explode str))))
            1)
        (<= (* (combine16u (char-code (nth 15 (explode str)))
                           (char-code (nth 14 (explode str))))
               (combine16u (char-code (nth 12 (explode str)))
                           (char-code (nth 11 (explode str)))))
            (length str)))
   (equal
    (read-reserved-area fat32-in-memory
                        (subseq str 0
                                (* (combine16u (char-code (nth 15 (explode str)))
                                               (char-code (nth 14 (explode str))))
                                   (combine16u (char-code (nth 12 (explode str)))
                                               (char-code (nth 11 (explode str)))))))
    (read-reserved-area fat32-in-memory str)))
  :hints
  (("goal"
    :in-theory (e/d (read-reserved-area get-initial-bytes
                                        fat-entry-count count-of-clusters
                                        cluster-size take-of-nthcdr)
                    (read-reserved-area-correctness-1-lemma-1
                     read-reserved-area-correctness-1-lemma-2))
    :use (read-reserved-area-correctness-1-lemma-1
          read-reserved-area-correctness-1-lemma-2))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defun
    update-data-region
    (fat32-in-memory str len)
    (declare
     (xargs
      :guard (and (stringp str)
                  (natp len)
                  (<= len
                      (data-region-length fat32-in-memory))
                  (>= (length str)
                      (* (- (data-region-length fat32-in-memory)
                            len)
                         (cluster-size fat32-in-memory)))
                  (<= len
                      (- *ms-bad-cluster*
                         *ms-first-data-cluster*)))
      :stobjs fat32-in-memory
      :measure (nfix len)))
    (b*
        ((len (the (unsigned-byte 28) len))
         ((when (zp len)) (mv fat32-in-memory 0))
         (cluster-size (cluster-size fat32-in-memory))
         (index (- (data-region-length fat32-in-memory)
                   len)))
      (if
       (<= (* (+ index 1) cluster-size)
           (length str))
       (b*
           ((current-cluster (subseq str (* index cluster-size)
                                     (* (+ index 1) cluster-size)))
            (fat32-in-memory
             (update-data-regioni
              index current-cluster fat32-in-memory)))
         (update-data-region
          fat32-in-memory
          str (the (unsigned-byte 28) (- len 1))))
       (b*
           ((current-cluster (subseq str (* index cluster-size) nil))
            (fat32-in-memory
             (update-data-regioni
              index current-cluster fat32-in-memory)))
         (mv fat32-in-memory *eio*)))))

  (defun
      update-data-region-from-disk-image
      (fat32-in-memory len state tmp_init image-path)
    (declare
     (xargs
      :guard
      (and (natp tmp_init)
           (stringp image-path)
           (stringp (read-file-into-string image-path))
           (natp len)
           (<= len
               (data-region-length fat32-in-memory))
           (>= (length (read-file-into-string image-path))
               (+ tmp_init
                  (* (- (data-region-length fat32-in-memory)
                        len)
                     (cluster-size fat32-in-memory))))
           (<= len
               (- *ms-bad-cluster*
                  *ms-first-data-cluster*)))
      :stobjs (fat32-in-memory state)
      :measure (nfix len)))
    (b*
        ((len (the (unsigned-byte 28) len))
         ((when (zp len)) (mv fat32-in-memory 0))
         (cluster-size (cluster-size fat32-in-memory))
         (index (- (data-region-length fat32-in-memory)
                   len))
         (fat32-in-memory
          (update-data-regioni
           index
           (read-file-into-string
            image-path
            :start (+ tmp_init (* index cluster-size))
            :bytes cluster-size)
           fat32-in-memory)))
      (if (equal (length (data-regioni index fat32-in-memory))
                 cluster-size)
          (update-data-region-from-disk-image
           fat32-in-memory
           (the (unsigned-byte 28) (- len 1))
           state tmp_init image-path)
        (mv fat32-in-memory *eio*))))

  (defthm
    update-data-region-from-disk-image-correctness-1
    (implies
     (and (natp tmp_init)
          (<= len
              (data-region-length fat32-in-memory))
          (>= (length (read-file-into-string image-path))
              (+ tmp_init
                 (* (- (data-region-length fat32-in-memory)
                       len)
                    (cluster-size fat32-in-memory))))
          (not (zp (cluster-size fat32-in-memory))))
     (equal (update-data-region-from-disk-image fat32-in-memory
                                                len state tmp_init image-path)
            (update-data-region fat32-in-memory
                                (subseq (read-file-into-string image-path)
                                        tmp_init nil)
                                len)))
    :hints
    (("goal"
      :induct (update-data-region-from-disk-image fat32-in-memory
                                                  len state tmp_init image-path)
      :in-theory (e/d (take-of-nthcdr nthcdr-when->=-n-len-l
                                      by-slice-you-mean-the-whole-cake-2)
                      nil)
      :expand (:free (fat32-in-memory str)
                     (update-data-region fat32-in-memory str len))))))

(defthm
  fat32-in-memoryp-of-update-data-regioni
  (implies
   (fat32-in-memoryp fat32-in-memory)
   (equal
    (fat32-in-memoryp (update-data-regioni i v fat32-in-memory))
    (and (stringp v)
         (<= (nfix i)
             (data-region-length fat32-in-memory)))))
  :hints
  (("goal"
    :in-theory (enable fat32-in-memoryp update-data-regioni
                       data-region-length))))

(defthm
  fat32-in-memoryp-of-update-data-region
  (implies (and (fat32-in-memoryp fat32-in-memory)
                (stringp str))
           (fat32-in-memoryp
            (mv-nth 0
                    (update-data-region fat32-in-memory str len)))))

(defthm
  bpb_bytspersec-of-update-data-region
  (equal
   (bpb_bytspersec (mv-nth 0 (update-data-region fat32-in-memory str len)))
   (bpb_bytspersec fat32-in-memory)))

(defthm
  bpb_secperclus-of-update-data-region
  (equal
   (bpb_secperclus (mv-nth 0 (update-data-region fat32-in-memory str len)))
   (bpb_secperclus fat32-in-memory)))

(defthm
  bpb_rsvdseccnt-of-update-data-region
  (equal
   (bpb_rsvdseccnt (mv-nth 0 (update-data-region fat32-in-memory str len)))
   (bpb_rsvdseccnt fat32-in-memory)))

(defthm
  bpb_totsec32-of-update-data-region
  (equal
   (bpb_totsec32 (mv-nth 0 (update-data-region fat32-in-memory str len)))
   (bpb_totsec32 fat32-in-memory)))

(defthm
  bpb_fatsz32-of-update-data-region
  (equal
   (bpb_fatsz32 (mv-nth 0 (update-data-region fat32-in-memory str len)))
   (bpb_fatsz32 fat32-in-memory)))

(defthm
  bpb_numfats-of-update-data-region
  (equal
   (bpb_numfats (mv-nth 0 (update-data-region fat32-in-memory str len)))
   (bpb_numfats fat32-in-memory)))

(defthm
  bpb_rootclus-of-update-data-region
  (equal
   (bpb_rootclus (mv-nth 0 (update-data-region fat32-in-memory str len)))
   (bpb_rootclus fat32-in-memory)))

(defthm
  fat-length-of-update-data-region
  (equal
   (fat-length (mv-nth 0 (update-data-region fat32-in-memory str len)))
   (fat-length fat32-in-memory)))

(defthm
  fat-entry-count-of-update-data-region
  (equal (fat-entry-count
          (mv-nth 0 (update-data-region fat32-in-memory str len)))
         (fat-entry-count fat32-in-memory))
  :hints (("goal" :in-theory (enable fat-entry-count))))

(defthm
  data-region-length-of-update-data-region
  (implies
   (<= len
       (data-region-length fat32-in-memory))
   (equal (data-region-length
           (mv-nth 0 (update-data-region fat32-in-memory str len)))
          (data-region-length fat32-in-memory)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (<= len
         (data-region-length fat32-in-memory))
     (equal
      (consp (nth *data-regioni*
                  (mv-nth 0 (update-data-region fat32-in-memory str len))))
      (consp (nth *data-regioni* fat32-in-memory))))
    :hints
    (("goal"
      :in-theory (enable data-region-length)
      :do-not-induct t
      :expand
      ((len (nth *data-regioni*
                 (mv-nth 0 (update-data-region fat32-in-memory str len))))
       (len (nth *data-regioni* fat32-in-memory))))))))

(defthmd
  update-data-region-correctness-2
  (equal
   (update-data-region fat32-in-memory str len)
   (mv (mv-nth 0
               (update-data-region fat32-in-memory str len))
       (mv-nth 1
               (update-data-region fat32-in-memory str len)))))

(encapsulate
  ()

  (local (include-book "arithmetic-3/top" :dir :system))

  (set-default-hints
   '((nonlinearp-default-hint stable-under-simplificationp
                              hist pspv)))

  (defthm update-data-region-alt-lemma-4
    (implies (and (not (zp len))
                  (< (len (explode str))
                     (+ (cluster-size fat32-in-memory)
                        (* -1 len (cluster-size fat32-in-memory))
                        (* (cluster-size fat32-in-memory)
                           (len (nth *data-regioni* fat32-in-memory)))))
                  (< 0 (cluster-size fat32-in-memory)))
             (< (len (explode str))
                (* (cluster-size fat32-in-memory)
                   (len (nth *data-regioni* fat32-in-memory)))))
    :rule-classes :linear)

  (defthm
    update-data-region-correctness-1
    (implies (and (natp len)
                  (<= len
                      (data-region-length fat32-in-memory))
                  (>= (length str)
                      (* (- (data-region-length fat32-in-memory)
                            len)
                         (cluster-size fat32-in-memory))))
             (iff
              (equal (mv-nth 1
                             (update-data-region fat32-in-memory str len))
                     0)
              (>= (length str)
                  (* (data-region-length fat32-in-memory)
                     (cluster-size fat32-in-memory)))))))

(encapsulate
  ()
  
  (local
   (defthm
     update-data-region-alt-lemma-1
     (equal (update-nth *data-regioni* val
                        (update-data-regioni i v fat32-in-memory))
            (update-nth *data-regioni* val fat32-in-memory))
     :hints (("goal" :in-theory (enable update-data-regioni)))))

  (local
   (defthm
     update-data-region-alt-lemma-2
     (implies (fat32-in-memoryp fat32-in-memory)
              (and
               (true-listp (nth *data-regioni* fat32-in-memory))
               (equal
                (update-nth *data-regioni*
                            (nth *data-regioni* fat32-in-memory)
                            fat32-in-memory)
                fat32-in-memory)))
     :hints (("goal" :in-theory (enable fat32-in-memoryp)))))

  (local
   (defthm
     update-data-region-alt-lemma-3
     (equal
      (nth *data-regioni*
           (update-data-regioni i v fat32-in-memory))
      (update-nth i v
                  (nth *data-regioni* fat32-in-memory)))
     :hints (("goal" :in-theory (enable update-data-regioni)) )))

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthmd
    update-data-region-alt
    (implies
     (and (stringp str)
          (natp len)
          (>= (data-region-length fat32-in-memory)
              len)
          (fat32-in-memoryp fat32-in-memory)
          (< 0 (cluster-size fat32-in-memory))
          (>= (length str)
              (* (data-region-length fat32-in-memory)
                 (cluster-size fat32-in-memory))))
     (equal
      (update-data-region fat32-in-memory str len)
      (mv
       (update-nth
        *data-regioni*
        (append
         (take (- (data-region-length fat32-in-memory)
                  len)
               (nth *data-regioni* fat32-in-memory))
         (make-clusters
          (subseq str
                  (* (- (data-region-length fat32-in-memory)
                        len)
                     (cluster-size fat32-in-memory))
                  (* (data-region-length fat32-in-memory)
                     (cluster-size fat32-in-memory)))
          (cluster-size fat32-in-memory)))
        fat32-in-memory)
       0)))
    :hints
    (("goal"
      :in-theory
      (e/d (data-region-length make-clusters
                               remember-that-time-with-update-nth
                               by-slice-you-mean-the-whole-cake-2
                               take-of-nthcdr)
           (append take take-redefinition))
      :induct (update-data-region fat32-in-memory str len)))))

(defthm
  cluster-listp-after-update-data-region
  (implies
   (and
    (fat32-in-memoryp fat32-in-memory)
    (stringp str)
    (natp len)
    (>= (len (explode str))
        (* (cluster-size fat32-in-memory)
           (data-region-length fat32-in-memory)))
    (< 0 (cluster-size fat32-in-memory))
    (cluster-listp (take (- (data-region-length fat32-in-memory)
                            len)
                         (nth *data-regioni* fat32-in-memory))
                   (cluster-size fat32-in-memory))
    (>= (data-region-length fat32-in-memory)
        len))
   (cluster-listp
    (nth *data-regioni*
         (mv-nth 0
                 (update-data-region fat32-in-memory str len)))
    (cluster-size fat32-in-memory)))
  :hints (("goal" :use update-data-region-alt))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (fat32-in-memoryp fat32-in-memory)
          (stringp str)
          (natp len)
          (>= (len (explode str))
              (* (cluster-size fat32-in-memory)
                 (data-region-length fat32-in-memory)))
          (< 0 (cluster-size fat32-in-memory))
          (cluster-listp
           (take (- (data-region-length fat32-in-memory)
                    len)
                 (nth *data-regioni* fat32-in-memory))
           cluster-size)
          (>= (data-region-length fat32-in-memory)
              len)
          (equal cluster-size
                 (cluster-size fat32-in-memory)))
     (cluster-listp
      (nth
       *data-regioni*
       (mv-nth 0
               (update-data-region fat32-in-memory str len)))
      cluster-size))
    :hints
    (("goal"
      :in-theory (e/d (fat32-in-memoryp)
                      (fat32-in-memoryp-of-update-data-region))
      :use fat32-in-memoryp-of-update-data-region
      :do-not-induct t)))))

(defun
  update-fat (fat32-in-memory str pos)
  (declare
   (xargs :guard (and (stringp str)
                      (unsigned-byte-p 48 pos)
                      (<= (* pos 4) (length str))
                      (equal (length str)
                             (* (fat-length fat32-in-memory) 4)))
          :guard-hints
          (("goal" :in-theory (e/d (fat-length update-fati)
                                   (fat32-in-memoryp))))
          :stobjs fat32-in-memory))
  (b*
      ((pos (the (unsigned-byte 48) pos)))
    (if
     (zp pos)
     fat32-in-memory
     (b*
         ((ch-word
           (the
            (unsigned-byte 32)
            (combine32u (char-code (char str
                                         (the (unsigned-byte 50)
                                              (- (* pos 4) 1))))
                        (char-code (char str
                                         (the (unsigned-byte 50)
                                              (- (* pos 4) 2))))
                        (char-code (char str
                                         (the (unsigned-byte 50)
                                              (- (* pos 4) 3))))
                        (char-code (char str
                                         (the (unsigned-byte 50)
                                              (- (* pos 4) 4)))))))
          (fat32-in-memory (update-fati (- pos 1)
                                        ch-word fat32-in-memory)))
       (update-fat fat32-in-memory str
                   (the (unsigned-byte 48) (- pos 1)))))))

(defthm
  nth-of-update-fat
  (implies (not (equal (nfix n) *fati*))
           (equal (nth n (update-fat fat32-in-memory str pos))
                  (nth n fat32-in-memory)))
  :hints (("goal" :in-theory (enable update-fat update-fati))))

(defthm bpb_secperclus-of-update-fat
  (equal (bpb_secperclus
          (update-fat fat32-in-memory str pos))
         (bpb_secperclus fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_secperclus)) ))

(defthm bpb_fatsz32-of-update-fat
  (equal (bpb_fatsz32
          (update-fat fat32-in-memory str pos))
         (bpb_fatsz32 fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_fatsz32)) ))

(defthm bpb_numfats-of-update-fat
  (equal (bpb_numfats
          (update-fat fat32-in-memory str pos))
         (bpb_numfats fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_numfats)) ))

(defthm bpb_rsvdseccnt-of-update-fat
  (equal (bpb_rsvdseccnt
          (update-fat fat32-in-memory str pos))
         (bpb_rsvdseccnt fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_rsvdseccnt)) ))

(defthm bpb_totsec32-of-update-fat
  (equal (bpb_totsec32
          (update-fat fat32-in-memory str pos))
         (bpb_totsec32 fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_totsec32)) ))

(defthm bpb_bytspersec-of-update-fat
  (equal (bpb_bytspersec
          (update-fat fat32-in-memory str pos))
         (bpb_bytspersec fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_bytspersec)) ))

(defthm count-of-clusters-of-update-fat
  (equal (count-of-clusters
          (update-fat fat32-in-memory str pos))
         (count-of-clusters fat32-in-memory))
  :hints (("Goal" :in-theory (enable count-of-clusters)) ))

(defthm cluster-size-of-update-fat
  (equal (cluster-size
          (update-fat fat32-in-memory str pos))
         (cluster-size fat32-in-memory))
  :hints (("Goal" :in-theory (enable cluster-size)) ))

(defthm
  data-region-length-of-update-fat
  (equal (data-region-length
          (update-fat fat32-in-memory str pos))
         (data-region-length fat32-in-memory))
  :hints (("goal" :in-theory (enable data-region-length))))

(defthm fat32-in-memoryp-of-update-fat
  (implies (and (<= (* pos 4) (length str))
                (equal (length str)
                       (* (fat-length fat32-in-memory) 4))
                (fat32-in-memoryp fat32-in-memory))
           (fat32-in-memoryp (update-fat fat32-in-memory str pos))))

(defthm
  fat-entry-count-of-update-fat
  (equal (fat-entry-count
          (update-fat fat32-in-memory str pos))
         (fat-entry-count fat32-in-memory))
  :hints (("goal" :in-theory (enable fat-entry-count))))

(defthm
  bpb_rootclus-of-update-fat
  (equal
   (bpb_rootclus (update-fat fat32-in-memory str pos))
   (bpb_rootclus fat32-in-memory)))

(defthm
  fat-length-of-update-fat
  (implies (and (<= (* pos 4) (length str))
                (equal (length str)
                       (* (fat-length fat32-in-memory) 4)))
           (equal (fat-length (update-fat fat32-in-memory str pos))
                  (fat-length fat32-in-memory))))

(defthm
  bpb_secperclus-of-read-reserved-area
  (and
   (implies
    (stringp str)
    (>=
     (bpb_secperclus
      (mv-nth 0
              (read-reserved-area fat32-in-memory str)))
     1))
   (natp
    (bpb_secperclus
     (mv-nth 0
             (read-reserved-area fat32-in-memory str)))))
  :hints
    (("goal"
      :do-not-induct t
      :in-theory (e/d (read-reserved-area) (subseq))))
  :rule-classes
  ((:linear
    :corollary
    (<= 1
        (bpb_secperclus
         (mv-nth 0
                 (read-reserved-area fat32-in-memory str))))
    :hints
    (("goal" :do-not-induct t
      :in-theory (e/d (read-reserved-area) (subseq)))))
   (:rewrite
    :corollary
    (integerp
     (bpb_secperclus
      (mv-nth 0
              (read-reserved-area fat32-in-memory str))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (e/d (read-reserved-area) (subseq)))))
   (:type-prescription
    :corollary
    (natp
     (bpb_secperclus
      (mv-nth 0
              (read-reserved-area fat32-in-memory str))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (e/d (read-reserved-area) (subseq)))))))

(defthm
  bpb_rsvdseccnt-of-read-reserved-area
  (and
   (integerp
    (bpb_rsvdseccnt
     (mv-nth
      0
      (read-reserved-area fat32-in-memory str))))
   (<= 1
       (bpb_rsvdseccnt
        (mv-nth
         0
         (read-reserved-area fat32-in-memory str)))))
  :rule-classes
  ((:linear
    :corollary
    (<= 1
        (bpb_rsvdseccnt
         (mv-nth
          0
          (read-reserved-area fat32-in-memory str)))))
   (:rewrite
    :corollary
    (integerp
     (bpb_rsvdseccnt
      (mv-nth
       0
       (read-reserved-area fat32-in-memory str)))))
   (:type-prescription
    :corollary
    (natp
     (bpb_rsvdseccnt
      (mv-nth
       0
       (read-reserved-area fat32-in-memory str))))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (read-reserved-area) (subseq)))))

(defthm
  bpb_numfats-of-read-reserved-area
  (and
   (<= 1
       (bpb_numfats
        (mv-nth
         0
         (read-reserved-area fat32-in-memory str))))
   (integerp
    (bpb_numfats
     (mv-nth
      0
      (read-reserved-area fat32-in-memory str)))))
  :rule-classes
  ((:linear
    :corollary
    (<= 1
        (bpb_numfats
         (mv-nth
          0
          (read-reserved-area fat32-in-memory str)))))
   (:rewrite
    :corollary
    (integerp
     (bpb_numfats
      (mv-nth
       0
       (read-reserved-area fat32-in-memory str)))))
   (:type-prescription
    :corollary
    (natp
     (bpb_numfats
      (mv-nth
       0
       (read-reserved-area fat32-in-memory str))))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (read-reserved-area) (subseq)))))

(defthm
  bpb_fatsz32-of-read-reserved-area
  (and
   (<= 1
       (bpb_fatsz32
        (mv-nth
         0
         (read-reserved-area fat32-in-memory str))))
   (integerp
    (bpb_fatsz32
     (mv-nth
      0
      (read-reserved-area fat32-in-memory str)))))
  :rule-classes
  ((:linear
    :corollary
    (<= 1
        (bpb_fatsz32
         (mv-nth
          0
          (read-reserved-area fat32-in-memory str)))))
   (:rewrite
    :corollary
    (integerp
     (bpb_fatsz32
      (mv-nth
       0
       (read-reserved-area fat32-in-memory str)))))
   (:type-prescription
    :corollary
    (natp
     (bpb_fatsz32
      (mv-nth
       0
       (read-reserved-area fat32-in-memory str))))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (read-reserved-area) (subseq)))))

(defthm
  bpb_bytspersec-of-read-reserved-area
  (and
   (integerp
    (bpb_bytspersec
     (mv-nth 0
             (read-reserved-area fat32-in-memory str))))
   (<= *ms-min-bytes-per-sector*
       (bpb_bytspersec
        (mv-nth 0
                (read-reserved-area fat32-in-memory str))))
   (< (bpb_bytspersec
       (mv-nth 0
               (read-reserved-area fat32-in-memory str)))
      (ash 1 16)))
  :rule-classes
  ((:linear
    :corollary
    (and
     (<= *ms-min-bytes-per-sector*
         (bpb_bytspersec
          (mv-nth 0
                  (read-reserved-area fat32-in-memory str))))
     (< (bpb_bytspersec
         (mv-nth 0
                 (read-reserved-area fat32-in-memory str)))
        (ash 1 16))))
   (:rewrite
    :corollary
    (integerp
     (bpb_bytspersec
      (mv-nth 0
              (read-reserved-area fat32-in-memory str)))))
   (:type-prescription
    :corollary
    (natp
     (bpb_bytspersec
      (mv-nth 0
              (read-reserved-area fat32-in-memory str))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (read-reserved-area) (subseq unsigned-byte-p))
    :use
    ((:instance
      (:theorem (implies (unsigned-byte-p 16 x)
                         (< x (ash 1 16))))
      (x (combine16u
          (nth 12 (get-initial-bytes (str-fix str)))
          (nth 11
               (get-initial-bytes (str-fix str))))))))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    cluster-size-of-read-reserved-area
    (natp
    (- (cluster-size
         (mv-nth 0
                 (read-reserved-area fat32-in-memory str)))
       *ms-min-bytes-per-sector*))
    :rule-classes
    ((:linear
      :corollary
      (<= *ms-min-bytes-per-sector*
          (cluster-size
           (mv-nth 0
                   (read-reserved-area fat32-in-memory str)))))
     (:rewrite
      :corollary
      (integerp
       (cluster-size
        (mv-nth 0
                (read-reserved-area fat32-in-memory str)))))
     (:type-prescription
      :corollary
      (natp
       (cluster-size
        (mv-nth 0
                (read-reserved-area fat32-in-memory str))))))
    :hints
    (("goal"
      :in-theory (e/d (cluster-size read-reserved-area)
                      (bpb_bytspersec-of-read-reserved-area
                       bpb_secperclus-of-read-reserved-area))
      :use (bpb_bytspersec-of-read-reserved-area
            bpb_secperclus-of-read-reserved-area))))

  (defthm
    fat-entry-count-of-read-reserved-area
    (implies
     (equal (mv-nth 1
                    (read-reserved-area fat32-in-memory str))
            0)
     (and
      (<= 512
          (fat-entry-count
           (mv-nth 0
                   (read-reserved-area fat32-in-memory str))))
      (< (fat-entry-count
          (mv-nth 0
                  (read-reserved-area fat32-in-memory str)))
         (ash 1 48))))
    :rule-classes :linear
    :hints
    (("goal"
      :in-theory (e/d (fat-entry-count read-reserved-area)
                      ((:rewrite combine16u-unsigned-byte)
                       (:rewrite combine32u-unsigned-byte)))
      :use
      ((:instance
        (:rewrite combine16u-unsigned-byte)
        (a0 (nth 11 (get-initial-bytes (str-fix str))))
        (a1 (nth 12 (get-initial-bytes (str-fix str)))))
       (:instance
        (:rewrite combine32u-unsigned-byte)
        (a0 (nth 20
                 (get-remaining-rsvdbyts (str-fix str))))
        (a1 (nth 21
                 (get-remaining-rsvdbyts (str-fix str))))
        (a2 (nth 22
                 (get-remaining-rsvdbyts (str-fix str))))
        (a3 (nth 23
                 (get-remaining-rsvdbyts (str-fix str))))))))))

(defthm
  count-of-clusters-of-read-reserved-area
  (implies
   (equal (mv-nth 1
                  (read-reserved-area fat32-in-memory str))
          0)
   (and
    (<= *ms-min-count-of-clusters*
        (count-of-clusters
         (mv-nth 0
                 (read-reserved-area fat32-in-memory str))))
    (integerp
     (count-of-clusters
      (mv-nth 0
              (read-reserved-area fat32-in-memory str))))))
  :rule-classes
  ((:linear
    :corollary
    (implies
     (equal (mv-nth 1
                    (read-reserved-area fat32-in-memory str))
            0)
     (<= *ms-min-count-of-clusters*
         (count-of-clusters
          (mv-nth 0
                  (read-reserved-area fat32-in-memory str))))))
   (:rewrite
    :corollary
    (implies
     (equal (mv-nth 1
                    (read-reserved-area fat32-in-memory str))
            0)
     (integerp
      (count-of-clusters
       (mv-nth 0
               (read-reserved-area fat32-in-memory str)))))))
  :hints (("goal" :in-theory (enable count-of-clusters read-reserved-area))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    fat32-in-memoryp-of-read-reserved-area
    (implies (and (fat32-in-memoryp fat32-in-memory)
                  (stringp str))
             (fat32-in-memoryp
              (mv-nth 0
                      (read-reserved-area fat32-in-memory str))))
    :hints (("Goal" :in-theory (enable read-reserved-area)) ))

  (defund
    string-to-lofat
    (fat32-in-memory str)
    (declare
     (xargs
      :guard (and (stringp str)
                  (>= (length str) *initialbytcnt*)
                  (fat32-in-memoryp fat32-in-memory))
      :guard-debug t
      :guard-hints
      (("goal"
        :do-not-induct t
        :in-theory (enable cluster-size count-of-clusters)))
      :stobjs fat32-in-memory))
    (b*
        (((mv fat32-in-memory error-code)
          (read-reserved-area fat32-in-memory str))
         ((unless (equal error-code 0))
          (mv fat32-in-memory error-code))
         (fat-read-size (fat-entry-count fat32-in-memory))
         ;; The expression below should eventually be replaced by
         ;; fat-entry-count, but that is going to open a can of worms...
         ((unless (integerp
                   (/ (* (bpb_fatsz32 fat32-in-memory)
                         (bpb_bytspersec fat32-in-memory))
                      4)))
          (mv fat32-in-memory *EIO*))
         (data-byte-count (* (count-of-clusters fat32-in-memory)
                             (cluster-size fat32-in-memory)))
         ((unless (> data-byte-count 0))
          (mv fat32-in-memory *EIO*))
         (tmp_bytspersec (bpb_bytspersec fat32-in-memory))
         (tmp_init (* tmp_bytspersec
                      (+ (bpb_rsvdseccnt fat32-in-memory)
                         (* (bpb_numfats fat32-in-memory)
                            (bpb_fatsz32 fat32-in-memory)))))
         (fat32-in-memory
          (resize-fat fat-read-size fat32-in-memory))
         ((unless (and
                   (<= (+ (* (bpb_rsvdseccnt fat32-in-memory)
                             (bpb_bytspersec fat32-in-memory))
                          (* fat-read-size 4))
                       (length str))
                   (unsigned-byte-p 48 fat-read-size)))
          (mv fat32-in-memory *EIO*))
         (fat32-in-memory
          (update-fat
           fat32-in-memory
           (subseq str
                   (* (bpb_rsvdseccnt fat32-in-memory)
                      (bpb_bytspersec fat32-in-memory))
                   (+ (* (bpb_rsvdseccnt fat32-in-memory)
                         (bpb_bytspersec fat32-in-memory))
                      (* fat-read-size 4)))
           fat-read-size))
         (fat32-in-memory
          (resize-data-region (count-of-clusters fat32-in-memory) fat32-in-memory))
         ((unless
              (and (<= (data-region-length fat32-in-memory)
                       (- *ms-bad-cluster* *ms-first-data-cluster*))
                   (>= (length str) tmp_init)))
          (mv fat32-in-memory *EIO*))
         (data-region-string
          (subseq str tmp_init nil)))
      (update-data-region fat32-in-memory data-region-string
                          (data-region-length fat32-in-memory)))))

(defthmd
  string-to-lofat-correctness-1
  (equal
   (string-to-lofat fat32-in-memory str)
   (mv
    (mv-nth 0
            (string-to-lofat fat32-in-memory str))
    (mv-nth 1
            (string-to-lofat fat32-in-memory str))))
  :hints
  (("goal"
    :in-theory (e/d (string-to-lofat)
                    (subseq))
    :use
    (:instance
     update-data-region-correctness-2
     (fat32-in-memory
      (resize-data-region
       (count-of-clusters
        (mv-nth 0
                (read-reserved-area fat32-in-memory str)))
       (update-fat
        (resize-fat
         (fat-entry-count
          (mv-nth 0
                  (read-reserved-area fat32-in-memory str)))
         (mv-nth 0
                 (read-reserved-area fat32-in-memory str)))
        (subseq
         str
         (*
          (bpb_bytspersec
           (mv-nth 0
                   (read-reserved-area fat32-in-memory str)))
          (bpb_rsvdseccnt
           (mv-nth 0
                   (read-reserved-area fat32-in-memory str))))
         (+
          (*
           4
           (fat-entry-count
            (mv-nth 0
                    (read-reserved-area fat32-in-memory str))))
          (*
           (bpb_bytspersec
            (mv-nth 0
                    (read-reserved-area fat32-in-memory str)))
           (bpb_rsvdseccnt
            (mv-nth
             0
             (read-reserved-area fat32-in-memory str))))))
        (fat-entry-count
         (mv-nth 0
                 (read-reserved-area fat32-in-memory str))))))
     (str
      (subseq
       str
       (+
        (*
         (bpb_bytspersec
          (mv-nth 0
                  (read-reserved-area fat32-in-memory str)))
         (bpb_rsvdseccnt
          (mv-nth 0
                  (read-reserved-area fat32-in-memory str))))
        (*
         (bpb_bytspersec
          (mv-nth 0
                  (read-reserved-area fat32-in-memory str)))
         (bpb_fatsz32
          (mv-nth 0
                  (read-reserved-area fat32-in-memory str)))
         (bpb_numfats
          (mv-nth 0
                  (read-reserved-area fat32-in-memory str)))))
       nil))
     (len
      (count-of-clusters
       (mv-nth 0
               (read-reserved-area fat32-in-memory str))))))))

(defthm
  disk-image-to-lofat-guard-lemma-1
  (iff
   (< (len (explode (read-file-into-string2
                     image-path 0 *initialbytcnt* state)))
      *initialbytcnt*)
   (<
    (len
     (explode (read-file-into-string2 image-path 0 nil state)))
    *initialbytcnt*))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (<=
      *initialbytcnt*
      (len
       (explode
        (read-file-into-string2 image-path 0 nil state))))
     (and
      (stringp (read-file-into-string2
                image-path 0 *initialbytcnt* state))
      (equal
       (len (explode (read-file-into-string2
                      image-path 0 *initialbytcnt* state)))
       *initialbytcnt*))))))

(defthm
  disk-image-to-lofat-guard-lemma-3
  (equal
   (read-reserved-area
    (update-bpb_bytspersec
     512
     (update-bpb_fatsz32
      1
      (update-bpb_numfats
       1
       (update-bpb_rsvdseccnt
        1
        (update-bpb_secperclus 1 fat32-in-memory)))))
    str)
   (read-reserved-area fat32-in-memory str))
  :hints (("Goal" :in-theory (enable read-reserved-area)) ))

(defthm
  disk-image-to-lofat-guard-lemma-9
  (implies
   (< (nfix n) 16)
   (equal
    (nth
     n
     (explode (read-file-into-string2 image-path 0 16 state)))
    (nth
     n
     (explode
      (read-file-into-string2 image-path 0 nil state)))))
  :hints (("goal" :in-theory (enable nth))))

(defthm
  disk-image-to-lofat-guard-lemma-4
  (implies
   (equal
    (mv-nth
     1
     (read-reserved-area fat32-in-memory
                         (read-file-into-string2 image-path 0 nil state)))
    0)
   (and
    (equal
     (combine16u
      (char-code
       (nth 12
            (explode (read-file-into-string2 image-path 0 nil state))))
      (char-code
       (nth 11
            (explode (read-file-into-string2 image-path 0 nil state)))))
     (bpb_bytspersec
      (mv-nth
       0
       (read-reserved-area fat32-in-memory
                           (read-file-into-string2 image-path 0 nil state)))))
    (equal
     (combine16u
      (char-code
       (nth 15
            (explode (read-file-into-string2 image-path 0 nil state))))
      (char-code
       (nth 14
            (explode (read-file-into-string2 image-path 0 nil state)))))
     (bpb_rsvdseccnt
      (mv-nth
       0
       (read-reserved-area fat32-in-memory
                           (read-file-into-string2 image-path 0 nil state)))))))
  :hints (("Goal" :in-theory (enable read-reserved-area get-initial-bytes)) ))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    disk-image-to-lofat-guard-lemma-5
    (implies
     (equal (mv-nth 1
                    (read-reserved-area fat32-in-memory str))
            0)
     (<=
      (* *ms-min-bytes-per-sector*
         *ms-min-count-of-clusters*)
      (*
       (cluster-size
        (mv-nth 0
                (read-reserved-area fat32-in-memory str)))
       (count-of-clusters
        (mv-nth 0
                (read-reserved-area fat32-in-memory str))))))
    :rule-classes :linear
    :hints
    (("goal"
      :in-theory (disable cluster-size-of-read-reserved-area
                          count-of-clusters-of-read-reserved-area
                          read-reserved-area)
      :use (cluster-size-of-read-reserved-area
            count-of-clusters-of-read-reserved-area))))

  (defthm
    disk-image-to-lofat-guard-lemma-15
    (iff
     (integerp
      (*
       (bpb_fatsz32
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state))))
       1/4
       (bpb_bytspersec
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state))))))
     (integerp
      (*
       1/4
       (bpb_bytspersec
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state))))
       (bpb_fatsz32
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state))))))))

  (defthm
    disk-image-to-lofat-guard-lemma-22
    (implies
     (and
      (integerp
       (*
        1/4
        (bpb_bytspersec
         (mv-nth
          0
          (read-reserved-area fat32-in-memory
                              str)))
        (bpb_fatsz32
         (mv-nth 0
                 (read-reserved-area
                  fat32-in-memory
                  str))))))
     (<=
      (* 4
         (fat-entry-count
          (mv-nth 0
                  (read-reserved-area
                   fat32-in-memory
                   str))))
      (*
       (bpb_bytspersec
        (mv-nth
         0
         (read-reserved-area fat32-in-memory
                             str)))
       (bpb_fatsz32
        (mv-nth
         0
         (read-reserved-area fat32-in-memory
                             str)))
       (bpb_numfats
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 str))))))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable fat-entry-count)) )))

(defthm
  disk-image-to-lofat-guard-lemma-6
  (implies
   (<=
    16
    (len
     (explode (read-file-into-string2 image-path 0 16 state))))
   (stringp
    (read-file-into-string2
     image-path 16
     (+
      -16
      (*
       (bpb_bytspersec
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state))))
       (bpb_rsvdseccnt
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state))))))
     state))))

(defthm
  disk-image-to-lofat-guard-lemma-7
  (implies
   (and
    (not
     (equal
      (mv-nth
       1
       (read-reserved-area
        fat32-in-memory
        (read-file-into-string2 image-path 0 nil state)))
      0))
    (<=
     16
     (len
      (explode
       (read-file-into-string2 image-path 0 16 state)))))
   (stringp
    (read-file-into-string2
     image-path 16
     (+
      -16
      (*
       (combine16u
        (char-code
         (nth
          12
          (explode
           (read-file-into-string2 image-path 0 nil state))))
        (char-code
         (nth
          11
          (explode
           (read-file-into-string2 image-path 0 nil state)))))
       (combine16u
        (char-code
         (nth
          15
          (explode
           (read-file-into-string2 image-path 0 nil state))))
        (char-code
         (nth
          14
          (explode
           (read-file-into-string2 image-path 0 nil state)))))))
     state)))
  :hints (("goal" :in-theory (enable read-reserved-area))))

(defthm
  disk-image-to-lofat-guard-lemma-8
  (implies
   (and (stringp str)
        (<= *initialbytcnt* (len (explode str)))
        (< (combine16u (char-code (nth 15 (explode str)))
                       (char-code (nth 14 (explode str))))
           1))
   (equal
    (read-reserved-area fat32-in-memory str)
    (mv
     (update-bpb_bytspersec
      512
      (update-bpb_fatsz32
       1
       (update-bpb_numfats
        1
        (update-bpb_rsvdseccnt
         1
         (update-bpb_secperclus 1 fat32-in-memory)))))
     *EIO*)))
  :hints
  (("goal"
    :in-theory (enable read-reserved-area get-initial-bytes))))

(defthm
  disk-image-to-lofat-guard-lemma-10
  (implies
   (equal
    (mv-nth
     1
     (read-reserved-area
      fat32-in-memory
      (read-file-into-string2 image-path 0 nil state)))
    0)
   (equal
    (len
     (explode
      (read-file-into-string2
       image-path 16
       (+
        -16
        (*
         (bpb_bytspersec
          (mv-nth
           0
           (read-reserved-area
            fat32-in-memory
            (read-file-into-string2 image-path 0 nil state))))
         (bpb_rsvdseccnt
          (mv-nth
           0
           (read-reserved-area
            fat32-in-memory
            (read-file-into-string2 image-path 0 nil state))))))
       state)))
    (+
     -16
     (*
      (bpb_bytspersec
       (mv-nth
        0
        (read-reserved-area
         fat32-in-memory
         (read-file-into-string2 image-path 0 nil state))))
      (bpb_rsvdseccnt
       (mv-nth
        0
        (read-reserved-area
         fat32-in-memory
         (read-file-into-string2 image-path 0 nil state))))))))
  :hints (("goal" :in-theory (enable read-reserved-area))))

(defthm
  disk-image-to-lofat-guard-lemma-11
  (implies
   (<
    (len
     (explode
      (read-file-into-string2
       image-path 16
       (+
        -16
        (*
         (combine16u
          (char-code
           (nth 12
                (explode (read-file-into-string2 image-path 0 nil state))))
          (char-code
           (nth 11
                (explode (read-file-into-string2 image-path 0 nil state)))))
         (combine16u
          (char-code
           (nth 15
                (explode (read-file-into-string2 image-path 0 nil state))))
          (char-code
           (nth 14
                (explode (read-file-into-string2 image-path 0 nil state)))))))
       state)))
    (+
     -16
     (*
      (combine16u
       (char-code
        (nth 12
             (explode (read-file-into-string2 image-path 0 nil state))))
       (char-code
        (nth 11
             (explode (read-file-into-string2 image-path 0 nil state)))))
      (combine16u
       (char-code
        (nth 15
             (explode (read-file-into-string2 image-path 0 nil state))))
       (char-code
        (nth 14
             (explode (read-file-into-string2 image-path 0 nil state))))))))
   (equal
    (read-reserved-area
     fat32-in-memory
     (read-file-into-string2 image-path 0 nil state))
    (mv
     (update-bpb_bytspersec
      512
      (update-bpb_fatsz32
       1
       (update-bpb_numfats
        1
        (update-bpb_rsvdseccnt 1
                               (update-bpb_secperclus 1 fat32-in-memory)))))
     *EIO*)))
  :hints (("goal" :in-theory (enable get-initial-bytes read-reserved-area))))

(defthmd
  disk-image-to-lofat-guard-lemma-12
  (implies
   (and (stringp str)
        (<= *initialbytcnt* (len (explode str)))
        (<
         (combine16u
          (char-code
           (nth 12
                (explode str)))
          (char-code
           (nth 11
                (explode str))))
         512))
   (equal
    (read-reserved-area fat32-in-memory str)
    (mv
     (update-bpb_bytspersec
      512
      (update-bpb_fatsz32
       1
       (update-bpb_numfats
        1
        (update-bpb_rsvdseccnt
         1
         (update-bpb_secperclus 1 fat32-in-memory)))))
     *EIO*)))
  :hints
  (("goal"
    :in-theory (enable read-reserved-area get-initial-bytes))))

(defthm
  disk-image-to-lofat-guard-lemma-13
  (implies
   (and
    (<= 16
        (len (explode (read-file-into-string2 image-path 0 16 state))))
    (>=
     (combine16u
      (char-code
       (nth 12
            (explode (read-file-into-string2 image-path 0 nil state))))
      (char-code
       (nth 11
            (explode (read-file-into-string2 image-path 0 nil state)))))
     512)
    (>=
     (combine16u
      (char-code
       (nth 15
            (explode (read-file-into-string2 image-path 0 nil state))))
      (char-code
       (nth 14
            (explode (read-file-into-string2 image-path 0 nil state)))))
     1))
   (equal
    (read-reserved-area
     fat32-in-memory
     (read-file-into-string2
      image-path 0
      (*
       (combine16u
        (char-code
         (nth 12
              (explode (read-file-into-string2 image-path 0 nil state))))
        (char-code
         (nth 11
              (explode (read-file-into-string2 image-path 0 nil state)))))
       (combine16u
        (char-code
         (nth 15
              (explode (read-file-into-string2 image-path 0 nil state))))
        (char-code
         (nth 14
              (explode (read-file-into-string2 image-path 0 nil state))))))
      state))
    (read-reserved-area fat32-in-memory
                        (read-file-into-string2 image-path 0 nil state))))
  :hints
  (("goal"
    :in-theory (e/d nil
                    (read-reserved-area-correctness-1))
    :use (:instance read-reserved-area-correctness-1
                    (str (read-file-into-string2 image-path 0 nil state))))))

(defthm
  disk-image-to-lofat-guard-lemma-14
  (implies
   (equal
    (mv-nth
     1
     (read-reserved-area fat32-in-memory
                         (read-file-into-string2 image-path 0 nil state)))
    0)
   (equal
    (read-reserved-area
     fat32-in-memory
     (read-file-into-string2
      image-path 0
      (*
       (bpb_bytspersec
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state))))
       (bpb_rsvdseccnt
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state)))))
      state))
    (read-reserved-area fat32-in-memory
                        (read-file-into-string2 image-path 0 nil state))))
  :hints
  (("goal"
    :in-theory (e/d (read-reserved-area)
                    (disk-image-to-lofat-guard-lemma-13))
    :use disk-image-to-lofat-guard-lemma-13)))

;; Accumulated-persistence suggests disabling this rule, but really it only
;; gets tried in the main lemma, where we have to leave it enabled anyway. So
;; we might as well skip (or at least shrink) that one in-theory hint.
(defthm
  disk-image-to-lofat-guard-lemma-16
  (implies
   (and (stringp str)
        (<= *initialbytcnt* (len (explode str)))
        (<
         (*
          (combine16u
           (char-code
            (nth 12
                 (explode str)))
           (char-code
            (nth 11
                 (explode str))))
          (combine16u
           (char-code
            (nth 15
                 (explode str)))
           (char-code
            (nth 14
                 (explode str)))))
         16))
   (equal
    (read-reserved-area fat32-in-memory str)
    (mv
     (update-bpb_bytspersec
      512
      (update-bpb_fatsz32
       1
       (update-bpb_numfats
        1
        (update-bpb_rsvdseccnt
         1
         (update-bpb_secperclus 1 fat32-in-memory)))))
     *EIO*)))
  :hints
  (("goal"
    :in-theory (enable read-reserved-area get-initial-bytes))))

(defthm
  disk-image-to-lofat-guard-lemma-17
  (implies
   (equal
    (mv-nth
     1
     (read-reserved-area fat32-in-memory
                         (read-file-into-string2 image-path 0 nil state)))
    0)
   (iff
    (<
     (len
      (explode
       (read-file-into-string2
        image-path
        (*
         (bpb_bytspersec
          (mv-nth 0
                  (read-reserved-area
                   fat32-in-memory
                   (read-file-into-string2 image-path 0 nil state))))
         (bpb_rsvdseccnt
          (mv-nth 0
                  (read-reserved-area
                   fat32-in-memory
                   (read-file-into-string2 image-path 0 nil state)))))
        (*
         4
         (fat-entry-count
          (mv-nth 0
                  (read-reserved-area
                   fat32-in-memory
                   (read-file-into-string2 image-path 0 nil state)))))
        state)))
     (*
      4
      (fat-entry-count
       (mv-nth
        0
        (read-reserved-area fat32-in-memory
                            (read-file-into-string2 image-path 0 nil state))))))
    (<
     (len (explode (read-file-into-string2 image-path 0 nil state)))
     (+
      (* 4
         (fat-entry-count
          (mv-nth 0
                  (read-reserved-area
                   fat32-in-memory
                   (read-file-into-string2 image-path 0 nil state)))))
      (*
       (bpb_bytspersec
        (mv-nth
         0
         (read-reserved-area fat32-in-memory
                             (read-file-into-string2 image-path 0 nil state))))
       (bpb_rsvdseccnt
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state))))))))))

(defthm
  disk-image-to-lofat-guard-lemma-19
  (implies
   (and
    (equal
     (mv-nth
      1
      (read-reserved-area
       fat32-in-memory
       (read-file-into-string2 image-path 0 nil state)))
     0)
    (<=
     (+
      (*
       4
       (fat-entry-count
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state)))))
      (*
       (bpb_bytspersec
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state))))
       (bpb_rsvdseccnt
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state))))))
     (len
      (explode
       (read-file-into-string2 image-path 0 nil state)))))
   (equal
    (read-file-into-string2
     image-path
     (*
      (bpb_bytspersec
       (mv-nth
        0
        (read-reserved-area
         fat32-in-memory
         (read-file-into-string2 image-path 0 nil state))))
      (bpb_rsvdseccnt
       (mv-nth
        0
        (read-reserved-area
         fat32-in-memory
         (read-file-into-string2 image-path 0 nil state)))))
     (*
      4
      (fat-entry-count
       (mv-nth
        0
        (read-reserved-area
         fat32-in-memory
         (read-file-into-string2 image-path 0 nil state)))))
     state)
    (implode
     (take
      (*
       4
       (fat-entry-count
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state)))))
      (nthcdr
       (*
        (bpb_bytspersec
         (mv-nth
          0
          (read-reserved-area
           fat32-in-memory
           (read-file-into-string2 image-path 0 nil state))))
        (bpb_rsvdseccnt
         (mv-nth
          0
          (read-reserved-area
           fat32-in-memory
           (read-file-into-string2 image-path 0 nil state)))))
       (explode
        (read-file-into-string2 image-path 0 nil state)))))))
  :hints
  (("goal"
    :in-theory (enable take-of-nthcdr)
    :use
    (:theorem
     (equal
      (+
       (len
        (explode
         (mv-nth
          0
          (read-file-into-string1
           (mv-nth 0
                   (open-input-channel image-path
                                       :character state))
           (mv-nth 1
                   (open-input-channel image-path
                                       :character state))
           nil 1152921504606846975))))
       (*
        4
        (fat-entry-count
         (mv-nth
          0
          (read-reserved-area
           fat32-in-memory
           (mv-nth
            0
            (read-file-into-string1
             (mv-nth 0
                     (open-input-channel image-path
                                         :character state))
             (mv-nth 1
                     (open-input-channel image-path
                                         :character state))
             nil 1152921504606846975))))))
       (*
        -4
        (fat-entry-count
         (mv-nth
          0
          (read-reserved-area
           fat32-in-memory
           (mv-nth
            0
            (read-file-into-string1
             (mv-nth 0
                     (open-input-channel image-path
                                         :character state))
             (mv-nth 1
                     (open-input-channel image-path
                                         :character state))
             nil 1152921504606846975)))))))
      (len
       (explode
        (mv-nth
         0
         (read-file-into-string1
          (mv-nth 0
                  (open-input-channel image-path
                                      :character state))
          (mv-nth 1
                  (open-input-channel image-path
                                      :character state))
          nil 1152921504606846975)))))))))

(defthm
  disk-image-to-lofat-guard-lemma-21
  (equal
   (+
    (-
     (*
      4
      (fat-entry-count
       (mv-nth 0
               (read-reserved-area fat32-in-memory str)))))
    (* (bpb_bytspersec
        (mv-nth 0
                (read-reserved-area fat32-in-memory str)))
       (bpb_rsvdseccnt
        (mv-nth 0
                (read-reserved-area fat32-in-memory str))))
    (-
     (*
      (bpb_bytspersec
       (mv-nth 0
               (read-reserved-area fat32-in-memory str)))
      (bpb_rsvdseccnt
       (mv-nth 0
               (read-reserved-area fat32-in-memory str)))))
    (* (bpb_bytspersec
        (mv-nth 0
                (read-reserved-area fat32-in-memory str)))
       (bpb_fatsz32
        (mv-nth 0
                (read-reserved-area fat32-in-memory str)))
       (bpb_numfats
        (mv-nth 0
                (read-reserved-area fat32-in-memory str)))))
   (+
    (-
     (*
      4
      (fat-entry-count
       (mv-nth 0
               (read-reserved-area fat32-in-memory str)))))
    (*
     (bpb_bytspersec
      (mv-nth 0
              (read-reserved-area fat32-in-memory str)))
     (bpb_fatsz32
      (mv-nth 0
              (read-reserved-area fat32-in-memory str)))
     (bpb_numfats
      (mv-nth 0
              (read-reserved-area fat32-in-memory str)))))))

(defthm
  disk-image-to-lofat-guard-lemma-25
  (implies
   (stringp (read-file-into-string2 image-path 0 nil state))
   (iff
    (stringp
     (read-file-into-string2
      image-path
      (+
       (*
        4
        (fat-entry-count
         (mv-nth
          0
          (read-reserved-area
           fat32-in-memory
           (read-file-into-string2 image-path 0 nil state)))))
       (*
        (bpb_bytspersec
         (mv-nth
          0
          (read-reserved-area
           fat32-in-memory
           (read-file-into-string2 image-path 0 nil state))))
        (bpb_rsvdseccnt
         (mv-nth
          0
          (read-reserved-area
           fat32-in-memory
           (read-file-into-string2 image-path 0 nil state))))))
      (+
       (-
        (*
         4
         (fat-entry-count
          (mv-nth
           0
           (read-reserved-area
            fat32-in-memory
            (read-file-into-string2 image-path 0 nil state))))))
       (*
        (bpb_bytspersec
         (mv-nth
          0
          (read-reserved-area
           fat32-in-memory
           (read-file-into-string2 image-path 0 nil state))))
        (bpb_fatsz32
         (mv-nth
          0
          (read-reserved-area
           fat32-in-memory
           (read-file-into-string2 image-path 0 nil state))))
        (bpb_numfats
         (mv-nth
          0
          (read-reserved-area
           fat32-in-memory
           (read-file-into-string2 image-path 0 nil state))))))
      state))
    (<=
     (+
      (*
       4
       (fat-entry-count
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state)))))
      (*
       (bpb_bytspersec
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state))))
       (bpb_rsvdseccnt
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state))))))
     (length
      (read-file-into-string2 image-path 0 nil state))))))

(defthm
  disk-image-to-lofat-guard-lemma-27
  (implies
   (and
    (<=
     0
     (+
      (* 4
         (fat-entry-count
          (mv-nth 0
                  (read-reserved-area
                   fat32-in-memory
                   (read-file-into-string2 image-path 0 nil state)))))
      (*
       (bpb_bytspersec
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state))))
       (bpb_rsvdseccnt
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state)))))))
    (<=
     (+
      (* 4
         (fat-entry-count
          (mv-nth 0
                  (read-reserved-area
                   fat32-in-memory
                   (read-file-into-string2 image-path 0 nil state)))))
      (*
       (bpb_bytspersec
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state))))
       (bpb_rsvdseccnt
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state))))))
     (len (explode (read-file-into-string2 image-path 0 nil state)))))
   (iff
    (<
     (len
      (explode
       (read-file-into-string2
        image-path
        (+
         (*
          4
          (fat-entry-count
           (mv-nth 0
                   (read-reserved-area
                    fat32-in-memory
                    (read-file-into-string2 image-path 0 nil state)))))
         (*
          (bpb_bytspersec
           (mv-nth 0
                   (read-reserved-area
                    fat32-in-memory
                    (read-file-into-string2 image-path 0 nil state))))
          (bpb_rsvdseccnt
           (mv-nth 0
                   (read-reserved-area
                    fat32-in-memory
                    (read-file-into-string2 image-path 0 nil state))))))
        (+
         (-
          (*
           4
           (fat-entry-count
            (mv-nth 0
                    (read-reserved-area
                     fat32-in-memory
                     (read-file-into-string2 image-path 0 nil state))))))
         (*
          (bpb_bytspersec
           (mv-nth 0
                   (read-reserved-area
                    fat32-in-memory
                    (read-file-into-string2 image-path 0 nil state))))
          (bpb_fatsz32
           (mv-nth 0
                   (read-reserved-area
                    fat32-in-memory
                    (read-file-into-string2 image-path 0 nil state))))
          (bpb_numfats
           (mv-nth 0
                   (read-reserved-area
                    fat32-in-memory
                    (read-file-into-string2 image-path 0 nil state))))))
        state)))
     (+
      (-
       (*
        4
        (fat-entry-count
         (mv-nth 0
                 (read-reserved-area
                  fat32-in-memory
                  (read-file-into-string2 image-path 0 nil state))))))
      (*
       (bpb_bytspersec
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state))))
       (bpb_fatsz32
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state))))
       (bpb_numfats
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state)))))))
    (<
     (len (explode (read-file-into-string2 image-path 0 nil state)))
     (+
      (* (bpb_bytspersec
          (mv-nth 0
                  (read-reserved-area
                   fat32-in-memory
                   (read-file-into-string2 image-path 0 nil state))))
         (bpb_rsvdseccnt
          (mv-nth 0
                  (read-reserved-area
                   fat32-in-memory
                   (read-file-into-string2 image-path 0 nil state)))))
      (*
       (bpb_bytspersec
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state))))
       (bpb_fatsz32
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state))))
       (bpb_numfats
        (mv-nth 0
                (read-reserved-area
                 fat32-in-memory
                 (read-file-into-string2 image-path 0 nil state))))))))))

(defthm
  disk-image-to-lofat-guard-lemma-28
  (implies
   (stringp (read-file-into-string2 image-path 0 nil state))
   (iff
    (stringp
     (read-file-into-string2
      image-path
      (*
       (bpb_bytspersec
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state))))
       (bpb_rsvdseccnt
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state)))))
      (*
       4
       (fat-entry-count
        (mv-nth
         0
         (read-reserved-area
          fat32-in-memory
          (read-file-into-string2 image-path 0 nil state)))))
      state))
    (<=
     (*
      (bpb_bytspersec
       (mv-nth
        0
        (read-reserved-area
         fat32-in-memory
         (read-file-into-string2 image-path 0 nil state))))
      (bpb_rsvdseccnt
       (mv-nth
        0
        (read-reserved-area
         fat32-in-memory
         (read-file-into-string2 image-path 0 nil state)))))
     (len
      (explode
       (read-file-into-string2 image-path 0 nil state)))))))

(defthm
  disk-image-to-lofat-guard-lemma-29
  (implies
   (and
    (stringp (read-file-into-string2 image-path 0 nil state))
    (equal
     (len
      (explode
       (read-file-into-string2
        image-path
        (*
         (bpb_bytspersec
          (mv-nth 0
                  (read-reserved-area
                   fat32-in-memory
                   (read-file-into-string2 image-path 0 nil state))))
         (bpb_rsvdseccnt
          (mv-nth 0
                  (read-reserved-area
                   fat32-in-memory
                   (read-file-into-string2 image-path 0 nil state)))))
        (*
         4
         (fat-entry-count
          (mv-nth 0
                  (read-reserved-area
                   fat32-in-memory
                   (read-file-into-string2 image-path 0 nil state)))))
        state)))
     (* 4
        (fat-entry-count
         (mv-nth 0
                 (read-reserved-area
                  fat32-in-memory
                  (read-file-into-string2 image-path 0 nil state))))))
    (>=
     (len
      (explode
       (read-file-into-string2 image-path 0 nil state)))
     (*
      (bpb_bytspersec
       (mv-nth
        0
        (read-reserved-area
         fat32-in-memory
         (read-file-into-string2 image-path 0 nil state))))
      (bpb_rsvdseccnt
       (mv-nth
        0
        (read-reserved-area
         fat32-in-memory
         (read-file-into-string2 image-path 0 nil state)))))))
   (<=
    (+
     (* 4
        (fat-entry-count
         (mv-nth 0
                 (read-reserved-area
                  fat32-in-memory
                  (read-file-into-string2 image-path 0 nil state)))))
     (*
      (bpb_bytspersec
       (mv-nth
        0
        (read-reserved-area fat32-in-memory
                            (read-file-into-string2 image-path 0 nil state))))
      (bpb_rsvdseccnt
       (mv-nth 0
               (read-reserved-area
                fat32-in-memory
                (read-file-into-string2 image-path 0 nil state))))))
    (len (explode (read-file-into-string2 image-path 0 nil state)))))
  :rule-classes :linear)

(defun
  disk-image-to-lofat
  (fat32-in-memory image-path state)
  (declare
   (xargs
    :guard (and (stringp image-path)
                (fat32-in-memoryp fat32-in-memory))
    :guard-hints
    (("goal"
      :in-theory
      (e/d (string-to-lofat
            disk-image-to-lofat-guard-lemma-12)
           (string-append
            read-file-into-string2
            ;; The following came from accumulated-persistence results.
            (:rewrite str::explode-when-not-stringp)
            (:definition update-fat)
            (:rewrite nth-of-make-character-list)
            (:rewrite fat32-filename-p-correctness-1)))))
    :stobjs (fat32-in-memory state)))
  ;; The idea behind this MBE is that slurping in the whole string at once is
  ;; causing inefficiencies in terms of memory allocated for all these subseq
  ;; operations. For instance, for one disk image of size 64 MB with 69441
  ;; clusters, each subseq operation allocated 4,112 bytes and the whole
  ;; update-data-region operation allocated 496,573,872 bytes. This is several
  ;; times the size of the disk, and is probably the reason why we can't
  ;; execute for disks of size 300 MB or more.
  (mbe
   ;; It's a good idea to keep the spec simple.
   :logic (b* ((str (read-file-into-string image-path))
               ((unless (and (stringp str)
                             (>= (length str) *initialbytcnt*)))
                (mv fat32-in-memory *EIO*)))
            (string-to-lofat fat32-in-memory str))
   ;; This b* form pretty closely follows the structure of
   ;; string-to-lofat.
   :exec
   (b*
       ((initial-bytes-str
         (read-file-into-string image-path
                                :bytes *initialbytcnt*))
        ((unless (and (stringp initial-bytes-str)
                      (>= (length initial-bytes-str)
                          *initialbytcnt*)))
         (mv fat32-in-memory *EIO*))
        (fat32-in-memory (update-bpb_secperclus 1 fat32-in-memory))
        (fat32-in-memory (update-bpb_rsvdseccnt 1 fat32-in-memory))
        (fat32-in-memory (update-bpb_numfats 1 fat32-in-memory))
        (fat32-in-memory (update-bpb_fatsz32 1 fat32-in-memory))
        (fat32-in-memory
         (update-bpb_bytspersec 512 fat32-in-memory))
        (tmp_bytspersec
         (combine16u (char-code (char initial-bytes-str 12))
                     (char-code (char initial-bytes-str 11))))
        (tmp_rsvdseccnt
         (combine16u (char-code (char initial-bytes-str 15))
                     (char-code (char initial-bytes-str 14))))
        (tmp_rsvdbytcnt (* tmp_rsvdseccnt tmp_bytspersec))
        ((unless (and (>= tmp_bytspersec 512)
                      (>= tmp_rsvdseccnt 1)
                      (>= tmp_rsvdbytcnt *initialbytcnt*)))
         (mv fat32-in-memory *EIO*))
        (remaining-rsvdbyts-str
         (read-file-into-string
          image-path
          :start *initialbytcnt*
          :bytes (- tmp_rsvdbytcnt *initialbytcnt*)))
        ((unless (and (stringp remaining-rsvdbyts-str)
                      (>= (length remaining-rsvdbyts-str)
                          (- tmp_rsvdbytcnt *initialbytcnt*))))
         (mv fat32-in-memory *EIO*))
        ((mv fat32-in-memory error-code)
         (read-reserved-area
          fat32-in-memory
          (string-append initial-bytes-str
                         remaining-rsvdbyts-str)))
        ((unless (equal error-code 0))
         (mv fat32-in-memory error-code))
        (fat-read-size (fat-entry-count fat32-in-memory))
        ((unless (integerp (/ (* (bpb_fatsz32 fat32-in-memory)
                                 (bpb_bytspersec fat32-in-memory))
                              4)))
         (mv fat32-in-memory *EIO*))
        (data-byte-count (* (count-of-clusters fat32-in-memory)
                            (cluster-size fat32-in-memory)))
        ((unless (> data-byte-count 0))
         (mv fat32-in-memory *EIO*))
        (tmp_bytspersec (bpb_bytspersec fat32-in-memory))
        (tmp_init (* tmp_bytspersec
                     (+ (bpb_rsvdseccnt fat32-in-memory)
                        (* (bpb_numfats fat32-in-memory)
                           (bpb_fatsz32 fat32-in-memory)))))
        (fat32-in-memory
         (resize-fat fat-read-size fat32-in-memory))
        (fat-string
         (read-file-into-string image-path
                                :start tmp_rsvdbytcnt
                                :bytes (* fat-read-size 4)))
        ((unless (and (<= (* fat-read-size 4)
                          (length fat-string))
                      (unsigned-byte-p 48 fat-read-size)))
         (mv fat32-in-memory *EIO*))
        (fat32-in-memory (update-fat fat32-in-memory
                                     fat-string fat-read-size))
        (fat32-in-memory
         (resize-data-region (count-of-clusters fat32-in-memory)
                             fat32-in-memory))
        ;; This test doesn't accomplish much other than getting the extra
        ;; copies of the file allocation table out of the way.
        ((unless
             (and
              (<= (data-region-length fat32-in-memory)
                  (- *ms-bad-cluster*
                     *ms-first-data-cluster*))
              (>=
               (length
                (read-file-into-string
                 image-path
                 :start (+ tmp_rsvdbytcnt (* fat-read-size 4))
                 :bytes (- tmp_init
                           (+ tmp_rsvdbytcnt (* fat-read-size 4)))))
               (- tmp_init
                  (+ tmp_rsvdbytcnt (* fat-read-size 4))))))
         (mv fat32-in-memory *EIO*)))
     (update-data-region-from-disk-image
      fat32-in-memory
      (data-region-length fat32-in-memory)
      state
      tmp_init
      image-path))))

(defund
  get-clusterchain
  (fat32-in-memory masked-current-cluster length)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :measure (nfix length)
    :guard (and (lofat-fs-p fat32-in-memory)
                (fat32-masked-entry-p masked-current-cluster)
                (natp length)
                (>= masked-current-cluster
                    *ms-first-data-cluster*)
                (< masked-current-cluster
                   (+ (count-of-clusters fat32-in-memory)
                      *ms-first-data-cluster*)))))
  (let
   ((cluster-size (cluster-size fat32-in-memory)))
   (if
    (or (zp length) (zp cluster-size))
    (mv nil (- *eio*))
    (let
     ((masked-next-cluster
       (fat32-entry-mask
        (if (mbt (< (nfix masked-current-cluster)
                    (nfix (+ (count-of-clusters fat32-in-memory)
                             *ms-first-data-cluster*))))
            (fati masked-current-cluster fat32-in-memory)
            nil))))
     (if
      (< masked-next-cluster
         *ms-first-data-cluster*)
      (mv (list masked-current-cluster)
          (- *eio*))
      (if
       (or
        (fat32-is-eof masked-next-cluster)
        (>=
         masked-next-cluster
         (mbe
          :exec (+ (count-of-clusters fat32-in-memory)
                   *ms-first-data-cluster*)
          :logic (nfix (+ (count-of-clusters fat32-in-memory)
                          *ms-first-data-cluster*)))))
       (mv (list masked-current-cluster) 0)
       (b*
           (((mv tail-index-list tail-error)
             (get-clusterchain fat32-in-memory masked-next-cluster
                               (nfix (- length cluster-size)))))
         (mv (list* masked-current-cluster tail-index-list)
             tail-error))))))))

(defund-nx
  effective-fat (fat32-in-memory)
  (declare
   (xargs :stobjs fat32-in-memory
          :guard (lofat-fs-p fat32-in-memory)
          :guard-hints
          (("goal" :in-theory (enable fat32-in-memoryp)))))
  (take (+ (count-of-clusters fat32-in-memory)
           *ms-first-data-cluster*)
        (nth *fati* fat32-in-memory)))

(defthm len-of-effective-fat
  (equal (len (effective-fat fat32-in-memory))
         (nfix (+ (count-of-clusters fat32-in-memory)
                  *ms-first-data-cluster*)))
  :hints (("goal" :in-theory (enable effective-fat))))

(defthm
  fat32-entry-list-p-of-effective-fat
  (implies (and (fat32-in-memoryp fat32-in-memory)
                (<= (+ (count-of-clusters fat32-in-memory)
                       *ms-first-data-cluster*)
                    (fat-length fat32-in-memory)))
           (fat32-entry-list-p (effective-fat fat32-in-memory)))
  :hints
  (("goal" :in-theory (enable effective-fat
                              fat-length fat32-in-memoryp)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies (lofat-fs-p fat32-in-memory)
             (fat32-entry-list-p (effective-fat fat32-in-memory))))))

(defthm
  nth-of-effective-fat
  (equal (nth n (effective-fat fat32-in-memory))
         (if (< (nfix n)
                (nfix (+ (count-of-clusters fat32-in-memory)
                         *ms-first-data-cluster*)))
             (fati n fat32-in-memory)
             nil))
  :hints (("goal" :in-theory (enable fati effective-fat nth))))

(defthm
  effective-fat-of-update-data-regioni
  (equal
   (effective-fat (update-data-regioni i v fat32-in-memory))
   (effective-fat fat32-in-memory))
  :hints (("goal" :in-theory (enable effective-fat))))

(defthm
  effective-fat-of-update-fati
  (equal (effective-fat (update-fati i v fat32-in-memory))
         (if (< (nfix i)
                (+ (count-of-clusters fat32-in-memory)
                   *ms-first-data-cluster*))
             (update-nth i v (effective-fat fat32-in-memory))
             (effective-fat fat32-in-memory)))
  :hints (("goal" :in-theory (enable effective-fat update-fati)
           :do-not-induct t)))

;; Avoid a subinduction
(defthmd
  get-clusterchain-alt-lemma-1
  (implies
   (and (not (zp length))
        (integerp (cluster-size fat32-in-memory))
        (< 0 (cluster-size fat32-in-memory))
        (integerp masked-current-cluster)
        (<= 0 masked-current-cluster)
        (<= (+ 2 (count-of-clusters fat32-in-memory))
            masked-current-cluster))
   (equal (fat32-build-index-list
           (take (+ 2 (count-of-clusters fat32-in-memory))
                 (nth *fati* fat32-in-memory))
           masked-current-cluster
           length (cluster-size fat32-in-memory))
          (mv (list masked-current-cluster)
              (- *eio*)))))

(defthm
  get-clusterchain-alt
  (equal (get-clusterchain fat32-in-memory
                           masked-current-cluster length)
         (fat32-build-index-list
          (effective-fat fat32-in-memory)
          masked-current-cluster
          length (cluster-size fat32-in-memory)))
  :rule-classes :definition
  :hints
  (("goal" :in-theory (enable get-clusterchain
                              fati fat-length effective-fat nth
                              get-clusterchain-alt-lemma-1))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defun
      get-contents-from-clusterchain
      (fat32-in-memory clusterchain file-size)
    (declare
     (xargs
      :stobjs (fat32-in-memory)
      :guard
      (and
       (lofat-fs-p fat32-in-memory)
       (equal (data-region-length fat32-in-memory)
              (count-of-clusters fat32-in-memory))
       (fat32-masked-entry-list-p clusterchain)
       (natp file-size)
       (bounded-nat-listp clusterchain
                          (count-of-clusters fat32-in-memory))
       (lower-bounded-integer-listp
        clusterchain *ms-first-data-cluster*))))
    (if
        (atom clusterchain)
        ""
      (let*
          ((cluster-size (cluster-size fat32-in-memory))
           (masked-current-cluster (car clusterchain)))
        (concatenate
         'string
         (subseq
          (data-regioni
           (nfix (- masked-current-cluster *ms-first-data-cluster*))
           fat32-in-memory)
          0
          (min file-size cluster-size))
         (get-contents-from-clusterchain
          fat32-in-memory (cdr clusterchain)
          (nfix (- file-size cluster-size)))))))

  (defthm
    stringp-of-get-contents-from-clusterchain
    (stringp
     (get-contents-from-clusterchain
      fat32-in-memory clusterchain file-size))
    :rule-classes :type-prescription)

  (defund
    get-clusterchain-contents
    (fat32-in-memory masked-current-cluster length)
    (declare
     (xargs
      :stobjs fat32-in-memory
      :measure (nfix length)
      :guard (and (lofat-fs-p fat32-in-memory)
                  (equal (data-region-length fat32-in-memory)
                         (count-of-clusters fat32-in-memory))
                  (fat32-masked-entry-p masked-current-cluster)
                  (natp length)
                  (>= masked-current-cluster
                      *ms-first-data-cluster*)
                  (< masked-current-cluster
                     (+ (count-of-clusters fat32-in-memory)
                        *ms-first-data-cluster*)))
      :verify-guards nil))
    (b*
        ((cluster-size (cluster-size fat32-in-memory))
         ((unless (and (not (zp length))
                       (not (zp cluster-size))
                       (>= masked-current-cluster
                           *ms-first-data-cluster*)))
          (mv "" (- *eio*)))
         (current-cluster-contents
          (str-fix
           (data-regioni (- masked-current-cluster 2) fat32-in-memory)))
         (masked-next-cluster
          (fat32-entry-mask
           ;; This mbt (must be true) form was inserted in order to comport
           ;; with our current definition of effective-fat, which is implicitly
           ;; used in the rule get-clusterchain-contents-correctness-1.
           (if (mbt (< (nfix masked-current-cluster)
                       (nfix (+ (count-of-clusters fat32-in-memory)
                                *ms-first-data-cluster*))))
               (fati masked-current-cluster fat32-in-memory)
             nil)))
         ((unless (>= masked-next-cluster
                      *ms-first-data-cluster*))
          (mv (subseq current-cluster-contents 0 (min length cluster-size))
              (- *eio*)))
         ((unless (and (not (fat32-is-eof masked-next-cluster))
                       (< masked-next-cluster
                          (+ (count-of-clusters fat32-in-memory)
                             *ms-first-data-cluster*))))
          (mv (subseq current-cluster-contents 0 (min length cluster-size)) 0))
         ((mv tail-string tail-error)
          (get-clusterchain-contents
           fat32-in-memory masked-next-cluster
           (nfix (- length cluster-size))))
         ((unless (equal tail-error 0))
          (mv "" (- *eio*))))
      (mv (concatenate 'string
                       current-cluster-contents
                       tail-string)
          0)))

  (defthm stringp-of-get-clusterchain-contents
    (stringp
     (mv-nth 0
             (get-clusterchain-contents
              fat32-in-memory masked-current-cluster length)))
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (enable get-clusterchain-contents)) ))

  (verify-guards get-clusterchain-contents))

(defthm
  get-clusterchain-contents-correctness-2
  (implies
   (>= masked-current-cluster
       *ms-first-data-cluster*)
   (equal (mv-nth 1
                  (fat32-build-index-list
                   (effective-fat fat32-in-memory)
                   masked-current-cluster
                   length (cluster-size fat32-in-memory)))
          (mv-nth 1
                  (get-clusterchain-contents
                   fat32-in-memory
                   masked-current-cluster length))))
  :hints
  (("goal" :in-theory
    (e/d (fat-length fati effective-fat
                     nth get-clusterchain-contents)))))

(defthm
  get-contents-from-clusterchain-of-update-data-regioni
  (implies
   (and (integerp file-size)
        (lofat-fs-p fat32-in-memory)
        (equal (data-region-length fat32-in-memory)
               (count-of-clusters fat32-in-memory))
        (natp i)
        (not (member-equal (+ i *ms-first-data-cluster*)
                           clusterchain))
        (lower-bounded-integer-listp
         clusterchain *ms-first-data-cluster*))
   (equal
    (get-contents-from-clusterchain
     (update-data-regioni i v fat32-in-memory)
     clusterchain file-size)
    (get-contents-from-clusterchain fat32-in-memory
                                    clusterchain file-size))))

(defthm
  get-clusterchain-contents-correctness-1
  (implies
   (and
    (fat32-masked-entry-p masked-current-cluster)
    (lofat-fs-p fat32-in-memory)
    (equal
     (mv-nth
      1
      (get-clusterchain-contents fat32-in-memory
                                 masked-current-cluster length))
     0))
   (equal
    (get-contents-from-clusterchain
     fat32-in-memory
     (mv-nth 0
             (get-clusterchain fat32-in-memory
                               masked-current-cluster length))
     length)
    (mv-nth 0
            (get-clusterchain-contents
             fat32-in-memory
             masked-current-cluster length))))
  :hints
  (("goal" :in-theory (enable by-slice-you-mean-the-whole-cake-2
                              get-clusterchain-contents)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and
      (fat32-masked-entry-p masked-current-cluster)
      (>= masked-current-cluster
          *ms-first-data-cluster*)
      (lofat-fs-p fat32-in-memory)
      (equal
       (mv-nth 1
               (fat32-build-index-list
                (effective-fat fat32-in-memory)
                masked-current-cluster
                length (cluster-size fat32-in-memory)))
       0))
     (equal
      (get-contents-from-clusterchain
       fat32-in-memory
       (mv-nth 0
               (fat32-build-index-list
                (effective-fat fat32-in-memory)
                masked-current-cluster
                length (cluster-size fat32-in-memory)))
       length)
      (mv-nth 0
              (get-clusterchain-contents
               fat32-in-memory
               masked-current-cluster length)))))))

(defthm
  get-clusterchain-contents-correctness-3
  (equal
   (mv
    (mv-nth
     0
     (get-clusterchain-contents fat32-in-memory
                                masked-current-cluster length))
    (mv-nth
     1
     (get-clusterchain-contents fat32-in-memory
                                masked-current-cluster length)))
   (get-clusterchain-contents fat32-in-memory
                              masked-current-cluster length))
  :hints (("Goal" :in-theory (enable get-clusterchain-contents)) ))

(defthm
  length-of-get-clusterchain-contents
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (natp length))
   (<=
    (len (explode (mv-nth 0
                          (get-clusterchain-contents
                           fat32-in-memory
                           masked-current-cluster length))))
    length))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable get-clusterchain-contents)) ))

;; The following is not a theorem, because we took our error codes, more or
;; less, from fs/fat/cache.c, and there the length is not taken into account
;; while returning error codes (or not). Thus, it's possible to return an error
;; code of 0 without conforming to the length.
;; (defthm len-of-get-clusterchain-contents
;;   (b*
;;       (((mv contents error-code)
;;         (get-clusterchain-contents fat32-in-memory masked-current-cluster length)))
;;     (implies
;;      (equal error-code 0)
;;      (equal (length contents) length))))

;; Here's the idea: while transforming from M2 to M1,
;; - we are not going to to take directory entries which are deleted
;; - we are not going to take dot or dotdot entries
(defund
  useless-dir-ent-p (dir-ent)
  (declare
   (xargs
    :guard (dir-ent-p dir-ent)
    :guard-hints
    (("goal" :in-theory (e/d (dir-ent-p dir-ent-first-cluster)
                             (unsigned-byte-p))))))
  (or
   ;; the byte #xe5 marks deleted files, according to the spec
   (equal (nth 0 dir-ent) #xe5)
   (equal (dir-ent-filename dir-ent)
          *current-dir-fat32-name*)
   (equal (dir-ent-filename dir-ent)
          *parent-dir-fat32-name*)))

(defthm
  useless-dir-ent-p-of-dir-ent-install-directory-bit
  (implies
   (dir-ent-p dir-ent)
   (equal (useless-dir-ent-p
           (dir-ent-install-directory-bit dir-ent val))
          (useless-dir-ent-p dir-ent)))
  :hints
  (("goal"
    :in-theory (enable dir-ent-install-directory-bit
                       useless-dir-ent-p dir-ent-filename))))

(defthm
  useless-dir-ent-p-of-dir-ent-set-filename
  (implies (and (fat32-filename-p filename)
                (dir-ent-p dir-ent))
           (not (useless-dir-ent-p
                 (dir-ent-set-filename dir-ent filename))))
  :hints (("goal" :in-theory (enable useless-dir-ent-p))))

(defund
  make-dir-ent-list (dir-contents)
  (declare
   (xargs
    :guard (unsigned-byte-listp 8 dir-contents)
    :measure (len dir-contents)
    :guard-hints (("goal" :in-theory (enable dir-ent-p)))))
  (b* (((when (< (len dir-contents)
                 *ms-dir-ent-length*))
        nil)
       (dir-ent
        (mbe
         :exec (take *ms-dir-ent-length* dir-contents)
         :logic (dir-ent-fix (take *ms-dir-ent-length* dir-contents))))
       ;; From page 24 of the specification: "If DIR_Name[0] == 0x00, then the
       ;; directory entry is free (same as for 0xE5), and there are no
       ;; allocated directory entries after this one (all of the DIR_Name[0]
       ;; bytes in all of the entries after this one are also set to 0). The
       ;; special 0 value, rather than the 0xE5 value, indicates to FAT file
       ;; system driver code that the rest of the entries in this directory do
       ;; not need to be examined because they are all free."
       ((when (equal (nth 0 dir-ent) 0)) nil)
       ((when (useless-dir-ent-p dir-ent))
        (make-dir-ent-list
         (nthcdr *ms-dir-ent-length* dir-contents))))
    (list* dir-ent
           (make-dir-ent-list
            (nthcdr *ms-dir-ent-length* dir-contents)))))

(defund useful-dir-ent-list-p (dir-ent-list)
  (declare (xargs :guard t))
  (if (atom dir-ent-list)
      (equal dir-ent-list nil)
      (and (dir-ent-p (car dir-ent-list))
           (not (equal (nth 0 (car dir-ent-list)) 0))
           (not (useless-dir-ent-p (car dir-ent-list)))
           (useful-dir-ent-list-p (cdr dir-ent-list)))))

(defthm dir-ent-list-p-when-useful-dir-ent-list-p
  (implies (useful-dir-ent-list-p dir-ent-list)
           (dir-ent-list-p dir-ent-list))
  :hints
  (("Goal" :in-theory (enable useful-dir-ent-list-p))))

(defthm
  useful-dir-ent-list-p-of-make-dir-ent-list
  (useful-dir-ent-list-p (make-dir-ent-list dir-contents))
  :hints
  (("goal"
    :in-theory (enable make-dir-ent-list useful-dir-ent-list-p))))

(defthm
  useful-dir-ent-list-p-of-cdr
  (implies (useful-dir-ent-list-p dir-ent-list)
           (useful-dir-ent-list-p (cdr dir-ent-list)))
  :hints (("goal" :in-theory (enable useful-dir-ent-list-p))))

;; Here's the idea behind this recursion: A loop could occur on a badly formed
;; FAT32 volume which has a cycle in its directory structure (for instance, if
;; / and /tmp/ were to point to the same cluster as their initial cluster.)
;; This loop could be stopped most cleanly by maintaining a list of all
;; clusters which could be visited, and checking them off as we visit more
;; entries. Then, we would detect a second visit to the same cluster, and
;; terminate with an error condition . Only otherwise would we make a recursive
;; call, and our measure - the length of the list of unvisited clusters - would
;; decrease.

;; This would probably impose performance penalties, and so there's a better
;; way which does not (good!), and also does not cleanly detect cycles in the
;; directory structure (bad.) Still, it returns exactly the same result for
;; good FAT32 volumes, so it's acceptable. In this helper function, we set our
;; measure to be entry-limit, an upper bound on the number of entries we can
;; visit, and decrement every time we visit a new entry. In the main function,
;; we count the total number of visitable directory entries, by dividing the
;; entire length of the data region by *ms-dir-ent-length*, and set that as the
;; upper limit. This makes sure that we aren't disallowing any legitimate FAT32
;; volumes which just happen to be full of directories.

;; We're adding a return value for collecting all these clusterchains... again,
;; for proof purposes. We're also adding a return value, to signal an error
;; when we run out of entries.
(defund
  lofat-to-hifat-helper
  (fat32-in-memory dir-ent-list entry-limit)
  (declare (xargs :measure (nfix entry-limit)
                  :guard (and (natp entry-limit)
                              (useful-dir-ent-list-p dir-ent-list)
                              (lofat-fs-p fat32-in-memory))
                  :verify-guards nil
                  :stobjs (fat32-in-memory)))
  (b*
      (;; entry-limit is the loop stopper, kind of - we know that in a
       ;; filesystem instance without any looping clusterchains (where, for
       ;; instance, 2 points to 3 and 3 points to 2), we can't have more
       ;; entries than the total number of entries possible if the data region
       ;; was fully packed with directory entries. So, we begin with that
       ;; number as the entry count, and keep decreasing in recursive
       ;; calls. This means we also decrease when we find an entry for a
       ;; deleted file, or a "." or ".."  entry, even though we won't include
       ;; these in the filesystem instance. The measure must strictly decrease.
       ;; If there isn't a full directory entry in dir-contents, we're done.
       ((when
            (atom dir-ent-list))
        (mv nil 0 nil 0))
       ((when (zp entry-limit))
        (mv nil 0 nil *EIO*))
       (dir-ent
        (car dir-ent-list))
       ;; Learn about the file we're looking at.
       (first-cluster (dir-ent-first-cluster dir-ent))
       (filename (dir-ent-filename dir-ent))
       (directory-p
        (dir-ent-directory-p dir-ent))
       ;; From page 36 of the specification: "Similarly, a FAT file system
       ;; driver must not allow a directory (a file that is actually a
       ;; container for other files) to be larger than 65,536 * 32 (2,097,152)
       ;; bytes." Note, this is the length value we'll use to traverse the
       ;; clusterchain, not the value we'll store in the directory entry -
       ;; that's 0, per the spec.
       (length (if directory-p
                   *ms-max-dir-size*
                 (dir-ent-file-size dir-ent)))
       ((mv contents error-code)
        (if
            ;; This clause is intended to make sure we don't try to explore the
            ;; contents of an empty file; that would cause a guard
            ;; violation. Unlike deleted file entries and dot or dotdot
            ;; entries, though, these will be present in the m1 instance.
            (or (< first-cluster
                   *ms-first-data-cluster*)
                (>=
                 first-cluster
                 (+ (count-of-clusters fat32-in-memory)
                    *ms-first-data-cluster*)))
            (mv "" 0)
            (get-clusterchain-contents fat32-in-memory
                                       first-cluster
                                       length)))
       ((mv clusterchain &)
        (if
            ;; This clause is intended to make sure we don't try to explore the
            ;; contents of an empty file; that would cause a guard
            ;; violation. Unlike deleted file entries and dot or dotdot
            ;; entries, though, these will be present in the m1 instance.
            (or (< first-cluster
                   *ms-first-data-cluster*)
                (>=
                 first-cluster
                 (+ (count-of-clusters fat32-in-memory)
                    *ms-first-data-cluster*)))
            (mv nil 0)
            (get-clusterchain fat32-in-memory
                              first-cluster
                              length)))
       ;; head-entry-count and head-clusterchain-list, here, do not include the
       ;; entry or clusterchain respectively for the head itself. Those will be
       ;; added at the end.
       ((mv head head-entry-count head-clusterchain-list head-error-code)
        (if directory-p
            (lofat-to-hifat-helper
             fat32-in-memory
             (make-dir-ent-list (string=>nats contents))
             (- entry-limit 1))
          (mv contents 0 nil 0)))
       ;; get-clusterchain-contents returns either 0 or a negative error code,
       ;; which is not what we want...
       (error-code
        (if (equal error-code 0)
            head-error-code
          *EIO*))
       ;; we want entry-limit to serve both as a measure and an upper
       ;; bound on how many entries are found.
       (tail-entry-limit (nfix (- entry-limit
                                  (+ 1 (nfix head-entry-count)))))
       ((mv tail tail-entry-count tail-clusterchain-list tail-error-code)
        (lofat-to-hifat-helper
         fat32-in-memory
         (cdr dir-ent-list)
         tail-entry-limit))
       (error-code (if (zp error-code) tail-error-code error-code)))
    ;; We add the file to this m1 instance.
    (mv (list* (cons filename
                     (make-m1-file :dir-ent dir-ent
                                   :contents head))
               tail)
        (+ 1 head-entry-count tail-entry-count)
        (append (list clusterchain) head-clusterchain-list
                tail-clusterchain-list)
        error-code)))

(defthm lofat-to-hifat-helper-correctness-1-lemma-1
  (equal (rationalp (nth n (dir-ent-fix x)))
         (< (nfix n) *ms-dir-ent-length*)))

(defthm
  lofat-to-hifat-helper-correctness-1
  (b* (((mv m1-file-alist entry-count
            clusterchain-list error-code)
        (lofat-to-hifat-helper
         fat32-in-memory
         dir-ent-list entry-limit)))
    (and (natp entry-count)
         (<= entry-count (nfix entry-limit))
         (<= (len m1-file-alist)
             (len dir-ent-list))
         (alistp m1-file-alist)
         (true-list-listp clusterchain-list)
         (natp error-code)))
  :hints
  (("goal"
    :in-theory
    (e/d (fat32-filename-p lofat-to-hifat-helper)
         (nth-of-string=>nats
          natp-of-cluster-size take-redefinition))
    :induct
    (lofat-to-hifat-helper fat32-in-memory
                                     dir-ent-list entry-limit)))
  :rule-classes
  ((:type-prescription
    :corollary (b* (((mv & & & error-code)
                     (lofat-to-hifat-helper
                      fat32-in-memory
                      dir-ent-list entry-limit)))
                 (natp error-code)))
   (:linear :corollary (b* (((mv m1-file-alist & & error-code)
                             (lofat-to-hifat-helper
                              fat32-in-memory
                              dir-ent-list entry-limit)))
                         (and (<= 0 error-code)
                              (<= (len m1-file-alist)
                                  (len dir-ent-list)))))
   (:rewrite
    :corollary (b* (((mv & & clusterchain-list error-code)
                     (lofat-to-hifat-helper
                      fat32-in-memory
                      dir-ent-list entry-limit)))
                 (and (integerp error-code)
                      (true-list-listp clusterchain-list))))
   (:type-prescription
    :corollary (b* (((mv m1-file-alist &)
                     (lofat-to-hifat-helper
                      fat32-in-memory
                      dir-ent-list entry-limit)))
                 (true-listp m1-file-alist)))))

(defthm
  lofat-to-hifat-helper-correctness-2-lemma-1
  (implies (and (dir-ent-p dir-ent)
                (< (nfix n) *ms-dir-ent-length*))
           (rationalp (nth n dir-ent)))
  :hints (("goal" :in-theory (enable dir-ent-p)))
  :rule-classes
  ((:rewrite
    :corollary (implies (and (dir-ent-p dir-ent)
                             (< (nfix n) *ms-dir-ent-length*))
                        (acl2-numberp (nth n dir-ent))))))

(defthm
  lofat-to-hifat-helper-correctness-2
  (implies (useful-dir-ent-list-p dir-ent-list)
           (b* (((mv m1-file-alist & & &)
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  dir-ent-list entry-limit)))
             (m1-file-alist-p m1-file-alist)))
  :hints
  (("goal"
    :in-theory
    (e/d (fat32-filename-p useless-dir-ent-p
                           lofat-to-hifat-helper
                           useful-dir-ent-list-p)
         (nth-of-string=>nats natp-of-cluster-size
                              take-redefinition))
    :induct (lofat-to-hifat-helper
             fat32-in-memory
             dir-ent-list entry-limit))))

(defthm
  lofat-to-hifat-helper-correctness-3
  (b* (((mv m1-file-alist entry-count & &)
        (lofat-to-hifat-helper
         fat32-in-memory
         dir-ent-list entry-limit)))
    (equal entry-count
           (m1-entry-count m1-file-alist)))
  :hints
  (("goal" :in-theory (enable lofat-to-hifat-helper m1-entry-count)))
  :rule-classes
  (:rewrite
   (:linear
    :corollary (b* (((mv m1-file-alist & & &)
                     (lofat-to-hifat-helper
                      fat32-in-memory
                      dir-ent-list entry-limit)))
                 (<= (m1-entry-count m1-file-alist)
                     (nfix entry-limit)))
    :hints
    (("goal"
      :in-theory
      (disable lofat-to-hifat-helper-correctness-1)
      :use lofat-to-hifat-helper-correctness-1)))))

(defthmd
  lofat-to-hifat-helper-correctness-4
  (implies
   (and (equal (mv-nth 3
                       (lofat-to-hifat-helper
                        fat32-in-memory
                        dir-ent-list entry-limit1))
               0)
        (>= (nfix entry-limit2)
            (mv-nth 1
                    (lofat-to-hifat-helper
                     fat32-in-memory
                     dir-ent-list entry-limit1))))
   (equal
    (lofat-to-hifat-helper fat32-in-memory
                                     dir-ent-list entry-limit2)
    (lofat-to-hifat-helper
     fat32-in-memory
     dir-ent-list entry-limit1)))
  :hints
  (("goal" :in-theory (enable lofat-to-hifat-helper
                              m1-entry-count)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (equal (mv-nth 3
                         (lofat-to-hifat-helper
                          fat32-in-memory
                          dir-ent-list entry-limit1))
                 0)
          (>= (nfix entry-limit2)
              (mv-nth 1
                      (lofat-to-hifat-helper
                       fat32-in-memory
                       dir-ent-list entry-limit1)))
          (> entry-limit2 entry-limit1))
     (equal (lofat-to-hifat-helper
             fat32-in-memory
             dir-ent-list entry-limit2)
            (lofat-to-hifat-helper
             fat32-in-memory
             dir-ent-list entry-limit1))))))

(defthm true-listp-of-lofat-to-hifat-helper
  (true-listp (mv-nth 2
                      (lofat-to-hifat-helper
                       fat32-in-memory
                       dir-contents entry-limit))))

(verify-guards
  lofat-to-hifat-helper
  :hints
  (("goal"
    :in-theory (disable (:e dir-ent-directory-p)
                        (:t dir-ent-directory-p)
                        (:definition fat32-build-index-list)))))

(defthm
  data-region-length-of-update-fati
  (equal (data-region-length (update-fati i v fat32-in-memory))
         (data-region-length fat32-in-memory))
  :hints
  (("goal" :in-theory (enable data-region-length update-fati))))

(defund max-entry-count (fat32-in-memory)
  (declare
   (xargs :guard (lofat-fs-p fat32-in-memory)
          :stobjs fat32-in-memory))
  (mbe
   :exec
   (floor (* (data-region-length fat32-in-memory)
             (cluster-size fat32-in-memory))
          *ms-dir-ent-length*)
   :logic
   (nfix
    (floor (* (data-region-length fat32-in-memory)
              (cluster-size fat32-in-memory))
           *ms-dir-ent-length*))))

(defthm max-entry-count-of-update-fati
  (equal
   (max-entry-count (update-fati i v fat32-in-memory))
   (max-entry-count fat32-in-memory))
  :hints (("Goal" :in-theory (enable max-entry-count)) ))

(defund
  lofat-to-hifat
  (fat32-in-memory)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (lofat-fs-p fat32-in-memory)
    :guard-hints
    (("goal"
      :in-theory
      (disable
       (:rewrite get-clusterchain-contents-correctness-2))
      :use
      (:instance
       (:rewrite get-clusterchain-contents-correctness-2)
       (length *ms-max-dir-size*)
       (masked-current-cluster
        (fat32-entry-mask (bpb_rootclus fat32-in-memory)))
       (fat32-in-memory fat32-in-memory))))))
  (b*
      (((unless
         (mbt (>= (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                  *ms-first-data-cluster*)))
        (mv nil *eio*))
       ((mv root-dir-contents error-code)
        (get-clusterchain-contents
         fat32-in-memory
         (fat32-entry-mask (bpb_rootclus fat32-in-memory))
         *ms-max-dir-size*))
       ((unless (equal error-code 0))
        (mv nil (- error-code)))
       (entry-limit (max-entry-count fat32-in-memory))
       ((mv m1-file-alist & & error-code)
        (lofat-to-hifat-helper
         fat32-in-memory
         (make-dir-ent-list (string=>nats root-dir-contents))
         entry-limit)))
    (mv m1-file-alist error-code)))

(defthm
  lofat-to-hifat-correctness-1
  (and
   (m1-file-alist-p
    (mv-nth 0
            (lofat-to-hifat fat32-in-memory)))
   (natp (mv-nth 1
                 (lofat-to-hifat fat32-in-memory))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lofat-to-hifat)
     (m1-file-p
      (:rewrite get-clusterchain-contents-correctness-2)))
    :use
    (:instance
     (:rewrite get-clusterchain-contents-correctness-2)
     (length *ms-max-dir-size*)
     (masked-current-cluster
      (fat32-entry-mask (bpb_rootclus fat32-in-memory)))
     (fat32-in-memory fat32-in-memory))))
  :rule-classes
  ((:rewrite
    :corollary
    (and
     (m1-file-alist-p
      (mv-nth 0
              (lofat-to-hifat fat32-in-memory)))
     (integerp
      (mv-nth 1
              (lofat-to-hifat fat32-in-memory)))))
   (:linear
    :corollary
    (<= 0
        (mv-nth 1
                (lofat-to-hifat fat32-in-memory))))
   (:type-prescription
    :corollary
    (true-listp
     (mv-nth 0
             (lofat-to-hifat fat32-in-memory))))
   (:type-prescription
    :corollary
    (natp
     (mv-nth 1
             (lofat-to-hifat fat32-in-memory))))))

(defthm
  lofat-to-hifat-correctness-2
  (implies
   (equal
    (mv-nth
     0
     (get-clusterchain-contents
      fat32-in-memory
      (fat32-entry-mask (bpb_rootclus fat32-in-memory))
      *ms-max-dir-size*))
    "")
   (equal (mv-nth 0 (lofat-to-hifat fat32-in-memory))
          nil))
  :hints
  (("goal"
    :in-theory
    (enable lofat-to-hifat lofat-to-hifat-helper))))

(defthm
  m1-entry-count-of-lofat-to-hifat
  (implies
   (lofat-fs-p fat32-in-memory)
   (<= (m1-entry-count
        (mv-nth 0
                (lofat-to-hifat fat32-in-memory)))
       (max-entry-count fat32-in-memory)))
  :hints (("goal" :in-theory (enable lofat-to-hifat)))
  :rule-classes :linear)

(defund
  stobj-find-n-free-clusters-helper
  (fat32-in-memory n start)
  (declare
   (xargs
    :guard (and (lofat-fs-p fat32-in-memory)
                (natp n)
                (natp start))
    :stobjs fat32-in-memory
    :measure (nfix (- (+ (count-of-clusters fat32-in-memory)
                         *ms-first-data-cluster*)
                      start))))
  (if
   (or (zp n)
       (mbe :logic (zp (- (+ (count-of-clusters fat32-in-memory)
                             *ms-first-data-cluster*)
                          start))
            :exec (>= start
                      (+ (count-of-clusters fat32-in-memory)
                         *ms-first-data-cluster*))))
   nil
   (if
    (not (equal (fat32-entry-mask (fati start fat32-in-memory))
                0))
    (stobj-find-n-free-clusters-helper
     fat32-in-memory n (+ start 1))
    (cons
     (mbe :exec start :logic (nfix start))
     (stobj-find-n-free-clusters-helper fat32-in-memory (- n 1)
                                        (+ start 1))))))

(defthm
  nat-listp-of-stobj-find-n-free-clusters-helper
  (nat-listp
   (stobj-find-n-free-clusters-helper fat32-in-memory n start))
  :hints
  (("goal"
    :in-theory (enable stobj-find-n-free-clusters-helper)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary (integer-listp (stobj-find-n-free-clusters-helper
                               fat32-in-memory n start)))))

(defthm
  stobj-find-n-free-clusters-helper-correctness-1
  (implies
   (and (natp start)
        (lofat-fs-p fat32-in-memory))
   (equal
    (stobj-find-n-free-clusters-helper fat32-in-memory n start)
    (find-n-free-clusters-helper
     (nthcdr start (effective-fat fat32-in-memory))
     n start)))
  :hints
  (("goal" :in-theory (enable stobj-find-n-free-clusters-helper
                              find-n-free-clusters-helper)
    :induct (stobj-find-n-free-clusters-helper
             fat32-in-memory n start))))

(defund
  stobj-find-n-free-clusters
  (fat32-in-memory n)
  (declare
   (xargs :guard (and (lofat-fs-p fat32-in-memory)
                      (natp n))
          :stobjs fat32-in-memory))
  (stobj-find-n-free-clusters-helper
   fat32-in-memory n *ms-first-data-cluster*))

(defthm
  nat-listp-of-stobj-find-n-free-clusters
  (nat-listp (stobj-find-n-free-clusters fat32-in-memory n))
  :hints
  (("goal" :in-theory (enable stobj-find-n-free-clusters)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary (integer-listp (stobj-find-n-free-clusters-helper
                               fat32-in-memory n start)))))

(defthm
  stobj-find-n-free-clusters-correctness-1
  (implies
   (lofat-fs-p fat32-in-memory)
   (equal (stobj-find-n-free-clusters fat32-in-memory n)
          (find-n-free-clusters (effective-fat fat32-in-memory)
                                n)))
  :hints (("goal" :in-theory (enable stobj-find-n-free-clusters
                                     find-n-free-clusters)))
  :rule-classes :definition)

(defthm
  stobj-set-indices-in-fa-table-guard-lemma-1
  (implies (fat32-in-memoryp fat32-in-memory)
           (fat32-entry-list-p (nth *fati* fat32-in-memory)))
  :hints (("Goal" :in-theory (enable fat32-in-memoryp))))

(defthm
  stobj-set-indices-in-fa-table-guard-lemma-2
  (implies
   (and (fat32-entry-p entry)
        (fat32-masked-entry-p masked-entry))
   (unsigned-byte-p 32
                    (fat32-update-lower-28 entry masked-entry)))
  :hints
  (("goal"
    :in-theory
    (e/d (fat32-entry-p)
         (fat32-update-lower-28-correctness-1 unsigned-byte-p))
    :use fat32-update-lower-28-correctness-1)))

(defund
  stobj-set-indices-in-fa-table
  (fat32-in-memory index-list value-list)
  (declare
   (xargs
    :measure (acl2-count index-list)
    :stobjs fat32-in-memory
    :guard (and (lofat-fs-p fat32-in-memory)
                (nat-listp index-list)
                (fat32-masked-entry-list-p value-list)
                (equal (len index-list)
                       (len value-list)))
    :guard-hints
    (("goal" :in-theory (e/d (lofat-fs-p-of-update-fati)
                             (unsigned-byte-p))))))
  (b*
      (((when (atom index-list))
        fat32-in-memory)
       (current-index (car index-list))
       ((when (or (not (natp current-index))
                  (>= current-index
                      (+ (count-of-clusters fat32-in-memory)
                         *ms-first-data-cluster*))
                  (mbe :logic (>= current-index
                                  (fat-length fat32-in-memory))
                       :exec nil)))
        fat32-in-memory)
       (fat32-in-memory
        (update-fati current-index
                     (fat32-update-lower-28
                      (fati current-index fat32-in-memory)
                      (car value-list))
                     fat32-in-memory)))
    (stobj-set-indices-in-fa-table
     fat32-in-memory (cdr index-list)
     (cdr value-list))))

(defthm
  stobj-set-indices-in-fa-table-correctness-1-lemma-1
  (implies
   (fat32-in-memoryp fat32-in-memory)
   (equal (update-nth *fati* (nth *fati* fat32-in-memory)
                      fat32-in-memory)
          fat32-in-memory))
  :hints (("Goal" :in-theory (enable fat32-in-memoryp))))

(defthm
  stobj-set-indices-in-fa-table-correctness-1-lemma-2
  (implies
   (fat32-in-memoryp fat32-in-memory)
   (equal
    (fat32-in-memoryp (update-nth *fati* val fat32-in-memory))
    (fat32-entry-list-p val)))
  :hints (("Goal" :in-theory (enable fat32-in-memoryp))))

(defthm
  count-of-clusters-of-stobj-set-indices-in-fa-table
  (equal
   (count-of-clusters (stobj-set-indices-in-fa-table
                  fat32-in-memory index-list value-list))
   (count-of-clusters fat32-in-memory))
  :hints
  (("goal" :in-theory (enable stobj-set-indices-in-fa-table))))

(defthm
  stobj-set-indices-in-fa-table-correctness-1
  (implies
   (and (fat32-masked-entry-list-p value-list)
        (equal (len index-list)
               (len value-list))
        (lofat-fs-p fat32-in-memory))
   (equal
    (effective-fat (stobj-set-indices-in-fa-table
                    fat32-in-memory index-list value-list))
    (set-indices-in-fa-table (effective-fat fat32-in-memory)
                             index-list value-list)))
  :hints
  (("goal"
    :in-theory
    (e/d (set-indices-in-fa-table
          stobj-set-indices-in-fa-table
          lofat-fs-p-of-update-fati)))))

(defthm
  fati-of-stobj-set-indices-in-fa-table
  (implies
   (and (fat32-masked-entry-list-p value-list)
        (equal (len index-list)
               (len value-list))
        (lofat-fs-p fat32-in-memory)
        (natp n)
        (nat-listp index-list)
        (not (member-equal n index-list)))
   (equal
    (nth n
         (effective-fat
          (stobj-set-indices-in-fa-table
           fat32-in-memory index-list value-list)))
    (nth n (effective-fat fat32-in-memory))))
  :hints (("goal" :in-theory (disable nth-of-effective-fat)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (fat32-masked-entry-list-p value-list)
          (equal (len index-list)
                 (len value-list))
          (lofat-fs-p fat32-in-memory)
          (natp n)
          (nat-listp index-list)
          (not (member-equal n index-list))
          (< n
             (+ (count-of-clusters fat32-in-memory)
                *ms-first-data-cluster*)))
     (equal (fati n
                  (stobj-set-indices-in-fa-table
                   fat32-in-memory index-list value-list))
            (fati n fat32-in-memory)))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (disable stobj-set-indices-in-fa-table-correctness-1))))))

(defthm
  lofat-fs-p-of-stobj-set-indices-in-fa-table
  (implies (and (lofat-fs-p fat32-in-memory)
                (fat32-masked-entry-list-p value-list)
                (equal (len index-list)
                       (len value-list)))
           (lofat-fs-p
            (stobj-set-indices-in-fa-table
             fat32-in-memory index-list value-list)))
  :hints
  (("goal" :in-theory
    (enable stobj-set-indices-in-fa-table
            lofat-fs-p-of-update-fati))))

(defthm
  cluster-size-of-stobj-set-indices-in-fa-table
  (equal
   (cluster-size (stobj-set-indices-in-fa-table
                  fat32-in-memory index-list value-list))
   (cluster-size fat32-in-memory))
  :hints
  (("goal" :in-theory (enable stobj-set-indices-in-fa-table))))

(defthm
  data-region-length-of-stobj-set-indices-in-fa-table
  (equal
   (data-region-length (stobj-set-indices-in-fa-table
                  fat32-in-memory index-list value-list))
   (data-region-length fat32-in-memory))
  :hints
  (("goal" :in-theory (enable stobj-set-indices-in-fa-table))))

(defthm
  fat-length-of-stobj-set-indices-in-fa-table
  (equal
   (fat-length (stobj-set-indices-in-fa-table
                fat32-in-memory index-list value-list))
   (fat-length fat32-in-memory))
  :hints
  (("goal" :in-theory (enable stobj-set-indices-in-fa-table))))

(defthm
  bpb_rootclus-of-stobj-set-indices-in-fa-table
  (equal
   (bpb_rootclus (stobj-set-indices-in-fa-table
                  fat32-in-memory index-list value-list))
   (bpb_rootclus fat32-in-memory))
  :hints
  (("goal" :in-theory (enable stobj-set-indices-in-fa-table))))

(defthm
  data-regioni-of-stobj-set-indices-in-fa-table
  (equal (data-regioni i (stobj-set-indices-in-fa-table
                          fat32-in-memory index-list value-list))
         (data-regioni i fat32-in-memory))
  :hints
  (("goal" :in-theory (enable stobj-set-indices-in-fa-table))))

(defthm
  max-entry-count-of-stobj-set-indices-in-fa-table
  (equal
   (max-entry-count (stobj-set-indices-in-fa-table
                     fat32-in-memory index-list value-list))
   (max-entry-count fat32-in-memory))
  :hints (("goal" :in-theory (enable max-entry-count))))

(defun
    stobj-set-clusters
    (cluster-list index-list fat32-in-memory)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard
    (and (lofat-fs-p fat32-in-memory)
         (lower-bounded-integer-listp
          index-list *ms-first-data-cluster*)
         (cluster-listp cluster-list (cluster-size fat32-in-memory))
         (equal (len index-list)
                (len cluster-list)))))
  (b*
      (((unless (consp cluster-list))
        fat32-in-memory)
       (fat32-in-memory
        (stobj-set-clusters (cdr cluster-list)
                            (cdr index-list)
                            fat32-in-memory))
       ((unless (and (integerp (car index-list))
                     (>= (car index-list)
                         *ms-first-data-cluster*)
                     (< (car index-list)
                        (+ *ms-first-data-cluster*
                           (data-region-length fat32-in-memory)))))
        fat32-in-memory))
    (update-data-regioni (- (car index-list) *ms-first-data-cluster*)
                         (car cluster-list)
                         fat32-in-memory)))

(defthm
  cluster-size-of-stobj-set-clusters
  (equal
   (cluster-size
    (stobj-set-clusters cluster-list
                        index-list fat32-in-memory))
   (cluster-size fat32-in-memory)))

(defthm
  count-of-clusters-of-stobj-set-clusters
  (equal
   (count-of-clusters
    (stobj-set-clusters cluster-list
                        index-list fat32-in-memory))
   (count-of-clusters fat32-in-memory)))

(defthm
  data-region-length-of-stobj-set-clusters
  (equal
   (data-region-length
    (stobj-set-clusters cluster-list
                        index-list fat32-in-memory))
   (data-region-length fat32-in-memory)))

(defthm
  lofat-fs-p-of-stobj-set-clusters
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (lower-bounded-integer-listp
         index-list *ms-first-data-cluster*)
        (cluster-listp cluster-list (cluster-size fat32-in-memory))
        (equal (len cluster-list)
               (len index-list))
        (equal (data-region-length fat32-in-memory)
               (count-of-clusters fat32-in-memory)))
   (lofat-fs-p
    (stobj-set-clusters cluster-list
                        index-list fat32-in-memory)))
  :hints
  (("goal"
    :induct
    (stobj-set-clusters cluster-list index-list fat32-in-memory))))

(defthm
  fati-of-stobj-set-clusters
  (equal (fati i
               (stobj-set-clusters cluster-list
                                   index-list fat32-in-memory))
         (fati i fat32-in-memory)))

(defthm
  fat-length-of-stobj-set-clusters
  (equal
   (fat-length
    (stobj-set-clusters cluster-list
                        index-list fat32-in-memory))
   (fat-length fat32-in-memory)))

(defthm
  bpb_rootclus-of-stobj-set-clusters
  (equal
   (bpb_rootclus
    (stobj-set-clusters cluster-list
                        index-list fat32-in-memory))
   (bpb_rootclus fat32-in-memory)))

;; This function needs to return an mv containing the fat32-in-memory stobj,
;; the new directory entry, and an errno value (either 0 or ENOSPC).

;; One idea we tried was setting first-cluster to *ms-end-of-clusterchain*
;; (basically, marking it used) inside the body of this function. This would
;; have made some proofs more modular... but it doesn't work, because when
;; we're placing the contents of a directory (inside
;; hifat-to-lofat-helper), we need to make a recursive call to get
;; the contents of that directory in the first place... and first-cluster must
;; be marked used before that call is made to ensure that cluster doesn't get
;; used.
(defund
  place-contents
  (fat32-in-memory dir-ent
                   contents file-length first-cluster)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (and (lofat-fs-p fat32-in-memory)
                (dir-ent-p dir-ent)
                (unsigned-byte-p 32 file-length)
                (stringp contents)
                (fat32-masked-entry-p first-cluster)
                (>= first-cluster *ms-first-data-cluster*)
                (< first-cluster
                   (+ *ms-first-data-cluster*
                      (count-of-clusters fat32-in-memory))))
    :guard-hints
    (("goal"
      :in-theory
      (disable
       (:rewrite
        fat32-masked-entry-list-p-of-find-n-free-clusters
        . 1)
       unsigned-byte-p)
      :use
      (:instance
       (:rewrite
        fat32-masked-entry-list-p-of-find-n-free-clusters
        . 1)
       (n
        (binary-+
         '-1
         (len (make-clusters contents
                             (cluster-size fat32-in-memory)))))
       (fa-table (effective-fat fat32-in-memory)))))))
  (b*
      ((dir-ent (dir-ent-fix dir-ent))
       (cluster-size (cluster-size fat32-in-memory))
       (clusters (make-clusters contents cluster-size)))
    (if
        (and
         (< (len clusters) 1)
         (mbt
          (and
           (fat32-masked-entry-p first-cluster)
           (< first-cluster
              (fat-length fat32-in-memory)))))
        (b*
            (;; There shouldn't be a memory leak - mark this as free.
             (fat32-in-memory
              (update-fati first-cluster
                           (fat32-update-lower-28
                            (fati first-cluster fat32-in-memory)
                            0)
                           fat32-in-memory))
             ;; From page 17 of the FAT specification: "Note that a zero-length
             ;; file [...] has a first cluster number of 0 placed in its
             ;; directory entry."
             (dir-ent (dir-ent-set-first-cluster-file-size
                       dir-ent 0 file-length)))
          (mv fat32-in-memory dir-ent 0 nil))
      (b*
          ((indices
            (list* first-cluster
                   (stobj-find-n-free-clusters
                    fat32-in-memory (- (len clusters) 1))))
           ((unless (equal (len indices) (len clusters)))
            (mv fat32-in-memory dir-ent *enospc* nil))
           (fat32-in-memory
            (stobj-set-clusters clusters indices fat32-in-memory))
           (fat32-in-memory
            (stobj-set-indices-in-fa-table
             fat32-in-memory indices
             (binary-append (cdr indices)
                            (list *ms-end-of-clusterchain*)))))
        (mv
         fat32-in-memory
         (dir-ent-set-first-cluster-file-size dir-ent (car indices)
                                              file-length)
         0 indices)))))

(defthm
  lofat-fs-p-of-place-contents
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (stringp contents)
        (natp file-length)
        (integerp first-cluster)
        (>= first-cluster *ms-first-data-cluster*)
        (< first-cluster
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory))))
   (lofat-fs-p
    (mv-nth
     0
     (place-contents fat32-in-memory dir-ent
                     contents file-length first-cluster))))
  :hints
  (("goal" :in-theory
    (enable place-contents
            lofat-fs-p-of-update-fati))))

(defthm
  cluster-size-of-place-contents
  (equal
   (cluster-size
    (mv-nth 0
            (place-contents fat32-in-memory
                            dir-ent contents file-length first-cluster)))
   (cluster-size fat32-in-memory))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  count-of-clusters-of-place-contents
  (equal
   (count-of-clusters
    (mv-nth 0
            (place-contents fat32-in-memory
                            dir-ent contents file-length first-cluster)))
   (count-of-clusters fat32-in-memory))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  data-region-length-of-place-contents
  (equal
   (data-region-length
    (mv-nth
     0
     (place-contents fat32-in-memory dir-ent
                     contents file-length first-cluster)))
   (data-region-length fat32-in-memory))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  bpb_rootclus-of-place-contents
  (equal
   (bpb_rootclus
    (mv-nth
     0
     (place-contents fat32-in-memory dir-ent
                     contents file-length first-cluster)))
   (bpb_rootclus fat32-in-memory))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  dir-ent-p-of-place-contents
  (dir-ent-p
   (mv-nth 1
           (place-contents fat32-in-memory
                           dir-ent contents file-length first-cluster)))
  :hints (("goal" :in-theory (enable place-contents)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (unsigned-byte-listp
     8
     (mv-nth 1
             (place-contents fat32-in-memory
                             dir-ent contents file-length first-cluster)))
    :hints (("goal" :in-theory (enable dir-ent-p))))
   (:rewrite
    :corollary
    (equal
     (len
      (mv-nth 1
              (place-contents fat32-in-memory
                              dir-ent contents file-length first-cluster)))
     *ms-dir-ent-length*)
    :hints (("goal" :in-theory (enable dir-ent-p))))
   (:rewrite
    :corollary
    (true-listp
     (mv-nth 1
             (place-contents fat32-in-memory
                             dir-ent contents file-length first-cluster)))
    :hints (("goal" :in-theory (enable dir-ent-p))))))

(defthm
  useless-dir-ent-p-of-dir-ent-set-first-cluster-file-size
  (implies
   (dir-ent-p dir-ent)
   (equal
    (useless-dir-ent-p (dir-ent-set-first-cluster-file-size
                        dir-ent first-cluster file-size))
    (useless-dir-ent-p dir-ent)))
  :hints
  (("goal"
    :in-theory
    (e/d (useless-dir-ent-p dir-ent-p dir-ent-filename
                            dir-ent-set-first-cluster-file-size)
         ((:rewrite logtail-loghead))))))

(defthm
  useless-dir-ent-p-of-place-contents
  (implies
   (dir-ent-p dir-ent)
   (equal
    (useless-dir-ent-p
     (mv-nth 1
             (place-contents fat32-in-memory
                             dir-ent contents file-length first-cluster)))
    (useless-dir-ent-p
     dir-ent)))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  fat-length-of-place-contents
  (equal
   (fat-length
    (mv-nth 0
            (place-contents fat32-in-memory
                            dir-ent contents file-length first-cluster)))
   (fat-length fat32-in-memory))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  natp-of-place-contents
  (natp
   (mv-nth 2
           (place-contents fat32-in-memory dir-ent
                           contents file-length first-cluster)))
  :hints (("goal" :in-theory (enable place-contents)))
  :rule-classes
  (:type-prescription
   (:rewrite
    :corollary
    (integerp
     (mv-nth
      2
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))))
   (:linear
    :corollary
    (<=
     0
     (mv-nth
      2
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))))))

(defthm
  true-listp-of-place-contents
  (true-listp
   (mv-nth 3
           (place-contents fat32-in-memory dir-ent
                           contents file-length first-cluster)))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  fat32-masked-entry-list-p-of-place-contents
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (fat32-masked-entry-p first-cluster))
   (fat32-masked-entry-list-p
    (mv-nth
     3
     (place-contents fat32-in-memory dir-ent
                     contents file-length first-cluster))))
  :hints
  (("goal"
    :in-theory
    (e/d (place-contents)
         ((:rewrite
           fat32-masked-entry-list-p-of-find-n-free-clusters
           . 1)))
    :use
    (:instance
     (:rewrite fat32-masked-entry-list-p-of-find-n-free-clusters
               . 1)
     (n
      (binary-+
       '-1
       (len (make-clusters contents
                           (cluster-size fat32-in-memory)))))
     (fa-table (effective-fat fat32-in-memory))))))

(defthm
  max-entry-count-of-place-contents
  (equal
   (max-entry-count
    (mv-nth
     0
     (place-contents fat32-in-memory dir-ent
                     contents file-length first-cluster)))
   (max-entry-count fat32-in-memory))
  :hints
  (("goal" :in-theory (enable max-entry-count place-contents))))

;; OK, this function needs to return a list of directory entries, so that when
;; it is called recursively to take care of all the entries in a subdirectory,
;; the caller gets the list of these entries and becomes able to concatenate
;; them all together, add entries in the front for "." and "..", and then treat
;; the result as the contents of a file. In this scenario, the
;; caller must allocate one cluster even before making the recursive call for
;; the subdirectory, because  the FAT spec says, on page 26, "One cluster is
;; allocated to the directory (unless it is the root directory on a FAT16/FAT12
;; volume), and you set DIR_FstClusLO and DIR_FstClusHI to that cluster number
;; and place an EOC mark in that cluster's entry in the FAT." Now, after the
;; recursive call returns a list of entries, the caller can create a "." entry
;; using the index of the cluster allocated for this subdirectory before this
;; call, and a ".." entry using its own first cluster. However, it cannot know
;; its own first cluster without having it passed from its parent, so this must
;; be an extra argument to the recursive call.
;; Purely for proof purposes, we're also going to have to return an extra
;; argument, namely, the list of indices we used. That will be (mv-nth 3 ...)
;; of the thing.
(defun
    hifat-to-lofat-helper
    (fat32-in-memory fs current-dir-first-cluster)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (and (lofat-fs-p fat32-in-memory)
                (m1-file-alist-p fs)
                (fat32-masked-entry-p current-dir-first-cluster))
    :hints (("goal" :in-theory (enable m1-file->contents
                                       m1-file-contents-fix)))
    :verify-guards nil))
  (b*
      (;; This is the base case; no directory entries are left. Return an error
       ;; code of 0 (that is, the (mv-nth 2 ...) of the return value).
       ((unless (consp fs))
        (mv fat32-in-memory nil 0 nil))
       ;; The induction case begins here. First, recursively take care of all
       ;; the directory entries after this one in the same directory.
       ((mv fat32-in-memory tail-list errno tail-index-list)
        (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                         current-dir-first-cluster))
       ;; If there was an error in the recursive call, terminate.
       ((unless (zp errno)) (mv fat32-in-memory tail-list errno tail-index-list))
       (head (car fs))
       ;; "." and ".." entries are not even allowed to be part of an
       ;; m1-file-alist, so perhaps we can use mbt to wipe out this clause...
       ((when (or (equal (car head) *current-dir-fat32-name*)
                  (equal (car head) *parent-dir-fat32-name*)))
        (mv fat32-in-memory tail-list errno tail-index-list))
       ;; Get the directory entry for the first file in this directory.
       (dir-ent (m1-file->dir-ent (cdr head)))
       ;; Search for one cluster - unless empty, the file will need at least
       ;; one.
       (indices
        (stobj-find-n-free-clusters
         fat32-in-memory 1))
       ;; This means we couldn't find even one free cluster, so we return a "no
       ;; space left" error.
       ((when (< (len indices) 1))
        (mv fat32-in-memory tail-list *enospc* tail-index-list))
       (first-cluster
        (nth 0 indices))
       ;; The mbt below says this branch will never be taken; but having this
       ;; allows us to prove a strong rule about fat-length.
       ((unless (mbt (< first-cluster (fat-length fat32-in-memory))))
        (mv fat32-in-memory tail-list *enospc* tail-index-list))
       ;; Mark this cluster as used, without possibly interfering with any
       ;; existing clusterchains.
       (fat32-in-memory
        (update-fati
         first-cluster
         (fat32-update-lower-28 (fati first-cluster fat32-in-memory)
                                *ms-end-of-clusterchain*)
         fat32-in-memory)))
    (if
        (m1-regular-file-p (cdr head))
        (b* ((contents (m1-file->contents (cdr head)))
             (file-length (length contents))
             ((mv fat32-in-memory dir-ent errno head-index-list)
              (place-contents fat32-in-memory
                              dir-ent contents file-length first-cluster))
             (dir-ent (dir-ent-set-filename dir-ent (car head)))
             (dir-ent
              (dir-ent-install-directory-bit
               dir-ent nil)))
        (mv fat32-in-memory
            (list* dir-ent tail-list)
            errno
            (append head-index-list tail-index-list)))
      (b* ((contents (m1-file->contents (cdr head)))
           (file-length 0)
           ((mv fat32-in-memory unflattened-contents errno head-index-list1)
            (hifat-to-lofat-helper
             fat32-in-memory contents first-cluster))
           ((unless (zp errno)) (mv fat32-in-memory tail-list errno tail-index-list))
           (contents
            (nats=>string
             (append
              (dir-ent-install-directory-bit
               (dir-ent-set-filename
                (dir-ent-set-first-cluster-file-size
                 dir-ent
                 first-cluster
                 0)
                *current-dir-fat32-name*)
               t)
              (dir-ent-install-directory-bit
               (dir-ent-set-filename
                (dir-ent-set-first-cluster-file-size
                 dir-ent
                 current-dir-first-cluster
                 0)
                *parent-dir-fat32-name*)
               t)
              (flatten unflattened-contents))))
           ((mv fat32-in-memory dir-ent errno head-index-list2)
            (place-contents fat32-in-memory
                            dir-ent contents file-length
                            first-cluster))
           (dir-ent (dir-ent-set-filename dir-ent (car head)))
           (dir-ent
            (dir-ent-install-directory-bit
             dir-ent t)))
        (mv fat32-in-memory
            (list* dir-ent tail-list)
            errno
            (append head-index-list1 head-index-list2 tail-index-list))))))

(defthm
  cluster-size-of-hifat-to-lofat-helper
  (equal
   (cluster-size (mv-nth 0
                         (hifat-to-lofat-helper
                          fat32-in-memory
                          fs current-dir-first-cluster)))
   (cluster-size fat32-in-memory)))

(defthm
  count-of-clusters-of-hifat-to-lofat-helper
  (equal
   (count-of-clusters
    (mv-nth 0
            (hifat-to-lofat-helper
             fat32-in-memory fs current-dir-first-cluster)))
   (count-of-clusters fat32-in-memory)))

(defthm natp-of-hifat-to-lofat-helper
  (natp (mv-nth 2
                (hifat-to-lofat-helper
                 fat32-in-memory
                 fs current-dir-first-cluster)))
  :rule-classes
  (:type-prescription
   (:rewrite
    :corollary
    (integerp (mv-nth 2
                      (hifat-to-lofat-helper
                       fat32-in-memory
                       fs current-dir-first-cluster))))
   (:linear
    :corollary
    (<= 0
        (mv-nth 2
                (hifat-to-lofat-helper
                 fat32-in-memory
                 fs current-dir-first-cluster))))))

(defthm
  data-region-length-of-hifat-to-lofat-helper
  (equal
   (data-region-length
    (mv-nth 0
            (hifat-to-lofat-helper
             fat32-in-memory fs current-dir-first-cluster)))
   (data-region-length fat32-in-memory)))

(defthm
  bpb_rootclus-of-hifat-to-lofat-helper
  (equal
   (bpb_rootclus
    (mv-nth 0
            (hifat-to-lofat-helper
             fat32-in-memory fs current-dir-first-cluster)))
   (bpb_rootclus fat32-in-memory)))

(defthm
  fat-length-of-hifat-to-lofat-helper
  (equal
   (fat-length (mv-nth 0
                       (hifat-to-lofat-helper
                        fat32-in-memory fs first-cluster)))
   (fat-length fat32-in-memory))
  :hints (("goal" :in-theory (enable nth))))

(defthm
  lofat-fs-p-of-hifat-to-lofat-helper-lemma-1
  (implies
   (lofat-fs-p fat32-in-memory)
   (and
    (not (< (binary-+ '2
                      (count-of-clusters fat32-in-memory))
            '0))
    (not (< (binary-+ '2
                      (count-of-clusters fat32-in-memory))
            '2))
    (not
     (< (nfix (binary-+ '2
                        (count-of-clusters fat32-in-memory)))
        '2)))))

(defthm
  lofat-fs-p-of-hifat-to-lofat-helper
  (implies
   (lofat-fs-p fat32-in-memory)
   (lofat-fs-p
    (mv-nth 0
            (hifat-to-lofat-helper
             fat32-in-memory fs first-cluster))))
  :hints
  (("goal"
    :in-theory (e/d (lofat-fs-p-of-update-fati)
                    (stobj-set-indices-in-fa-table)))))

(defthm
  dir-ent-list-p-of-hifat-to-lofat-helper
  (dir-ent-list-p
   (mv-nth 1
           (hifat-to-lofat-helper
            fat32-in-memory fs first-cluster))))

(defthm
  useful-dir-ent-list-p-of-hifat-to-lofat-helper
  (implies
   (m1-file-alist-p fs)
   (useful-dir-ent-list-p
    (mv-nth 1
            (hifat-to-lofat-helper
             fat32-in-memory fs first-cluster))))
  :hints
  (("goal"
    :in-theory
    (enable useful-dir-ent-list-p))))

(defthm
  unsigned-byte-listp-of-flatten-when-dir-ent-list-p
  (implies (dir-ent-list-p dir-ent-list)
           (unsigned-byte-listp 8 (flatten dir-ent-list)))
  :hints (("goal" :in-theory (enable flatten))))

(defthm
  len-of-flatten-when-dir-ent-list-p
  (implies (dir-ent-list-p dir-ent-list)
           (equal
            (len (flatten dir-ent-list))
            (* *ms-dir-ent-length* (len dir-ent-list))))
  :hints (("goal" :in-theory (enable flatten len-when-dir-ent-p))))

(defthmd
  hifat-to-lofat-helper-correctness-4
  (implies
   (and (m1-file-alist-p fs)
        (zp (mv-nth 2
                    (hifat-to-lofat-helper
                     fat32-in-memory fs first-cluster))))
   (equal (len (mv-nth 1
                       (hifat-to-lofat-helper
                        fat32-in-memory fs first-cluster)))
          (len fs)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (m1-file-alist-p fs)
          (zp (mv-nth 2
                      (hifat-to-lofat-helper
                       fat32-in-memory fs first-cluster))))
     (equal (consp (mv-nth 1
                         (hifat-to-lofat-helper
                          fat32-in-memory fs first-cluster)))
            (consp fs))))))

(defthm
  true-listp-of-hifat-to-lofat-helper
  (true-listp (mv-nth 3
                      (hifat-to-lofat-helper
                       fat32-in-memory
                       fs current-dir-first-cluster))))

(encapsulate
  ()

  (local
   (defthm
     hifat-to-lofat-helper-guard-lemma-1
     (implies (not (m1-regular-file-p file))
              (equal (m1-directory-file-p file)
                     (m1-file-p file)))
     :hints
     (("goal"
       :in-theory (enable m1-directory-file-p m1-file-p
                          m1-regular-file-p m1-file-contents-p
                          m1-file->contents)))))

  (local
   (defthm
     hifat-to-lofat-helper-guard-lemma-2
     (implies (unsigned-byte-listp 8 x)
              (true-listp x))))

  (defthm
    hifat-to-lofat-helper-guard-lemma-3
    (implies
     (lofat-fs-p fat32-in-memory)
     (not
      (<
       (nth
        '0
        (find-n-free-clusters
         (effective-fat (mv-nth '0
                                (hifat-to-lofat-helper
                                 fat32-in-memory (cdr fs)
                                 current-dir-first-cluster)))
         '1))
       '0)))
    :hints (("Goal" :in-theory (enable nth))))

  (verify-guards
    hifat-to-lofat-helper
    :hints
    (("goal"
      :in-theory
      (e/d
       (painful-debugging-lemma-9 lofat-fs-p-of-update-fati)
       (stobj-set-indices-in-fa-table))))))

(defthm
  max-entry-count-of-hifat-to-lofat-helper
  (equal
   (max-entry-count
    (mv-nth
     0
     (hifat-to-lofat-helper fat32-in-memory
                                      fs current-dir-first-cluster)))
   (max-entry-count fat32-in-memory)))

(defthmd
  hifat-to-lofat-guard-lemma-1
  (implies
   (lofat-fs-p fat32-in-memory)
   (iff
    (< (binary-+
        '1
        (fat32-entry-mask (bpb_rootclus fat32-in-memory)))
       (fat-entry-count fat32-in-memory))
    (or
     (not
      (equal (fat32-entry-mask (bpb_rootclus fat32-in-memory))
             (+ (count-of-clusters fat32-in-memory)
                1)))
     (not (equal (fat-entry-count fat32-in-memory)
                 (+ (count-of-clusters fat32-in-memory)
                    2))))))
  :hints
  (("goal" :in-theory
    (disable lofat-fs-p-correctness-1)
    :use lofat-fs-p-correctness-1)))

(defund
  hifat-to-lofat
  (fat32-in-memory fs)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (and (lofat-fs-p fat32-in-memory)
                (m1-file-alist-p fs))
    :guard-hints
    (("goal" :in-theory (e/d (hifat-to-lofat-guard-lemma-1
                              lofat-fs-p-of-update-fati)
                             (unsigned-byte-p))
      ;; This is the second time we've had to add a :cases hint, really. The
      ;; reason is the same: brr tells us that a case split which should be
      ;; happening is not happening automatically.
      :cases
      ((not (equal (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                   (binary-+ '1
                             (count-of-clusters fat32-in-memory))))
       (not (equal (fat-entry-count fat32-in-memory)
                   (binary-+ '2
                             (count-of-clusters fat32-in-memory)))))
      :do-not-induct t))))
  (b*
      ((rootclus (bpb_rootclus fat32-in-memory))
       (index-list-to-clear
        (generate-index-list *ms-first-data-cluster*
                             (count-of-clusters fat32-in-memory)))
       (fat32-in-memory (stobj-set-indices-in-fa-table
                         fat32-in-memory index-list-to-clear
                         (make-list (len index-list-to-clear)
                                    :initial-element 0)))
       (fat32-in-memory (update-fati (fat32-entry-mask rootclus)
                                     (fat32-update-lower-28
                                      (fati
                                       (fat32-entry-mask rootclus)
                                       fat32-in-memory)
                                      *ms-end-of-clusterchain*)
                                     fat32-in-memory))
       ((mv fat32-in-memory
            root-dir-ent-list errno &)
        (hifat-to-lofat-helper
         fat32-in-memory
         fs (fat32-entry-mask rootclus)))
       ((unless (zp errno))
        (mv fat32-in-memory errno))
       (contents
        (if
            (atom root-dir-ent-list)
            ;; Here's the reasoning: there has to be something in the root
            ;; directory, even if the root directory is empty (i.e. the
            ;; contents of the root directory are all zeros, occupying at least
            ;; one cluster.)
            (coerce (make-list (cluster-size fat32-in-memory)
                               :initial-element (code-char 0))
                    'string)
          (nats=>string (flatten root-dir-ent-list))))
       ((mv fat32-in-memory & error-code &)
        (place-contents fat32-in-memory (dir-ent-fix nil)
                        contents
                        0 (fat32-entry-mask rootclus))))
    (mv fat32-in-memory error-code)))

(defthm natp-of-hifat-to-lofat
  (natp (mv-nth 1
                (hifat-to-lofat
                 fat32-in-memory
                 fs)))
  :rule-classes
  (:type-prescription
   (:rewrite
    :corollary
    (integerp (mv-nth 1
                      (hifat-to-lofat
                       fat32-in-memory
                       fs))))
   (:linear
    :corollary
    (<= 0
        (mv-nth 1
                (hifat-to-lofat
                 fat32-in-memory
                 fs)))))
  :hints (("Goal" :in-theory (enable hifat-to-lofat)) ))

(defthm
  lofat-fs-p-of-hifat-to-lofat
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (m1-file-alist-p fs))
   (lofat-fs-p
    (mv-nth 0
            (hifat-to-lofat fat32-in-memory fs))))
  :hints
  (("goal"
    :in-theory (enable hifat-to-lofat
                       hifat-to-lofat-guard-lemma-1
                       lofat-fs-p-of-update-fati)
    :do-not-induct t
    :cases
    ((not
      (equal (fat32-entry-mask (bpb_rootclus fat32-in-memory))
             (binary-+ '1
                       (count-of-clusters fat32-in-memory))))
     (not
      (equal
       (fat-length fat32-in-memory)
       (binary-+ '2
                 (count-of-clusters fat32-in-memory))))))))

(defun
    stobj-fa-table-to-string-helper
    (fat32-in-memory length ac)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (and (lofat-fs-p fat32-in-memory)
                (natp length)
                (<= length (fat-length fat32-in-memory)))
    :guard-hints
    (("goal"
      :in-theory
      (e/d
       (fat32-entry-p)
       (unsigned-byte-p fati-when-lofat-fs-p))
      :use (:instance fati-when-lofat-fs-p
                      (i (+ -1 length)))))))
  (if
      (zp length)
      ac
    (let ((current (fati (- length 1) fat32-in-memory)))
      (stobj-fa-table-to-string-helper
       fat32-in-memory (- length 1)
       (list*
        (code-char (loghead 8             current ))
        (code-char (loghead 8 (logtail  8 current)))
        (code-char (loghead 8 (logtail 16 current)))
        (code-char            (logtail 24 current))
        ac)))))

(defthm
  character-listp-of-stobj-fa-table-to-string-helper
  (equal
   (character-listp
    (stobj-fa-table-to-string-helper fat32-in-memory length ac))
   (character-listp ac)))

(defthm
  len-of-stobj-fa-table-to-string-helper
  (equal
   (len
    (stobj-fa-table-to-string-helper
     fat32-in-memory length ac))
   (+ (len ac) (* 4 (nfix length)))))

(defund
    stobj-fa-table-to-string
    (fat32-in-memory)
    (declare
     (xargs
      :stobjs fat32-in-memory
      :guard (lofat-fs-p fat32-in-memory)))
    (coerce
     (stobj-fa-table-to-string-helper
      fat32-in-memory (fat-length fat32-in-memory) nil)
     'string))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    reserved-area-string-guard-lemma-1
    (implies (lofat-fs-p fat32-in-memory)
             (natp (- (* (bpb_bytspersec fat32-in-memory)
                         (bpb_rsvdseccnt fat32-in-memory))
                      90)))
    :rule-classes
    ((:linear
      :corollary
      (implies (lofat-fs-p fat32-in-memory)
               (<= 90
                   (* (bpb_bytspersec fat32-in-memory)
                      (bpb_rsvdseccnt fat32-in-memory)))))
     (:rewrite
      :corollary
      (implies (lofat-fs-p fat32-in-memory)
               (integerp (* (bpb_bytspersec fat32-in-memory)
                            (bpb_rsvdseccnt fat32-in-memory)))))
     (:rewrite
      :corollary
      (implies (lofat-fs-p fat32-in-memory)
               (integerp (- (* (bpb_bytspersec fat32-in-memory)
                               (bpb_rsvdseccnt fat32-in-memory)))))))
    :hints (("goal" :in-theory (e/d (lofat-fs-p)
                                    (fat32-in-memoryp))))))

(defthm
  reserved-area-string-guard-lemma-2
  (implies (and (lofat-fs-p fat32-in-memory)
                (natp i)
                (< i (fat-length fat32-in-memory)))
           (and (integerp (fati i fat32-in-memory))
                (<= 0 (fati i fat32-in-memory))
                (< (fati i fat32-in-memory) 4294967296)))
  :rule-classes
  ((:rewrite
    :corollary (implies (and (lofat-fs-p fat32-in-memory)
                             (natp i)
                             (< i (fat-length fat32-in-memory)))
                        (integerp (fati i fat32-in-memory))))
   (:linear
    :corollary (implies (and (lofat-fs-p fat32-in-memory)
                             (natp i)
                             (< i (fat-length fat32-in-memory)))
                        (and (<= 0 (fati i fat32-in-memory))
                             (< (fati i fat32-in-memory)
                                4294967296)))))
  :hints
  (("goal"
    :in-theory
    (e/d (lofat-fs-p fat32-entry-p)
         (fati fati-when-lofat-fs-p))
    :use fati-when-lofat-fs-p)))

(encapsulate
  ()

  (local
   (defthm
     reserved-area-string-guard-lemma-3
     (implies (and (logtail-guard size i)
                   (unsigned-byte-p (+ size 8) i))
              (and (integerp (logtail size i))
                   (<= 0 (logtail size i))
                   (< (logtail size i) 256)))
     :rule-classes
     ((:rewrite
       :corollary
       (implies (and (logtail-guard size i)
                     (unsigned-byte-p (+ size 8) i))
                (integerp (logtail size i))))
      (:linear
       :corollary
       (implies (and (logtail-guard size i)
                     (unsigned-byte-p (+ size 8) i))
                (and (<= 0 (logtail size i))
                     (< (logtail size i) 256)))))
     :hints
     (("goal" :in-theory (disable logtail-unsigned-byte-p)
       :use (:instance logtail-unsigned-byte-p (size1 8))))))

  (defund reserved-area-chars (fat32-in-memory)
    (declare (xargs :stobjs fat32-in-memory
                    :guard (lofat-fs-p fat32-in-memory)
                    :guard-hints (("Goal"
                                   :do-not-induct t
                                   :in-theory (disable bs_vollabi
                                                       bs_jmpbooti
                                                       bs_oemnamei
                                                       bs_filsystypei
                                                       bpb_reservedi
                                                       reserved-area-string-guard-lemma-2)
                                   :use
                                   reserved-area-string-guard-lemma-2))))
    (append
     ;; initial bytes
     (list (code-char (bs_jmpbooti 0 fat32-in-memory))
           (code-char (bs_jmpbooti 1 fat32-in-memory))
           (code-char (bs_jmpbooti 2 fat32-in-memory)))
     (list (code-char (bs_oemnamei 0 fat32-in-memory))
           (code-char (bs_oemnamei 1 fat32-in-memory))
           (code-char (bs_oemnamei 2 fat32-in-memory))
           (code-char (bs_oemnamei 3 fat32-in-memory))
           (code-char (bs_oemnamei 4 fat32-in-memory))
           (code-char (bs_oemnamei 5 fat32-in-memory))
           (code-char (bs_oemnamei 6 fat32-in-memory))
           (code-char (bs_oemnamei 7 fat32-in-memory)))
     (list (code-char (loghead 8 (bpb_bytspersec fat32-in-memory)))
           (code-char (logtail 8 (bpb_bytspersec fat32-in-memory)))
           (code-char (bpb_secperclus fat32-in-memory))
           (code-char (loghead 8 (bpb_rsvdseccnt fat32-in-memory)))
           (code-char (logtail 8 (bpb_rsvdseccnt fat32-in-memory))))
     ;; remaining reserved bytes
     (list (code-char (bpb_numfats fat32-in-memory))
           (code-char (loghead 8 (bpb_rootentcnt fat32-in-memory)))
           (code-char (logtail 8 (bpb_rootentcnt fat32-in-memory)))
           (code-char (loghead 8 (bpb_totsec16 fat32-in-memory)))
           (code-char (logtail 8 (bpb_totsec16 fat32-in-memory)))
           (code-char (bpb_media fat32-in-memory))
           (code-char (loghead 8 (bpb_fatsz16 fat32-in-memory)))
           (code-char (logtail 8 (bpb_fatsz16 fat32-in-memory)))
           (code-char (loghead 8 (bpb_secpertrk fat32-in-memory)))
           (code-char (logtail 8 (bpb_secpertrk fat32-in-memory)))
           (code-char (loghead 8 (bpb_numheads fat32-in-memory)))
           (code-char (logtail 8 (bpb_numheads fat32-in-memory)))
           (code-char (loghead 8             (bpb_hiddsec fat32-in-memory) ))
           (code-char (loghead 8 (logtail  8 (bpb_hiddsec fat32-in-memory))))
           (code-char (loghead 8 (logtail 16 (bpb_hiddsec fat32-in-memory))))
           (code-char            (logtail 24 (bpb_hiddsec fat32-in-memory)) )
           (code-char (loghead 8             (bpb_totsec32 fat32-in-memory) ))
           (code-char (loghead 8 (logtail  8 (bpb_totsec32 fat32-in-memory))))
           (code-char (loghead 8 (logtail 16 (bpb_totsec32 fat32-in-memory))))
           (code-char            (logtail 24 (bpb_totsec32 fat32-in-memory)) )
           (code-char (loghead 8             (bpb_fatsz32 fat32-in-memory) ))
           (code-char (loghead 8 (logtail  8 (bpb_fatsz32 fat32-in-memory))))
           (code-char (loghead 8 (logtail 16 (bpb_fatsz32 fat32-in-memory))))
           (code-char            (logtail 24 (bpb_fatsz32 fat32-in-memory)) )
           (code-char (loghead 8 (bpb_extflags fat32-in-memory)))
           (code-char (logtail 8 (bpb_extflags fat32-in-memory)))
           (code-char (bpb_fsver_minor fat32-in-memory))
           (code-char (bpb_fsver_major fat32-in-memory))
           (code-char (loghead 8             (bpb_rootclus fat32-in-memory) ))
           (code-char (loghead 8 (logtail  8 (bpb_rootclus fat32-in-memory))))
           (code-char (loghead 8 (logtail 16 (bpb_rootclus fat32-in-memory))))
           (code-char            (logtail 24 (bpb_rootclus fat32-in-memory)) )
           (code-char (loghead 8 (bpb_fsinfo fat32-in-memory)))
           (code-char (logtail 8 (bpb_fsinfo fat32-in-memory)))
           (code-char (loghead 8 (bpb_bkbootsec fat32-in-memory)))
           (code-char (logtail 8 (bpb_bkbootsec fat32-in-memory))))
     (list (code-char (bpb_reservedi  0 fat32-in-memory))
           (code-char (bpb_reservedi  1 fat32-in-memory))
           (code-char (bpb_reservedi  2 fat32-in-memory))
           (code-char (bpb_reservedi  3 fat32-in-memory))
           (code-char (bpb_reservedi  4 fat32-in-memory))
           (code-char (bpb_reservedi  5 fat32-in-memory))
           (code-char (bpb_reservedi  6 fat32-in-memory))
           (code-char (bpb_reservedi  7 fat32-in-memory))
           (code-char (bpb_reservedi  8 fat32-in-memory))
           (code-char (bpb_reservedi  9 fat32-in-memory))
           (code-char (bpb_reservedi 10 fat32-in-memory))
           (code-char (bpb_reservedi 11 fat32-in-memory)))
     (list (code-char (bs_drvnum fat32-in-memory))
           (code-char (bs_reserved1 fat32-in-memory))
           (code-char (bs_bootsig fat32-in-memory))
           (code-char (loghead 8             (bs_volid fat32-in-memory) ))
           (code-char (loghead 8 (logtail  8 (bs_volid fat32-in-memory))))
           (code-char (loghead 8 (logtail 16 (bs_volid fat32-in-memory))))
           (code-char            (logtail 24 (bs_volid fat32-in-memory)) ))
     (list (code-char (bs_vollabi  0 fat32-in-memory))
           (code-char (bs_vollabi  1 fat32-in-memory))
           (code-char (bs_vollabi  2 fat32-in-memory))
           (code-char (bs_vollabi  3 fat32-in-memory))
           (code-char (bs_vollabi  4 fat32-in-memory))
           (code-char (bs_vollabi  5 fat32-in-memory))
           (code-char (bs_vollabi  6 fat32-in-memory))
           (code-char (bs_vollabi  7 fat32-in-memory))
           (code-char (bs_vollabi  8 fat32-in-memory))
           (code-char (bs_vollabi  9 fat32-in-memory))
           (code-char (bs_vollabi 10 fat32-in-memory)))
     (list (code-char (bs_filsystypei 0 fat32-in-memory))
           (code-char (bs_filsystypei 1 fat32-in-memory))
           (code-char (bs_filsystypei 2 fat32-in-memory))
           (code-char (bs_filsystypei 3 fat32-in-memory))
           (code-char (bs_filsystypei 4 fat32-in-memory))
           (code-char (bs_filsystypei 5 fat32-in-memory))
           (code-char (bs_filsystypei 6 fat32-in-memory))
           (code-char (bs_filsystypei 7 fat32-in-memory)))
     (make-list
      (- (* (bpb_rsvdseccnt fat32-in-memory) (bpb_bytspersec fat32-in-memory)) 90)
      :initial-element (code-char 0)))))

(defthm character-listp-of-reserved-area-chars
  (character-listp (reserved-area-chars fat32-in-memory))
  :hints (("Goal" :in-theory (enable reserved-area-chars))))

(defthm
  len-of-reserved-area-chars
  (implies
   (lofat-fs-p fat32-in-memory)
   (equal (len (reserved-area-chars fat32-in-memory))
          (* (bpb_rsvdseccnt fat32-in-memory)
             (bpb_bytspersec fat32-in-memory))))
  :hints (("goal" :in-theory (enable reserved-area-chars))))

(defund
  reserved-area-string (fat32-in-memory)
  (declare
   (xargs :stobjs fat32-in-memory
          :guard (lofat-fs-p fat32-in-memory)))
  (implode (reserved-area-chars fat32-in-memory)))

(defthm
  length-of-reserved-area-string
  (implies
   (lofat-fs-p fat32-in-memory)
   (equal (len (explode (reserved-area-string fat32-in-memory)))
          (* (bpb_rsvdseccnt fat32-in-memory)
             (bpb_bytspersec fat32-in-memory))))
  :hints (("goal" :in-theory (enable reserved-area-string))))

;; This seems like the only way...
;; There is an automatic way to do this proof, but I can't recall it.
(defthm
  nth-of-explode-of-reserved-area-string
  (equal
   (nth n
        (explode (reserved-area-string fat32-in-memory)))
   (nth
    n
    (append
     (list (code-char (bs_jmpbooti 0 fat32-in-memory))
           (code-char (bs_jmpbooti 1 fat32-in-memory))
           (code-char (bs_jmpbooti 2 fat32-in-memory)))
     (list (code-char (bs_oemnamei 0 fat32-in-memory))
           (code-char (bs_oemnamei 1 fat32-in-memory))
           (code-char (bs_oemnamei 2 fat32-in-memory))
           (code-char (bs_oemnamei 3 fat32-in-memory))
           (code-char (bs_oemnamei 4 fat32-in-memory))
           (code-char (bs_oemnamei 5 fat32-in-memory))
           (code-char (bs_oemnamei 6 fat32-in-memory))
           (code-char (bs_oemnamei 7 fat32-in-memory)))
     (list (code-char (loghead 8 (bpb_bytspersec fat32-in-memory)))
           (code-char (logtail 8 (bpb_bytspersec fat32-in-memory)))
           (code-char (bpb_secperclus fat32-in-memory))
           (code-char (loghead 8 (bpb_rsvdseccnt fat32-in-memory)))
           (code-char (logtail 8 (bpb_rsvdseccnt fat32-in-memory))))
     (list (code-char (bpb_numfats fat32-in-memory))
           (code-char (loghead 8 (bpb_rootentcnt fat32-in-memory)))
           (code-char (logtail 8 (bpb_rootentcnt fat32-in-memory)))
           (code-char (loghead 8 (bpb_totsec16 fat32-in-memory)))
           (code-char (logtail 8 (bpb_totsec16 fat32-in-memory)))
           (code-char (bpb_media fat32-in-memory))
           (code-char (loghead 8 (bpb_fatsz16 fat32-in-memory)))
           (code-char (logtail 8 (bpb_fatsz16 fat32-in-memory)))
           (code-char (loghead 8 (bpb_secpertrk fat32-in-memory)))
           (code-char (logtail 8 (bpb_secpertrk fat32-in-memory)))
           (code-char (loghead 8 (bpb_numheads fat32-in-memory)))
           (code-char (logtail 8 (bpb_numheads fat32-in-memory)))
           (code-char (loghead 8 (bpb_hiddsec fat32-in-memory)))
           (code-char (loghead 8
                               (logtail 8 (bpb_hiddsec fat32-in-memory))))
           (code-char (loghead 8
                               (logtail 16 (bpb_hiddsec fat32-in-memory))))
           (code-char (logtail 24 (bpb_hiddsec fat32-in-memory)))
           (code-char (loghead 8 (bpb_totsec32 fat32-in-memory)))
           (code-char (loghead 8
                               (logtail 8 (bpb_totsec32 fat32-in-memory))))
           (code-char (loghead 8
                               (logtail 16 (bpb_totsec32 fat32-in-memory))))
           (code-char (logtail 24 (bpb_totsec32 fat32-in-memory)))
           (code-char (loghead 8 (bpb_fatsz32 fat32-in-memory)))
           (code-char (loghead 8
                               (logtail 8 (bpb_fatsz32 fat32-in-memory))))
           (code-char (loghead 8
                               (logtail 16 (bpb_fatsz32 fat32-in-memory))))
           (code-char (logtail 24 (bpb_fatsz32 fat32-in-memory)))
           (code-char (loghead 8 (bpb_extflags fat32-in-memory)))
           (code-char (logtail 8 (bpb_extflags fat32-in-memory)))
           (code-char (bpb_fsver_minor fat32-in-memory))
           (code-char (bpb_fsver_major fat32-in-memory))
           (code-char (loghead 8 (bpb_rootclus fat32-in-memory)))
           (code-char (loghead 8
                               (logtail 8 (bpb_rootclus fat32-in-memory))))
           (code-char (loghead 8
                               (logtail 16 (bpb_rootclus fat32-in-memory))))
           (code-char (logtail 24 (bpb_rootclus fat32-in-memory)))
           (code-char (loghead 8 (bpb_fsinfo fat32-in-memory)))
           (code-char (logtail 8 (bpb_fsinfo fat32-in-memory)))
           (code-char (loghead 8 (bpb_bkbootsec fat32-in-memory)))
           (code-char (logtail 8 (bpb_bkbootsec fat32-in-memory))))
     (list (code-char (bpb_reservedi 0 fat32-in-memory))
           (code-char (bpb_reservedi 1 fat32-in-memory))
           (code-char (bpb_reservedi 2 fat32-in-memory))
           (code-char (bpb_reservedi 3 fat32-in-memory))
           (code-char (bpb_reservedi 4 fat32-in-memory))
           (code-char (bpb_reservedi 5 fat32-in-memory))
           (code-char (bpb_reservedi 6 fat32-in-memory))
           (code-char (bpb_reservedi 7 fat32-in-memory))
           (code-char (bpb_reservedi 8 fat32-in-memory))
           (code-char (bpb_reservedi 9 fat32-in-memory))
           (code-char (bpb_reservedi 10 fat32-in-memory))
           (code-char (bpb_reservedi 11 fat32-in-memory)))
     (list (code-char (bs_drvnum fat32-in-memory))
           (code-char (bs_reserved1 fat32-in-memory))
           (code-char (bs_bootsig fat32-in-memory))
           (code-char (loghead 8 (bs_volid fat32-in-memory)))
           (code-char (loghead 8
                               (logtail 8 (bs_volid fat32-in-memory))))
           (code-char (loghead 8
                               (logtail 16 (bs_volid fat32-in-memory))))
           (code-char (logtail 24 (bs_volid fat32-in-memory))))
     (list (code-char (bs_vollabi 0 fat32-in-memory))
           (code-char (bs_vollabi 1 fat32-in-memory))
           (code-char (bs_vollabi 2 fat32-in-memory))
           (code-char (bs_vollabi 3 fat32-in-memory))
           (code-char (bs_vollabi 4 fat32-in-memory))
           (code-char (bs_vollabi 5 fat32-in-memory))
           (code-char (bs_vollabi 6 fat32-in-memory))
           (code-char (bs_vollabi 7 fat32-in-memory))
           (code-char (bs_vollabi 8 fat32-in-memory))
           (code-char (bs_vollabi 9 fat32-in-memory))
           (code-char (bs_vollabi 10 fat32-in-memory)))
     (list (code-char (bs_filsystypei 0 fat32-in-memory))
           (code-char (bs_filsystypei 1 fat32-in-memory))
           (code-char (bs_filsystypei 2 fat32-in-memory))
           (code-char (bs_filsystypei 3 fat32-in-memory))
           (code-char (bs_filsystypei 4 fat32-in-memory))
           (code-char (bs_filsystypei 5 fat32-in-memory))
           (code-char (bs_filsystypei 6 fat32-in-memory))
           (code-char (bs_filsystypei 7 fat32-in-memory)))
     (make-list (- (* (bpb_rsvdseccnt fat32-in-memory)
                      (bpb_bytspersec fat32-in-memory))
                   90)
                :initial-element (code-char 0)))))
  
  :instructions ((:dive 1 2 1)
                 :x
                 :up (:rewrite str::explode-of-implode)
                 :s (:rewrite str::make-character-list-when-character-listp)
                 :x :top
                 :bash :bash))

;; A bit of explanation is in order here - this function recurs on n, which is
;; instantiated with (bpb_numfats fat32-in-memory) in
;; lofat-to-string. stobj-fa-table-to-string, in contrast, generates
;; one copy of the FAT string from the fat32-in-memory instance, and does all
;; the part-select heavy lifting.
(defund
  make-fat-string-ac
  (n fat32-in-memory ac)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (and (lofat-fs-p fat32-in-memory)
                (natp n)
                (stringp ac))))
  (b* (((when (zp n)) ac)
       (fa-table-string
        (stobj-fa-table-to-string fat32-in-memory)))
    (make-fat-string-ac (1- n)
                        fat32-in-memory
                        (concatenate 'string
                                     fa-table-string ac))))

(defthm
  length-of-stobj-fa-table-to-string
  (equal
   (len
    (explode (stobj-fa-table-to-string fat32-in-memory)))
   (* (fat-length fat32-in-memory) 4))
  :hints (("goal" :in-theory (enable stobj-fa-table-to-string))))

(defthm
  length-of-make-fat-string-ac
  (equal
   (len (explode (make-fat-string-ac n fat32-in-memory ac)))
   (+ (* (nfix n)
         (fat-length fat32-in-memory)
         4)
      (len (explode ac))))
  :hints (("Goal" :in-theory (enable make-fat-string-ac))))

(defun
    data-region-string-helper
    (fat32-in-memory len ac)
  (declare
   (xargs
    :stobjs (fat32-in-memory)
    :guard (and (natp len)
                (lofat-fs-p fat32-in-memory)
                (<= len
                    (data-region-length fat32-in-memory))
                (character-listp ac))
    :guard-hints
    (("goal" :in-theory (enable by-slice-you-mean-the-whole-cake-2)))))
  (if
      (zp len)
      (mbe :exec ac
           :logic (make-character-list ac))
    (data-region-string-helper
     fat32-in-memory (- len 1)
     (append
      (mbe :exec (coerce (data-regioni (- len 1) fat32-in-memory)
                         'list)
           :logic (take (cluster-size fat32-in-memory)
                        (coerce (data-regioni (- len 1) fat32-in-memory)
                                'list)))
      ac))))

(defthm
  character-listp-of-data-region-string-helper
  (character-listp
   (data-region-string-helper fat32-in-memory len ac))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (equal
     (make-character-list
      (data-region-string-helper fat32-in-memory len ac))
     (data-region-string-helper fat32-in-memory len ac)))
   (:type-prescription
    :corollary
    (true-listp
     (data-region-string-helper fat32-in-memory len ac)))))

(defthm
  len-of-data-region-string-helper
  (equal
   (len (data-region-string-helper fat32-in-memory len ac))
   (+ (len ac)
      (* (nfix len)
         (nfix (cluster-size fat32-in-memory))))))

;; Later
;; (thm
;;  (implies
;;   (and (natp len)
;;        (lofat-fs-p fat32-in-memory)
;;        (<= len
;;            (data-region-length fat32-in-memory))
;;        (character-listp ac))
;;   (equal
;;    (make-clusters
;;     (implode
;;      (data-region-string-helper
;;       fat32-in-memory len ac))
;;     (cluster-size fat32-in-memory))
;;    (append
;;     (take
;;      len
;;      (nth *data-regioni* fat32-in-memory))
;;     (make-clusters
;;      (implode ac)
;;      (cluster-size fat32-in-memory)))))
;;  :hints (("Goal" :in-theory (enable make-clusters remember-that-time-with-update-nth
;;                                     append-of-take-and-cons)
;;           :induct
;;           (data-region-string-helper fat32-in-memory len ac))
;;          ("Subgoal *1/2.2"
;;           :expand
;;           (make-clusters
;;            (implode (append (take (cluster-size fat32-in-memory)
;;                                   (explode (data-regioni (+ -1 len)
;;                                                          fat32-in-memory)))
;;                             ac))
;;            (cluster-size fat32-in-memory))
;;           :use
;;           (:theorem
;;            (equal
;;             (+ (CLUSTER-SIZE FAT32-IN-MEMORY)
;;                (- (CLUSTER-SIZE FAT32-IN-MEMORY))
;;                (LEN AC))
;;             (len ac))))))

(defun
    princ$-data-region-string-helper
    (fat32-in-memory len channel state)
  (declare
   (xargs
    :stobjs (fat32-in-memory state)
    :guard (and (natp len)
                (lofat-fs-p fat32-in-memory)
                (<= len
                    (data-region-length fat32-in-memory))
                (symbolp channel)
                (open-output-channel-p channel
                                       :character state))
    :verify-guards nil))
  (b*
      (((when (zp len)) state)
       (state
        (princ$-data-region-string-helper
         fat32-in-memory (- len 1)
         channel
         state)))
    (princ$ (data-regioni (- len 1) fat32-in-memory) channel state)))

(defthm
  princ$-data-region-string-helper-guard-lemma-1
  (implies
   (and (open-output-channel-p1 channel
                                :character state)
        (symbolp channel)
        (<= len
            (data-region-length fat32-in-memory))
        (lofat-fs-p fat32-in-memory)
        (natp len)
        (state-p1 state))
   (and (open-output-channel-p1
         channel
         :character (princ$-data-region-string-helper
                     fat32-in-memory len channel state))
        (state-p1 (princ$-data-region-string-helper
                   fat32-in-memory len channel state))))
  :hints
  (("goal" :induct (princ$-data-region-string-helper
                    fat32-in-memory len channel state))))

(verify-guards
  princ$-data-region-string-helper)

(defthm
  data-region-string-helper-of-binary-append
  (implies
   (and (natp len)
        (lofat-fs-p fat32-in-memory)
        (<= len
            (data-region-length fat32-in-memory))
        (character-listp ac1)
        (character-listp ac2))
   (equal
    (data-region-string-helper fat32-in-memory
                               len (binary-append ac1 ac2))
    (binary-append
     (data-region-string-helper fat32-in-memory len ac1)
     ac2))))

(defthm
  princ$-data-region-string-helper-correctness-1
  (implies
   (and (natp len)
        (lofat-fs-p fat32-in-memory)
        (<= len
            (data-region-length fat32-in-memory))
        (character-listp ac))
   (equal
    (princ$
     (coerce (data-region-string-helper fat32-in-memory len ac)
             'string)
     channel state)
    (princ$ (coerce ac 'string)
            channel
            (princ$-data-region-string-helper
             fat32-in-memory len channel state))))
  :hints (("Goal" :in-theory (enable by-slice-you-mean-the-whole-cake-2))))

(defund
  lofat-to-string
  (fat32-in-memory)
  (declare
   (xargs :stobjs fat32-in-memory
          :guard (lofat-fs-p fat32-in-memory)))
  (b* ((reserved-area-string
        (reserved-area-string fat32-in-memory))
       (fat-string
        (make-fat-string-ac (bpb_numfats fat32-in-memory)
                            fat32-in-memory ""))
       (data-region-string
        (coerce (data-region-string-helper
                 fat32-in-memory
                 (data-region-length fat32-in-memory)
                 nil)
                'string)))
    (concatenate 'string
                 reserved-area-string
                 fat-string data-region-string)))

(defthm
  length-of-lofat-to-string-lemma-1
  (implies (lofat-fs-p fat32-in-memory)
           (and
           (equal (nfix (bpb_numfats fat32-in-memory))
                  (bpb_numfats fat32-in-memory))
           (equal (nfix (count-of-clusters fat32-in-memory))
                  (count-of-clusters fat32-in-memory))))
  :hints (("goal" :in-theory (enable lofat-fs-p
                                     fat32-in-memoryp
                                     bpb_numfats))))

(defthm
  length-of-lofat-to-string
  (implies
   (lofat-fs-p fat32-in-memory)
   (equal
    (len
     (explode (lofat-to-string fat32-in-memory)))
    (+ (* (bpb_rsvdseccnt fat32-in-memory)
          (bpb_bytspersec fat32-in-memory))
       (* (bpb_numfats fat32-in-memory)
          (fat-length fat32-in-memory)
          4)
       (* (cluster-size fat32-in-memory)
          (data-region-length fat32-in-memory)))))
  :hints
  (("goal" :in-theory (e/d (lofat-to-string) (nfix)))))

(defun
  lofat-to-disk-image
  (fat32-in-memory image-path state)
  (declare
   (xargs
    :stobjs (fat32-in-memory state)
    :guard (and (state-p state)
                (stringp image-path)
                (lofat-fs-p fat32-in-memory))
    :guard-hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d (lofat-to-string)
           (princ$-of-princ$
            princ$-data-region-string-helper-correctness-1))
      :use
      ((:instance
        princ$-of-princ$
        (state
         (mv-nth '1
                 (open-output-channel image-path ':character
                                      state)))
        (x (reserved-area-string fat32-in-memory))
        (channel
         (mv-nth '0
                 (open-output-channel image-path ':character
                                      state)))
        (y (make-fat-string-ac (bpb_numfats fat32-in-memory)
                               fat32-in-memory '"")))
       (:instance
        princ$-of-princ$
        (state
         (mv-nth '1
                 (open-output-channel image-path ':character
                                      state)))
        (x
         (string-append
          (reserved-area-string fat32-in-memory)
          (make-fat-string-ac (bpb_numfats fat32-in-memory)
                              fat32-in-memory "")))
        (channel
         (mv-nth '0
                 (open-output-channel image-path ':character
                                      state)))
        (y (implode$inline
            (data-region-string-helper
             fat32-in-memory
             (data-region-length fat32-in-memory)
             'nil))))
       (:instance
        princ$-data-region-string-helper-correctness-1
        (ac nil)
        (len (data-region-length fat32-in-memory))
        (state
         (princ$
          (implode
           (append
            (explode (reserved-area-string fat32-in-memory))
            (explode
             (make-fat-string-ac (bpb_numfats fat32-in-memory)
                                 fat32-in-memory ""))))
          (mv-nth 0
                  (open-output-channel image-path
                                       :character state))
          (mv-nth 1
                  (open-output-channel image-path
                                       :character state))))
        (channel
         (mv-nth 0
                 (open-output-channel image-path
                                      :character state)))))))))
  (b*
      (((mv channel state)
        (open-output-channel image-path
                             :character state))
       ((when (null channel)) state)
       (state
        (mbe
         :logic (princ$ (lofat-to-string fat32-in-memory)
                        channel state)
         :exec
         (b*
             ((state (princ$ (reserved-area-string fat32-in-memory)
                             channel state))
              (state
               (princ$
                (make-fat-string-ac (bpb_numfats fat32-in-memory)
                                    fat32-in-memory "")
                channel state))
              (state (princ$-data-region-string-helper
                      fat32-in-memory
                      (data-region-length fat32-in-memory)
                      channel state)))
           (princ$ "" channel state))))
       (state (close-output-channel channel state)))
    state))

(defthm
  data-regioni-of-stobj-set-clusters
  (implies
   (and (natp i)
        (not (member-equal (+ i *ms-first-data-cluster*)
                           index-list)))
   (equal (data-regioni i
                        (stobj-set-clusters cluster-list
                                            index-list fat32-in-memory))
          (data-regioni i fat32-in-memory))))

(defthm
  get-clusterchain-contents-of-place-contents-disjoint
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (stringp contents)
    (integerp first-cluster)
    (<= 2 first-cluster)
    (fat32-masked-entry-p masked-current-cluster)
    (equal
     (mv-nth
      1
      (get-clusterchain-contents fat32-in-memory
                                 masked-current-cluster length))
     0)
    (not (member-equal
          first-cluster
          (mv-nth 0
                  (fat32-build-index-list
                   (effective-fat fat32-in-memory)
                   masked-current-cluster length
                   (cluster-size fat32-in-memory))))))
   (equal
    (get-clusterchain-contents
     (mv-nth
      0
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))
     masked-current-cluster length)
    (get-clusterchain-contents fat32-in-memory
                               masked-current-cluster length)))
  :hints
  (("goal"
    :in-theory (e/d (place-contents intersectp-equal
                                    get-clusterchain-contents)
                    (intersectp-is-commutative)))))

(defthm
  effective-fat-of-stobj-set-clusters
  (equal (effective-fat
          (stobj-set-clusters cluster-list
                              index-list fat32-in-memory))
         (effective-fat fat32-in-memory)))

(defthm
  lofat-to-hifat-helper-of-place-contents-lemma-1
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (<= 2 masked-current-cluster)
    (fat32-masked-entry-p masked-current-cluster)
    (integerp first-cluster)
    (>= first-cluster *ms-first-data-cluster*)
    (stringp contents)
    (not (member-equal
          first-cluster
          (mv-nth 0
                  (fat32-build-index-list (effective-fat fat32-in-memory)
                                          masked-current-cluster
                                          length cluster-size))))
    (equal (mv-nth 1
                   (fat32-build-index-list (effective-fat fat32-in-memory)
                                           masked-current-cluster
                                           length cluster-size))
           0))
   (equal
    (fat32-build-index-list
     (effective-fat
      (mv-nth 0
              (place-contents fat32-in-memory dir-ent
                              contents file-length first-cluster)))
     masked-current-cluster
     length cluster-size)
    (fat32-build-index-list (effective-fat fat32-in-memory)
                            masked-current-cluster
                            length cluster-size)))
  :hints
  (("goal"
    :in-theory
    (e/d (place-contents)
         ((:rewrite fat32-masked-entry-list-p-of-find-n-free-clusters
                    . 1)
          (:rewrite intersectp-is-commutative)))
    :do-not-induct t
    :use
    ((:instance (:rewrite fat32-masked-entry-list-p-of-find-n-free-clusters
                          . 1)
                (n (+ -1
                      (len (make-clusters contents
                                          (cluster-size fat32-in-memory)))))
                (fa-table (effective-fat fat32-in-memory)))
     (:instance
      (:rewrite intersectp-is-commutative)
      (y
       (cons first-cluster
             (find-n-free-clusters
              (effective-fat fat32-in-memory)
              (+ -1
                 (len (make-clusters contents
                                     (cluster-size fat32-in-memory)))))))
      (x (mv-nth 0
                 (fat32-build-index-list (effective-fat fat32-in-memory)
                                         masked-current-cluster
                                         length cluster-size)))))
    :expand
    (intersectp-equal
     (cons first-cluster
           (find-n-free-clusters
            (effective-fat fat32-in-memory)
            (+ -1
               (len (make-clusters contents
                                   (cluster-size fat32-in-memory))))))
     (mv-nth 0
             (fat32-build-index-list (effective-fat fat32-in-memory)
                                     masked-current-cluster
                                     length cluster-size))))))

(defthm
  lofat-to-hifat-helper-of-place-contents
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (stringp contents)
        (integerp first-cluster)
        (>= first-cluster *ms-first-data-cluster*)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper
                        fat32-in-memory
                        dir-ent-list entry-limit))
               0)
        (not-intersectp-list
         (list first-cluster)
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  dir-ent-list entry-limit)))
        (dir-ent-list-p dir-ent-list))
   (equal
    (lofat-to-hifat-helper
     (mv-nth
      0
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))
     dir-ent-list entry-limit)
    (lofat-to-hifat-helper fat32-in-memory
                                     dir-ent-list entry-limit)))
  :hints
  (("goal"
    :in-theory
    (e/d (lofat-to-hifat-helper)
         (dir-ent-fix))
    :induct
    (lofat-to-hifat-helper fat32-in-memory
                                     dir-ent-list entry-limit)
    :expand
    ((lofat-to-hifat-helper
      (mv-nth
       0
       (place-contents fat32-in-memory dir-ent
                       contents file-length first-cluster))
      dir-ent-list entry-limit)
     (:free (y)
            (intersectp-equal (list first-cluster)
                              y))))))

(defthm
  get-clusterchain-contents-of-update-fati
  (implies
   (and
    (integerp masked-current-cluster)
    (not
     (member-equal
      i
      (mv-nth 0
              (fat32-build-index-list (effective-fat fat32-in-memory)
                                      masked-current-cluster length
                                      (cluster-size fat32-in-memory))))))
   (equal (get-clusterchain-contents (update-fati i v fat32-in-memory)
                                     masked-current-cluster length)
          (get-clusterchain-contents fat32-in-memory
                                     masked-current-cluster length)))
  :hints
  (("goal"
    :in-theory (enable get-clusterchain-contents)
    :induct (get-clusterchain-contents fat32-in-memory
                                       masked-current-cluster length)
    :expand ((get-clusterchain-contents (update-fati i v fat32-in-memory)
                                        masked-current-cluster length)))))

(defthm
  lofat-to-hifat-helper-of-update-fati
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (dir-ent-list-p dir-ent-list)
        (< (nfix i)
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory)))
        (not-intersectp-list
         (list i)
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  dir-ent-list entry-limit)))
        (equal (mv-nth 3
                       (lofat-to-hifat-helper
                        fat32-in-memory
                        dir-ent-list entry-limit))
               0))
   (equal
    (lofat-to-hifat-helper
     (update-fati i v fat32-in-memory)
     dir-ent-list entry-limit)
    (lofat-to-hifat-helper fat32-in-memory
                                     dir-ent-list entry-limit)))
  :hints
  (("goal"
    :induct
    (lofat-to-hifat-helper fat32-in-memory
                                     dir-ent-list entry-limit)
    :expand ((lofat-to-hifat-helper
              (update-fati i v fat32-in-memory)
              dir-ent-list entry-limit)
             (:free (x y)
                    (intersectp-equal (list x) y))
             (:free (y) (intersectp-equal nil y)))
    :in-theory
    (e/d
     (lofat-to-hifat-helper)
     ((:rewrite natp-of-cluster-size . 1)
      (:definition fat32-build-index-list))))
   ;; This case split, below, is needed because :brr shows ACL2 hesitating
   ;; before a case split it needs to do...
   ("Subgoal *1/3" :cases ((natp i)))))

(encapsulate
  ()

  (local
   (in-theory (enable by-slice-you-mean-the-whole-cake-2)))

  (local
   (defun induction-scheme
       (index-list text cluster-size length)
     (if (or (zp (length text))
             (zp cluster-size))
         (mv index-list length)
         (induction-scheme
          (cdr index-list)
          (subseq text (min cluster-size (length text))
                  nil)
          cluster-size
          (+ length (- cluster-size))))))

  (local
   (defthm
     get-contents-from-clusterchain-of-stobj-set-clusters-coincident-lemma-1
     (iff (equal (+ 1 (len x)) 1) (atom x))))

  (local
   (in-theory (enable make-clusters
                      nthcdr-when->=-n-len-l)))

  (defthm
    get-contents-from-clusterchain-of-stobj-set-clusters-coincident
    (implies
     (and
      (stringp text)
      (equal
       (len (make-clusters text (cluster-size fat32-in-memory)))
       (len index-list))
      (integerp length)
      (>= length (length text))
      (lower-bounded-integer-listp
       index-list *ms-first-data-cluster*)
      (bounded-nat-listp
       index-list
       (+ 2 (data-region-length fat32-in-memory)))
      (lofat-fs-p fat32-in-memory)
      (no-duplicatesp-equal index-list))
     (equal
      (get-contents-from-clusterchain
       (stobj-set-clusters
        (make-clusters text (cluster-size fat32-in-memory))
        index-list fat32-in-memory)
       index-list length)
      (implode
       (append
        (explode text)
        (make-list (- (min length
                           (* (len index-list)
                              (cluster-size fat32-in-memory)))
                      (length text))
                   :initial-element (code-char 0))))))
    :hints
    (("goal"
      :induct
      (induction-scheme index-list
                        text (cluster-size fat32-in-memory)
                        length)
      :expand
      ((:free (fat32-in-memory length)
              (get-contents-from-clusterchain
               fat32-in-memory index-list length))
       (make-clusters text (cluster-size fat32-in-memory))))
     ("subgoal *1/2"
      :in-theory
      (disable (:rewrite associativity-of-append))
      :use
      ((:instance
        (:rewrite associativity-of-append)
        (c (make-list-ac (+ (cluster-size fat32-in-memory)
                            (- (len (explode text)))
                            (* (cluster-size fat32-in-memory)
                               (len (cdr index-list))))
                         #\  nil))
        (b (nthcdr (cluster-size fat32-in-memory)
                   (explode text)))
        (a (take (cluster-size fat32-in-memory)
                 (explode text))))
       (:instance
        (:rewrite associativity-of-append)
        (c (make-list-ac (+ length (- (len (explode text))))
                         #\  nil))
        (b (nthcdr (cluster-size fat32-in-memory)
                   (explode text)))
        (a (take (cluster-size fat32-in-memory)
                 (explode text))))
       (:theorem (equal (+ (cluster-size fat32-in-memory)
                           (- (cluster-size fat32-in-memory))
                           (- (len (explode text))))
                        (- (len (explode text)))))))
     ("subgoal *1/1" :expand ((len (explode text))
                              (len index-list))))))

(defthm
  get-contents-from-clusterchain-of-stobj-set-indices-in-fa-table
  (equal
   (get-contents-from-clusterchain
    (stobj-set-indices-in-fa-table
     fat32-in-memory index-list value-list)
    clusterchain file-size)
   (get-contents-from-clusterchain fat32-in-memory
                                   clusterchain file-size)))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    get-clusterchain-contents-of-place-contents-coincident-lemma-1
    (implies (not (zp x))
             (<= (* x
                    (len (find-n-free-clusters fa-table n)))
                 (* x (nfix n))))
    :rule-classes :linear))

(defthm
  get-clusterchain-contents-of-place-contents-coincident
  (implies
   (and
    (equal
     (mv-nth
      2
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))
     0)
    (not (zp (length contents)))
    (<= *ms-first-data-cluster* first-cluster)
    (stringp contents)
    (integerp length)
    (<= (length contents) length)
    (lofat-fs-p fat32-in-memory)
    (not
     (equal
      (fat32-entry-mask (fati first-cluster fat32-in-memory))
      0))
    (< first-cluster
       (+ 2 (count-of-clusters fat32-in-memory)))
    (fat32-masked-entry-p first-cluster))
   (equal
    (get-clusterchain-contents
     (mv-nth
      0
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))
     first-cluster length)
    (mv
     (implode
      (append
       (explode contents)
       (make-list
        (+
         (min
          length
          (*
           (len (make-clusters contents
                               (cluster-size fat32-in-memory)))
           (cluster-size fat32-in-memory)))
         (- (length contents)))
        :initial-element (code-char 0))))
     0)))
  :hints
  (("goal" :in-theory (e/d (place-contents)
                           ((:rewrite
                             fat32-build-index-list-of-set-indices-in-fa-table)
                            (:rewrite get-clusterchain-contents-correctness-3)
                            (:rewrite get-clusterchain-contents-correctness-2)
                            (:rewrite get-clusterchain-contents-correctness-1)))
    :do-not-induct t
    :use
    ((:instance
      (:rewrite get-clusterchain-contents-correctness-1)
      (length length)
      (masked-current-cluster first-cluster)
      (fat32-in-memory
       (stobj-set-indices-in-fa-table
        (stobj-set-clusters
         (make-clusters contents (cluster-size fat32-in-memory))
         (cons
          first-cluster
          (find-n-free-clusters
           (effective-fat fat32-in-memory)
           (+
            -1
            (len
             (make-clusters contents
                            (cluster-size fat32-in-memory))))))
         fat32-in-memory)
        (cons
         first-cluster
         (find-n-free-clusters
          (effective-fat fat32-in-memory)
          (+
           -1
           (len (make-clusters contents
                               (cluster-size fat32-in-memory))))))
        (append
         (find-n-free-clusters
          (effective-fat fat32-in-memory)
          (+
           -1
           (len (make-clusters contents
                               (cluster-size fat32-in-memory)))))
         '(268435455)))))
     (:instance
      (:rewrite fat32-build-index-list-of-set-indices-in-fa-table)
      (cluster-size (cluster-size fat32-in-memory))
      (file-length length)
      (file-index-list
       (cons
        first-cluster
        (find-n-free-clusters
         (effective-fat fat32-in-memory)
         (+
          -1
          (len (make-clusters contents
                              (cluster-size fat32-in-memory)))))))
      (fa-table (effective-fat fat32-in-memory)))
     (:instance
      (:rewrite get-clusterchain-contents-correctness-3)
      (length length)
      (masked-current-cluster first-cluster)
      (fat32-in-memory
       (stobj-set-indices-in-fa-table
        (stobj-set-clusters
         (make-clusters contents (cluster-size fat32-in-memory))
         (cons
          first-cluster
          (find-n-free-clusters
           (effective-fat fat32-in-memory)
           (+
            -1
            (len
             (make-clusters contents
                            (cluster-size fat32-in-memory))))))
         fat32-in-memory)
        (cons
         first-cluster
         (find-n-free-clusters
          (effective-fat fat32-in-memory)
          (+
           -1
           (len (make-clusters contents
                               (cluster-size fat32-in-memory))))))
        (append
         (find-n-free-clusters
          (effective-fat fat32-in-memory)
          (+
           -1
           (len (make-clusters contents
                               (cluster-size fat32-in-memory)))))
         '(268435455)))))
     (:instance
      (:rewrite get-clusterchain-contents-correctness-2)
      (length length)
      (masked-current-cluster first-cluster)
      (fat32-in-memory
       (stobj-set-indices-in-fa-table
        (stobj-set-clusters
         (make-clusters contents (cluster-size fat32-in-memory))
         (cons
          first-cluster
          (find-n-free-clusters
           (effective-fat fat32-in-memory)
           (+
            -1
            (len
             (make-clusters contents
                            (cluster-size fat32-in-memory))))))
         fat32-in-memory)
        (cons
         first-cluster
         (find-n-free-clusters
          (effective-fat fat32-in-memory)
          (+
           -1
           (len (make-clusters contents
                               (cluster-size fat32-in-memory))))))
        (append
         (find-n-free-clusters
          (effective-fat fat32-in-memory)
          (+
           -1
           (len (make-clusters contents
                               (cluster-size fat32-in-memory)))))
         '(268435455)))))))))

(defthm
  fati-of-place-contents-disjoint
  (implies
   (and (natp x)
        (not (equal x first-cluster))
        (< x
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory)))
        (integerp first-cluster)
        (>= first-cluster *ms-first-data-cluster*)
        (lofat-fs-p fat32-in-memory)
        (stringp contents)
        (not (equal (fat32-entry-mask (fati x fat32-in-memory))
                    0)))
   (equal
    (fati
     x
     (mv-nth
      0
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster)))
    (fati x fat32-in-memory)))
  :hints
  (("goal" :in-theory (enable place-contents))))

(defthm
  fati-of-hifat-to-lofat-helper-disjoint-lemma-1
  (implies
   (and
    (equal
     (len
      (find-n-free-clusters
       (effective-fat
        (mv-nth 0
                (hifat-to-lofat-helper fat32-in-memory fs
                                                 current-dir-first-cluster)))
       1))
     1)
    (equal
     (fati
      (nth
       0
       (find-n-free-clusters
        (effective-fat
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory fs
                                                  current-dir-first-cluster)))
        1))
      (mv-nth 0
              (hifat-to-lofat-helper fat32-in-memory fs
                                               current-dir-first-cluster)))
     (fati
      (nth
       0
       (find-n-free-clusters
        (effective-fat
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory fs
                                                  current-dir-first-cluster)))
        1))
      fat32-in-memory))
    (lofat-fs-p fat32-in-memory))
   (equal
    (fat32-entry-mask
     (fati
      (nth
       0
       (find-n-free-clusters
        (effective-fat
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory fs
                                                  current-dir-first-cluster)))
        1))
      fat32-in-memory))
    0))
  :hints
  (("goal"
    :in-theory (disable nth
                        (:rewrite find-n-free-clusters-correctness-4))
    :use
    (:instance
     (:rewrite find-n-free-clusters-correctness-4)
     (n 1)
     (fa-table
      (effective-fat
       (mv-nth 0
               (hifat-to-lofat-helper fat32-in-memory fs
                                                current-dir-first-cluster))))
     (x
      (nth
       0
       (find-n-free-clusters
        (effective-fat
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory fs
                                                  current-dir-first-cluster)))
        1)))))))

(defthm
  fati-of-hifat-to-lofat-helper-disjoint-lemma-2
  (implies
   (and
    (equal
     (len
      (find-n-free-clusters
       (effective-fat
        (mv-nth 0
                (hifat-to-lofat-helper fat32-in-memory fs
                                                 current-dir-first-cluster)))
       1))
     1)
    (equal
     (fati
      x
      (mv-nth 0
              (hifat-to-lofat-helper fat32-in-memory fs
                                               current-dir-first-cluster)))
     (fati x fat32-in-memory))
    (lofat-fs-p fat32-in-memory)
    (not (equal (fat32-entry-mask (fati x fat32-in-memory))
                0)))
   (not
    (equal
     x
     (nth
      '0
      (find-n-free-clusters
       (effective-fat
        (mv-nth '0
                (hifat-to-lofat-helper fat32-in-memory fs
                                                 current-dir-first-cluster)))
       '1)))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite make-clusters-correctness-1 . 1)))))

(defthm
  fati-of-hifat-to-lofat-helper-disjoint
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (integerp x)
        (>= x *ms-first-data-cluster*)
        (< x
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory)))
        (not (equal (fat32-entry-mask (fati x fat32-in-memory))
                    0))
        (equal (mv-nth 2
                       (hifat-to-lofat-helper
                        fat32-in-memory
                        fs current-dir-first-cluster))
               0))
   (equal (fati x
                (mv-nth 0
                        (hifat-to-lofat-helper
                         fat32-in-memory
                         fs current-dir-first-cluster)))
          (fati x fat32-in-memory)))
  :hints
  (("goal"
    :in-theory (e/d (lofat-fs-p-of-update-fati)
                    ((:rewrite make-clusters-correctness-1 . 1))))))

(defthm
  fat32-build-index-list-of-place-contents-coincident
  (implies
   (and
    (equal
     (mv-nth
      2
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))
     0)
    (not (zp (length contents)))
    (<= *ms-first-data-cluster* first-cluster)
    (stringp contents)
    (integerp length)
    (<= (length contents) length)
    (lofat-fs-p fat32-in-memory)
    (not
     (equal
      (fat32-entry-mask (fati first-cluster fat32-in-memory))
      0))
    (< first-cluster
       (+ 2 (count-of-clusters fat32-in-memory)))
    (fat32-masked-entry-p first-cluster)
    (equal cluster-size
           (cluster-size fat32-in-memory)))
   (equal
    (fat32-build-index-list
     (effective-fat
      (mv-nth
       0
       (place-contents fat32-in-memory dir-ent
                       contents file-length first-cluster)))
     first-cluster length cluster-size)
    (mv
     (cons
      first-cluster
      (find-n-free-clusters
       (effective-fat fat32-in-memory)
       (+
        -1
        (len (make-clusters contents
                            (cluster-size fat32-in-memory))))))
     0)))
  :hints
  (("goal"
    :in-theory
    (e/d
     (place-contents)
     ((:rewrite
       fat32-build-index-list-of-set-indices-in-fa-table)))
    :do-not-induct t
    :use
    ((:instance
      (:rewrite
       fat32-build-index-list-of-set-indices-in-fa-table)
      (cluster-size (cluster-size fat32-in-memory))
      (file-length length)
      (file-index-list
       (cons
        first-cluster
        (find-n-free-clusters
         (effective-fat fat32-in-memory)
         (+
          -1
          (len
           (make-clusters contents
                          (cluster-size fat32-in-memory)))))))
      (fa-table (effective-fat fat32-in-memory)))))))

(defthm place-contents-expansion-1
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (not (zp (cluster-size fat32-in-memory)))
        (dir-ent-p dir-ent)
        (fat32-masked-entry-p first-cluster)
        (< first-cluster
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory))))
   (equal
    (mv-nth 1
            (place-contents fat32-in-memory dir-ent
                            contents file-length first-cluster))
    (if
        (equal (length contents) 0)
        (dir-ent-set-first-cluster-file-size dir-ent 0 file-length)
      (if
          (equal
           (+
            1
            (len (stobj-find-n-free-clusters
                  fat32-in-memory
                  (+ -1
                     (len (make-clusters contents
                                         (cluster-size fat32-in-memory)))))))
           (len (make-clusters contents
                               (cluster-size fat32-in-memory))))
          (dir-ent-set-first-cluster-file-size dir-ent first-cluster file-length)
        dir-ent))))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm place-contents-expansion-2
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (not (zp (cluster-size fat32-in-memory)))
        (dir-ent-p dir-ent)
        (fat32-masked-entry-p first-cluster)
        (< first-cluster
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory))))
   (equal
    (mv-nth 2
            (place-contents fat32-in-memory dir-ent
                            contents file-length first-cluster))
    (if
        (equal (length contents) 0)
        0
      (if
          (equal
           (+
            1
            (len (stobj-find-n-free-clusters
                  fat32-in-memory
                  (+ -1
                     (len (make-clusters contents
                                         (cluster-size fat32-in-memory)))))))
           (len (make-clusters contents
                               (cluster-size fat32-in-memory))))
          0
        *enospc*))))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm place-contents-expansion-3
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (not (zp (cluster-size fat32-in-memory)))
        (dir-ent-p dir-ent)
        (fat32-masked-entry-p first-cluster)
        (< first-cluster
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory)))
        (equal (length contents) 0))
   (equal
    (mv-nth 0
            (place-contents fat32-in-memory dir-ent
                            contents file-length first-cluster))
    (update-fati first-cluster
                 (fat32-update-lower-28
                  (fati first-cluster fat32-in-memory)
                  0)
                 fat32-in-memory)))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  make-dir-ent-list-of-append-1
  (implies
   (dir-ent-p dir-ent)
   (equal (make-dir-ent-list (append dir-ent dir-contents))
          (if (equal (nth 0 dir-ent) 0)
              nil
              (if (useless-dir-ent-p dir-ent)
                  (make-dir-ent-list dir-contents)
                  (cons dir-ent
                        (make-dir-ent-list dir-contents))))))
  :hints (("goal" :in-theory (enable make-dir-ent-list
                                     len-when-dir-ent-p))))

(defthm
  make-dir-ent-list-of-append-2
  (implies
   (and (dir-ent-list-p dir-ent-list)
        (unsigned-byte-listp 8 y)
        (or (< (len y) *ms-dir-ent-length*)
            (equal (nth 0 y) 0)))
   (equal (make-dir-ent-list (append (flatten dir-ent-list) y))
          (make-dir-ent-list (flatten dir-ent-list))))
  :hints
  (("goal" :in-theory (enable make-dir-ent-list flatten dir-ent-p)
    :induct (flatten dir-ent-list))))

(defthm
  make-dir-ent-list-of-make-list-ac-1
  (implies (not (zp n))
           (equal (make-dir-ent-list (make-list-ac n 0 ac))
                  nil))
  :hints
  (("goal"
    :in-theory (e/d (make-dir-ent-list) (make-list-ac))
    :expand ((make-dir-ent-list (make-list-ac n 0 ac))
             (dir-ent-fix (take *ms-dir-ent-length*
                                (make-list-ac n 0 ac)))))))

(defthm
  make-dir-ent-list-of-flatten-when-useful-dir-ent-listp
  (implies (useful-dir-ent-list-p dir-ent-list)
           (equal (make-dir-ent-list (flatten dir-ent-list))
                  dir-ent-list))
  :hints
  (("goal"
    :in-theory
    (enable useful-dir-ent-list-p make-dir-ent-list flatten))))

(defthm
  useless-dir-ent-p-of-dir-ent-set-filename-of-constant
  (implies
   (dir-ent-p dir-ent)
   (and
    (useless-dir-ent-p
     (dir-ent-set-filename dir-ent *parent-dir-fat32-name*))
    (useless-dir-ent-p
     (dir-ent-set-filename dir-ent *current-dir-fat32-name*))))
  :hints
  (("goal"
    :in-theory (enable useless-dir-ent-p
                       dir-ent-filename dir-ent-set-filename
                       dir-ent-fix dir-ent-p))))

(defun
    unmodifiable-listp (x fa-table)
  (if
      (atom x)
      (equal x nil)
    (and (integerp (car x))
         (<= *ms-first-data-cluster* (car x))
         (< (car x) (len fa-table))
         (not (equal (fat32-entry-mask (nth (car x) fa-table))
                     0))
         (unmodifiable-listp (cdr x)
                             fa-table))))

(defthm
  unmodifiable-listp-of-update-nth
  (implies
   (and (not (member-equal key x))
        (< key (len fa-table)))
   (equal (unmodifiable-listp x (update-nth key val fa-table))
          (unmodifiable-listp x fa-table))))

(defthm
  unmodifiable-listp-correctness-2
  (implies (and (unmodifiable-listp x fa-table)
                (equal (fat32-entry-mask (nth key fa-table))
                       0))
           (not (member-equal key x)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (unmodifiable-listp x fa-table)
          (equal (fat32-entry-mask (nth key fa-table))
                 0)
          (< key (len fa-table)))
     (unmodifiable-listp x (update-nth key val fa-table))))))

(defthm
  unmodifiable-listp-correctness-3
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (unmodifiable-listp x (effective-fat fat32-in-memory))
    (not (member-equal first-cluster x))
    (integerp first-cluster)
    (<= *ms-first-data-cluster* first-cluster)
    (stringp contents)
    (equal
     (mv-nth
      2
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))
     0))
   (unmodifiable-listp
    x
    (effective-fat
     (mv-nth
      0
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))))))

(defthm
  unmodifiable-listp-correctness-4-lemma-1
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (natp n1)
    (<
     (nfix n2)
     (len (find-n-free-clusters (effective-fat fat32-in-memory)
                                n1))))
   (equal
    (fat32-entry-mask
     (fati
      (nth n2
           (find-n-free-clusters (effective-fat fat32-in-memory)
                                 n1))
      fat32-in-memory))
    0))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (disable find-n-free-clusters-correctness-5
             (:linear find-n-free-clusters-correctness-7))
    :use
    ((:instance find-n-free-clusters-correctness-5
                (fa-table (effective-fat fat32-in-memory)))
     (:instance (:linear find-n-free-clusters-correctness-7)
                (n n1)
                (fa-table (effective-fat fat32-in-memory))
                (m n2))))))

(defthm
  unmodifiable-listp-correctness-4
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (equal (mv-nth 2
                       (hifat-to-lofat-helper
                        fat32-in-memory
                        fs current-dir-first-cluster))
               0)
        (unmodifiable-listp x (effective-fat fat32-in-memory)))
   (unmodifiable-listp
    x
    (effective-fat
     (mv-nth 0
             (hifat-to-lofat-helper
              fat32-in-memory
              fs current-dir-first-cluster)))))
  :hints (("Goal" :in-theory (enable lofat-fs-p-of-update-fati)) ))

(defthm
  unmodifiable-listp-correctness-5
  (implies
   (and (unmodifiable-listp x fa-table)
        (natp n)
        (fat32-entry-list-p fa-table))
   (not (intersectp-equal x (find-n-free-clusters fa-table n))))
  :hints (("goal" :in-theory (enable intersectp-equal))))

(defthm
  unmodifiable-listp-of-append
  (equal (unmodifiable-listp (append x y) fa-table)
         (and
          (unmodifiable-listp (true-list-fix x) fa-table)
          (unmodifiable-listp y fa-table))))

(defthm
  unmodifiable-listp-of-fat32-build-index-list
  (implies
   (and
    (equal
     (mv-nth
      1
      (fat32-build-index-list fa-table masked-current-cluster
                              length cluster-size))
     0)
    (integerp masked-current-cluster)
    (<= 2 masked-current-cluster)
    (< masked-current-cluster (len fa-table)))
   (unmodifiable-listp
    (mv-nth
     0
     (fat32-build-index-list fa-table masked-current-cluster
                             length cluster-size))
    fa-table)))

(defthm
  lofat-to-hifat-helper-of-hifat-to-lofat-helper-disjoint-lemma-1
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (natp n)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper
                        fat32-in-memory
                        dir-ent-list entry-limit))
               0))
   (not-intersectp-list
    (find-n-free-clusters (effective-fat fat32-in-memory)
                          n)
    (mv-nth 2
            (lofat-to-hifat-helper
             fat32-in-memory
             dir-ent-list entry-limit))))
  :hints
  (("goal"
    :in-theory
    (e/d (intersectp-equal lofat-to-hifat-helper)
         ((:definition fat32-build-index-list)))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and
      (lofat-fs-p fat32-in-memory)
      (equal n 1)
      (equal
       (len
        (find-n-free-clusters (effective-fat fat32-in-memory)
                              n))
       1)
      (equal (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32-in-memory
                      dir-ent-list entry-limit))
             0))
     (not-intersectp-list
      (cons
       (nth
        0
        (find-n-free-clusters (effective-fat fat32-in-memory)
                              n))
       nil)
      (mv-nth 2
              (lofat-to-hifat-helper
               fat32-in-memory
               dir-ent-list entry-limit))))
    :hints
    (("goal"
      :do-not-induct t
      :expand
      ((len
        (find-n-free-clusters (effective-fat fat32-in-memory)
                              1))
       (len
        (cdr
         (find-n-free-clusters (effective-fat fat32-in-memory)
                               1))))
      :cases
      ((equal
        (list
         (car
          (find-n-free-clusters (effective-fat fat32-in-memory)
                                1)))
        (find-n-free-clusters (effective-fat fat32-in-memory)
                              1))))))))

(defthm
  lofat-to-hifat-helper-of-hifat-to-lofat-helper-disjoint
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper
                        fat32-in-memory
                        dir-ent-list entry-limit))
               0)
        (dir-ent-list-p dir-ent-list))
   (equal
    (lofat-to-hifat-helper
     (mv-nth 0
             (hifat-to-lofat-helper
              fat32-in-memory
              fs current-dir-first-cluster))
     dir-ent-list entry-limit)
    (lofat-to-hifat-helper fat32-in-memory
                                     dir-ent-list entry-limit)))
  :hints (("Goal" :in-theory (enable lofat-fs-p-of-update-fati)) ))

(defthm
  hifat-to-lofat-inversion-lemma-1
  (implies
   (and (equal (len (find-n-free-clusters fa-table 1))
               1)
        (not (intersectp-equal x (find-n-free-clusters fa-table 1)))
        (not (intersectp-equal x y)))
   (not (intersectp-equal x
                          (cons (nth 0 (find-n-free-clusters fa-table 1))
                                y))))
  :hints
  (("Goal" :in-theory (enable nth)
    :expand
    ((len (find-n-free-clusters fa-table 1))
     (len (cdr (find-n-free-clusters fa-table 1))))
    :cases
    ((equal (cons (nth 0 (find-n-free-clusters fa-table 1))
                  y)
            (append (find-n-free-clusters fa-table 1)
                    y))))))

;; At least once, accumulated-persistence has reported this rule as :useless,
;; but in fact it is needed to discharge a subgoal. There's no trivial way
;; around it.
(defthm
  hifat-to-lofat-inversion-lemma-2
  (implies (and (stringp (m1-file->contents file))
                (equal (len (explode (m1-file->contents file)))
                       0))
           (equal (m1-file->contents file) ""))
  :hints
  (("goal" :expand (len (explode (m1-file->contents file))))))

(defthm
  hifat-to-lofat-inversion-lemma-3
  (implies
   (not-intersectp-list
    (cons
     (nth
      0
      (find-n-free-clusters
       (effective-fat (mv-nth 0
                              (hifat-to-lofat-helper
                               fat32-in-memory (cdr fs)
                               current-dir-first-cluster)))
       1))
     x)
    (mv-nth
     2
     (lofat-to-hifat-helper
      (mv-nth
       0
       (hifat-to-lofat-helper
        (update-fati
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth 0
                    (hifat-to-lofat-helper
                     fat32-in-memory (cdr fs)
                     current-dir-first-cluster)))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper
                       fat32-in-memory (cdr fs)
                       current-dir-first-cluster)))
             1))
           (mv-nth 0
                   (hifat-to-lofat-helper
                    fat32-in-memory (cdr fs)
                    current-dir-first-cluster)))
          268435455)
         (mv-nth 0
                 (hifat-to-lofat-helper
                  fat32-in-memory (cdr fs)
                  current-dir-first-cluster)))
        (m1-file->contents (cdr (car fs)))
        (nth 0
             (find-n-free-clusters
              (effective-fat
               (mv-nth 0
                       (hifat-to-lofat-helper
                        fat32-in-memory (cdr fs)
                        current-dir-first-cluster)))
              1))))
      (mv-nth
       1
       (hifat-to-lofat-helper
        (update-fati
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth 0
                    (hifat-to-lofat-helper
                     fat32-in-memory (cdr fs)
                     current-dir-first-cluster)))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper
                       fat32-in-memory (cdr fs)
                       current-dir-first-cluster)))
             1))
           (mv-nth 0
                   (hifat-to-lofat-helper
                    fat32-in-memory (cdr fs)
                    current-dir-first-cluster)))
          268435455)
         (mv-nth 0
                 (hifat-to-lofat-helper
                  fat32-in-memory (cdr fs)
                  current-dir-first-cluster)))
        (m1-file->contents (cdr (car fs)))
        (nth 0
             (find-n-free-clusters
              (effective-fat
               (mv-nth 0
                       (hifat-to-lofat-helper
                        fat32-in-memory (cdr fs)
                        current-dir-first-cluster)))
              1))))
      (+ -1 entry-limit))))
   (and
   (not-intersectp-list
    (list
     (nth
      0
      (find-n-free-clusters
       (effective-fat (mv-nth 0
                              (hifat-to-lofat-helper
                               fat32-in-memory (cdr fs)
                               current-dir-first-cluster)))
       1)))
    (mv-nth
     2
     (lofat-to-hifat-helper
      (mv-nth
       0
       (hifat-to-lofat-helper
        (update-fati
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth 0
                    (hifat-to-lofat-helper
                     fat32-in-memory (cdr fs)
                     current-dir-first-cluster)))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper
                       fat32-in-memory (cdr fs)
                       current-dir-first-cluster)))
             1))
           (mv-nth 0
                   (hifat-to-lofat-helper
                    fat32-in-memory (cdr fs)
                    current-dir-first-cluster)))
          268435455)
         (mv-nth 0
                 (hifat-to-lofat-helper
                  fat32-in-memory (cdr fs)
                  current-dir-first-cluster)))
        (m1-file->contents (cdr (car fs)))
        (nth 0
             (find-n-free-clusters
              (effective-fat
               (mv-nth 0
                       (hifat-to-lofat-helper
                        fat32-in-memory (cdr fs)
                        current-dir-first-cluster)))
              1))))
      (mv-nth
       1
       (hifat-to-lofat-helper
        (update-fati
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth 0
                    (hifat-to-lofat-helper
                     fat32-in-memory (cdr fs)
                     current-dir-first-cluster)))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper
                       fat32-in-memory (cdr fs)
                       current-dir-first-cluster)))
             1))
           (mv-nth 0
                   (hifat-to-lofat-helper
                    fat32-in-memory (cdr fs)
                    current-dir-first-cluster)))
          268435455)
         (mv-nth 0
                 (hifat-to-lofat-helper
                  fat32-in-memory (cdr fs)
                  current-dir-first-cluster)))
        (m1-file->contents (cdr (car fs)))
        (nth 0
             (find-n-free-clusters
              (effective-fat
               (mv-nth 0
                       (hifat-to-lofat-helper
                        fat32-in-memory (cdr fs)
                        current-dir-first-cluster)))
              1))))
      (+ -1 entry-limit))))
   (not-intersectp-list
    x
    (mv-nth
     2
     (lofat-to-hifat-helper
      (mv-nth
       0
       (hifat-to-lofat-helper
        (update-fati
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth 0
                    (hifat-to-lofat-helper
                     fat32-in-memory (cdr fs)
                     current-dir-first-cluster)))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper
                       fat32-in-memory (cdr fs)
                       current-dir-first-cluster)))
             1))
           (mv-nth 0
                   (hifat-to-lofat-helper
                    fat32-in-memory (cdr fs)
                    current-dir-first-cluster)))
          268435455)
         (mv-nth 0
                 (hifat-to-lofat-helper
                  fat32-in-memory (cdr fs)
                  current-dir-first-cluster)))
        (m1-file->contents (cdr (car fs)))
        (nth 0
             (find-n-free-clusters
              (effective-fat
               (mv-nth 0
                       (hifat-to-lofat-helper
                        fat32-in-memory (cdr fs)
                        current-dir-first-cluster)))
              1))))
      (mv-nth
       1
       (hifat-to-lofat-helper
        (update-fati
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth 0
                    (hifat-to-lofat-helper
                     fat32-in-memory (cdr fs)
                     current-dir-first-cluster)))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper
                       fat32-in-memory (cdr fs)
                       current-dir-first-cluster)))
             1))
           (mv-nth 0
                   (hifat-to-lofat-helper
                    fat32-in-memory (cdr fs)
                    current-dir-first-cluster)))
          268435455)
         (mv-nth 0
                 (hifat-to-lofat-helper
                  fat32-in-memory (cdr fs)
                  current-dir-first-cluster)))
        (m1-file->contents (cdr (car fs)))
        (nth 0
             (find-n-free-clusters
              (effective-fat
               (mv-nth 0
                       (hifat-to-lofat-helper
                        fat32-in-memory (cdr fs)
                        current-dir-first-cluster)))
              1))))
      (+ -1 entry-limit))))))
  :hints
  (("goal"
    :in-theory
    (disable (:rewrite not-intersectp-list-of-append-2))
    :use
    (:instance
     (:rewrite not-intersectp-list-of-append-2)
     (l
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth
         0
         (hifat-to-lofat-helper
          (update-fati
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper
                       fat32-in-memory (cdr fs)
                       current-dir-first-cluster)))
             1))
           (fat32-update-lower-28
            (fati
             (nth
              0
              (find-n-free-clusters
               (effective-fat
                (mv-nth 0
                        (hifat-to-lofat-helper
                         fat32-in-memory (cdr fs)
                         current-dir-first-cluster)))
               1))
             (mv-nth 0
                     (hifat-to-lofat-helper
                      fat32-in-memory (cdr fs)
                      current-dir-first-cluster)))
            268435455)
           (mv-nth 0
                   (hifat-to-lofat-helper
                    fat32-in-memory (cdr fs)
                    current-dir-first-cluster)))
          (m1-file->contents (cdr (car fs)))
          (nth
           0
           (find-n-free-clusters
            (effective-fat
             (mv-nth 0
                     (hifat-to-lofat-helper
                      fat32-in-memory (cdr fs)
                      current-dir-first-cluster)))
            1))))
        (mv-nth
         1
         (hifat-to-lofat-helper
          (update-fati
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper
                       fat32-in-memory (cdr fs)
                       current-dir-first-cluster)))
             1))
           (fat32-update-lower-28
            (fati
             (nth
              0
              (find-n-free-clusters
               (effective-fat
                (mv-nth 0
                        (hifat-to-lofat-helper
                         fat32-in-memory (cdr fs)
                         current-dir-first-cluster)))
               1))
             (mv-nth 0
                     (hifat-to-lofat-helper
                      fat32-in-memory (cdr fs)
                      current-dir-first-cluster)))
            268435455)
           (mv-nth 0
                   (hifat-to-lofat-helper
                    fat32-in-memory (cdr fs)
                    current-dir-first-cluster)))
          (m1-file->contents (cdr (car fs)))
          (nth
           0
           (find-n-free-clusters
            (effective-fat
             (mv-nth 0
                     (hifat-to-lofat-helper
                      fat32-in-memory (cdr fs)
                      current-dir-first-cluster)))
            1))))
        (+ -1 entry-limit))))
     (y x)
     (x
      (list
       (nth 0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper
                       fat32-in-memory (cdr fs)
                       current-dir-first-cluster)))
             1))))))))

(encapsulate
  ()

  (local
   (defun-nx
     induction-scheme
     (fat32-in-memory fs
                      current-dir-first-cluster entry-limit x)
     (declare
      (xargs
       :stobjs fat32-in-memory
       :guard
       (and (lofat-fs-p fat32-in-memory)
            (m1-file-alist-p fs)
            (fat32-masked-entry-p current-dir-first-cluster))
       :hints (("goal" :in-theory (enable m1-file->contents
                                          m1-file-contents-fix)))
       :verify-guards nil))
     (b*
         (((unless (consp fs))
           (mv fat32-in-memory nil 0 nil))
          (head (car fs))
          ((mv fat32-in-memory
               tail-list errno tail-index-list)
           (induction-scheme
            fat32-in-memory (cdr fs)
            current-dir-first-cluster
            (-
             entry-limit
             (if
              (m1-regular-file-p (cdr head))
              1
              (+ 1
                 (m1-entry-count (m1-file->contents (cdr head))))))
            x))
          ((unless (zp errno))
           (mv fat32-in-memory
               tail-list errno tail-index-list))
          ((when (or (equal (car head)
                            *current-dir-fat32-name*)
                     (equal (car head)
                            *parent-dir-fat32-name*)))
           (mv fat32-in-memory
               tail-list errno tail-index-list))
          (dir-ent (m1-file->dir-ent (cdr head)))
          (indices (stobj-find-n-free-clusters fat32-in-memory 1))
          ((when (< (len indices) 1))
           (mv fat32-in-memory
               tail-list *enospc* tail-index-list))
          (first-cluster (nth 0 indices))
          ((unless (mbt (< first-cluster
                           (fat-length fat32-in-memory))))
           (mv fat32-in-memory
               tail-list *enospc* tail-index-list))
          (fat32-in-memory
           (update-fati first-cluster
                        (fat32-update-lower-28
                         (fati first-cluster fat32-in-memory)
                         *ms-end-of-clusterchain*)
                        fat32-in-memory)))
       (if
        (m1-regular-file-p (cdr head))
        (b*
            ((contents (m1-file->contents (cdr head)))
             (file-length (length contents))
             ((mv fat32-in-memory
                  dir-ent errno head-index-list)
              (place-contents fat32-in-memory dir-ent
                              contents file-length first-cluster))
             (dir-ent (dir-ent-set-filename dir-ent (car head)))
             (dir-ent (dir-ent-install-directory-bit dir-ent nil)))
          (mv fat32-in-memory
              (list* dir-ent tail-list)
              errno
              (append head-index-list tail-index-list)))
        (b*
            ((contents (m1-file->contents (cdr head)))
             (file-length 0)
             ((mv fat32-in-memory unflattened-contents
                  errno head-index-list1)
              (induction-scheme
               fat32-in-memory
               contents first-cluster (- entry-limit 1)
               (cons first-cluster x)))
             ((unless (zp errno))
              (mv fat32-in-memory
                  tail-list errno tail-index-list))
             (contents
              (nats=>string
               (append
                (dir-ent-install-directory-bit
                 (dir-ent-set-filename (dir-ent-set-first-cluster-file-size
                                        dir-ent first-cluster 0)
                                       *current-dir-fat32-name*)
                 t)
                (dir-ent-install-directory-bit
                 (dir-ent-set-filename
                  (dir-ent-set-first-cluster-file-size
                   dir-ent current-dir-first-cluster 0)
                  *parent-dir-fat32-name*)
                 t)
                (flatten unflattened-contents))))
             ((mv fat32-in-memory
                  dir-ent errno head-index-list2)
              (place-contents fat32-in-memory dir-ent
                              contents file-length first-cluster))
             (dir-ent (dir-ent-set-filename dir-ent (car head)))
             (dir-ent (dir-ent-install-directory-bit dir-ent t)))
          (mv fat32-in-memory
              (list* dir-ent tail-list)
              errno
              (append head-index-list1
                      head-index-list2 tail-index-list)))))))

  (local
   (defthm
     induction-scheme-correctness
     (equal
      (induction-scheme fat32-in-memory fs
                        current-dir-first-cluster entry-limit x)
      (hifat-to-lofat-helper
       fat32-in-memory
       fs current-dir-first-cluster))))

  ;; We tried (in commit aaf008a0e4edf4343b3d33e23d4aeff897cb1138) removing the
  ;; three place-contents-expansion rules in favour of rules which do not
  ;; introduce case splits. This is not easily doable, because the case split
  ;; based on the emptiness of the file contents is necessary for Subgoal *1/3
  ;; of this induction. Either we'd have to do the case split in a different
  ;; rule, or else we'd have to introduce a hint for Subgoal *1/3 - neither
  ;; seems very much better than the status quo. Therefore, this will remain
  ;; the slowest proof because the case splitting is necessary.
  (defthm
    hifat-to-lofat-inversion-big-induction
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (m1-file-alist-p fs)
          (m1-bounded-file-alist-p fs)
          (m1-file-no-dups-p fs)
          (fat32-masked-entry-p current-dir-first-cluster)
          (<= *ms-first-data-cluster*
              current-dir-first-cluster)
          (< current-dir-first-cluster
             (+ *ms-first-data-cluster*
                (count-of-clusters fat32-in-memory)))
          (integerp entry-limit)
          (>= entry-limit (m1-entry-count fs))
          (unmodifiable-listp x (effective-fat fat32-in-memory)))
     (b*
         (((mv fat32-in-memory dir-ent-list error-code)
           (hifat-to-lofat-helper
            fat32-in-memory
            fs current-dir-first-cluster)))
       (implies
        (zp error-code)
        (and (equal (mv-nth 3
                            (lofat-to-hifat-helper
                             fat32-in-memory
                             dir-ent-list entry-limit))
                    0)
             (not-intersectp-list
              x
              (mv-nth 2
                      (lofat-to-hifat-helper
                       fat32-in-memory
                       dir-ent-list entry-limit)))
             (hifat-equiv (mv-nth 0
                                   (lofat-to-hifat-helper
                                    fat32-in-memory
                                    dir-ent-list entry-limit))
                           fs)))))
    :hints
    (("goal"
      :induct
      (induction-scheme fat32-in-memory fs
                        current-dir-first-cluster entry-limit x)
      :in-theory
      (e/d
       (lofat-to-hifat-helper
        hifat-to-lofat-helper-correctness-4
        lofat-fs-p-of-update-fati
        m1-entry-count
        (:definition m1-file-no-dups-p))
       ((:rewrite make-clusters-correctness-1 . 1)
        (:rewrite nth-of-nats=>chars)
        (:rewrite dir-ent-p-when-member-equal-of-dir-ent-list-p)
        (:rewrite
         fati-of-hifat-to-lofat-helper-disjoint-lemma-2)
        (:definition induction-scheme)))
      :expand
      ((:free (y) (intersectp-equal nil y))
       (:free (x1 x2 y)
              (intersectp-equal (list x1)
                                (cons x2 y)))
       (:free (fat32-in-memory dir-ent dir-ent-list entry-limit)
              (lofat-to-hifat-helper
               fat32-in-memory
               (cons dir-ent dir-ent-list)
               entry-limit)))))
    :rule-classes
    ((:rewrite
      :corollary
      (implies
       (and (lofat-fs-p fat32-in-memory)
            (m1-file-alist-p fs)
            (m1-bounded-file-alist-p fs)
            (m1-file-no-dups-p fs)
            (fat32-masked-entry-p current-dir-first-cluster)
            (<= *ms-first-data-cluster*
                current-dir-first-cluster)
            (< current-dir-first-cluster
               (+ *ms-first-data-cluster*
                  (count-of-clusters fat32-in-memory)))
            (integerp entry-limit)
            (>= entry-limit (m1-entry-count fs))
            (unmodifiable-listp x (effective-fat fat32-in-memory)))
       (b*
           (((mv fat32-in-memory dir-ent-list error-code)
             (hifat-to-lofat-helper
              fat32-in-memory
              fs current-dir-first-cluster)))
         (implies
          (zp error-code)
          (not-intersectp-list
           x
           (mv-nth 2
                   (lofat-to-hifat-helper
                    fat32-in-memory
                    dir-ent-list entry-limit))))))))))

(defthm
  hifat-to-lofat-inversion-big-induction-corollaries
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (m1-file-alist-p fs)
        (m1-bounded-file-alist-p fs)
        (m1-file-no-dups-p fs)
        (fat32-masked-entry-p current-dir-first-cluster)
        (<= *ms-first-data-cluster*
            current-dir-first-cluster)
        (< current-dir-first-cluster
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory)))
        (integerp entry-limit)
        (>= entry-limit (m1-entry-count fs)))
   (b*
       (((mv fat32-in-memory dir-ent-list error-code)
         (hifat-to-lofat-helper
          fat32-in-memory
          fs current-dir-first-cluster)))
     (implies
      (zp error-code)
      (and (equal (mv-nth 3
                          (lofat-to-hifat-helper
                           fat32-in-memory
                           dir-ent-list entry-limit))
                  0)
           (hifat-equiv (mv-nth 0
                                 (lofat-to-hifat-helper
                                  fat32-in-memory
                                  dir-ent-list entry-limit))
                         fs)))))
  :hints
  (("goal"
    :in-theory (disable hifat-to-lofat-inversion-big-induction)
    :use
    (:instance hifat-to-lofat-inversion-big-induction
               (x nil)))))

(defthmd hifat-to-lofat-inversion-lemma-10
  (implies
   (atom dir-ent-list)
   (equal
    (lofat-to-hifat-helper fat32-in-memory
                                     dir-ent-list entry-limit)
    (mv nil 0 nil 0)))
  :hints (("goal" :in-theory (enable lofat-to-hifat-helper)) ))

(defthmd
  hifat-to-lofat-inversion-lemma-11
  (implies
   (lofat-fs-p fat32-in-memory)
   (and
    (< (fat32-entry-mask (bpb_rootclus fat32-in-memory))
       (binary-+ '2
                 (count-of-clusters fat32-in-memory)))
    (not
     (<
      (binary-+ '2
                (count-of-clusters fat32-in-memory))
      (binary-+
       '1
       (fat32-entry-mask (bpb_rootclus fat32-in-memory))))))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    hifat-to-lofat-inversion-lemma-12
    (implies (lofat-fs-p fat32-in-memory)
             (>= *ms-max-dir-size*
                 (cluster-size fat32-in-memory)))
    :rule-classes :linear
    :hints
    (("goal" :in-theory
      (disable lofat-fs-p-correctness-1)
      :use lofat-fs-p-correctness-1)))

  (defthmd
    hifat-to-lofat-inversion-lemma-13
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (stringp text)
          (equal (length text)
                 (cluster-size fat32-in-memory)))
     (equal
      (len (make-clusters text (cluster-size fat32-in-memory)))
      1))
    :hints
    (("goal"
      :in-theory
      (disable lofat-fs-p-correctness-1)
      :use
      (lofat-fs-p-correctness-1
       (:instance
        len-of-make-clusters
        (cluster-size (cluster-size fat32-in-memory))))))))

(defthm
  hifat-to-lofat-inversion
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (m1-file-alist-p fs)
        (m1-bounded-file-alist-p fs)
        (m1-file-no-dups-p fs)
        (<=
         (m1-entry-count fs)
         (max-entry-count fat32-in-memory)))
   (b*
       (((mv fat32-in-memory error-code)
         (hifat-to-lofat
          fat32-in-memory fs)))
     (implies
      (zp error-code)
      (and
       (equal
        (mv-nth 1
                (lofat-to-hifat
                 fat32-in-memory))
        0)
       (hifat-equiv
        (mv-nth 0
                (lofat-to-hifat
                 fat32-in-memory))
        fs)))))
  :hints
  (("goal" :do-not-induct t
    :in-theory (enable lofat-to-hifat
                       hifat-to-lofat
                       hifat-to-lofat-helper-correctness-4
                       hifat-to-lofat-inversion-lemma-10
                       hifat-to-lofat-inversion-lemma-11
                       hifat-to-lofat-inversion-lemma-13
                       painful-debugging-lemma-10
                       painful-debugging-lemma-11
                       lofat-fs-p-of-update-fati))))

(defund-nx
  lofat-equiv
  (fat32-in-memory1 fat32-in-memory2)
  (b* (((mv fs1 error-code1)
        (lofat-to-hifat fat32-in-memory1))
       (good1 (and (lofat-fs-p fat32-in-memory1)
                   (equal error-code1 0)))
       ((mv fs2 error-code2)
        (lofat-to-hifat fat32-in-memory2))
       (good2 (and (lofat-fs-p fat32-in-memory2)
                   (equal error-code2 0)))
       ((unless (and good1 good2))
        (and (not good1) (not good2))))
    (hifat-equiv fs1 fs2)))

(defequiv
  lofat-equiv
  :hints (("goal" :in-theory (enable lofat-equiv))))

(defthm
  lofat-to-hifat-inversion
  (implies
   (lofat-fs-p fat32-in-memory)
   (b*
       (((mv fs error-code)
         (lofat-to-hifat fat32-in-memory))
        )
     (implies
      (and
       (equal error-code 0)
       (m1-bounded-file-alist-p fs)
       (m1-file-no-dups-p fs)
       ;; This clause should always be true, but that's not yet proven. The
       ;; argument is: The only time we get an error out of
       ;; hifat-to-lofat-helper (and the wrapper) is when we run out
       ;; of space. We shouldn't be able to run out of space when we just
       ;; extracted an m1 instance from fat32-in-memory, and we didn't change
       ;; the size of fat32-in-memory at all. However, that's going to involve
       ;; reasoning about the number of clusters taken up by an m1 instance,
       ;; which is not really where it's at right now.
       (equal
        (mv-nth
         1
         (hifat-to-lofat
          fat32-in-memory
          fs))
        0))
      (lofat-equiv
       (mv-nth
        0
        (hifat-to-lofat
         fat32-in-memory
         fs))
       fat32-in-memory))))
  :hints (("Goal" :in-theory (enable lofat-equiv)) ))

(defthm
  lofat-to-string-inversion-lemma-1
  (implies
   (and (< (nfix n)
           (* (bpb_rsvdseccnt fat32-in-memory)
              (bpb_bytspersec fat32-in-memory)))
        (lofat-fs-p fat32-in-memory))
   (equal
    (nth
     n
     (append
      (explode (reserved-area-string fat32-in-memory))
      (explode (make-fat-string-ac (bpb_numfats fat32-in-memory)
                                   fat32-in-memory ""))
      (data-region-string-helper
       fat32-in-memory
       (count-of-clusters fat32-in-memory)
       nil)))
    (nth n
         (explode (reserved-area-string fat32-in-memory))))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    lofat-to-string-inversion-lemma-2
    (implies (fat32-in-memoryp fat32-in-memory)
             (>= (+ (data-region-length fat32-in-memory)
                    (* (bpb_bytspersec fat32-in-memory)
                       (bpb_rsvdseccnt fat32-in-memory))
                    (* (bpb_numfats fat32-in-memory)
                       4 (fat-length fat32-in-memory)))
                 (* (bpb_bytspersec fat32-in-memory)
                    (bpb_rsvdseccnt fat32-in-memory))))
    :hints
    (("goal" :in-theory (enable bpb_numfats fat32-in-memoryp)))
    :rule-classes :linear)

  (defthm
    lofat-to-string-inversion-lemma-3
    (implies (equal (* (bpb_fatsz32 fat32-in-memory)
                       1/4 (bpb_bytspersec fat32-in-memory))
                    (fat-length fat32-in-memory))
             (equal (* (bpb_bytspersec fat32-in-memory)
                       (bpb_fatsz32 fat32-in-memory)
                       (bpb_numfats fat32-in-memory))
                    (* (bpb_numfats fat32-in-memory)
                       4 (fat-length fat32-in-memory))))))

(encapsulate
  ()

  (local
   (in-theory (e/d (lofat-to-string get-initial-bytes get-remaining-rsvdbyts)
                   (;; the splitter-note suggests these could usefully be
                    ;; disabled
                    nth-of-append nthcdr-of-append take-of-append))))

  (defthm
    lofat-to-string-inversion-lemma-4
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth 11
            (get-initial-bytes
             (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_bytspersec fat32-in-memory)))
      (equal
       (nth 12
            (get-initial-bytes
             (lofat-to-string fat32-in-memory)))
       (logtail 8 (bpb_bytspersec fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-5
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (nth 13
           (get-initial-bytes
            (lofat-to-string fat32-in-memory)))
      (bpb_secperclus fat32-in-memory))))

  (defthm
    lofat-to-string-inversion-lemma-6
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth 14
            (get-initial-bytes
             (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_rsvdseccnt fat32-in-memory)))
      (equal
       (nth 15
            (get-initial-bytes
             (lofat-to-string fat32-in-memory)))
       (logtail 8 (bpb_rsvdseccnt fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-7
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (nth 0
           (get-remaining-rsvdbyts
            (lofat-to-string fat32-in-memory)))
      (bpb_numfats fat32-in-memory)))
    :hints
    (("goal" :in-theory (e/d (string=>nats) (nth)))))

  (defthm
    lofat-to-string-inversion-lemma-8
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth
        1
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_rootentcnt fat32-in-memory)))
      (equal
       (nth
        2
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (logtail 8 (bpb_rootentcnt fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-9
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth
        3
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_totsec16 fat32-in-memory)))
      (equal
       (nth
        4
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (logtail 8 (bpb_totsec16 fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-10
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (nth
       5
       (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
      (bpb_media fat32-in-memory))))

  (defthm
    lofat-to-string-inversion-lemma-11
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth
        6
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_fatsz16 fat32-in-memory)))
      (equal
       (nth
        7
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (logtail 8 (bpb_fatsz16 fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-12
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth
        8
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_secpertrk fat32-in-memory)))
      (equal
       (nth
        9
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (logtail 8 (bpb_secpertrk fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-13
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth
        10
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_numheads fat32-in-memory)))
      (equal
       (nth
        11
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (logtail 8 (bpb_numheads fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-14
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth
        12
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_hiddsec fat32-in-memory)))
      (equal
       (nth
        13
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (logtail  8 (bpb_hiddsec fat32-in-memory))))
      (equal
       (nth
        14
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (logtail 16 (bpb_hiddsec fat32-in-memory))))
      (equal
       (nth
        15
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (logtail 24 (bpb_hiddsec fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-15
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth
        16
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_totsec32 fat32-in-memory)))
      (equal
       (nth
        17
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (logtail  8 (bpb_totsec32 fat32-in-memory))))
      (equal
       (nth
        18
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (logtail 16 (bpb_totsec32 fat32-in-memory))))
      (equal
       (nth
        19
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (logtail 24 (bpb_totsec32 fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-16
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth
        20
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_fatsz32 fat32-in-memory)))
      (equal
       (nth
        21
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (logtail 8 (bpb_fatsz32 fat32-in-memory))))
      (equal
       (nth
        22
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (logtail 16 (bpb_fatsz32 fat32-in-memory))))
      (equal
       (nth
        23
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (logtail 24 (bpb_fatsz32 fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-17
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth
        24
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_extflags fat32-in-memory)))
      (equal
       (nth
        25
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (logtail 8 (bpb_extflags fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-18
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (nth
       26
       (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
      (bpb_fsver_minor fat32-in-memory))))

  (defthm
    lofat-to-string-inversion-lemma-19
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (nth
       27
       (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
      (bpb_fsver_major fat32-in-memory))))

  (defthm
    lofat-to-string-inversion-lemma-20
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth
        28
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_rootclus fat32-in-memory)))
      (equal
       (nth
        29
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (logtail  8 (bpb_rootclus fat32-in-memory))))
      (equal
       (nth
        30
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (logtail 16 (bpb_rootclus fat32-in-memory))))
      (equal
       (nth
        31
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (logtail 24 (bpb_rootclus fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-21
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth
        32
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_fsinfo fat32-in-memory)))
      (equal
       (nth
        33
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (logtail 8 (bpb_fsinfo fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-22
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth
        34
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (bpb_bkbootsec fat32-in-memory)))
      (equal
       (nth
        35
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (logtail 8 (bpb_bkbootsec fat32-in-memory))))))

  (defthm
    lofat-to-string-inversion-lemma-23
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (nth
       48
       (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
      (bs_drvnum fat32-in-memory))))

  (defthm
    lofat-to-string-inversion-lemma-24
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (nth
       49
       (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
      (bs_reserved1 fat32-in-memory))))

  (defthm
    lofat-to-string-inversion-lemma-25
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (nth
       50
       (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
      (bs_bootsig fat32-in-memory))))

  (defthm
    lofat-to-string-inversion-lemma-26
    (implies
     (lofat-fs-p fat32-in-memory)
     (and
      (equal
       (nth
        51
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (bs_volid fat32-in-memory)))
      (equal
       (nth
        52
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (logtail  8 (bs_volid fat32-in-memory))))
      (equal
       (nth
        53
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (loghead 8 (logtail 16 (bs_volid fat32-in-memory))))
      (equal
       (nth
        54
        (get-remaining-rsvdbyts (lofat-to-string fat32-in-memory)))
       (logtail 24 (bs_volid fat32-in-memory)))))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    lofat-to-string-inversion-lemma-27
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (natp index)
          (< index
             (data-region-length fat32-in-memory)))
     (equal
      (take
       (cluster-size fat32-in-memory)
       (nthcdr
        (* (cluster-size fat32-in-memory) index)
        (data-region-string-helper fat32-in-memory len ac)))
      (if (< index (nfix len))
          (coerce (data-regioni index fat32-in-memory)
                  'list)
        (take (cluster-size fat32-in-memory)
              (nthcdr (* (cluster-size fat32-in-memory)
                         (- index (nfix len)))
                      (make-character-list ac))))))
    :hints (("Goal" :in-theory (enable by-slice-you-mean-the-whole-cake-2))))

  (defthm
    lofat-to-string-inversion-lemma-30
    (implies (and (fat32-in-memoryp fat32-in-memory)
                  (<= 512 (bpb_bytspersec fat32-in-memory))
                  (<= 1 (bpb_secperclus fat32-in-memory))
                  (> (+ (- (bpb_rsvdseccnt fat32-in-memory))
                        (bpb_totsec32 fat32-in-memory)
                        (- (* (bpb_fatsz32 fat32-in-memory)
                              (bpb_numfats fat32-in-memory))))
                     (bpb_secperclus fat32-in-memory)))
             (> (* (bpb_bytspersec fat32-in-memory)
                   (bpb_secperclus fat32-in-memory)
                   (floor (+ (- (bpb_rsvdseccnt fat32-in-memory))
                             (bpb_totsec32 fat32-in-memory)
                             (- (* (bpb_fatsz32 fat32-in-memory)
                                   (bpb_numfats fat32-in-memory))))
                          (bpb_secperclus fat32-in-memory)))
                0))
    :rule-classes :linear
    :instructions
    (:promote (:rewrite product-greater-than-zero-2)
              (:change-goal nil t)
              :bash :s-prop
              (:rewrite product-greater-than-zero-2)
              (:change-goal nil t)
              :bash :s-prop
              (:use (:instance lofat-to-string-inversion-lemma-29
                               (i (+ (- (bpb_rsvdseccnt fat32-in-memory))
                                     (bpb_totsec32 fat32-in-memory)
                                     (- (* (bpb_fatsz32 fat32-in-memory)
                                           (bpb_numfats fat32-in-memory)))))
                               (j (bpb_secperclus fat32-in-memory))))
              :promote (:demote 1)
              (:dive 1 1)
              (:= t)
              :top :bash))

  (defthm lofat-to-string-inversion-lemma-31
    (implies (lofat-fs-p fat32-in-memory)
             (<=
              (* 4 (fat-length fat32-in-memory))
              (* (bpb_numfats fat32-in-memory)
                 4 (fat-length fat32-in-memory))))
    :rule-classes :linear)

  (defthm lofat-to-string-inversion-lemma-32
    (implies (and (not (zp len))
                  (< (* (cluster-size fat32-in-memory)
                        (count-of-clusters fat32-in-memory))
                     (+ (cluster-size fat32-in-memory)
                        (* (cluster-size fat32-in-memory)
                           (count-of-clusters fat32-in-memory))
                        (* (cluster-size fat32-in-memory)
                           (- len))))
                  (lofat-fs-p fat32-in-memory))
             (< (count-of-clusters fat32-in-memory)
                len))
    :rule-classes :linear))

(defthm
  lofat-to-string-inversion-lemma-28
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (natp len)
        (<= len
            (data-region-length fat32-in-memory)))
   (equal (update-data-region
           fat32-in-memory
           (implode (data-region-string-helper
                     fat32-in-memory
                     (count-of-clusters fat32-in-memory)
                     nil))
           len)
          (mv
           fat32-in-memory
           0)))
  :hints
  (("goal" :in-theory (disable data-region-string-helper)
    :induct
    (update-data-region
     fat32-in-memory
     (implode (data-region-string-helper fat32-in-memory
                                         (count-of-clusters fat32-in-memory)
                                         nil))
     len))
   ("subgoal *1/2"
    :in-theory
    (disable lofat-to-string-inversion-lemma-27)
    :use
    (:instance lofat-to-string-inversion-lemma-27
               (index (- (count-of-clusters fat32-in-memory)
                         len))
               (len (count-of-clusters fat32-in-memory))
               (ac nil)))))

(defthm
  lofat-to-string-inversion-lemma-35
  (implies
   (and (natp n2)
        (< n2 (* 4 (fat-length fat32-in-memory)))
        (not (zp n1)))
   (equal
    (nth n2
         (explode (make-fat-string-ac n1 fat32-in-memory ac)))
    (nth n2
         (explode (stobj-fa-table-to-string
                   fat32-in-memory)))))
  :hints (("Goal" :in-theory (enable make-fat-string-ac))))

(defthm
  lofat-to-string-inversion-lemma-36
  (implies
   (and (fat32-entry-p current)
        (< (nfix n) 4))
   (unsigned-byte-p 8
                    (nth n
                         (list (loghead 8 current)
                               (loghead 8 (logtail 8 current))
                               (loghead 8 (logtail 16 current))
                               (logtail 24 current)))))
  :hints
  (("goal" :in-theory (e/d (fat32-entry-p)
                           (unsigned-byte-p))))
  :rule-classes
  ((:linear
    :corollary
    (implies
     (and (fat32-entry-p current)
          (< (nfix n) 4))
     (and (<= 0
              (nth n
                   (list (loghead 8 current)
                         (loghead 8 (logtail 8 current))
                         (loghead 8 (logtail 16 current))
                         (logtail 24 current))))
          (< (nth n
                  (list (loghead 8 current)
                        (loghead 8 (logtail 8 current))
                        (loghead 8 (logtail 16 current))
                        (logtail 24 current)))
             256))))
   (:rewrite
    :corollary
    (implies
     (and (fat32-entry-p current)
          (< (nfix n) 4))
     (integerp (nth n
                    (list (loghead 8 current)
                          (loghead 8 (logtail 8 current))
                          (loghead 8 (logtail 16 current))
                          (logtail 24 current))))))))

(defthm
  lofat-to-string-inversion-lemma-37
  (implies (and (integerp pos)
                (integerp length)
                (<= pos length))
           (and (iff (< (+ -1 (* 4 pos)) (+ -4 (* 4 length)))
                     (not (equal pos length)))
                (iff (< (+ -2 (* 4 pos)) (+ -4 (* 4 length)))
                     (not (equal pos length)))
                (iff (< (+ -3 (* 4 pos)) (+ -4 (* 4 length)))
                     (not (equal pos length)))
                (iff (< (+ -4 (* 4 pos)) (+ -4 (* 4 length)))
                     (not (equal pos length))))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    lofat-to-string-inversion-lemma-38
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (not (zp pos))
          (natp length))
     (and
      (equal (nth (+ -1 (* 4 pos))
                  (stobj-fa-table-to-string-helper fat32-in-memory
                                                   length
                                                   ac))
             (if (zp (- pos length))
                 (code-char (logtail 24 (fati (+ -1 pos) fat32-in-memory)))
               (nth (+ -1 (* 4 (- pos length))) ac)))
      (equal (nth (+ -2 (* 4 pos))
                  (stobj-fa-table-to-string-helper fat32-in-memory
                                                   length
                                                   ac))
             (if (zp (- pos length))
                 (code-char (loghead 8
                                     (logtail 16
                                              (fati (+ -1 pos) fat32-in-memory))))
               (nth (+ -2 (* 4 (- pos length))) ac)))
      (equal (nth (+ -3 (* 4 pos))
                  (stobj-fa-table-to-string-helper fat32-in-memory
                                                   length
                                                   ac))
             (if (zp (- pos length))
                 (code-char (loghead 8
                                     (logtail 8 (fati (+ -1 pos) fat32-in-memory))))
               (nth (+ -3 (* 4 (- pos length))) ac)))
      (equal (nth (+ -4 (* 4 pos))
                  (stobj-fa-table-to-string-helper fat32-in-memory
                                                   length
                                                   ac))
             (if (zp (- pos length))
                 (code-char (loghead 8 (fati (+ -1 pos) fat32-in-memory)))
               (nth (+ -4 (* 4 (- pos length))) ac)))))
    :hints (("goal"
             :induct
             (stobj-fa-table-to-string-helper fat32-in-memory
                                              length
                                              ac)
              :expand (:free (n x y) (nth n (cons x y)))))))

(defthm
  lofat-to-string-inversion-lemma-39
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (not (zp pos))
        (<= pos (fat-length fat32-in-memory)))
   (and
    (equal
     (nth
      (+ -1 (* 4 pos))
      (explode
       (stobj-fa-table-to-string fat32-in-memory)))
     (code-char (logtail 24 (fati (- pos 1) fat32-in-memory))))
    (equal
     (nth
      (+ -2 (* 4 pos))
      (explode
       (stobj-fa-table-to-string fat32-in-memory)))
     (code-char
      (loghead 8
               (logtail 16 (fati (- pos 1) fat32-in-memory)))))
    (equal
     (nth
      (+ -3 (* 4 pos))
      (explode
       (stobj-fa-table-to-string fat32-in-memory)))
     (code-char
      (loghead 8
               (logtail 8 (fati (- pos 1) fat32-in-memory)))))
    (equal
     (nth
      (+ -4 (* 4 pos))
      (explode
       (stobj-fa-table-to-string fat32-in-memory)))
     (code-char (loghead 8 (fati (- pos 1) fat32-in-memory))))))
  :hints (("goal" :in-theory (enable stobj-fa-table-to-string))))

(defthm
  lofat-to-string-inversion-lemma-41
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (not (zp pos))
        (<= pos (fat-length fat32-in-memory)))
   (equal (update-fat
           fat32-in-memory
           (make-fat-string-ac (bpb_numfats fat32-in-memory)
                               fat32-in-memory "")
           pos)
          fat32-in-memory))
  :hints
  (("goal"
    :induct
    (update-fat
     fat32-in-memory
     (make-fat-string-ac (bpb_numfats fat32-in-memory)
                         fat32-in-memory "")
     pos))
   ("subgoal *1/3"
    :in-theory
    (disable lofat-to-string-inversion-lemma-39)
    :use (:instance lofat-to-string-inversion-lemma-39
                    (pos 1)))))

(defthm
  lofat-to-string-inversion-lemma-50
  (implies (lofat-fs-p fat32-in-memory)
           (> (* (bpb_numfats fat32-in-memory)
                 4 (fat-entry-count fat32-in-memory))
              0))
  :hints
  (("goal" :in-theory
    (disable lofat-fs-p-correctness-1)
    :use lofat-fs-p-correctness-1))
  :rule-classes :linear)

(encapsulate
  ()

  (local (in-theory (disable bs_jmpbooti update-bs_jmpbooti
                             bs_oemnamei bpb_reservedi bs_vollabi
                             bs_filsystypei)))

  (defthm
    lofat-to-string-inversion-lemma-42
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (chars=>nats (explode (reserved-area-string fat32-in-memory)))
      (append
       ;; initial bytes
       (list (bs_jmpbooti 0 fat32-in-memory)
             (bs_jmpbooti 1 fat32-in-memory)
             (bs_jmpbooti 2 fat32-in-memory))
       (list (bs_oemnamei 0 fat32-in-memory)
             (bs_oemnamei 1 fat32-in-memory)
             (bs_oemnamei 2 fat32-in-memory)
             (bs_oemnamei 3 fat32-in-memory)
             (bs_oemnamei 4 fat32-in-memory)
             (bs_oemnamei 5 fat32-in-memory)
             (bs_oemnamei 6 fat32-in-memory)
             (bs_oemnamei 7 fat32-in-memory))
       (list (loghead 8 (bpb_bytspersec fat32-in-memory))
             (logtail 8 (bpb_bytspersec fat32-in-memory))
             (bpb_secperclus fat32-in-memory)
             (loghead 8 (bpb_rsvdseccnt fat32-in-memory))
             (logtail 8 (bpb_rsvdseccnt fat32-in-memory)))
       ;; remaining reserved bytes
       (list (bpb_numfats fat32-in-memory)
             (loghead 8 (bpb_rootentcnt fat32-in-memory))
             (logtail 8 (bpb_rootentcnt fat32-in-memory))
             (loghead 8 (bpb_totsec16 fat32-in-memory))
             (logtail 8 (bpb_totsec16 fat32-in-memory))
             (bpb_media fat32-in-memory)
             (loghead 8 (bpb_fatsz16 fat32-in-memory))
             (logtail 8 (bpb_fatsz16 fat32-in-memory))
             (loghead 8 (bpb_secpertrk fat32-in-memory))
             (logtail 8 (bpb_secpertrk fat32-in-memory))
             (loghead 8 (bpb_numheads fat32-in-memory))
             (logtail 8 (bpb_numheads fat32-in-memory))
             (loghead 8             (bpb_hiddsec fat32-in-memory) )
             (loghead 8 (logtail  8 (bpb_hiddsec fat32-in-memory)))
             (loghead 8 (logtail 16 (bpb_hiddsec fat32-in-memory)))
             (logtail 24 (bpb_hiddsec fat32-in-memory) )
             (loghead 8             (bpb_totsec32 fat32-in-memory) )
             (loghead 8 (logtail  8 (bpb_totsec32 fat32-in-memory)))
             (loghead 8 (logtail 16 (bpb_totsec32 fat32-in-memory)))
             (logtail 24 (bpb_totsec32 fat32-in-memory) )
             (loghead 8             (bpb_fatsz32 fat32-in-memory) )
             (loghead 8 (logtail  8 (bpb_fatsz32 fat32-in-memory)))
             (loghead 8 (logtail 16 (bpb_fatsz32 fat32-in-memory)))
             (logtail 24 (bpb_fatsz32 fat32-in-memory) )
             (loghead 8 (bpb_extflags fat32-in-memory))
             (logtail 8 (bpb_extflags fat32-in-memory))
             (bpb_fsver_minor fat32-in-memory)
             (bpb_fsver_major fat32-in-memory)
             (loghead 8             (bpb_rootclus fat32-in-memory) )
             (loghead 8 (logtail  8 (bpb_rootclus fat32-in-memory)))
             (loghead 8 (logtail 16 (bpb_rootclus fat32-in-memory)))
             (logtail 24 (bpb_rootclus fat32-in-memory) )
             (loghead 8 (bpb_fsinfo fat32-in-memory))
             (logtail 8 (bpb_fsinfo fat32-in-memory))
             (loghead 8 (bpb_bkbootsec fat32-in-memory))
             (logtail 8 (bpb_bkbootsec fat32-in-memory)))
       (list (bpb_reservedi  0 fat32-in-memory)
             (bpb_reservedi  1 fat32-in-memory)
             (bpb_reservedi  2 fat32-in-memory)
             (bpb_reservedi  3 fat32-in-memory)
             (bpb_reservedi  4 fat32-in-memory)
             (bpb_reservedi  5 fat32-in-memory)
             (bpb_reservedi  6 fat32-in-memory)
             (bpb_reservedi  7 fat32-in-memory)
             (bpb_reservedi  8 fat32-in-memory)
             (bpb_reservedi  9 fat32-in-memory)
             (bpb_reservedi 10 fat32-in-memory)
             (bpb_reservedi 11 fat32-in-memory))
       (list (bs_drvnum fat32-in-memory)
             (bs_reserved1 fat32-in-memory)
             (bs_bootsig fat32-in-memory)
             (loghead 8             (bs_volid fat32-in-memory) )
             (loghead 8 (logtail  8 (bs_volid fat32-in-memory)))
             (loghead 8 (logtail 16 (bs_volid fat32-in-memory)))
             (logtail 24 (bs_volid fat32-in-memory) ))
       (list (bs_vollabi  0 fat32-in-memory)
             (bs_vollabi  1 fat32-in-memory)
             (bs_vollabi  2 fat32-in-memory)
             (bs_vollabi  3 fat32-in-memory)
             (bs_vollabi  4 fat32-in-memory)
             (bs_vollabi  5 fat32-in-memory)
             (bs_vollabi  6 fat32-in-memory)
             (bs_vollabi  7 fat32-in-memory)
             (bs_vollabi  8 fat32-in-memory)
             (bs_vollabi  9 fat32-in-memory)
             (bs_vollabi 10 fat32-in-memory))
       (list (bs_filsystypei 0 fat32-in-memory)
             (bs_filsystypei 1 fat32-in-memory)
             (bs_filsystypei 2 fat32-in-memory)
             (bs_filsystypei 3 fat32-in-memory)
             (bs_filsystypei 4 fat32-in-memory)
             (bs_filsystypei 5 fat32-in-memory)
             (bs_filsystypei 6 fat32-in-memory)
             (bs_filsystypei 7 fat32-in-memory))
       (make-list
        (- (* (bpb_rsvdseccnt fat32-in-memory) (bpb_bytspersec fat32-in-memory)) 90)
        :initial-element 0))))
    :hints (("Goal" :in-theory (e/d (chars=>nats reserved-area-string
                                                 reserved-area-chars)
                                    (unsigned-byte-p)))))

  (local (in-theory (enable chars=>nats-of-take get-initial-bytes
                            lofat-to-string)))

  (defthm
    lofat-to-string-inversion-lemma-43
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (update-bs_jmpboot
       (take 3
             (get-initial-bytes
              (lofat-to-string fat32-in-memory)))
       fat32-in-memory)
      fat32-in-memory)))

  (defthm
    lofat-to-string-inversion-lemma-44
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (update-bs_oemname
       (take
        8
        (nthcdr
         3
         (get-initial-bytes
          (lofat-to-string fat32-in-memory))))
       fat32-in-memory)
      fat32-in-memory)))

  (local (in-theory (enable chars=>nats-of-nthcdr get-remaining-rsvdbyts)))

  (defthm
    lofat-to-string-inversion-lemma-45
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (update-bs_vollab
       (take
        11
        (nthcdr
         55
         (get-remaining-rsvdbyts
          (lofat-to-string fat32-in-memory))))
       fat32-in-memory)
      fat32-in-memory)))

  (defthm
    lofat-to-string-inversion-lemma-46
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (update-bs_filsystype
       (take
        8
        (nthcdr
         66
         (get-remaining-rsvdbyts
          (lofat-to-string fat32-in-memory))))
       fat32-in-memory)
      fat32-in-memory)))

  ;; Kinda wish we could have made use of update_bpb_reserved-alt for this
  ;; theorem, and then done the same kind of thing elsewhere.
  (defthm
    lofat-to-string-inversion-lemma-40
    (implies
     (lofat-fs-p fat32-in-memory)
     (equal
      (update-bpb_reserved
       (take 12
             (nthcdr 36
                     (get-remaining-rsvdbyts
                      (lofat-to-string fat32-in-memory))))
       fat32-in-memory)
      fat32-in-memory))))

(defthm
  lofat-to-string-inversion-lemma-47
  (implies
   (and (natp n2)
        (zp (+ n2
               (- (* 4 (fat-length fat32-in-memory)))))
        (not (zp n1)))
   (equal
    (take n2
          (explode (make-fat-string-ac n1 fat32-in-memory ac)))
    (take n2
          (explode (stobj-fa-table-to-string
                    fat32-in-memory)))))
  :hints
  (("goal" :in-theory (enable make-fat-string-ac
                              by-slice-you-mean-the-whole-cake-2))))

(defthm
  lofat-to-string-inversion-lemma-48
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (not (zp pos))
        (<= pos (fat-length fat32-in-memory)))
   (equal (update-fat
           fat32-in-memory
           (stobj-fa-table-to-string fat32-in-memory)
           pos)
          fat32-in-memory))
  :hints
  (("goal"
    :induct
    (update-fat
     fat32-in-memory
     (stobj-fa-table-to-string fat32-in-memory)
     pos))))

(defthm
  lofat-to-string-inversion-lemma-49
  (equal
   (nthcdr
    n
    (explode (lofat-to-string fat32-in-memory)))
   (if
    (<= (nfix n)
        (len (explode (reserved-area-string fat32-in-memory))))
    (append
     (nthcdr n
             (explode (reserved-area-string fat32-in-memory)))
     (explode (make-fat-string-ac (bpb_numfats fat32-in-memory)
                                  fat32-in-memory ""))
     (data-region-string-helper
      fat32-in-memory
      (data-region-length fat32-in-memory)
      nil))
    (nthcdr
     (- n
        (len (explode (reserved-area-string fat32-in-memory))))
     (append
      (explode (make-fat-string-ac (bpb_numfats fat32-in-memory)
                                   fat32-in-memory ""))
      (data-region-string-helper
       fat32-in-memory
       (data-region-length fat32-in-memory)
       nil)))))
  :hints
  (("goal" :in-theory
    (e/d (lofat-to-string)
         (fat32-in-memoryp
          length-of-reserved-area-string
          nth-of-explode-of-reserved-area-string)))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthmd
    lofat-to-string-inversion-lemma-51
    (implies (lofat-fs-p fat32-in-memory)
             (equal (* (bpb_fatsz32 fat32-in-memory)
                       1/4 (bpb_bytspersec fat32-in-memory))
                    (fat-entry-count fat32-in-memory)))
    :hints
    (("goal" :in-theory (enable lofat-fs-p)
      :use fat-entry-count))))

(defthm
  lofat-to-string-inversion-lemma-52
  (implies
   (lofat-fs-p fat32-in-memory)
   (equal (take (+ (* 4 (fat-entry-count fat32-in-memory))
                   (- (* (bpb_numfats fat32-in-memory)
                         4 (fat-entry-count fat32-in-memory))))
                (data-region-string-helper
                 fat32-in-memory
                 (count-of-clusters fat32-in-memory)
                 nil))
          nil))
  :hints
  (("goal" :in-theory
    (disable lofat-fs-p-correctness-1)
    :use lofat-fs-p-correctness-1)))

(defthm
  lofat-to-string-inversion
  (implies
   (lofat-fs-p fat32-in-memory)
   (equal (string-to-lofat
           fat32-in-memory
           (lofat-to-string fat32-in-memory))
          (mv fat32-in-memory 0)))
  :hints
  (("goal"
    :in-theory
    (e/d (string-to-lofat
          painful-debugging-lemma-4
          painful-debugging-lemma-5
          by-slice-you-mean-the-whole-cake-2
          lofat-to-string-inversion-lemma-51
          cluster-size read-reserved-area
          update-data-region-alt)
         (lofat-fs-p-correctness-1))
    :use lofat-fs-p-correctness-1)))

(defund-nx
  eqfat (str1 str2)
  (b*
      (((mv fat32-in-memory1 error-code1)
        (string-to-lofat (create-fat32-in-memory)
                                   str1))
       (good1 (and (stringp str1)
                   (equal error-code1 0)))
       ((mv fat32-in-memory2 error-code2)
        (string-to-lofat (create-fat32-in-memory)
                                   str2))
       (good2 (and (stringp str2)
                   (equal error-code2 0)))
       ((unless (and good1 good2))
        (and (not good1) (not good2))))
    (lofat-equiv fat32-in-memory1 fat32-in-memory2)))

(defequiv
  eqfat
  :hints (("goal" :in-theory (enable eqfat))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    lofat-fs-p-of-string-to-lofat-lemma-1
    (implies
     (and
      (<= 512
          (combine16u (nth 12 (get-initial-bytes str))
                      (nth 11 (get-initial-bytes str))))
      (<= 1 (nth 13 (get-initial-bytes str)))
      (<
       0
       (* (nth 13 (get-initial-bytes str))
          (combine16u (nth 12 (get-initial-bytes str))
                      (nth 11 (get-initial-bytes str)))
          (floor (+ (- (combine16u (nth 15 (get-initial-bytes str))
                                   (nth 14 (get-initial-bytes str))))
                    (combine32u (nth 19 (get-remaining-rsvdbyts str))
                                (nth 18 (get-remaining-rsvdbyts str))
                                (nth 17 (get-remaining-rsvdbyts str))
                                (nth 16 (get-remaining-rsvdbyts str)))
                    (- (* (nth 0 (get-remaining-rsvdbyts str))
                          (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                      (nth 22 (get-remaining-rsvdbyts str))
                                      (nth 21 (get-remaining-rsvdbyts str))
                                      (nth 20 (get-remaining-rsvdbyts str))))))
                 (nth 13 (get-initial-bytes str))))))
     (not
      (< (floor (+ (- (combine16u (nth 15 (get-initial-bytes str))
                                  (nth 14 (get-initial-bytes str))))
                   (combine32u (nth 19 (get-remaining-rsvdbyts str))
                               (nth 18 (get-remaining-rsvdbyts str))
                               (nth 17 (get-remaining-rsvdbyts str))
                               (nth 16 (get-remaining-rsvdbyts str)))
                   (- (* (nth 0 (get-remaining-rsvdbyts str))
                         (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                     (nth 22 (get-remaining-rsvdbyts str))
                                     (nth 21 (get-remaining-rsvdbyts str))
                                     (nth 20 (get-remaining-rsvdbyts str))))))
                (nth 13 (get-initial-bytes str)))
         0))))

  (defthm
    lofat-fs-p-of-string-to-lofat-lemma-2
    (implies
     (and (<= 512
              (combine16u (nth 12 (get-initial-bytes str))
                          (nth 11 (get-initial-bytes str))))
          (<= 1
              (combine16u (nth 15 (get-initial-bytes str))
                          (nth 14 (get-initial-bytes str)))))
     (and
      (<= 512
          (* (combine16u (nth 12 (get-initial-bytes str))
                         (nth 11 (get-initial-bytes str)))
             (combine16u (nth 15 (get-initial-bytes str))
                         (nth 14 (get-initial-bytes str)))))
      (equal
       (nfix
        (binary-+
         '-16
         (binary-*
          (combine16u$inline (nth '12 (get-initial-bytes str))
                             (nth '11 (get-initial-bytes str)))
          (combine16u$inline
           (nth '15 (get-initial-bytes str))
           (nth '14 (get-initial-bytes str))))))
       (binary-+
        '-16
        (binary-*
         (combine16u$inline (nth '12 (get-initial-bytes str))
                            (nth '11 (get-initial-bytes str)))
         (combine16u$inline
          (nth '15 (get-initial-bytes str))
          (nth '14 (get-initial-bytes str))))))))
    :rule-classes
    ((:linear
      :corollary
      (implies
       (and (<= 512
                (combine16u (nth 12 (get-initial-bytes str))
                            (nth 11 (get-initial-bytes str))))
            (<= 1
                (combine16u (nth 15 (get-initial-bytes str))
                            (nth 14 (get-initial-bytes str)))))
       (<= 512
           (* (combine16u (nth 12 (get-initial-bytes str))
                          (nth 11 (get-initial-bytes str)))
              (combine16u (nth 15 (get-initial-bytes str))
                          (nth 14 (get-initial-bytes str)))))))
     (:rewrite
      :corollary
      (implies
       (and (<= 512
                (combine16u (nth 12 (get-initial-bytes str))
                            (nth 11 (get-initial-bytes str))))
            (<= 1
                (combine16u (nth 15 (get-initial-bytes str))
                            (nth 14 (get-initial-bytes str)))))
       (equal
        (nfix
         (binary-+
          '-16
          (binary-*
           (combine16u$inline (nth '12 (get-initial-bytes str))
                              (nth '11 (get-initial-bytes str)))
           (combine16u$inline
            (nth '15 (get-initial-bytes str))
            (nth '14 (get-initial-bytes str))))))
        (binary-+
         '-16
         (binary-*
          (combine16u$inline (nth '12 (get-initial-bytes str))
                             (nth '11 (get-initial-bytes str)))
          (combine16u$inline
           (nth '15 (get-initial-bytes str))
           (nth '14
                (get-initial-bytes str))))))))))

  (defthm
    lofat-fs-p-of-string-to-lofat-lemma-3
    (implies
     (integerp (* 1/4
                  (combine16u (nth 12 (get-initial-bytes str))
                              (nth 11 (get-initial-bytes str)))
                  (combine32u (nth 23 (get-remaining-rsvdbyts str))
                              (nth 22 (get-remaining-rsvdbyts str))
                              (nth 21 (get-remaining-rsvdbyts str))
                              (nth 20 (get-remaining-rsvdbyts str)))))
     (equal (* 4
               (floor (* (combine16u (nth 12 (get-initial-bytes str))
                                     (nth 11 (get-initial-bytes str)))
                         (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                     (nth 22 (get-remaining-rsvdbyts str))
                                     (nth 21 (get-remaining-rsvdbyts str))
                                     (nth 20 (get-remaining-rsvdbyts str))))
                      4))
            (* (combine16u (nth 12 (get-initial-bytes str))
                           (nth 11 (get-initial-bytes str)))
               (combine32u (nth 23 (get-remaining-rsvdbyts str))
                           (nth 22 (get-remaining-rsvdbyts str))
                           (nth 21 (get-remaining-rsvdbyts str))
                           (nth 20 (get-remaining-rsvdbyts str)))))))

  (defthm
    lofat-fs-p-of-string-to-lofat-lemma-4
    (implies
     (<= 1 (nth 0 (get-remaining-rsvdbyts str)))
     (not
      (<
       (binary-+
        (binary-* (combine16u$inline (nth '12 (get-initial-bytes str))
                                     (nth '11 (get-initial-bytes str)))
                  (combine16u$inline (nth '15 (get-initial-bytes str))
                                     (nth '14 (get-initial-bytes str))))
        (binary-*
         (combine16u$inline (nth '12 (get-initial-bytes str))
                            (nth '11 (get-initial-bytes str)))
         (binary-* (nth '0 (get-remaining-rsvdbyts str))
                   (combine32u$inline (nth '23 (get-remaining-rsvdbyts str))
                                      (nth '22 (get-remaining-rsvdbyts str))
                                      (nth '21 (get-remaining-rsvdbyts str))
                                      (nth '20
                                           (get-remaining-rsvdbyts str))))))
       0))))

  (defthm
    lofat-fs-p-of-string-to-lofat-lemma-6
    (implies
     (and (<= 512
              (combine16u (nth 12 (get-initial-bytes str))
                          (nth 11 (get-initial-bytes str))))
          (<= 1 (nth 13 (get-initial-bytes str))))
     (< '0
        (binary-* (nth '13 (get-initial-bytes str))
                  (combine16u$inline (nth '12 (get-initial-bytes str))
                                     (nth '11 (get-initial-bytes str))))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (enable string-to-lofat count-of-clusters
                         cluster-size fat-entry-count
                         lofat-fs-p
                         painful-debugging-lemma-1
                         painful-debugging-lemma-2
                         painful-debugging-lemma-3)))))

(defthm
  lofat-fs-p-of-string-to-lofat-lemma-5
  (implies (and (<= (nfix i)
                    (data-region-length fat32-in-memory))
                (cluster-listp (nth *data-regioni* fat32-in-memory)
                               cluster-size))
           (cluster-listp (nth *data-regioni*
                               (resize-data-region i fat32-in-memory))
                          cluster-size))
  :hints (("goal" :in-theory (enable data-region-length
                                     resize-data-region))))

(defthm
  lofat-fs-p-of-string-to-lofat
  (implies
   (and
    (stringp str)
    (equal
     (mv-nth 1
             (string-to-lofat fat32-in-memory str))
     0)
    (fat32-in-memoryp fat32-in-memory))
   (lofat-fs-p
    (mv-nth 0
            (string-to-lofat fat32-in-memory str))))
  :hints
  (("goal" :in-theory (enable string-to-lofat
                              count-of-clusters cluster-size
                              fat-entry-count read-reserved-area
                              lofat-fs-p
                              painful-debugging-lemma-1
                              painful-debugging-lemma-2
                              painful-debugging-lemma-3))))

(defund
  update-fat-aux (fa-table str pos)
  (if
   (zp pos)
   fa-table
   (let*
    ((ch-word
      (combine32u (char-code (char str (+ -1 (* pos 4))))
                  (char-code (char str (+ -2 (* pos 4))))
                  (char-code (char str (+ -3 (* pos 4))))
                  (char-code (char str (+ -4 (* pos 4))))))
     (fa-table (update-nth (+ -1 pos)
                           ch-word fa-table)))
    (update-fat-aux fa-table str (+ -1 pos)))))

(defthm
  nth-of-update-fat-aux
  (implies
   (integerp pos)
   (equal
    (nth n (update-fat-aux fa-table str pos))
    (if (< (nfix n) (nfix pos))
        (combine32u (char-code (char str (+ 3 (* (nfix n) 4))))
                    (char-code (char str (+ 2 (* (nfix n) 4))))
                    (char-code (char str (+ 1 (* (nfix n) 4))))
                    (char-code (char str (+ 0 (* (nfix n) 4)))))
        (nth n fa-table))))
  :hints (("goal" :in-theory (enable update-fat-aux)
           :induct (update-fat-aux fa-table str pos))
          ("subgoal *1/2.6'"
           :use (:theorem (implies (integerp pos)
                                   (iff (equal 0 (+ -1 pos))
                                        (equal pos 1)))))
          ("subgoal *1/2.1'"
           :use (:theorem (implies (integerp pos)
                                   (iff (equal 0 (+ -1 pos))
                                        (equal pos 1)))))))

(encapsulate
  ()

  (local
   (defun
       induction-scheme
       (fa-table1 fa-table2 pos str)
     (if
         (zp pos)
         (mv fa-table1 fa-table2 pos str)
       (induction-scheme
        (update-nth
         (+ -1 pos)
         (combine32u (char-code (char str (+ -1 (* pos 4))))
                     (char-code (char str (+ -2 (* pos 4))))
                     (char-code (char str (+ -3 (* pos 4))))
                     (char-code (char str (+ -4 (* pos 4)))))
         fa-table1)
        (update-nth
         (+ -1 pos)
         (combine32u (char-code (char str (+ -1 (* pos 4))))
                     (char-code (char str (+ -2 (* pos 4))))
                     (char-code (char str (+ -3 (* pos 4))))
                     (char-code (char str (+ -4 (* pos 4)))))
         fa-table2)
        (+ -1 pos)
        str))))

  (defthmd
    take-of-update-fat-aux
    (equal (take pos (update-fat-aux fa-table1 str pos))
           (take pos (update-fat-aux fa-table2 str pos)))
    :hints
    (("goal"
      :induct (induction-scheme fa-table1 fa-table2 pos str)
      :in-theory (e/d (update-fat-aux)
                      (equal-of-append-repeat
                       (:rewrite append-of-take-and-cons)))
      :expand (update-fat-aux fa-table2 str pos))
     ("subgoal *1/2"
      :use
      ((:instance
        (:rewrite append-of-take-and-cons)
        (y nil)
        (x (combine32u
            (char-code (nth (+ -1 (* 4 pos)) (explode str)))
            (char-code (nth (+ -2 (* 4 pos)) (explode str)))
            (char-code (nth (+ -3 (* 4 pos)) (explode str)))
            (char-code (nth (+ -4 (* 4 pos)) (explode str)))))
        (l
         (update-fat-aux
          (update-nth
           (+ -1 pos)
           (combine32u
            (char-code (nth (+ -1 (* 4 pos)) (explode str)))
            (char-code (nth (+ -2 (* 4 pos)) (explode str)))
            (char-code (nth (+ -3 (* 4 pos)) (explode str)))
            (char-code (nth (+ -4 (* 4 pos)) (explode str))))
           fa-table1)
          str (+ -1 pos)))
        (n (+ -1 pos)))
       (:instance
        (:rewrite append-of-take-and-cons)
        (y nil)
        (x (combine32u
            (char-code (nth (+ -1 (* 4 pos)) (explode str)))
            (char-code (nth (+ -2 (* 4 pos)) (explode str)))
            (char-code (nth (+ -3 (* 4 pos)) (explode str)))
            (char-code (nth (+ -4 (* 4 pos)) (explode str)))))
        (l
         (update-fat-aux
          (update-nth
           (+ -1 pos)
           (combine32u
            (char-code (nth (+ -1 (* 4 pos)) (explode str)))
            (char-code (nth (+ -2 (* 4 pos)) (explode str)))
            (char-code (nth (+ -3 (* 4 pos)) (explode str)))
            (char-code (nth (+ -4 (* 4 pos)) (explode str))))
           fa-table2)
          str (+ -1 pos)))
        (n (+ -1 pos))))))))

(defthm len-of-update-fat-aux
  (equal (len (update-fat-aux fa-table str pos))
         (max (nfix pos) (len fa-table)))
  :hints (("goal" :in-theory (enable update-fat-aux))))

(defthm
  true-list-fix-of-update-fat-aux
  (implies
   (true-listp fa-table)
   (equal (true-list-fix (update-fat-aux fa-table str pos))
          (update-fat-aux fa-table str pos)))
  :hints (("goal" :in-theory (enable update-fat-aux))))

(defthmd
  update-fat-alt
  (equal
   (update-fat fat32-in-memory str pos)
   (if (zp pos)
       fat32-in-memory
       (update-nth *fati*
                   (update-fat-aux (nth *fati* fat32-in-memory)
                                   str pos)
                   fat32-in-memory)))
  :hints
  (("goal" :in-theory (enable update-fat-aux update-fati)
    :induct (update-fat fat32-in-memory str pos))))

(encapsulate
  ()

  (local
   (defthm
     string-to-lofat-ignore-lemma-1
     (implies
      (and
       (stringp str)
       (equal
        (mv-nth 1
                (string-to-lofat fat32-in-memory str))
        0)
       (fat32-in-memoryp fat32-in-memory))
      (and
       (true-listp
        (mv-nth 0
                (string-to-lofat fat32-in-memory str)))
       (equal
        (len
         (mv-nth 0
                 (string-to-lofat fat32-in-memory str)))
        30)))
     :hints
     (("goal"
       :in-theory
       (e/d
        (lofat-fs-p fat32-in-memoryp)
        (lofat-fs-p-of-string-to-lofat))
       :use
       lofat-fs-p-of-string-to-lofat))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-2
     (implies
      (and (stringp str)
           (natp len)
           (>= (data-region-length fat32-in-memory)
               len)
           (fat32-in-memoryp fat32-in-memory)
           (< 0 (cluster-size fat32-in-memory))
           (>= (length str)
               (* (- (data-region-length fat32-in-memory)
                     len)
                  (cluster-size fat32-in-memory)))
           (equal
            (mv-nth
             1
             (update-data-region fat32-in-memory str len))
            0))
      (equal
       (nth
        *data-regioni*
        (mv-nth
         0
         (update-data-region fat32-in-memory str len)))
       (append
        (take (- (data-region-length fat32-in-memory)
                 len)
              (nth *data-regioni* fat32-in-memory))
        (make-clusters
         (subseq str
                 (* (- (data-region-length fat32-in-memory)
                       len)
                    (cluster-size fat32-in-memory))
                 (* (data-region-length fat32-in-memory)
                    (cluster-size fat32-in-memory)))
         (cluster-size fat32-in-memory)))))
     :hints
     (("goal"
       :in-theory (disable update-data-region-correctness-1)
       :do-not-induct t
       :use
       (update-data-region-alt
        update-data-region-correctness-1)))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-3
     (implies
      (not
       (equal fat32-in-memory (create-fat32-in-memory)))
      (equal
       (bpb_bytspersec
        (mv-nth 0
                (read-reserved-area fat32-in-memory str)))
       (bpb_bytspersec
        (mv-nth 0
                (read-reserved-area (create-fat32-in-memory)
                                    str)))))
     :hints (("goal" :in-theory (e/d (read-reserved-area)
                                     (create-fat32-in-memory))))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-4
     (implies
      (not
       (equal fat32-in-memory (create-fat32-in-memory)))
      (equal
       (bpb_rsvdseccnt
        (mv-nth 0
                (read-reserved-area fat32-in-memory str)))
       (bpb_rsvdseccnt
        (mv-nth 0
                (read-reserved-area (create-fat32-in-memory)
                                    str)))))
     :hints (("goal" :in-theory (enable read-reserved-area
                                        cluster-size
                                        count-of-clusters
                                        fat-entry-count)))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-5
     (implies
      (not
       (equal fat32-in-memory (create-fat32-in-memory)))
      (equal
       (bpb_fatsz32
        (mv-nth 0
                (read-reserved-area fat32-in-memory str)))
       (bpb_fatsz32
        (mv-nth 0
                (read-reserved-area (create-fat32-in-memory)
                                    str)))))
     :hints (("goal" :in-theory (enable read-reserved-area
                                        count-of-clusters
                                        fat-entry-count
                                        cluster-size)))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-6
     (implies
      (not
       (equal fat32-in-memory (create-fat32-in-memory)))
      (equal
       (bpb_numfats
        (mv-nth 0
                (read-reserved-area fat32-in-memory str)))
       (bpb_numfats
        (mv-nth 0
                (read-reserved-area (create-fat32-in-memory)
                                    str)))))
     :hints (("goal" :in-theory (enable read-reserved-area
                                        count-of-clusters
                                        fat-entry-count
                                        cluster-size)))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-7
     (implies
      (and
       (not
        (equal fat32-in-memory (create-fat32-in-memory)))
       (equal
        (mv-nth 1
                (read-reserved-area fat32-in-memory str))
        0))
      (equal
       (bpb_totsec32
        (mv-nth 0
                (read-reserved-area fat32-in-memory str)))
       (bpb_totsec32
        (mv-nth 0
                (read-reserved-area (create-fat32-in-memory)
                                    str)))))
     :hints (("goal" :in-theory (enable read-reserved-area
                                        count-of-clusters
                                        fat-entry-count
                                        cluster-size)))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-8
     (implies
      (not
       (equal fat32-in-memory (create-fat32-in-memory)))
      (equal
       (bpb_secperclus
        (mv-nth 0
                (read-reserved-area fat32-in-memory str)))
       (bpb_secperclus
        (mv-nth 0
                (read-reserved-area (create-fat32-in-memory)
                                    str)))))
     :hints (("goal" :in-theory (enable read-reserved-area
                                        count-of-clusters
                                        fat-entry-count
                                        cluster-size)))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-9
     (implies
      (not
       (equal fat32-in-memory (create-fat32-in-memory)))
      (equal
       (mv-nth 1
               (read-reserved-area fat32-in-memory str))
       (mv-nth 1
               (read-reserved-area (create-fat32-in-memory)
                                   str))))
     :hints (("goal" :in-theory (enable read-reserved-area
                                        count-of-clusters
                                        fat-entry-count
                                        cluster-size)))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-10
     (< '0
        (binary-*
         (bpb_bytspersec (mv-nth 0
                                 (read-reserved-area fat32-in-memory str)))
         (bpb_secperclus (mv-nth 0
                                 (read-reserved-area fat32-in-memory str)))))
     :rule-classes :linear
     :hints (("goal" :in-theory (e/d (read-reserved-area cluster-size))))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-11
     (implies
      (not (equal n *data-regioni*))
      (equal
       (nth n
            (mv-nth 0
                    (update-data-region fat32-in-memory str len)))
       (nth n fat32-in-memory)))
     :hints (("goal" :in-theory (enable update-data-regioni)))))

  (local
   (defthm string-to-lofat-ignore-lemma-12
     (equal (nth *fati*
                 (mv-nth 0
                         (read-reserved-area fat32-in-memory str)))
            (nth *fati* fat32-in-memory))
     :hints (("Goal" :in-theory (enable read-reserved-area)) )))

  (defthmd
    string-to-lofat-ignore-lemma-13
    (implies (and (equal (data-region-length fat32-in-memory1)
                         (data-region-length fat32-in-memory2))
                  (equal (cluster-size fat32-in-memory1)
                         (cluster-size fat32-in-memory2)))
             (equal (mv-nth 1
                            (update-data-region fat32-in-memory1 str len))
                    (mv-nth 1
                            (update-data-region fat32-in-memory2 str len))))
    :hints
    (("goal" :induct (mv (update-data-region fat32-in-memory1 str len)
                         (update-data-region fat32-in-memory2 str len)))))

  (defthmd
    string-to-lofat-ignore-lemma-14
    (implies
     (case-split (not (equal fat32-in-memory (create-fat32-in-memory))))
     (equal (mv-nth 1
                    (string-to-lofat fat32-in-memory str))
            (mv-nth 1
                    (string-to-lofat (create-fat32-in-memory)
                                               str))))
    :hints
    (("goal"
      :in-theory
      (enable string-to-lofat read-reserved-area
              update-data-region-alt cluster-size
              count-of-clusters fat-entry-count)
      :use
      (:instance
       (:rewrite string-to-lofat-ignore-lemma-13)
       (len
        (floor (+ (- (combine16u (nth 15 (get-initial-bytes str))
                                 (nth 14 (get-initial-bytes str))))
                  (combine32u (nth 19 (get-remaining-rsvdbyts str))
                              (nth 18 (get-remaining-rsvdbyts str))
                              (nth 17 (get-remaining-rsvdbyts str))
                              (nth 16 (get-remaining-rsvdbyts str)))
                  (- (* (nth 0 (get-remaining-rsvdbyts str))
                        (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                    (nth 22 (get-remaining-rsvdbyts str))
                                    (nth 21 (get-remaining-rsvdbyts str))
                                    (nth 20 (get-remaining-rsvdbyts str))))))
               (nth 13 (get-initial-bytes str))))
       (str
        (implode
         (take
          (+ (len (explode str))
             (- (* (combine16u (nth 12 (get-initial-bytes str))
                               (nth 11 (get-initial-bytes str)))
                   (combine16u (nth 15 (get-initial-bytes str))
                               (nth 14 (get-initial-bytes str)))))
             (- (* (combine16u (nth 12 (get-initial-bytes str))
                               (nth 11 (get-initial-bytes str)))
                   (nth 0 (get-remaining-rsvdbyts str))
                   (combine32u (nth 23 (get-remaining-rsvdbyts str))
                               (nth 22 (get-remaining-rsvdbyts str))
                               (nth 21 (get-remaining-rsvdbyts str))
                               (nth 20 (get-remaining-rsvdbyts str))))))
          (nthcdr (+ (* (combine16u (nth 12 (get-initial-bytes str))
                                    (nth 11 (get-initial-bytes str)))
                        (combine16u (nth 15 (get-initial-bytes str))
                                    (nth 14 (get-initial-bytes str))))
                     (* (combine16u (nth 12 (get-initial-bytes str))
                                    (nth 11 (get-initial-bytes str)))
                        (nth 0 (get-remaining-rsvdbyts str))
                        (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                    (nth 22 (get-remaining-rsvdbyts str))
                                    (nth 21 (get-remaining-rsvdbyts str))
                                    (nth 20 (get-remaining-rsvdbyts str)))))
                  (explode str)))))
       (fat32-in-memory1
        (resize-data-region
         (floor (+ (- (combine16u (nth 15 (get-initial-bytes str))
                                  (nth 14 (get-initial-bytes str))))
                   (combine32u (nth 19 (get-remaining-rsvdbyts str))
                               (nth 18 (get-remaining-rsvdbyts str))
                               (nth 17 (get-remaining-rsvdbyts str))
                               (nth 16 (get-remaining-rsvdbyts str)))
                   (- (* (nth 0 (get-remaining-rsvdbyts str))
                         (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                     (nth 22 (get-remaining-rsvdbyts str))
                                     (nth 21 (get-remaining-rsvdbyts str))
                                     (nth 20 (get-remaining-rsvdbyts str))))))
                (nth 13 (get-initial-bytes str)))
         (update-fat
          (update-bs_filsystype
           (take 8
                 (nthcdr 66 (get-remaining-rsvdbyts str)))
           (update-bs_vollab
            (take 11
                  (nthcdr 55 (get-remaining-rsvdbyts str)))
            (update-bs_volid
             (combine32u (nth 54 (get-remaining-rsvdbyts str))
                         (nth 53 (get-remaining-rsvdbyts str))
                         (nth 52 (get-remaining-rsvdbyts str))
                         (nth 51 (get-remaining-rsvdbyts str)))
             (update-bs_bootsig
              (nth 50 (get-remaining-rsvdbyts str))
              (update-bs_reserved1
               (nth 49 (get-remaining-rsvdbyts str))
               (update-bs_drvnum
                (nth 48 (get-remaining-rsvdbyts str))
                (update-bpb_reserved
                 (take 12
                       (nthcdr 36 (get-remaining-rsvdbyts str)))
                 (update-bpb_bkbootsec
                  (combine16u (nth 35 (get-remaining-rsvdbyts str))
                              (nth 34 (get-remaining-rsvdbyts str)))
                  (update-bpb_fsinfo
                   (combine16u (nth 33 (get-remaining-rsvdbyts str))
                               (nth 32 (get-remaining-rsvdbyts str)))
                   (update-bpb_rootclus
                    (combine32u (nth 31 (get-remaining-rsvdbyts str))
                                (nth 30 (get-remaining-rsvdbyts str))
                                (nth 29 (get-remaining-rsvdbyts str))
                                (nth 28 (get-remaining-rsvdbyts str)))
                    (update-bpb_fsver_major
                     (nth 27 (get-remaining-rsvdbyts str))
                     (update-bpb_fsver_minor
                      (nth 26 (get-remaining-rsvdbyts str))
                      (update-bpb_extflags
                       (combine16u (nth 25 (get-remaining-rsvdbyts str))
                                   (nth 24 (get-remaining-rsvdbyts str)))
                       (update-bpb_totsec32
                        (combine32u (nth 19 (get-remaining-rsvdbyts str))
                                    (nth 18 (get-remaining-rsvdbyts str))
                                    (nth 17 (get-remaining-rsvdbyts str))
                                    (nth 16 (get-remaining-rsvdbyts str)))
                        (update-bpb_hiddsec
                         (combine32u (nth 15 (get-remaining-rsvdbyts str))
                                     (nth 14 (get-remaining-rsvdbyts str))
                                     (nth 13 (get-remaining-rsvdbyts str))
                                     (nth 12 (get-remaining-rsvdbyts str)))
                         (update-bpb_numheads
                          (combine16u (nth 11 (get-remaining-rsvdbyts str))
                                      (nth 10 (get-remaining-rsvdbyts str)))
                          (update-bpb_secpertrk
                           (combine16u (nth 9 (get-remaining-rsvdbyts str))
                                       (nth 8 (get-remaining-rsvdbyts str)))
                           (update-bpb_fatsz16
                            (combine16u (nth 7 (get-remaining-rsvdbyts str))
                                        (nth 6 (get-remaining-rsvdbyts str)))
                            (update-bpb_media
                             (nth 5 (get-remaining-rsvdbyts str))
                             (update-bpb_totsec16
                              (combine16u (nth 4 (get-remaining-rsvdbyts str))
                                          (nth 3 (get-remaining-rsvdbyts str)))
                              (update-bpb_rootentcnt
                               (combine16u (nth 2 (get-remaining-rsvdbyts str))
                                           (nth 1 (get-remaining-rsvdbyts str)))
                               (update-bs_oemname
                                (take 8 (nthcdr 3 (get-initial-bytes str)))
                                (update-bs_jmpboot
                                 (take 3 (get-initial-bytes str))
                                 (update-bpb_bytspersec
                                  (combine16u (nth 12 (get-initial-bytes str))
                                              (nth 11 (get-initial-bytes str)))
                                  (update-bpb_fatsz32
                                   (combine32u
                                    (nth 23 (get-remaining-rsvdbyts str))
                                    (nth 22 (get-remaining-rsvdbyts str))
                                    (nth 21 (get-remaining-rsvdbyts str))
                                    (nth 20 (get-remaining-rsvdbyts str)))
                                   (update-bpb_numfats
                                    (nth 0 (get-remaining-rsvdbyts str))
                                    (update-bpb_rsvdseccnt
                                     (combine16u
                                      (nth 15 (get-initial-bytes str))
                                      (nth 14 (get-initial-bytes str)))
                                     (update-bpb_secperclus
                                      (nth 13 (get-initial-bytes str))
                                      (resize-fat
                                       (floor
                                        (*
                                         (combine16u
                                          (nth 12 (get-initial-bytes str))
                                          (nth 11 (get-initial-bytes str)))
                                         (combine32u
                                          (nth 23 (get-remaining-rsvdbyts str))
                                          (nth 22 (get-remaining-rsvdbyts str))
                                          (nth 21 (get-remaining-rsvdbyts str))
                                          (nth
                                           20 (get-remaining-rsvdbyts str))))
                                        4)
                                       fat32-in-memory)))))))))))))))))))))))))))))
          (implode
           (take (+ (* (combine16u (nth 12 (get-initial-bytes str))
                                   (nth 11 (get-initial-bytes str)))
                       (combine16u (nth 15 (get-initial-bytes str))
                                   (nth 14 (get-initial-bytes str))))
                    (- (* (combine16u (nth 12 (get-initial-bytes str))
                                      (nth 11 (get-initial-bytes str)))
                          (combine16u (nth 15 (get-initial-bytes str))
                                      (nth 14 (get-initial-bytes str)))))
                    (* (combine16u (nth 12 (get-initial-bytes str))
                                   (nth 11 (get-initial-bytes str)))
                       (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                   (nth 22 (get-remaining-rsvdbyts str))
                                   (nth 21 (get-remaining-rsvdbyts str))
                                   (nth 20 (get-remaining-rsvdbyts str)))))
                 (nthcdr (* (combine16u (nth 12 (get-initial-bytes str))
                                        (nth 11 (get-initial-bytes str)))
                            (combine16u (nth 15 (get-initial-bytes str))
                                        (nth 14 (get-initial-bytes str))))
                         (explode str))))
          (floor (* (combine16u (nth 12 (get-initial-bytes str))
                                (nth 11 (get-initial-bytes str)))
                    (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                (nth 22 (get-remaining-rsvdbyts str))
                                (nth 21 (get-remaining-rsvdbyts str))
                                (nth 20 (get-remaining-rsvdbyts str))))
                 4))))
       (fat32-in-memory2
        (resize-data-region
         (floor (+ (- (combine16u (nth 15 (get-initial-bytes str))
                                  (nth 14 (get-initial-bytes str))))
                   (combine32u (nth 19 (get-remaining-rsvdbyts str))
                               (nth 18 (get-remaining-rsvdbyts str))
                               (nth 17 (get-remaining-rsvdbyts str))
                               (nth 16 (get-remaining-rsvdbyts str)))
                   (- (* (nth 0 (get-remaining-rsvdbyts str))
                         (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                     (nth 22 (get-remaining-rsvdbyts str))
                                     (nth 21 (get-remaining-rsvdbyts str))
                                     (nth 20 (get-remaining-rsvdbyts str))))))
                (nth 13 (get-initial-bytes str)))
         (update-fat
          (update-bs_filsystype
           (take 8
                 (nthcdr 66 (get-remaining-rsvdbyts str)))
           (update-bs_vollab
            (take 11
                  (nthcdr 55 (get-remaining-rsvdbyts str)))
            (update-bs_volid
             (combine32u (nth 54 (get-remaining-rsvdbyts str))
                         (nth 53 (get-remaining-rsvdbyts str))
                         (nth 52 (get-remaining-rsvdbyts str))
                         (nth 51 (get-remaining-rsvdbyts str)))
             (update-bs_bootsig
              (nth 50 (get-remaining-rsvdbyts str))
              (update-bs_reserved1
               (nth 49 (get-remaining-rsvdbyts str))
               (update-bs_drvnum
                (nth 48 (get-remaining-rsvdbyts str))
                (update-bpb_reserved
                 (take 12
                       (nthcdr 36 (get-remaining-rsvdbyts str)))
                 (update-bpb_bkbootsec
                  (combine16u (nth 35 (get-remaining-rsvdbyts str))
                              (nth 34 (get-remaining-rsvdbyts str)))
                  (update-bpb_fsinfo
                   (combine16u (nth 33 (get-remaining-rsvdbyts str))
                               (nth 32 (get-remaining-rsvdbyts str)))
                   (update-bpb_rootclus
                    (combine32u (nth 31 (get-remaining-rsvdbyts str))
                                (nth 30 (get-remaining-rsvdbyts str))
                                (nth 29 (get-remaining-rsvdbyts str))
                                (nth 28 (get-remaining-rsvdbyts str)))
                    (update-bpb_fsver_major
                     (nth 27 (get-remaining-rsvdbyts str))
                     (update-bpb_fsver_minor
                      (nth 26 (get-remaining-rsvdbyts str))
                      (update-bpb_extflags
                       (combine16u (nth 25 (get-remaining-rsvdbyts str))
                                   (nth 24 (get-remaining-rsvdbyts str)))
                       (update-bpb_totsec32
                        (combine32u (nth 19 (get-remaining-rsvdbyts str))
                                    (nth 18 (get-remaining-rsvdbyts str))
                                    (nth 17 (get-remaining-rsvdbyts str))
                                    (nth 16 (get-remaining-rsvdbyts str)))
                        (update-bpb_hiddsec
                         (combine32u (nth 15 (get-remaining-rsvdbyts str))
                                     (nth 14 (get-remaining-rsvdbyts str))
                                     (nth 13 (get-remaining-rsvdbyts str))
                                     (nth 12 (get-remaining-rsvdbyts str)))
                         (update-bpb_numheads
                          (combine16u (nth 11 (get-remaining-rsvdbyts str))
                                      (nth 10 (get-remaining-rsvdbyts str)))
                          (update-bpb_secpertrk
                           (combine16u (nth 9 (get-remaining-rsvdbyts str))
                                       (nth 8 (get-remaining-rsvdbyts str)))
                           (update-bpb_fatsz16
                            (combine16u (nth 7 (get-remaining-rsvdbyts str))
                                        (nth 6 (get-remaining-rsvdbyts str)))
                            (update-bpb_media
                             (nth 5 (get-remaining-rsvdbyts str))
                             (update-bpb_totsec16
                              (combine16u (nth 4 (get-remaining-rsvdbyts str))
                                          (nth 3 (get-remaining-rsvdbyts str)))
                              (update-bpb_rootentcnt
                               (combine16u (nth 2 (get-remaining-rsvdbyts str))
                                           (nth 1 (get-remaining-rsvdbyts str)))
                               (update-bs_oemname
                                (take 8 (nthcdr 3 (get-initial-bytes str)))
                                (update-bs_jmpboot
                                 (take 3 (get-initial-bytes str))
                                 (update-bpb_bytspersec
                                  (combine16u (nth 12 (get-initial-bytes str))
                                              (nth 11 (get-initial-bytes str)))
                                  (update-bpb_fatsz32
                                   (combine32u
                                    (nth 23 (get-remaining-rsvdbyts str))
                                    (nth 22 (get-remaining-rsvdbyts str))
                                    (nth 21 (get-remaining-rsvdbyts str))
                                    (nth 20 (get-remaining-rsvdbyts str)))
                                   (update-bpb_numfats
                                    (nth 0 (get-remaining-rsvdbyts str))
                                    (update-bpb_rsvdseccnt
                                     (combine16u
                                      (nth 15 (get-initial-bytes str))
                                      (nth 14 (get-initial-bytes str)))
                                     (update-bpb_secperclus
                                      (nth 13 (get-initial-bytes str))
                                      (resize-fat
                                       (floor
                                        (*
                                         (combine16u
                                          (nth 12 (get-initial-bytes str))
                                          (nth 11 (get-initial-bytes str)))
                                         (combine32u
                                          (nth 23 (get-remaining-rsvdbyts str))
                                          (nth 22 (get-remaining-rsvdbyts str))
                                          (nth 21 (get-remaining-rsvdbyts str))
                                          (nth
                                           20 (get-remaining-rsvdbyts str))))
                                        4)
                                       (create-fat32-in-memory))))))))))))))))))))))))))))))
          (implode
           (take (+ (* (combine16u (nth 12 (get-initial-bytes str))
                                   (nth 11 (get-initial-bytes str)))
                       (combine16u (nth 15 (get-initial-bytes str))
                                   (nth 14 (get-initial-bytes str))))
                    (- (* (combine16u (nth 12 (get-initial-bytes str))
                                      (nth 11 (get-initial-bytes str)))
                          (combine16u (nth 15 (get-initial-bytes str))
                                      (nth 14 (get-initial-bytes str)))))
                    (* (combine16u (nth 12 (get-initial-bytes str))
                                   (nth 11 (get-initial-bytes str)))
                       (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                   (nth 22 (get-remaining-rsvdbyts str))
                                   (nth 21 (get-remaining-rsvdbyts str))
                                   (nth 20 (get-remaining-rsvdbyts str)))))
                 (nthcdr (* (combine16u (nth 12 (get-initial-bytes str))
                                        (nth 11 (get-initial-bytes str)))
                            (combine16u (nth 15 (get-initial-bytes str))
                                        (nth 14 (get-initial-bytes str))))
                         (explode str))))
          (floor (* (combine16u (nth 12 (get-initial-bytes str))
                                (nth 11 (get-initial-bytes str)))
                    (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                (nth 22 (get-remaining-rsvdbyts str))
                                (nth 21 (get-remaining-rsvdbyts str))
                                (nth 20 (get-remaining-rsvdbyts str))))
                 4))))))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-16
     (equal
      (nth *fati*
           (update-fat fat32-in-memory str pos))
      (if (zp pos)
          (nth *fati* fat32-in-memory)
        (update-fat-aux (nth *fati* fat32-in-memory)
                        str pos)))
     :hints
     (("goal" :use update-fat-alt))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-17
     (implies
      (and
       (not (equal fat32-in-memory (create-fat32-in-memory)))
       (<=
        (+ 2
           (floor (+ (- (combine16u (nth 15 (get-initial-bytes str))
                                    (nth 14 (get-initial-bytes str))))
                     (combine32u (nth 19 (get-remaining-rsvdbyts str))
                                 (nth 18 (get-remaining-rsvdbyts str))
                                 (nth 17 (get-remaining-rsvdbyts str))
                                 (nth 16 (get-remaining-rsvdbyts str)))
                     (- (* (nth 0 (get-remaining-rsvdbyts str))
                           (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                       (nth 22 (get-remaining-rsvdbyts str))
                                       (nth 21 (get-remaining-rsvdbyts str))
                                       (nth 20 (get-remaining-rsvdbyts str))))))
                  (nth 13 (get-initial-bytes str))))
        (floor (* (combine16u (nth 12 (get-initial-bytes str))
                              (nth 11 (get-initial-bytes str)))
                  (combine32u (nth 23 (get-remaining-rsvdbyts str))
                              (nth 22 (get-remaining-rsvdbyts str))
                              (nth 21 (get-remaining-rsvdbyts str))
                              (nth 20 (get-remaining-rsvdbyts str))))
               4))
       (<
        (fat32-entry-mask (combine32u (nth 31 (get-remaining-rsvdbyts str))
                                      (nth 30 (get-remaining-rsvdbyts str))
                                      (nth 29 (get-remaining-rsvdbyts str))
                                      (nth 28 (get-remaining-rsvdbyts str))))
        (+ 2
           (floor (+ (- (combine16u (nth 15 (get-initial-bytes str))
                                    (nth 14 (get-initial-bytes str))))
                     (combine32u (nth 19 (get-remaining-rsvdbyts str))
                                 (nth 18 (get-remaining-rsvdbyts str))
                                 (nth 17 (get-remaining-rsvdbyts str))
                                 (nth 16 (get-remaining-rsvdbyts str)))
                     (- (* (nth 0 (get-remaining-rsvdbyts str))
                           (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                       (nth 22 (get-remaining-rsvdbyts str))
                                       (nth 21 (get-remaining-rsvdbyts str))
                                       (nth 20 (get-remaining-rsvdbyts str))))))
                  (nth 13 (get-initial-bytes str)))))
       (<= (floor (+ (- (combine16u (nth 15 (get-initial-bytes str))
                                    (nth 14 (get-initial-bytes str))))
                     (combine32u (nth 19 (get-remaining-rsvdbyts str))
                                 (nth 18 (get-remaining-rsvdbyts str))
                                 (nth 17 (get-remaining-rsvdbyts str))
                                 (nth 16 (get-remaining-rsvdbyts str)))
                     (- (* (nth 0 (get-remaining-rsvdbyts str))
                           (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                       (nth 22 (get-remaining-rsvdbyts str))
                                       (nth 21 (get-remaining-rsvdbyts str))
                                       (nth 20 (get-remaining-rsvdbyts str))))))
                  (nth 13 (get-initial-bytes str)))
           268435445))
      (equal
       (update-fat-aux
        (resize-list
         (nth *fati* fat32-in-memory)
         (floor (* (combine16u (nth 12 (get-initial-bytes str))
                               (nth 11 (get-initial-bytes str)))
                   (combine32u (nth 23 (get-remaining-rsvdbyts str))
                               (nth 22 (get-remaining-rsvdbyts str))
                               (nth 21 (get-remaining-rsvdbyts str))
                               (nth 20 (get-remaining-rsvdbyts str))))
                4)
         0)
        (implode (take (+ (* (combine16u (nth 12 (get-initial-bytes str))
                                         (nth 11 (get-initial-bytes str)))
                             (combine16u (nth 15 (get-initial-bytes str))
                                         (nth 14 (get-initial-bytes str))))
                          (- (* (combine16u (nth 12 (get-initial-bytes str))
                                            (nth 11 (get-initial-bytes str)))
                                (combine16u (nth 15 (get-initial-bytes str))
                                            (nth 14 (get-initial-bytes str)))))
                          (* (combine16u (nth 12 (get-initial-bytes str))
                                         (nth 11 (get-initial-bytes str)))
                             (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                         (nth 22 (get-remaining-rsvdbyts str))
                                         (nth 21 (get-remaining-rsvdbyts str))
                                         (nth 20 (get-remaining-rsvdbyts str)))))
                       (nthcdr (* (combine16u (nth 12 (get-initial-bytes str))
                                              (nth 11 (get-initial-bytes str)))
                                  (combine16u (nth 15 (get-initial-bytes str))
                                              (nth 14 (get-initial-bytes str))))
                               (explode str))))
        (floor (* (combine16u (nth 12 (get-initial-bytes str))
                              (nth 11 (get-initial-bytes str)))
                  (combine32u (nth 23 (get-remaining-rsvdbyts str))
                              (nth 22 (get-remaining-rsvdbyts str))
                              (nth 21 (get-remaining-rsvdbyts str))
                              (nth 20 (get-remaining-rsvdbyts str))))
               4))
       (update-fat-aux
        (resize-list
         (nth *fati* (create-fat32-in-memory))
         (floor (* (combine16u (nth 12 (get-initial-bytes str))
                               (nth 11 (get-initial-bytes str)))
                   (combine32u (nth 23 (get-remaining-rsvdbyts str))
                               (nth 22 (get-remaining-rsvdbyts str))
                               (nth 21 (get-remaining-rsvdbyts str))
                               (nth 20 (get-remaining-rsvdbyts str))))
                4)
         0)
        (implode (take (+ (* (combine16u (nth 12 (get-initial-bytes str))
                                         (nth 11 (get-initial-bytes str)))
                             (combine16u (nth 15 (get-initial-bytes str))
                                         (nth 14 (get-initial-bytes str))))
                          (- (* (combine16u (nth 12 (get-initial-bytes str))
                                            (nth 11 (get-initial-bytes str)))
                                (combine16u (nth 15 (get-initial-bytes str))
                                            (nth 14 (get-initial-bytes str)))))
                          (* (combine16u (nth 12 (get-initial-bytes str))
                                         (nth 11 (get-initial-bytes str)))
                             (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                         (nth 22 (get-remaining-rsvdbyts str))
                                         (nth 21 (get-remaining-rsvdbyts str))
                                         (nth 20 (get-remaining-rsvdbyts str)))))
                       (nthcdr (* (combine16u (nth 12 (get-initial-bytes str))
                                              (nth 11 (get-initial-bytes str)))
                                  (combine16u (nth 15 (get-initial-bytes str))
                                              (nth 14 (get-initial-bytes str))))
                               (explode str))))
        (floor (* (combine16u (nth 12 (get-initial-bytes str))
                              (nth 11 (get-initial-bytes str)))
                  (combine32u (nth 23 (get-remaining-rsvdbyts str))
                              (nth 22 (get-remaining-rsvdbyts str))
                              (nth 21 (get-remaining-rsvdbyts str))
                              (nth 20 (get-remaining-rsvdbyts str))))
               4))))
     :hints
     (("goal"
       :in-theory (enable by-slice-you-mean-the-whole-cake-2)
       :use
       (:instance
        (:rewrite take-of-update-fat-aux)
        (str
         (implode
          (take (+ (* (combine16u (nth 12 (get-initial-bytes str))
                                  (nth 11 (get-initial-bytes str)))
                      (combine16u (nth 15 (get-initial-bytes str))
                                  (nth 14 (get-initial-bytes str))))
                   (- (* (combine16u (nth 12 (get-initial-bytes str))
                                     (nth 11 (get-initial-bytes str)))
                         (combine16u (nth 15 (get-initial-bytes str))
                                     (nth 14 (get-initial-bytes str)))))
                   (* (combine16u (nth 12 (get-initial-bytes str))
                                  (nth 11 (get-initial-bytes str)))
                      (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                  (nth 22 (get-remaining-rsvdbyts str))
                                  (nth 21 (get-remaining-rsvdbyts str))
                                  (nth 20 (get-remaining-rsvdbyts str)))))
                (nthcdr (* (combine16u (nth 12 (get-initial-bytes str))
                                       (nth 11 (get-initial-bytes str)))
                           (combine16u (nth 15 (get-initial-bytes str))
                                       (nth 14 (get-initial-bytes str))))
                        (explode str)))))
        (fa-table1
         (resize-list
          (nth *fati* fat32-in-memory)
          (floor (* (combine16u (nth 12 (get-initial-bytes str))
                                (nth 11 (get-initial-bytes str)))
                    (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                (nth 22 (get-remaining-rsvdbyts str))
                                (nth 21 (get-remaining-rsvdbyts str))
                                (nth 20 (get-remaining-rsvdbyts str))))
                 4)
          0))
        (fa-table2
         (resize-list
          (nth *fati* (create-fat32-in-memory))
          (floor (* (combine16u (nth 12 (get-initial-bytes str))
                                (nth 11 (get-initial-bytes str)))
                    (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                (nth 22 (get-remaining-rsvdbyts str))
                                (nth 21 (get-remaining-rsvdbyts str))
                                (nth 20 (get-remaining-rsvdbyts str))))
                 4)
          0))
        (pos (floor (* (combine16u (nth 12 (get-initial-bytes str))
                                   (nth 11 (get-initial-bytes str)))
                       (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                   (nth 22 (get-remaining-rsvdbyts str))
                                   (nth 21 (get-remaining-rsvdbyts str))
                                   (nth 20 (get-remaining-rsvdbyts str))))
                    4)))))))

  (local (include-book "std/lists/nth" :dir :system))

  (local (in-theory (e/d
                     (count-of-clusters cluster-size fat-entry-count)
                     (nth-when-zp
                      ;; These are from accumulated-persistence.
                      (:definition update-nth-array)
                      (:definition len)))))

  (local
   (defthm
     string-to-lofat-ignore-lemma-15
     (implies
      (and
       (<= 512
           (combine16u (nth 12 (get-initial-bytes str))
                       (nth 11 (get-initial-bytes str))))
       (<= 1 (nth 13 (get-initial-bytes str)))
       (<= 2
           (fat32-entry-mask (combine32u (nth 31 (get-remaining-rsvdbyts str))
                                         (nth 30 (get-remaining-rsvdbyts str))
                                         (nth 29 (get-remaining-rsvdbyts str))
                                         (nth 28 (get-remaining-rsvdbyts str)))))
       (<
        (fat32-entry-mask (combine32u (nth 31 (get-remaining-rsvdbyts str))
                                      (nth 30 (get-remaining-rsvdbyts str))
                                      (nth 29 (get-remaining-rsvdbyts str))
                                      (nth 28 (get-remaining-rsvdbyts str))))
        (+ 2
           (floor (+ (- (combine16u (nth 15 (get-initial-bytes str))
                                    (nth 14 (get-initial-bytes str))))
                     (combine32u (nth 19 (get-remaining-rsvdbyts str))
                                 (nth 18 (get-remaining-rsvdbyts str))
                                 (nth 17 (get-remaining-rsvdbyts str))
                                 (nth 16 (get-remaining-rsvdbyts str)))
                     (- (* (nth 0 (get-remaining-rsvdbyts str))
                           (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                       (nth 22 (get-remaining-rsvdbyts str))
                                       (nth 21 (get-remaining-rsvdbyts str))
                                       (nth 20 (get-remaining-rsvdbyts str))))))
                  (nth 13 (get-initial-bytes str)))))
       (equal
        (mv-nth
         1
         (update-data-region
          (resize-data-region
           (floor (+ (- (combine16u (nth 15 (get-initial-bytes str))
                                    (nth 14 (get-initial-bytes str))))
                     (combine32u (nth 19 (get-remaining-rsvdbyts str))
                                 (nth 18 (get-remaining-rsvdbyts str))
                                 (nth 17 (get-remaining-rsvdbyts str))
                                 (nth 16 (get-remaining-rsvdbyts str)))
                     (- (* (nth 0 (get-remaining-rsvdbyts str))
                           (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                       (nth 22 (get-remaining-rsvdbyts str))
                                       (nth 21 (get-remaining-rsvdbyts str))
                                       (nth 20 (get-remaining-rsvdbyts str))))))
                  (nth 13 (get-initial-bytes str)))
           (update-fat
            (update-bs_filsystype
             (take 8
                   (nthcdr 66 (get-remaining-rsvdbyts str)))
             (update-bs_vollab
              (take 11
                    (nthcdr 55 (get-remaining-rsvdbyts str)))
              (update-bs_volid
               (combine32u (nth 54 (get-remaining-rsvdbyts str))
                           (nth 53 (get-remaining-rsvdbyts str))
                           (nth 52 (get-remaining-rsvdbyts str))
                           (nth 51 (get-remaining-rsvdbyts str)))
               (update-bs_bootsig
                (nth 50 (get-remaining-rsvdbyts str))
                (update-bs_reserved1
                 (nth 49 (get-remaining-rsvdbyts str))
                 (update-bs_drvnum
                  (nth 48 (get-remaining-rsvdbyts str))
                  (update-bpb_reserved
                   (take 12
                         (nthcdr 36 (get-remaining-rsvdbyts str)))
                   (update-bpb_bkbootsec
                    (combine16u (nth 35 (get-remaining-rsvdbyts str))
                                (nth 34 (get-remaining-rsvdbyts str)))
                    (update-bpb_fsinfo
                     (combine16u (nth 33 (get-remaining-rsvdbyts str))
                                 (nth 32 (get-remaining-rsvdbyts str)))
                     (update-bpb_rootclus
                      (combine32u (nth 31 (get-remaining-rsvdbyts str))
                                  (nth 30 (get-remaining-rsvdbyts str))
                                  (nth 29 (get-remaining-rsvdbyts str))
                                  (nth 28 (get-remaining-rsvdbyts str)))
                      (update-bpb_fsver_major
                       (nth 27 (get-remaining-rsvdbyts str))
                       (update-bpb_fsver_minor
                        (nth 26 (get-remaining-rsvdbyts str))
                        (update-bpb_extflags
                         (combine16u (nth 25 (get-remaining-rsvdbyts str))
                                     (nth 24 (get-remaining-rsvdbyts str)))
                         (update-bpb_totsec32
                          (combine32u (nth 19 (get-remaining-rsvdbyts str))
                                      (nth 18 (get-remaining-rsvdbyts str))
                                      (nth 17 (get-remaining-rsvdbyts str))
                                      (nth 16 (get-remaining-rsvdbyts str)))
                          (update-bpb_hiddsec
                           (combine32u (nth 15 (get-remaining-rsvdbyts str))
                                       (nth 14 (get-remaining-rsvdbyts str))
                                       (nth 13 (get-remaining-rsvdbyts str))
                                       (nth 12 (get-remaining-rsvdbyts str)))
                           (update-bpb_numheads
                            (combine16u (nth 11 (get-remaining-rsvdbyts str))
                                        (nth 10 (get-remaining-rsvdbyts str)))
                            (update-bpb_secpertrk
                             (combine16u (nth 9 (get-remaining-rsvdbyts str))
                                         (nth 8 (get-remaining-rsvdbyts str)))
                             (update-bpb_fatsz16
                              (combine16u (nth 7 (get-remaining-rsvdbyts str))
                                          (nth 6 (get-remaining-rsvdbyts str)))
                              (update-bpb_media
                               (nth 5 (get-remaining-rsvdbyts str))
                               (update-bpb_totsec16
                                (combine16u (nth 4 (get-remaining-rsvdbyts str))
                                            (nth 3 (get-remaining-rsvdbyts str)))
                                (update-bpb_rootentcnt
                                 (combine16u
                                  (nth 2 (get-remaining-rsvdbyts str))
                                  (nth 1 (get-remaining-rsvdbyts str)))
                                 (update-bs_oemname
                                  (take 8 (nthcdr 3 (get-initial-bytes str)))
                                  (update-bs_jmpboot
                                   (take 3 (get-initial-bytes str))
                                   (update-bpb_bytspersec
                                    (combine16u (nth 12 (get-initial-bytes str))
                                                (nth 11 (get-initial-bytes str)))
                                    (update-bpb_fatsz32
                                     (combine32u
                                      (nth 23 (get-remaining-rsvdbyts str))
                                      (nth 22 (get-remaining-rsvdbyts str))
                                      (nth 21 (get-remaining-rsvdbyts str))
                                      (nth 20 (get-remaining-rsvdbyts str)))
                                     (update-bpb_numfats
                                      (nth 0 (get-remaining-rsvdbyts str))
                                      (update-bpb_rsvdseccnt
                                       (combine16u
                                        (nth 15 (get-initial-bytes str))
                                        (nth 14 (get-initial-bytes str)))
                                       (update-bpb_secperclus
                                        (nth 13 (get-initial-bytes str))
                                        (resize-fat
                                         (floor
                                          (*
                                           (combine16u
                                            (nth 12 (get-initial-bytes str))
                                            (nth 11 (get-initial-bytes str)))
                                           (combine32u
                                            (nth 23 (get-remaining-rsvdbyts str))
                                            (nth 22 (get-remaining-rsvdbyts str))
                                            (nth 21 (get-remaining-rsvdbyts str))
                                            (nth
                                             20 (get-remaining-rsvdbyts str))))
                                          4)
                                         (create-fat32-in-memory))))))))))))))))))))))))))))))
            (implode
             (take (+ (* (combine16u (nth 12 (get-initial-bytes str))
                                     (nth 11 (get-initial-bytes str)))
                         (combine16u (nth 15 (get-initial-bytes str))
                                     (nth 14 (get-initial-bytes str))))
                      (- (* (combine16u (nth 12 (get-initial-bytes str))
                                        (nth 11 (get-initial-bytes str)))
                            (combine16u (nth 15 (get-initial-bytes str))
                                        (nth 14 (get-initial-bytes str)))))
                      (* (combine16u (nth 12 (get-initial-bytes str))
                                     (nth 11 (get-initial-bytes str)))
                         (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                     (nth 22 (get-remaining-rsvdbyts str))
                                     (nth 21 (get-remaining-rsvdbyts str))
                                     (nth 20 (get-remaining-rsvdbyts str)))))
                   (nthcdr (* (combine16u (nth 12 (get-initial-bytes str))
                                          (nth 11 (get-initial-bytes str)))
                              (combine16u (nth 15 (get-initial-bytes str))
                                          (nth 14 (get-initial-bytes str))))
                           (explode str))))
            (floor (* (combine16u (nth 12 (get-initial-bytes str))
                                  (nth 11 (get-initial-bytes str)))
                      (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                  (nth 22 (get-remaining-rsvdbyts str))
                                  (nth 21 (get-remaining-rsvdbyts str))
                                  (nth 20 (get-remaining-rsvdbyts str))))
                   4)))
          (implode
           (take
            (+ (len (explode str))
               (- (* (combine16u (nth 12 (get-initial-bytes str))
                                 (nth 11 (get-initial-bytes str)))
                     (combine16u (nth 15 (get-initial-bytes str))
                                 (nth 14 (get-initial-bytes str)))))
               (- (* (combine16u (nth 12 (get-initial-bytes str))
                                 (nth 11 (get-initial-bytes str)))
                     (nth 0 (get-remaining-rsvdbyts str))
                     (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                 (nth 22 (get-remaining-rsvdbyts str))
                                 (nth 21 (get-remaining-rsvdbyts str))
                                 (nth 20 (get-remaining-rsvdbyts str))))))
            (nthcdr (+ (* (combine16u (nth 12 (get-initial-bytes str))
                                      (nth 11 (get-initial-bytes str)))
                          (combine16u (nth 15 (get-initial-bytes str))
                                      (nth 14 (get-initial-bytes str))))
                       (* (combine16u (nth 12 (get-initial-bytes str))
                                      (nth 11 (get-initial-bytes str)))
                          (nth 0 (get-remaining-rsvdbyts str))
                          (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                      (nth 22 (get-remaining-rsvdbyts str))
                                      (nth 21 (get-remaining-rsvdbyts str))
                                      (nth 20 (get-remaining-rsvdbyts str)))))
                    (explode str))))
          (floor (+ (- (combine16u (nth 15 (get-initial-bytes str))
                                   (nth 14 (get-initial-bytes str))))
                    (combine32u (nth 19 (get-remaining-rsvdbyts str))
                                (nth 18 (get-remaining-rsvdbyts str))
                                (nth 17 (get-remaining-rsvdbyts str))
                                (nth 16 (get-remaining-rsvdbyts str)))
                    (- (* (nth 0 (get-remaining-rsvdbyts str))
                          (combine32u (nth 23 (get-remaining-rsvdbyts str))
                                      (nth 22 (get-remaining-rsvdbyts str))
                                      (nth 21 (get-remaining-rsvdbyts str))
                                      (nth 20 (get-remaining-rsvdbyts str))))))
                 (nth 13 (get-initial-bytes str)))))
        0))
      (integerp
       (binary-+
        (len (explode$inline str))
        (binary-+
         (unary--
          (binary-* (combine16u$inline (nth '12 (get-initial-bytes str))
                                       (nth '11 (get-initial-bytes str)))
                    (combine16u$inline (nth '15 (get-initial-bytes str))
                                       (nth '14 (get-initial-bytes str)))))
         (unary--
          (binary-*
           (combine16u$inline (nth '12 (get-initial-bytes str))
                              (nth '11 (get-initial-bytes str)))
           (binary-*
            (nth '0 (get-remaining-rsvdbyts str))
            (combine32u$inline (nth '23 (get-remaining-rsvdbyts str))
                               (nth '22 (get-remaining-rsvdbyts str))
                               (nth '21 (get-remaining-rsvdbyts str))
                               (nth '20
                                    (get-remaining-rsvdbyts str))))))))))))

  (defthm
    string-to-lofat-ignore-lemma-18
    (implies
     (and (not (equal fat32-in-memory
                      (create-fat32-in-memory)))
          (fat32-in-memoryp fat32-in-memory)
          (equal (mv-nth 1
                         (string-to-lofat fat32-in-memory str))
                 0)
          (equal (mv-nth 1
                         (string-to-lofat (create-fat32-in-memory)
                                                    str))
                 0)
          (integerp n)
          (<= 0 n)
          (< n 30))
     (equal (nth n
                 (mv-nth 0
                         (string-to-lofat fat32-in-memory str)))
            (nth n
                 (mv-nth 0
                         (string-to-lofat (create-fat32-in-memory)
                                                    str)))))
    :hints
    (("goal" :cases ((equal n *bs_jmpbooti*)
                     (equal n *bs_oemnamei*)
                     (equal n *bpb_bytspersec*)
                     (equal n *bpb_secperclus*)
                     (equal n *bpb_rsvdseccnt*)
                     (equal n *bpb_numfats*)
                     (equal n *bpb_rootentcnt*)
                     (equal n *bpb_totsec16*)
                     (equal n *bpb_media*)
                     (equal n *bpb_fatsz16*)
                     (equal n *bpb_secpertrk*)
                     (equal n *bpb_numheads*)
                     (equal n *bpb_hiddsec*)
                     (equal n *bpb_totsec32*)
                     (equal n *bpb_fatsz32*)
                     (equal n *bpb_extflags*)
                     (equal n *bpb_fsver_minor*)
                     (equal n *bpb_fsver_major*)
                     (equal n *bpb_rootclus*)
                     (equal n *bpb_fsinfo*)
                     (equal n *bpb_bkbootsec*)
                     (equal n *bpb_reservedi*)
                     (equal n *bs_drvnum*)
                     (equal n *bs_reserved1*)
                     (equal n *bs_bootsig*)
                     (equal n *bs_volid*)
                     (equal n *bs_vollabi*)
                     (equal n *bs_filsystypei*)
                     (equal n *fati*)
                     (equal n *data-regioni*))
      :in-theory (e/d (string-to-lofat read-reserved-area)
                      (;; accumulated-persistence suggests disabling a bunch of
                       ;; rules.
                       (:REWRITE NTH-WHEN-ATOM)
                       (:DEFINITION UPDATE-DATA-REGION)
                       (:REWRITE CONSP-OF-TAKE)
                       (:DEFINITION TAKE-REDEFINITION)
                       (:REWRITE
                        RESIZE-FAT-OF-FAT-LENGTH-WHEN-FAT32-IN-MEMORYP
                        . 2)
                       (:REWRITE CAR-OF-NTHCDR)
                       (:REWRITE NTH-OF-MAKE-CHARACTER-LIST)
                       (:DEFINITION UPDATE-FAT))))))

  (defthm
    string-to-lofat-ignore
    (implies
     (and
      (stringp str)
      (not (equal fat32-in-memory
                  (create-fat32-in-memory)))
      (fat32-in-memoryp fat32-in-memory)
      (equal
       (mv-nth 1
               (string-to-lofat (create-fat32-in-memory)
                                          str))
       0))
     (equal (string-to-lofat fat32-in-memory str)
            (string-to-lofat (create-fat32-in-memory)
                                       str)))
    :hints
    (("goal"
      :use
      (string-to-lofat-correctness-1
       (:instance string-to-lofat-correctness-1
                  (fat32-in-memory (create-fat32-in-memory)))
       string-to-lofat-ignore-lemma-14)
      :cases
      ((equal
        (mv-nth 0
                (string-to-lofat fat32-in-memory str))
        (mv-nth
         0
         (string-to-lofat (create-fat32-in-memory)
                                    str)))))
     ("subgoal 2''"
      :use
      ((:functional-instance
        equal-by-nths
        (equal-by-nths-hyp
         (lambda
          nil
          (and
           (stringp str)
           (not (equal fat32-in-memory
                       (create-fat32-in-memory)))
           (fat32-in-memoryp fat32-in-memory)
           (equal
            (mv-nth
             1
             (string-to-lofat fat32-in-memory str))
            0)
           (equal
            (mv-nth
             1
             (string-to-lofat (create-fat32-in-memory)
                                        str))
            0))))
        (equal-by-nths-lhs
         (lambda
          nil
          (mv-nth
           0
           (string-to-lofat fat32-in-memory str))))
        (equal-by-nths-rhs
         (lambda
          nil
          (mv-nth
           0
           (string-to-lofat (create-fat32-in-memory)
                                      str))))))))))

(encapsulate
  ()

  (local
   (defthmd
     string-to-lofat-inversion-lemma-1
     (implies
      (and
       (stringp str)
       (fat32-in-memoryp fat32-in-memory)
       (equal
        (mv-nth 1
                (string-to-lofat (create-fat32-in-memory)
                                           str))
        0))
      (eqfat
       (lofat-to-string
        (mv-nth 0
                (string-to-lofat fat32-in-memory str)))
       str))
     :hints
     (("goal"
       :in-theory
       (e/d (eqfat)
            (create-fat32-in-memory
             (:rewrite string-to-lofat-ignore)
             (:rewrite lofat-to-string-inversion)))
       :cases ((equal fat32-in-memory
                      (create-fat32-in-memory)))
       :use
       ((:rewrite string-to-lofat-ignore)
        (:instance
         (:rewrite lofat-to-string-inversion)
         (fat32-in-memory
          (mv-nth
           0
           (string-to-lofat (create-fat32-in-memory)
                                      str))))
        (:instance
         (:rewrite string-to-lofat-ignore)
         (str
          (lofat-to-string
           (mv-nth
            0
            (string-to-lofat (create-fat32-in-memory)
                                       str))))
         (fat32-in-memory
          (mv-nth
           0
           (string-to-lofat (create-fat32-in-memory)
                                      str))))
        (:instance
         (:rewrite string-to-lofat-ignore-lemma-14)
         (str
          (lofat-to-string
           (mv-nth
            0
            (string-to-lofat (create-fat32-in-memory)
                                       str))))
         (fat32-in-memory
          (mv-nth
           0
           (string-to-lofat (create-fat32-in-memory)
                                      str)))))))))

  (defthm
    string-to-lofat-inversion
    (implies
     (and
      (stringp str)
      (fat32-in-memoryp fat32-in-memory)
      (equal
       (mv-nth 1
               (string-to-lofat fat32-in-memory str))
       0))
     (eqfat
      (lofat-to-string
       (mv-nth 0
               (string-to-lofat fat32-in-memory str)))
      str))
    :hints
    (("goal" :in-theory (e/d nil (create-fat32-in-memory))
      :use
      (string-to-lofat-ignore-lemma-14
       string-to-lofat-inversion-lemma-1)))))

(defthm
  hifat-to-string-inversion
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (m1-file-alist-p fs)
        (m1-bounded-file-alist-p fs)
        (m1-file-no-dups-p fs)
        (<= (m1-entry-count fs)
            (max-entry-count fat32-in-memory)))
   (b*
       (((mv fat32-in-memory error-code)
         (hifat-to-lofat fat32-in-memory fs)))
     (implies
      (zp error-code)
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat
         (mv-nth
          0
          (string-to-lofat
           fat32-in-memory
           (lofat-to-string fat32-in-memory)))))
       fs)))))

(encapsulate
  ()

  (local
   (defthmd
     string-to-hifat-inversion-lemma-1
     (implies
      (and
       (stringp str)
       (fat32-in-memoryp fat32-in-memory)
       (equal
        (mv-nth
         1
         (string-to-lofat
          (create-fat32-in-memory)
          (lofat-to-string
           (mv-nth
            0
            (hifat-to-lofat
             (mv-nth
              0
              (string-to-lofat fat32-in-memory str))
             (mv-nth 0
                     (lofat-to-hifat
                      (mv-nth 0
                              (string-to-lofat
                               fat32-in-memory str)))))))))
        0)
       (equal
        (mv-nth 1
                (string-to-lofat (create-fat32-in-memory)
                                           str))
        0)
       (equal
        (mv-nth
         1
         (lofat-to-hifat
          (mv-nth
           0
           (string-to-lofat fat32-in-memory str))))
        0)
       (m1-bounded-file-alist-p
        (mv-nth
         0
         (lofat-to-hifat
          (mv-nth
           0
           (string-to-lofat fat32-in-memory str)))))
       (m1-file-no-dups-p
        (mv-nth
         0
         (lofat-to-hifat
          (mv-nth
           0
           (string-to-lofat fat32-in-memory str)))))
       (equal
        (mv-nth
         1
         (hifat-to-lofat
          (mv-nth 0
                  (string-to-lofat fat32-in-memory str))
          (mv-nth
           0
           (lofat-to-hifat
            (mv-nth
             0
             (string-to-lofat fat32-in-memory str))))))
        0))
      (eqfat
       (lofat-to-string
        (mv-nth
         0
         (hifat-to-lofat
          (mv-nth 0
                  (string-to-lofat fat32-in-memory str))
          (mv-nth
           0
           (lofat-to-hifat
            (mv-nth
             0
             (string-to-lofat fat32-in-memory str)))))))
       str))
     :hints
     (("goal"
       :in-theory
       (e/d (eqfat)
            ((:rewrite lofat-to-string-inversion)
             (:rewrite string-to-lofat-ignore)))
       :use
       ((:instance
         (:rewrite lofat-to-string-inversion)
         (fat32-in-memory
          (mv-nth
           0
           (hifat-to-lofat
            (mv-nth
             0
             (string-to-lofat (create-fat32-in-memory)
                                        str))
            (mv-nth
             0
             (lofat-to-hifat
              (mv-nth
               0
               (string-to-lofat (create-fat32-in-memory)
                                          str))))))))
        (:instance
         (:rewrite string-to-lofat-ignore)
         (str
          (lofat-to-string
           (mv-nth
            0
            (hifat-to-lofat
             (mv-nth
              0
              (string-to-lofat (create-fat32-in-memory)
                                         str))
             (mv-nth
              0
              (lofat-to-hifat
               (mv-nth
                0
                (string-to-lofat (create-fat32-in-memory)
                                           str))))))))
         (fat32-in-memory
          (mv-nth
           0
           (hifat-to-lofat
            (mv-nth
             0
             (string-to-lofat (create-fat32-in-memory)
                                        str))
            (mv-nth
             0
             (lofat-to-hifat
              (mv-nth
               0
               (string-to-lofat (create-fat32-in-memory)
                                          str))))))))
        (:rewrite string-to-lofat-ignore))
       :cases ((equal fat32-in-memory
                      (create-fat32-in-memory)))))))

  (local
   (defthmd
     string-to-hifat-inversion-lemma-2
     (implies
      (and
       (stringp str)
       (fat32-in-memoryp fat32-in-memory)
       (equal
        (mv-nth
         1
         (string-to-lofat
          (mv-nth
           0
           (hifat-to-lofat
            (mv-nth
             0
             (string-to-lofat fat32-in-memory str))
            (mv-nth 0
                    (lofat-to-hifat
                     (mv-nth 0
                             (string-to-lofat
                              fat32-in-memory str))))))
          (lofat-to-string
           (mv-nth
            0
            (hifat-to-lofat
             (mv-nth
              0
              (string-to-lofat fat32-in-memory str))
             (mv-nth 0
                     (lofat-to-hifat
                      (mv-nth 0
                              (string-to-lofat
                               fat32-in-memory str)))))))))
        0)
       (equal
        (mv-nth 1
                (string-to-lofat fat32-in-memory
                                           str))
        0)
       (equal
        (mv-nth
         1
         (lofat-to-hifat
          (mv-nth
           0
           (string-to-lofat fat32-in-memory str))))
        0)
       (m1-bounded-file-alist-p
        (mv-nth
         0
         (lofat-to-hifat
          (mv-nth
           0
           (string-to-lofat fat32-in-memory str)))))
       (m1-file-no-dups-p
        (mv-nth
         0
         (lofat-to-hifat
          (mv-nth
           0
           (string-to-lofat fat32-in-memory str)))))
       (equal
        (mv-nth
         1
         (hifat-to-lofat
          (mv-nth 0
                  (string-to-lofat fat32-in-memory str))
          (mv-nth
           0
           (lofat-to-hifat
            (mv-nth
             0
             (string-to-lofat fat32-in-memory str))))))
        0))
      (eqfat
       (lofat-to-string
        (mv-nth
         0
         (hifat-to-lofat
          (mv-nth 0
                  (string-to-lofat fat32-in-memory str))
          (mv-nth
           0
           (lofat-to-hifat
            (mv-nth
             0
             (string-to-lofat fat32-in-memory str)))))))
       str))
     :hints
     (("goal"
       :use
       (string-to-hifat-inversion-lemma-1
        string-to-lofat-ignore-lemma-14
        (:instance
         (:rewrite string-to-lofat-ignore-lemma-14)
         (str
          (lofat-to-string
           (mv-nth
            0
            (hifat-to-lofat
             (mv-nth 0
                     (string-to-lofat fat32-in-memory str))
             (mv-nth 0
                     (lofat-to-hifat
                      (mv-nth 0
                              (string-to-lofat
                               fat32-in-memory str))))))))
         (fat32-in-memory
          (mv-nth
           0
           (hifat-to-lofat
            (mv-nth 0
                    (string-to-lofat fat32-in-memory str))
            (mv-nth
             0
             (lofat-to-hifat
              (mv-nth
               0
               (string-to-lofat fat32-in-memory str)))))))))))))

  ;; This was earlier named string-to-m1-fs-inversion.
  (defthm
    string-to-hifat-inversion
    (implies
     (and (stringp str)
          (fat32-in-memoryp fat32-in-memory))
     (b*
         (((mv fat32-in-memory error-code1)
           (string-to-lofat fat32-in-memory str))
          ((mv fs error-code2)
           (lofat-to-hifat fat32-in-memory)))
       (implies
        (and
         (equal error-code1 0)
         (equal error-code2 0)
         (m1-bounded-file-alist-p fs)
         (m1-file-no-dups-p fs)
         (equal
          (mv-nth 1
                  (hifat-to-lofat fat32-in-memory fs))
          0))
        (eqfat
         (lofat-to-string
          (mv-nth 0
                  (hifat-to-lofat fat32-in-memory fs)))
         str))))
    :hints
    (("goal"
      :in-theory
      (disable (:rewrite lofat-to-string-inversion))
      :use
      (string-to-hifat-inversion-lemma-2
       (:instance
        (:rewrite lofat-to-string-inversion)
        (fat32-in-memory
         (mv-nth
          0
          (hifat-to-lofat
           (mv-nth
            0
            (string-to-lofat fat32-in-memory str))
           (mv-nth
            0
            (lofat-to-hifat
             (mv-nth 0
                     (string-to-lofat
                      fat32-in-memory str)))))))))))))

#|
Some (rather awful) testing forms are
(b* (((mv contents &)
      (get-clusterchain-contents fat32-in-memory 2 *ms-max-dir-size*)))
  (get-dir-filenames fat32-in-memory contents *ms-max-dir-size*))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 *ms-max-dir-size*)))
  (lofat-to-hifat fat32-in-memory))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 *ms-max-dir-size*))
     (fs (lofat-to-hifat fat32-in-memory)))
  (hifat-open (list "INITRD  IMG")
           fs nil nil))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 *ms-max-dir-size*))
     (fs (lofat-to-hifat fat32-in-memory))
     ((mv fd-table file-table & &)
      (hifat-open (list "INITRD  IMG")
               fs nil nil)))
  (hifat-pread 0 6 49 fs fd-table file-table))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 *ms-max-dir-size*))
     (fs (lofat-to-hifat fat32-in-memory))
     ((mv fd-table file-table & &)
      (hifat-open (list "INITRD  IMG")
               fs nil nil)))
  (hifat-pwrite 0 "ornery" 49 fs fd-table file-table))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 *ms-max-dir-size*))
     (fs (lofat-to-hifat fat32-in-memory))
     ((mv fd-table file-table & &)
      (hifat-open (list "INITRD  IMG")
               fs nil nil))
     ((mv fs & &)
      (hifat-pwrite 0 "ornery" 49 fs fd-table file-table))
     ((mv fat32-in-memory dir-ent-list)
      (hifat-to-lofat-helper fat32-in-memory fs)))
  (mv fat32-in-memory dir-ent-list))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 *ms-max-dir-size*))
     (fs (lofat-to-hifat fat32-in-memory))
     ((mv fd-table file-table & &)
      (hifat-open (list "INITRD  IMG")
               fs nil nil))
     ((mv fs & &)
      (hifat-pwrite 0 "ornery" 49 fs fd-table file-table)))
  (hifat-to-lofat fat32-in-memory fs))
(time$
 (b*
     ((str (lofat-to-string
            fat32-in-memory))
      ((unless (and (stringp str)
                    (>= (length str) *initialbytcnt*)))
       (mv fat32-in-memory -1))
      ((mv fat32-in-memory error-code)
       (read-reserved-area fat32-in-memory str))
      ((unless (equal error-code 0))
       (mv fat32-in-memory "it was read-reserved-area"))
      (fat-read-size (/ (* (bpb_fatsz32 fat32-in-memory)
                           (bpb_bytspersec fat32-in-memory))
                        4))
      ((unless (integerp fat-read-size))
       (mv fat32-in-memory "it was fat-read-size"))
      (data-byte-count (* (count-of-clusters fat32-in-memory)
                          (cluster-size fat32-in-memory)))
      ((unless (> data-byte-count 0))
       (mv fat32-in-memory "it was data-byte-count"))
      (tmp_bytspersec (bpb_bytspersec fat32-in-memory))
      (tmp_init (* tmp_bytspersec
                   (+ (bpb_rsvdseccnt fat32-in-memory)
                      (* (bpb_numfats fat32-in-memory)
                         (bpb_fatsz32 fat32-in-memory)))))
      ((unless (>= (length str)
                   (+ tmp_init
                      (data-region-length fat32-in-memory))))
       (mv fat32-in-memory "it was (length str)"))
      (fat32-in-memory (resize-fat fat-read-size fat32-in-memory))
      (fat32-in-memory
       (update-fat fat32-in-memory
                   (subseq str
                           (* (bpb_rsvdseccnt fat32-in-memory)
                              (bpb_bytspersec fat32-in-memory))
                           (+ (* (bpb_rsvdseccnt fat32-in-memory)
                                 (bpb_bytspersec fat32-in-memory))
                              (* fat-read-size 4)))
                   fat-read-size))
      (fat32-in-memory
       (resize-data-region data-byte-count fat32-in-memory))
      (data-region-string
       (subseq str tmp_init
               (+ tmp_init
                  (data-region-length fat32-in-memory))))
      (fat32-in-memory
       (update-data-region fat32-in-memory data-region-string
                           (data-region-length fat32-in-memory)
                           0)))
   (mv fat32-in-memory error-code)))
(time$
 (b*
     (((mv channel state)
       (open-output-channel "test/disk2.raw" :character state))
      (state
         (princ$
          (lofat-to-string fat32-in-memory)
          channel state))
      (state
       (close-output-channel channel state)))
   (mv fat32-in-memory state)))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 *ms-max-dir-size*))
     (fs (lofat-to-hifat fat32-in-memory))
     ((mv fs & &)
      (hifat-mkdir fs (list "" "TMP        "))))
  (hifat-to-lofat fat32-in-memory fs))
|#

(defund lofat-file-contents-p (contents)
  (declare (xargs :guard t))
  (or (and (stringp contents)
           (unsigned-byte-p 32 (length contents)))
      (dir-ent-list-p contents)))

(defund lofat-file-contents-fix (contents)
  (declare (xargs :guard t))
  (if (lofat-file-contents-p contents)
      contents
    ""))

(defthm
  lofat-file-contents-fix-of-lofat-file-contents-fix
  (equal (lofat-file-contents-fix (lofat-file-contents-fix x))
         (lofat-file-contents-fix x))
  :hints (("goal" :in-theory (enable lofat-file-contents-fix))))

(fty::deffixtype lofat-file-contents
                 :pred lofat-file-contents-p
                 :fix lofat-file-contents-fix
                 :equiv lofat-file-contents-equiv
                 :define t)

(defthm
  lofat-file-contents-p-of-lofat-file-contents-fix
  (lofat-file-contents-p (lofat-file-contents-fix x))
  :hints (("goal" :in-theory (enable lofat-file-contents-fix
                                     lofat-file-contents-p))))

(defthm
  lofat-file-contents-fix-when-lofat-file-contents-p
  (implies (lofat-file-contents-p x)
           (equal (lofat-file-contents-fix x) x))
  :hints (("goal" :in-theory (enable lofat-file-contents-fix
                                     lofat-file-contents-p))))

(defthm
  lofat-file-contents-p-when-stringp
  (implies (stringp contents)
           (equal (lofat-file-contents-p contents)
                  (unsigned-byte-p 32 (length contents))))
  :hints (("goal" :in-theory (enable lofat-file-contents-p))))

(defthm lofat-file-contents-p-when-dir-ent-listp
  (implies (dir-ent-list-p contents)
           (lofat-file-contents-p contents))
  :hints (("goal" :in-theory (enable lofat-file-contents-p))))

(fty::defprod
 lofat-file
 ((dir-ent dir-ent-p :default (dir-ent-fix nil))
  (contents lofat-file-contents-p :default (lofat-file-contents-fix nil))))

(defund lofat-regular-file-p (file)
  (declare (xargs :guard t))
  (and (lofat-file-p file)
       (stringp (lofat-file->contents file))
       (unsigned-byte-p 32 (length (lofat-file->contents file)))))

(defund lofat-directory-file-p (file)
  (declare (xargs :guard t))
  (and (lofat-file-p file)
       (dir-ent-list-p (lofat-file->contents file))))

(defthm
  lofat-regular-file-p-correctness-1
  (implies
   (dir-ent-list-p contents)
   (not (lofat-regular-file-p (lofat-file dir-ent contents))))
  :hints (("goal" :in-theory (enable lofat-regular-file-p))))

(defthm
  lofat-directory-file-p-correctness-1
  (implies
   (stringp contents)
   (not (lofat-directory-file-p (lofat-file dir-ent contents))))
  :hints (("goal" :in-theory (enable lofat-directory-file-p))))

(defun lofat-statfs (fat32-in-memory)
  (declare (xargs :stobjs (fat32-in-memory)
                  :verify-guards nil))
  (b*
      ((total_blocks (count-of-clusters fat32-in-memory))
       (available_blocks
        (len (stobj-find-n-free-clusters
              fat32-in-memory
              (count-of-clusters fat32-in-memory)))))
    (make-struct-statfs
     :f_type *S_MAGIC_FUSEBLK*
     :f_bsize (cluster-size fat32-in-memory)
     :f_blocks total_blocks
     :f_bfree available_blocks
     :f_bavail available_blocks
     :f_files 0
     :f_ffree 0
     :f_fsid 0
     :f_namelen 72)))

(defun
  find-dir-ent (dir-ent-list filename)
  (declare (xargs :guard (and (fat32-filename-p filename)
                              (dir-ent-list-p dir-ent-list))))
  (b* (((when (atom dir-ent-list))
        (mv (dir-ent-fix nil) *enoent*))
       (dir-ent (mbe :exec (car dir-ent-list)
                     :logic (dir-ent-fix (car dir-ent-list))))
       ((when (equal (dir-ent-filename dir-ent)
                     filename))
        (mv dir-ent 0)))
    (find-dir-ent (cdr dir-ent-list)
                  filename)))

(defthm
  find-dir-ent-correctness-1
  (and
   (dir-ent-p (mv-nth 0 (find-dir-ent dir-ent-list filename)))
   (natp (mv-nth 1
                 (find-dir-ent dir-ent-list filename))))
  :hints (("goal" :induct (find-dir-ent dir-ent-list filename)))
  :rule-classes
  ((:rewrite
    :corollary
    (dir-ent-p (mv-nth 0
                       (find-dir-ent dir-ent-list filename))))
   (:type-prescription
    :corollary
    (natp (mv-nth 1
                  (find-dir-ent dir-ent-list filename))))))

(defthm
  find-dir-ent-correctness-2
  (implies
   (not (equal (mv-nth 1 (find-dir-ent dir-ent-list filename))
               0))
   (equal (mv-nth 1 (find-dir-ent dir-ent-list filename))
          *enoent*)))

(defun lofat-find-file-by-pathname (fat32-in-memory dir-ent-list pathname)
  (declare (xargs :guard (and (lofat-fs-p fat32-in-memory)
                              (fat32-filename-list-p pathname)
                              (useful-dir-ent-list-p dir-ent-list))
                  :measure (acl2-count pathname)
                  :stobjs fat32-in-memory))
  (b* (((unless (consp pathname))
        (mv (make-lofat-file) *enoent*))
       (name (fat32-filename-fix (car pathname)))
       ((mv dir-ent error-code) (find-dir-ent dir-ent-list name))
       ((unless (equal error-code 0))
        (mv (make-lofat-file) error-code))
       (first-cluster (dir-ent-first-cluster dir-ent))
       (directory-p
        (dir-ent-directory-p dir-ent))
       (length (if directory-p
                   *ms-max-dir-size*
                 (dir-ent-file-size dir-ent)))
       ((mv contents &)
        (if
            (or (< first-cluster
                   *ms-first-data-cluster*)
                (>=
                 first-cluster
                 (+ (count-of-clusters fat32-in-memory)
                    *ms-first-data-cluster*)))
            (mv "" 0)
          (get-clusterchain-contents fat32-in-memory
                                     first-cluster
                                     length)))
       ((unless directory-p)
        (if (consp (cdr pathname))
            (mv (make-lofat-file) *enotdir*)
          (mv (make-lofat-file :dir-ent dir-ent :contents contents) 0)))
       ((when (atom (cdr pathname)))
        (mv
         (make-lofat-file :dir-ent dir-ent
                          :contents (make-dir-ent-list
                                     (string=>nats contents)))
         0)))
    (lofat-find-file-by-pathname
     fat32-in-memory
     (make-dir-ent-list (string=>nats contents))
     (cdr pathname))))

;; The dir-ent-list-p hypothesis is only there because
;; lofat-to-hifat-helper doesn't fix its arguments. Should it?
(defthm
  lofat-find-file-by-pathname-correctness-1-lemma-1
  (implies
   (and (dir-ent-list-p dir-ent-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper
                        fat32-in-memory
                        dir-ent-list entry-limit))
               0))
   (iff
    (consp
     (assoc-equal name
                  (mv-nth 0
                          (lofat-to-hifat-helper
                           fat32-in-memory
                           dir-ent-list entry-limit))))
    (equal (mv-nth 1 (find-dir-ent dir-ent-list name))
           0)))
  :hints
  (("goal"
    :in-theory (enable lofat-to-hifat-helper))))

(defthm
  lofat-find-file-by-pathname-correctness-1-lemma-2
  (implies
   (and
    (useful-dir-ent-list-p dir-ent-list)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32-in-memory
                                                    dir-ent-list entry-limit))
           0))
   (equal
    (m1-file->dir-ent
     (cdr
      (assoc-equal
       name
       (mv-nth 0
               (lofat-to-hifat-helper fat32-in-memory
                                                dir-ent-list entry-limit)))))
    (mv-nth 0 (find-dir-ent dir-ent-list name))))
  :hints (("goal" :in-theory (enable lofat-to-hifat-helper))))

(defthm
  lofat-find-file-by-pathname-correctness-1-lemma-3
  (implies
   (and
    (equal (mv-nth 1 (find-dir-ent dir-ent-list name))
           0)
    (useful-dir-ent-list-p dir-ent-list)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper
                    fat32-in-memory
                    dir-ent-list entry-limit))
           0)
    (not (dir-ent-directory-p
          (mv-nth 0 (find-dir-ent dir-ent-list name))))
    (or (< (dir-ent-first-cluster
            (mv-nth 0 (find-dir-ent dir-ent-list name)))
           2)
        (<= (+ 2 (count-of-clusters fat32-in-memory))
            (dir-ent-first-cluster
             (mv-nth 0 (find-dir-ent dir-ent-list name))))))
   (equal
    (cdr (assoc-equal name
                      (mv-nth 0
                              (lofat-to-hifat-helper
                               fat32-in-memory
                               dir-ent-list entry-limit))))
    (make-m1-file
     :contents ""
     :dir-ent (mv-nth 0 (find-dir-ent dir-ent-list name)))))
  :hints
  (("goal"
    :in-theory (enable lofat-to-hifat-helper))))

(defthm
  lofat-find-file-by-pathname-correctness-1-lemma-4
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (useful-dir-ent-list-p dir-ent-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper
                        fat32-in-memory
                        dir-ent-list entry-limit))
               0)
        (not (dir-ent-directory-p
              (mv-nth 0 (find-dir-ent dir-ent-list name))))
        (<= 2
            (dir-ent-first-cluster
             (mv-nth 0 (find-dir-ent dir-ent-list name))))
        (< (dir-ent-first-cluster
            (mv-nth 0 (find-dir-ent dir-ent-list name)))
           (+ 2 (count-of-clusters fat32-in-memory))))
   (equal
    (cdr (assoc-equal name
                      (mv-nth 0
                              (lofat-to-hifat-helper
                               fat32-in-memory
                               dir-ent-list entry-limit))))
    (make-m1-file
     :contents
     (mv-nth
      0
      (get-clusterchain-contents
       fat32-in-memory
       (dir-ent-first-cluster
        (mv-nth 0 (find-dir-ent dir-ent-list name)))
       (dir-ent-file-size
        (mv-nth 0 (find-dir-ent dir-ent-list name)))))
     :dir-ent (mv-nth 0 (find-dir-ent dir-ent-list name)))))
  :hints
  (("goal"
    :in-theory (enable lofat-to-hifat-helper))))

(defthm
  lofat-find-file-by-pathname-correctness-1-lemma-5
  (implies
   (and (useful-dir-ent-list-p dir-ent-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper
                        fat32-in-memory
                        dir-ent-list entry-limit))
               0))
   (iff
    (m1-directory-file-p
     (cdr
      (assoc-equal name
                   (mv-nth 0
                           (lofat-to-hifat-helper
                            fat32-in-memory
                            dir-ent-list entry-limit)))))
    (dir-ent-directory-p
     (mv-nth 0
             (find-dir-ent dir-ent-list name)))))
  :hints
  (("goal" :in-theory (enable lofat-to-hifat-helper
                              m1-directory-file-p))))

(defthm
  lofat-find-file-by-pathname-correctness-1-lemma-6
  (implies
   (and (dir-ent-directory-p
         (mv-nth 0 (find-dir-ent dir-ent-list name)))
        (<= 2
            (dir-ent-first-cluster
             (mv-nth 0 (find-dir-ent dir-ent-list name))))
        (< (dir-ent-first-cluster
            (mv-nth 0 (find-dir-ent dir-ent-list name)))
           (+ 2 (count-of-clusters fat32-in-memory)))
        (useful-dir-ent-list-p dir-ent-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper
                        fat32-in-memory
                        dir-ent-list entry-limit))
               0))
   (equal
    (mv-nth
     3
     (lofat-to-hifat-helper
      fat32-in-memory
      (make-dir-ent-list
       (string=>nats
        (mv-nth
         0
         (get-clusterchain-contents
          fat32-in-memory
          (dir-ent-first-cluster
           (mv-nth 0 (find-dir-ent dir-ent-list name)))
          2097152))))
      entry-limit))
    0))
  :hints
  (("goal" :in-theory
    (enable lofat-to-hifat-helper-correctness-4
            lofat-to-hifat-helper))))

(defthm
  lofat-find-file-by-pathname-correctness-1-lemma-7
  (implies
   (and (dir-ent-directory-p
         (mv-nth 0 (find-dir-ent dir-ent-list name)))
        (<= 2
            (dir-ent-first-cluster
             (mv-nth 0 (find-dir-ent dir-ent-list name))))
        (< (dir-ent-first-cluster
            (mv-nth 0 (find-dir-ent dir-ent-list name)))
           (+ 2 (count-of-clusters fat32-in-memory)))
        (useful-dir-ent-list-p dir-ent-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper
                        fat32-in-memory
                        dir-ent-list entry-limit))
               0))
   (equal
    (cdr (assoc-equal name
                      (mv-nth 0
                              (lofat-to-hifat-helper
                               fat32-in-memory
                               dir-ent-list entry-limit))))
    (make-m1-file
     :dir-ent (mv-nth 0 (find-dir-ent dir-ent-list name))
     :contents
     (mv-nth
      0
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (string=>nats
         (mv-nth
          0
          (get-clusterchain-contents
           fat32-in-memory
           (dir-ent-first-cluster
            (mv-nth 0 (find-dir-ent dir-ent-list name)))
           2097152))))
       entry-limit)))))
  :hints
  (("goal"
    :in-theory
    (enable lofat-to-hifat-helper-correctness-4)
    :induct (find-dir-ent dir-ent-list name)
    :expand (lofat-to-hifat-helper
             fat32-in-memory
             dir-ent-list entry-limit))))

(defthm
  lofat-find-file-by-pathname-correctness-1-lemma-8
  (implies
   (and
    (dir-ent-directory-p
     (mv-nth 0 (find-dir-ent dir-ent-list name)))
    (not
     (and (<= 2
              (dir-ent-first-cluster
               (mv-nth 0 (find-dir-ent dir-ent-list name))))
          (< (dir-ent-first-cluster
              (mv-nth 0 (find-dir-ent dir-ent-list name)))
             (+ 2
                (count-of-clusters fat32-in-memory)))))
    (useful-dir-ent-list-p dir-ent-list)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper
                    fat32-in-memory
                    dir-ent-list entry-limit))
           0))
   (equal
    (cdr (assoc-equal name
                      (mv-nth 0
                              (lofat-to-hifat-helper
                               fat32-in-memory
                               dir-ent-list entry-limit))))
    (make-m1-file
     :dir-ent (mv-nth 0 (find-dir-ent dir-ent-list name))
     :contents nil)))
  :hints
  (("goal"
    :in-theory
    (enable lofat-to-hifat-helper-correctness-4)
    :induct (find-dir-ent dir-ent-list name)
    :expand
    ((lofat-to-hifat-helper fat32-in-memory
                                      dir-ent-list entry-limit)
     (lofat-to-hifat-helper
      fat32-in-memory
      nil (+ -1 entry-limit))))))

(defthm
  lofat-find-file-by-pathname-correctness-1
  (b*
      (((mv file error-code)
        (find-file-by-pathname
         (mv-nth 0
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  dir-ent-list entry-limit))
         pathname)))
    (implies
     (and
      (lofat-fs-p fat32-in-memory)
      (useful-dir-ent-list-p dir-ent-list)
      (equal (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32-in-memory
                      dir-ent-list entry-limit))
             0)
      (lofat-regular-file-p
       (mv-nth
        0
        (lofat-find-file-by-pathname fat32-in-memory
                                     dir-ent-list pathname))))
     (equal (lofat-find-file-by-pathname
             fat32-in-memory dir-ent-list pathname)
            (mv (make-lofat-file :contents (m1-file->contents file)
                                 :dir-ent (m1-file->dir-ent file))
                error-code)))))

(defthm
  lofat-find-file-by-pathname-correctness-2
  (b*
      (((mv file error-code)
        (find-file-by-pathname
         (mv-nth 0
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  dir-ent-list entry-limit))
         pathname)))
    (implies
     (and
      (lofat-fs-p fat32-in-memory)
      (useful-dir-ent-list-p dir-ent-list)
      (equal (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32-in-memory
                      dir-ent-list entry-limit))
             0)
      (lofat-directory-file-p
       (mv-nth
        0
        (lofat-find-file-by-pathname fat32-in-memory
                                     dir-ent-list pathname))))
     (and
      (equal
       (lofat-file->dir-ent
        (mv-nth 0
                (lofat-find-file-by-pathname
                 fat32-in-memory dir-ent-list pathname)))
       (m1-file->dir-ent file))
      (equal
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32-in-memory
         (lofat-file->contents
          (mv-nth 0
                  (lofat-find-file-by-pathname
                   fat32-in-memory dir-ent-list pathname)))
         entry-limit))
       (m1-file->contents file))
      (equal
       (mv-nth 1
               (lofat-find-file-by-pathname
                fat32-in-memory dir-ent-list pathname))
       error-code))))
  :hints
  (("goal"
    :induct
    (mv (mv-nth 0
                (find-file-by-pathname
                 (mv-nth 0
                         (lofat-to-hifat-helper
                          fat32-in-memory
                          dir-ent-list entry-limit))
                 pathname))
        (mv-nth 0
                (lofat-find-file-by-pathname
                 fat32-in-memory dir-ent-list pathname)))
    :expand (lofat-to-hifat-helper
             fat32-in-memory nil entry-limit))))

(defthm
  lofat-find-file-by-pathname-correctness-3
  (lofat-file-p
   (mv-nth 0
           (lofat-find-file-by-pathname
            fat32-in-memory dir-ent-list pathname))))

;; This needs some revision... obviously, we don't want to be staring into the
;; computation to get the root directory's directory entries here.
(defun lofat-open (pathname fat32-in-memory fd-table file-table)
  (declare (xargs :guard (and (lofat-fs-p fat32-in-memory)
                              (fat32-filename-list-p pathname)
                              (fd-table-p fd-table)
                              (file-table-p file-table))
                  :stobjs fat32-in-memory))
  (b*
      ((fd-table (fd-table-fix fd-table))
       (file-table (file-table-fix file-table))
       ((mv root-contents &)
        (get-clusterchain-contents
         fat32-in-memory
         (fat32-entry-mask (bpb_rootclus fat32-in-memory))
         2097152))
       ((mv & errno)
        (lofat-find-file-by-pathname
         fat32-in-memory
         (make-dir-ent-list
          (string=>nats
           root-contents))
         pathname))
       ((unless (equal errno 0))
        (mv fd-table file-table -1 errno))
       (file-table-index
        (find-new-index (strip-cars file-table)))
       (fd-table-index
        (find-new-index (strip-cars fd-table))))
    (mv
     (cons
      (cons fd-table-index file-table-index)
      fd-table)
     (cons
      (cons file-table-index (make-file-table-element :pos 0 :fid pathname))
      file-table)
     fd-table-index 0)))

;; This needs some revision... obviously, we don't want to be staring into the
;; computation to get the root directory's directory entries here.
(defun
  lofat-pread
  (fd count offset fat32-in-memory fd-table file-table)
  (declare (xargs :guard (and (natp fd)
                              (natp count)
                              (natp offset)
                              (fd-table-p fd-table)
                              (file-table-p file-table)
                              (lofat-fs-p fat32-in-memory))
                  :stobjs fat32-in-memory))
  (b*
      ((fd-table-entry (assoc-equal fd fd-table))
       ((unless (consp fd-table-entry))
        (mv "" -1 *ebadf*))
       (file-table-entry (assoc-equal (cdr fd-table-entry)
                                      file-table))
       ((unless (consp file-table-entry))
        (mv "" -1 *ebadf*))
       (pathname (file-table-element->fid (cdr file-table-entry)))
       ((mv root-contents &)
        (get-clusterchain-contents
         fat32-in-memory
         (fat32-entry-mask (bpb_rootclus fat32-in-memory))
         2097152))
       ((mv file-contents error-code)
        (lofat-find-file-by-pathname
         fat32-in-memory
         (make-dir-ent-list
          (string=>nats
           root-contents))
         pathname))
       ((unless (and (equal error-code 0)
                     (stringp file-contents)))
        (mv "" -1 error-code))
       (new-offset (min (+ offset count)
                        (length file-contents)))
       (buf (subseq file-contents
                    (min offset
                         (length file-contents))
                    new-offset)))
    (mv buf (length buf) 0)))

(defun lofat-lstat (fat32-in-memory pathname)
  (declare (xargs :guard (and (lofat-fs-p fat32-in-memory)
                              (fat32-filename-list-p pathname))
                  :stobjs fat32-in-memory))
  (b*
      (((mv root-contents &)
        (get-clusterchain-contents
         fat32-in-memory
         (fat32-entry-mask (bpb_rootclus fat32-in-memory))
         2097152))
       ((mv file errno)
        (lofat-find-file-by-pathname
         fat32-in-memory
         (make-dir-ent-list
          (string=>nats
           root-contents))
         pathname))
       ((when (not (equal errno 0)))
        (mv (make-struct-stat) -1 errno)))
    (mv
       (make-struct-stat
        :st_size (dir-ent-file-size
                  (lofat-file->dir-ent file)))
       0 0)))
