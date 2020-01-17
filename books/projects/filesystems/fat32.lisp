(in-package "ACL2")

;  fat32.lisp                                  Mihir Mehta

; Utilities for FAT32.

;; In commit e1d2e33807c4c529d2c7b1eb7d481f466e7a7d67 there's a (successful)
;; attempt to remove the non-local inclusion of this book. Ultimately, though,
;; this commit was rolled back since the redundant redefinition of logapp,
;; loghead, logtail, imod, ifloor and expt2 is deemed excessively
;; cumbersome. This is part of our theory now.
(include-book "ihs/logops-lemmas" :dir :system)

(include-book "centaur/fty/top" :dir :system)

(include-book "file-system-lemmas")
(include-book "bounded-nat-listp")

(defconst *expt-2-28* (expt 2 28))

;; from page 18 of the FAT specification
(defconst *ms-end-of-clusterchain* (- *expt-2-28* 1))

;; from page 14 of the FAT specification
(defconst *ms-first-data-cluster* 2)

;; from page 18 of the FAT specification
(defconst *ms-bad-cluster* 268435447)

;; from page 15 of the FAT specification
(defconst *ms-min-count-of-clusters* 65525)

;; from page 9 of the FAT specification
(defconst *ms-min-bytes-per-sector* 512)

;; inferred - there can be as few as one sectors in a cluster
(defconst *ms-min-data-region-size* (* *ms-min-bytes-per-sector*
                                       1
                                       *ms-min-count-of-clusters*))

(defconst *ms-max-bytes-per-sector* 4096)

;; inferred - there can be as many as 128 sectors in a cluster
(defconst *ms-max-data-region-size* (* *ms-max-bytes-per-sector*
                                       128
                                       (- *ms-bad-cluster* 2)))

(defconst *ms-dir-ent-length* 32)

;; observed
(defconst *current-dir-fat32-name* ".          ")
(defconst *parent-dir-fat32-name* "..         ")

;; This has not really been observed to be any FAT32 entry's name. In fact, it
;; cannot be, since the FAT specification says that the filesystem's root
;; directory does not have "." and ".." entries, and those entries would have
;; different names even if they existed. Still, this is what our
;; name-to-fat32-name function computes when passed the empty string - and that
;; in turn happens with the empty string preceding the first slash in "/home"
;; or "/vmlinuz".
(defconst *empty-fat32-name* "           ")

;; known
(defconst *current-dir-name* ".")
(defconst *parent-dir-name* "..")

;; Page 36 of the FAT specification states that a directory shouldn't have more
;; than 65536 entries. However, *ms-max-dir-ent-count* below is used for the
;; definition of hifat-bounded-file-alist-p, and since that's applicable to our
;; internal representation of the filesystem, we need to leave room for two
;; entries (dot and dotdot) to be added when we store a directory in the stobj
;; representation. However, *ms-max-dir-size* is applicable to extracting
;; directory contents from the disk, and therefore it needs to be 2097152 as
;; stipulated.
(defconst *ms-max-dir-ent-count* (- (ash 1 16) 2))
(defconst *ms-max-dir-size* (ash 1 21))

;; from include/uapi/asm-generic/errno-base.h in the linux kernel sources
(defconst *ENOENT* 2) ;; No such file or directory
(defconst *EIO* 5) ;; I/O error
(defconst *EBADF* 9) ;; Bad file number
(defconst *EEXIST* 17) ;; File exists
(defconst *ENOTDIR* 20)	;; Not a directory
(defconst *EISDIR* 21) ;; Is a directory
(defconst *ENOSPC* 28) ;; No space left on device
(defconst *ENAMETOOLONG* 36) ;; File name too long

;; from the stat code in the coreutils sources
(defconst *S_MAGIC_FUSEBLK* #x65735546)

(encapsulate
  ()

  (local
   (include-book "arithmetic/top-with-meta" :dir :system))

  (local
   (defun induction-scheme (bits x)
     (if (zp bits)
         x
       (induction-scheme (- bits 1)
                         (logcdr x)))))

  (defthmd
    unsigned-byte-p-alt
    (implies (natp bits)
             (equal (unsigned-byte-p bits x)
                    (and (unsigned-byte-p (+ bits 1) x)
                         (zp (logand (ash 1 bits) x)))))
    :hints
    (("goal" :in-theory (e/d nil (logand ash logcar logcdr)
                             (logand* ash*))
      :induct (induction-scheme bits x)))))

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm
    logand-ash-lemma-1
    (implies (and (natp c))
             (unsigned-byte-p c (logand i (- (ash 1 c) 1))))))

(defund fat32-entry-p (x)
  (declare (xargs :guard t))
  (unsigned-byte-p 32 x))

(defund fat32-masked-entry-p (x)
  (declare (xargs :guard t))
  (unsigned-byte-p 28 x))

;; 0 is chosen as the default value based on this comment from Microsoft's FAT
;; overview:
;; The only time that the high 4 bits of FAT32 FAT entries should ever be
;; changed is when the volume is formatted, at which time the whole 32-bit FAT
;; entry should be zeroed, including the high 4 bits.
(defund fat32-entry-fix (x)
  (declare (xargs :guard t))
  (if (fat32-entry-p x)
      x 0))

(defund fat32-masked-entry-fix (x)
  (declare (xargs :guard t))
  (if (fat32-masked-entry-p x)
      x 0))

(in-theory (enable fat32-entry-p fat32-entry-fix fat32-masked-entry-p fat32-masked-entry-fix))

(defthm fat32-masked-entry-p-correctness-1
  (implies (fat32-masked-entry-p x)
           (natp x))
  :rule-classes :forward-chaining)

(defthm fat32-entry-fix-when-fat32-entry-p
  (implies (fat32-entry-p x)
           (equal (fat32-entry-fix x) x))
  :hints (("Goal" :in-theory (enable fat32-entry-fix))))

(defthm fat32-masked-entry-fix-when-fat32-masked-entry-p
  (implies (fat32-masked-entry-p x)
           (equal (fat32-masked-entry-fix x) x))
  :hints (("Goal" :in-theory (enable fat32-masked-entry-fix))))

(defthm
  fat32-entry-fix-correctness-1
  (and (<= 0 (fat32-entry-fix x))
       (< (fat32-entry-fix x) (ash 1 32))
       (integerp (fat32-entry-fix x)))
  :rule-classes
  ((:linear
    :corollary
    (and (<= 0 (fat32-entry-fix x))
         (< (fat32-entry-fix x) (ash 1 32))))
   (:type-prescription
    :corollary
    (integerp (fat32-entry-fix x))))
  :hints
  (("goal" :in-theory (enable fat32-entry-fix fat32-entry-p))))

;; Use a mask to take the low 28 bits.
(defund fat32-entry-mask (x)
  (declare (xargs :guard (fat32-entry-p x)))
  (loghead 28 x))

(defthm
  fat32-entry-mask-correctness-1
  (fat32-masked-entry-p (fat32-entry-mask x))
  :hints (("goal" :in-theory (e/d (fat32-entry-mask fat32-masked-entry-p)
                                  (unsigned-byte-p logand-ash-lemma-1))
           :use (:instance logand-ash-lemma-1 (c 28)
                           (i x)))))

(fty::deffixtype fat32-entry
                 :pred   fat32-entry-p
                 :fix    fat32-entry-fix
                 :equiv  fat32-entry-equiv
                 :define t
                 :forward t)

(fty::deffixtype fat32-masked-entry
                 :pred   fat32-masked-entry-p
                 :fix    fat32-masked-entry-fix
                 :equiv  fat32-masked-entry-equiv
                 :define t
                 :forward t)

(fty::deflist fat32-entry-list :elt-type fat32-entry-p :true-listp t)

(fty::deflist fat32-masked-entry-list :elt-type fat32-masked-entry-p :true-listp t)

(defthm nat-listp-if-fat32-masked-entry-list-p
  (implies (fat32-masked-entry-list-p x)
           (nat-listp x))
  :rule-classes (:forward-chaining :rewrite))

(in-theory (disable fat32-entry-p fat32-entry-fix fat32-masked-entry-p fat32-masked-entry-fix))

(defthm member-of-fat32-entry-list
  (implies (and (member-equal x lst)
                (fat32-entry-list-p lst))
           (fat32-entry-p x)))

(defthm
  fat32-masked-entry-list-p-of-make-list-ac
  (implies (and (fat32-masked-entry-p val)
                (fat32-masked-entry-list-p ac))
           (fat32-masked-entry-list-p (make-list-ac n val ac))))

(defthm fat32-masked-entry-list-p-of-append
  (equal (fat32-masked-entry-list-p (binary-append x y))
         (and (fat32-masked-entry-list-p (true-list-fix x))
              (fat32-masked-entry-list-p y))))

(defthm fat32-masked-entry-list-p-of-true-list-fix
  (implies
   (fat32-masked-entry-list-p x)
   (fat32-masked-entry-list-p (true-list-fix x))))

(defthm fat32-entry-list-p-of-update-nth
  (implies
   (fat32-entry-list-p l)
   (equal (fat32-entry-list-p (update-nth key val l))
          (and (<= (nfix key) (len l))
               (fat32-entry-p val)))))

(defthm fat32-entry-list-p-of-revappend
  (equal (fat32-entry-list-p (revappend x y))
         (and (fat32-entry-list-p y)
              (fat32-entry-list-p (list-fix x)))))

(defthm fat32-entry-list-of-nthcdr
  (implies (fat32-entry-list-p l)
           (fat32-entry-list-p (nthcdr n l))))

(defthm
  fat32-masked-entry-p-of-nth-when-fat32-masked-entry-list-p
  (implies (fat32-masked-entry-list-p l)
           (iff (fat32-masked-entry-p (nth n l))
                (< (nfix n) (len l))))
  :rule-classes
  ((:rewrite
    :corollary (implies (fat32-masked-entry-list-p l)
                        (equal (fat32-masked-entry-p (nth n l))
                               (< (nfix n) (len l)))))))

(encapsulate
  ()

  (local
   (defthm fat32-entry-list-p-of-first-n-ac-lemma-1
     (implies (not (fat32-entry-list-p (true-list-fix ac)))
              (not (fat32-entry-list-p (first-n-ac i l ac))))))

  (defthm
    fat32-entry-list-p-of-first-n-ac
    (implies (fat32-entry-list-p l)
             (equal (fat32-entry-list-p (first-n-ac n l ac))
                    (and (fat32-entry-list-p (true-list-fix ac))
                         (<= (nfix n) (len l)))))))

(defthm
  fat32-entry-list-p-of-take
  (implies (fat32-entry-list-p l)
           (equal (fat32-entry-list-p (take n l))
                  (<= (nfix n) (len l)))))

(defthm fat32-entry-list-p-of-repeat
  (implies (fat32-entry-p x)
           (fat32-entry-list-p (repeat n x)))
  :hints (("goal" :in-theory (enable repeat))))

(defthm
  fat32-entry-list-p-of-resize-list
  (implies
   (and (fat32-entry-list-p lst)
        (fat32-entry-p default-value))
   (fat32-entry-list-p (resize-list lst n default-value))))

(defthm natp-when-fat32-entry-p
  (implies (fat32-entry-p x) (natp x))
  :hints (("goal" :in-theory (enable fat32-entry-p)))
  :rule-classes :forward-chaining)

(encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (local
   (defthm fat32-entry-p-of-nth-lemma-1
     (equal (< (+ -1 n) (len (cdr l)))
            (< n (+ 1 (len (cdr l)))))))

  (defthm fat32-entry-p-of-nth
    (implies (fat32-entry-list-p l)
             (equal (fat32-entry-p (nth n l))
                    (< (nfix n) (len l))))
    :hints (("Goal" :in-theory (disable nth-when->=-n-len-l)))))

(defund
  fat32-update-lower-28
  (entry masked-entry)
  (declare
   (xargs
    :guard-hints
    (("goal"
      :in-theory (enable fat32-entry-p fat32-masked-entry-p)))
    :guard (and (fat32-entry-p entry)
                (fat32-masked-entry-p masked-entry))))
  (logapp 28 masked-entry
          (logtail 28
                   (mbe :exec entry
                        :logic (fat32-entry-fix entry)))))

(defthm
  fat32-update-lower-28-correctness-1
  (implies (fat32-masked-entry-p masked-entry)
           (fat32-entry-p (fat32-update-lower-28 entry masked-entry)))
  :hints (("goal" :in-theory (e/d (fat32-update-lower-28 fat32-entry-p)
                                  (logapp logtail))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (fat32-masked-entry-p masked-entry)
             (unsigned-byte-p 32
                              (fat32-update-lower-28 entry masked-entry)))
    :hints (("goal" :in-theory (enable fat32-entry-p))))))

(defthm
  fat32-entry-mask-of-fat32-update-lower-28
  (implies
   (fat32-masked-entry-p masked-entry)
   (equal (fat32-entry-mask (fat32-update-lower-28 entry masked-entry))
          masked-entry))
  :hints
  (("goal" :in-theory
    (e/d (fat32-update-lower-28 fat32-entry-mask fat32-masked-entry-p)
         (unsigned-byte-p loghead logapp)))))

(defthm
  fat32-update-lower-28-of-fat32-update-lower-28
  (implies
   (fat32-masked-entry-p masked-entry1)
   (equal (fat32-update-lower-28 (fat32-update-lower-28 entry masked-entry1)
                                 masked-entry2)
          (fat32-update-lower-28 entry masked-entry2)))
  :hints
  (("goal"
    :in-theory (e/d (fat32-update-lower-28)
                    (logapp logtail
                            (:rewrite fat32-update-lower-28-correctness-1
                                      . 1)))
    :use (:instance (:rewrite fat32-update-lower-28-correctness-1 . 1)
                    (masked-entry masked-entry1)
                    (entry entry)))))

(defthmd
  fat32-update-lower-28-of-fat32-entry-mask
  (implies (and (fat32-entry-p entry)
                (equal masked-entry (fat32-entry-mask entry)))
           (equal (fat32-update-lower-28 entry masked-entry)
                  entry))
  :hints
  (("goal"
    :in-theory (e/d (fat32-update-lower-28 fat32-entry-mask)
                    (logapp loghead logtail)))))

;; This is taken from page 18 of the fat specification.
(defund fat32-is-eof (fat-content)
  (declare (xargs :guard (fat32-masked-entry-p fat-content)
                  :guard-hints (("Goal'" :in-theory (enable fat32-masked-entry-p)))))
  (>= fat-content #xFFFFFF8))

(defthm fat32-is-eof-correctness-1
  (implies (< fat-content *ms-bad-cluster*)
           (not (fat32-is-eof fat-content)))
  :hints (("Goal" :in-theory (enable fat32-is-eof)) ))

(defund
  fat32-build-index-list
  (fa-table masked-current-cluster
            length cluster-size)
  (declare
   (xargs
    :measure (nfix length)
    :guard (and (fat32-entry-list-p fa-table)
                (fat32-masked-entry-p masked-current-cluster)
                (natp length)
                (>= masked-current-cluster
                    *ms-first-data-cluster*)
                (< masked-current-cluster (len fa-table))
                (integerp cluster-size)
                (> cluster-size 0))))
  (b*
      (((when (or (zp length) (zp cluster-size)))
        ;; This represents a problem case because masked-current-cluster is a
        ;; valid non-free cluster, but the length is 0. This loosely
        ;; corresponds to the infinite loop protection in the function
        ;; fs/fat/cache.c:fat_get_cluster.
        (mv nil (- *eio*)))
       (masked-next-cluster
        (fat32-entry-mask (nth masked-current-cluster fa-table)))
       ((when (< masked-next-cluster
                 *ms-first-data-cluster*))
        (mv (list masked-current-cluster)
            (- *eio*)))
       ((when (or (fat32-is-eof masked-next-cluster)
                  (>= masked-next-cluster (len fa-table))))
        (mv (list masked-current-cluster) 0))
       ((mv tail-index-list tail-error)
        (fat32-build-index-list fa-table masked-next-cluster
                                (nfix (- length cluster-size))
                                cluster-size)))
    (mv (list* masked-current-cluster tail-index-list)
        tail-error)))

(defthm bounded-nat-listp-of-fat32-build-index-list
  (implies (and (equal b (len fa-table))
                (fat32-masked-entry-p masked-current-cluster)
                (< masked-current-cluster (len fa-table)))
           (b* (((mv index-list &)
                 (fat32-build-index-list fa-table masked-current-cluster
                                         length cluster-size)))
             (bounded-nat-listp index-list b)))
  :hints (("Goal" :in-theory (enable fat32-build-index-list))))

(defthm
  fat32-masked-entry-list-p-of-fat32-build-index-list
  (implies
   (and
    (fat32-masked-entry-p masked-current-cluster)
    (>= masked-current-cluster *ms-first-data-cluster*)
    (< masked-current-cluster (len fa-table)))
   (b* (((mv index-list &)
         (fat32-build-index-list fa-table masked-current-cluster
                                 length cluster-size)))
     (fat32-masked-entry-list-p index-list)))
  :hints (("Goal" :in-theory (enable fat32-build-index-list))))

(defthm
  fat32-build-index-list-of-update-nth
  (implies
   (and (<= *ms-first-data-cluster*
            masked-current-cluster)
        (fat32-masked-entry-p masked-current-cluster))
   (mv-let
     (index-list error-code)
     (fat32-build-index-list fa-table masked-current-cluster
                             length cluster-size)
     (declare (ignore error-code))
     (implies (and (not (member-equal key index-list))
                   (< (nfix key) (len fa-table)))
              (equal (fat32-build-index-list (update-nth key val fa-table)
                                             masked-current-cluster
                                             length cluster-size)
                     (fat32-build-index-list fa-table masked-current-cluster
                                             length cluster-size)))))
  :hints
  (("goal" :induct (fat32-build-index-list fa-table masked-current-cluster
                                           length cluster-size)
    :in-theory (e/d (fat32-build-index-list)
                    (nth update-nth))
    :expand (fat32-build-index-list (update-nth key val fa-table)
                                    masked-current-cluster
                                    length cluster-size))))

(defthm
  lower-bounded-integer-listp-of-fat32-build-index-list
  (implies
   (and (fat32-masked-entry-p masked-current-cluster)
        (<= *ms-first-data-cluster*
            masked-current-cluster))
   (lower-bounded-integer-listp
    (mv-nth
     0
     (fat32-build-index-list fa-table masked-current-cluster
                             length cluster-size))
    *ms-first-data-cluster*))
  :hints
  (("goal" :in-theory (enable fat32-build-index-list))))

(defthm
  true-listp-of-fat32-build-index-list
  (true-listp
    (mv-nth
     0
     (fat32-build-index-list fa-table masked-current-cluster
                             length cluster-size)))
  :hints
  (("goal" :in-theory (enable fat32-build-index-list))))

(defun count-free-clusters-helper (fa-table n)
  (declare (xargs :guard (and (fat32-entry-list-p fa-table)
                              (natp n)
                              (>= (len fa-table) n))
                  :guard-hints (("Goal" :in-theory (disable nth)) )))
  (if
      (zp n)
      0
    (if
        (not (equal (fat32-entry-mask (nth (- n 1) fa-table)) 0))
        (count-free-clusters-helper fa-table (- n 1))
      (+ 1 (count-free-clusters-helper fa-table (- n 1))))))

(defthm
  count-free-clusters-helper-of-update-nth-1
  (implies (not (equal (fat32-entry-mask val) 0))
           (equal (count-free-clusters-helper (update-nth key val fa-table)
                                              n)
                  (if (and (< (nfix key) (nfix n))
                           (equal (fat32-entry-mask (nth key fa-table))
                                  0))
                      (- (count-free-clusters-helper fa-table n)
                         1)
                      (count-free-clusters-helper fa-table n))))
  :hints (("goal" :in-theory (disable update-nth))))

(defthm
  count-free-clusters-helper-of-update-nth-2
  (implies (equal (fat32-entry-mask val) 0)
           (equal (count-free-clusters-helper (update-nth key val fa-table)
                                              n)
                  (if (and (< (nfix key) (nfix n))
                           (not (equal (fat32-entry-mask (nth key fa-table))
                                       0)))
                      (+ (count-free-clusters-helper fa-table n)
                         1)
                      (count-free-clusters-helper fa-table n))))
  :hints (("goal" :in-theory (disable update-nth))))

(defthm count-free-clusters-helper-correctness-1
  (<= (count-free-clusters-helper fa-table n)
      (nfix n))
  :rule-classes :linear)

(defund
  count-free-clusters (fa-table)
  (declare
   (xargs :guard (and (fat32-entry-list-p fa-table)
                      (>= (len fa-table)
                          *ms-first-data-cluster*))
          :guard-hints (("goal" :in-theory (disable nth)))))
  (count-free-clusters-helper
   (nthcdr *ms-first-data-cluster* fa-table)
   (- (len fa-table)
      *ms-first-data-cluster*)))

(defthm count-free-clusters-of-update-nth
  (implies (and (<= *ms-first-data-cluster* (nfix key))
                (< (nfix key) (len fa-table)))
           (equal (count-free-clusters (update-nth key val fa-table))
                  (cond ((and (equal (fat32-entry-mask (nth key fa-table))
                                     0)
                              (not (equal (fat32-entry-mask val) 0)))
                         (- (count-free-clusters fa-table) 1))
                        ((and (equal (fat32-entry-mask val) 0)
                              (not (equal (fat32-entry-mask (nth key fa-table))
                                          0)))
                         (+ (count-free-clusters fa-table) 1))
                        (t (count-free-clusters fa-table)))))
  :hints (("goal" :in-theory (enable count-free-clusters))))

(defthm
  count-free-clusters-correctness-1
  (implies (>= (len fa-table)
               *ms-first-data-cluster*)
           (<= (count-free-clusters fa-table)
               (- (len fa-table)
                  *ms-first-data-cluster*)))
  :rule-classes :linear
  :hints (("goal" :in-theory (enable count-free-clusters))))

(defund
  find-n-free-clusters-helper
  (fa-table n start)
  (declare (xargs :guard (and (fat32-entry-list-p fa-table)
                              (natp n)
                              (natp start))))
  (if (or (atom fa-table) (zp n))
      nil
      (if (not (equal (fat32-entry-mask (car fa-table))
                      0))
          (find-n-free-clusters-helper (cdr fa-table)
                                       n (+ start 1))
          (cons start
                (find-n-free-clusters-helper (cdr fa-table)
                                             (- n 1)
                                             (+ start 1))))))

(defthmd
  find-n-free-clusters-helper-correctness-1
  (implies (and (fat32-entry-list-p fa-table)
                (natp n)
                (natp start)
                (equal b (+ start (len fa-table))))
           (bounded-nat-listp
            (find-n-free-clusters-helper fa-table n start)
            b))
  :hints
  (("goal'" :in-theory (enable find-n-free-clusters-helper))))

(defthmd
  find-n-free-clusters-helper-correctness-2
  (implies
   (natp start)
   (nat-listp (find-n-free-clusters-helper fa-table n start)))
  :hints
  (("goal" :in-theory (enable find-n-free-clusters-helper))))

(defthmd
  find-n-free-clusters-helper-correctness-3
  (implies
   (and (natp start)
        (member-equal
         x
         (find-n-free-clusters-helper fa-table n start)))
   (and (integerp x)
        (<= start x)
        (< x (+ start (len fa-table)))))
  :hints
  (("goal" :in-theory (enable find-n-free-clusters-helper))))

(defthm
  find-n-free-clusters-helper-correctness-4
  (implies
   (and
    (fat32-entry-list-p fa-table)
    (natp n)
    (natp start)
    (not (equal (fat32-entry-mask (nth (- x start) fa-table))
                0)))
   (not (member-equal
         x
         (find-n-free-clusters-helper fa-table n start))))
  :hints
  (("goal" :in-theory (enable find-n-free-clusters-helper)
    :use find-n-free-clusters-helper-correctness-3)
   ("subgoal *1/2"
    :use (:instance find-n-free-clusters-helper-correctness-3
                    (fa-table (cdr fa-table))
                    (start (+ 1 start))))))

(defthm
  find-n-free-clusters-helper-correctness-6
  (implies
   (and (fat32-entry-list-p fa-table)
        (natp start))
   (no-duplicatesp-equal (find-n-free-clusters-helper fa-table n start)))
  :hints
  (("goal" :in-theory (enable find-n-free-clusters-helper))
   ("goal'" :induct (find-n-free-clusters-helper fa-table n start))
   ("subgoal *1/9" :use (:instance find-n-free-clusters-helper-correctness-3
                                   (x start)
                                   (fa-table (cdr fa-table))
                                   (n (- n 1))
                                   (start (+ 1 start))))))

(defthm
  find-n-free-clusters-helper-correctness-7
  (implies
   (and
    (natp start)
    (< (nfix m)
       (len (find-n-free-clusters-helper fa-table n start))))
   (and
    (integerp
     (nth m
          (find-n-free-clusters-helper fa-table n start)))
    (<= start
        (nth m
             (find-n-free-clusters-helper fa-table n start)))
    (< (nth m
             (find-n-free-clusters-helper fa-table n start))
        (+ start (len fa-table)))))
  :rule-classes
  ((:linear :corollary
            (implies
             (and
              (natp start)
              (< (nfix m)
                 (len (find-n-free-clusters-helper fa-table n start))))
             (and
              (<= start
                  (nth m
                       (find-n-free-clusters-helper fa-table n start)))
              (< (nth m
                      (find-n-free-clusters-helper fa-table n start))
                 (+ start (len fa-table))))))
   (:rewrite :corollary
            (implies
             (and
              (natp start)
              (< (nfix m)
                 (len (find-n-free-clusters-helper fa-table n start))))
             (integerp
              (nth m
                   (find-n-free-clusters-helper fa-table n start))))))
  :hints
  (("goal"
    :use
    (:instance
     find-n-free-clusters-helper-correctness-3
     (x
      (nth m
           (find-n-free-clusters-helper fa-table n start)))))))


(encapsulate
  ()

  (local
   (defthm
     len-of-find-n-free-clusters-helper-lemma-1
     (implies
      (consp fa-table)
      (equal
       (len (find-n-free-clusters-helper fa-table n start))
       (if
           (and
            (<
             (len (find-n-free-clusters-helper (take (- (len fa-table) 1) fa-table)
                                               n start))
             (nfix n))
            (equal (fat32-entry-mask (nth (- (len fa-table) 1) fa-table))
                   0))
           (+ (len (find-n-free-clusters-helper (take (- (len fa-table) 1) fa-table)
                                                n start))
              1)
         (len (find-n-free-clusters-helper (take (- (len fa-table) 1) fa-table)
                                           n start)))))
     :hints (("goal" :in-theory (enable find-n-free-clusters-helper)
              :induct (find-n-free-clusters-helper fa-table n start)
              :expand (len (cdr fa-table))))))

  (local
   (defthm
     len-of-find-n-free-clusters-helper-lemma-2
     (<= (len (find-n-free-clusters-helper fa-table n start))
         (nfix n))
     :rule-classes :linear
     :hints
     (("goal" :in-theory (enable find-n-free-clusters-helper)))))

  (defthm
    len-of-find-n-free-clusters-helper
    (equal (len (find-n-free-clusters-helper (take n2 fa-table)
                                             n1 start))
           (min (count-free-clusters-helper fa-table n2)
                (nfix n1)))
    :hints
    (("goal" :in-theory (enable find-n-free-clusters-helper
                                len-of-find-n-free-clusters-helper-lemma-1)))
    :rule-classes
    (:rewrite
     (:linear
      :corollary
      (<= (len (find-n-free-clusters-helper fa-table n start))
          (nfix n))))))

(in-theory (disable (:linear len-of-find-n-free-clusters-helper)))

(defund
    find-n-free-clusters (fa-table n)
  (declare (xargs :guard (and (fat32-entry-list-p fa-table)
                              (natp n))))
  ;; the first 2 clusters are excluded
  (find-n-free-clusters-helper
   (nthcdr *ms-first-data-cluster* fa-table)
   n *ms-first-data-cluster*))

(defthm
  find-n-free-clusters-correctness-1
  (implies (and (fat32-entry-list-p fa-table)
                (natp n)
                (equal b (len fa-table))
                (>= (len fa-table)
                    *ms-first-data-cluster*))
           (bounded-nat-listp (find-n-free-clusters fa-table n)
                              b))
  :hints
  (("goal"
    :in-theory (enable find-n-free-clusters)
    :use
    ((:instance
      find-n-free-clusters-helper-correctness-1
      (start *ms-first-data-cluster*)
      (fa-table (nthcdr *ms-first-data-cluster* fa-table))
      (b (len fa-table))))))
  :rule-classes
  (:rewrite
   (:linear
    :corollary
    (implies (and (fat32-entry-list-p fa-table)
                  (natp n)
                  (equal b (len fa-table))
                  (>= (len fa-table)
                      *ms-first-data-cluster*)
                  (consp (find-n-free-clusters fa-table n)))
             (< (car (find-n-free-clusters fa-table n))
                b)))))

(defthm
  find-n-free-clusters-correctness-2
  (nat-listp (find-n-free-clusters fa-table n))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (consp (find-n-free-clusters fa-table n))
             (and (nat-listp (cdr (find-n-free-clusters fa-table n)))
                  (integerp (car (find-n-free-clusters fa-table n))))))
   (:linear
    :corollary (implies (consp (find-n-free-clusters fa-table n))
                        (<= 0
                            (car (find-n-free-clusters fa-table n))))))
  :hints
  (("goal"
    :in-theory (enable find-n-free-clusters
                       find-n-free-clusters-helper-correctness-2))))

(defthmd
  find-n-free-clusters-correctness-3
  (implies (member-equal x (find-n-free-clusters fa-table n))
           (and (integerp x)
                (<= *ms-first-data-cluster* x)
                (< x (len fa-table))))
  :hints
  (("goal" :in-theory (enable find-n-free-clusters))
   ("goal'"
    :use
    (:instance
     find-n-free-clusters-helper-correctness-3
     (start *ms-first-data-cluster*)
     (fa-table (nthcdr *ms-first-data-cluster* fa-table))))))

(defthm
  find-n-free-clusters-correctness-4
  (implies
   (and (fat32-entry-list-p fa-table)
        (natp n)
        (not (equal (fat32-entry-mask (nth x fa-table))
                    0)))
   (not (member-equal x (find-n-free-clusters fa-table n))))
  :hints
  (("goal"
    :in-theory (e/d (find-n-free-clusters)
                    (member-of-a-nat-list))
    :use
    ((:instance
      member-of-a-nat-list
      (lst (find-n-free-clusters-helper
            (nthcdr *ms-first-data-cluster* fa-table)
            n *ms-first-data-cluster*)))
     (:instance
      find-n-free-clusters-helper-correctness-3
      (fa-table (nthcdr *ms-first-data-cluster* fa-table))
      (start *ms-first-data-cluster*))))))

;; Holding off for now on determining what
;; find-n-free-clusters-helper-correctness-5 should look like.
(defthm
  find-n-free-clusters-correctness-5
  (implies
   (and (fat32-entry-list-p fa-table)
        (natp n1)
        (< (nfix n2)
           (len (find-n-free-clusters fa-table n1))))
   (equal (fat32-entry-mask
           (nth (nth n2 (find-n-free-clusters fa-table n1))
                fa-table))
          0))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d nil
                    (find-n-free-clusters-correctness-4))
    :use ((:instance
           find-n-free-clusters-correctness-4
           (n n1)
           (x (nth n2
                   (find-n-free-clusters fa-table n1))))))))

(defthm find-n-free-clusters-correctness-6
  (implies (fat32-entry-list-p fa-table)
           (no-duplicatesp-equal (find-n-free-clusters fa-table n)))
  :hints (("goal" :in-theory (enable find-n-free-clusters))))

(defthm
  find-n-free-clusters-correctness-8
  (integer-listp (find-n-free-clusters fa-table n)))

(defthm find-n-free-clusters-correctness-7
  (implies (force (< (nfix m)
                     (len (find-n-free-clusters fa-table n))))
           (and (<= *ms-first-data-cluster*
                    (nth m (find-n-free-clusters fa-table n)))
                (< (nth m (find-n-free-clusters fa-table n))
                   (len fa-table))))
  :rule-classes :linear
  :hints (("goal" :in-theory (e/d (find-n-free-clusters) (nth)))))

(defthm
  find-n-free-clusters-helper-of-true-list-fix
  (equal (find-n-free-clusters-helper (true-list-fix fa-table)
                                      n start)
         (find-n-free-clusters-helper fa-table n start))
  :hints
  (("goal" :in-theory (enable find-n-free-clusters-helper))))

(defthm
  len-of-find-n-free-clusters
  (equal (len (find-n-free-clusters fa-table n))
         (min (count-free-clusters fa-table)
              (nfix n)))
  :hints (("goal" :in-theory (e/d (count-free-clusters find-n-free-clusters)
                                  (nthcdr len-of-find-n-free-clusters-helper))
           :use (:instance len-of-find-n-free-clusters-helper
                           (n2 (len (nthcdr 2 fa-table)))
                           (fa-table (nthcdr 2 fa-table))
                           (n1 n)
                           (start 2))))
  :rule-classes
  (:rewrite
   (:linear
    :corollary
    (<= (len (find-n-free-clusters fa-table n))
        (nfix n)))))

(in-theory (disable (:linear len-of-find-n-free-clusters)))

(defthmd
  fat32-masked-entry-list-p-alt
  (equal (fat32-masked-entry-list-p x)
         (bounded-nat-listp x *expt-2-28*))
  :hints (("goal" :in-theory (enable fat32-masked-entry-p))))

(defthm
  fat32-masked-entry-list-p-of-find-n-free-clusters
  (implies (and (fat32-entry-list-p fa-table)
                (natp n)
                (>= (len fa-table) *ms-first-data-cluster*)
                (<= (len fa-table) *ms-bad-cluster*))
           (fat32-masked-entry-list-p (find-n-free-clusters fa-table n)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (fat32-entry-list-p fa-table)
          (natp n)
          (>= (len fa-table) *ms-first-data-cluster*)
          (<= (len fa-table) *ms-bad-cluster*))
     (let ((l (find-n-free-clusters fa-table n)))
       (implies (consp l)
                (and (fat32-masked-entry-list-p (cdr l))
                     (fat32-masked-entry-p (car l))))))))
  :hints (("goal" :in-theory (disable find-n-free-clusters-correctness-1)
           :use ((:instance find-n-free-clusters-correctness-1
                            (b (len fa-table)))
                 (:instance fat32-masked-entry-list-p-alt
                            (x (find-n-free-clusters fa-table n)))
                 (:instance bounded-nat-listp-correctness-5
                            (l (find-n-free-clusters fa-table n))
                            (x (len fa-table))
                            (y *expt-2-28*))))))

(defthm
  lower-bounded-integer-listp-of-find-n-free-clusters-helper
  (implies (integerp start)
           (lower-bounded-integer-listp
            (find-n-free-clusters-helper fa-table n start)
            start))
  :hints
  (("goal" :in-theory (enable lower-bounded-integer-listp
                              find-n-free-clusters-helper))
   ("subgoal *1/5.1'"
    :use
    (:instance lower-bounded-integer-listp-correctness-5
               (l (find-n-free-clusters-helper (cdr fa-table)
                                               (+ -1 n)
                                               (+ 1 start)))
               (x (+ 1 start))
               (y start)))
   ("subgoal *1/3''"
    :use
    (:instance lower-bounded-integer-listp-correctness-5
               (l (find-n-free-clusters-helper (cdr fa-table)
                                               n (+ 1 start)))
               (x (+ 1 start))
               (y start)))))

(defthm
  lower-bounded-integer-listp-of-find-n-free-clusters
  (lower-bounded-integer-listp (find-n-free-clusters fa-table n)
                               *ms-first-data-cluster*)
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (consp (find-n-free-clusters fa-table n))
     (lower-bounded-integer-listp (cdr (find-n-free-clusters fa-table n))
                                  *ms-first-data-cluster*))
    :hints (("goal" :in-theory (enable lower-bounded-integer-listp))))
   (:linear
    :corollary (implies (consp (find-n-free-clusters fa-table n))
                        (<= *ms-first-data-cluster*
                            (car (find-n-free-clusters fa-table n))))
    :hints (("goal" :in-theory (enable lower-bounded-integer-listp)))))
  :hints (("goal" :in-theory (enable find-n-free-clusters))))

(defund
  set-indices-in-fa-table
  (fa-table index-list value-list)
  (declare
   (xargs :measure (acl2-count index-list)
          :guard (and (fat32-entry-list-p fa-table)
                      (nat-listp index-list)
                      (fat32-masked-entry-list-p value-list)
                      (equal (len index-list)
                             (len value-list)))))
  (if
   (atom index-list)
   fa-table
   (let
    ((current-index (car index-list)))
    (if
     (or (not (natp current-index))
         (>= current-index (len fa-table)))
     fa-table
     (set-indices-in-fa-table
      (update-nth current-index
                  (fat32-update-lower-28 (nth current-index fa-table)
                                         (car value-list))
                  fa-table)
      (cdr index-list)
      (cdr value-list))))))

(defthm
  set-indices-in-fa-table-correctness-1
  (implies
   (and (fat32-entry-list-p fa-table)
        (bounded-nat-listp index-list (len fa-table))
        (fat32-masked-entry-list-p value-list)
        (equal (len index-list)
               (len value-list)))
   (fat32-entry-list-p
    (set-indices-in-fa-table fa-table index-list value-list)))
  :hints (("Goal" :in-theory (enable set-indices-in-fa-table))))

(defthm
  set-indices-in-fa-table-correctness-2
  (equal (len (set-indices-in-fa-table fa-table index-list value-list))
         (len fa-table))
  :hints (("goal" :in-theory (enable set-indices-in-fa-table))))

;; Well, it might not be a great idea to borrow a numbering scheme from
;; set-indices.lisp
(defthm set-indices-in-fa-table-correctness-3
  (implies (and (natp n)
                (nat-listp index-list)
                (not (member-equal n index-list)))
           (equal (nth n (set-indices-in-fa-table fa-table index-list value-list))
                  (nth n fa-table)))
  :hints (("Goal" :in-theory (enable set-indices-in-fa-table))))

(defthm set-indices-in-fa-table-correctness-4
  (implies (and (natp key)
                (< key (len l))
                (nat-listp index-list)
                (not (member-equal key index-list)))
           (equal (set-indices-in-fa-table (update-nth key val l) index-list value-list)
                  (update-nth key val (set-indices-in-fa-table l index-list value-list))))
  :hints (("Goal" :in-theory (enable set-indices-in-fa-table))))

(defthm
  fat32-masked-entry-list-p-when-bounded-nat-listp
  (implies
   (and (bounded-nat-listp file-index-list (len fa-table))
        (<= (len fa-table) *ms-bad-cluster*))
   (fat32-masked-entry-list-p file-index-list))
  :hints (("goal" :in-theory (enable fat32-masked-entry-p))))

(defthm
  fat32-build-index-list-of-set-indices-disjoint
  (implies
   (and
    (natp masked-current-cluster)
    (nat-listp index-list)
    (not (intersectp-equal
          (mv-nth 0
                  (fat32-build-index-list fa-table masked-current-cluster
                                          length cluster-size))
          index-list)))
   (equal (fat32-build-index-list
           (set-indices-in-fa-table fa-table index-list value-list)
           masked-current-cluster
           length cluster-size)
          (fat32-build-index-list fa-table masked-current-cluster
                                  length cluster-size)))
  :hints
  (("goal" :induct (fat32-build-index-list fa-table masked-current-cluster
                                           length cluster-size)
    :in-theory (e/d (intersectp-equal fat32-build-index-list)
                    (intersectp-is-commutative)))))

(encapsulate
  ()

  (local
   (defun
     induction-scheme
     (file-index-list file-length cluster-size)
     (if (or (zp file-length) (zp cluster-size))
         file-index-list
         (induction-scheme (cdr file-index-list)
                           (nfix (- file-length cluster-size))
                           cluster-size))))

  (defthm
    fat32-build-index-list-of-set-indices-in-fa-table-coincident
    (implies
     (and (natp file-length)
          (no-duplicatesp-equal file-index-list)
          (< (* cluster-size
                (+ -1 (len file-index-list)))
             file-length)
          (lower-bounded-integer-listp
           file-index-list *ms-first-data-cluster*)
          (bounded-nat-listp file-index-list (len fa-table))
          (consp file-index-list)
          (<= (len fa-table) *ms-bad-cluster*)
          (not (zp cluster-size)))
     (equal (fat32-build-index-list
             (set-indices-in-fa-table
              fa-table file-index-list
              (append (cdr file-index-list)
                      (list *ms-end-of-clusterchain*)))
             (car file-index-list)
             file-length cluster-size)
            (mv file-index-list 0)))
    :hints
    (("goal" :in-theory (e/d (set-indices-in-fa-table fat32-build-index-list)
                             (fat32-masked-entry-list-p-when-bounded-nat-listp))
      :induct (induction-scheme file-index-list
                                file-length cluster-size)
      :expand
      ((:free (fa-table value-list)
              (set-indices-in-fa-table
               fa-table file-index-list value-list))
       (fat32-build-index-list
        (update-nth
         (car file-index-list)
         (fat32-update-lower-28
          (nth (car file-index-list) fa-table)
          (cadr file-index-list))
         (set-indices-in-fa-table fa-table (cdr file-index-list)
                                  (append (cddr file-index-list)
                                          '(268435455))))
        (car file-index-list)
        file-length cluster-size)))
     ("subgoal *1/2"
      :use fat32-masked-entry-list-p-when-bounded-nat-listp))))

(defthm
  member-of-fat32-build-index-list
  (implies
   (and (equal (mv-nth 1
                       (fat32-build-index-list fa-table masked-current-cluster
                                               length cluster-size))
               0)
        (equal (fat32-entry-mask (nth x fa-table))
               0))
   (not (member-equal
         x
         (mv-nth 0
                 (fat32-build-index-list fa-table masked-current-cluster
                                         length cluster-size)))))
  :hints (("goal" :in-theory (enable fat32-build-index-list))))

(defthm
  integerp-of-fat32-build-index-list
  (implies
   (not (equal (mv-nth 1
                       (fat32-build-index-list fa-table masked-current-cluster
                                               length cluster-size))
               0))
   (equal (mv-nth 1
                  (fat32-build-index-list fa-table masked-current-cluster
                                          length cluster-size))
          (- *eio*)))
  :hints (("goal" :in-theory (enable fat32-build-index-list)))
  :rule-classes
  (:rewrite
   (:type-prescription
    :corollary
    (and
     (integerp (mv-nth 1
                       (fat32-build-index-list fa-table masked-current-cluster
                                               length cluster-size)))
     (<= (mv-nth 1
                 (fat32-build-index-list fa-table masked-current-cluster
                                         length cluster-size))
         0)))))

(defthm
  fat32-build-index-list-correctness-1
  (implies
   (and (fat32-entry-list-p fa-table)
        (natp n)
        (equal (mv-nth 1
                       (fat32-build-index-list fa-table masked-current-cluster
                                               length cluster-size))
               0))
   (not (intersectp-equal
         (mv-nth 0
                 (fat32-build-index-list fa-table masked-current-cluster
                                         length cluster-size))
         (find-n-free-clusters fa-table n))))
  :hints (("goal" :in-theory (e/d (intersectp-equal fat32-build-index-list)
                                  (intersectp-is-commutative))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and
      (fat32-entry-list-p fa-table)
      (natp n)
      (equal (mv-nth 1
                     (fat32-build-index-list fa-table masked-current-cluster
                                             length cluster-size))
             0))
     (not (intersectp-equal
           (find-n-free-clusters fa-table n)
           (mv-nth 0
                   (fat32-build-index-list fa-table masked-current-cluster
                                           length cluster-size))))))))

(defthm
  nth-of-set-indices-in-fa-table-when-member
  (implies (and (bounded-nat-listp index-list (len fa-table))
                (fat32-masked-entry-p val)
                (member-equal n index-list))
           (equal (nth n
                       (set-indices-in-fa-table fa-table index-list
                                                (make-list-ac (len index-list)
                                                              val nil)))
                  (fat32-update-lower-28 (nth n fa-table)
                                         val)))
  :hints (("goal" :in-theory (enable set-indices-in-fa-table))))

(defthm
  fat32-build-index-list-correctness-2
  (implies
   (equal (mv-nth 1
                  (fat32-build-index-list fa-table masked-current-cluster
                                          length cluster-size))
          0)
   (member-equal
    masked-current-cluster
    (mv-nth 0
            (fat32-build-index-list fa-table masked-current-cluster
                                    length cluster-size))))
  :hints
  (("goal" :in-theory (enable fat32-build-index-list))))

(defthm
  car-of-last-of-fat32-build-index-list
  (implies
   (and (fat32-masked-entry-p masked-current-cluster)
        (< masked-current-cluster (len fa-table)))
   (<
    (car (last (mv-nth 0
                       (fat32-build-index-list fa-table masked-current-cluster
                                               length cluster-size))))
    (len fa-table)))
  :hints
  (("goal"
    :in-theory (disable car-of-last-when-bounded-nat-listp)
    :use
    (:instance
     car-of-last-when-bounded-nat-listp
     (l (mv-nth 0
                (fat32-build-index-list fa-table masked-current-cluster
                                        length cluster-size)))
     (b (len fa-table)))))
  :rule-classes :linear)
