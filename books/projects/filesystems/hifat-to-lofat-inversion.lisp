(in-package "ACL2")

;  hifat-to-lofat-inversion.lisp                        Mihir Mehta

; This is a proof of the invertibility of the hifat-to-lofat transformation as
; well as its inverse transformation lofat-to-hifat.

(include-book "generate-index-list")
(include-book "hifat-entry-count")
(include-book "update-data-region")

;; These are some rules from other books which are either interacting badly
;; with the theory I've built up so far, or else causing a lot of unnecessary
;; frames and tries.
(local
 (in-theory (disable take-of-too-many take-when-atom make-list-ac-removal
                     revappend-removal str::hex-digit-listp-of-cons
                     loghead logtail)))

(local
 (in-theory (disable nth update-nth ceiling floor mod true-listp)))

(defthm
  bounded-nat-listp-of-generate-index-list
  (implies (natp start)
           (bounded-nat-listp (generate-index-list start n)
                              (+ start (nfix n))))
  :rule-classes
  ((:rewrite
    :corollary (implies (and (natp start)
                             (equal b (+ start (nfix n))))
                        (bounded-nat-listp (generate-index-list start n)
                                           b)))))

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
  (b*
      ((cluster-size (cluster-size fat32-in-memory))
       ((when
            (or (zp length) (zp cluster-size)))
        (mv nil (- *eio*)))
       (masked-next-cluster
        (fat32-entry-mask
         (if (mbt (< (nfix masked-current-cluster)
                     (nfix (+ (count-of-clusters fat32-in-memory)
                              *ms-first-data-cluster*))))
             (fati masked-current-cluster fat32-in-memory)
           nil)))
       ((when
            (< masked-next-cluster
               *ms-first-data-cluster*))
        (mv (list masked-current-cluster)
            (- *eio*)))
       ((when
            (or
             (fat32-is-eof masked-next-cluster)
             (>=
              masked-next-cluster
              (mbe
               :exec (+ (count-of-clusters fat32-in-memory)
                        *ms-first-data-cluster*)
               :logic (nfix (+ (count-of-clusters fat32-in-memory)
                               *ms-first-data-cluster*))))))
        (mv (list masked-current-cluster) 0))
       ((mv tail-index-list tail-error)
        (get-clusterchain fat32-in-memory masked-next-cluster
                          (nfix (- length cluster-size)))))
    (mv (list* masked-current-cluster tail-index-list)
        tail-error)))

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
  :hints (("goal" :in-theory (enable effective-fat update-fati))))

(defthm
  get-clusterchain-alt
  (equal (get-clusterchain fat32-in-memory
                           masked-current-cluster length)
         (fat32-build-index-list (effective-fat fat32-in-memory)
                                 masked-current-cluster
                                 length (cluster-size fat32-in-memory)))
  :rule-classes :definition
  :hints (("goal" :in-theory (enable get-clusterchain fat32-build-index-list
                                     fati fat-length effective-fat nth))))

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
       ;; A bug was here for a long time - the bound was set to
       ;; (count-of-clusters fat32-in-memory), giving away the last two
       ;; clusters.
       (bounded-nat-listp clusterchain
                          (+ *ms-first-data-cluster*
                             (count-of-clusters fat32-in-memory)))
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

  (defthm
    integerp-of-get-clusterchain-contents
    (and
     (integerp (mv-nth 1
                       (get-clusterchain-contents
                        fat32-in-memory
                        masked-current-cluster length)))
     (>= 0
         (mv-nth 1
                 (get-clusterchain-contents
                  fat32-in-memory
                  masked-current-cluster length))))
    :rule-classes
    :type-prescription
    :hints
    (("goal" :in-theory (enable get-clusterchain-contents)))))

(defthm
  stringp-of-get-clusterchain-contents
  (stringp
   (mv-nth
    0
    (get-clusterchain-contents fat32-in-memory
                               masked-current-cluster length)))
  :rule-classes :type-prescription
  :hints
  (("goal" :in-theory (enable get-clusterchain-contents))))

(verify-guards get-clusterchain-contents)

(defthm
  get-clusterchain-contents-correctness-2
  (implies
   (>= masked-current-cluster
       *ms-first-data-cluster*)
   (equal
    (mv-nth 1
            (fat32-build-index-list (effective-fat fat32-in-memory)
                                    masked-current-cluster
                                    length (cluster-size fat32-in-memory)))
    (mv-nth 1
            (get-clusterchain-contents fat32-in-memory
                                       masked-current-cluster length))))
  :hints (("goal" :in-theory (enable fat-length fati
                                     effective-fat fat32-build-index-list
                                     nth get-clusterchain-contents))))

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
    (equal (mv-nth 1
                   (get-clusterchain-contents fat32-in-memory
                                              masked-current-cluster length))
           0))
   (equal (get-contents-from-clusterchain
           fat32-in-memory
           (mv-nth 0
                   (get-clusterchain fat32-in-memory
                                     masked-current-cluster length))
           length)
          (mv-nth 0
                  (get-clusterchain-contents fat32-in-memory
                                             masked-current-cluster length))))
  :hints (("goal" :in-theory (enable get-clusterchain-contents
                                     fat32-build-index-list)))
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
               (fat32-build-index-list (effective-fat fat32-in-memory)
                                       masked-current-cluster
                                       length (cluster-size fat32-in-memory)))
       0))
     (equal
      (get-contents-from-clusterchain
       fat32-in-memory
       (mv-nth 0
               (fat32-build-index-list (effective-fat fat32-in-memory)
                                       masked-current-cluster
                                       length (cluster-size fat32-in-memory)))
       length)
      (mv-nth 0
              (get-clusterchain-contents fat32-in-memory
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
  t
  :rule-classes
  ((:linear
    :corollary
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (natp length))
     (<=
      (len (explode (mv-nth 0
                            (get-clusterchain-contents
                             fat32-in-memory
                             masked-current-cluster length))))
      length))
    :hints (("Goal" :in-theory (enable get-clusterchain-contents)) ))
   (:linear
    :corollary
    (implies
     (equal (mv-nth 1
                    (get-clusterchain-contents fat32-in-memory
                                               masked-current-cluster length))
            0)
     (<
      0
      (len
       (explode
        (mv-nth 0
                (get-clusterchain-contents fat32-in-memory
                                           masked-current-cluster length))))))
    :hints (("goal" :in-theory (enable get-clusterchain-contents))))))

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
    :in-theory (enable get-clusterchain-contents
                       fat32-build-index-list)
    :induct (get-clusterchain-contents fat32-in-memory
                                       masked-current-cluster length)
    :expand ((get-clusterchain-contents (update-fati i v fat32-in-memory)
                                        masked-current-cluster length)))))

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
   (equal (char (dir-ent-filename dir-ent) 0) (code-char #xe5))
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
  (implies (fat32-filename-p filename)
           (not (useless-dir-ent-p (dir-ent-set-filename dir-ent filename))))
  :hints (("goal" :in-theory (enable useless-dir-ent-p))))

(defund
  make-dir-ent-list (dir-contents)
  (declare
   (xargs
    :guard (stringp dir-contents)
    :measure (length dir-contents)
    :guard-hints (("goal" :in-theory (enable dir-ent-p)))))
  (b*
      (((when (< (length dir-contents)
                 *ms-dir-ent-length*))
        nil)
       (dir-ent
        (mbe
         :exec
         (string=>nats (subseq dir-contents 0 *ms-dir-ent-length*))
         :logic
         (dir-ent-fix
          (chars=>nats
           (take *ms-dir-ent-length* (explode dir-contents))))))
       ;; From page 24 of the specification: "If DIR_Name[0] == 0x00, then the
       ;; directory entry is free (same as for 0xE5), and there are no
       ;; allocated directory entries after this one (all of the DIR_Name[0]
       ;; bytes in all of the entries after this one are also set to 0). The
       ;; special 0 value, rather than the 0xE5 value, indicates to FAT file
       ;; system driver code that the rest of the entries in this directory do
       ;; not need to be examined because they are all free."
       ((when (equal (char (dir-ent-filename dir-ent) 0)
                     (code-char 0)))
        nil)
       ((when (useless-dir-ent-p dir-ent))
        (make-dir-ent-list
         (subseq dir-contents *ms-dir-ent-length* nil))))
    (list*
     dir-ent
     (make-dir-ent-list (subseq dir-contents
                                *ms-dir-ent-length* nil)))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthmd
    len-of-make-dir-ent-list
    (<= (len (make-dir-ent-list dir-contents))
        (floor (len (explode dir-contents))
               *ms-dir-ent-length*))
    :rule-classes
    ((:linear :trigger-terms ((len (make-dir-ent-list dir-contents))
                              (floor (len (explode dir-contents))
                                     *ms-dir-ent-length*))))
    :hints (("goal" :in-theory (enable make-dir-ent-list)))))

(defund useful-dir-ent-list-p (dir-ent-list)
  (declare (xargs :guard t))
  (if (atom dir-ent-list)
      (equal dir-ent-list nil)
    (and (dir-ent-p (car dir-ent-list))
         (not (equal (char (dir-ent-filename
                            (car dir-ent-list))
                           0)
                     (code-char #x00)))
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

(defthm
  useful-dir-ent-list-p-correctness-1
  (implies (and (useful-dir-ent-list-p dir-ent-list)
                (consp dir-ent-list))
           (fat32-filename-p (dir-ent-filename (car dir-ent-list))))
  :hints (("goal" :in-theory (enable useful-dir-ent-list-p useless-dir-ent-p
                                     fat32-filename-p dir-ent-filename))))

;; This is deliberately different from clear-dir-ent, because it only removes
;; the first instance of the directory entry. That's pretty much all we need,
;; because we're only going to use this to remove dot and dotdot entries, and
;; any extra ./.. entries will be cleared out by make-dir-ent-list.
(defund
  remove1-dir-ent (dir-contents filename)
  (declare (xargs :measure (length dir-contents)
                  :guard (stringp dir-contents)
                  :verify-guards nil))
  (b* (((when (< (length dir-contents)
                 *ms-dir-ent-length*))
        "")
       (head (subseq dir-contents 0 *ms-dir-ent-length*))
       (dir-ent (string=>nats head))
       ((when (equal (char (dir-ent-filename dir-ent) 0)
                     (code-char 0)))
        dir-contents)
       ((when (equal (dir-ent-filename dir-ent)
                     filename))
        (subseq dir-contents *ms-dir-ent-length* nil)))
    (string-append
     head
     (remove1-dir-ent
      (subseq dir-contents *ms-dir-ent-length* nil)
      filename))))

(defthm
  stringp-of-remove1-dir-ent
  (implies (stringp dir-contents)
           (stringp (remove1-dir-ent dir-contents filename)))
  :hints (("goal" :in-theory (enable remove1-dir-ent))))

(verify-guards remove1-dir-ent
  :hints (("goal" :in-theory (enable dir-ent-p))))

(defthm
  make-dir-ent-list-of-remove1-dir-ent
  (implies (not (fat32-filename-p filename))
           (equal (make-dir-ent-list (remove1-dir-ent dir-contents filename))
                  (make-dir-ent-list (str-fix dir-contents))))
  :hints (("goal" :in-theory (enable remove1-dir-ent make-dir-ent-list
                                     fat32-filename-p useless-dir-ent-p))))

(defund
  dir-ent-clusterchain
  (fat32-in-memory dir-ent)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (and (lofat-fs-p fat32-in-memory)
                (dir-ent-p dir-ent)
                (<= *ms-first-data-cluster*
                    (dir-ent-first-cluster dir-ent))
                (< (dir-ent-first-cluster dir-ent)
                   (+ *ms-first-data-cluster*
                      (count-of-clusters fat32-in-memory))))))
  (if (dir-ent-directory-p dir-ent)
      (get-clusterchain fat32-in-memory
                        (dir-ent-first-cluster dir-ent)
                        *ms-max-dir-size*)
    (get-clusterchain fat32-in-memory
                      (dir-ent-first-cluster dir-ent)
                      (dir-ent-file-size dir-ent))))

(defthm
  true-listp-of-dir-ent-clusterchain
  (true-listp
   (mv-nth
    0
    (dir-ent-clusterchain fat32-in-memory dir-ent)))
  :hints
  (("goal" :in-theory (enable dir-ent-clusterchain))))

(defthm
  fat32-masked-entry-list-p-of-dir-ent-clusterchain
  (implies (and (dir-ent-p dir-ent)
                (<= *ms-first-data-cluster*
                    (dir-ent-first-cluster dir-ent))
                (< (dir-ent-first-cluster dir-ent)
                   (+ *ms-first-data-cluster*
                      (count-of-clusters fat32-in-memory))))
           (fat32-masked-entry-list-p
            (mv-nth 0
                    (dir-ent-clusterchain fat32-in-memory dir-ent))))
  :hints (("goal" :in-theory (enable dir-ent-clusterchain))))

(defthm
  dir-ent-clusterchain-of-update-fati
  (implies
   (and (dir-ent-p dir-ent)
        (<= *ms-first-data-cluster* (dir-ent-first-cluster dir-ent))
        (not
         (member-equal i
                       (mv-nth 0
                               (dir-ent-clusterchain fat32-in-memory dir-ent)))))
   (equal (dir-ent-clusterchain (update-fati i v fat32-in-memory)
                                dir-ent)
          (dir-ent-clusterchain fat32-in-memory dir-ent)))
  :hints (("goal" :in-theory (enable dir-ent-clusterchain))))

(defund
  dir-ent-clusterchain-contents
  (fat32-in-memory dir-ent)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (and (lofat-fs-p fat32-in-memory)
                (dir-ent-p dir-ent)
                (<= *ms-first-data-cluster*
                    (dir-ent-first-cluster dir-ent))
                (< (dir-ent-first-cluster dir-ent)
                   (+ *ms-first-data-cluster*
                      (count-of-clusters fat32-in-memory))))))
  (if (dir-ent-directory-p dir-ent)
      (get-clusterchain-contents fat32-in-memory
                                 (dir-ent-first-cluster dir-ent)
                                 *ms-max-dir-size*)
    (get-clusterchain-contents fat32-in-memory
                               (dir-ent-first-cluster dir-ent)
                               (dir-ent-file-size dir-ent))))

(defthm
  stringp-of-dir-ent-clusterchain-contents
  (stringp
   (mv-nth
    0
    (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
  :rule-classes :type-prescription
  :hints
  (("goal" :in-theory (enable dir-ent-clusterchain-contents))))

(defthm
  length-of-dir-ent-clusterchain-contents
  t
  :rule-classes
  ((:linear
    :corollary
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (not (dir-ent-directory-p dir-ent)))
     (<= (len (explode (mv-nth 0
                               (dir-ent-clusterchain-contents
                                fat32-in-memory dir-ent))))
         (dir-ent-file-size dir-ent)))
    :hints
    (("goal"
      :in-theory (enable dir-ent-clusterchain-contents))))
   (:linear
    :corollary
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (dir-ent-directory-p dir-ent))
     (<= (len (explode (mv-nth 0
                               (dir-ent-clusterchain-contents
                                fat32-in-memory dir-ent))))
         *ms-max-dir-size*))
    :hints
    (("goal"
      :in-theory (enable dir-ent-clusterchain-contents))))
   (:linear
    :corollary
    (implies
     (equal
      (mv-nth 1
              (dir-ent-clusterchain-contents
               fat32-in-memory dir-ent))
      0)
     (< 0
        (len (explode (mv-nth 0
                              (dir-ent-clusterchain-contents
                               fat32-in-memory dir-ent))))))
    :hints
    (("goal"
      :in-theory (enable dir-ent-clusterchain-contents))))))

;; After the fashion of get-clusterchain-contents-correctness-2, we're going to
;; rewrite instances of (mv-nth 1 (dir-ent-clusterchain ...))
;; We're adding a return value for collecting all these clusterchains, to help
;; us ensure the separation properties we want. We're also adding a return
;; value, to signal an error when we run out of entries.
(defthm
  dir-ent-clusterchain-correctness-1
  (implies
   (<= *ms-first-data-cluster*
       (dir-ent-first-cluster dir-ent))
   (equal (mv-nth 1
                  (dir-ent-clusterchain fat32-in-memory dir-ent))
          (mv-nth 1
                  (dir-ent-clusterchain-contents fat32-in-memory dir-ent))))
  :hints (("goal" :in-theory (enable dir-ent-clusterchain
                                     dir-ent-clusterchain-contents))))

(defthm
  dir-ent-clusterchain-contents-of-update-fati
  (implies
   (not
    (member-equal i
                  (mv-nth 0
                          (dir-ent-clusterchain fat32-in-memory dir-ent))))
   (equal (dir-ent-clusterchain-contents (update-fati i v fat32-in-memory)
                                         dir-ent)
          (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
  :hints (("goal" :in-theory (enable dir-ent-clusterchain-contents
                                     dir-ent-clusterchain))))

(defthm
  integerp-of-dir-ent-clusterchain-contents
  (and
   (integerp (mv-nth 1
                     (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
   (>= 0
       (mv-nth 1
               (dir-ent-clusterchain-contents fat32-in-memory dir-ent))))
  :rule-classes :type-prescription
  :hints (("goal" :in-theory (enable dir-ent-clusterchain-contents))))

(defund
  dir-ent-list-from-first-cluster
  (fat32-in-memory first-cluster)
  (declare
   (xargs :stobjs fat32-in-memory
          :guard (and (lofat-fs-p fat32-in-memory)
                      (fat32-masked-entry-p first-cluster)
                      (>= first-cluster *ms-first-data-cluster*)
                      (< first-cluster
                         (+ (count-of-clusters fat32-in-memory)
                            *ms-first-data-cluster*)))))
  (mv-let
    (contents error-code)
    (get-clusterchain-contents fat32-in-memory
                               first-cluster *ms-max-dir-size*)
    (mv (make-dir-ent-list contents) error-code)))

;; We're going to take this theorem and part of the implementation, but not
;; more. We can't afford to get sidetracked and have to completely rethink the
;; proof.
(defthm
  useful-dir-ent-list-p-of-dir-ent-list-from-first-cluster
  (useful-dir-ent-list-p
   (mv-nth 0
           (dir-ent-list-from-first-cluster
            fat32-in-memory first-cluster)))
  :hints (("Goal" :in-theory (enable dir-ent-list-from-first-cluster)) ))

(defund
  subdir-contents-p (contents)
  (declare (xargs :guard (stringp contents)))
  (let*
      ((contents-without-dot
        (remove1-dir-ent contents *current-dir-fat32-name*))
       (contents-without-dot-or-dotdot
        (remove1-dir-ent contents-without-dot
                         *parent-dir-fat32-name*)))
    (and (<= (length contents-without-dot)
             (- (length contents) *ms-dir-ent-length*))
         (<= (length contents-without-dot-or-dotdot)
             (- (length contents-without-dot)
                *ms-dir-ent-length*)))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    len-of-dir-ent-list-from-first-cluster-when-subdir-contents-p
    (implies
     (and
      (lofat-fs-p fat32-in-memory)
      (dir-ent-directory-p dir-ent)
      (subdir-contents-p
       (mv-nth 0
               (dir-ent-clusterchain-contents fat32-in-memory dir-ent))))
     (<=
      (len
       (mv-nth
        0
        (dir-ent-list-from-first-cluster fat32-in-memory
                                         (dir-ent-first-cluster dir-ent))))
      *ms-max-dir-ent-count*))
    :hints
    (("goal"
      :in-theory (enable dir-ent-list-from-first-cluster
                         subdir-contents-p
                         dir-ent-clusterchain-contents)
      :use
      ((:instance
        (:linear len-of-make-dir-ent-list)
        (dir-contents
         (remove1-dir-ent
          (remove1-dir-ent
           (mv-nth 0
                   (get-clusterchain-contents fat32-in-memory
                                              (dir-ent-first-cluster dir-ent)
                                              *ms-max-dir-size*))
           *current-dir-fat32-name*)
          *parent-dir-fat32-name*)))
       (:instance
        painful-debugging-lemma-16
        (i1
         (len
          (remove1-dir-ent
           (remove1-dir-ent
            (mv-nth 0
                    (get-clusterchain-contents fat32-in-memory
                                               (dir-ent-first-cluster dir-ent)
                                               *ms-max-dir-size*))
            *current-dir-fat32-name*)
           *parent-dir-fat32-name*)))
        (i2 (+ -64 *ms-max-dir-size*))
        (j 32)))))
    :rule-classes
    (:linear
     (:linear
      :corollary
      (implies
       (and
        (lofat-fs-p fat32-in-memory)
        (dir-ent-directory-p dir-ent)
        (subdir-contents-p
         (mv-nth 0
                 (dir-ent-clusterchain-contents fat32-in-memory dir-ent))))
       (<=
        (len
         (make-dir-ent-list
          (mv-nth 0
                  (dir-ent-clusterchain-contents fat32-in-memory dir-ent))))
        *ms-max-dir-ent-count*))
      :hints
      (("goal"
        :in-theory (enable dir-ent-list-from-first-cluster
                           dir-ent-clusterchain-contents))))
     (:linear
      :corollary
      (implies
       (and (lofat-fs-p fat32-in-memory)
            (dir-ent-directory-p dir-ent)
            (subdir-contents-p
             (mv-nth 0
                     (get-clusterchain-contents
                      fat32-in-memory
                      (dir-ent-first-cluster dir-ent)
                      *ms-max-dir-size*))))
       (<=
        (len
         (make-dir-ent-list (mv-nth 0
                                    (get-clusterchain-contents
                                     fat32-in-memory
                                     (dir-ent-first-cluster dir-ent)
                                     *ms-max-dir-size*))))
        *ms-max-dir-ent-count*))
      :hints
      (("goal"
        :in-theory (enable dir-ent-list-from-first-cluster
                           dir-ent-clusterchain-contents
                           get-clusterchain-contents)))))))

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

;; Here's the idea behind this recursion: A loop could occur on a badly formed
;; FAT32 volume which has a cycle in its directory structure (for instance, if
;; / and /tmp/ were to point to the same cluster as their initial cluster.)
;; This loop could be stopped most cleanly by maintaining a list of all
;; clusters which could be visited, and checking them off as we visit more
;; entries. Then, we would detect a second visit to the same cluster, and
;; terminate with an error condition. Only otherwise would we make a recursive
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
          (dir-ent-clusterchain-contents
           fat32-in-memory dir-ent)))
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
          (dir-ent-clusterchain
           fat32-in-memory dir-ent)))
       ;; head-entry-count and head-clusterchain-list, here, do not include the
       ;; entry or clusterchain respectively for the head itself. Those will be
       ;; added at the end.
       ((mv head head-entry-count head-clusterchain-list head-error-code)
        (if directory-p
            (lofat-to-hifat-helper
             fat32-in-memory
             (make-dir-ent-list contents)
             (- entry-limit 1))
          (mv contents 0 nil 0)))
       ;; we want entry-limit to serve both as a measure and an upper
       ;; bound on how many entries are found.
       (tail-entry-limit (- entry-limit
                            (+ 1 (nfix head-entry-count))))
       ((mv tail tail-entry-count tail-clusterchain-list tail-error-code)
        (lofat-to-hifat-helper
         fat32-in-memory
         (cdr dir-ent-list)
         tail-entry-limit))
       (error-code
        (if (and ;; get-clusterchain-contents returns an error code of 0.
             (equal error-code 0)
             (equal head-error-code 0)
             (equal tail-error-code 0)
             (not
              ;; This is the weird case where we have a directory... and
              ;; it's 2^21 or fewer bytes long... but somehow it's managed
              ;; to skip either the . entry or the .. entry.
              (and directory-p
                   (not (subdir-contents-p contents))))
             ;; The three following clauses come around to the point that
             ;; the whole expression
             ;; (append (list clusterchain) head-clusterchain-list
             ;;         tail-clusterchain-list)
             ;; should satsify disjoint-list-listp and
             ;; no-duplicates-listp. See the flatten-disjoint-lists
             ;; theorem to understand what this means.
             (no-duplicatesp clusterchain)
             (not-intersectp-list
              clusterchain
              (append head-clusterchain-list
                      tail-clusterchain-list))
             (not (member-intersectp-equal head-clusterchain-list
                                           tail-clusterchain-list)))
            0
          *EIO*))
       ((mv & find-dir-ent-error-code)
        (find-dir-ent (cdr dir-ent-list) (dir-ent-filename dir-ent))))
    (if
        (equal find-dir-ent-error-code 0)
        (mv tail tail-entry-count tail-clusterchain-list *EIO*)
      ;; We add the file to this m1 instance, having made sure it isn't a
      ;; duplicate.
      (mv (list* (cons filename
                       (make-m1-file :dir-ent dir-ent
                                     :contents head))
                 tail)
          (+ 1 head-entry-count tail-entry-count)
          (append (list clusterchain) head-clusterchain-list
                  tail-clusterchain-list)
          error-code))))

(defthm lofat-to-hifat-helper-correctness-1-lemma-1
  (equal (rationalp (nth n (dir-ent-fix x)))
         (< (nfix n) *ms-dir-ent-length*)))

(defthm
  lofat-to-hifat-helper-correctness-1
  (b* (((mv m1-file-alist entry-count
            clusterchain-list error-code)
        (lofat-to-hifat-helper fat32-in-memory
                               dir-ent-list entry-limit)))
    (and (natp entry-count)
         (<= entry-count (nfix entry-limit))
         (<= (len m1-file-alist)
             (len dir-ent-list))
         (alistp m1-file-alist)
         (true-list-listp clusterchain-list)
         (natp error-code)))
  :hints
  (("goal" :in-theory
    (e/d (fat32-filename-p lofat-to-hifat-helper)
         (nth-of-string=>nats natp-of-cluster-size
                              (:definition fat32-filename-p)))
    :induct (lofat-to-hifat-helper fat32-in-memory
                                   dir-ent-list entry-limit)))
  :rule-classes
  ((:type-prescription
    :corollary (b* (((mv & & & error-code)
                     (lofat-to-hifat-helper fat32-in-memory
                                            dir-ent-list entry-limit)))
                 (natp error-code)))
   (:linear
    :corollary (b* (((mv m1-file-alist & & error-code)
                     (lofat-to-hifat-helper fat32-in-memory
                                            dir-ent-list entry-limit)))
                 (and (<= 0 error-code)
                      (<= (len m1-file-alist)
                          (len dir-ent-list)))))
   (:rewrite
    :corollary (b* (((mv m1-file-alist
                         & clusterchain-list error-code)
                     (lofat-to-hifat-helper fat32-in-memory
                                            dir-ent-list entry-limit)))
                 (and (alistp m1-file-alist)
                      (integerp error-code)
                      (true-list-listp clusterchain-list))))
   (:type-prescription
    :corollary (b* (((mv m1-file-alist &)
                     (lofat-to-hifat-helper fat32-in-memory
                                            dir-ent-list entry-limit)))
                 (true-listp m1-file-alist)))
   (:type-prescription
    :corollary (b* (((mv & entry-count & &)
                     (lofat-to-hifat-helper fat32-in-memory
                                            dir-ent-list entry-limit)))
                 (natp entry-count)))))

(defthm
  m1-file-alist-p-of-lofat-to-hifat-helper-lemma-1
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
  m1-file-alist-p-of-lofat-to-hifat-helper
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
                           useful-dir-ent-list-p hifat-no-dups-p)
         (nth-of-string=>nats natp-of-cluster-size))
    :induct (lofat-to-hifat-helper
             fat32-in-memory
             dir-ent-list entry-limit))))

;; This is local because hifat-to-lofat-inversion-lemma-23 is, despite stronger
;; hypotheses, more general in what it rewrites.
(local
 (defthmd
   hifat-no-dups-p-of-lofat-to-hifat-helper-lemma-1
   (implies
    (not (equal (mv-nth 1 (find-dir-ent dir-ent-list name))
                0))
    (not
     (consp (assoc-equal
             name
             (mv-nth 0
                     (lofat-to-hifat-helper fat32-in-memory
                                            dir-ent-list entry-limit))))))
   :hints (("goal" :in-theory (enable lofat-to-hifat-helper)))))

(defthm
  hifat-no-dups-p-of-lofat-to-hifat-helper
  (b* (((mv m1-file-alist & & &)
        (lofat-to-hifat-helper
         fat32-in-memory
         dir-ent-list entry-limit)))
    (hifat-no-dups-p m1-file-alist))
  :hints
  (("goal"
    :in-theory
    (e/d (fat32-filename-p useless-dir-ent-p
                           lofat-to-hifat-helper
                           useful-dir-ent-list-p hifat-no-dups-p
                           hifat-no-dups-p-of-lofat-to-hifat-helper-lemma-1)
         (nth-of-string=>nats natp-of-cluster-size))
    :induct (lofat-to-hifat-helper
             fat32-in-memory
             dir-ent-list entry-limit))))

(local
 (defthm
   lofat-to-hifat-helper-correctness-3-lemma-1
   (implies
    (and (useful-dir-ent-list-p dir-ent-list)
         (not (fat32-filename-p (dir-ent-filename dir-ent))))
    (not (member-equal dir-ent dir-ent-list)))
   :hints
   (("goal"
     :in-theory (enable useful-dir-ent-list-p
                        fat32-filename-p useless-dir-ent-p)))))

(defthm
  lofat-to-hifat-helper-correctness-3
  (implies
   (useful-dir-ent-list-p dir-ent-list)
   (b* (((mv m1-file-alist entry-count & &)
         (lofat-to-hifat-helper fat32-in-memory
                                dir-ent-list entry-limit)))
     (equal entry-count
            (hifat-entry-count m1-file-alist))))
  :hints
  (("goal"
    :in-theory
    (e/d (lofat-to-hifat-helper
          hifat-entry-count
          hifat-no-dups-p-of-lofat-to-hifat-helper-lemma-1)
         (lofat-to-hifat-helper-correctness-3-lemma-1))
    :induct
    (lofat-to-hifat-helper fat32-in-memory
                           dir-ent-list entry-limit))
   ("subgoal *1/4"
    :use
    (:instance lofat-to-hifat-helper-correctness-3-lemma-1
               (dir-ent (car dir-ent-list)))))
  :rule-classes
  (:rewrite
   (:linear
    :corollary
    (implies
     (useful-dir-ent-list-p dir-ent-list)
     (b*
         (((mv m1-file-alist & & &)
           (lofat-to-hifat-helper fat32-in-memory
                                  dir-ent-list entry-limit)))
       (<= (hifat-entry-count m1-file-alist)
           (nfix entry-limit))))
    :hints
    (("goal" :in-theory
      (disable lofat-to-hifat-helper-correctness-1)
      :use lofat-to-hifat-helper-correctness-1)))))

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
                        (:t dir-ent-directory-p)))))

(defthmd
  lofat-to-hifat-helper-correctness-4
  (implies
   (and (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32-in-memory
                                              dir-ent-list entry-limit1))
               0)
        (>= (nfix entry-limit2)
            (mv-nth 1
                    (lofat-to-hifat-helper fat32-in-memory
                                           dir-ent-list entry-limit1))))
   (equal (lofat-to-hifat-helper fat32-in-memory
                                 dir-ent-list entry-limit2)
          (lofat-to-hifat-helper fat32-in-memory
                                 dir-ent-list entry-limit1)))
  :hints
  (("goal"
    :in-theory (e/d (lofat-to-hifat-helper)
                    ((:rewrite hifat-file-alist-fix-when-hifat-no-dups-p)
                     (:rewrite take-of-len-free)
                     (:definition member-equal)
                     (:rewrite subsetp-car-member)))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32-in-memory
                                            dir-ent-list entry-limit1))
             0)
      (>= (nfix entry-limit2)
          (mv-nth 1
                  (lofat-to-hifat-helper fat32-in-memory
                                         dir-ent-list entry-limit1)))
      ;; This extra clause is for loop-stopping.
      (> entry-limit2 entry-limit1))
     (equal (lofat-to-hifat-helper fat32-in-memory
                                   dir-ent-list entry-limit2)
            (lofat-to-hifat-helper fat32-in-memory
                                   dir-ent-list entry-limit1))))))

(defthmd hifat-to-lofat-inversion-lemma-17
  (implies
   (atom dir-ent-list)
   (equal
    (lofat-to-hifat-helper fat32-in-memory
                           dir-ent-list entry-limit)
    (mv nil 0 nil 0)))
  :hints (("goal" :in-theory (enable lofat-to-hifat-helper))))

(defthm
  lofat-to-hifat-helper-of-update-fati
  (implies
   (and (dir-ent-list-p dir-ent-list)
        (not-intersectp-list
         (list i)
         (mv-nth 2
                 (lofat-to-hifat-helper fat32-in-memory
                                        dir-ent-list entry-limit)))
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32-in-memory
                                              dir-ent-list entry-limit))
               0))
   (equal (lofat-to-hifat-helper (update-fati i v fat32-in-memory)
                                 dir-ent-list entry-limit)
          (lofat-to-hifat-helper fat32-in-memory
                                 dir-ent-list entry-limit)))
  :hints
  (("goal"
    :induct (lofat-to-hifat-helper fat32-in-memory
                                   dir-ent-list entry-limit)
    :expand ((lofat-to-hifat-helper (update-fati i v fat32-in-memory)
                                    dir-ent-list entry-limit)
             (:free (x y)
                    (intersectp-equal (list x) y))
             (:free (y) (intersectp-equal nil y)))
    :in-theory (e/d (lofat-to-hifat-helper not-intersectp-list)
                    ((:rewrite natp-of-cluster-size . 1))))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    hifat-bounded-file-alist-p-helper-of-lofat-to-hifat-helper-lemma-1
    (implies
     (and
      (dir-ent-directory-p (car dir-ent-list))
      (hifat-bounded-file-alist-p-helper
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32-in-memory
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
         (+ -1 entry-limit)))
       (len
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))))
      (subdir-contents-p
       (mv-nth
        0
        (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
      (lofat-fs-p fat32-in-memory))
     (hifat-bounded-file-alist-p-helper
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32-in-memory
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
        (+ -1 entry-limit)))
      *ms-max-dir-ent-count*))
    :hints
    (("goal"
      :in-theory (enable (:rewrite hifat-bounded-file-alist-p-of-cdr-lemma-1))
      :cases
      ((equal
        (len
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list)))))
        *ms-max-dir-ent-count*))))))

(defthm
  hifat-bounded-file-alist-p-helper-of-lofat-to-hifat-helper
  (b* (((mv m1-file-alist & & error-code)
        (lofat-to-hifat-helper fat32-in-memory
                               dir-ent-list entry-limit)))
    (implies (and (equal error-code 0) (lofat-fs-p fat32-in-memory))
             (hifat-bounded-file-alist-p-helper
              m1-file-alist (len dir-ent-list))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lofat-to-hifat-helper)
     (make-dir-ent-list-of-remove1-dir-ent))
    :induct
    (lofat-to-hifat-helper fat32-in-memory
                           dir-ent-list entry-limit))))

(defthm
  no-duplicates-listp-of-lofat-to-hifat-helper
  (b* (((mv & & clusterchain-list error-code)
        (lofat-to-hifat-helper fat32-in-memory
                               dir-ent-list entry-limit)))
    (implies (equal error-code 0)
             (no-duplicates-listp clusterchain-list)))
  :hints
  (("goal" :in-theory (enable lofat-to-hifat-helper)
    :induct (lofat-to-hifat-helper fat32-in-memory
                                   dir-ent-list entry-limit))))

(defthm
  disjoint-list-listp-of-lofat-to-hifat-helper
  (b* (((mv & & clusterchain-list error-code)
        (lofat-to-hifat-helper fat32-in-memory
                               dir-ent-list entry-limit)))
    (implies (equal error-code 0)
             (disjoint-list-listp clusterchain-list)))
  :hints
  (("goal" :in-theory (enable lofat-to-hifat-helper)
    :induct (lofat-to-hifat-helper fat32-in-memory
                                   dir-ent-list entry-limit))))

(defthm
  no-duplicatesp-of-flatten-of-lofat-to-hifat-helper
  (b* (((mv & & clusterchain-list error-code)
        (lofat-to-hifat-helper fat32-in-memory
                               dir-ent-list entry-limit)))
    (implies
     (equal error-code 0)
     (no-duplicatesp-equal (flatten clusterchain-list)))))

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

(defund pseudo-root-dir-ent (fat32-in-memory)
  (declare (xargs :stobjs fat32-in-memory
                  :guard (lofat-fs-p fat32-in-memory)))
  (dir-ent-install-directory-bit
   (dir-ent-set-first-cluster-file-size
    (dir-ent-fix nil)
    (fat32-entry-mask (bpb_rootclus fat32-in-memory))
    0)
   t))

(defthm
  pseudo-root-dir-ent-correctness-1
  (implies
   (lofat-fs-p fat32-in-memory)
   (and (<= 2
            (dir-ent-first-cluster (pseudo-root-dir-ent fat32-in-memory)))
        (< (dir-ent-first-cluster (pseudo-root-dir-ent fat32-in-memory))
           (+ 2 (count-of-clusters fat32-in-memory)))
        (dir-ent-p (pseudo-root-dir-ent fat32-in-memory))))
  :hints (("goal" :in-theory (enable pseudo-root-dir-ent)))
  :rule-classes
  ((:rewrite
    :corollary (implies (lofat-fs-p fat32-in-memory)
                        (dir-ent-p (pseudo-root-dir-ent fat32-in-memory))))
   (:linear
    :corollary
    (implies
     (lofat-fs-p fat32-in-memory)
     (and (<= 2
              (dir-ent-first-cluster (pseudo-root-dir-ent fat32-in-memory)))
          (< (dir-ent-first-cluster (pseudo-root-dir-ent fat32-in-memory))
             (+ 2
                (count-of-clusters fat32-in-memory))))))))

(defthm pseudo-root-dir-ent-of-update-fati
  (equal (pseudo-root-dir-ent (update-fati i v fat32-in-memory))
         (pseudo-root-dir-ent fat32-in-memory))
  :hints (("goal" :in-theory (enable pseudo-root-dir-ent))))

(defthm dir-ent-directory-p-of-pseudo-root-dir-ent
  (dir-ent-directory-p (pseudo-root-dir-ent fat32-in-memory))
  :hints (("Goal" :in-theory (enable pseudo-root-dir-ent))))

(defund root-dir-ent-list (fat32-in-memory)
  (declare (xargs :stobjs fat32-in-memory
                  :guard (lofat-fs-p fat32-in-memory)))
  (mv-let
    (root-dir-contents error-code)
    (dir-ent-clusterchain-contents
     fat32-in-memory
     (pseudo-root-dir-ent fat32-in-memory))
    (mv
     (make-dir-ent-list root-dir-contents)
     error-code)))

(defthm
  useful-dir-ent-list-p-of-root-dir-ent-list
  (useful-dir-ent-list-p
   (mv-nth 0 (root-dir-ent-list fat32-in-memory)))
  :hints (("goal" :in-theory (enable root-dir-ent-list))))

(defthm
  integerp-of-root-dir-ent-list
  (and
   (integerp (mv-nth 1 (root-dir-ent-list fat32-in-memory)))
   (>= 0 (mv-nth 1 (root-dir-ent-list fat32-in-memory))))
  :hints (("goal" :in-theory (enable root-dir-ent-list pseudo-root-dir-ent)))
  :rule-classes :type-prescription)

(defun
    stobj-count-free-clusters-helper
    (fat32-in-memory n)
  (declare
   (xargs :stobjs fat32-in-memory
          :guard (and (lofat-fs-p fat32-in-memory)
                      (natp n)
                      (<= n
                          (count-of-clusters fat32-in-memory)))))
  (if
      (zp n)
      0
    (if
        (not
         (equal
          (fat32-entry-mask (fati (+ n *ms-first-data-cluster* -1)
                                  fat32-in-memory))
          0))
        (stobj-count-free-clusters-helper fat32-in-memory (- n 1))
      (+ 1
         (stobj-count-free-clusters-helper
          fat32-in-memory (- n 1))))))

(defthm
  stobj-count-free-clusters-helper-correctness-1
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (>= (count-of-clusters fat32-in-memory)
            n))
   (equal (stobj-count-free-clusters-helper fat32-in-memory n)
          (count-free-clusters-helper
           (nthcdr *ms-first-data-cluster* (effective-fat fat32-in-memory))
           n))))

(defund stobj-count-free-clusters
  (fat32-in-memory)
  (declare (xargs :stobjs fat32-in-memory
                  :guard (lofat-fs-p fat32-in-memory)))
  (stobj-count-free-clusters-helper
   fat32-in-memory
   (count-of-clusters fat32-in-memory)))

(defthm
  stobj-count-free-clusters-correctness-1
  (implies
   (lofat-fs-p fat32-in-memory)
   (equal
    (stobj-count-free-clusters fat32-in-memory)
    (count-free-clusters (effective-fat fat32-in-memory))))
  :hints
  (("goal" :in-theory (enable count-free-clusters
                              stobj-count-free-clusters))))

(defund
  lofat-to-hifat (fat32-in-memory)
  (declare
   (xargs :stobjs fat32-in-memory
          :guard (lofat-fs-p fat32-in-memory)
          :guard-hints
          (("Goal" :in-theory (enable root-dir-ent-list pseudo-root-dir-ent
                                      dir-ent-clusterchain-contents
                                      dir-ent-clusterchain)))))
  (b*
      (((unless
            (mbt (>= (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                     *ms-first-data-cluster*)))
        (mv nil *eio*))
       ((mv root-dir-clusterchain error-code)
        (dir-ent-clusterchain
         fat32-in-memory
         (pseudo-root-dir-ent fat32-in-memory)))
       ;; We're gradually trying to have more of the pattern where we
       ;; explicitly say what the error code is going to be, rather than pass
       ;; on the value of the error code from a function call. We actually
       ;; aren't changing what was there before! It's a nice thing about
       ;; theorem proving (and the way we've set up our functions and lemmas)
       ;; that we can actually prove that a given function, for instance, only
       ;; returns the error codes 0 and *enoent* (or more commonly, 0 and
       ;; *eio*).
       ((unless
            (and (equal error-code 0)
                 (no-duplicatesp-equal root-dir-clusterchain)))
        (mv nil *eio*))
       ;; If at all there are performance problems after this point, this mbe
       ;; should be checked...
       ((mv root-dir-ent-list &)
        (mbe
         :logic
         (root-dir-ent-list fat32-in-memory)
         :exec
         (mv (make-dir-ent-list
              (get-contents-from-clusterchain
               fat32-in-memory
               root-dir-clusterchain
               *ms-max-dir-size*))
             error-code)))
       ;; This clause might be a problem, since the root directory is not
       ;; obliged to contain dot and dotdot directory entries, which means we
       ;; might be unfairly constraining it to 2^16 -2 directory entries when
       ;; it can have 2^16.
       ((unless (<= (len root-dir-ent-list) *ms-max-dir-ent-count*))
        (mv nil *eio*))
       ((mv m1-file-alist & clusterchain-list error-code)
        (lofat-to-hifat-helper
         fat32-in-memory root-dir-ent-list
         (max-entry-count fat32-in-memory)))
       ((unless (not-intersectp-list root-dir-clusterchain clusterchain-list))
        (mv m1-file-alist *eio*)))
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
   (equal (mv-nth 0
                  (get-clusterchain-contents
                   fat32-in-memory
                   (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                   *ms-max-dir-size*))
          "")
   (equal (mv-nth 0 (lofat-to-hifat fat32-in-memory))
          nil))
  :hints (("goal" :in-theory (enable lofat-to-hifat
                                     lofat-to-hifat-helper
                                     root-dir-ent-list
                                     pseudo-root-dir-ent
                                     dir-ent-clusterchain-contents))))

(defthm
  hifat-entry-count-of-lofat-to-hifat
  (implies
   (lofat-fs-p fat32-in-memory)
   (<= (hifat-entry-count
        (mv-nth 0
                (lofat-to-hifat fat32-in-memory)))
       (max-entry-count fat32-in-memory)))
  :hints (("goal" :in-theory (enable lofat-to-hifat)))
  :rule-classes :linear)

(defthm
  hifat-no-dups-p-of-lofat-to-hifat
  (b* (((mv m1-file-alist &)
        (lofat-to-hifat fat32-in-memory)))
    (hifat-no-dups-p m1-file-alist))
  :hints
  (("goal"
    :in-theory (enable lofat-to-hifat))))

(defthm
  hifat-bounded-file-alist-p-of-lofat-to-hifat
  (b* (((mv m1-file-alist error-code)
        (lofat-to-hifat fat32-in-memory)))
    (implies (and (lofat-fs-p fat32-in-memory)
                  (equal error-code 0))
             (hifat-bounded-file-alist-p m1-file-alist)))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lofat-to-hifat hifat-bounded-file-alist-p)
     ((:rewrite
       hifat-bounded-file-alist-p-helper-of-lofat-to-hifat-helper)))
    :use
    ((:instance
      (:rewrite hifat-bounded-file-alist-p-of-cdr-lemma-1)
      (ac1 (len (mv-nth 0 (root-dir-ent-list fat32-in-memory))))
      (ac2 *ms-max-dir-ent-count*)
      (x
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32-in-memory
         (mv-nth 0 (root-dir-ent-list fat32-in-memory))
         (max-entry-count fat32-in-memory)))))
     (:instance
      (:rewrite
       hifat-bounded-file-alist-p-helper-of-lofat-to-hifat-helper)
      (entry-limit (max-entry-count fat32-in-memory))
      (dir-ent-list
       (mv-nth 0 (root-dir-ent-list fat32-in-memory)))
      (fat32-in-memory fat32-in-memory)))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (b* (((mv & error-code)
          (lofat-to-hifat fat32-in-memory)))
      (implies (and (lofat-fs-p fat32-in-memory)
                    (equal error-code 0))
               (hifat-bounded-file-alist-p
                (mv-nth 0 (lofat-to-hifat-helper
                           fat32-in-memory
                           (mv-nth 0 (root-dir-ent-list fat32-in-memory))
                           (max-entry-count fat32-in-memory))))))
    :hints (("Goal" :in-theory (enable lofat-to-hifat)) ))))

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
    (("goal" :in-theory (disable unsigned-byte-p)))))
  (b*
      (((when (atom index-list))
        fat32-in-memory)
       (current-index (car index-list))
       ((unless (and (natp current-index)
                     (< current-index
                        (+ (count-of-clusters fat32-in-memory)
                           *ms-first-data-cluster*))
                     (mbt
                      (< current-index
                         (fat-length fat32-in-memory)))))
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
          stobj-set-indices-in-fa-table)))))

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
    (enable stobj-set-indices-in-fa-table))))

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

(defthm
  pseudo-root-dir-ent-of-stobj-set-indices-in-fa-table
  (equal (pseudo-root-dir-ent
          (stobj-set-indices-in-fa-table
           fat32-in-memory index-list value-list))
         (pseudo-root-dir-ent fat32-in-memory))
  :hints (("goal" :in-theory (enable pseudo-root-dir-ent))))

(defthm
  get-clusterchain-contents-of-stobj-set-indices-in-fa-table-disjoint
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (not
     (intersectp-equal
      (mv-nth 0
              (fat32-build-index-list (effective-fat fat32-in-memory)
                                      masked-current-cluster
                                      length (cluster-size fat32-in-memory)))
      index-list))
    (integerp masked-current-cluster)
    (fat32-masked-entry-list-p value-list)
    (equal (len index-list)
           (len value-list))
    (nat-listp index-list))
   (equal
    (get-clusterchain-contents
     (stobj-set-indices-in-fa-table fat32-in-memory index-list value-list)
     masked-current-cluster length)
    (get-clusterchain-contents fat32-in-memory
                               masked-current-cluster length)))
  :hints
  (("goal"
    :induct (get-clusterchain-contents fat32-in-memory
                                       masked-current-cluster length)
    :in-theory (e/d (get-clusterchain-contents fat32-build-index-list)
                    (intersectp-is-commutative))
    :expand
    ((get-clusterchain-contents
      (stobj-set-indices-in-fa-table fat32-in-memory index-list value-list)
      masked-current-cluster length)
     (:free (y)
            (intersectp-equal (cons masked-current-cluster y)
                              index-list))))))

(defthm
  get-contents-from-clusterchain-of-stobj-set-indices-in-fa-table
  (equal
   (get-contents-from-clusterchain
    (stobj-set-indices-in-fa-table
     fat32-in-memory index-list value-list)
    clusterchain file-size)
   (get-contents-from-clusterchain fat32-in-memory
                                   clusterchain file-size)))

(defthm
  dir-ent-clusterchain-of-stobj-set-indices-in-fa-table-disjoint
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (nat-listp index-list)
        (fat32-masked-entry-list-p value-list)
        (equal (len index-list)
               (len value-list))
        (not (intersectp-equal
              index-list
              (mv-nth '0
                      (dir-ent-clusterchain fat32-in-memory dir-ent)))))
   (equal
    (dir-ent-clusterchain
     (stobj-set-indices-in-fa-table fat32-in-memory index-list value-list)
     dir-ent)
    (dir-ent-clusterchain fat32-in-memory dir-ent)))
  :hints (("goal" :in-theory (enable dir-ent-clusterchain))))

(defthm
  dir-ent-clusterchain-contents-of-stobj-set-indices-in-fa-table-disjoint
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (not
     (intersectp-equal (mv-nth 0
                               (dir-ent-clusterchain fat32-in-memory dir-ent))
                       index-list))
    (fat32-masked-entry-list-p value-list)
    (equal (len index-list)
           (len value-list))
    (nat-listp index-list))
   (equal
    (dir-ent-clusterchain-contents
     (stobj-set-indices-in-fa-table fat32-in-memory index-list value-list)
     dir-ent)
    (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
  :hints (("goal" :in-theory (enable dir-ent-clusterchain-contents
                                     dir-ent-clusterchain))))

(defthmd
  lofat-to-hifat-helper-of-stobj-set-indices-in-fa-table
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (fat32-masked-entry-list-p value-list)
        (nat-listp index-list)
        (equal (len index-list)
               (len value-list))
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32-in-memory
                                              dir-ent-list entry-limit))
               0)
        (not-intersectp-list
         index-list
         (mv-nth 2
                 (lofat-to-hifat-helper fat32-in-memory
                                        dir-ent-list entry-limit))))
   (equal
    (lofat-to-hifat-helper
     (stobj-set-indices-in-fa-table fat32-in-memory index-list value-list)
     dir-ent-list entry-limit)
    (lofat-to-hifat-helper fat32-in-memory
                           dir-ent-list entry-limit)))
  :hints (("goal" :induct (lofat-to-hifat-helper fat32-in-memory
                                                 dir-ent-list entry-limit)
           :in-theory (e/d (lofat-to-hifat-helper not-intersectp-list)
                           ((:rewrite nth-of-effective-fat)
                            (:rewrite member-of-a-nat-list)
                            (:definition member-equal))))))

(defthm
  stobj-set-indices-in-fa-table-of-stobj-set-indices-in-fa-table-lemma-1
  (implies
   (and (not (member-equal i index-list))
        (natp i))
   (equal
    (fati
     i
     (stobj-set-indices-in-fa-table fat32-in-memory index-list value-list))
    (fati i fat32-in-memory)))
  :hints (("goal" :in-theory (enable stobj-set-indices-in-fa-table))))

(defthmd
  stobj-set-indices-in-fa-table-of-stobj-set-indices-in-fa-table-lemma-2
  (implies
   (and (natp i)
        (< i (fat-length fat32-in-memory))
        (not (member-equal i index-list)))
   (equal
    (stobj-set-indices-in-fa-table (update-fati i v fat32-in-memory)
                                   index-list value-list)
    (update-fati i v
                 (stobj-set-indices-in-fa-table fat32-in-memory
                                                index-list value-list))))
  :hints (("goal" :in-theory (enable stobj-set-indices-in-fa-table))))

(defthm
  stobj-set-indices-in-fa-table-of-stobj-set-indices-in-fa-table-lemma-4
  (implies (and (member-equal x l) (>= x b))
           (not (bounded-nat-listp l b))))

(defthm
  stobj-set-indices-in-fa-table-of-stobj-set-indices-in-fa-table-lemma-3
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (bounded-nat-listp index-list
                           (+ *ms-first-data-cluster*
                              (count-of-clusters fat32-in-memory)))
        (member-equal i index-list)
        (fat32-masked-entry-p v)
        (fat32-masked-entry-list-p value-list)
        (equal (len index-list)
               (len value-list)))
   (equal
    (stobj-set-indices-in-fa-table
     (update-fati i
                  (fat32-update-lower-28 (fati i fat32-in-memory)
                                         v)
                  fat32-in-memory)
     index-list value-list)
    (stobj-set-indices-in-fa-table fat32-in-memory index-list value-list)))
  :hints (("goal" :in-theory (enable stobj-set-indices-in-fa-table)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (natp i)
          (< i (fat-length fat32-in-memory))
          (bounded-nat-listp index-list
                             (+ *ms-first-data-cluster*
                                (count-of-clusters fat32-in-memory)))
          (fat32-masked-entry-p v)
          (fat32-masked-entry-list-p value-list)
          (equal (len index-list)
                 (len value-list)))
     (equal
      (stobj-set-indices-in-fa-table
       (update-fati i
                    (fat32-update-lower-28 (fati i fat32-in-memory)
                                           v)
                    fat32-in-memory)
       index-list value-list)
      (if (member-equal i index-list)
          (stobj-set-indices-in-fa-table fat32-in-memory index-list value-list)
          (update-fati i
                       (fat32-update-lower-28 (fati i fat32-in-memory)
                                              v)
                       (stobj-set-indices-in-fa-table fat32-in-memory
                                                      index-list value-list)))))
    :hints
    (("goal"
      :in-theory
      (enable
       stobj-set-indices-in-fa-table-of-stobj-set-indices-in-fa-table-lemma-2))))))

(encapsulate
  ()

  (local
   (defun-nx
     induction-scheme
     (fat32-in-memory index-list value-list1 value-list2)
     (cond
      ((not (consp value-list2))
       (mv fat32-in-memory
           index-list value-list1 value-list2))
      (t
       (induction-scheme
        (update-fati (car index-list)
                     (fat32-update-lower-28
                      (fati (car index-list) fat32-in-memory)
                      (car value-list2))
                     fat32-in-memory)
        (cdr index-list)
        (cdr value-list1)
        (cdr value-list2))))))

  (defthm
    stobj-set-indices-in-fa-table-of-stobj-set-indices-in-fa-table
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (fat32-masked-entry-list-p value-list1)
          (equal (len value-list1)
                 (len index-list))
          (equal (len value-list2)
                 (len index-list))
          (bounded-nat-listp index-list
                             (+ *ms-first-data-cluster*
                                (count-of-clusters fat32-in-memory)))
          (fat32-masked-entry-list-p value-list2))
     (equal
      (stobj-set-indices-in-fa-table
       (stobj-set-indices-in-fa-table fat32-in-memory index-list value-list1)
       index-list value-list2)
      (stobj-set-indices-in-fa-table fat32-in-memory
                                     index-list value-list2)))
    :hints
    (("goal"
      :in-theory (enable stobj-set-indices-in-fa-table)
      :induct (induction-scheme fat32-in-memory
                                index-list value-list1 value-list2)
      :expand (:free (fat32-in-memory value-list)
                     (stobj-set-indices-in-fa-table fat32-in-memory
                                                    index-list value-list))))))

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
  effective-fat-of-stobj-set-clusters
  (equal (effective-fat
          (stobj-set-clusters cluster-list
                              index-list fat32-in-memory))
         (effective-fat fat32-in-memory)))

(encapsulate
  ()

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

  (defthm
    get-contents-from-clusterchain-of-stobj-set-clusters-coincident
    (implies
     (and (stringp text)
          (equal (len (make-clusters text (cluster-size fat32-in-memory)))
                 (len index-list))
          (integerp length)
          (>= length (length text))
          (lower-bounded-integer-listp index-list *ms-first-data-cluster*)
          (bounded-nat-listp index-list
                             (+ 2 (data-region-length fat32-in-memory)))
          (lofat-fs-p fat32-in-memory)
          (no-duplicatesp-equal index-list))
     (equal
      (get-contents-from-clusterchain
       (stobj-set-clusters (make-clusters text (cluster-size fat32-in-memory))
                           index-list fat32-in-memory)
       index-list length)
      (implode (append (explode text)
                       (make-list (- (min length
                                          (* (len index-list)
                                             (cluster-size fat32-in-memory)))
                                     (length text))
                                  :initial-element (code-char 0))))))
    :hints
    (("goal"
      :induct (induction-scheme index-list
                                text (cluster-size fat32-in-memory)
                                length)
      :expand
      ((:free
        (fat32-in-memory length)
        (get-contents-from-clusterchain fat32-in-memory index-list length))
       (make-clusters text (cluster-size fat32-in-memory)))
      :in-theory (e/d (make-clusters)
                      ((:rewrite associativity-of-append))))
     ("subgoal *1/2"
      :use ((:instance (:rewrite associativity-of-append)
                       (c (make-list-ac (+ (cluster-size fat32-in-memory)
                                           (- (len (explode text)))
                                           (* (cluster-size fat32-in-memory)
                                              (len (cdr index-list))))
                                        (code-char 0)
                                        nil))
                       (b (nthcdr (cluster-size fat32-in-memory)
                                  (explode text)))
                       (a (take (cluster-size fat32-in-memory)
                                (explode text))))
            (:instance (:rewrite associativity-of-append)
                       (c (make-list-ac (+ length (- (len (explode text))))
                                        (code-char 0)
                                        nil))
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

;; This function needs to return an mv containing the fat32-in-memory stobj,
;; the new directory entry, and an errno value (either 0 or ENOSPC).
;;
;; One idea we tried was setting first-cluster to *ms-end-of-clusterchain*
;; (basically, marking it used) inside the body of this function. This would
;; have made some proofs more modular... but it doesn't work, because when
;; we're placing the contents of a directory (inside hifat-to-lofat-helper), we
;; need to make a recursive call to get the contents of that directory in the
;; first place... and first-cluster must be marked used before that call is
;; made to ensure that cluster doesn't get used.
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
                ;; There are no contents to place if the length is zero...
                (> (length contents) 0)
                (fat32-masked-entry-p first-cluster)
                (>= first-cluster *ms-first-data-cluster*)
                (< first-cluster
                   (+ *ms-first-data-cluster*
                      (count-of-clusters fat32-in-memory))))
    :guard-hints
    (("goal" :in-theory (disable unsigned-byte-p)))))
  (b*
      ((dir-ent (dir-ent-fix dir-ent))
       (cluster-size (cluster-size fat32-in-memory))
       (clusters (make-clusters contents cluster-size))
       (indices
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
     0 indices)))

(defthm
  lofat-fs-p-of-place-contents
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (stringp contents)
        (integerp first-cluster)
        (>= first-cluster *ms-first-data-cluster*)
        (< first-cluster
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory))))
   (lofat-fs-p (mv-nth 0
                       (place-contents fat32-in-memory dir-ent
                                       contents file-length first-cluster))))
  :hints (("goal" :in-theory (enable place-contents))))

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
  pseudo-root-dir-ent-of-place-contents
  (equal (pseudo-root-dir-ent
          (mv-nth 0
                  (place-contents fat32-in-memory dir-ent
                                  contents file-length first-cluster)))
         (pseudo-root-dir-ent fat32-in-memory))
  :hints (("goal" :in-theory (enable pseudo-root-dir-ent))))

(defthmd
  place-contents-correctness-1
  (implies
   (not (equal (mv-nth 2
                       (place-contents fat32-in-memory dir-ent
                                       contents file-length first-cluster))
               0))
   (equal (mv-nth 0
                  (place-contents fat32-in-memory dir-ent
                                  contents file-length first-cluster))
          fat32-in-memory))
  :hints (("goal" :in-theory (enable place-contents))))

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
                             fat32-build-index-list-of-set-indices-in-fa-table-coincident)
                            (:rewrite get-clusterchain-contents-correctness-3)
                            (:rewrite get-clusterchain-contents-correctness-2)
                            (:rewrite get-clusterchain-contents-correctness-1)))
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
      (:rewrite fat32-build-index-list-of-set-indices-in-fa-table-coincident)
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
  dir-ent-clusterchain-contents-of-place-contents-coincident-1
  (implies
   (and (dir-ent-directory-p dir-ent2)
        (equal (mv-nth 2
                       (place-contents fat32-in-memory
                                       dir-ent1 contents 0 first-cluster))
               0)
        (equal first-cluster
               (dir-ent-first-cluster dir-ent2))
        (not (zp (length contents)))
        (<= *ms-first-data-cluster* first-cluster)
        (stringp contents)
        (<= (length contents) *ms-max-dir-size*)
        (lofat-fs-p fat32-in-memory)
        (not (equal (fat32-entry-mask (fati first-cluster fat32-in-memory))
                    0))
        (< first-cluster
           (+ 2 (count-of-clusters fat32-in-memory)))
        (fat32-masked-entry-p first-cluster))
   (equal
    (dir-ent-clusterchain-contents
     (mv-nth 0
             (place-contents fat32-in-memory
                             dir-ent1 contents 0 first-cluster))
     dir-ent2)
    (mv
     (implode
      (append
       (explode contents)
       (make-list
        (+ (min *ms-max-dir-size*
                (* (len (make-clusters contents
                                       (cluster-size fat32-in-memory)))
                   (cluster-size fat32-in-memory)))
           (- (length contents)))
        :initial-element (code-char 0))))
     0)))
  :hints (("goal" :in-theory (enable dir-ent-clusterchain-contents))))

(defthm
  dir-ent-clusterchain-contents-of-place-contents-coincident-2
  (implies
   (and (not (dir-ent-directory-p dir-ent2))
        (equal (mv-nth 2
                       (place-contents fat32-in-memory dir-ent1
                                       contents file-length first-cluster))
               0)
        (equal first-cluster
               (dir-ent-first-cluster dir-ent2))
        (equal length (dir-ent-file-size dir-ent2))
        (not (zp (length contents)))
        (<= *ms-first-data-cluster* first-cluster)
        (stringp contents)
        (<= (length contents) length)
        (lofat-fs-p fat32-in-memory)
        (not (equal (fat32-entry-mask (fati first-cluster fat32-in-memory))
                    0))
        (< first-cluster
           (+ 2 (count-of-clusters fat32-in-memory)))
        (fat32-masked-entry-p first-cluster))
   (equal
    (dir-ent-clusterchain-contents
     (mv-nth 0
             (place-contents fat32-in-memory dir-ent1
                             contents file-length first-cluster))
     dir-ent2)
    (mv
     (implode
      (append
       (explode contents)
       (make-list
        (+ (min length
                (* (len (make-clusters contents
                                       (cluster-size fat32-in-memory)))
                   (cluster-size fat32-in-memory)))
           (- (length contents)))
        :initial-element (code-char 0))))
     0)))
  :hints (("goal" :in-theory (enable dir-ent-clusterchain-contents))))

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
  useless-dir-ent-p-of-dir-ent-set-first-cluster-file-size
  (equal
   (useless-dir-ent-p
    (dir-ent-set-first-cluster-file-size dir-ent first-cluster file-size))
   (useless-dir-ent-p dir-ent))
  :hints (("goal" :in-theory (enable useless-dir-ent-p))))

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
  (implies
   (not
    (equal
     (mv-nth
      2
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))
     0))
   (equal
    (mv-nth 2
            (place-contents fat32-in-memory dir-ent
                            contents file-length first-cluster))
    *enospc*))
  :hints (("goal" :in-theory (enable place-contents)))
  :rule-classes
  (:rewrite
   (:type-prescription
    :corollary
    (natp
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

(defthm
  get-clusterchain-contents-of-place-contents-disjoint
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (stringp contents)
    (integerp first-cluster)
    (<= 2 first-cluster)
    (fat32-masked-entry-p masked-current-cluster)
    (equal (mv-nth 1
                   (get-clusterchain-contents fat32-in-memory
                                              masked-current-cluster length))
           0)
    (not
     (member-equal
      first-cluster
      (mv-nth 0
              (fat32-build-index-list (effective-fat fat32-in-memory)
                                      masked-current-cluster length
                                      (cluster-size fat32-in-memory))))))
   (equal (get-clusterchain-contents
           (mv-nth 0
                   (place-contents fat32-in-memory dir-ent
                                   contents file-length first-cluster))
           masked-current-cluster length)
          (get-clusterchain-contents fat32-in-memory
                                     masked-current-cluster length)))
  :hints
  (("goal"
    :in-theory (e/d (place-contents intersectp-equal fat32-build-index-list
                                    get-clusterchain-contents)
                    (intersectp-is-commutative)))))

(defthm
  fat32-build-index-list-of-effective-fat-of-place-contents-disjoint
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
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
    (e/d (place-contents intersectp-equal)
         ((:rewrite fat32-masked-entry-list-p-of-find-n-free-clusters
                    . 1)
          (:rewrite intersectp-is-commutative)))
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
                                         length cluster-size))))))))

(defthm
  dir-ent-clusterchain-of-place-contents-disjoint
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (integerp first-cluster)
    (>= first-cluster *ms-first-data-cluster*)
    (stringp contents)
    (dir-ent-p dir-ent1)
    (not
     (member-equal first-cluster
                   (mv-nth 0
                           (dir-ent-clusterchain fat32-in-memory dir-ent1))))
    (equal (mv-nth 1
                   (dir-ent-clusterchain fat32-in-memory dir-ent1))
           0))
   (equal (dir-ent-clusterchain
           (mv-nth 0
                   (place-contents fat32-in-memory dir-ent2
                                   contents file-length first-cluster))
           dir-ent1)
          (dir-ent-clusterchain fat32-in-memory dir-ent1)))
  :hints (("goal" :in-theory (enable dir-ent-clusterchain))))

(defthm
  dir-ent-clusterchain-contents-of-place-contents-disjoint
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (force (integerp first-cluster))
    (>= first-cluster *ms-first-data-cluster*)
    (stringp contents)
    (dir-ent-p dir-ent1)
    (not
     (member-equal first-cluster
                   (mv-nth 0
                           (dir-ent-clusterchain fat32-in-memory dir-ent1))))
    (equal (mv-nth 1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent1))
           0))
   (equal (dir-ent-clusterchain-contents
           (mv-nth 0
                   (place-contents fat32-in-memory dir-ent2
                                   contents file-length first-cluster))
           dir-ent1)
          (dir-ent-clusterchain-contents fat32-in-memory dir-ent1)))
  :hints (("goal" :in-theory (enable dir-ent-clusterchain-contents
                                     dir-ent-clusterchain))))

(defthm
  lofat-to-hifat-helper-of-place-contents
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (stringp contents)
        (force (integerp first-cluster))
        (>= first-cluster *ms-first-data-cluster*)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32-in-memory
                                              dir-ent-list entry-limit))
               0)
        (not-intersectp-list
         (list first-cluster)
         (mv-nth 2
                 (lofat-to-hifat-helper fat32-in-memory
                                        dir-ent-list entry-limit)))
        (dir-ent-list-p dir-ent-list))
   (equal (lofat-to-hifat-helper
           (mv-nth 0
                   (place-contents fat32-in-memory dir-ent
                                   contents file-length first-cluster))
           dir-ent-list entry-limit)
          (lofat-to-hifat-helper fat32-in-memory
                                 dir-ent-list entry-limit)))
  :hints
  (("goal"
    :in-theory (enable lofat-to-hifat-helper not-intersectp-list)
    :induct (lofat-to-hifat-helper fat32-in-memory
                                   dir-ent-list entry-limit)
    :expand ((lofat-to-hifat-helper
              (mv-nth 0
                      (place-contents fat32-in-memory dir-ent
                                      contents file-length first-cluster))
              dir-ent-list entry-limit)
             (:free (y)
                    (intersectp-equal (list first-cluster)
                                      y))))))

(defthm
  fat32-build-index-list-of-effective-fat-of-place-contents-coincident
  (implies
   (and (equal (mv-nth 2
                       (place-contents fat32-in-memory dir-ent
                                       contents file-length first-cluster))
               0)
        (<= *ms-first-data-cluster* first-cluster)
        (stringp contents)
        (integerp length)
        (<= (length contents) length)
        (lofat-fs-p fat32-in-memory)
        (not (equal (fat32-entry-mask (fati first-cluster fat32-in-memory))
                    0))
        (< first-cluster
           (+ 2 (count-of-clusters fat32-in-memory)))
        (fat32-masked-entry-p first-cluster)
        (equal cluster-size
               (cluster-size fat32-in-memory)))
   (equal
    (fat32-build-index-list
     (effective-fat
      (mv-nth 0
              (place-contents fat32-in-memory dir-ent
                              contents file-length first-cluster)))
     first-cluster length cluster-size)
    (mv (cons first-cluster
              (find-n-free-clusters
               (effective-fat fat32-in-memory)
               (+ -1
                  (len (make-clusters contents
                                      (cluster-size fat32-in-memory))))))
        0)))
  :hints
  (("goal"
    :in-theory
    (e/d (place-contents)
         ((:rewrite
           fat32-build-index-list-of-set-indices-in-fa-table-coincident)))
    :use
    ((:instance
      (:rewrite fat32-build-index-list-of-set-indices-in-fa-table-coincident)
      (cluster-size (cluster-size fat32-in-memory))
      (file-length length)
      (file-index-list
       (cons first-cluster
             (find-n-free-clusters
              (effective-fat fat32-in-memory)
              (+ -1
                 (len (make-clusters contents
                                     (cluster-size fat32-in-memory)))))))
      (fa-table (effective-fat fat32-in-memory)))))))

(defthm
  dir-ent-clusterchain-of-place-contents-coincident-1
  (implies
   (and (dir-ent-directory-p dir-ent1)
        (equal (mv-nth 2
                       (place-contents fat32-in-memory dir-ent2
                                       contents file-length first-cluster))
               0)
        (equal first-cluster
               (dir-ent-first-cluster dir-ent1))
        (<= *ms-first-data-cluster* first-cluster)
        (stringp contents)
        (<= (length contents) *ms-max-dir-size*)
        (lofat-fs-p fat32-in-memory)
        (not (equal (fat32-entry-mask (fati first-cluster fat32-in-memory))
                    0))
        (< first-cluster
           (+ 2 (count-of-clusters fat32-in-memory)))
        (fat32-masked-entry-p first-cluster))
   (equal
    (dir-ent-clusterchain
     (mv-nth 0
             (place-contents fat32-in-memory dir-ent2
                             contents file-length first-cluster))
     dir-ent1)
    (mv (cons first-cluster
              (find-n-free-clusters
               (effective-fat fat32-in-memory)
               (+ -1
                  (len (make-clusters contents
                                      (cluster-size fat32-in-memory))))))
        0)))
  :hints (("goal" :in-theory (enable dir-ent-clusterchain))))

(defthm
  dir-ent-clusterchain-of-place-contents-coincident-2
  (implies
   (and (not (dir-ent-directory-p dir-ent1))
        (equal (mv-nth 2
                       (place-contents fat32-in-memory dir-ent2
                                       contents file-length first-cluster))
               0)
        (equal first-cluster
               (dir-ent-first-cluster dir-ent1))
        (<= *ms-first-data-cluster* first-cluster)
        (stringp contents)
        (<= (length contents)
            (dir-ent-file-size dir-ent1))
        (lofat-fs-p fat32-in-memory)
        (not (equal (fat32-entry-mask (fati first-cluster fat32-in-memory))
                    0))
        (< first-cluster
           (+ 2 (count-of-clusters fat32-in-memory)))
        (fat32-masked-entry-p first-cluster))
   (equal
    (dir-ent-clusterchain
     (mv-nth 0
             (place-contents fat32-in-memory dir-ent2
                             contents file-length first-cluster))
     dir-ent1)
    (mv (cons first-cluster
              (find-n-free-clusters
               (effective-fat fat32-in-memory)
               (+ -1
                  (len (make-clusters contents
                                      (cluster-size fat32-in-memory))))))
        0)))
  :hints (("goal" :in-theory (enable dir-ent-clusterchain))))

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
       (contents (m1-file->contents (cdr head)))
       ;; "." and ".." entries are not even allowed to be part of an
       ;; m1-file-alist, so we can use mbt to wipe out this clause...
       ((unless (mbt (and (not (equal (car head) *current-dir-fat32-name*))
                          (not (equal (car head) *parent-dir-fat32-name*)))))
        (mv fat32-in-memory tail-list errno tail-index-list))
       ;; Get the directory entry for the first file in this directory.
       (dir-ent (m1-file->dir-ent (cdr head)))
       ((when (and (m1-regular-file-p (cdr head)) (equal (length contents) 0)))
        (mv fat32-in-memory
            (list*
             (dir-ent-install-directory-bit
              (dir-ent-set-filename
               (dir-ent-set-first-cluster-file-size dir-ent 0 0)
               (mbe :exec (car head) :logic (fat32-filename-fix (car head))))
              nil)
             tail-list)
            0
            tail-index-list))
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
        (b* ((file-length (length contents))
             ((mv fat32-in-memory dir-ent errno head-index-list)
              (place-contents fat32-in-memory
                              dir-ent contents file-length first-cluster))
             (dir-ent (dir-ent-set-filename
                       dir-ent
                       (mbe :exec (car head) :logic (fat32-filename-fix (car head)))))
             (dir-ent
              (dir-ent-install-directory-bit
               dir-ent nil)))
          (mv fat32-in-memory
              (list* dir-ent tail-list)
              errno
              (append head-index-list tail-index-list)))
      (b* ((file-length 0)
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
           (dir-ent (dir-ent-set-filename
                     dir-ent
                     (mbe :exec (car head) :logic (fat32-filename-fix (car head)))))
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

(defthm
  natp-of-hifat-to-lofat-helper
  (implies
   (not
    (equal
     (mv-nth
      2
      (hifat-to-lofat-helper fat32-in-memory
                             fs current-dir-first-cluster))
     0))
   (equal
    (mv-nth
     2
     (hifat-to-lofat-helper fat32-in-memory
                            fs current-dir-first-cluster))
    *enospc*))
  :rule-classes
  (:rewrite
   (:type-prescription
    :corollary
    (natp
     (mv-nth
      2
      (hifat-to-lofat-helper fat32-in-memory
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
    :in-theory (disable stobj-set-indices-in-fa-table))))

(defthm
  dir-ent-list-p-of-hifat-to-lofat-helper
  (dir-ent-list-p
   (mv-nth 1
           (hifat-to-lofat-helper
            fat32-in-memory fs first-cluster))))

(defthm
  useful-dir-ent-list-p-of-hifat-to-lofat-helper
  (useful-dir-ent-list-p
   (mv-nth 1
           (hifat-to-lofat-helper fat32-in-memory fs first-cluster)))
  :hints (("goal" :in-theory (enable useful-dir-ent-list-p))))

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

(defthm
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
       (painful-debugging-lemma-9)
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
    (("goal" :in-theory (e/d (hifat-to-lofat-guard-lemma-1)
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
                             (count-of-clusters fat32-in-memory)))))))))
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
  (natp (mv-nth 1 (hifat-to-lofat fat32-in-memory fs)))
  :rule-classes :type-prescription
  :hints (("goal" :in-theory (enable hifat-to-lofat))))

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
                       hifat-to-lofat-guard-lemma-1)
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
       '1))))))

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
          (fati x fat32-in-memory))))

(defthm
  place-contents-expansion-1
  (and
   (implies
    (zp (mv-nth 2
                (place-contents fat32-in-memory dir-ent
                                contents file-length first-cluster)))
    (equal
     (mv-nth 1
             (place-contents fat32-in-memory dir-ent
                             contents file-length first-cluster))
     (dir-ent-set-first-cluster-file-size dir-ent first-cluster file-length)))
   (implies
    (not
     (zp (mv-nth 2
                 (place-contents fat32-in-memory dir-ent
                                 contents file-length first-cluster))))
    (equal
     (mv-nth 1
             (place-contents fat32-in-memory dir-ent
                             contents file-length first-cluster))
     (dir-ent-fix dir-ent))))
  :hints
  (("goal" :in-theory (enable place-contents
                              (:rewrite make-clusters-correctness-1 . 1)))))

(defthm
  place-contents-expansion-2
  (and
   (implies
    (equal
     (+ 1
        (len (stobj-find-n-free-clusters
              fat32-in-memory
              (+ -1
                 (len (make-clusters contents
                                     (cluster-size fat32-in-memory)))))))
     (len (make-clusters contents
                         (cluster-size fat32-in-memory))))
    (equal
     (mv-nth 2
             (place-contents fat32-in-memory dir-ent
                             contents file-length first-cluster))
     0))
   (implies
    (not
     (equal
      (+ 1
         (len (stobj-find-n-free-clusters
               fat32-in-memory
               (+ -1
                  (len (make-clusters contents
                                      (cluster-size fat32-in-memory)))))))
      (len (make-clusters contents
                          (cluster-size fat32-in-memory)))))
    (equal
     (mv-nth 2
             (place-contents fat32-in-memory dir-ent
                             contents file-length first-cluster))
     *enospc*)))
  :hints
  (("goal" :in-theory (enable place-contents
                              (:rewrite make-clusters-correctness-1 . 1)))))

(defthm
  make-dir-ent-list-of-append-1
  (implies (dir-ent-p (chars=>nats x))
           (equal (make-dir-ent-list (implode (append x y)))
                  (if (equal (char (dir-ent-filename (chars=>nats x))
                                   0)
                             (code-char 0))
                      nil
                    (if (useless-dir-ent-p (chars=>nats x))
                        (make-dir-ent-list (implode y))
                      (cons (chars=>nats x)
                            (make-dir-ent-list (implode y)))))))
  :hints (("goal" :in-theory (enable make-dir-ent-list len-when-dir-ent-p)
           :use (:instance (:rewrite len-when-dir-ent-p)
                           (dir-ent (chars=>nats x)))
           :expand (make-dir-ent-list (implode (append x y))))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (local
   (defthmd
     make-dir-ent-list-of-append-2-lemma-1
     (implies (and (character-listp y)
                   (or (< (len y) *ms-dir-ent-length*)
                       (equal (nth 0 y) (code-char 0)))
                   (equal (mod (len (explode x))
                               *ms-dir-ent-length*)
                          0))
              (equal (make-dir-ent-list (implode (append (explode x) y)))
                     (make-dir-ent-list x)))
     :hints (("goal" :in-theory (enable make-dir-ent-list flatten dir-ent-p)
              :induct (make-dir-ent-list x)))))

  (defthm
    make-dir-ent-list-of-append-2
    (implies (and (character-listp y)
                  (or (< (len y) *ms-dir-ent-length*)
                      (equal (nth 0 y) (code-char 0)))
                  (equal (mod (len x)
                              *ms-dir-ent-length*)
                         0)
                  (character-listp x))
             (equal (make-dir-ent-list (implode (append x y)))
                    (make-dir-ent-list (implode x))))
    :hints (("goal" :do-not-induct t
             :use (:instance
                   make-dir-ent-list-of-append-2-lemma-1
                   (x (implode x)))))))

(defthm
  make-dir-ent-list-of-implode-of-make-list-ac-1
  (implies
   (not (zp n))
   (equal (make-dir-ent-list (implode (make-list-ac n (code-char 0) ac)))
          nil))
  :hints
  (("goal"
    :in-theory (e/d (make-dir-ent-list) (make-list-ac))
    :expand
    ((:free (val)
            (make-dir-ent-list (implode (make-list-ac n val ac))))
     (:free (val)
            (dir-ent-fix (chars=>nats (take *ms-dir-ent-length*
                                            (make-list-ac n val ac)))))))))

(defthm
  make-dir-ent-list-inversion
  (implies
   (useful-dir-ent-list-p dir-ent-list)
   (equal (make-dir-ent-list (implode (nats=>chars (flatten dir-ent-list))))
          dir-ent-list))
  :hints (("goal" :in-theory (enable useful-dir-ent-list-p
                                     make-dir-ent-list flatten))))

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

;; I know the two following definitions should really look more alike, but they
;; just happened to develop for different purposes.
(defun free-index-listp (index-list fa-table)
  (declare (xargs :guard (and (fat32-entry-list-p fa-table)
                              (bounded-nat-listp index-list (len fa-table)))))
  (or (atom index-list)
      (and (equal (fat32-entry-mask (nth (car index-list) fa-table)) 0)
           (free-index-listp (cdr index-list) fa-table))))

(defun
    non-free-index-listp (x fa-table)
  (if
      (atom x)
      (equal x nil)
    (and (integerp (car x))
         (<= *ms-first-data-cluster* (car x))
         (< (car x) (len fa-table))
         (not (equal (fat32-entry-mask (nth (car x) fa-table))
                     0))
         (non-free-index-listp (cdr x)
                               fa-table))))

(defthm
  non-free-index-listp-of-update-nth
  (implies
   (and (not (member-equal key x))
        (< key (len fa-table)))
   (equal (non-free-index-listp x (update-nth key val fa-table))
          (non-free-index-listp x fa-table))))

(defthm
  non-free-index-listp-of-set-indices-in-fa-table
  (implies (and (non-free-index-listp x fa-table)
                (not (intersectp-equal index-list x)))
           (non-free-index-listp
            x
            (set-indices-in-fa-table fa-table index-list value-list)))
  :hints
  (("goal" :in-theory (enable set-indices-in-fa-table
                              intersectp-equal)
    :induct (set-indices-in-fa-table fa-table index-list value-list))))

(defthm
  non-free-index-listp-correctness-2
  (implies (and (non-free-index-listp x fa-table)
                (equal (fat32-entry-mask (nth key fa-table))
                       0))
           (not (member-equal key x)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (non-free-index-listp x fa-table)
          (equal (fat32-entry-mask (nth key fa-table))
                 0)
          (< key (len fa-table)))
     (non-free-index-listp x (update-nth key val fa-table))))))

(defthm
  free-index-listp-correctness-1
  (implies (and (free-index-listp x fa-table)
                (not (equal (fat32-entry-mask (nth key fa-table))
                            0)))
           (not (member-equal key x))))

(defthm
  non-free-index-listp-correctness-3
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (non-free-index-listp x (effective-fat fat32-in-memory))
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
   (non-free-index-listp
    x
    (effective-fat
     (mv-nth
      0
      (place-contents fat32-in-memory dir-ent
                      contents file-length first-cluster))))))

(defthm
  non-free-index-listp-correctness-4-lemma-1
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (< (nfix n2)
           (len (find-n-free-clusters (effective-fat fat32-in-memory)
                                      n1))))
   (equal
    (fat32-entry-mask
     (fati (nth n2
                (find-n-free-clusters (effective-fat fat32-in-memory)
                                      n1))
           fat32-in-memory))
    0))
  :hints
  (("goal" :do-not-induct t
    :in-theory (disable find-n-free-clusters-correctness-5)
    :use ((:instance find-n-free-clusters-correctness-5
                     (fa-table (effective-fat fat32-in-memory)))))))

(defthm
  non-free-index-listp-correctness-4
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (equal (mv-nth 2
                       (hifat-to-lofat-helper
                        fat32-in-memory
                        fs current-dir-first-cluster))
               0)
        (non-free-index-listp x (effective-fat fat32-in-memory)))
   (non-free-index-listp
    x
    (effective-fat
     (mv-nth 0
             (hifat-to-lofat-helper
              fat32-in-memory
              fs current-dir-first-cluster))))))

(defthm
  non-free-index-listp-correctness-5
  (implies
   (and (non-free-index-listp x fa-table)
        (natp n)
        (fat32-entry-list-p fa-table))
   (not (intersectp-equal x (find-n-free-clusters fa-table n))))
  :hints (("goal" :in-theory (enable intersectp-equal))))

(defthm
  non-free-index-listp-of-append
  (equal (non-free-index-listp (append x y) fa-table)
         (and
          (non-free-index-listp (true-list-fix x) fa-table)
          (non-free-index-listp y fa-table))))

(defthm
  non-free-index-listp-of-fat32-build-index-list
  (implies
   (and (equal (mv-nth 1
                       (fat32-build-index-list fa-table masked-current-cluster
                                               length cluster-size))
               0)
        (integerp masked-current-cluster)
        (<= 2 masked-current-cluster)
        (< masked-current-cluster (len fa-table)))
   (non-free-index-listp
    (mv-nth 0
            (fat32-build-index-list fa-table masked-current-cluster
                                    length cluster-size))
    fa-table))
  :hints (("goal" :in-theory (enable fat32-build-index-list))))

(defthm
  free-index-listp-of-update-nth
  (implies
   (and (not (free-index-listp index-list fa-table))
        (not (equal (fat32-entry-mask val) 0)))
   (not (free-index-listp index-list
                          (update-nth key val fa-table)))))

(defthm
  count-free-clusters-of-set-indices-in-fa-table-lemma-1
  (implies (and (free-index-listp index-list fa-table)
                (lower-bounded-integer-listp index-list 2)
                (not (member-equal key index-list)))
           (free-index-listp index-list
                             (update-nth key val fa-table)))
  :hints (("goal" :in-theory (disable update-nth))))

;; It would be nice to move this, along with several other things...
(defthm
  count-free-clusters-of-set-indices-in-fa-table-1
  (implies
   (and (non-free-index-listp index-list fa-table)
        (no-duplicatesp-equal index-list))
   (equal
    (count-free-clusters
     (set-indices-in-fa-table fa-table index-list
                              (make-list-ac (len index-list) 0 nil)))
    (+ (count-free-clusters fa-table)
       (len index-list))))
  :hints
  (("goal" :in-theory (enable set-indices-in-fa-table)
    :induct (set-indices-in-fa-table fa-table index-list
                                     (make-list-ac (len index-list)
                                                   0 nil))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (non-free-index-listp index-list fa-table)
          (no-duplicatesp-equal index-list)
          (equal n (len index-list)))
     (equal
      (count-free-clusters
       (set-indices-in-fa-table fa-table index-list
                                (make-list-ac n 0 nil)))
      (+ (count-free-clusters fa-table)
         (len index-list)))))))
(defthm count-free-clusters-of-set-indices-in-fa-table-2
  (implies
   (and (free-index-listp index-list fa-table)
        (bounded-nat-listp index-list (len fa-table))
        (lower-bounded-integer-listp index-list 2)
        (not (member-equal 0 value-list))
        (fat32-masked-entry-list-p value-list)
        (no-duplicatesp-equal index-list)
        (equal (len index-list)
               (len value-list)))
   (equal (count-free-clusters
           (set-indices-in-fa-table fa-table index-list value-list))
          (- (count-free-clusters fa-table)
             (len index-list))))
  :hints
  (("goal" :in-theory (enable set-indices-in-fa-table)
    :induct (set-indices-in-fa-table fa-table index-list value-list))))

(defun
    non-free-index-list-listp (l fa-table)
  (or (atom l)
      (and (non-free-index-listp (car l) fa-table)
           (non-free-index-list-listp (cdr l) fa-table))))

(defthm non-free-index-list-listp-of-append
  (equal (non-free-index-list-listp (append x y)
                                    fa-table)
         (and (non-free-index-list-listp x fa-table)
              (non-free-index-list-listp y fa-table))))

(defthm
  non-free-index-listp-of-dir-ent-clusterchain
  (implies (and (<= *ms-first-data-cluster*
                    (dir-ent-first-cluster dir-ent))
                (equal (mv-nth 1
                               (dir-ent-clusterchain fat32-in-memory dir-ent))
                       0)
                (< (dir-ent-first-cluster dir-ent)
                   (+ *ms-first-data-cluster*
                      (count-of-clusters fat32-in-memory))))
           (non-free-index-listp
            (mv-nth 0
                    (dir-ent-clusterchain fat32-in-memory dir-ent))
            (effective-fat fat32-in-memory)))
  :hints (("goal" :in-theory (enable dir-ent-clusterchain))))

(defthm
  non-free-index-list-listp-of-lofat-to-hifat-helper
  (b* (((mv & & clusterchain-list error-code)
        (lofat-to-hifat-helper fat32-in-memory
                               dir-ent-list entry-limit)))
    (implies (equal error-code 0)
             (non-free-index-list-listp
              clusterchain-list
              (effective-fat fat32-in-memory))))
  :hints
  (("goal"
    :in-theory (enable lofat-to-hifat-helper)
    :induct
    (lofat-to-hifat-helper fat32-in-memory
                           dir-ent-list entry-limit))))

;; Disabling this because otherwise it'll get tried for every intersectp-equal
;; term on earth.
(defthmd non-free-index-list-listp-correctness-1-lemma-1
  (implies (and (non-free-index-listp x fa-table)
                (free-index-listp index-list fa-table))
           (not (intersectp-equal index-list x)))
  :hints (("goal" :in-theory (enable intersectp-equal not-intersectp-list))))

(defthm
  non-free-index-list-listp-correctness-1
  (implies (and (free-index-listp index-list fa-table)
                (non-free-index-list-listp l fa-table))
           (not-intersectp-list index-list l))
  :hints
  (("goal"
    :in-theory
    (enable non-free-index-list-listp-correctness-1-lemma-1
            not-intersectp-list))))

(defthm non-free-index-list-listp-of-update-nth
  (implies (and (non-free-index-list-listp l fa-table)
                (not-intersectp-list (list key) l))
           (non-free-index-list-listp l (update-nth key val fa-table)))
  :hints (("goal" :induct t
           :in-theory (e/d (not-intersectp-list)
                           (intersectp-is-commutative))
           :expand ((intersectp-equal (list key) (car l))
                    (intersectp-equal nil (car l))))))

(defthm
  non-free-index-list-listp-of-set-indices-in-fa-table
  (implies (and (non-free-index-list-listp l fa-table)
                (not-intersectp-list index-list l))
           (non-free-index-list-listp
            l
            (set-indices-in-fa-table fa-table index-list value-list)))
  :hints (("goal" :in-theory (enable not-intersectp-list))))

(defthm
  not-intersectp-list-of-lofat-to-hifat-helper
  (b*
      (((mv & & clusterchain-list error-code)
        (lofat-to-hifat-helper fat32-in-memory
                               dir-ent-list entry-limit)))
    (implies
     (and (equal error-code 0)
          (free-index-listp index-list
                            (effective-fat fat32-in-memory)))
     (not-intersectp-list index-list clusterchain-list)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable non-free-index-list-listp-correctness-1)
    :use
    (:instance non-free-index-list-listp-correctness-1
               (fa-table (effective-fat fat32-in-memory))
               (l (mv-nth 2
                          (lofat-to-hifat-helper
                           fat32-in-memory
                           dir-ent-list entry-limit)))))))

(defthm
  non-free-index-list-listp-correctness-2
  (implies (true-list-listp l)
           (equal (non-free-index-listp (flatten l)
                                        fa-table)
                  (non-free-index-list-listp l fa-table)))
  :hints (("goal" :in-theory (enable flatten))))

(defun
    free-index-list-listp (l fa-table)
  (or (atom l)
      (and (free-index-listp (car l) fa-table)
           (free-index-list-listp (cdr l) fa-table))))

(defthm
  free-index-list-listp-correctness-1
  (implies (and (free-index-list-listp l2 fa-table)
                (non-free-index-list-listp l1 fa-table))
           (not (member-intersectp-equal l2 l1)))
  :hints
  (("goal"
    :in-theory (disable member-intersectp-is-commutative))))

(defthm free-index-list-listp-of-append
  (equal (free-index-list-listp (append x y)
                                fa-table)
         (and (free-index-list-listp x fa-table)
              (free-index-list-listp y fa-table))))

(defthm free-index-list-listp-of-update-nth-lemma-1
  (implies (and (integerp key)
                (<= *ms-first-data-cluster* key)
                (not (member-equal key x)))
           (equal (free-index-listp x (update-nth key val fa-table))
                  (free-index-listp x fa-table)))
  :hints (("goal" :in-theory (enable update-nth))))

(defthm
  free-index-list-listp-of-update-nth
  (implies
   (and (integerp key)
        (<= *ms-first-data-cluster* key)
        (not-intersectp-list (list key) l))
   (equal
    (free-index-list-listp l (update-nth key val fa-table))
    (free-index-list-listp l fa-table)))
  :hints (("goal" :induct t
           :in-theory (e/d (not-intersectp-list)
                           (intersectp-is-commutative))
           :expand ((intersectp-equal (list key) (car l))
                    (intersectp-equal nil (car l))))))

(encapsulate
  ()

  (local
   (defun induction-scheme
       (fa-table n start)
     (declare (xargs :measure (nfix (- (len fa-table) start))))
     (if (or (zp n) (not (integerp start)) (<= (len fa-table) start))
         nil
       (if (not (equal (fat32-entry-mask (nth start fa-table))
                       0))
           (induction-scheme fa-table
                             n (+ start 1))
         (cons start
               (induction-scheme fa-table
                                 (- n 1)
                                 (+ start 1)))))))

  (defthm
    free-index-listp-of-find-n-free-clusters-helper
    (implies
     (natp start)
     (free-index-listp (find-n-free-clusters-helper (nthcdr start fa-table)
                                                    n start)
                       fa-table))
    :hints (("goal" :induct (induction-scheme fa-table n start)
             :in-theory (enable find-n-free-clusters-helper)
             :expand (find-n-free-clusters-helper fa-table n start)))))

(defthm free-index-listp-of-find-n-free-clusters
  (free-index-listp (find-n-free-clusters fa-table n)
                    fa-table)
  :hints (("goal" :in-theory (enable find-n-free-clusters))))

(defthm
  lofat-to-hifat-helper-of-hifat-to-lofat-helper-disjoint-lemma-1
  (implies (non-free-index-listp x fa-table)
           (and
            (not (intersectp-equal (find-n-free-clusters fa-table n)
                                   x))
            (not (intersectp-equal x
                                   (find-n-free-clusters fa-table n)))))
  :hints
  (("goal"
    :use (:instance (:rewrite non-free-index-list-listp-correctness-1-lemma-1)
                    (index-list (find-n-free-clusters fa-table n))))))

(defthm
  lofat-to-hifat-helper-of-hifat-to-lofat-helper-disjoint-lemma-2
  (implies (equal (mv-nth 3
                          (lofat-to-hifat-helper fat32-in-memory
                                                 dir-ent-list entry-limit))
                  0)
           (not-intersectp-list
            (find-n-free-clusters (effective-fat fat32-in-memory)
                                  n)
            (mv-nth 2
                    (lofat-to-hifat-helper fat32-in-memory
                                           dir-ent-list entry-limit))))
  :hints
  (("goal" :in-theory (enable intersectp-equal lofat-to-hifat-helper
                              not-intersectp-list)
    :induct (lofat-to-hifat-helper fat32-in-memory
                                   dir-ent-list entry-limit)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (equal n 1)
          (equal (len (find-n-free-clusters (effective-fat fat32-in-memory)
                                            n))
                 1)
          (equal (mv-nth 3
                         (lofat-to-hifat-helper fat32-in-memory
                                                dir-ent-list entry-limit))
                 0))
     (not-intersectp-list
      (cons (nth 0
                 (find-n-free-clusters (effective-fat fat32-in-memory)
                                       n))
            nil)
      (mv-nth 2
              (lofat-to-hifat-helper fat32-in-memory
                                     dir-ent-list entry-limit))))
    :hints
    (("goal"
      :in-theory (disable len-of-find-n-free-clusters)
      :expand ((len (find-n-free-clusters (effective-fat fat32-in-memory)
                                          1))
               (len (cdr (find-n-free-clusters (effective-fat fat32-in-memory)
                                               1))))
      :cases
      ((equal (list (car (find-n-free-clusters (effective-fat fat32-in-memory)
                                               1)))
              (find-n-free-clusters (effective-fat fat32-in-memory)
                                    1))))))))

(defthm
  lofat-to-hifat-helper-of-hifat-to-lofat-helper-disjoint
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32-in-memory
                                              dir-ent-list entry-limit))
               0)
        (dir-ent-list-p dir-ent-list))
   (equal (lofat-to-hifat-helper
           (mv-nth 0
                   (hifat-to-lofat-helper fat32-in-memory
                                          fs current-dir-first-cluster))
           dir-ent-list entry-limit)
          (lofat-to-hifat-helper fat32-in-memory
                                 dir-ent-list entry-limit)))
  :hints
  (("goal"
    :in-theory
    (disable (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
             (:rewrite fati-of-hifat-to-lofat-helper-disjoint-lemma-1)))))

(defthm
  free-index-listp-of-set-indices-in-fa-table-lemma-1
  (implies
   (not (equal (fat32-entry-mask val) 0))
   (free-index-listp
    (find-n-free-clusters (update-nth key val fa-table)
                          n)
    fa-table))
  :hints
  (("goal"
    :in-theory
    (disable free-index-listp-of-update-nth)
    :use
    (:instance
     free-index-listp-of-update-nth
     (index-list
      (find-n-free-clusters (update-nth key val fa-table)
                            n))))))

(defthm
  free-index-listp-of-set-indices-in-fa-table
  (implies
   (and (not (free-index-listp index-list1 fa-table))
        (fat32-masked-entry-list-p value-list)
        (lower-bounded-integer-listp value-list *ms-first-data-cluster*)
        (equal (len index-list2)
               (len value-list)))
   (not (free-index-listp
         index-list1
         (set-indices-in-fa-table fa-table index-list2 value-list))))
  :hints
  (("goal"
    :in-theory (enable set-indices-in-fa-table)
    :induct (set-indices-in-fa-table fa-table index-list2 value-list))))

(defthm
  free-index-listp-of-effective-fat-of-place-contents
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (not (free-index-listp index-list
                               (effective-fat fat32-in-memory)))
        (integerp first-cluster)
        (<= *ms-first-data-cluster* first-cluster)
        (stringp contents))
   (not
    (free-index-listp
     index-list
     (effective-fat
      (mv-nth 0
              (place-contents fat32-in-memory dir-ent
                              contents file-length first-cluster))))))
  :hints (("goal" :in-theory (enable place-contents)
           :do-not-induct t)))

(defthm
  free-index-listp-of-effective-fat-of-hifat-to-lofat-helper
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (not (free-index-listp index-list
                           (effective-fat fat32-in-memory))))
   (not
    (free-index-listp
     index-list
     (effective-fat
      (mv-nth 0
              (hifat-to-lofat-helper
               fat32-in-memory
               fs current-dir-first-cluster)))))))

(defthm
  nth-of-free-index-list
  (implies
   (and (force (< (nfix n) (len index-list)))
        (free-index-listp index-list fa-table))
   (equal (fat32-entry-mask (nth (nth n index-list) fa-table))
          0))
  :hints (("goal" :in-theory (enable nth))))

(defthm
  free-index-list-listp-of-effective-fat-of-hifat-to-lofat-helper
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (not
     (free-index-list-listp l (effective-fat fat32-in-memory))))
   (not
    (free-index-list-listp
     l
     (effective-fat
      (mv-nth
       0
       (hifat-to-lofat-helper fat32-in-memory
                              fs current-dir-first-cluster))))))
  :hints
  (("goal"
    :induct
    (free-index-list-listp l (effective-fat fat32-in-memory)))))

(defthm
  root-dir-ent-list-of-place-contents-coincident-lemma-1
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

(defthm
  root-dir-ent-list-of-place-contents-coincident
  (implies
   (and
    (equal
     (mv-nth
      2
      (place-contents fat32-in-memory
                      dir-ent contents file-length
                      (fat32-entry-mask (bpb_rootclus fat32-in-memory))))
     0)
    (not (zp (length contents)))
    (stringp contents)
    (<= (length contents) *ms-max-dir-size*)
    (lofat-fs-p fat32-in-memory)
    (not (equal (fat32-entry-mask (fati first-cluster fat32-in-memory))
                0))
    (equal first-cluster
           (fat32-entry-mask (bpb_rootclus fat32-in-memory))))
   (equal
    (root-dir-ent-list
     (mv-nth 0
             (place-contents fat32-in-memory dir-ent
                             contents file-length first-cluster)))
    (mv
     (make-dir-ent-list
      (implode
       (append
        (explode contents)
        (make-list
         (+ (min *ms-max-dir-size*
                 (* (len (make-clusters contents
                                        (cluster-size fat32-in-memory)))
                    (cluster-size fat32-in-memory)))
            (- (length contents)))
         :initial-element (code-char 0)))))
     0)))
  :hints
  (("goal"
    :in-theory (e/d (root-dir-ent-list pseudo-root-dir-ent dir-ent-clusterchain-contents)
                    (get-clusterchain-contents-of-place-contents-coincident))
    :use
    (:instance
     get-clusterchain-contents-of-place-contents-coincident
     (first-cluster (fat32-entry-mask (bpb_rootclus fat32-in-memory)))
     (length *ms-max-dir-size*)))))

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
  (("Goal" :in-theory (e/d (nth) (len-of-find-n-free-clusters))
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

(defthmd
  hifat-to-lofat-inversion-lemma-3
  (implies (and (hifat-subsetp m1-file-alist1 m1-file-alist2)
                (alistp m1-file-alist2)
                (consp (assoc-equal key m1-file-alist1)))
           (consp (assoc-equal key m1-file-alist2))))

;; Not ideal...
(defthm
  hifat-to-lofat-inversion-lemma-4
  (implies
   (hifat-equiv m1-file-alist1 m1-file-alist2)
   (equal
    (consp (assoc-equal key
                        (hifat-file-alist-fix m1-file-alist1)))
    (consp
     (assoc-equal key
                  (hifat-file-alist-fix m1-file-alist2)))))
  :hints
  (("goal"
    :expand (hifat-equiv m1-file-alist1 m1-file-alist2)
    :use
    ((:instance
      hifat-to-lofat-inversion-lemma-3
      (m1-file-alist1 (hifat-file-alist-fix m1-file-alist1))
      (m1-file-alist2 (hifat-file-alist-fix m1-file-alist2)))
     (:instance
      hifat-to-lofat-inversion-lemma-3
      (m1-file-alist1 (hifat-file-alist-fix m1-file-alist2))
      (m1-file-alist2 (hifat-file-alist-fix m1-file-alist1))))))
  :rule-classes :congruence)

(defthm
  hifat-to-lofat-inversion-lemma-5
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (<
     0
     (len
      (find-n-free-clusters
       (effective-fat
        (mv-nth '0
                (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                       current-dir-first-cluster)))
       '1))))
   (not
    (<
     (binary-+ '2
               (count-of-clusters fat32-in-memory))
     (binary-+
      '1
      (nth
       '0
       (find-n-free-clusters
        (effective-fat
         (mv-nth '0
                 (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                        current-dir-first-cluster)))
        '1))))))
  :hints (("goal" :in-theory (enable painful-debugging-lemma-13))))

(defthm
  hifat-to-lofat-inversion-lemma-6
  (implies
   (and
    (equal
     (mv-nth 3
             (lofat-to-hifat-helper
              (mv-nth 0
                      (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster))
              (mv-nth 1
                      (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster))
              (+ -1 entry-limit)))
     0)
    (lofat-fs-p fat32-in-memory)
    (<= 0
        (+ -1
           (len (make-clusters (m1-file->contents (cdr (car fs)))
                               (cluster-size fat32-in-memory)))))
    (<=
     (+ -1
        (len (make-clusters (m1-file->contents (cdr (car fs)))
                            (cluster-size fat32-in-memory))))
     (+
      -1
      (count-free-clusters
       (effective-fat
        (mv-nth 0
                (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                       current-dir-first-cluster)))))))
   (not-intersectp-list
    (cons
     (nth
      0
      (find-n-free-clusters
       (effective-fat
        (mv-nth 0
                (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                       current-dir-first-cluster)))
       1))
     (find-n-free-clusters
      (update-nth
       (nth
        0
        (find-n-free-clusters
         (effective-fat
          (mv-nth 0
                  (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                         current-dir-first-cluster)))
         1))
       (fat32-update-lower-28
        (fati
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth 0
                    (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                           current-dir-first-cluster)))
           1))
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                        current-dir-first-cluster)))
        268435455)
       (effective-fat
        (mv-nth 0
                (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                       current-dir-first-cluster))))
      (+ -1
         (len (make-clusters (m1-file->contents (cdr (car fs)))
                             (cluster-size fat32-in-memory))))))
    (mv-nth 2
            (lofat-to-hifat-helper
             (mv-nth 0
                     (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster))
             (mv-nth 1
                     (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster))
             (+ -1 entry-limit)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable (:rewrite not-intersectp-list-of-append-2))
    :use
    (:instance
     (:rewrite not-intersectp-list-of-append-2)
     (l
      (mv-nth 2
              (lofat-to-hifat-helper
               (mv-nth 0
                       (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                              current-dir-first-cluster))
               (mv-nth 1
                       (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                              current-dir-first-cluster))
               (+ -1 entry-limit))))
     (y
      (find-n-free-clusters
       (update-nth
        (nth
         0
         (find-n-free-clusters
          (effective-fat
           (mv-nth 0
                   (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
          1))
        (fat32-update-lower-28
         (fati
          (nth
           0
           (find-n-free-clusters
            (effective-fat
             (mv-nth 0
                     (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
            1))
          (mv-nth 0
                  (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                         current-dir-first-cluster)))
         268435455)
        (effective-fat
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                        current-dir-first-cluster))))
       (+ -1
          (len (make-clusters (m1-file->contents (cdr (car fs)))
                              (cluster-size fat32-in-memory))))))
     (x
      (list
       (nth
        0
        (find-n-free-clusters
         (effective-fat
          (mv-nth 0
                  (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                         current-dir-first-cluster)))
         1))))))))

(defthm
  hifat-to-lofat-inversion-lemma-7
  (implies
   (and
    (<=
     1
     (count-free-clusters
      (effective-fat
       (mv-nth
        0
        (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                               current-dir-first-cluster)))))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth
        0
        (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                               current-dir-first-cluster))
       (mv-nth
        1
        (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                               current-dir-first-cluster))
       (+ -1 entry-limit
          (- (hifat-entry-count
              (m1-file->contents (cdr (car fs))))))))
     0)
    (lofat-fs-p fat32-in-memory))
   (not-intersectp-list
    (cons
     (nth
      0
      (find-n-free-clusters
       (effective-fat
        (mv-nth
         0
         (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                current-dir-first-cluster)))
       1))
     (find-n-free-clusters
      (effective-fat
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
            (mv-nth
             0
             (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                    current-dir-first-cluster)))
           268435455)
          (mv-nth
           0
           (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                  current-dir-first-cluster)))
         (m1-file->contents (cdr (car fs)))
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth
             0
             (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                    current-dir-first-cluster)))
           1)))))
      (+
       -1
       (len
        (make-clusters
         (nats=>string
          (append
           (dir-ent-install-directory-bit
            (dir-ent-set-filename
             (dir-ent-set-first-cluster-file-size
              (m1-file->dir-ent (cdr (car fs)))
              (nth
               0
               (find-n-free-clusters
                (effective-fat
                 (mv-nth 0
                         (hifat-to-lofat-helper
                          fat32-in-memory (cdr fs)
                          current-dir-first-cluster)))
                1))
              0)
             ".          ")
            t)
           (dir-ent-install-directory-bit
            (dir-ent-set-filename
             (dir-ent-set-first-cluster-file-size
              (m1-file->dir-ent (cdr (car fs)))
              current-dir-first-cluster 0)
             "..         ")
            t)
           (flatten
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
                1)))))))
         (cluster-size fat32-in-memory))))))
    (mv-nth
     2
     (lofat-to-hifat-helper
      (mv-nth 0
              (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                     current-dir-first-cluster))
      (mv-nth 1
              (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                     current-dir-first-cluster))
      (+ -1 entry-limit
         (- (hifat-entry-count
             (m1-file->contents (cdr (car fs))))))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (disable
     (:rewrite not-intersectp-list-of-append-2)
     (:rewrite free-index-listp-of-find-n-free-clusters)
     (:rewrite
      free-index-listp-of-effective-fat-of-hifat-to-lofat-helper)
     free-index-listp-of-update-nth)
    :use
    ((:instance
      (:rewrite not-intersectp-list-of-append-2)
      (l
       (mv-nth
        2
        (lofat-to-hifat-helper
         (mv-nth
          0
          (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                 current-dir-first-cluster))
         (mv-nth
          1
          (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                 current-dir-first-cluster))
         (+ -1 entry-limit
            (- (hifat-entry-count
                (m1-file->contents (cdr (car fs)))))))))
      (y
       (find-n-free-clusters
        (effective-fat
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
            (mv-nth
             0
             (hifat-to-lofat-helper fat32-in-memory (cdr fs)
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
             1)))))
        (+
         -1
         (len
          (make-clusters
           (nats=>string
            (append
             (dir-ent-install-directory-bit
              (dir-ent-set-filename
               (dir-ent-set-first-cluster-file-size
                (m1-file->dir-ent (cdr (car fs)))
                (nth
                 0
                 (find-n-free-clusters
                  (effective-fat
                   (mv-nth 0
                           (hifat-to-lofat-helper
                            fat32-in-memory (cdr fs)
                            current-dir-first-cluster)))
                  1))
                0)
               ".          ")
              t)
             (dir-ent-install-directory-bit
              (dir-ent-set-filename
               (dir-ent-set-first-cluster-file-size
                (m1-file->dir-ent (cdr (car fs)))
                current-dir-first-cluster 0)
               "..         ")
              t)
             (flatten
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
                  1)))))))
           (cluster-size fat32-in-memory))))))
      (x
       (list
        (nth
         0
         (find-n-free-clusters
          (effective-fat
           (mv-nth
            0
            (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                   current-dir-first-cluster)))
          1)))))
     (:instance
      (:rewrite free-index-listp-of-find-n-free-clusters)
      (n
       (+
        -1
        (len
         (make-clusters
          (nats=>string
           (append
            (dir-ent-install-directory-bit
             (dir-ent-set-filename
              (dir-ent-set-first-cluster-file-size
               (m1-file->dir-ent (cdr (car fs)))
               (nth
                0
                (find-n-free-clusters
                 (effective-fat
                  (mv-nth 0
                          (hifat-to-lofat-helper
                           fat32-in-memory (cdr fs)
                           current-dir-first-cluster)))
                 1))
               0)
              ".          ")
             t)
            (dir-ent-install-directory-bit
             (dir-ent-set-filename
              (dir-ent-set-first-cluster-file-size
               (m1-file->dir-ent (cdr (car fs)))
               current-dir-first-cluster 0)
              "..         ")
             t)
            (flatten
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
                 1)))))))
          (cluster-size fat32-in-memory)))))
      (fa-table
       (effective-fat
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
           (mv-nth
            0
            (hifat-to-lofat-helper fat32-in-memory (cdr fs)
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
            1)))))))
     (:instance
      (:rewrite
       free-index-listp-of-effective-fat-of-hifat-to-lofat-helper)
      (current-dir-first-cluster
       (nth
        0
        (find-n-free-clusters
         (effective-fat
          (mv-nth
           0
           (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                  current-dir-first-cluster)))
         1)))
      (fs (m1-file->contents (cdr (car fs))))
      (fat32-in-memory
       (update-fati
        (nth
         0
         (find-n-free-clusters
          (effective-fat
           (mv-nth
            0
            (hifat-to-lofat-helper fat32-in-memory (cdr fs)
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
          (mv-nth
           0
           (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                  current-dir-first-cluster)))
         268435455)
        (mv-nth
         0
         (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                current-dir-first-cluster))))
      (index-list
       (find-n-free-clusters
        (effective-fat
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
            (mv-nth
             0
             (hifat-to-lofat-helper fat32-in-memory (cdr fs)
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
             1)))))
        (+
         -1
         (len
          (make-clusters
           (nats=>string
            (append
             (dir-ent-install-directory-bit
              (dir-ent-set-filename
               (dir-ent-set-first-cluster-file-size
                (m1-file->dir-ent (cdr (car fs)))
                (nth
                 0
                 (find-n-free-clusters
                  (effective-fat
                   (mv-nth 0
                           (hifat-to-lofat-helper
                            fat32-in-memory (cdr fs)
                            current-dir-first-cluster)))
                  1))
                0)
               ".          ")
              t)
             (dir-ent-install-directory-bit
              (dir-ent-set-filename
               (dir-ent-set-first-cluster-file-size
                (m1-file->dir-ent (cdr (car fs)))
                current-dir-first-cluster 0)
               "..         ")
              t)
             (flatten
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
                  1)))))))
           (cluster-size fat32-in-memory)))))))
     (:instance
      free-index-listp-of-update-nth
      (fa-table
       (effective-fat
        (mv-nth
         0
         (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                current-dir-first-cluster))))
      (val
       (fat32-update-lower-28
        (fati
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth
             0
             (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                    current-dir-first-cluster)))
           1))
         (mv-nth
          0
          (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                 current-dir-first-cluster)))
        268435455))
      (key
       (nth
        0
        (find-n-free-clusters
         (effective-fat
          (mv-nth
           0
           (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                  current-dir-first-cluster)))
         1)))
      (index-list
       (find-n-free-clusters
        (effective-fat
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
            (mv-nth
             0
             (hifat-to-lofat-helper fat32-in-memory (cdr fs)
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
             1)))))
        (+
         -1
         (len
          (make-clusters
           (nats=>string
            (append
             (dir-ent-install-directory-bit
              (dir-ent-set-filename
               (dir-ent-set-first-cluster-file-size
                (m1-file->dir-ent (cdr (car fs)))
                (nth
                 0
                 (find-n-free-clusters
                  (effective-fat
                   (mv-nth 0
                           (hifat-to-lofat-helper
                            fat32-in-memory (cdr fs)
                            current-dir-first-cluster)))
                  1))
                0)
               ".          ")
              t)
             (dir-ent-install-directory-bit
              (dir-ent-set-filename
               (dir-ent-set-first-cluster-file-size
                (m1-file->dir-ent (cdr (car fs)))
                current-dir-first-cluster 0)
               "..         ")
              t)
             (flatten
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
                  1)))))))
           (cluster-size fat32-in-memory)))))))))))

;; This is weird, but it's needed in order to discharge a subgoal... Still,
;; there's no reason for it to be non-local.
(local
 (defthm
   hifat-to-lofat-inversion-lemma-8
   (implies
    (not-intersectp-list
     (cons
      (nth
       0
       (find-n-free-clusters
        (effective-fat
         (mv-nth
          0
          (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                 current-dir-first-cluster)))
        1))
      x)
     (mv-nth 2 l))
    (and
     (not-intersectp-list
      (list
       (nth
        0
        (find-n-free-clusters
         (effective-fat
          (mv-nth
           0
           (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                  current-dir-first-cluster)))
         1)))
      (mv-nth 2 l))
     (not-intersectp-list x (mv-nth 2 l))))
   :hints
   (("goal"
     :in-theory
     (disable (:rewrite not-intersectp-list-of-append-2))
     :use
     (:instance
      (:rewrite not-intersectp-list-of-append-2)
      (l (mv-nth 2 l))
      (y x)
      (x
       (list
        (nth
         0
         (find-n-free-clusters
          (effective-fat
           (mv-nth
            0
            (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                   current-dir-first-cluster)))
          1)))))))))

(defthm
  hifat-to-lofat-inversion-lemma-9
  (implies
   (and
    (equal
     (mv-nth
      3
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
                     (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
            1))
          (fat32-update-lower-28
           (fati
            (nth
             0
             (find-n-free-clusters
              (effective-fat
               (mv-nth 0
                       (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                              current-dir-first-cluster)))
              1))
            (mv-nth 0
                    (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                           current-dir-first-cluster)))
           268435455)
          (mv-nth 0
                  (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                         current-dir-first-cluster)))
         (m1-file->contents (cdr (car fs)))
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth 0
                    (hifat-to-lofat-helper fat32-in-memory (cdr fs)
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
                     (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
            1))
          (fat32-update-lower-28
           (fati
            (nth
             0
             (find-n-free-clusters
              (effective-fat
               (mv-nth 0
                       (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                              current-dir-first-cluster)))
              1))
            (mv-nth 0
                    (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                           current-dir-first-cluster)))
           268435455)
          (mv-nth 0
                  (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                         current-dir-first-cluster)))
         (m1-file->contents (cdr (car fs)))
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth 0
                    (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                           current-dir-first-cluster)))
           1))))
       (+ -1 entry-limit)))
     0)
    (not-intersectp-list
     (cons
      (nth
       0
       (find-n-free-clusters
        (effective-fat
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory (cdr fs)
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
                     (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
            1))
          (fat32-update-lower-28
           (fati
            (nth
             0
             (find-n-free-clusters
              (effective-fat
               (mv-nth 0
                       (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                              current-dir-first-cluster)))
              1))
            (mv-nth 0
                    (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                           current-dir-first-cluster)))
           268435455)
          (mv-nth 0
                  (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                         current-dir-first-cluster)))
         (m1-file->contents (cdr (car fs)))
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth 0
                    (hifat-to-lofat-helper fat32-in-memory (cdr fs)
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
                     (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
            1))
          (fat32-update-lower-28
           (fati
            (nth
             0
             (find-n-free-clusters
              (effective-fat
               (mv-nth 0
                       (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                              current-dir-first-cluster)))
              1))
            (mv-nth 0
                    (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                           current-dir-first-cluster)))
           268435455)
          (mv-nth 0
                  (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                         current-dir-first-cluster)))
         (m1-file->contents (cdr (car fs)))
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth 0
                    (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                           current-dir-first-cluster)))
           1))))
       (+ -1 entry-limit)))))
   (not-intersectp-list
    (cons
     (nth
      0
      (find-n-free-clusters
       (effective-fat
        (mv-nth 0
                (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                       current-dir-first-cluster)))
       1))
     (find-n-free-clusters
      (effective-fat
       (mv-nth
        0
        (hifat-to-lofat-helper
         (update-fati
          (nth
           0
           (find-n-free-clusters
            (effective-fat
             (mv-nth 0
                     (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
            1))
          (fat32-update-lower-28
           (fati
            (nth
             0
             (find-n-free-clusters
              (effective-fat
               (mv-nth 0
                       (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                              current-dir-first-cluster)))
              1))
            (mv-nth 0
                    (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                           current-dir-first-cluster)))
           268435455)
          (mv-nth 0
                  (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                         current-dir-first-cluster)))
         (m1-file->contents (cdr (car fs)))
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth 0
                    (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                           current-dir-first-cluster)))
           1)))))
      (+
       -1
       (len
        (make-clusters
         (nats=>string
          (append
           (dir-ent-install-directory-bit
            (dir-ent-set-filename
             (dir-ent-set-first-cluster-file-size
              (m1-file->dir-ent (cdr (car fs)))
              (nth
               0
               (find-n-free-clusters
                (effective-fat
                 (mv-nth 0
                         (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster)))
                1))
              0)
             ".          ")
            t)
           (dir-ent-install-directory-bit
            (dir-ent-set-filename (dir-ent-set-first-cluster-file-size
                                   (m1-file->dir-ent (cdr (car fs)))
                                   current-dir-first-cluster 0)
                                  "..         ")
            t)
           (flatten
            (mv-nth
             1
             (hifat-to-lofat-helper
              (update-fati
               (nth
                0
                (find-n-free-clusters
                 (effective-fat
                  (mv-nth 0
                          (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
                 1))
               (fat32-update-lower-28
                (fati
                 (nth
                  0
                  (find-n-free-clusters
                   (effective-fat
                    (mv-nth
                     0
                     (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
                   1))
                 (mv-nth 0
                         (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster)))
                268435455)
               (mv-nth 0
                       (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                              current-dir-first-cluster)))
              (m1-file->contents (cdr (car fs)))
              (nth
               0
               (find-n-free-clusters
                (effective-fat
                 (mv-nth 0
                         (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster)))
                1)))))))
         (cluster-size fat32-in-memory))))))
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
                    (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                           current-dir-first-cluster)))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
             1))
           (mv-nth 0
                   (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
          268435455)
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                        current-dir-first-cluster)))
        (m1-file->contents (cdr (car fs)))
        (nth
         0
         (find-n-free-clusters
          (effective-fat
           (mv-nth 0
                   (hifat-to-lofat-helper fat32-in-memory (cdr fs)
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
                    (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                           current-dir-first-cluster)))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
             1))
           (mv-nth 0
                   (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
          268435455)
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                        current-dir-first-cluster)))
        (m1-file->contents (cdr (car fs)))
        (nth
         0
         (find-n-free-clusters
          (effective-fat
           (mv-nth 0
                   (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
          1))))
      (+ -1 entry-limit)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable (:rewrite not-intersectp-list-of-append-2))
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
                      (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
             1))
           (fat32-update-lower-28
            (fati
             (nth
              0
              (find-n-free-clusters
               (effective-fat
                (mv-nth 0
                        (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                               current-dir-first-cluster)))
               1))
             (mv-nth 0
                     (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
            268435455)
           (mv-nth 0
                   (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
          (m1-file->contents (cdr (car fs)))
          (nth
           0
           (find-n-free-clusters
            (effective-fat
             (mv-nth 0
                     (hifat-to-lofat-helper fat32-in-memory (cdr fs)
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
                      (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
             1))
           (fat32-update-lower-28
            (fati
             (nth
              0
              (find-n-free-clusters
               (effective-fat
                (mv-nth 0
                        (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                               current-dir-first-cluster)))
               1))
             (mv-nth 0
                     (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
            268435455)
           (mv-nth 0
                   (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
          (m1-file->contents (cdr (car fs)))
          (nth
           0
           (find-n-free-clusters
            (effective-fat
             (mv-nth 0
                     (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
            1))))
        (+ -1 entry-limit))))
     (y
      (find-n-free-clusters
       (effective-fat
        (mv-nth
         0
         (hifat-to-lofat-helper
          (update-fati
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
             1))
           (fat32-update-lower-28
            (fati
             (nth
              0
              (find-n-free-clusters
               (effective-fat
                (mv-nth 0
                        (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                               current-dir-first-cluster)))
               1))
             (mv-nth 0
                     (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
            268435455)
           (mv-nth 0
                   (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
          (m1-file->contents (cdr (car fs)))
          (nth
           0
           (find-n-free-clusters
            (effective-fat
             (mv-nth 0
                     (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
            1)))))
       (+
        -1
        (len
         (make-clusters
          (nats=>string
           (append
            (dir-ent-install-directory-bit
             (dir-ent-set-filename
              (dir-ent-set-first-cluster-file-size
               (m1-file->dir-ent (cdr (car fs)))
               (nth
                0
                (find-n-free-clusters
                 (effective-fat
                  (mv-nth 0
                          (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
                 1))
               0)
              ".          ")
             t)
            (dir-ent-install-directory-bit
             (dir-ent-set-filename (dir-ent-set-first-cluster-file-size
                                    (m1-file->dir-ent (cdr (car fs)))
                                    current-dir-first-cluster 0)
                                   "..         ")
             t)
            (flatten
             (mv-nth
              1
              (hifat-to-lofat-helper
               (update-fati
                (nth
                 0
                 (find-n-free-clusters
                  (effective-fat
                   (mv-nth 0
                           (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
                  1))
                (fat32-update-lower-28
                 (fati
                  (nth
                   0
                   (find-n-free-clusters
                    (effective-fat
                     (mv-nth
                      0
                      (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
                    1))
                  (mv-nth 0
                          (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
                 268435455)
                (mv-nth 0
                        (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                               current-dir-first-cluster)))
               (m1-file->contents (cdr (car fs)))
               (nth
                0
                (find-n-free-clusters
                 (effective-fat
                  (mv-nth 0
                          (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
                 1)))))))
          (cluster-size fat32-in-memory))))))
     (x
      (list
       (nth
        0
        (find-n-free-clusters
         (effective-fat
          (mv-nth 0
                  (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                         current-dir-first-cluster)))
         1))))))))

(defthm
  hifat-to-lofat-inversion-lemma-10
  (implies
   (and (< (nfix n) (len index-list))
        (free-index-listp index-list
                          (effective-fat fat32-in-memory))
        (< (nfix (nth n index-list))
           (nfix (+ (count-of-clusters fat32-in-memory)
                    2))))
   (equal (fat32-entry-mask (fati (nth n index-list)
                                  fat32-in-memory))
          0))
  :hints
  (("goal"
    :in-theory (disable (:rewrite nth-of-effective-fat)
                        (:rewrite nth-of-free-index-list))
    :use
    ((:instance (:rewrite nth-of-effective-fat)
                (n (nth n index-list)))
     (:instance (:rewrite nth-of-free-index-list)
                (fa-table (effective-fat fat32-in-memory)))))))

(defthm
  hifat-to-lofat-inversion-lemma-11
  (implies
   (and
    (<=
     1
     (count-free-clusters
      (effective-fat
       (mv-nth 0
               (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                      current-dir-first-cluster)))))
    (lofat-fs-p fat32-in-memory))
   (equal
    (fat32-entry-mask
     (fati
      (nth
       0
       (find-n-free-clusters
        (effective-fat
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                        current-dir-first-cluster)))
        1))
      fat32-in-memory))
    0))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (disable
     (:rewrite free-index-listp-of-find-n-free-clusters)
     (:rewrite free-index-listp-of-effective-fat-of-hifat-to-lofat-helper))
    :use
    ((:instance
      (:rewrite free-index-listp-of-find-n-free-clusters)
      (n 1)
      (fa-table
       (effective-fat
        (mv-nth 0
                (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                       current-dir-first-cluster)))))
     (:instance
      (:rewrite free-index-listp-of-effective-fat-of-hifat-to-lofat-helper)
      (current-dir-first-cluster current-dir-first-cluster)
      (fs (cdr fs))
      (fat32-in-memory fat32-in-memory)
      (index-list
       (find-n-free-clusters
        (effective-fat
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                        current-dir-first-cluster)))
        1)))))))

(defthm
  hifat-to-lofat-inversion-lemma-12
  (implies
   (and
    (<=
     1
     (count-free-clusters
      (effective-fat
       (mv-nth 0
               (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                      current-dir-first-cluster)))))
    (lofat-fs-p fat32-in-memory))
   (free-index-listp
    (find-n-free-clusters
     (effective-fat
      (mv-nth
       0
       (hifat-to-lofat-helper
        (update-fati
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth 0
                    (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                           current-dir-first-cluster)))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
             1))
           (mv-nth 0
                   (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
          268435455)
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                        current-dir-first-cluster)))
        (m1-file->contents (cdr (car fs)))
        (nth
         0
         (find-n-free-clusters
          (effective-fat
           (mv-nth 0
                   (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
          1)))))
     (+
      -1
      (len
       (make-clusters
        (nats=>string
         (append
          (dir-ent-install-directory-bit
           (dir-ent-set-filename
            (dir-ent-set-first-cluster-file-size
             (m1-file->dir-ent (cdr (car fs)))
             (nth
              0
              (find-n-free-clusters
               (effective-fat
                (mv-nth 0
                        (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                               current-dir-first-cluster)))
               1))
             0)
            ".          ")
           t)
          (dir-ent-install-directory-bit
           (dir-ent-set-filename (dir-ent-set-first-cluster-file-size
                                  (m1-file->dir-ent (cdr (car fs)))
                                  current-dir-first-cluster 0)
                                 "..         ")
           t)
          (flatten
           (mv-nth
            1
            (hifat-to-lofat-helper
             (update-fati
              (nth
               0
               (find-n-free-clusters
                (effective-fat
                 (mv-nth 0
                         (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster)))
                1))
              (fat32-update-lower-28
               (fati
                (nth
                 0
                 (find-n-free-clusters
                  (effective-fat
                   (mv-nth 0
                           (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
                  1))
                (mv-nth 0
                        (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                               current-dir-first-cluster)))
               268435455)
              (mv-nth 0
                      (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
             (m1-file->contents (cdr (car fs)))
             (nth
              0
              (find-n-free-clusters
               (effective-fat
                (mv-nth 0
                        (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                               current-dir-first-cluster)))
               1)))))))
        (cluster-size fat32-in-memory)))))
    (effective-fat fat32-in-memory)))
  :hints
  (("goal"
    :in-theory
    (disable
     (:rewrite free-index-listp-of-find-n-free-clusters)
     (:rewrite free-index-listp-of-effective-fat-of-hifat-to-lofat-helper))
    :use
    ((:instance
      (:rewrite free-index-listp-of-find-n-free-clusters)
      (n
       (+
        -1
        (len
         (make-clusters
          (nats=>string
           (append
            (dir-ent-install-directory-bit
             (dir-ent-set-filename
              (dir-ent-set-first-cluster-file-size
               (m1-file->dir-ent (cdr (car fs)))
               (nth
                0
                (find-n-free-clusters
                 (effective-fat
                  (mv-nth 0
                          (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
                 1))
               0)
              ".          ")
             t)
            (dir-ent-install-directory-bit
             (dir-ent-set-filename (dir-ent-set-first-cluster-file-size
                                    (m1-file->dir-ent (cdr (car fs)))
                                    current-dir-first-cluster 0)
                                   "..         ")
             t)
            (flatten
             (mv-nth
              1
              (hifat-to-lofat-helper
               (update-fati
                (nth
                 0
                 (find-n-free-clusters
                  (effective-fat
                   (mv-nth 0
                           (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
                  1))
                (fat32-update-lower-28
                 (fati
                  (nth
                   0
                   (find-n-free-clusters
                    (effective-fat
                     (mv-nth
                      0
                      (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
                    1))
                  (mv-nth 0
                          (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
                 268435455)
                (mv-nth 0
                        (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                               current-dir-first-cluster)))
               (m1-file->contents (cdr (car fs)))
               (nth
                0
                (find-n-free-clusters
                 (effective-fat
                  (mv-nth 0
                          (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                 current-dir-first-cluster)))
                 1)))))))
          (cluster-size fat32-in-memory)))))
      (fa-table
       (effective-fat
        (mv-nth
         0
         (hifat-to-lofat-helper
          (update-fati
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
             1))
           (fat32-update-lower-28
            (fati
             (nth
              0
              (find-n-free-clusters
               (effective-fat
                (mv-nth 0
                        (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                               current-dir-first-cluster)))
               1))
             (mv-nth 0
                     (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
            268435455)
           (mv-nth 0
                   (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
          (m1-file->contents (cdr (car fs)))
          (nth
           0
           (find-n-free-clusters
            (effective-fat
             (mv-nth 0
                     (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
            1)))))))
     (:instance
      (:rewrite free-index-listp-of-effective-fat-of-hifat-to-lofat-helper)
      (current-dir-first-cluster
       (nth
        0
        (find-n-free-clusters
         (effective-fat
          (mv-nth 0
                  (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                         current-dir-first-cluster)))
         1)))
      (fs (m1-file->contents (cdr (car fs))))
      (fat32-in-memory
       (update-fati
        (nth
         0
         (find-n-free-clusters
          (effective-fat
           (mv-nth 0
                   (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
          1))
        (fat32-update-lower-28
         (fati
          (nth
           0
           (find-n-free-clusters
            (effective-fat
             (mv-nth 0
                     (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
            1))
          (mv-nth 0
                  (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                         current-dir-first-cluster)))
         268435455)
        (mv-nth 0
                (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                       current-dir-first-cluster))))
      (index-list
       (find-n-free-clusters
        (effective-fat
         (mv-nth
          0
          (hifat-to-lofat-helper
           (update-fati
            (nth
             0
             (find-n-free-clusters
              (effective-fat
               (mv-nth 0
                       (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                              current-dir-first-cluster)))
              1))
            (fat32-update-lower-28
             (fati
              (nth
               0
               (find-n-free-clusters
                (effective-fat
                 (mv-nth 0
                         (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster)))
                1))
              (mv-nth 0
                      (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
             268435455)
            (mv-nth 0
                    (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                           current-dir-first-cluster)))
           (m1-file->contents (cdr (car fs)))
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
             1)))))
        (+
         -1
         (len
          (make-clusters
           (nats=>string
            (append
             (dir-ent-install-directory-bit
              (dir-ent-set-filename
               (dir-ent-set-first-cluster-file-size
                (m1-file->dir-ent (cdr (car fs)))
                (nth
                 0
                 (find-n-free-clusters
                  (effective-fat
                   (mv-nth 0
                           (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
                  1))
                0)
               ".          ")
              t)
             (dir-ent-install-directory-bit
              (dir-ent-set-filename (dir-ent-set-first-cluster-file-size
                                     (m1-file->dir-ent (cdr (car fs)))
                                     current-dir-first-cluster 0)
                                    "..         ")
              t)
             (flatten
              (mv-nth
               1
               (hifat-to-lofat-helper
                (update-fati
                 (nth
                  0
                  (find-n-free-clusters
                   (effective-fat
                    (mv-nth
                     0
                     (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
                   1))
                 (fat32-update-lower-28
                  (fati
                   (nth
                    0
                    (find-n-free-clusters
                     (effective-fat
                      (mv-nth
                       0
                       (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                              current-dir-first-cluster)))
                     1))
                   (mv-nth 0
                           (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
                  268435455)
                 (mv-nth 0
                         (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster)))
                (m1-file->contents (cdr (car fs)))
                (nth
                 0
                 (find-n-free-clusters
                  (effective-fat
                   (mv-nth 0
                           (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
                  1)))))))
           (cluster-size fat32-in-memory)))))))
     (:instance
      (:rewrite free-index-listp-of-effective-fat-of-hifat-to-lofat-helper)
      (fs (cdr fs))
      (fat32-in-memory fat32-in-memory)
      (index-list
       (find-n-free-clusters
        (effective-fat
         (mv-nth
          0
          (hifat-to-lofat-helper
           (update-fati
            (nth
             0
             (find-n-free-clusters
              (effective-fat
               (mv-nth 0
                       (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                              current-dir-first-cluster)))
              1))
            (fat32-update-lower-28
             (fati
              (nth
               0
               (find-n-free-clusters
                (effective-fat
                 (mv-nth 0
                         (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster)))
                1))
              (mv-nth 0
                      (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
             268435455)
            (mv-nth 0
                    (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                           current-dir-first-cluster)))
           (m1-file->contents (cdr (car fs)))
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
             1)))))
        (+
         -1
         (len
          (make-clusters
           (nats=>string
            (append
             (dir-ent-install-directory-bit
              (dir-ent-set-filename
               (dir-ent-set-first-cluster-file-size
                (m1-file->dir-ent (cdr (car fs)))
                (nth
                 0
                 (find-n-free-clusters
                  (effective-fat
                   (mv-nth 0
                           (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
                  1))
                0)
               ".          ")
              t)
             (dir-ent-install-directory-bit
              (dir-ent-set-filename (dir-ent-set-first-cluster-file-size
                                     (m1-file->dir-ent (cdr (car fs)))
                                     current-dir-first-cluster 0)
                                    "..         ")
              t)
             (flatten
              (mv-nth
               1
               (hifat-to-lofat-helper
                (update-fati
                 (nth
                  0
                  (find-n-free-clusters
                   (effective-fat
                    (mv-nth
                     0
                     (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
                   1))
                 (fat32-update-lower-28
                  (fati
                   (nth
                    0
                    (find-n-free-clusters
                     (effective-fat
                      (mv-nth
                       0
                       (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                              current-dir-first-cluster)))
                     1))
                   (mv-nth 0
                           (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
                  268435455)
                 (mv-nth 0
                         (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster)))
                (m1-file->contents (cdr (car fs)))
                (nth
                 0
                 (find-n-free-clusters
                  (effective-fat
                   (mv-nth 0
                           (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                  current-dir-first-cluster)))
                  1)))))))
           (cluster-size fat32-in-memory)))))))))))

(defthm
  hifat-to-lofat-inversion-lemma-13
  (implies
   (lofat-fs-p fat32-in-memory)
   (free-index-listp
    (find-n-free-clusters
     (update-nth
      (nth
       0
       (find-n-free-clusters
        (effective-fat
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                        current-dir-first-cluster)))
        1))
      (fat32-update-lower-28
       (fati
        (nth
         0
         (find-n-free-clusters
          (effective-fat
           (mv-nth 0
                   (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
          1))
        (mv-nth 0
                (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                       current-dir-first-cluster)))
       268435455)
      (effective-fat
       (mv-nth 0
               (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                      current-dir-first-cluster))))
     (+ -1
        (len (make-clusters (m1-file->contents (cdr (car fs)))
                            (cluster-size fat32-in-memory)))))
    (effective-fat fat32-in-memory)))
  :hints
  (("goal"
    :in-theory (disable (:rewrite free-index-listp-of-update-nth)
                        (:rewrite free-index-listp-of-find-n-free-clusters))
    :use
    ((:instance
      (:rewrite free-index-listp-of-find-n-free-clusters)
      (n (+ -1
            (len (make-clusters (m1-file->contents (cdr (car fs)))
                                (cluster-size fat32-in-memory)))))
      (fa-table
       (update-nth
        (nth
         0
         (find-n-free-clusters
          (effective-fat
           (mv-nth 0
                   (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
          1))
        (fat32-update-lower-28
         (fati
          (nth
           0
           (find-n-free-clusters
            (effective-fat
             (mv-nth 0
                     (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
            1))
          (mv-nth 0
                  (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                         current-dir-first-cluster)))
         268435455)
        (effective-fat
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                        current-dir-first-cluster))))))
     (:instance
      (:rewrite free-index-listp-of-update-nth)
      (fa-table
       (effective-fat
        (mv-nth 0
                (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                       current-dir-first-cluster))))
      (val
       (fat32-update-lower-28
        (fati
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth 0
                    (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                           current-dir-first-cluster)))
           1))
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                        current-dir-first-cluster)))
        268435455))
      (key
       (nth
        0
        (find-n-free-clusters
         (effective-fat
          (mv-nth 0
                  (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                         current-dir-first-cluster)))
         1)))
      (index-list
       (find-n-free-clusters
        (update-nth
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth 0
                    (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                           current-dir-first-cluster)))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
             1))
           (mv-nth 0
                   (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
          268435455)
         (effective-fat
          (mv-nth 0
                  (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                         current-dir-first-cluster))))
        (+ -1
           (len (make-clusters (m1-file->contents (cdr (car fs)))
                               (cluster-size fat32-in-memory)))))))))))

(defthm
  hifat-to-lofat-inversion-lemma-21
  (subdir-contents-p
   (implode
    (append
     (nats=>chars
      (dir-ent-install-directory-bit
       (dir-ent-set-filename
        (dir-ent-set-first-cluster-file-size
         (m1-file->dir-ent (cdr (car fs)))
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth 0
                    (hifat-to-lofat-helper
                     fat32-in-memory (cdr fs)
                     current-dir-first-cluster)))
           1))
         0)
        ".          ")
       t))
     (nats=>chars
      (dir-ent-install-directory-bit
       (dir-ent-set-filename
        (dir-ent-set-first-cluster-file-size
         (m1-file->dir-ent (cdr (car fs)))
         current-dir-first-cluster 0)
        "..         ")
       t))
     (nats=>chars
      (flatten
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
          (mv-nth
           0
           (hifat-to-lofat-helper fat32-in-memory (cdr fs)
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
           1))))))
     (make-list-ac
      (+
       -64
       (- (* 32
             (len (m1-file->contents (cdr (car fs))))))
       (*
        (cluster-size fat32-in-memory)
        (len
         (make-clusters
          (nats=>string
           (append
            (dir-ent-install-directory-bit
             (dir-ent-set-filename
              (dir-ent-set-first-cluster-file-size
               (m1-file->dir-ent (cdr (car fs)))
               (nth
                0
                (find-n-free-clusters
                 (effective-fat
                  (mv-nth 0
                          (hifat-to-lofat-helper
                           fat32-in-memory (cdr fs)
                           current-dir-first-cluster)))
                 1))
               0)
              ".          ")
             t)
            (dir-ent-install-directory-bit
             (dir-ent-set-filename
              (dir-ent-set-first-cluster-file-size
               (m1-file->dir-ent (cdr (car fs)))
               current-dir-first-cluster 0)
              "..         ")
             t)
            (flatten
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
                 1)))))))
          (cluster-size fat32-in-memory)))))
      (code-char 0)
      nil))))
  :hints
  (("goal"
    :in-theory (enable subdir-contents-p remove1-dir-ent))))

;; The dir-ent-list-p hypothesis is only there because
;; lofat-to-hifat-helper doesn't fix its arguments. Should it?
(defthm
  hifat-to-lofat-inversion-lemma-23
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
  hifat-to-lofat-inversion-lemma-18
  (implies (not (equal (fat32-entry-mask (nth key fa-table))
                       0))
           (not (member-equal key (find-n-free-clusters fa-table n))))
  :hints
  (("goal" :in-theory (disable (:rewrite free-index-listp-correctness-1))
    :use (:instance (:rewrite free-index-listp-correctness-1)
                    (x (find-n-free-clusters fa-table n))))))

(encapsulate
  ()

  ;; This rule is weaker than it could be, but proving the stronger version
  ;; can't be done until more stuff is proved.
  (local
   (defthm
     hifat-to-lofat-inversion-lemma-14
     (implies
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth
          0
          (hifat-to-lofat-helper fat32-in-memory
                                 fs current-dir-first-cluster))
         (mv-nth
          1
          (hifat-to-lofat-helper fat32-in-memory
                                 fs current-dir-first-cluster))
         entry-limit))
       fs)
      (equal
       (consp
        (assoc-equal
         key
         (mv-nth
          0
          (lofat-to-hifat-helper
           (mv-nth
            0
            (hifat-to-lofat-helper fat32-in-memory
                                   fs current-dir-first-cluster))
           (mv-nth
            1
            (hifat-to-lofat-helper fat32-in-memory
                                   fs current-dir-first-cluster))
           entry-limit))))
       (consp (assoc-equal key (hifat-file-alist-fix fs)))))
     :hints
     (("goal"
       :in-theory (disable hifat-to-lofat-inversion-lemma-4)
       :use
       (:instance
        hifat-to-lofat-inversion-lemma-4
        (m1-file-alist1
         (mv-nth
          0
          (lofat-to-hifat-helper
           (mv-nth
            0
            (hifat-to-lofat-helper fat32-in-memory
                                   fs current-dir-first-cluster))
           (mv-nth
            1
            (hifat-to-lofat-helper fat32-in-memory
                                   fs current-dir-first-cluster))
           entry-limit)))
        (m1-file-alist2 fs))))))

  (local
   (defthm
     hifat-to-lofat-inversion-lemma-24
     (implies
      (and
       (equal
        (mv-nth 3
                (lofat-to-hifat-helper
                 (mv-nth 0
                         (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster))
                 (mv-nth 1
                         (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster))
                 entry-limit))
        0)
       (hifat-equiv
        (mv-nth 0
                (lofat-to-hifat-helper
                 (mv-nth 0
                         (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster))
                 (mv-nth 1
                         (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster))
                 entry-limit))
        (cdr fs))
       (m1-file-alist-p fs)
       (hifat-no-dups-p (cdr fs))
       (not (consp (assoc-equal (car (car fs)) (cdr fs)))))
      (not
       (equal
        (mv-nth
         1
         (find-dir-ent (mv-nth 1
                               (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                      current-dir-first-cluster))
                       (car (car fs))))
        0)))
     :hints
     (("goal"
       :in-theory (disable (:rewrite hifat-to-lofat-inversion-lemma-23))
       :use
       (:instance
        (:rewrite hifat-to-lofat-inversion-lemma-23)
        (dir-ent-list (mv-nth 1
                              (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                     current-dir-first-cluster)))
        (fat32-in-memory
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                        current-dir-first-cluster)))
        (name (car (car fs))))))))

  (local
   (defthm
     hifat-to-lofat-inversion-lemma-15
     (iff (equal (hifat-entry-count fs) 0) (atom fs))
     :hints
     (("goal"
       :in-theory (enable hifat-entry-count)))))

  (defthmd
    hifat-to-lofat-inversion-lemma-16
    (implies (and (stringp text)
                  (not (zp cluster-size))
                  (<= (length text) *ms-max-dir-size*)
                  (equal (mod *ms-max-dir-size* cluster-size)
                         0))
             (<= (* cluster-size
                    (len (make-clusters text cluster-size)))
                 *ms-max-dir-size*))
    :rule-classes :linear
    :hints
    (("goal" :in-theory (disable make-clusters-correctness-3)
      :use (:instance make-clusters-correctness-3
                      (max-length *ms-max-dir-size*)))))

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
          (contents (m1-file->contents (cdr head)))
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
                  (hifat-entry-count (m1-file->contents (cdr head))))))
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
          ((when (and (m1-regular-file-p (cdr head))
                      (equal (length contents) 0)))
           (mv
            fat32-in-memory
            (list*
             (dir-ent-install-directory-bit
              (dir-ent-set-filename
               (dir-ent-set-first-cluster-file-size dir-ent 0 0)
               (mbe :exec (car head)
                    :logic (fat32-filename-fix (car head))))
              nil)
             tail-list)
            0 tail-index-list))
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
               ((file-length (length contents))
                ((mv fat32-in-memory
                     dir-ent errno head-index-list)
                 (place-contents fat32-in-memory dir-ent
                                 contents file-length first-cluster))
                (dir-ent (dir-ent-set-filename
                          dir-ent
                          (mbe :exec (car head) :logic (fat32-filename-fix (car head)))))
                (dir-ent (dir-ent-install-directory-bit dir-ent nil)))
             (mv fat32-in-memory
                 (list* dir-ent tail-list)
                 errno
                 (append head-index-list tail-index-list)))
         (b*
             ((file-length 0)
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
              (dir-ent (dir-ent-set-filename
                        dir-ent
                        (mbe :exec (car head) :logic (fat32-filename-fix (car head)))))
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
          (hifat-bounded-file-alist-p fs)
          (hifat-no-dups-p fs)
          (integerp entry-limit)
          (>= entry-limit (hifat-entry-count fs))
          (non-free-index-listp x (effective-fat fat32-in-memory))
          (zp
           (mv-nth
            2
            (hifat-to-lofat-helper fat32-in-memory
                                   fs current-dir-first-cluster))))
     (and
      (equal (mv-nth
              3
              (lofat-to-hifat-helper
               (mv-nth 0
                       (hifat-to-lofat-helper fat32-in-memory
                                              fs current-dir-first-cluster))
               (mv-nth 1
                       (hifat-to-lofat-helper fat32-in-memory
                                              fs current-dir-first-cluster))
               entry-limit))
             0)
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         (mv-nth
          0
          (hifat-to-lofat-helper fat32-in-memory
                                 fs current-dir-first-cluster))
         (mv-nth
          1
          (hifat-to-lofat-helper fat32-in-memory
                                 fs current-dir-first-cluster))
         entry-limit)))
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory
                                        fs current-dir-first-cluster))
         (mv-nth 1
                 (hifat-to-lofat-helper fat32-in-memory
                                        fs current-dir-first-cluster))
         entry-limit))
       fs)
      (free-index-list-listp
       (mv-nth
        2
        (lofat-to-hifat-helper
         (mv-nth
          0
          (hifat-to-lofat-helper fat32-in-memory
                                 fs current-dir-first-cluster))
         (mv-nth
          1
          (hifat-to-lofat-helper fat32-in-memory
                                 fs current-dir-first-cluster))
         entry-limit))
       (effective-fat fat32-in-memory))))
    :hints
    (("goal"
      :induct (induction-scheme fat32-in-memory fs
                                current-dir-first-cluster entry-limit x)
      :in-theory
      (e/d (lofat-to-hifat-helper
            (:definition hifat-no-dups-p)
            remove1-dir-ent not-intersectp-list
            (:linear hifat-to-lofat-inversion-lemma-16))
           ((:rewrite nth-of-nats=>chars)
            (:rewrite dir-ent-p-when-member-equal-of-dir-ent-list-p)
            (:rewrite fati-of-hifat-to-lofat-helper-disjoint-lemma-2)
            (:definition induction-scheme)))
      :expand ((:free (y) (intersectp-equal nil y))
               (:free (x1 x2 y)
                      (intersectp-equal (list x1)
                                        (cons x2 y)))
               (:free (fat32-in-memory dir-ent dir-ent-list entry-limit)
                      (lofat-to-hifat-helper fat32-in-memory
                                             (cons dir-ent dir-ent-list)
                                             entry-limit)))))
    :rule-classes
    ((:rewrite
      :corollary
      (implies
       (and (lofat-fs-p fat32-in-memory)
            (m1-file-alist-p fs)
            (hifat-bounded-file-alist-p fs)
            (hifat-no-dups-p fs)
            (fat32-masked-entry-p current-dir-first-cluster)
            (integerp entry-limit)
            (>= entry-limit (hifat-entry-count fs))
            (non-free-index-listp x (effective-fat fat32-in-memory)))
       (b*
           (((mv fat32-in-memory dir-ent-list error-code)
             (hifat-to-lofat-helper fat32-in-memory
                                    fs current-dir-first-cluster)))
         (implies
          (zp error-code)
          (not-intersectp-list
           x
           (mv-nth 2
                   (lofat-to-hifat-helper fat32-in-memory
                                          dir-ent-list entry-limit))))))))))

(defthm
  hifat-to-lofat-inversion-big-induction-corollaries
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (m1-file-alist-p fs)
        (hifat-bounded-file-alist-p fs)
        (hifat-no-dups-p fs)
        (integerp entry-limit)
        (>= entry-limit (hifat-entry-count fs)))
   (b*
       (((mv fat32-in-memory dir-ent-list error-code)
         (hifat-to-lofat-helper fat32-in-memory
                                fs current-dir-first-cluster)))
     (implies
      (zp error-code)
      (and
       (equal (mv-nth 3
                      (lofat-to-hifat-helper fat32-in-memory
                                             dir-ent-list entry-limit))
              0)
       (hifat-equiv
        (mv-nth 0
                (lofat-to-hifat-helper fat32-in-memory
                                       dir-ent-list entry-limit))
        fs)))))
  :hints (("goal" :in-theory (disable hifat-to-lofat-inversion-big-induction)
           :use (:instance hifat-to-lofat-inversion-big-induction
                           (x nil)))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    hifat-to-lofat-inversion-lemma-19
    (implies (lofat-fs-p fat32-in-memory)
             (>= *ms-max-dir-size*
                 (cluster-size fat32-in-memory)))
    :rule-classes :linear
    :hints
    (("goal" :in-theory
      (disable lofat-fs-p-correctness-1)
      :use lofat-fs-p-correctness-1)))

  (defthmd
    hifat-to-lofat-inversion-lemma-20
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
      (e/d (painful-debugging-lemma-14) (lofat-fs-p-correctness-1))
      :use
      (lofat-fs-p-correctness-1
       (:instance
        len-of-make-clusters
        (cluster-size (cluster-size fat32-in-memory))))))))

(defthm
  hifat-to-lofat-inversion-lemma-22
  (implies
   (and
    (equal
     (mv-nth
      2
      (hifat-to-lofat-helper
       (update-fati
        (fat32-entry-mask (bpb_rootclus fat32-in-memory))
        (fat32-update-lower-28
         (fati
          (fat32-entry-mask (bpb_rootclus fat32-in-memory))
          (stobj-set-indices-in-fa-table
           fat32-in-memory
           (generate-index-list
            2 (count-of-clusters fat32-in-memory))
           (make-list-ac (count-of-clusters fat32-in-memory)
                         0 nil)))
         268435455)
        (stobj-set-indices-in-fa-table
         fat32-in-memory
         (generate-index-list
          2 (count-of-clusters fat32-in-memory))
         (make-list-ac (count-of-clusters fat32-in-memory)
                       0 nil)))
       fs
       (fat32-entry-mask (bpb_rootclus fat32-in-memory))))
     0)
    (lofat-fs-p fat32-in-memory)
    (m1-file-alist-p fs)
    (hifat-bounded-file-alist-p fs)
    (hifat-no-dups-p fs)
    (<= (hifat-entry-count fs)
        (max-entry-count fat32-in-memory)))
   (not-intersectp-list
    (cons
     (fat32-entry-mask (bpb_rootclus fat32-in-memory))
     (find-n-free-clusters
      (effective-fat
       (mv-nth
        0
        (hifat-to-lofat-helper
         (update-fati
          (fat32-entry-mask (bpb_rootclus fat32-in-memory))
          (fat32-update-lower-28
           (fati
            (fat32-entry-mask (bpb_rootclus fat32-in-memory))
            (stobj-set-indices-in-fa-table
             fat32-in-memory
             (generate-index-list
              2 (count-of-clusters fat32-in-memory))
             (make-list-ac (count-of-clusters fat32-in-memory)
                           0 nil)))
           268435455)
          (stobj-set-indices-in-fa-table
           fat32-in-memory
           (generate-index-list
            2 (count-of-clusters fat32-in-memory))
           (make-list-ac (count-of-clusters fat32-in-memory)
                         0 nil)))
         fs
         (fat32-entry-mask (bpb_rootclus fat32-in-memory)))))
      n))
    (mv-nth
     2
     (lofat-to-hifat-helper
      (mv-nth
       0
       (hifat-to-lofat-helper
        (update-fati
         (fat32-entry-mask (bpb_rootclus fat32-in-memory))
         (fat32-update-lower-28
          (fati
           (fat32-entry-mask (bpb_rootclus fat32-in-memory))
           (stobj-set-indices-in-fa-table
            fat32-in-memory
            (generate-index-list
             2 (count-of-clusters fat32-in-memory))
            (make-list-ac (count-of-clusters fat32-in-memory)
                          0 nil)))
          268435455)
         (stobj-set-indices-in-fa-table
          fat32-in-memory
          (generate-index-list
           2 (count-of-clusters fat32-in-memory))
          (make-list-ac (count-of-clusters fat32-in-memory)
                        0 nil)))
        fs
        (fat32-entry-mask (bpb_rootclus fat32-in-memory))))
      (mv-nth
       1
       (hifat-to-lofat-helper
        (update-fati
         (fat32-entry-mask (bpb_rootclus fat32-in-memory))
         (fat32-update-lower-28
          (fati
           (fat32-entry-mask (bpb_rootclus fat32-in-memory))
           (stobj-set-indices-in-fa-table
            fat32-in-memory
            (generate-index-list
             2 (count-of-clusters fat32-in-memory))
            (make-list-ac (count-of-clusters fat32-in-memory)
                          0 nil)))
          268435455)
         (stobj-set-indices-in-fa-table
          fat32-in-memory
          (generate-index-list
           2 (count-of-clusters fat32-in-memory))
          (make-list-ac (count-of-clusters fat32-in-memory)
                        0 nil)))
        fs
        (fat32-entry-mask (bpb_rootclus fat32-in-memory))))
      (max-entry-count fat32-in-memory)))))
  :hints
  (("goal"
    :do-not-induct t
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
           (fat32-entry-mask (bpb_rootclus fat32-in-memory))
           (fat32-update-lower-28
            (fati
             (fat32-entry-mask (bpb_rootclus fat32-in-memory))
             (stobj-set-indices-in-fa-table
              fat32-in-memory
              (generate-index-list
               2 (count-of-clusters fat32-in-memory))
              (make-list-ac (count-of-clusters fat32-in-memory)
                            0 nil)))
            268435455)
           (stobj-set-indices-in-fa-table
            fat32-in-memory
            (generate-index-list
             2 (count-of-clusters fat32-in-memory))
            (make-list-ac (count-of-clusters fat32-in-memory)
                          0 nil)))
          fs
          (fat32-entry-mask (bpb_rootclus fat32-in-memory))))
        (mv-nth
         1
         (hifat-to-lofat-helper
          (update-fati
           (fat32-entry-mask (bpb_rootclus fat32-in-memory))
           (fat32-update-lower-28
            (fati
             (fat32-entry-mask (bpb_rootclus fat32-in-memory))
             (stobj-set-indices-in-fa-table
              fat32-in-memory
              (generate-index-list
               2 (count-of-clusters fat32-in-memory))
              (make-list-ac (count-of-clusters fat32-in-memory)
                            0 nil)))
            268435455)
           (stobj-set-indices-in-fa-table
            fat32-in-memory
            (generate-index-list
             2 (count-of-clusters fat32-in-memory))
            (make-list-ac (count-of-clusters fat32-in-memory)
                          0 nil)))
          fs
          (fat32-entry-mask (bpb_rootclus fat32-in-memory))))
        (max-entry-count fat32-in-memory))))
     (y
      (find-n-free-clusters
       (effective-fat
        (mv-nth
         0
         (hifat-to-lofat-helper
          (update-fati
           (fat32-entry-mask (bpb_rootclus fat32-in-memory))
           (fat32-update-lower-28
            (fati
             (fat32-entry-mask (bpb_rootclus fat32-in-memory))
             (stobj-set-indices-in-fa-table
              fat32-in-memory
              (generate-index-list
               2 (count-of-clusters fat32-in-memory))
              (make-list-ac (count-of-clusters fat32-in-memory)
                            0 nil)))
            268435455)
           (stobj-set-indices-in-fa-table
            fat32-in-memory
            (generate-index-list
             2 (count-of-clusters fat32-in-memory))
            (make-list-ac (count-of-clusters fat32-in-memory)
                          0 nil)))
          fs
          (fat32-entry-mask (bpb_rootclus fat32-in-memory)))))
       n))
     (x
      (list
       (fat32-entry-mask (bpb_rootclus fat32-in-memory))))))))

(defthm
  hifat-to-lofat-inversion
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (m1-file-alist-p fs)
        (hifat-bounded-file-alist-p fs)
        (hifat-no-dups-p fs)
        (<=
         (hifat-entry-count fs)
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
  (("goal"
    :in-theory (enable lofat-to-hifat
                       hifat-to-lofat
                       root-dir-ent-list
                       pseudo-root-dir-ent
                       not-intersectp-list
                       hifat-to-lofat-inversion-lemma-17
                       hifat-to-lofat-inversion-lemma-20
                       painful-debugging-lemma-10
                       painful-debugging-lemma-11))))

;; In the subdirectory case, we need to place all the entries (32 bytes each)
;; and two entries (dot and dotdot). The space taken up for these things is
;; determined by the rule len-of-make-clusters, which expresses the length in
;; terms of the greatest integer function.
(defund
  hifat-cluster-count (fs cluster-size)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (integerp cluster-size)
                              (< 0 cluster-size))))
  (b*
      (((unless (consp fs)) 0)
       (head (car fs))
       (contents (m1-file->contents (cdr head))))
    (+
     (hifat-cluster-count (cdr fs)
                          cluster-size)
     (if
         (m1-regular-file-p (cdr head))
         (len (make-clusters contents cluster-size))
       (+ (hifat-cluster-count contents cluster-size)
          ;; This mbe form is here to help make a good type-prescription rule,
          ;; which identifies this thing as a natural number - not just an
          ;; integer. As an aside, I guess the battle over whether 0 is a
          ;; natural number has been lost for a while, since nobody seems to use
          ;; the term "whole number" any more.
          (mbe :exec (ceiling (* 32 (+ 2 (len contents)))
                              cluster-size)
               :logic (nfix (ceiling (* 32 (+ 2 (len contents)))
                                     cluster-size))))))))

(defthm
  count-free-clusters-of-effective-fat-of-place-contents
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (stringp contents)
    (fat32-masked-entry-p first-cluster)
    (>= first-cluster *ms-first-data-cluster*)
    (< first-cluster
       (+ *ms-first-data-cluster*
          (count-of-clusters fat32-in-memory)))
    (not
     (equal
      (fat32-entry-mask (fati first-cluster fat32-in-memory))
      0)))
   (equal
    (count-free-clusters
     (effective-fat
      (mv-nth
       0
       (place-contents fat32-in-memory dir-ent
                       contents file-length first-cluster))))
    (if
        (equal
         (mv-nth
          2
          (place-contents fat32-in-memory dir-ent
                          contents file-length first-cluster))
         *enospc*)
        (count-free-clusters (effective-fat fat32-in-memory))
      (+
       1
       (count-free-clusters (effective-fat fat32-in-memory))
       (-
        (len (make-clusters contents
                            (cluster-size fat32-in-memory))))))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (place-contents
      set-indices-in-fa-table
      length-of-empty-list)
     ((:rewrite len-of-find-n-free-clusters)))
    :use
    ((:instance
      find-n-free-clusters-correctness-3
      (n
       (+ -1
          (len (make-clusters contents
                              (cluster-size fat32-in-memory)))))
      (fa-table (effective-fat fat32-in-memory))
      (x 0))
     (:instance
      (:rewrite len-of-find-n-free-clusters)
      (n
       (+ -1
          (len (make-clusters contents
                              (cluster-size fat32-in-memory)))))
      (fa-table (effective-fat fat32-in-memory))))
    :expand (make-clusters "" (cluster-size fat32-in-memory)))))

(defthm
  count-free-clusters-of-effective-fat-of-hifat-to-lofat-helper
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (m1-file-alist-p fs)
        (equal (mv-nth 2
                       (hifat-to-lofat-helper fat32-in-memory
                                              fs current-dir-first-cluster))
               0))
   (equal
    (count-free-clusters
     (effective-fat
      (mv-nth 0
              (hifat-to-lofat-helper fat32-in-memory
                                     fs current-dir-first-cluster))))
    (- (count-free-clusters (effective-fat fat32-in-memory))
       (hifat-cluster-count fs (cluster-size fat32-in-memory)))))
  :hints
  (("goal"
    :in-theory (enable len-of-make-clusters hifat-cluster-count
                       painful-debugging-lemma-14))))

(defthm
  hifat-to-lofat-helper-correctness-5-lemma-1
  (implies
   (and
    (equal
     (mv-nth
      2
      (hifat-to-lofat-helper
       (update-fati
        (nth
         0
         (find-n-free-clusters
          (effective-fat
           (mv-nth 0
                   (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
          1))
        (fat32-update-lower-28
         (fati
          (nth
           0
           (find-n-free-clusters
            (effective-fat
             (mv-nth 0
                     (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
            1))
          (mv-nth 0
                  (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                         current-dir-first-cluster)))
         268435455)
        (mv-nth 0
                (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                       current-dir-first-cluster)))
       (m1-file->contents (cdr (car fs)))
       (nth
        0
        (find-n-free-clusters
         (effective-fat
          (mv-nth 0
                  (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                         current-dir-first-cluster)))
         1))))
     0)
    (equal (mv-nth 2
                   (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                          current-dir-first-cluster))
           0)
    (not (m1-regular-file-p (cdr (car fs))))
    (<
     (nth
      0
      (find-n-free-clusters
       (effective-fat
        (mv-nth 0
                (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                       current-dir-first-cluster)))
       1))
     (+ 2 (count-of-clusters fat32-in-memory)))
    (<= (hifat-cluster-count (m1-file->contents (cdr (car fs)))
                             (cluster-size fat32-in-memory))
        (+ -1
           (count-free-clusters (effective-fat fat32-in-memory))
           (- (hifat-cluster-count (cdr fs)
                                   (cluster-size fat32-in-memory)))))
    (lofat-fs-p fat32-in-memory)
    (m1-file-alist-p fs)
    (< (count-free-clusters (effective-fat fat32-in-memory))
       (+ (hifat-cluster-count (cdr fs)
                               (cluster-size fat32-in-memory))
          (hifat-cluster-count (m1-file->contents (cdr (car fs)))
                               (cluster-size fat32-in-memory))
          (ceiling (+ 64
                      (* 32
                         (len (m1-file->contents (cdr (car fs))))))
                   (cluster-size fat32-in-memory)))))
   (equal
    (mv-nth
     2
     (place-contents
      (mv-nth
       0
       (hifat-to-lofat-helper
        (update-fati
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth 0
                    (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                           current-dir-first-cluster)))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
             1))
           (mv-nth 0
                   (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
          268435455)
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                        current-dir-first-cluster)))
        (m1-file->contents (cdr (car fs)))
        (nth
         0
         (find-n-free-clusters
          (effective-fat
           (mv-nth 0
                   (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
          1))))
      (m1-file->dir-ent (cdr (car fs)))
      (nats=>string
       (append
        (dir-ent-install-directory-bit
         (dir-ent-set-filename
          (dir-ent-set-first-cluster-file-size
           (m1-file->dir-ent (cdr (car fs)))
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
             1))
           0)
          ".          ")
         t)
        (dir-ent-install-directory-bit
         (dir-ent-set-filename (dir-ent-set-first-cluster-file-size
                                (m1-file->dir-ent (cdr (car fs)))
                                current-dir-first-cluster 0)
                               "..         ")
         t)
        (flatten
         (mv-nth
          1
          (hifat-to-lofat-helper
           (update-fati
            (nth
             0
             (find-n-free-clusters
              (effective-fat
               (mv-nth 0
                       (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                              current-dir-first-cluster)))
              1))
            (fat32-update-lower-28
             (fati
              (nth
               0
               (find-n-free-clusters
                (effective-fat
                 (mv-nth 0
                         (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster)))
                1))
              (mv-nth 0
                      (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
             268435455)
            (mv-nth 0
                    (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                           current-dir-first-cluster)))
           (m1-file->contents (cdr (car fs)))
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
             1)))))))
      0
      (nth
       0
       (find-n-free-clusters
        (effective-fat
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                        current-dir-first-cluster)))
        1))))
    28))
  :hints
  (("goal"
    :in-theory (e/d (hifat-cluster-count length-of-empty-list
                                         painful-debugging-lemma-12
                                         len-of-make-clusters)
                    ((:rewrite fati-of-hifat-to-lofat-helper-disjoint)
                     (:rewrite fati-of-hifat-to-lofat-helper-disjoint-lemma-1))))))

(defthm
  hifat-to-lofat-helper-correctness-5-lemma-2
  (implies
   (and
    (equal
     (mv-nth
      2
      (hifat-to-lofat-helper
       (update-fati
        (nth
         0
         (find-n-free-clusters
          (effective-fat
           (mv-nth 0
                   (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
          1))
        (fat32-update-lower-28
         (fati
          (nth
           0
           (find-n-free-clusters
            (effective-fat
             (mv-nth 0
                     (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
            1))
          (mv-nth 0
                  (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                         current-dir-first-cluster)))
         268435455)
        (mv-nth 0
                (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                       current-dir-first-cluster)))
       (m1-file->contents (cdr (car fs)))
       (nth
        0
        (find-n-free-clusters
         (effective-fat
          (mv-nth 0
                  (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                         current-dir-first-cluster)))
         1))))
     0)
    (equal (mv-nth 2
                   (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                          current-dir-first-cluster))
           0)
    (not (m1-regular-file-p (cdr (car fs))))
    (<
     (nth
      0
      (find-n-free-clusters
       (effective-fat
        (mv-nth 0
                (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                       current-dir-first-cluster)))
       1))
     (+ 2 (count-of-clusters fat32-in-memory)))
    (lofat-fs-p fat32-in-memory)
    (m1-file-alist-p fs)
    (<= (+ (hifat-cluster-count (cdr fs)
                                (cluster-size fat32-in-memory))
           (hifat-cluster-count (m1-file->contents (cdr (car fs)))
                                (cluster-size fat32-in-memory))
           (ceiling (+ 64
                       (* 32
                          (len (m1-file->contents (cdr (car fs))))))
                    (cluster-size fat32-in-memory)))
        (count-free-clusters (effective-fat fat32-in-memory))))
   (equal
    (mv-nth
     2
     (place-contents
      (mv-nth
       0
       (hifat-to-lofat-helper
        (update-fati
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth 0
                    (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                           current-dir-first-cluster)))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
             1))
           (mv-nth 0
                   (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
          268435455)
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                        current-dir-first-cluster)))
        (m1-file->contents (cdr (car fs)))
        (nth
         0
         (find-n-free-clusters
          (effective-fat
           (mv-nth 0
                   (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
          1))))
      (m1-file->dir-ent (cdr (car fs)))
      (nats=>string
       (append
        (dir-ent-install-directory-bit
         (dir-ent-set-filename
          (dir-ent-set-first-cluster-file-size
           (m1-file->dir-ent (cdr (car fs)))
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
             1))
           0)
          ".          ")
         t)
        (dir-ent-install-directory-bit
         (dir-ent-set-filename (dir-ent-set-first-cluster-file-size
                                (m1-file->dir-ent (cdr (car fs)))
                                current-dir-first-cluster 0)
                               "..         ")
         t)
        (flatten
         (mv-nth
          1
          (hifat-to-lofat-helper
           (update-fati
            (nth
             0
             (find-n-free-clusters
              (effective-fat
               (mv-nth 0
                       (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                              current-dir-first-cluster)))
              1))
            (fat32-update-lower-28
             (fati
              (nth
               0
               (find-n-free-clusters
                (effective-fat
                 (mv-nth 0
                         (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                                current-dir-first-cluster)))
                1))
              (mv-nth 0
                      (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
             268435455)
            (mv-nth 0
                    (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                           current-dir-first-cluster)))
           (m1-file->contents (cdr (car fs)))
           (nth
            0
            (find-n-free-clusters
             (effective-fat
              (mv-nth 0
                      (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                             current-dir-first-cluster)))
             1)))))))
      0
      (nth
       0
       (find-n-free-clusters
        (effective-fat
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                        current-dir-first-cluster)))
        1))))
    0))
  :hints
  (("goal"
    :in-theory (e/d (hifat-cluster-count length-of-empty-list
                                         painful-debugging-lemma-12
                                         len-of-make-clusters)
                    ((:rewrite fati-of-hifat-to-lofat-helper-disjoint)
                     (:rewrite fati-of-hifat-to-lofat-helper-disjoint-lemma-1))))))

(defthm
  hifat-to-lofat-helper-correctness-5-lemma-3
  (implies
   (and (equal (mv-nth 2
                       (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                              current-dir-first-cluster))
               0)
        (not (equal (m1-file->contents (cdr (car fs)))
                    ""))
        (<= 1
            (+ (count-free-clusters (effective-fat fat32-in-memory))
               (- (hifat-cluster-count (cdr fs)
                                       (cluster-size fat32-in-memory)))))
        (m1-regular-file-p (cdr (car fs)))
        (lofat-fs-p fat32-in-memory)
        (m1-file-alist-p fs)
        (<= (+ (hifat-cluster-count (cdr fs)
                                    (cluster-size fat32-in-memory))
               (len (make-clusters (m1-file->contents (cdr (car fs)))
                                   (cluster-size fat32-in-memory))))
            (count-free-clusters (effective-fat fat32-in-memory))))
   (equal
    (mv-nth
     2
     (place-contents
      (update-fati
       (nth
        0
        (find-n-free-clusters
         (effective-fat
          (mv-nth 0
                  (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                         current-dir-first-cluster)))
         1))
       (fat32-update-lower-28
        (fati
         (nth
          0
          (find-n-free-clusters
           (effective-fat
            (mv-nth 0
                    (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                           current-dir-first-cluster)))
           1))
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                        current-dir-first-cluster)))
        268435455)
       (mv-nth 0
               (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                      current-dir-first-cluster)))
      (m1-file->dir-ent (cdr (car fs)))
      (m1-file->contents (cdr (car fs)))
      (len (explode (m1-file->contents (cdr (car fs)))))
      (nth
       0
       (find-n-free-clusters
        (effective-fat
         (mv-nth 0
                 (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                        current-dir-first-cluster)))
        1))))
    0))
  :hints
  (("goal"
    :in-theory (disable (:rewrite place-contents-expansion-2))
    :use
    ((:instance
      (:rewrite place-contents-expansion-2)
      (first-cluster
       (nth
        0
        (find-n-free-clusters
         (effective-fat
          (mv-nth 0
                  (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                         current-dir-first-cluster)))
         1)))
      (file-length (len (explode (m1-file->contents (cdr (car fs))))))
      (contents (m1-file->contents (cdr (car fs))))
      (dir-ent (m1-file->dir-ent (cdr (car fs))))
      (fat32-in-memory
       (update-fati
        (nth
         0
         (find-n-free-clusters
          (effective-fat
           (mv-nth 0
                   (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                          current-dir-first-cluster)))
          1))
        (fat32-update-lower-28
         (fati
          (nth
           0
           (find-n-free-clusters
            (effective-fat
             (mv-nth 0
                     (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                            current-dir-first-cluster)))
            1))
          (mv-nth 0
                  (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                         current-dir-first-cluster)))
         268435455)
        (mv-nth 0
                (hifat-to-lofat-helper fat32-in-memory (cdr fs)
                                       current-dir-first-cluster)))))))))

(defthm
  hifat-to-lofat-helper-correctness-5
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (m1-file-alist-p fs))
   (equal
    (mv-nth
     2
     (hifat-to-lofat-helper fat32-in-memory
                            fs current-dir-first-cluster))
    (if
        (>=
         (count-free-clusters (effective-fat fat32-in-memory))
         (hifat-cluster-count fs (cluster-size fat32-in-memory)))
        0 *enospc*)))
  :hints
  (("goal"
    :induct (hifat-to-lofat-helper fat32-in-memory
                                   fs current-dir-first-cluster)
    :expand
    ((make-clusters "" (cluster-size fat32-in-memory))
     (hifat-cluster-count fs (cluster-size fat32-in-memory)))
    :in-theory
    (e/d
     (hifat-cluster-count
      length-of-empty-list
      painful-debugging-lemma-12)
     ((:rewrite fati-of-hifat-to-lofat-helper-disjoint)
      (:rewrite fati-of-hifat-to-lofat-helper-disjoint-lemma-1))))))

(defthm non-free-index-listp-correctness-6-lemma-1
  (implies (and (bounded-nat-listp l (+ b 1))
                (integerp b))
           (bounded-nat-listp (remove-equal b l)
                              b))
  :hints (("goal" :induct (remove-assoc-equal b l))))

(defthm
  non-free-index-listp-correctness-6-lemma-2
  (implies
   (non-free-index-listp x fa-table)
   (and
    (bounded-nat-listp x (len fa-table))
    (lower-bounded-integer-listp x *ms-first-data-cluster*))))

(encapsulate
  ()

  (local
   (defun
       induction-scheme (x fa-table b)
     (declare (xargs :verify-guards nil :measure (len fa-table)))
     (if (<= (len fa-table) (nfix b))
         (mv x fa-table b)
       (induction-scheme (remove-equal (- (len fa-table) 1) x)
                         (butlast fa-table 1)
                         b))))

  (defthm non-free-index-listp-correctness-6-lemma-3
    (implies (and (lower-bounded-integer-listp x b)
                  (bounded-nat-listp x (len fa-table))
                  (no-duplicatesp-equal x)
                  (<= b (len fa-table)))
             (<= (+ (len x) b) (len fa-table)))
    :rule-classes :linear
    :hints (("goal" :induct (induction-scheme x fa-table b)))))

(defthm
  non-free-index-listp-correctness-6
  (implies (and (<= *ms-first-data-cluster* (len fa-table))
                (non-free-index-listp x fa-table)
                (no-duplicatesp-equal x))
           (<= (+ 2 (len x)) (len fa-table)))
  :hints
  (("goal"
    :in-theory (disable non-free-index-listp-correctness-6-lemma-3)
    :use (:instance non-free-index-listp-correctness-6-lemma-3
                    (b *ms-first-data-cluster*)))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    lofat-to-hifat-helper-correctness-5-lemma-1
    (implies (and (integerp cluster-size)
                  (<= 64 cluster-size))
             (equal (floor (+ 63 cluster-size) cluster-size)
                    1))))

(defthmd
  lofat-to-hifat-helper-correctness-5-lemma-2
  (implies
   (equal
    (len
     (mv-nth
      0
      (fat32-build-index-list (effective-fat fat32-in-memory)
                              masked-current-cluster file-size
                              (cluster-size fat32-in-memory))))
    0)
   (equal
    (len (explode$inline
          (mv-nth '0
                  (get-clusterchain-contents
                   fat32-in-memory
                   masked-current-cluster file-size))))
    0))
  :hints
  (("goal" :in-theory (enable fat32-build-index-list
                              get-clusterchain-contents))))

(defthm
  lofat-to-hifat-helper-correctness-5-lemma-3
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (unsigned-byte-p 32 length))
   (equal (m1-file-contents-fix
           (mv-nth '0
                   (get-clusterchain-contents
                    fat32-in-memory
                    masked-current-cluster length)))
          (mv-nth '0
                  (get-clusterchain-contents
                   fat32-in-memory
                   masked-current-cluster length))))
  :hints
  (("goal"
    :in-theory
    (disable
     (:rewrite m1-file-contents-fix-when-m1-file-contents-p))
    :use
    (:instance
     (:rewrite m1-file-contents-fix-when-m1-file-contents-p)
     (x (mv-nth 0
                (get-clusterchain-contents
                 fat32-in-memory
                 masked-current-cluster length)))))))

(defthm
  lofat-to-hifat-helper-correctness-5-lemma-4
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (>= masked-current-cluster
        *ms-first-data-cluster*)
    (equal
     (mv-nth 1
             (fat32-build-index-list (effective-fat fat32-in-memory)
                                     masked-current-cluster
                                     length (cluster-size fat32-in-memory)))
     0))
   (equal
    (len
     (make-clusters
      (mv-nth 0
              (get-clusterchain-contents fat32-in-memory
                                         masked-current-cluster length))
      (cluster-size fat32-in-memory)))
    (len (mv-nth 0
                 (fat32-build-index-list (effective-fat fat32-in-memory)
                                         masked-current-cluster length
                                         (cluster-size fat32-in-memory))))))
  :hints
  (("goal"
    :in-theory (enable get-clusterchain-contents
                       make-clusters fat32-build-index-list)
    :induct (get-clusterchain-contents fat32-in-memory
                                       masked-current-cluster length)
    :expand
    ((make-clusters
      (implode (take length
                     (explode (data-regioni (+ -2 masked-current-cluster)
                                            fat32-in-memory))))
      (cluster-size fat32-in-memory))
     (make-clusters (data-regioni (+ -2 masked-current-cluster)
                                  fat32-in-memory)
                    (cluster-size fat32-in-memory))
     (make-clusters
      (implode
       (append
        (explode (data-regioni (+ -2 masked-current-cluster)
                               fat32-in-memory))
        (explode
         (mv-nth
          0
          (get-clusterchain-contents
           fat32-in-memory
           (fat32-entry-mask (fati masked-current-cluster fat32-in-memory))
           (+ length
              (- (cluster-size fat32-in-memory))))))))
      (cluster-size fat32-in-memory))))))

(defthmd
  lofat-to-hifat-helper-correctness-5-lemma-5
  (implies
   (equal (mv-nth 3
                  (lofat-to-hifat-helper fat32-in-memory
                                         dir-ent-list entry-limit))
          0)
   (equal (len (mv-nth 0
                       (lofat-to-hifat-helper fat32-in-memory
                                              dir-ent-list entry-limit)))
          (len dir-ent-list)))
  :hints (("goal" :in-theory (e/d (lofat-to-hifat-helper)
                                  ((:definition remove1-dir-ent)
                                   (:rewrite take-of-len-free)))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (equal (mv-nth 3
                    (lofat-to-hifat-helper fat32-in-memory
                                           dir-ent-list entry-limit))
            0)
     (equal (consp (mv-nth 0
                           (lofat-to-hifat-helper fat32-in-memory
                                                  dir-ent-list entry-limit)))
            (consp dir-ent-list))))))

(encapsulate
  ()

  (local (include-book "arithmetic-3/top" :dir :system))

  (defthmd
    lofat-to-hifat-helper-correctness-5-lemma-6
    (implies
     (and
      (lofat-fs-p fat32-in-memory)
      (equal (mv-nth 1
                     (get-clusterchain-contents fat32-in-memory
                                                masked-current-cluster length))
             0))
     (equal
      (len (mv-nth 0
                   (fat32-build-index-list (effective-fat fat32-in-memory)
                                           masked-current-cluster length
                                           (cluster-size fat32-in-memory))))
      (ceiling
       (len
        (explode
         (mv-nth 0
                 (get-clusterchain-contents fat32-in-memory
                                            masked-current-cluster length))))
       (cluster-size fat32-in-memory))))
    :hints
    (("goal"
      :in-theory (enable get-clusterchain-contents
                         fat32-build-index-list)
      :induct (get-clusterchain-contents fat32-in-memory
                                         masked-current-cluster length))))

  (defthm
    lofat-to-hifat-helper-correctness-5-lemma-7
    (implies
     (and
      (<=
       (hifat-cluster-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (mv-nth 0
                   (get-clusterchain-contents
                    fat32-in-memory
                    (dir-ent-first-cluster (car dir-ent-list))
                    2097152)))
          (+ -1 entry-limit)))
        (cluster-size fat32-in-memory))
       (len
        (flatten
         (mv-nth
          2
          (lofat-to-hifat-helper
           fat32-in-memory
           (make-dir-ent-list
            (mv-nth 0
                    (get-clusterchain-contents
                     fat32-in-memory
                     (dir-ent-first-cluster (car dir-ent-list))
                     2097152)))
           (+ -1 entry-limit))))))
      (<=
       (hifat-cluster-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32-in-memory (cdr dir-ent-list)
          (+
           -1 entry-limit
           (-
            (hifat-entry-count
             (mv-nth
              0
              (lofat-to-hifat-helper
               fat32-in-memory
               (make-dir-ent-list
                (mv-nth 0
                        (get-clusterchain-contents
                         fat32-in-memory
                         (dir-ent-first-cluster (car dir-ent-list))
                         2097152)))
               (+ -1 entry-limit))))))))
        (cluster-size fat32-in-memory))
       (len
        (flatten
         (mv-nth
          2
          (lofat-to-hifat-helper
           fat32-in-memory (cdr dir-ent-list)
           (+
            -1 entry-limit
            (-
             (hifat-entry-count
              (mv-nth
               0
               (lofat-to-hifat-helper
                fat32-in-memory
                (make-dir-ent-list
                 (mv-nth 0
                         (get-clusterchain-contents
                          fat32-in-memory
                          (dir-ent-first-cluster (car dir-ent-list))
                          2097152)))
                (+ -1 entry-limit)))))))))))
      (equal
       (mv-nth
        1
        (get-clusterchain-contents fat32-in-memory
                                   (dir-ent-first-cluster (car dir-ent-list))
                                   2097152))
       0)
      (subdir-contents-p
       (mv-nth
        0
        (get-clusterchain-contents fat32-in-memory
                                   (dir-ent-first-cluster (car dir-ent-list))
                                   2097152)))
      (lofat-fs-p fat32-in-memory))
     (<=
      (+
       (ceiling
        (+ 64
           (* 32
              (len (make-dir-ent-list
                    (mv-nth 0
                            (get-clusterchain-contents
                             fat32-in-memory
                             (dir-ent-first-cluster (car dir-ent-list))
                             2097152))))))
        (cluster-size fat32-in-memory))
       (hifat-cluster-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (mv-nth 0
                   (get-clusterchain-contents
                    fat32-in-memory
                    (dir-ent-first-cluster (car dir-ent-list))
                    2097152)))
          (+ -1 entry-limit)))
        (cluster-size fat32-in-memory))
       (hifat-cluster-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32-in-memory (cdr dir-ent-list)
          (+
           -1 entry-limit
           (-
            (hifat-entry-count
             (mv-nth
              0
              (lofat-to-hifat-helper
               fat32-in-memory
               (make-dir-ent-list
                (mv-nth 0
                        (get-clusterchain-contents
                         fat32-in-memory
                         (dir-ent-first-cluster (car dir-ent-list))
                         2097152)))
               (+ -1 entry-limit))))))))
        (cluster-size fat32-in-memory)))
      (+
       (len
        (mv-nth
         0
         (fat32-build-index-list (effective-fat fat32-in-memory)
                                 (dir-ent-first-cluster (car dir-ent-list))
                                 2097152
                                 (cluster-size fat32-in-memory))))
       (len
        (flatten
         (mv-nth
          2
          (lofat-to-hifat-helper
           fat32-in-memory
           (make-dir-ent-list
            (mv-nth 0
                    (get-clusterchain-contents
                     fat32-in-memory
                     (dir-ent-first-cluster (car dir-ent-list))
                     2097152)))
           (+ -1 entry-limit)))))
       (len
        (flatten
         (mv-nth
          2
          (lofat-to-hifat-helper
           fat32-in-memory (cdr dir-ent-list)
           (+
            -1 entry-limit
            (-
             (hifat-entry-count
              (mv-nth
               0
               (lofat-to-hifat-helper
                fat32-in-memory
                (make-dir-ent-list
                 (mv-nth 0
                         (get-clusterchain-contents
                          fat32-in-memory
                          (dir-ent-first-cluster (car dir-ent-list))
                          2097152)))
                (+ -1 entry-limit)))))))))))))
    :hints
    (("goal"
      :in-theory (e/d (subdir-contents-p)
                      ((:rewrite lofat-to-hifat-helper-correctness-5-lemma-6)))
      :use
      ((:instance
        (:linear len-of-make-dir-ent-list)
        (dir-contents
         (remove1-dir-ent
          (remove1-dir-ent
           (mv-nth 0
                   (get-clusterchain-contents
                    fat32-in-memory
                    (dir-ent-first-cluster (car dir-ent-list))
                    *ms-max-dir-size*))
           *current-dir-fat32-name*)
          *parent-dir-fat32-name*)))
       (:instance
        painful-debugging-lemma-16
        (i2 (- (length (mv-nth 0
                               (get-clusterchain-contents
                                fat32-in-memory
                                (dir-ent-first-cluster (car dir-ent-list))
                                *ms-max-dir-size*)))
               64))
        (i1
         (length
          (remove1-dir-ent
           (remove1-dir-ent
            (mv-nth 0
                    (get-clusterchain-contents
                     fat32-in-memory
                     (dir-ent-first-cluster (car dir-ent-list))
                     *ms-max-dir-size*))
            *current-dir-fat32-name*)
           *parent-dir-fat32-name*)))
        (j 32))
       (:instance
        (:rewrite lofat-to-hifat-helper-correctness-5-lemma-6)
        (length *ms-max-dir-size*)
        (masked-current-cluster (dir-ent-first-cluster (car dir-ent-list)))
        (fat32-in-memory fat32-in-memory))
       (:instance
        painful-debugging-lemma-16
        (i1
         (+
          64
          (*
           32
           (len
            (make-dir-ent-list
             (remove1-dir-ent
              (remove1-dir-ent
               (mv-nth 0
                       (get-clusterchain-contents
                        fat32-in-memory
                        (dir-ent-first-cluster (car dir-ent-list))
                        *ms-max-dir-size*))
               *current-dir-fat32-name*)
              *parent-dir-fat32-name*))))))
        (i2
         (len (explode (mv-nth 0
                               (get-clusterchain-contents
                                fat32-in-memory
                                (dir-ent-first-cluster (car dir-ent-list))
                                *ms-max-dir-size*)))))
        (j (cluster-size fat32-in-memory))))))))

(defthm
  lofat-to-hifat-helper-correctness-5
  (b* (((mv m1-file-alist
            & clusterchain-list error-code)
        (lofat-to-hifat-helper fat32-in-memory
                               dir-ent-list entry-limit)))
    (implies (and (lofat-fs-p fat32-in-memory)
                  (dir-ent-list-p dir-ent-list)
                  (equal error-code 0))
             (<= (hifat-cluster-count m1-file-alist
                                      (cluster-size fat32-in-memory))
                 (len (flatten clusterchain-list)))))
  :rule-classes :linear
  :hints
  (("goal" :in-theory (enable lofat-to-hifat-helper
                              hifat-cluster-count
                              lofat-to-hifat-helper-correctness-5-lemma-2
                              dir-ent-clusterchain
                              dir-ent-clusterchain-contents
                              lofat-to-hifat-helper-correctness-5-lemma-5)
    :induct (lofat-to-hifat-helper fat32-in-memory
                                   dir-ent-list entry-limit)
    :expand (make-clusters "" (cluster-size fat32-in-memory)))))

(defthm
  lofat-to-hifat-inversion-lemma-1
  (implies
   (and (natp start)
        (natp n)
        (<= (+ start (nfix len)) (len fa-table))
        (<= start (nfix n))
        (< (nfix n) (+ start (nfix len))))
   (equal
    (fat32-entry-mask
     (nth n
          (set-indices-in-fa-table
           fa-table (generate-index-list start len)
           (make-list-ac len 0 nil))))
    0))
  :hints (("goal" :in-theory (e/d (set-indices-in-fa-table)
                                  (make-list-ac))
           :induct (generate-index-list start len))))

(defthm
  lofat-to-hifat-inversion-lemma-2
  (implies
   (and (natp n)
        (<= (+ n 2) (len fa-table)))
   (equal
    (count-free-clusters-helper
     (nthcdr
      2
      (set-indices-in-fa-table fa-table
                               (generate-index-list 2 (+ -2 (len fa-table)))
                               (make-list-ac (+ -2 (len fa-table))
                                             0 nil)))
     n)
    n))
  :hints
  (("goal"
    :in-theory
    (e/d nil
         (generate-index-list make-list-ac nthcdr (:induction len)))
    :induct
    (count-free-clusters-helper
     (nthcdr
      2
      (set-indices-in-fa-table fa-table
                               (generate-index-list 2 (+ -2 (len fa-table)))
                               (make-list-ac (+ -2 (len fa-table))
                                             0 nil)))
     n))))

(defthm
  lofat-to-hifat-inversion-lemma-3
  (implies
   (<= 2 (len fa-table))
   (equal
    (count-free-clusters
     (set-indices-in-fa-table fa-table
                              (generate-index-list 2 (- (len fa-table) 2))
                              (make-list-ac (- (len fa-table) 2)
                                            0 nil)))
    (- (len fa-table) 2)))
  :hints (("goal" :in-theory (e/d (count-free-clusters)
                                  (make-list-ac)))))

(defthm
  lofat-to-hifat-inversion-lemma-5
  (implies
   (not (zp cluster-size))
   (equal
    (len
     (make-clusters
      (implode$inline (make-list-ac cluster-size val 'nil))
      cluster-size))
    1))
  :hints
  (("goal"
    :in-theory (disable make-list-ac)
    :expand
    ((make-clusters
      (implode$inline (make-list-ac cluster-size val 'nil))
      cluster-size)
     (make-clusters "" cluster-size)))))

;; The make-event is there to avoid writing out the value of (code-char 0),
;; which makes git assess this file as a binary file and messes up the ability
;; to do git diff and git merge.
(make-event
 `(defthm
    lofat-to-hifat-inversion-lemma-6
    (implies
     (and
      (equal
       (count-free-clusters
        (set-indices-in-fa-table
         (effective-fat fat32-in-memory)
         (generate-index-list 2 (count-of-clusters fat32-in-memory))
         (make-list-ac (count-of-clusters fat32-in-memory)
                       0 nil)))
       (count-of-clusters fat32-in-memory))
      (lofat-fs-p fat32-in-memory))
     (equal
      (root-dir-ent-list
       (mv-nth
        0
        (place-contents
         (update-fati
          (fat32-entry-mask (bpb_rootclus fat32-in-memory))
          (fat32-update-lower-28
           (fati
            (fat32-entry-mask (bpb_rootclus fat32-in-memory))
            (stobj-set-indices-in-fa-table
             fat32-in-memory
             (generate-index-list 2 (count-of-clusters fat32-in-memory))
             (make-list-ac (count-of-clusters fat32-in-memory)
                           0 nil)))
           *ms-end-of-clusterchain*)
          (stobj-set-indices-in-fa-table
           fat32-in-memory
           (generate-index-list 2 (count-of-clusters fat32-in-memory))
           (make-list-ac (count-of-clusters fat32-in-memory)
                         0 nil)))
         ,(quote (make-list-ac 32 0 nil))
         (implode (make-list-ac (cluster-size fat32-in-memory)
                                ,(code-char 0) nil))
         0
         (fat32-entry-mask (bpb_rootclus fat32-in-memory)))))
      (mv nil 0)))
    :hints (("goal" :in-theory
             (e/d (root-dir-ent-list)
                  ((:rewrite place-contents-expansion-2)))
             :use (:instance
                   (:rewrite place-contents-expansion-2) (first-cluster
                      (fat32-entry-mask (bpb_rootclus fat32-in-memory)))
                 (file-length 0)
                 (contents
                      (implode (make-list-ac (cluster-size fat32-in-memory)
                                             (code-char 0) nil)))
                 (dir-ent (make-list-ac 32 0 nil))
                 (fat32-in-memory
                  (update-fati
                   (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                   (fat32-update-lower-28
                    (fati
                       (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                       (stobj-set-indices-in-fa-table
                            fat32-in-memory
                            (generate-index-list
                                 2 (count-of-clusters fat32-in-memory))
                            (make-list-ac (count-of-clusters fat32-in-memory)
                                          0 nil)))
                    268435455)
                   (stobj-set-indices-in-fa-table
                        fat32-in-memory
                        (generate-index-list
                             2 (count-of-clusters fat32-in-memory))
                        (make-list-ac (count-of-clusters fat32-in-memory)
                                      0 nil)))))))))

(defthm
  lofat-to-hifat-inversion-lemma-8
  (implies
   (and
    (equal
     (count-free-clusters
      (set-indices-in-fa-table
       (effective-fat fat32-in-memory)
       (generate-index-list 2 (count-of-clusters fat32-in-memory))
       (make-list-ac (count-of-clusters fat32-in-memory)
                     0 nil)))
     (count-of-clusters fat32-in-memory))
    (lofat-fs-p fat32-in-memory)
    (<= (hifat-cluster-count
         (mv-nth 0
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  (mv-nth 0 (root-dir-ent-list fat32-in-memory))
                  (max-entry-count fat32-in-memory)))
         (cluster-size fat32-in-memory))
        (+ -1
           (count-of-clusters fat32-in-memory))))
   (equal
    (mv-nth
     '2
     (hifat-to-lofat-helper
      (update-fati
       (fat32-entry-mask (bpb_rootclus fat32-in-memory))
       (fat32-update-lower-28
        (fati (fat32-entry-mask (bpb_rootclus fat32-in-memory))
              (stobj-set-indices-in-fa-table
               fat32-in-memory
               (generate-index-list '2
                                    (count-of-clusters fat32-in-memory))
               (make-list-ac (count-of-clusters fat32-in-memory)
                             '0
                             'nil)))
        '268435455)
       (stobj-set-indices-in-fa-table
        fat32-in-memory
        (generate-index-list '2
                             (count-of-clusters fat32-in-memory))
        (make-list-ac (count-of-clusters fat32-in-memory)
                      '0
                      'nil)))
      (mv-nth '0
              (lofat-to-hifat-helper
               fat32-in-memory
               (mv-nth '0
                       (root-dir-ent-list fat32-in-memory))
               (max-entry-count fat32-in-memory)))
      (fat32-entry-mask (bpb_rootclus fat32-in-memory))))
    0))
  :hints
  (("goal"
    :in-theory (e/d (lofat-to-hifat hifat-to-lofat
                                    hifat-to-lofat-inversion-lemma-17)
                    (lofat-to-hifat-inversion-lemma-3 generate-index-list)))))

(defthm
  lofat-to-hifat-inversion-lemma-9
  (implies (lofat-fs-p fat32-in-memory)
           (< (fat32-entry-mask (bpb_rootclus fat32-in-memory))
              (fat-entry-count fat32-in-memory))))

(defthmd
  lofat-to-hifat-inversion-lemma-4
  (implies (not (zp cluster-size))
           (equal (len (make-clusters (nats=>string nats)
                                      cluster-size))
                  (ceiling (len nats)
                           cluster-size)))
  :hints (("goal" :in-theory (enable len-of-make-clusters))))

(defthm
  lofat-to-hifat-inversion-lemma-10
  (implies
   (lofat-fs-p fat32-in-memory)
   (equal
    (count-free-clusters
     (set-indices-in-fa-table
      (effective-fat fat32-in-memory)
      (generate-index-list
       2 (count-of-clusters fat32-in-memory))
      (make-list-ac (count-of-clusters fat32-in-memory)
                    0 nil)))
    (count-of-clusters fat32-in-memory)))
  :hints
  (("goal"
    :in-theory (disable lofat-to-hifat-inversion-lemma-3
                        generate-index-list make-list-ac)
    :use
    (:instance lofat-to-hifat-inversion-lemma-3
               (fa-table (effective-fat fat32-in-memory))))))

(defthmd
  lofat-to-hifat-inversion-lemma-15
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (equal (mv-nth 1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
           0))
   (equal
    (len (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory dir-ent)))
    (ceiling
     (len
      (explode
       (mv-nth 0
               (dir-ent-clusterchain-contents fat32-in-memory dir-ent))))
     (cluster-size fat32-in-memory))))
  :hints
  (("goal"
    :in-theory (enable dir-ent-clusterchain-contents dir-ent-clusterchain
                       lofat-to-hifat-helper-correctness-5-lemma-6))))

(encapsulate
  ()

  (local (include-book "arithmetic-3/top" :dir :system))

  (set-default-hints
   '((nonlinearp-default-hint stable-under-simplificationp
                              hist pspv)))

  (defthm
    lofat-to-hifat-inversion-lemma-11
    (implies
     (equal (len (mv-nth 0
                         (fat32-build-index-list
                          (effective-fat fat32-in-memory)
                          (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                          *ms-max-dir-size*
                          (cluster-size fat32-in-memory))))
            0)
     (equal (mv-nth 0 (root-dir-ent-list fat32-in-memory))
            nil))
    :hints
    (("goal"
      :cases
      ((and
        (lofat-fs-p fat32-in-memory)
        (equal (mv-nth 1
                       (get-clusterchain-contents
                        fat32-in-memory
                        (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                        2097152))
               0)
        (equal
         (len
          (explode
           (mv-nth 0
                   (get-clusterchain-contents
                    fat32-in-memory
                    (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                    2097152))))
         0)))
      :in-theory
      (e/d (root-dir-ent-list lofat-to-hifat-helper-correctness-5-lemma-2
                              pseudo-root-dir-ent dir-ent-clusterchain-contents
                              lofat-to-hifat-helper-correctness-5-lemma-6))
      :use
      (:instance
       length-of-empty-list
       (x (mv-nth 0
                  (get-clusterchain-contents
                   fat32-in-memory
                   (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                   2097152)))))))

  (defthm
    lofat-to-hifat-inversion-lemma-12
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (consp (mv-nth 0 (root-dir-ent-list fat32-in-memory))))
     (< 0
        (ceiling (* 32
                    (len (mv-nth 0
                                 (root-dir-ent-list fat32-in-memory))))
                 (cluster-size fat32-in-memory))))
    :rule-classes :linear
    :hints
    (("goal" :expand (len (mv-nth 0
                                  (root-dir-ent-list fat32-in-memory))))))

  (defthm
    lofat-to-hifat-inversion-lemma-13
    (implies
     (and
      (<=
       (+
        (len
         (flatten
          (mv-nth
           2
           (lofat-to-hifat-helper fat32-in-memory
                                  (mv-nth 0 (root-dir-ent-list fat32-in-memory))
                                  (max-entry-count fat32-in-memory)))))
        (len (mv-nth 0
                     (fat32-build-index-list
                      (effective-fat fat32-in-memory)
                      (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                      *ms-max-dir-size*
                      (cluster-size fat32-in-memory)))))
       (count-of-clusters fat32-in-memory))
      (lofat-fs-p fat32-in-memory)
      (equal (mv-nth 1
                     (get-clusterchain-contents
                      fat32-in-memory
                      (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                      *ms-max-dir-size*))
             0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper fat32-in-memory
                               (mv-nth 0 (root-dir-ent-list fat32-in-memory))
                               (max-entry-count fat32-in-memory)))
       0))
     (>=
      (count-of-clusters fat32-in-memory)
      (+
       (hifat-cluster-count
        (mv-nth
         0
         (lofat-to-hifat-helper fat32-in-memory
                                (mv-nth 0 (root-dir-ent-list fat32-in-memory))
                                (max-entry-count fat32-in-memory)))
        (cluster-size fat32-in-memory))
       (ceiling
        (* 32
           (len (mv-nth 0
                        (root-dir-ent-list fat32-in-memory))))
        (cluster-size fat32-in-memory)))))
    :rule-classes :linear
    :hints
    (("goal"
      :in-theory (e/d (root-dir-ent-list pseudo-root-dir-ent
                                         dir-ent-clusterchain-contents
                                         lofat-to-hifat-helper-correctness-5-lemma-6))
      :use
      (:instance
       len-of-make-dir-ent-list
       (dir-contents
        (mv-nth 0
                (get-clusterchain-contents
                 fat32-in-memory
                 (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                 *ms-max-dir-size*))))))))

(defthm
  lofat-to-hifat-inversion-lemma-14
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (equal (mv-nth 1 (lofat-to-hifat fat32-in-memory))
               0))
   (equal
    (mv-nth 1
            (hifat-to-lofat fat32-in-memory
                            (mv-nth 0 (lofat-to-hifat fat32-in-memory))))
    0))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lofat-to-hifat hifat-to-lofat
                     hifat-to-lofat-inversion-lemma-17
                     lofat-to-hifat-inversion-lemma-4
                     lofat-to-hifat-helper-correctness-5-lemma-5
                     dir-ent-clusterchain pseudo-root-dir-ent)
     (lofat-to-hifat-inversion-lemma-3 generate-index-list
                                       non-free-index-listp-correctness-6))
    :use
    (:instance
     non-free-index-listp-correctness-6
     (x
      (append
       (mv-nth 0
               (fat32-build-index-list
                (effective-fat fat32-in-memory)
                (fat32-entry-mask (bpb_rootclus fat32-in-memory))
                2097152 (cluster-size fat32-in-memory)))
       (flatten (mv-nth 2
                        (lofat-to-hifat-helper
                         fat32-in-memory
                         (mv-nth 0 (root-dir-ent-list fat32-in-memory))
                         (max-entry-count fat32-in-memory))))))
     (fa-table (effective-fat fat32-in-memory))))))

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

;; The proof of this theorem, and the subsequent removal of its hypotheses,
;; have significantly influenced the development of the model. We really want
;; the number of hypotheses for lofat-equiv to be the bare minimum, because
;; lofat-equiv is just an important predicate, around which we are building a
;; number of proofs. The git history will show the precise details, but at
;; various points we've removed hypotheses stating that the outcome of
;; lofat-to-hifat satisfied hifat-bounded-file-alist-p and
;; hifat-file-no-dups-p. The following paragraphs, written at an earlier point,
;; describe why one of these clauses was hard to remove. We ultimately removed
;; it by requiring all clusterchains to be distinct from each other.
;;
;; This clause should almost always be true (which is a difficult thing to say
;; in a theorem-proving setting...) The argument is: The only time we get an
;; error out of hifat-to-lofat-helper (and the wrapper) is when we run out of
;; space. We shouldn't be able to run out of space when we just extracted an m1
;; instance from fat32-in-memory, and we didn't change the size of
;; fat32-in-memory at all. However, that's going to involve reasoning about the
;; number of clusters taken up by an m1 instance, which is not really where
;; it's at right now.
;;
;; One reason why this clause will not always be true: we aren't
;; requiring dot and dotdot entries to exist (except vaguely, by making
;; sure that we don't have 65535 or 65536 useful directory entries in
;; any directory.)  As a result, it's possible for a lofat instance to
;; exist which completely fills up the available clusters on the disk,
;; but which leaves out at least one dot or dotdot entry, with the
;; result that attempting to remake the stobj after converting to hifat
;; would cause the directory with the missing dot/dotdot entry to cross
;; a cluster boundary and therefore occupy more space than available in
;; the stobj. This scenario wouldn't even need a directory with 65535 or
;; 65536 useful directory entries. The largest possible cluster size for
;; FAT32 is 2^15 bytes, which is a multiple of all other possible
;; cluster sizes - so let's consider an example where a directory
;; contains 2^11 useful directory entries and no dot or dotdot entries,
;; completely filling 2, 4, 8, or however many clusters. Then, when we
;; write back this directory, we'll have 3 clusters occupied by this
;; directory, or 5 or 9 or something. The problem is clear.
;;
;; One solution is to return a non-zero error code when a directory is
;; encountered without a dot or dotdot entry in it. Anything else wrecks
;; our guarantees that the transformation from lofat to hifat is
;; reversible. Then, the reasoning will involve the number of clusters
;; taken up for the on-disk representation of a lofat instance. That
;; reasoning will also involve proving that we can allocate upto
;; (count-of-clusters fat32-in-memory) clusters and no more.
;; But, this solution is not perfect - there still remains the problem
;; of clusters being shared across multiple files. So, if cluster 2
;; begins the root directory's clusterchain, and cluster 3 begins a
;; different clusterchain of length 1, then the rest of the clusters
;; could be filled up with directory files in which all the regular
;; file entries point to cluster 3. This would create a filesystem with
;; a huge number of identical files, and after converting it to HiFAT we
;; wouldn't be able to convert it back to LoFAT because of space
;; issues. There's no simple solution to this thing other than insisting
;; that all clusterchains should be disjoint from each other.
;;
;; By the way, what are our guarantees? We assure that a lofat instance
;; which can successfully be transformed to a hifat instance has no more
;; than (max-entry-count fat32-in-memory) directory entries, no
;; duplicate entries in any directory and no directories with more than
;; 2^16 - 2 useful entries. What about directories which blow past 2^16
;; entries altogether? Those will be caught thanks to the error code of
;; get-clusterchain-contents.
(defthm
  lofat-to-hifat-inversion
  (implies
   (lofat-fs-p fat32-in-memory)
   (b*
       (((mv fs error-code)
         (lofat-to-hifat fat32-in-memory)))
     (implies
      (equal error-code 0)
      (lofat-equiv
       (mv-nth
        0
        (hifat-to-lofat
         fat32-in-memory
         fs))
       fat32-in-memory))))
  :hints (("Goal" :in-theory (enable lofat-equiv)) ))
