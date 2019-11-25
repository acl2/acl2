(in-package "ACL2")

(include-book "hifat-to-lofat-inversion")
(include-book "lofat-to-string-inversion")

;  lofat.lisp                                           Mihir Mehta

; This is a stobj model of the FAT32 filesystem.

;; These are some rules from other books which are either interacting badly
;; with the theory I've built up so far, or else causing a lot of unnecessary
;; frames and tries.
(local
 (in-theory (disable take-of-too-many make-list-ac-removal
                     revappend-removal str::hex-digit-listp-of-cons
                     loghead logtail)))

(local
 (in-theory (disable nth update-nth floor mod true-listp take member-equal)))

(local
 (in-theory (disable non-free-index-list-listp-correctness-1
                     intersectp-member-when-not-member-intersectp
                     no-duplicatesp-of-member
                     free-index-list-listp-correctness-1)))

(defund-nx
  eqfat (str1 str2)
  (b*
      (((mv fat32-in-memory1 error-code1)
        (string-to-lofat-nx str1))
       (good1 (and (stringp str1) (equal error-code1 0)))
       ((mv fat32-in-memory2 error-code2)
        (string-to-lofat-nx str2))
       (good2 (and (stringp str2) (equal error-code2 0)))
       ((unless (and good1 good2))
        (and (not good1) (not good2))))
    (lofat-equiv fat32-in-memory1 fat32-in-memory2)))

(defequiv
  eqfat
  :hints (("goal" :in-theory (enable eqfat))))

(defthm
  string-to-lofat-inversion
  (implies
   (and (stringp str)
        (fat32-in-memoryp fat32-in-memory)
        (equal (mv-nth 1 (string-to-lofat fat32-in-memory str))
               0))
   (eqfat (lofat-to-string
           (mv-nth 0
                   (string-to-lofat fat32-in-memory str)))
          str))
  :hints
  (("goal"
    :in-theory (e/d (eqfat)
                    (create-fat32-in-memory
                     (:rewrite lofat-to-string-inversion)))
    :use
    ((:instance
      (:rewrite lofat-to-string-inversion)
      (fat32-in-memory
       (mv-nth 0
               (string-to-lofat (create-fat32-in-memory)
                                str))))
     (:instance
      (:rewrite string-to-lofat-ignore-lemma-14)
      (str
       (lofat-to-string
        (mv-nth 0
                (string-to-lofat (create-fat32-in-memory)
                                 str))))
      (fat32-in-memory
       (mv-nth 0
               (string-to-lofat (create-fat32-in-memory)
                                str))))
     string-to-lofat-ignore-lemma-14))))

(defthm
  hifat-to-string-inversion
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (m1-file-alist-p fs)
        (hifat-bounded-file-alist-p fs)
        (hifat-no-dups-p fs)
        (<= (hifat-entry-count fs)
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
      (and (equal error-code1 0)
           (equal error-code2 0)
           (hifat-bounded-file-alist-p fs)
           (hifat-no-dups-p fs)
           (equal (mv-nth 1 (hifat-to-lofat fat32-in-memory fs))
                  0))
      (eqfat (lofat-to-string
              (mv-nth 0 (hifat-to-lofat fat32-in-memory fs)))
             str))))
  :hints
  (("goal"
    :in-theory (e/d (eqfat)
                    ((:rewrite lofat-to-string-inversion)
                     (:rewrite string-to-lofat-ignore)))
    :use
    ((:instance
      (:rewrite lofat-to-string-inversion)
      (fat32-in-memory
       (mv-nth
        0
        (hifat-to-lofat
         (mv-nth 0 (string-to-lofat-nx str))
         (mv-nth 0
                 (lofat-to-hifat
                  (mv-nth 0 (string-to-lofat-nx str))))))))
     (:instance
      (:rewrite string-to-lofat-ignore)
      (str
       (lofat-to-string
        (mv-nth
         0
         (hifat-to-lofat
          (mv-nth 0 (string-to-lofat-nx str))
          (mv-nth 0
                  (lofat-to-hifat
                   (mv-nth 0 (string-to-lofat-nx str))))))))
      (fat32-in-memory
       (mv-nth
        0
        (hifat-to-lofat
         (mv-nth 0 (string-to-lofat-nx str))
         (mv-nth 0
                 (lofat-to-hifat
                  (mv-nth 0 (string-to-lofat-nx str))))))))
     (:rewrite string-to-lofat-ignore)
     string-to-lofat-ignore-lemma-14
     (:instance
      (:rewrite string-to-lofat-ignore-lemma-14)
      (str
       (lofat-to-string
        (mv-nth
         0
         (hifat-to-lofat
          (mv-nth 0 (string-to-lofat fat32-in-memory str))
          (mv-nth
           0
           (lofat-to-hifat
            (mv-nth 0
                    (string-to-lofat fat32-in-memory str))))))))
      (fat32-in-memory
       (mv-nth
        0
        (hifat-to-lofat
         (mv-nth 0 (string-to-lofat fat32-in-memory str))
         (mv-nth
          0
          (lofat-to-hifat
           (mv-nth 0
                   (string-to-lofat fat32-in-memory str))))))))
     (:instance
      (:rewrite lofat-to-string-inversion)
      (fat32-in-memory
       (mv-nth
        0
        (hifat-to-lofat
         (mv-nth 0 (string-to-lofat fat32-in-memory str))
         (mv-nth
          0
          (lofat-to-hifat
           (mv-nth
            0
            (string-to-lofat fat32-in-memory str))))))))))))

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
  lofat-regular-file-p-correctness-2
  (implies
   (lofat-regular-file-p file)
   (stringp (lofat-file->contents file)))
  :hints (("goal" :in-theory (enable lofat-regular-file-p))))

(defthm
  lofat-directory-file-p-correctness-1
  (implies
   (stringp contents)
   (not (lofat-directory-file-p (lofat-file dir-ent contents))))
  :hints (("goal" :in-theory (enable lofat-directory-file-p))))

(defthm
  lofat-directory-file-p-correctness-2
  (implies (lofat-regular-file-p file)
           (not (lofat-directory-file-p file)))
  :hints (("goal" :in-theory (enable lofat-directory-file-p
                                     lofat-regular-file-p))))

(defthm
  lofat-directory-file-p-when-lofat-file-p
  (implies (and (lofat-file-p file)
                (not (lofat-regular-file-p file)))
           (lofat-directory-file-p file))
  :hints (("goal" :in-theory (enable lofat-directory-file-p
                                     lofat-regular-file-p lofat-file-p
                                     lofat-file-contents-p
                                     lofat-file->contents))))

(defun lofat-find-file (fat32-in-memory dir-ent-list pathname)
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
       ((mv contents &)
        (if
            (or (< first-cluster
                   *ms-first-data-cluster*)
                (>=
                 first-cluster
                 (+ (count-of-clusters fat32-in-memory)
                    *ms-first-data-cluster*)))
            (mv "" 0)
          (dir-ent-clusterchain-contents
           fat32-in-memory dir-ent)))
       ((unless directory-p)
        (if (consp (cdr pathname))
            (mv (make-lofat-file) *enotdir*)
          (mv (make-lofat-file :dir-ent dir-ent :contents contents) 0)))
       ((when (atom (cdr pathname)))
        (mv
         (make-lofat-file :dir-ent dir-ent
                          :contents (make-dir-ent-list contents))
         0)))
    (lofat-find-file
     fat32-in-memory (make-dir-ent-list contents) (cdr pathname))))

(defthm
  lofat-find-file-correctness-1-lemma-2
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
  lofat-find-file-correctness-1-lemma-3
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
  lofat-find-file-correctness-1-lemma-4
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
      (dir-ent-clusterchain-contents
       fat32-in-memory
       (mv-nth 0 (find-dir-ent dir-ent-list name))))
     :dir-ent (mv-nth 0 (find-dir-ent dir-ent-list name)))))
  :hints
  (("goal"
    :in-theory (enable lofat-to-hifat-helper))))

(defthm
  lofat-find-file-correctness-1-lemma-5
  (implies
   (and (useful-dir-ent-list-p dir-ent-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper
                        fat32-in-memory
                        dir-ent-list entry-limit))
               0))
   (equal
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

;; Also general.
(defthm
  lofat-find-file-correctness-1-lemma-6
  (implies
   (and (dir-ent-directory-p (mv-nth 0 (find-dir-ent dir-ent-list name)))
        (useful-dir-ent-list-p dir-ent-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32-in-memory
                                              dir-ent-list entry-limit))
               0))
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents
                 fat32-in-memory
                 (mv-nth 0 (find-dir-ent dir-ent-list name)))))
       entry-limit))
     0)
    (<
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32-in-memory
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents
                  fat32-in-memory
                  (mv-nth 0 (find-dir-ent dir-ent-list name)))))
        entry-limit)))
     entry-limit)))
  :hints
  (("goal"
    :induct (mv (mv-nth 3
                        (lofat-to-hifat-helper fat32-in-memory
                                               dir-ent-list entry-limit))
                (mv-nth 0 (find-dir-ent dir-ent-list name)))
    :in-theory
    (e/d (lofat-to-hifat-helper-correctness-4 lofat-to-hifat-helper)
         ((:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
          (:definition free-index-listp)
          (:rewrite nth-of-effective-fat)
          (:definition no-duplicatesp-equal)))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (dir-ent-directory-p (mv-nth 0 (find-dir-ent dir-ent-list name)))
          (useful-dir-ent-list-p dir-ent-list)
          (equal (mv-nth 3
                         (lofat-to-hifat-helper fat32-in-memory
                                                dir-ent-list entry-limit))
                 0))
     (equal
      (mv-nth
       3
       (lofat-to-hifat-helper
        fat32-in-memory
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents
                  fat32-in-memory
                  (mv-nth 0 (find-dir-ent dir-ent-list name)))))
        entry-limit))
      0)))
   (:linear
    :corollary
    (implies
     (and (dir-ent-directory-p (mv-nth 0 (find-dir-ent dir-ent-list name)))
          (useful-dir-ent-list-p dir-ent-list)
          (equal (mv-nth 3
                         (lofat-to-hifat-helper fat32-in-memory
                                                dir-ent-list entry-limit))
                 0))
     (<
      (hifat-entry-count
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32-in-memory
         (make-dir-ent-list
          (mv-nth 0
                  (dir-ent-clusterchain-contents
                   fat32-in-memory
                   (mv-nth 0 (find-dir-ent dir-ent-list name)))))
         entry-limit)))
      entry-limit)))
   (:forward-chaining
    :corollary
    (implies
     (and (dir-ent-directory-p (mv-nth 0 (find-dir-ent dir-ent-list name)))
          (useful-dir-ent-list-p dir-ent-list)
          (equal (mv-nth 3
                         (lofat-to-hifat-helper fat32-in-memory
                                                dir-ent-list entry-limit))
                 0))
     (equal
      (mv-nth
       3
       (lofat-to-hifat-helper
        fat32-in-memory
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents
                  fat32-in-memory
                  (mv-nth 0 (find-dir-ent dir-ent-list name)))))
        entry-limit))
      0))
    :trigger-terms
    ((lofat-to-hifat-helper
      fat32-in-memory
      (make-dir-ent-list
       (mv-nth 0
               (dir-ent-clusterchain-contents
                fat32-in-memory
                (mv-nth 0 (find-dir-ent dir-ent-list name)))))
      entry-limit)))))

(defthm
  lofat-find-file-correctness-1-lemma-11
  (implies
   (and (useful-dir-ent-list-p dir-ent-list)
        (not (zp entry-limit)))
   (>=
    entry-limit
    (hifat-entry-count
     (mv-nth
      '0
      (lofat-to-hifat-helper
       fat32-in-memory (cdr dir-ent-list)
       (binary-+
        '-1
        (binary-+
         entry-limit
         (unary--
          (hifat-entry-count
           (mv-nth
            '0
            (lofat-to-hifat-helper
             fat32-in-memory
             (make-dir-ent-list
              (mv-nth '0
                      (dir-ent-clusterchain-contents
                       fat32-in-memory (car dir-ent-list))))
             (binary-+ '-1 entry-limit))))))))))))
  :hints
  (("goal"
    :in-theory (disable (:linear lofat-to-hifat-helper-correctness-3))
    :use
    (:instance
     (:linear lofat-to-hifat-helper-correctness-3)
     (entry-limit
      (+
       -1 entry-limit
       (-
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  (make-dir-ent-list
                   (mv-nth 0
                           (dir-ent-clusterchain-contents
                            fat32-in-memory (car dir-ent-list))))
                  (+ -1 entry-limit)))))))
     (dir-ent-list (cdr dir-ent-list))
     (fat32-in-memory fat32-in-memory))))
  :rule-classes :linear)

(defthm
  lofat-find-file-correctness-1-lemma-7
  (implies
   (and (dir-ent-directory-p (mv-nth 0 (find-dir-ent dir-ent-list name)))
        (useful-dir-ent-list-p dir-ent-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32-in-memory
                                              dir-ent-list entry-limit))
               0))
   (equal
    (cdr (assoc-equal
          name
          (mv-nth 0
                  (lofat-to-hifat-helper fat32-in-memory
                                         dir-ent-list entry-limit))))
    (make-m1-file
     :dir-ent (mv-nth 0 (find-dir-ent dir-ent-list name))
     :contents
     (mv-nth
      0
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents
          fat32-in-memory
          (mv-nth 0 (find-dir-ent dir-ent-list name)))))
       entry-limit)))))
  :hints
  (("goal" :in-theory (enable lofat-to-hifat-helper-correctness-4)
    :induct (find-dir-ent dir-ent-list name)
    :expand (lofat-to-hifat-helper fat32-in-memory
                                   dir-ent-list entry-limit))))

(defthm
  lofat-find-file-correctness-1-lemma-8
  (implies
   (and (dir-ent-directory-p (mv-nth 0 (find-dir-ent dir-ent-list name)))
        (useful-dir-ent-list-p dir-ent-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32-in-memory
                                              dir-ent-list entry-limit))
               0))
   (and
    (<= 2
        (dir-ent-first-cluster (mv-nth 0 (find-dir-ent dir-ent-list name))))
    (< (dir-ent-first-cluster (mv-nth 0 (find-dir-ent dir-ent-list name)))
       (+ 2
          (count-of-clusters fat32-in-memory)))))
  :hints (("goal" :in-theory (enable lofat-to-hifat-helper-correctness-4)
           :induct (find-dir-ent dir-ent-list name)
           :expand ((lofat-to-hifat-helper fat32-in-memory
                                           dir-ent-list entry-limit)
                    (lofat-to-hifat-helper fat32-in-memory
                                           nil (+ -1 entry-limit)))))
  :rule-classes :linear)

(defthm
  lofat-find-file-correctness-1
  (b*
      (((mv file error-code)
        (hifat-find-file
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
        (lofat-find-file fat32-in-memory
                         dir-ent-list pathname))))
     (equal (lofat-find-file
             fat32-in-memory dir-ent-list pathname)
            (mv (make-lofat-file :contents (m1-file->contents file)
                                 :dir-ent (m1-file->dir-ent file))
                error-code))))
  :hints (("Goal" :in-theory (enable hifat-find-file)) ))

(defthm
  lofat-find-file-correctness-2
  (b*
      (((mv file error-code)
        (hifat-find-file
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
        (lofat-find-file fat32-in-memory
                         dir-ent-list pathname))))
     (and
      (equal
       (lofat-file->dir-ent
        (mv-nth 0
                (lofat-find-file
                 fat32-in-memory dir-ent-list pathname)))
       (m1-file->dir-ent file))
      (equal
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32-in-memory
         (lofat-file->contents
          (mv-nth 0
                  (lofat-find-file
                   fat32-in-memory dir-ent-list pathname)))
         entry-limit))
       (m1-file->contents file))
      (equal
       (mv-nth 1
               (lofat-find-file
                fat32-in-memory dir-ent-list pathname))
       error-code))))
  :hints
  (("goal" :in-theory (enable hifat-find-file)
    :induct
    (mv (mv-nth 0
                (hifat-find-file
                 (mv-nth 0
                         (lofat-to-hifat-helper
                          fat32-in-memory
                          dir-ent-list entry-limit))
                 pathname))
        (mv-nth 0
                (lofat-find-file
                 fat32-in-memory dir-ent-list pathname)))
    :expand (lofat-to-hifat-helper
             fat32-in-memory nil entry-limit))))

(defthm
  lofat-find-file-correctness-3
  (and
   (lofat-file-p
    (mv-nth
     0
     (lofat-find-file fat32-in-memory dir-ent-list pathname)))
   (integerp (mv-nth 1
                     (lofat-find-file fat32-in-memory
                                      dir-ent-list pathname))))
  :hints (("goal" :induct t))
  :rule-classes
  ((:type-prescription
    :corollary
    (integerp (mv-nth 1
                      (lofat-find-file fat32-in-memory
                                       dir-ent-list pathname))))
   (:rewrite
    :corollary
    (lofat-file-p
     (mv-nth 0
             (lofat-find-file fat32-in-memory
                              dir-ent-list pathname))))))

(defun
    place-dir-ent (dir-ent-list dir-ent)
  (declare (xargs :guard (and (dir-ent-p dir-ent)
                              (dir-ent-list-p dir-ent-list))))
  (b*
      ((dir-ent (mbe :exec dir-ent
                     :logic (dir-ent-fix dir-ent)))
       ((when (atom dir-ent-list))
        (list dir-ent))
       ((when (equal (dir-ent-filename dir-ent)
                     (dir-ent-filename (car dir-ent-list))))
        (list*
         dir-ent
         (mbe :exec (cdr dir-ent-list)
              :logic (dir-ent-list-fix (cdr dir-ent-list))))))
    (list* (mbe :logic (dir-ent-fix (car dir-ent-list))
                :exec (car dir-ent-list))
           (place-dir-ent (cdr dir-ent-list)
                          dir-ent))))

(defthm dir-ent-list-p-of-place-dir-ent
  (dir-ent-list-p (place-dir-ent dir-ent-list dir-ent)))

(defthm find-dir-ent-of-place-dir-ent
  (implies (dir-ent-list-p dir-ent-list)
           (equal (find-dir-ent (place-dir-ent dir-ent-list dir-ent)
                                filename)
                  (if (equal (dir-ent-filename dir-ent)
                             filename)
                      (mv (dir-ent-fix dir-ent) 0)
                      (find-dir-ent dir-ent-list filename)))))

(defthm
  place-dir-ent-of-dir-ent-fix
  (equal (place-dir-ent dir-ent-list (dir-ent-fix dir-ent))
         (place-dir-ent dir-ent-list dir-ent))
  :hints (("goal" :in-theory (enable place-dir-ent))))

(defcong dir-ent-equiv equal
  (place-dir-ent dir-ent-list dir-ent)
  2)

(defthm
  len-of-place-dir-ent
  (equal
   (len (place-dir-ent dir-ent-list dir-ent))
   (if (zp (mv-nth 1
                   (find-dir-ent dir-ent-list
                                 (dir-ent-filename dir-ent))))
       (len dir-ent-list)
       (+ 1 (len dir-ent-list)))))

(defthm
  useful-dir-ent-list-p-of-place-dir-ent
  (implies
   (and (useful-dir-ent-list-p dir-ent-list)
        (not (useless-dir-ent-p (dir-ent-fix dir-ent)))
        (fat32-filename-p (dir-ent-filename dir-ent)))
   (useful-dir-ent-list-p (place-dir-ent dir-ent-list dir-ent)))
  :hints (("goal" :in-theory (enable useful-dir-ent-list-p
                                     fat32-filename-p))))

(defund clear-clusterchain
  (fat32-in-memory masked-current-cluster length)
  (declare
   (xargs :stobjs fat32-in-memory
          :guard (and (lofat-fs-p fat32-in-memory)
                      (fat32-masked-entry-p masked-current-cluster)
                      (natp length)
                      (>= masked-current-cluster
                          *ms-first-data-cluster*)
                      (< masked-current-cluster
                         (+ (count-of-clusters fat32-in-memory)
                            *ms-first-data-cluster*)))))
  (b*
      (((mv dir-clusterchain error-code)
        (get-clusterchain fat32-in-memory masked-current-cluster length))
       ((unless (equal error-code 0))
        (mv fat32-in-memory error-code))
       (fat32-in-memory
        (stobj-set-indices-in-fa-table
         fat32-in-memory dir-clusterchain
         (make-list (len dir-clusterchain)
                    :initial-element 0))))
    (mv fat32-in-memory 0)))

(defthm
  fat-length-of-clear-clusterchain
  (equal
   (fat-length
    (mv-nth 0
            (clear-clusterchain fat32-in-memory
                                masked-current-cluster length)))
   (fat-length fat32-in-memory))
  :hints (("goal" :in-theory (enable clear-clusterchain))))

(defthm
  count-of-clusters-of-clear-clusterchain
  (equal
   (count-of-clusters
    (mv-nth 0
            (clear-clusterchain fat32-in-memory
                                masked-current-cluster length)))
   (count-of-clusters fat32-in-memory))
  :hints (("goal" :in-theory (enable clear-clusterchain))))

(defthm
  lofat-fs-p-of-clear-clusterchain
  (implies
   (lofat-fs-p fat32-in-memory)
   (lofat-fs-p
    (mv-nth
     0
     (clear-clusterchain fat32-in-memory
                         masked-current-cluster length))))
  :hints (("goal" :in-theory (enable clear-clusterchain))))

(defthm
  cluster-size-of-clear-clusterchain
  (equal
   (cluster-size
    (mv-nth 0
            (clear-clusterchain fat32-in-memory
                                masked-current-cluster length)))
   (cluster-size fat32-in-memory))
  :hints (("goal" :in-theory (enable clear-clusterchain))))

(defthm
  max-entry-count-of-clear-clusterchain
  (equal (max-entry-count
          (mv-nth 0
                  (clear-clusterchain fat32-in-memory
                                      masked-current-cluster length)))
         (max-entry-count fat32-in-memory))
  :hints (("goal" :in-theory (enable clear-clusterchain))))

(defthm
  pseudo-root-dir-ent-of-clear-clusterchain
  (equal
   (pseudo-root-dir-ent
    (mv-nth 0
            (clear-clusterchain fat32-in-memory
                                masked-current-cluster length)))
   (pseudo-root-dir-ent fat32-in-memory))
  :hints (("goal" :in-theory (enable clear-clusterchain))))

;; This has to be disabled because it's causing fat32-build-index-list to
;; appear where it isn't wanted.
(defthmd
  clear-clusterchain-correctness-1
  (implies
   (<= 2 masked-current-cluster)
   (equal
    (mv-nth 1
            (clear-clusterchain fat32-in-memory
                                masked-current-cluster length))
    (mv-nth 1
            (get-clusterchain-contents
             fat32-in-memory
             masked-current-cluster length))))
  :hints (("goal" :in-theory (enable clear-clusterchain))))

(defthm
  clear-clusterchain-correctness-2
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (non-free-index-listp x (effective-fat fat32-in-memory))
    (not
     (intersectp-equal
      x
      (mv-nth 0
              (fat32-build-index-list (effective-fat fat32-in-memory)
                                      masked-current-cluster length
                                      (cluster-size fat32-in-memory))))))
   (non-free-index-listp
    x
    (effective-fat
     (mv-nth 0
             (clear-clusterchain fat32-in-memory
                                 masked-current-cluster length)))))
  :hints (("goal" :in-theory (enable clear-clusterchain))))

(defthmd clear-clusterchain-correctness-3
  (implies
   (not (equal (mv-nth
                1
                (clear-clusterchain
                 fat32-in-memory masked-current-cluster length))
               0))
   (equal (mv-nth
           0
           (clear-clusterchain
            fat32-in-memory masked-current-cluster length))
          fat32-in-memory))
  :hints (("goal" :in-theory (enable clear-clusterchain))))

(defthm
  clear-clusterchain-reversibility-lemma-1
  (implies
   (equal (mv-nth 1
                  (fat32-build-index-list fa-table masked-current-cluster
                                          length cluster-size))
          0)
   (consp (mv-nth 0
                  (fat32-build-index-list fa-table masked-current-cluster
                                          length cluster-size))))
  :hints (("goal" :in-theory (enable fat32-build-index-list))))

;; Hypotheses are minimal.
(defthm
  clear-clusterchain-reversibility-lemma-2
  (implies
   (lofat-fs-p fat32-in-memory)
   (equal
    (stobj-set-indices-in-fa-table
     fat32-in-memory
     (mv-nth 0
             (fat32-build-index-list (effective-fat fat32-in-memory)
                                     masked-current-cluster
                                     length (cluster-size fat32-in-memory)))
     (append
      (cdr
       (mv-nth
        0
        (fat32-build-index-list (effective-fat fat32-in-memory)
                                masked-current-cluster
                                length (cluster-size fat32-in-memory))))
      (list
       (fat32-entry-mask
        (fati
         (car
          (last
           (mv-nth 0
                   (fat32-build-index-list (effective-fat fat32-in-memory)
                                           masked-current-cluster length
                                           (cluster-size fat32-in-memory)))))
         fat32-in-memory)))))
    fat32-in-memory))
  :hints
  (("goal"
    :in-theory
    (e/d
     (stobj-set-indices-in-fa-table fat32-build-index-list
                                    fat32-update-lower-28-of-fat32-entry-mask)
     ((:rewrite get-clusterchain-contents-correctness-2)))
    :induct (fat32-build-index-list (effective-fat fat32-in-memory)
                                    masked-current-cluster
                                    length (cluster-size fat32-in-memory))
    :expand
    (fat32-build-index-list
     (effective-fat fat32-in-memory)
     (fat32-entry-mask (fati masked-current-cluster fat32-in-memory))
     (+ length
        (- (cluster-size fat32-in-memory)))
     (cluster-size fat32-in-memory)))))

(defthm
  clear-clusterchain-reversibility
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (fat32-masked-entry-p masked-current-cluster)
        (>= masked-current-cluster
            *ms-first-data-cluster*)
        (< masked-current-cluster
           (+ (count-of-clusters fat32-in-memory)
              *ms-first-data-cluster*)))
   (equal
    (stobj-set-indices-in-fa-table
     (mv-nth 0
             (clear-clusterchain fat32-in-memory
                                 masked-current-cluster length))
     (mv-nth 0
             (fat32-build-index-list (effective-fat fat32-in-memory)
                                     masked-current-cluster
                                     length (cluster-size fat32-in-memory)))
     (append
      (cdr
       (mv-nth
        0
        (fat32-build-index-list (effective-fat fat32-in-memory)
                                masked-current-cluster
                                length (cluster-size fat32-in-memory))))
      (list
       (fat32-entry-mask
        (fati
         (car
          (last
           (mv-nth 0
                   (fat32-build-index-list (effective-fat fat32-in-memory)
                                           masked-current-cluster length
                                           (cluster-size fat32-in-memory)))))
         fat32-in-memory)))))
    fat32-in-memory))
  :hints (("goal" :in-theory (e/d (clear-clusterchain)
                                  (clear-clusterchain-reversibility-lemma-2))
           :use clear-clusterchain-reversibility-lemma-2
           :do-not-induct t)))

(encapsulate
  ()

  (local
   (defthm
     fat32-build-index-list-of-effective-fat-of-clear-clusterchain-lemma-1
     (implies
      (and
       (<= (+ 2 (count-of-clusters fat32-in-memory))
           first-cluster)
       (lofat-fs-p fat32-in-memory)
       (fat32-masked-entry-p first-cluster)
       (fat32-masked-entry-p masked-current-cluster)
       (not
        (intersectp-equal
         (mv-nth 0
                 (fat32-build-index-list
                  (effective-fat fat32-in-memory)
                  masked-current-cluster
                  length1 (cluster-size fat32-in-memory)))
         (mv-nth 0
                 (fat32-build-index-list
                  (effective-fat fat32-in-memory)
                  first-cluster length2 (cluster-size fat32-in-memory))))))
      (equal
       (fat32-build-index-list
        (effective-fat
         (mv-nth 0
                 (clear-clusterchain
                  fat32-in-memory first-cluster length2)))
        masked-current-cluster
        length1 (cluster-size fat32-in-memory))
       (fat32-build-index-list
        (effective-fat fat32-in-memory)
        masked-current-cluster
        length1 (cluster-size fat32-in-memory))))
     :hints
     (("goal"
       :in-theory (e/d (intersectp-equal clear-clusterchain)
                       (intersectp-is-commutative))
       :expand
       ((fat32-build-index-list (effective-fat fat32-in-memory)
                                first-cluster length2
                                (cluster-size fat32-in-memory))
        (get-clusterchain-contents
         fat32-in-memory first-cluster length2))
       :use
       (:instance
        (:rewrite intersectp-is-commutative)
        (y
         (mv-nth
          0
          (fat32-build-index-list (effective-fat fat32-in-memory)
                                  first-cluster length2
                                  (cluster-size fat32-in-memory))))
        (x (mv-nth 0
                   (fat32-build-index-list
                    (effective-fat fat32-in-memory)
                    masked-current-cluster length1
                    (cluster-size fat32-in-memory)))))))))

  (defthm
    fat32-build-index-list-of-effective-fat-of-clear-clusterchain
    (implies
     (and
      (lofat-fs-p fat32-in-memory)
      (fat32-masked-entry-p masked-current-cluster1)
      (fat32-masked-entry-p masked-current-cluster2)
      (<= *ms-first-data-cluster*
          masked-current-cluster1)
      (not
       (intersectp-equal
        (mv-nth '0
                (fat32-build-index-list (effective-fat fat32-in-memory)
                                        masked-current-cluster1
                                        length1 (cluster-size fat32-in-memory)))
        (mv-nth '0
                (fat32-build-index-list (effective-fat fat32-in-memory)
                                        masked-current-cluster2 length2
                                        (cluster-size fat32-in-memory)))))
      (equal cluster-size (cluster-size fat32-in-memory)))
     (equal
      (fat32-build-index-list
       (effective-fat
        (mv-nth 0
                (clear-clusterchain fat32-in-memory
                                    masked-current-cluster1 length1)))
       masked-current-cluster2
       length2 cluster-size)
      (fat32-build-index-list (effective-fat fat32-in-memory)
                              masked-current-cluster2 length2
                              cluster-size)))
    :hints (("goal" :cases ((<= (+ 2 (count-of-clusters fat32-in-memory))
                                masked-current-cluster1)))
            ("subgoal 2" :in-theory (enable clear-clusterchain)))))

(defthm
  dir-ent-clusterchain-of-clear-clusterchain
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (fat32-masked-entry-p masked-current-cluster)
    (dir-ent-p dir-ent)
    (<= *ms-first-data-cluster*
        masked-current-cluster)
    (not
     (intersectp-equal
      (mv-nth '0
              (fat32-build-index-list (effective-fat fat32-in-memory)
                                      masked-current-cluster
                                      length (cluster-size fat32-in-memory)))
      (mv-nth '0
              (dir-ent-clusterchain fat32-in-memory dir-ent)))))
   (equal (dir-ent-clusterchain
           (mv-nth 0
                   (clear-clusterchain fat32-in-memory
                                       masked-current-cluster length))
           dir-ent)
          (dir-ent-clusterchain fat32-in-memory dir-ent)))
  :hints (("goal" :in-theory (enable dir-ent-clusterchain))))

(defthm
  effective-fat-of-clear-clusterchain
  (implies
   (lofat-fs-p fat32-in-memory)
   (equal
    (effective-fat
     (mv-nth 0
             (clear-clusterchain fat32-in-memory
                                 masked-current-cluster length)))
    (if
     (equal (mv-nth 1
                    (clear-clusterchain fat32-in-memory
                                        masked-current-cluster length))
            0)
     (set-indices-in-fa-table
      (effective-fat fat32-in-memory)
      (mv-nth 0
              (fat32-build-index-list (effective-fat fat32-in-memory)
                                      masked-current-cluster
                                      length (cluster-size fat32-in-memory)))
      (make-list-ac
       (len
        (mv-nth
         0
         (fat32-build-index-list (effective-fat fat32-in-memory)
                                 masked-current-cluster
                                 length (cluster-size fat32-in-memory))))
       0 nil))
     (effective-fat fat32-in-memory))))
  :hints (("goal" :in-theory (enable clear-clusterchain)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (not (dir-ent-directory-p dir-ent))
          (equal masked-current-cluster
                 (dir-ent-first-cluster dir-ent))
          (equal length (dir-ent-file-size dir-ent)))
     (equal
      (effective-fat
       (mv-nth 0
               (clear-clusterchain fat32-in-memory
                                   masked-current-cluster length)))
      (if
       (equal (mv-nth 1
                      (dir-ent-clusterchain fat32-in-memory dir-ent))
              0)
       (set-indices-in-fa-table
        (effective-fat fat32-in-memory)
        (mv-nth 0
                (dir-ent-clusterchain fat32-in-memory dir-ent))
        (make-list-ac
         (len (mv-nth 0
                      (dir-ent-clusterchain fat32-in-memory dir-ent)))
         0 nil))
       (effective-fat fat32-in-memory))))
    :hints (("goal" :in-theory (enable dir-ent-clusterchain
                                       clear-clusterchain))))
   (:rewrite
    :corollary
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (dir-ent-directory-p dir-ent)
          (equal masked-current-cluster
                 (dir-ent-first-cluster dir-ent))
          (equal length *ms-max-dir-size*))
     (equal
      (effective-fat
       (mv-nth 0
               (clear-clusterchain fat32-in-memory
                                   masked-current-cluster length)))
      (if
       (equal (mv-nth 1
                      (dir-ent-clusterchain fat32-in-memory dir-ent))
              0)
       (set-indices-in-fa-table
        (effective-fat fat32-in-memory)
        (mv-nth 0
                (dir-ent-clusterchain fat32-in-memory dir-ent))
        (make-list-ac
         (len (mv-nth 0
                      (dir-ent-clusterchain fat32-in-memory dir-ent)))
         0 nil))
       (effective-fat fat32-in-memory))))
    :hints (("goal" :in-theory (enable dir-ent-clusterchain
                                       clear-clusterchain))))))

;; This is needed, to avoid introducing unwanted fat32-build-index-list terms
;; into proofs.
(in-theory (disable (:rewrite effective-fat-of-clear-clusterchain . 1)))

(encapsulate
  ()

  (local
   (defthm
     get-clusterchain-contents-of-clear-clusterchain-lemma-1
     (implies
      (and
       (<= (+ 2 (count-of-clusters fat32-in-memory))
           first-cluster)
       (lofat-fs-p fat32-in-memory)
       (fat32-masked-entry-p first-cluster)
       (fat32-masked-entry-p masked-current-cluster)
       (not
        (intersectp-equal
         (mv-nth 0
                 (fat32-build-index-list
                  (effective-fat fat32-in-memory)
                  masked-current-cluster
                  length1 (cluster-size fat32-in-memory)))
         (mv-nth 0
                 (fat32-build-index-list
                  (effective-fat fat32-in-memory)
                  first-cluster length2 (cluster-size fat32-in-memory))))))
      (equal
       (get-clusterchain-contents
        (mv-nth 0
                (clear-clusterchain
                 fat32-in-memory first-cluster length2))
        masked-current-cluster length1)
       (get-clusterchain-contents
        fat32-in-memory masked-current-cluster length1)))
     :hints
     (("goal"
       :in-theory (e/d (intersectp-equal clear-clusterchain)
                       (intersectp-is-commutative))
       :expand
       ((fat32-build-index-list (effective-fat fat32-in-memory)
                                first-cluster length2
                                (cluster-size fat32-in-memory))
        (get-clusterchain-contents
         fat32-in-memory first-cluster length2))
       :use
       (:instance
        (:rewrite intersectp-is-commutative)
        (y
         (mv-nth
          0
          (fat32-build-index-list (effective-fat fat32-in-memory)
                                  first-cluster length2
                                  (cluster-size fat32-in-memory))))
        (x (mv-nth 0
                   (fat32-build-index-list
                    (effective-fat fat32-in-memory)
                    masked-current-cluster length1
                    (cluster-size fat32-in-memory)))))))))

  (defthm
    get-clusterchain-contents-of-clear-clusterchain
    (implies
     (and
      (lofat-fs-p fat32-in-memory)
      (fat32-masked-entry-p masked-current-cluster1)
      (fat32-masked-entry-p masked-current-cluster2)
      (<= *ms-first-data-cluster*
          masked-current-cluster1)
      (not
       (intersectp-equal
        (mv-nth '0
                (fat32-build-index-list (effective-fat fat32-in-memory)
                                        masked-current-cluster1
                                        length1 (cluster-size fat32-in-memory)))
        (mv-nth '0
                (fat32-build-index-list (effective-fat fat32-in-memory)
                                        masked-current-cluster2 length2
                                        (cluster-size fat32-in-memory))))))
     (equal
      (get-clusterchain-contents
       (mv-nth 0
               (clear-clusterchain fat32-in-memory
                                   masked-current-cluster1 length1))
       masked-current-cluster2 length2)
      (get-clusterchain-contents fat32-in-memory
                                 masked-current-cluster2 length2)))
    :hints (("goal" :cases ((<= (+ 2 (count-of-clusters fat32-in-memory))
                                masked-current-cluster1)))
            ("subgoal 2" :in-theory (enable clear-clusterchain)))))

(defthm
  dir-ent-clusterchain-contents-of-clear-clusterchain
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (fat32-masked-entry-p masked-current-cluster)
    (dir-ent-p dir-ent)
    (<= *ms-first-data-cluster*
        masked-current-cluster)
    (not
     (intersectp-equal
      (mv-nth '0
              (fat32-build-index-list (effective-fat fat32-in-memory)
                                      masked-current-cluster
                                      length (cluster-size fat32-in-memory)))
      (mv-nth '0
              (dir-ent-clusterchain fat32-in-memory dir-ent)))))
   (equal (dir-ent-clusterchain-contents
           (mv-nth 0
                   (clear-clusterchain fat32-in-memory
                                       masked-current-cluster length))
           dir-ent)
          (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
  :hints (("goal" :in-theory (enable dir-ent-clusterchain
                                     dir-ent-clusterchain-contents))))

;; Free variables, are they necessary?
(defthm
  fati-of-clear-clusterchain
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (natp i)
        (fat32-masked-entry-p masked-current-cluster)
        (<= *ms-first-data-cluster*
            masked-current-cluster)
        (< masked-current-cluster
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory)))
        (< i
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory))))
   (equal
    (fati
     i
     (mv-nth
      0
      (clear-clusterchain fat32-in-memory
                          masked-current-cluster length)))
    (if
     (and
      (equal
       (mv-nth 1
               (fat32-build-index-list
                (effective-fat fat32-in-memory)
                masked-current-cluster
                length (cluster-size fat32-in-memory)))
       0)
      (member-equal
       i
       (mv-nth 0
               (fat32-build-index-list
                (effective-fat fat32-in-memory)
                masked-current-cluster length
                (cluster-size fat32-in-memory)))))
     (fat32-update-lower-28 (fati i fat32-in-memory)
                            0)
     (fati i fat32-in-memory))))
  :hints
  (("goal"
    :in-theory (e/d (clear-clusterchain)
                    ((:rewrite nth-of-effective-fat)))
    :use
    ((:instance
      (:rewrite nth-of-effective-fat)
      (fat32-in-memory
       (stobj-set-indices-in-fa-table
        fat32-in-memory
        (mv-nth 0
                (fat32-build-index-list
                 (effective-fat fat32-in-memory)
                 masked-current-cluster
                 length (cluster-size fat32-in-memory)))
        (make-list-ac
         (len
          (mv-nth 0
                  (fat32-build-index-list
                   (effective-fat fat32-in-memory)
                   masked-current-cluster
                   length (cluster-size fat32-in-memory))))
         0 nil)))
      (n i))
     (:instance (:rewrite nth-of-effective-fat)
                (fat32-in-memory fat32-in-memory)
                (n i)))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (natp i)
          (fat32-masked-entry-p masked-current-cluster)
          (<= *ms-first-data-cluster*
              masked-current-cluster)
          (< masked-current-cluster
             (+ *ms-first-data-cluster*
                (count-of-clusters fat32-in-memory)))
          (< i
             (+ *ms-first-data-cluster*
                (count-of-clusters fat32-in-memory)))
          (not (dir-ent-directory-p dir-ent))
          (equal masked-current-cluster
                 (dir-ent-first-cluster dir-ent))
          (equal length (dir-ent-file-size dir-ent)))
     (equal
      (fati
       i
       (mv-nth
        0
        (clear-clusterchain fat32-in-memory
                            masked-current-cluster length)))
      (if
       (and
        (equal
         (mv-nth 1
                 (dir-ent-clusterchain fat32-in-memory dir-ent))
         0)
        (member-equal
         i
         (mv-nth
          0
          (dir-ent-clusterchain fat32-in-memory dir-ent))))
       (fat32-update-lower-28 (fati i fat32-in-memory)
                              0)
       (fati i fat32-in-memory))))
    :hints (("goal" :in-theory (enable dir-ent-clusterchain))))
   (:rewrite
    :corollary
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (natp i)
          (fat32-masked-entry-p masked-current-cluster)
          (<= *ms-first-data-cluster*
              masked-current-cluster)
          (< masked-current-cluster
             (+ *ms-first-data-cluster*
                (count-of-clusters fat32-in-memory)))
          (< i
             (+ *ms-first-data-cluster*
                (count-of-clusters fat32-in-memory)))
          (dir-ent-directory-p dir-ent)
          (equal masked-current-cluster
                 (dir-ent-first-cluster dir-ent))
          (equal length *ms-max-dir-size*))
     (equal
      (fati
       i
       (mv-nth
        0
        (clear-clusterchain fat32-in-memory
                            masked-current-cluster length)))
      (if
       (and
        (equal
         (mv-nth 1
                 (dir-ent-clusterchain fat32-in-memory dir-ent))
         0)
        (member-equal
         i
         (mv-nth
          0
          (dir-ent-clusterchain fat32-in-memory dir-ent))))
       (fat32-update-lower-28 (fati i fat32-in-memory)
                              0)
       (fati i fat32-in-memory))))
    :hints
    (("goal" :in-theory (enable dir-ent-clusterchain))))))

(in-theory (disable (:REWRITE FATI-OF-CLEAR-CLUSTERCHAIN . 1)))

;; This function calls place-contents with a meaningless value of dir-ent,
;; because we know that for a well-formed directory, the contents will be
;; non-empty and so there's no way we're going to be returned a dir-ent with
;; the first cluster set to 0 (with the mask, of course...) so we don't care
;; about the value of dir-ent returned.
(defund
  update-dir-contents
  (fat32-in-memory first-cluster dir-contents)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (and (lofat-fs-p fat32-in-memory)
                (fat32-masked-entry-p first-cluster)
                (<= *ms-first-data-cluster* first-cluster)
                (> (+ *ms-first-data-cluster*
                      (count-of-clusters fat32-in-memory))
                   first-cluster)
                (stringp dir-contents))
    :guard-debug t
    :guard-hints
    (("goal"
      :expand (fat32-build-index-list
               (effective-fat fat32-in-memory)
               first-cluster
               2097152 (cluster-size fat32-in-memory))
      :in-theory
      (disable unsigned-byte-p
       bounded-nat-listp-correctness-1
       (:linear non-negativity-of-car-of-last-when-nat-listp))
      :use
      ((:instance
        nat-listp-forward-to-integer-listp
        (x (mv-nth 0
                   (fat32-build-index-list
                    (effective-fat fat32-in-memory)
                    first-cluster *ms-max-dir-size*
                    (cluster-size fat32-in-memory)))))
       (:instance
        (:linear non-negativity-of-car-of-last-when-nat-listp)
        (l (mv-nth 0
                   (fat32-build-index-list
                    (effective-fat fat32-in-memory)
                    first-cluster *ms-max-dir-size*
                    (cluster-size fat32-in-memory))))))))))
  (b* (((mv clusterchain &)
        (get-clusterchain fat32-in-memory
                          first-cluster *ms-max-dir-size*))
       (last-value
        (fat32-entry-mask (fati (car (last clusterchain))
                                fat32-in-memory)))
       ((mv fat32-in-memory error-code)
        (clear-clusterchain fat32-in-memory
                            first-cluster *ms-max-dir-size*))
       ((unless (equal error-code 0))
        (mv fat32-in-memory *eio*))
       (fat32-in-memory
        (update-fati first-cluster
                     (fat32-update-lower-28
                      (fati first-cluster fat32-in-memory)
                      *ms-end-of-clusterchain*)
                     fat32-in-memory))
       ((unless (> (length dir-contents) 0))
        (mv fat32-in-memory 0))
       ((mv fat32-in-memory & error-code &)
        (place-contents fat32-in-memory (dir-ent-fix nil)
                        dir-contents 0 first-cluster))
       ((when (equal error-code 0))
        (mv fat32-in-memory 0))
       ;; Reversing the effects of clear-clusterchain
       (fat32-in-memory (stobj-set-indices-in-fa-table
                         fat32-in-memory clusterchain
                         (append (cdr clusterchain)
                                 (list last-value)))))
    (mv fat32-in-memory error-code)))

(defthm
  count-of-clusters-of-update-dir-contents
  (equal
   (count-of-clusters
    (mv-nth
     0
     (update-dir-contents fat32-in-memory
                          first-cluster dir-contents)))
   (count-of-clusters fat32-in-memory))
  :hints (("goal" :in-theory (enable update-dir-contents))))

(defthm
  cluster-size-of-update-dir-contents
  (equal
   (cluster-size
    (mv-nth
     0
     (update-dir-contents fat32-in-memory
                          first-cluster dir-contents)))
   (cluster-size fat32-in-memory))
  :hints (("goal" :in-theory (enable update-dir-contents))))

(defthm
  lofat-fs-p-of-update-dir-contents
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (fat32-masked-entry-p first-cluster)
        (<= *ms-first-data-cluster* first-cluster)
        (> (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory))
           first-cluster)
        (stringp dir-contents))
   (lofat-fs-p
    (mv-nth 0
            (update-dir-contents fat32-in-memory
                                 first-cluster dir-contents))))
  :hints (("goal" :in-theory (enable update-dir-contents
                                     clear-clusterchain-correctness-1))))

(defthm
  fat32-build-index-list-of-effective-fat-of-update-dir-contents
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (fat32-masked-entry-p first-cluster)
    (<= *ms-first-data-cluster* first-cluster)
    (stringp dir-contents)
    (fat32-masked-entry-p masked-current-cluster)
    (<= *ms-first-data-cluster*
        masked-current-cluster)
    (not
     (intersectp-equal
      (mv-nth 0
              (fat32-build-index-list (effective-fat fat32-in-memory)
                                      masked-current-cluster
                                      length (cluster-size fat32-in-memory)))
      (mv-nth 0
              (fat32-build-index-list (effective-fat fat32-in-memory)
                                      first-cluster *ms-max-dir-size*
                                      (cluster-size fat32-in-memory)))))
    (equal
     (mv-nth 1
             (fat32-build-index-list (effective-fat fat32-in-memory)
                                     masked-current-cluster
                                     length (cluster-size fat32-in-memory)))
     0)
    (equal cluster-size (cluster-size fat32-in-memory)))
   (equal
    (fat32-build-index-list
     (effective-fat
      (mv-nth 0
              (update-dir-contents fat32-in-memory
                                   first-cluster dir-contents)))
     masked-current-cluster
     length cluster-size)
    (fat32-build-index-list (effective-fat fat32-in-memory)
                            masked-current-cluster
                            length cluster-size)))
  :hints
  (("goal"
    :in-theory (e/d (update-dir-contents intersectp-equal clear-clusterchain)
                    (intersectp-is-commutative))
    :expand
    ((fat32-build-index-list (effective-fat fat32-in-memory)
                             first-cluster *ms-max-dir-size*
                             (cluster-size fat32-in-memory))
     (get-clusterchain-contents fat32-in-memory first-cluster 2097152))
    :use
    (:instance
     (:rewrite intersectp-is-commutative)
     (y (mv-nth 0
                (fat32-build-index-list (effective-fat fat32-in-memory)
                                        first-cluster 2097152
                                        (cluster-size fat32-in-memory))))
     (x (mv-nth 0
                (fat32-build-index-list (effective-fat fat32-in-memory)
                                        masked-current-cluster length
                                        (cluster-size fat32-in-memory))))))))

(defthm
  dir-ent-clusterchain-of-update-dir-contents
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (fat32-masked-entry-p first-cluster)
    (<= *ms-first-data-cluster* first-cluster)
    (stringp dir-contents)
    (dir-ent-p dir-ent)
    (<= *ms-first-data-cluster*
        (dir-ent-first-cluster dir-ent))
    (not
     (intersectp-equal
      (mv-nth 0
              (dir-ent-clusterchain fat32-in-memory dir-ent))
      (mv-nth 0
              (fat32-build-index-list (effective-fat fat32-in-memory)
                                      first-cluster *ms-max-dir-size*
                                      (cluster-size fat32-in-memory)))))
    (equal (mv-nth 1
                   (dir-ent-clusterchain fat32-in-memory dir-ent))
           0))
   (equal (dir-ent-clusterchain
           (mv-nth 0
                   (update-dir-contents fat32-in-memory
                                        first-cluster dir-contents))
           dir-ent)
          (dir-ent-clusterchain fat32-in-memory dir-ent)))
  :hints (("goal" :in-theory (enable dir-ent-clusterchain))))

(defthm
  max-entry-count-of-update-dir-contents
  (equal
   (max-entry-count (mv-nth 0
                            (update-dir-contents fat32-in-memory
                                                 first-cluster dir-contents)))
   (max-entry-count fat32-in-memory))
  :hints (("goal" :in-theory (enable update-dir-contents))))

(defthm
  pseudo-root-dir-ent-of-update-dir-contents
  (equal
   (pseudo-root-dir-ent
    (mv-nth 0
            (update-dir-contents fat32-in-memory
                                 first-cluster dir-contents)))
   (pseudo-root-dir-ent fat32-in-memory))
  :hints (("goal" :in-theory (enable update-dir-contents))))

(defthm
  update-dir-contents-correctness-1-lemma-1
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (fat32-masked-entry-p first-cluster)
    (<
     (+
      -1
      (count-free-clusters
       (set-indices-in-fa-table
        (effective-fat fat32-in-memory)
        (mv-nth
         0
         (fat32-build-index-list (effective-fat fat32-in-memory)
                                 first-cluster
                                 2097152 (cluster-size fat32-in-memory)))
        '(0))))
     (+ -1
        (len (make-clusters dir-contents
                            (cluster-size fat32-in-memory)))))
    (not
     (equal
      (count-free-clusters
       (set-indices-in-fa-table
        (effective-fat fat32-in-memory)
        (mv-nth
         0
         (fat32-build-index-list (effective-fat fat32-in-memory)
                                 first-cluster
                                 2097152 (cluster-size fat32-in-memory)))
        '(0)))
      (len (make-clusters dir-contents
                          (cluster-size fat32-in-memory)))))
    (equal
     (mv-nth 1
             (fat32-build-index-list (effective-fat fat32-in-memory)
                                     first-cluster
                                     2097152 (cluster-size fat32-in-memory)))
     0)
    (not
     (consp
      (cdr
       (mv-nth 0
               (fat32-build-index-list (effective-fat fat32-in-memory)
                                       first-cluster 2097152
                                       (cluster-size fat32-in-memory)))))))
   (equal
    (stobj-set-indices-in-fa-table
     (update-fati
      first-cluster
      (fat32-update-lower-28 (fati first-cluster fat32-in-memory)
                             268435455)
      (mv-nth 0
              (clear-clusterchain fat32-in-memory first-cluster 2097152)))
     (mv-nth 0
             (fat32-build-index-list (effective-fat fat32-in-memory)
                                     first-cluster
                                     2097152 (cluster-size fat32-in-memory)))
     (list
      (fat32-entry-mask
       (fati
        (car (mv-nth 0
                     (fat32-build-index-list (effective-fat fat32-in-memory)
                                             first-cluster 2097152
                                             (cluster-size fat32-in-memory))))
        fat32-in-memory))))
    fat32-in-memory))
  :hints
  (("goal" :in-theory
    (e/d (clear-clusterchain stobj-set-indices-in-fa-table
                             fat32-update-lower-28-of-fat32-entry-mask)
         (get-clusterchain-contents-correctness-2))
    :expand (fat32-build-index-list (effective-fat fat32-in-memory)
                                    first-cluster 2097152
                                    (cluster-size fat32-in-memory)))))

(defthm
  update-dir-contents-correctness-1-lemma-4
  (implies
   (and (fat32-masked-entry-p first-cluster)
        (< first-cluster
           (+ 2 (count-of-clusters fat32-in-memory))))
   (equal
    (fati
     first-cluster
     (stobj-set-indices-in-fa-table
      fat32-in-memory
      (mv-nth 0
              (fat32-build-index-list (effective-fat fat32-in-memory)
                                      first-cluster
                                      2097152 (cluster-size fat32-in-memory)))
      (make-list-ac
       (len (mv-nth 0
                    (fat32-build-index-list (effective-fat fat32-in-memory)
                                            first-cluster 2097152
                                            (cluster-size fat32-in-memory))))
       0 nil)))
    (nth
     first-cluster
     (effective-fat
      (stobj-set-indices-in-fa-table
       fat32-in-memory
       (mv-nth
        0
        (fat32-build-index-list (effective-fat fat32-in-memory)
                                first-cluster
                                2097152 (cluster-size fat32-in-memory)))
       (make-list-ac
        (len (mv-nth 0
                     (fat32-build-index-list (effective-fat fat32-in-memory)
                                             first-cluster 2097152
                                             (cluster-size fat32-in-memory))))
        0 nil))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite nth-of-effective-fat))
    :use
    (:instance
     (:rewrite nth-of-effective-fat)
     (fat32-in-memory
      (stobj-set-indices-in-fa-table
       fat32-in-memory
       (mv-nth
        0
        (fat32-build-index-list (effective-fat fat32-in-memory)
                                first-cluster
                                2097152 (cluster-size fat32-in-memory)))
       (make-list-ac
        (len (mv-nth 0
                     (fat32-build-index-list (effective-fat fat32-in-memory)
                                             first-cluster 2097152
                                             (cluster-size fat32-in-memory))))
        0 nil)))
     (n first-cluster)))))

(defthm
  update-dir-contents-correctness-1-lemma-2
  (implies
   (and
    (equal
     (stobj-set-indices-in-fa-table
      (update-fati
       first-cluster
       (fat32-update-lower-28
        (fati
         first-cluster
         (stobj-set-indices-in-fa-table
          fat32-in-memory
          (mv-nth
           0
           (fat32-build-index-list (effective-fat fat32-in-memory)
                                   first-cluster
                                   2097152 (cluster-size fat32-in-memory)))
          (make-list-ac
           (len
            (cdr
             (mv-nth
              0
              (fat32-build-index-list (effective-fat fat32-in-memory)
                                      first-cluster 2097152
                                      (cluster-size fat32-in-memory)))))
           0 '(0))))
        268435455)
       (stobj-set-indices-in-fa-table
        fat32-in-memory
        (mv-nth
         0
         (fat32-build-index-list (effective-fat fat32-in-memory)
                                 first-cluster
                                 2097152 (cluster-size fat32-in-memory)))
        (make-list-ac
         (len
          (cdr
           (mv-nth 0
                   (fat32-build-index-list (effective-fat fat32-in-memory)
                                           first-cluster 2097152
                                           (cluster-size fat32-in-memory)))))
         0 '(0))))
      (mv-nth 0
              (fat32-build-index-list (effective-fat fat32-in-memory)
                                      first-cluster
                                      2097152 (cluster-size fat32-in-memory)))
      (append
       (cdr (mv-nth 0
                    (fat32-build-index-list (effective-fat fat32-in-memory)
                                            first-cluster 2097152
                                            (cluster-size fat32-in-memory))))
       (list
        (fat32-entry-mask
         (fati
          (car
           (last
            (cdr
             (mv-nth
              0
              (fat32-build-index-list (effective-fat fat32-in-memory)
                                      first-cluster 2097152
                                      (cluster-size fat32-in-memory))))))
          fat32-in-memory)))))
     (stobj-set-indices-in-fa-table
      fat32-in-memory
      (mv-nth 0
              (fat32-build-index-list (effective-fat fat32-in-memory)
                                      first-cluster
                                      2097152 (cluster-size fat32-in-memory)))
      (append
       (cdr (mv-nth 0
                    (fat32-build-index-list (effective-fat fat32-in-memory)
                                            first-cluster 2097152
                                            (cluster-size fat32-in-memory))))
       (list
        (fat32-entry-mask
         (fati
          (car
           (last
            (cdr
             (mv-nth
              0
              (fat32-build-index-list (effective-fat fat32-in-memory)
                                      first-cluster 2097152
                                      (cluster-size fat32-in-memory))))))
          fat32-in-memory))))))
    (lofat-fs-p fat32-in-memory)
    (fat32-masked-entry-p first-cluster)
    (< first-cluster
       (+ 2 (count-of-clusters fat32-in-memory)))
    (consp
     (cdr (mv-nth 0
                  (fat32-build-index-list (effective-fat fat32-in-memory)
                                          first-cluster 2097152
                                          (cluster-size fat32-in-memory))))))
   (equal
    (stobj-set-indices-in-fa-table
     (update-fati
      first-cluster
      (fat32-update-lower-28 (fati first-cluster fat32-in-memory)
                             268435455)
      (stobj-set-indices-in-fa-table
       fat32-in-memory
       (mv-nth
        0
        (fat32-build-index-list (effective-fat fat32-in-memory)
                                first-cluster
                                2097152 (cluster-size fat32-in-memory)))
       (make-list-ac
        (len
         (cdr
          (mv-nth 0
                  (fat32-build-index-list (effective-fat fat32-in-memory)
                                          first-cluster 2097152
                                          (cluster-size fat32-in-memory)))))
        0 '(0))))
     (mv-nth 0
             (fat32-build-index-list (effective-fat fat32-in-memory)
                                     first-cluster
                                     2097152 (cluster-size fat32-in-memory)))
     (append
      (cdr (mv-nth 0
                   (fat32-build-index-list (effective-fat fat32-in-memory)
                                           first-cluster 2097152
                                           (cluster-size fat32-in-memory))))
      (list
       (fat32-entry-mask
        (fati
         (car
          (last
           (cdr
            (mv-nth
             0
             (fat32-build-index-list (effective-fat fat32-in-memory)
                                     first-cluster 2097152
                                     (cluster-size fat32-in-memory))))))
         fat32-in-memory)))))
    fat32-in-memory))
  :hints
  (("goal"
    :in-theory
    (disable (:rewrite fat32-update-lower-28-of-fat32-update-lower-28)
             (:rewrite clear-clusterchain-reversibility-lemma-2)
             nth-of-set-indices-in-fa-table-when-member
             (:rewrite stobj-set-indices-in-fa-table-correctness-1))
    :use
    ((:instance
      (:rewrite nth-of-set-indices-in-fa-table-when-member)
      (val 0)
      (index-list
       (mv-nth 0
               (fat32-build-index-list (effective-fat fat32-in-memory)
                                       first-cluster 2097152
                                       (cluster-size fat32-in-memory))))
      (fa-table (effective-fat fat32-in-memory))
      (n first-cluster))
     (:instance (:rewrite fat32-update-lower-28-of-fat32-update-lower-28)
                (masked-entry2 268435455)
                (masked-entry1 0)
                (entry (nth first-cluster
                            (effective-fat fat32-in-memory))))
     (:instance (:rewrite clear-clusterchain-reversibility-lemma-2)
                (length 2097152)
                (masked-current-cluster first-cluster)
                (fat32-in-memory fat32-in-memory))
     (:instance
      (:rewrite stobj-set-indices-in-fa-table-correctness-1)
      (value-list
       (make-list-ac
        (len (mv-nth 0
                     (fat32-build-index-list (effective-fat fat32-in-memory)
                                             first-cluster 2097152
                                             (cluster-size fat32-in-memory))))
        0 nil))
      (index-list
       (mv-nth 0
               (fat32-build-index-list (effective-fat fat32-in-memory)
                                       first-cluster 2097152
                                       (cluster-size fat32-in-memory))))
      (fat32-in-memory fat32-in-memory))))))

(defthm
  update-dir-contents-correctness-1-lemma-3
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (fat32-masked-entry-p first-cluster)
    (<= 2 first-cluster)
    (< first-cluster
       (+ 2 (count-of-clusters fat32-in-memory)))
    (equal
     (mv-nth 1
             (fat32-build-index-list (effective-fat fat32-in-memory)
                                     first-cluster
                                     2097152 (cluster-size fat32-in-memory)))
     0)
    (consp
     (cdr (mv-nth 0
                  (fat32-build-index-list (effective-fat fat32-in-memory)
                                          first-cluster 2097152
                                          (cluster-size fat32-in-memory))))))
   (equal
    (stobj-set-indices-in-fa-table
     (update-fati
      first-cluster
      (fat32-update-lower-28 (fati first-cluster fat32-in-memory)
                             268435455)
      (mv-nth 0
              (clear-clusterchain fat32-in-memory first-cluster 2097152)))
     (mv-nth 0
             (fat32-build-index-list (effective-fat fat32-in-memory)
                                     first-cluster
                                     2097152 (cluster-size fat32-in-memory)))
     (append
      (cdr (mv-nth 0
                   (fat32-build-index-list (effective-fat fat32-in-memory)
                                           first-cluster 2097152
                                           (cluster-size fat32-in-memory))))
      (list
       (fat32-entry-mask
        (fati
         (car
          (last
           (cdr
            (mv-nth
             0
             (fat32-build-index-list (effective-fat fat32-in-memory)
                                     first-cluster 2097152
                                     (cluster-size fat32-in-memory))))))
         fat32-in-memory)))))
    fat32-in-memory))
  :hints
  (("goal"
    :in-theory
    (e/d
     (clear-clusterchain)
     (get-clusterchain-contents-correctness-2
      (:rewrite
       stobj-set-indices-in-fa-table-of-stobj-set-indices-in-fa-table-lemma-3)))
    :use
    (:instance
     (:rewrite
      stobj-set-indices-in-fa-table-of-stobj-set-indices-in-fa-table-lemma-3)
     (value-list
      (append
       (cdr (mv-nth 0
                    (fat32-build-index-list (effective-fat fat32-in-memory)
                                            first-cluster 2097152
                                            (cluster-size fat32-in-memory))))
       (list
        (fat32-entry-mask
         (fati
          (car
           (last
            (cdr
             (mv-nth
              0
              (fat32-build-index-list (effective-fat fat32-in-memory)
                                      first-cluster 2097152
                                      (cluster-size fat32-in-memory))))))
          fat32-in-memory)))))
     (index-list
      (mv-nth 0
              (fat32-build-index-list (effective-fat fat32-in-memory)
                                      first-cluster 2097152
                                      (cluster-size fat32-in-memory))))
     (v 268435455)
     (fat32-in-memory
      (stobj-set-indices-in-fa-table
       fat32-in-memory
       (mv-nth
        0
        (fat32-build-index-list (effective-fat fat32-in-memory)
                                first-cluster
                                2097152 (cluster-size fat32-in-memory)))
       (make-list-ac
        (len
         (cdr
          (mv-nth 0
                  (fat32-build-index-list (effective-fat fat32-in-memory)
                                          first-cluster 2097152
                                          (cluster-size fat32-in-memory)))))
        0 '(0))))
     (i first-cluster)))))

(defthmd
  update-dir-contents-correctness-1
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (fat32-masked-entry-p first-cluster)
        (<= *ms-first-data-cluster* first-cluster)
        (> (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory))
           first-cluster)
        (not (equal (mv-nth 1
                            (update-dir-contents fat32-in-memory
                                                 first-cluster dir-contents))
                    0)))
   (equal (mv-nth 0
                  (update-dir-contents fat32-in-memory
                                       first-cluster dir-contents))
          fat32-in-memory))
  :hints
  (("goal"
    :in-theory (enable update-dir-contents clear-clusterchain-correctness-3
                       place-contents-correctness-1
                       clear-clusterchain-correctness-1
                       (:rewrite effective-fat-of-clear-clusterchain . 1)
                       (:rewrite fati-of-clear-clusterchain . 1)))))

(defthm natp-of-update-dir-contents
  (natp (mv-nth 1
                (update-dir-contents fat32-in-memory
                                     first-cluster dir-contents)))
  :rule-classes :type-prescription
  :hints (("goal" :in-theory (enable update-dir-contents))))

(defun
    delete-dir-ent (dir-ent-list filename)
  (declare (xargs :guard (and (fat32-filename-p filename)
                              (dir-ent-list-p dir-ent-list))
                  :guard-debug t))
  (b*
      (((when (atom dir-ent-list)) nil)
       (dir-ent (car dir-ent-list))
       ((when (equal (dir-ent-filename dir-ent)
                     filename))
        (delete-dir-ent (cdr dir-ent-list) filename)))
    (list* (dir-ent-fix dir-ent)
           (delete-dir-ent (cdr dir-ent-list)
                           filename))))

(defthm dir-ent-list-p-of-delete-dir-ent
  (dir-ent-list-p (delete-dir-ent dir-ent-list filename)))

(defthm len-of-delete-dir-ent
  (<= (len (delete-dir-ent dir-ent-list filename))
      (len dir-ent-list))
  :rule-classes :linear)

(defthm
  find-dir-ent-of-delete-dir-ent
  (implies
   (useful-dir-ent-list-p dir-ent-list)
   (equal (find-dir-ent (delete-dir-ent dir-ent-list filename1)
                        filename2)
          (if (equal filename1 filename2)
              (mv (dir-ent-fix nil) *enoent*)
            (find-dir-ent dir-ent-list filename2))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (useful-dir-ent-list-p dir-ent-filename len-when-dir-ent-p)
     ((:rewrite dir-ent-filename-of-dir-ent-set-filename)
      (:rewrite string=>nats-of-nats=>string)
      (:rewrite nth-update-nth)))
    :induct (delete-dir-ent dir-ent-list filename1))
   ("subgoal *1/2"
    :use
    ((:instance
      (:rewrite dir-ent-filename-of-dir-ent-set-filename)
      (filename
       (nats=>string
        (update-nth
         0 0
         (string=>nats (dir-ent-filename (car dir-ent-list))))))
      (dir-ent (car dir-ent-list)))
     (:instance
      (:rewrite string=>nats-of-nats=>string)
      (nats
       (update-nth
        0 0
        (string=>nats
         (nats=>string (take 11 (car dir-ent-list)))))))
     (:instance (:rewrite string=>nats-of-nats=>string)
                (nats (take 11 (car dir-ent-list))))
     (:instance (:rewrite nth-update-nth)
                (l (take 11 (car dir-ent-list)))
                (val 0)
                (n 0)
                (m 0))))))

(defthm
  useful-dir-ent-list-p-of-delete-dir-ent
  (implies (useful-dir-ent-list-p dir-ent-list)
           (useful-dir-ent-list-p (delete-dir-ent dir-ent-list filename)))
  :hints (("goal" :in-theory (enable useful-dir-ent-list-p))))

(defthm
  delete-dir-ent-correctness-1
  (implies
   (not (equal (mv-nth 1 (find-dir-ent dir-ent-list filename))
               0))
   (equal (delete-dir-ent dir-ent-list filename)
          (dir-ent-list-fix dir-ent-list))))

(defthm
  hifat-entry-count-of-lofat-to-hifat-helper-of-delete-dir-ent-lemma-3
  (implies
   (dir-ent-directory-p (mv-nth 0 (find-dir-ent dir-ent-list filename)))
   (equal (mv-nth 1 (find-dir-ent dir-ent-list filename))
          0)))

(encapsulate
  ()

  (local
   (defthmd
     hifat-entry-count-of-lofat-to-hifat-helper-of-delete-dir-ent-1
     (implies
      (and (useful-dir-ent-list-p dir-ent-list)
           (equal (mv-nth 3
                          (lofat-to-hifat-helper fat32-in-memory
                                                 dir-ent-list entry-limit))
                  0)
           (equal (mv-nth 1 (find-dir-ent dir-ent-list filename))
                  0)
           (not (dir-ent-directory-p (mv-nth 0
                                             (find-dir-ent dir-ent-list filename)))))
      (<
       (hifat-entry-count
        (mv-nth 0
                (lofat-to-hifat-helper fat32-in-memory
                                       (delete-dir-ent dir-ent-list filename)
                                       entry-limit)))
       (hifat-entry-count
        (mv-nth 0
                (lofat-to-hifat-helper fat32-in-memory
                                       dir-ent-list entry-limit)))))
     :hints
     (("goal" :in-theory
       (e/d (lofat-to-hifat-helper hifat-entry-count
                                   lofat-to-hifat-helper-correctness-4)
            ((:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
             (:rewrite nth-of-effective-fat)
             (:definition assoc-equal)
             (:definition hifat-file-alist-fix)))))
     :rule-classes :linear))

  ;; This induction proof is becoming a sort of bag to hold many things at
  ;; once... because it relieves the
  ;; (equal (mv-nth 3 (lofat-to-hifat-helper ...)) 0) free-variable related
  ;; hypothesis that's needed by some of these other things.
  (local
   (defthmd
     hifat-entry-count-of-lofat-to-hifat-helper-of-delete-dir-ent-2
     (implies
      (and (useful-dir-ent-list-p dir-ent-list)
           (equal (mv-nth 3
                          (lofat-to-hifat-helper fat32-in-memory
                                                 dir-ent-list entry-limit))
                  0)
           (dir-ent-directory-p (mv-nth 0
                                        (find-dir-ent dir-ent-list filename)))
           (not-intersectp-list
            x
            (mv-nth
             2
             (lofat-to-hifat-helper fat32-in-memory
                                    dir-ent-list entry-limit))))
      (and
       (<
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper fat32-in-memory
                                        (delete-dir-ent dir-ent-list filename)
                                        entry-limit)))
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper fat32-in-memory
                                         dir-ent-list entry-limit)))
         (hifat-entry-count
          (mv-nth
           0
           (lofat-to-hifat-helper
            fat32-in-memory
            (make-dir-ent-list
             (mv-nth 0
                     (dir-ent-clusterchain-contents
                      fat32-in-memory
                      (mv-nth 0
                              (find-dir-ent dir-ent-list filename)))))
            entry-limit)))))
       (equal
        (mv-nth
         3
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (mv-nth 0
                   (dir-ent-clusterchain-contents
                    fat32-in-memory
                    (mv-nth 0
                            (find-dir-ent dir-ent-list filename)))))
          entry-limit))
        0)
       (not-intersectp-list
        (mv-nth
         0
         (dir-ent-clusterchain
          fat32-in-memory
          (mv-nth 0
                  (find-dir-ent dir-ent-list filename))))
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents
             fat32-in-memory
             (mv-nth 0
                     (find-dir-ent dir-ent-list filename)))))
          entry-limit)))
       (not-intersectp-list
        x
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents
             fat32-in-memory
             (mv-nth 0
                     (find-dir-ent dir-ent-list filename)))))
          entry-limit)))))
     :hints
     (("goal" :in-theory
       (e/d (lofat-to-hifat-helper hifat-entry-count useful-dir-ent-list-p
                                   lofat-to-hifat-helper-correctness-4)
            ((:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
             (:rewrite nth-of-effective-fat)
             (:definition assoc-equal)
             (:definition hifat-file-alist-fix)))))))

  (defthm
    hifat-entry-count-of-lofat-to-hifat-helper-of-delete-dir-ent
    t
    :rule-classes
    ((:linear
      :corollary
      (implies
       (and (useful-dir-ent-list-p dir-ent-list)
            (equal (mv-nth 3
                           (lofat-to-hifat-helper fat32-in-memory
                                                  dir-ent-list entry-limit))
                   0))
       (<=
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper fat32-in-memory
                                        (delete-dir-ent dir-ent-list filename)
                                        entry-limit)))
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper fat32-in-memory
                                        dir-ent-list entry-limit)))))
      :hints
      (("Goal" :use
        (hifat-entry-count-of-lofat-to-hifat-helper-of-delete-dir-ent-1
         (:instance
          hifat-entry-count-of-lofat-to-hifat-helper-of-delete-dir-ent-2
          (x nil))))))
     (:linear
      :corollary
      (implies
       (and (useful-dir-ent-list-p dir-ent-list)
            (equal (mv-nth 3
                           (lofat-to-hifat-helper fat32-in-memory
                                                  dir-ent-list entry-limit))
                   0)
            (equal (mv-nth 1 (find-dir-ent dir-ent-list filename))
                   0)
            (not (dir-ent-directory-p (mv-nth 0
                                              (find-dir-ent dir-ent-list filename)))))
       (<
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper fat32-in-memory
                                        (delete-dir-ent dir-ent-list filename)
                                        entry-limit)))
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper fat32-in-memory
                                        dir-ent-list entry-limit)))))
      :hints
      (("Goal" :use
        (hifat-entry-count-of-lofat-to-hifat-helper-of-delete-dir-ent-1))))
     (:linear
      :corollary
      (implies
       (and (useful-dir-ent-list-p dir-ent-list)
            (equal (mv-nth 3
                           (lofat-to-hifat-helper fat32-in-memory
                                                  dir-ent-list entry-limit))
                   0)
            (dir-ent-directory-p (mv-nth 0
                                         (find-dir-ent dir-ent-list filename))))
       (<
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper fat32-in-memory
                                        (delete-dir-ent dir-ent-list filename)
                                        entry-limit)))
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper fat32-in-memory
                                         dir-ent-list entry-limit)))
         (hifat-entry-count
          (mv-nth
           0
           (lofat-to-hifat-helper
            fat32-in-memory
            (make-dir-ent-list
             (mv-nth 0
                     (dir-ent-clusterchain-contents
                      fat32-in-memory
                      (mv-nth 0
                              (find-dir-ent dir-ent-list filename)))))
            entry-limit))))))
      :hints
      (("Goal" :use
        (:instance
         hifat-entry-count-of-lofat-to-hifat-helper-of-delete-dir-ent-2
         (x nil)))))))

  (defthm
    dir-ent-clusterchain-contents-of-lofat-remove-file-disjoint-lemma-1
    (implies
     (and (useful-dir-ent-list-p dir-ent-list)
          (equal (mv-nth 3
                         (lofat-to-hifat-helper fat32-in-memory
                                                dir-ent-list entry-limit))
                 0)
          (dir-ent-directory-p (mv-nth 0
                                       (find-dir-ent dir-ent-list filename))))
     (not-intersectp-list
      (mv-nth
       0
       (dir-ent-clusterchain
        fat32-in-memory
        (mv-nth 0
                (find-dir-ent dir-ent-list filename))))
      (mv-nth
       2
       (lofat-to-hifat-helper
        fat32-in-memory
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents
           fat32-in-memory
           (mv-nth 0
                   (find-dir-ent dir-ent-list filename)))))
        entry-limit))))
    :hints
    (("Goal" :use
      (:instance
       hifat-entry-count-of-lofat-to-hifat-helper-of-delete-dir-ent-2
       (x nil)))))

  (defthm
    dir-ent-clusterchain-contents-of-lofat-remove-file-disjoint-lemma-2
    (implies
     (and (useful-dir-ent-list-p dir-ent-list)
          (equal (mv-nth 3
                         (lofat-to-hifat-helper fat32-in-memory
                                                dir-ent-list entry-limit))
                 0)
          (dir-ent-directory-p (mv-nth 0
                                       (find-dir-ent dir-ent-list filename)))
          (not-intersectp-list
           x
           (mv-nth
            2
            (lofat-to-hifat-helper fat32-in-memory
                                   dir-ent-list entry-limit))))
     (not-intersectp-list
      x
      (mv-nth
       2
       (lofat-to-hifat-helper
        fat32-in-memory
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents
           fat32-in-memory
           (mv-nth 0
                   (find-dir-ent dir-ent-list filename)))))
        entry-limit))))
    :hints
    (("Goal" :use
      hifat-entry-count-of-lofat-to-hifat-helper-of-delete-dir-ent-2))))

;; Care should be taken before choosing to change this function's
;; definition. It has the very useful property that the length of the directory
;; contents remain the same, which means no reallocation is required.
(defund
  clear-dir-ent (dir-contents filename)
  (declare
   (xargs :measure (len dir-contents)
          :guard (and (fat32-filename-p filename)
                      (unsigned-byte-listp 8 dir-contents))
          :guard-hints (("goal" :in-theory (enable dir-ent-p)))
          :guard-debug t))
  (b*
      (((when (< (len dir-contents)
                 *ms-dir-ent-length*))
        dir-contents)
       (dir-ent (take *ms-dir-ent-length* dir-contents))
       ((when (equal (char (dir-ent-filename dir-ent) 0)
                     (code-char 0)))
        dir-contents)
       ((when (equal (dir-ent-filename dir-ent)
                     filename))
        (append
         (dir-ent-set-filename
          dir-ent
          (nats=>string
           (update-nth 0 229
                       (string=>nats (dir-ent-filename dir-ent)))))
         (clear-dir-ent (nthcdr *ms-dir-ent-length* dir-contents)
                        filename))))
    (append
     dir-ent
     (clear-dir-ent (nthcdr *ms-dir-ent-length* dir-contents)
                    filename))))

(defthm
  len-of-clear-dir-ent
  (equal (len (clear-dir-ent dir-contents filename))
         (len dir-contents))
  :hints (("goal" :in-theory (enable len-when-dir-ent-p clear-dir-ent))))

(defthm
  unsigned-byte-listp-of-clear-dir-ent
  (implies
   (unsigned-byte-listp 8 dir-contents)
   (unsigned-byte-listp 8
                        (clear-dir-ent dir-contents filename)))
  :hints (("goal" :in-theory (enable clear-dir-ent))))

(defthm
  make-dir-ent-list-of-clear-dir-ent-lemma-1
  (implies
   (equal (char filename 0)
          (code-char #xe5))
   (useless-dir-ent-p (dir-ent-set-filename dir-ent filename)))
  :hints (("goal" :in-theory (enable useless-dir-ent-p))))

(defthm
  make-dir-ent-list-of-clear-dir-ent
  (equal
   (make-dir-ent-list (nats=>string (clear-dir-ent (string=>nats dir-contents)
                                                   filename)))
   (delete-dir-ent (make-dir-ent-list dir-contents)
                   filename))
  :hints (("goal" :in-theory (enable make-dir-ent-list dir-ent-fix
                                     clear-dir-ent
                                     len-when-dir-ent-p string=>nats
                                     nats=>string)
           :induct (make-dir-ent-list dir-contents)
           :expand (clear-dir-ent (chars=>nats (explode dir-contents))
                                  filename))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (make-event
   `(defthm
      make-dir-ent-list-of-append-3
      (implies
       (equal (mod (len (explode dir-contents))
                   *ms-dir-ent-length*)
              0)
       (equal
        (make-dir-ent-list
         (implode (append (nats=>chars (clear-dir-ent (string=>nats dir-contents)
                                                      filename))
                          (make-list-ac n ,(code-char 0) nil))))
        (delete-dir-ent (make-dir-ent-list dir-contents)
                        filename)))
      :hints
      (("goal" :induct (make-dir-ent-list dir-contents)
        :in-theory (e/d (make-dir-ent-list dir-ent-fix clear-dir-ent
                                           string=>nats))
        :expand ((make-dir-ent-list dir-contents)
                 (clear-dir-ent (chars=>nats (explode dir-contents))
                                filename)))))))

(defthm
  lofat-to-hifat-helper-of-clear-clusterchain
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (fat32-masked-entry-p masked-current-cluster)
    (<= *ms-first-data-cluster*
        masked-current-cluster)
    (< masked-current-cluster
       (+ *ms-first-data-cluster*
          (count-of-clusters fat32-in-memory)))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper fat32-in-memory
                             dir-ent-list entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0
             (fat32-build-index-list
              (effective-fat fat32-in-memory)
              masked-current-cluster
              length (cluster-size fat32-in-memory)))
     (mv-nth
      2
      (lofat-to-hifat-helper fat32-in-memory
                             dir-ent-list entry-limit))))
   (equal
    (lofat-to-hifat-helper
     (mv-nth 0
             (clear-clusterchain fat32-in-memory
                                 masked-current-cluster length))
     dir-ent-list entry-limit)
    (lofat-to-hifat-helper fat32-in-memory
                           dir-ent-list entry-limit)))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lofat-to-hifat-helper clear-clusterchain
                            lofat-to-hifat-helper-of-stobj-set-indices-in-fa-table)
     ((:rewrite nth-of-effective-fat)
      (:rewrite member-of-a-nat-list))))))

;; We're going to have to add a weird stipulation here about the length of a
;; directory file's contents being more than 0 (which is true, because dot and
;; dotdot entries have to be everywhere other than the root.)
(defun
    lofat-remove-file
    (fat32-in-memory root-dir-ent pathname)
  (declare
   (xargs
    :guard (and (lofat-fs-p fat32-in-memory)
                (dir-ent-p root-dir-ent)
                (>= (dir-ent-first-cluster root-dir-ent) *ms-first-data-cluster*)
                (< (dir-ent-first-cluster root-dir-ent)
                   (+ *ms-first-data-cluster*
                      (count-of-clusters fat32-in-memory)))
                (fat32-filename-list-p pathname))
    :measure (len pathname)
    :stobjs fat32-in-memory))
  (b*
      (((unless (consp pathname))
        (mv fat32-in-memory *enoent*))
       ;; Design choice - calls which ask for the entire root directory to be
       ;; affected will fail.
       (name (mbe :logic (fat32-filename-fix (car pathname))
                  :exec (car pathname)))
       ((mv dir-contents &)
        (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent))
       (dir-ent-list
        (make-dir-ent-list dir-contents))
       ((mv dir-ent error-code)
        (find-dir-ent dir-ent-list name))
       ;; If it's not there, it can't be removed
       ((unless (equal error-code 0))
        (mv fat32-in-memory *enoent*))
       ;; ENOTDIR - can't delete anything that supposedly exists inside a
       ;; regular file.
       ((when (and (consp (cdr pathname)) (not (dir-ent-directory-p dir-ent))))
        (mv fat32-in-memory *enotdir*))
       (first-cluster (dir-ent-first-cluster dir-ent))
       ((when
            (and
             (or (< first-cluster *ms-first-data-cluster*)
                 (<= (+ *ms-first-data-cluster*
                        (count-of-clusters fat32-in-memory))
                     first-cluster))
             (consp (cdr pathname))))
            (mv fat32-in-memory *eio*))
       ((when (consp (cdr pathname)))
        ;; Recursion
        (lofat-remove-file
         fat32-in-memory
         dir-ent
         (cdr pathname)))
       ;; After these conditionals, the only remaining possibility is that
       ;; (cdr pathname) is an atom, which means we need to delete a file or
       ;; a(n empty) directory.
       ((mv fat32-in-memory error-code)
        (update-dir-contents fat32-in-memory
                             (dir-ent-first-cluster root-dir-ent)
                             (nats=>string (clear-dir-ent (string=>nats
                                                           dir-contents)
                                                          name))))
       ((unless (equal error-code 0))
        (mv fat32-in-memory error-code))
       (length (if (dir-ent-directory-p dir-ent)
                   *ms-max-dir-size*
                 (dir-ent-file-size dir-ent)))
       ((mv fat32-in-memory &)
        (if
            (or (< first-cluster *ms-first-data-cluster*)
                (<= (+ *ms-first-data-cluster*
                       (count-of-clusters fat32-in-memory))
                    first-cluster))
            (mv fat32-in-memory 0)
          (clear-clusterchain
           fat32-in-memory
           first-cluster
           length))))
    (mv fat32-in-memory 0)))

(defthm
  lofat-fs-p-of-lofat-remove-file
  (implies (and (lofat-fs-p fat32-in-memory)
                (dir-ent-p root-dir-ent)
                (>= (dir-ent-first-cluster root-dir-ent)
                    *ms-first-data-cluster*)
                (< (dir-ent-first-cluster root-dir-ent)
                   (+ *ms-first-data-cluster*
                      (count-of-clusters fat32-in-memory))))
           (lofat-fs-p (mv-nth 0
                               (lofat-remove-file fat32-in-memory
                                                  root-dir-ent pathname)))))

(defthm
  max-entry-count-of-lofat-remove-file
  (equal
   (max-entry-count
    (mv-nth 0
            (lofat-remove-file fat32-in-memory root-dir-ent pathname)))
   (max-entry-count fat32-in-memory)))

(defthm
  pseudo-root-dir-ent-of-lofat-remove-file
  (equal
   (pseudo-root-dir-ent
    (mv-nth
     0
     (lofat-remove-file fat32-in-memory root-dir-ent pathname)))
   (pseudo-root-dir-ent fat32-in-memory)))

(defthm
  lofat-remove-file-correctness-2
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (dir-ent-p root-dir-ent)
    (>= (dir-ent-first-cluster root-dir-ent)
        *ms-first-data-cluster*)
    (< (dir-ent-first-cluster root-dir-ent)
       (+ *ms-first-data-cluster*
          (count-of-clusters fat32-in-memory)))
    (not
     (equal (mv-nth 1
                    (lofat-remove-file fat32-in-memory root-dir-ent pathname))
            0)))
   (equal (mv-nth 0
                  (lofat-remove-file fat32-in-memory root-dir-ent pathname))
          fat32-in-memory))
  :hints (("goal" :in-theory (enable update-dir-contents-correctness-1
                                     clear-clusterchain-correctness-3))))

(defthm
  get-clusterchain-contents-of-update-dir-contents-disjoint
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (stringp dir-contents)
    (fat32-masked-entry-p masked-current-cluster)
    (not (< masked-current-cluster '2))
    (fat32-masked-entry-p first-cluster)
    (<= 2 first-cluster)
    (not
     (intersectp-equal
      (mv-nth '0
              (fat32-build-index-list (effective-fat fat32-in-memory)
                                      first-cluster '2097152
                                      (cluster-size fat32-in-memory)))
      (mv-nth '0
              (fat32-build-index-list (effective-fat fat32-in-memory)
                                      masked-current-cluster length
                                      (cluster-size fat32-in-memory)))))
    (equal (mv-nth '1
                   (get-clusterchain-contents fat32-in-memory
                                              masked-current-cluster length))
           '0))
   (equal
    (get-clusterchain-contents
     (mv-nth 0
             (update-dir-contents fat32-in-memory
                                  first-cluster dir-contents))
     masked-current-cluster length)
    (get-clusterchain-contents fat32-in-memory
                               masked-current-cluster length)))
  :hints
  (("goal"
    :in-theory (e/d (update-dir-contents clear-clusterchain-correctness-1)
                    ((:rewrite intersectp-is-commutative)))
    :expand
    ((fat32-build-index-list (effective-fat fat32-in-memory)
                             first-cluster '2097152
                             (cluster-size fat32-in-memory))
     (intersectp-equal
      nil
      (mv-nth 0
              (fat32-build-index-list (effective-fat fat32-in-memory)
                                      masked-current-cluster length
                                      (cluster-size fat32-in-memory))))
     (:free
      (y)
      (intersectp-equal
       (cons first-cluster y)
       (mv-nth 0
               (fat32-build-index-list (effective-fat fat32-in-memory)
                                       masked-current-cluster length
                                       (cluster-size fat32-in-memory)))))
     (get-clusterchain-contents fat32-in-memory first-cluster 2097152))
    :use
    ((:instance
      (:rewrite intersectp-is-commutative)
      (y
       (cons
        first-cluster
        (mv-nth 0
                (fat32-build-index-list
                 (effective-fat fat32-in-memory)
                 (fat32-entry-mask (fati first-cluster fat32-in-memory))
                 (+ 2097152
                    (- (cluster-size fat32-in-memory)))
                 (cluster-size fat32-in-memory)))))
      (x (mv-nth 0
                 (fat32-build-index-list (effective-fat fat32-in-memory)
                                         masked-current-cluster length
                                         (cluster-size fat32-in-memory)))))
     (:instance
      (:rewrite intersectp-is-commutative)
      (y (cons first-cluster nil))
      (x
       (mv-nth 0
               (fat32-build-index-list (effective-fat fat32-in-memory)
                                       masked-current-cluster length
                                       (cluster-size fat32-in-memory)))))))))

(defthm
  get-clusterchain-contents-of-update-dir-contents-coincident-lemma-1
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (< 0 (len (explode dir-contents))))
   (not (< (binary-+ '-1
                     (len (make-clusters dir-contents
                                         (cluster-size fat32-in-memory))))
           '0))))

(defthmd
  get-clusterchain-contents-of-update-dir-contents-coincident-lemma-2
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
                                                   0 nil)))))

(defthmd
  get-clusterchain-contents-of-update-dir-contents-coincident-lemma-3
  (implies
   (<
    (+
     (count-free-clusters (effective-fat fat32-in-memory))
     (len
      (mv-nth
       0
       (fat32-build-index-list
        (effective-fat fat32-in-memory)
        (fat32-entry-mask (fati first-cluster fat32-in-memory))
        (+ 2097152
           (- (cluster-size fat32-in-memory)))
        (cluster-size fat32-in-memory)))))
    (+ -1
       (len (make-clusters dir-contents
                           (cluster-size fat32-in-memory)))))
   (not
    (equal
     (binary-+
      '1
      (binary-+
       (count-free-clusters (effective-fat fat32-in-memory))
       (len
        (mv-nth
         '0
         (fat32-build-index-list
          (effective-fat fat32-in-memory)
          (fat32-entry-mask
           (fati first-cluster fat32-in-memory))
          (binary-+ '2097152
                    (unary-- (cluster-size fat32-in-memory)))
          (cluster-size fat32-in-memory))))))
     (len (make-clusters dir-contents
                         (cluster-size fat32-in-memory)))))))

;; Hypotheses are minimal.
(defthm
  get-clusterchain-contents-of-update-dir-contents-coincident
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (fat32-masked-entry-p first-cluster)
    (stringp dir-contents)
    ;; Are we sure about the next hypothesis?
    (< 0 (len (explode dir-contents)))
    (<= (len (explode dir-contents))
        *ms-max-dir-size*)
    (equal
     (mv-nth 1
             (get-clusterchain-contents fat32-in-memory
                                        first-cluster *ms-max-dir-size*))
     0))
   (equal
    (get-clusterchain-contents
     (mv-nth 0
             (update-dir-contents fat32-in-memory
                                  first-cluster dir-contents))
     first-cluster *ms-max-dir-size*)
    (if
        (equal (mv-nth 1
                       (update-dir-contents fat32-in-memory
                                            first-cluster dir-contents))
               0)
        (mv
         (implode
          (append
           (explode dir-contents)
           (make-list-ac
            (+ (- (len (explode dir-contents)))
               (* (cluster-size fat32-in-memory)
                  (len (make-clusters dir-contents
                                      (cluster-size fat32-in-memory)))))
            (code-char 0)
            nil)))
         0)
      (get-clusterchain-contents
       fat32-in-memory
       first-cluster *ms-max-dir-size*))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (update-dir-contents
      get-clusterchain-contents-of-update-dir-contents-coincident-lemma-3
      (:linear hifat-to-lofat-inversion-lemma-16))
     ((:rewrite nth-of-set-indices-in-fa-table-when-member)))
    :expand
    ((fat32-build-index-list (effective-fat fat32-in-memory)
                             first-cluster *ms-max-dir-size*
                             (cluster-size fat32-in-memory))
     (get-clusterchain-contents fat32-in-memory first-cluster 2097152))
    :use
    ((:instance
      (:rewrite nth-of-set-indices-in-fa-table-when-member)
      (val 0)
      (index-list
       (cons
        first-cluster
        (mv-nth 0
                (fat32-build-index-list
                 (effective-fat fat32-in-memory)
                 (fat32-entry-mask (fati first-cluster fat32-in-memory))
                 (+ 2097152
                    (- (cluster-size fat32-in-memory)))
                 (cluster-size fat32-in-memory)))))
      (fa-table (effective-fat fat32-in-memory))
      (n first-cluster))
     (:instance
      (:rewrite
       get-clusterchain-contents-of-update-dir-contents-coincident-lemma-2)
      (index-list
       (cons
        first-cluster
        (mv-nth 0
                (fat32-build-index-list
                 (effective-fat fat32-in-memory)
                 (fat32-entry-mask (fati first-cluster fat32-in-memory))
                 (+ 2097152
                    (- (cluster-size fat32-in-memory)))
                 (cluster-size fat32-in-memory)))))
      (fa-table (effective-fat fat32-in-memory)))
     (:rewrite update-dir-contents-correctness-1)))))

(defthm
  dir-ent-clusterchain-contents-of-update-dir-contents-disjoint
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (stringp dir-contents)
    (dir-ent-p dir-ent)
    (<= *ms-first-data-cluster*
        (dir-ent-first-cluster dir-ent))
    (fat32-masked-entry-p first-cluster)
    (<= 2 first-cluster)
    (not (intersectp-equal
          (mv-nth '0
                  (fat32-build-index-list (effective-fat fat32-in-memory)
                                          first-cluster '2097152
                                          (cluster-size fat32-in-memory)))
          (mv-nth '0
                  (dir-ent-clusterchain fat32-in-memory dir-ent))))
    (equal (mv-nth '1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
           '0))
   (equal (dir-ent-clusterchain-contents
           (mv-nth 0
                   (update-dir-contents fat32-in-memory
                                        first-cluster dir-contents))
           dir-ent)
          (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
  :hints (("goal" :in-theory (enable dir-ent-clusterchain
                                     dir-ent-clusterchain-contents))))

;; Hypotheses are minimal.
(defthm
  dir-ent-clusterchain-contents-of-update-dir-contents-coincident
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (fat32-masked-entry-p first-cluster)
    (< 0 (len (explode dir-contents)))
    (<= (len (explode dir-contents))
        *ms-max-dir-size*)
    (equal (mv-nth 1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
           0)
    (equal (dir-ent-first-cluster dir-ent)
           first-cluster)
    (dir-ent-directory-p dir-ent))
   (equal
    (dir-ent-clusterchain-contents
     (mv-nth 0
             (update-dir-contents fat32-in-memory
                                  first-cluster dir-contents))
     dir-ent)
    (if
        (equal (mv-nth 1
                       (update-dir-contents fat32-in-memory
                                            first-cluster dir-contents))
               0)
        (mv
         (implode
          (append
           (explode dir-contents)
           (make-list-ac
            (+ (- (len (explode dir-contents)))
               (* (cluster-size fat32-in-memory)
                  (len (make-clusters dir-contents
                                      (cluster-size fat32-in-memory)))))
            (code-char 0)
            nil)))
         0)
      (dir-ent-clusterchain-contents
       fat32-in-memory
       dir-ent))))
  :hints
  (("goal" :in-theory
    (e/d (dir-ent-clusterchain-contents)
         (get-clusterchain-contents-of-update-dir-contents-coincident))
    :use get-clusterchain-contents-of-update-dir-contents-coincident)))

(defthm
  lofat-to-hifat-helper-of-update-dir-contents
  (implies
   (and (useful-dir-ent-list-p dir-ent-list)
        (lofat-fs-p fat32-in-memory)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32-in-memory
                                              dir-ent-list entry-limit))
               0)
        (fat32-masked-entry-p first-cluster)
        (<= *ms-first-data-cluster* first-cluster)
        (stringp dir-contents)
        (not-intersectp-list
         (mv-nth 0
                 (fat32-build-index-list (effective-fat fat32-in-memory)
                                         first-cluster *ms-max-dir-size*
                                         (cluster-size fat32-in-memory)))
         (mv-nth 2
                 (lofat-to-hifat-helper fat32-in-memory
                                        dir-ent-list entry-limit))))
   (equal (lofat-to-hifat-helper
           (mv-nth 0
                   (update-dir-contents fat32-in-memory
                                        first-cluster dir-contents))
           dir-ent-list entry-limit)
          (lofat-to-hifat-helper fat32-in-memory
                                 dir-ent-list entry-limit)))
  :hints (("goal" :in-theory (enable lofat-to-hifat-helper
                                     not-intersectp-list)
           :induct (lofat-to-hifat-helper fat32-in-memory
                                          dir-ent-list entry-limit))))

;; The (cdr dir-ent-list) stuff in this lemma isn't very nice, but the
;; alternative is having free variables, so...
(defthm
  dir-ent-clusterchain-contents-of-lofat-remove-file-disjoint-lemma-6
  (implies
   (equal
    (mv-nth
     3
     (lofat-to-hifat-helper
      fat32-in-memory
      (make-dir-ent-list
       (string=>nats (mv-nth 0
                             (dir-ent-clusterchain-contents
                              fat32-in-memory
                              (mv-nth 0
                                      (find-dir-ent (cdr dir-ent-list)
                                                    filename))))))
      (+
       -2 entry-limit
       (-
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32-in-memory
           (make-dir-ent-list
            (string=>nats (mv-nth 0
                                  (dir-ent-clusterchain-contents
                                   fat32-in-memory (car dir-ent-list)))))
           (+ -1 entry-limit))))))))
    0)
   (equal
    (lofat-to-hifat-helper
     fat32-in-memory
     (make-dir-ent-list
      (string=>nats (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory
                             (mv-nth 0
                                     (find-dir-ent (cdr dir-ent-list)
                                                   filename))))))
     (+ -1 entry-limit))
    (lofat-to-hifat-helper
     fat32-in-memory
     (make-dir-ent-list
      (string=>nats (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory
                             (mv-nth 0
                                     (find-dir-ent (cdr dir-ent-list)
                                                   filename))))))
     (+
      -2 entry-limit
      (-
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (string=>nats (mv-nth 0
                                 (dir-ent-clusterchain-contents
                                  fat32-in-memory (car dir-ent-list)))))
          (+ -1 entry-limit)))))))))
  :hints
  (("goal"
    :in-theory (disable (:linear lofat-to-hifat-helper-correctness-3))
    :use
    ((:instance
      (:rewrite lofat-to-hifat-helper-correctness-4)
      (entry-limit1
       (+
        -2 entry-limit
        (-
         (hifat-entry-count
          (mv-nth
           0
           (lofat-to-hifat-helper
            fat32-in-memory
            (make-dir-ent-list
             (string=>nats (mv-nth 0
                                   (dir-ent-clusterchain-contents
                                    fat32-in-memory (car dir-ent-list)))))
            (+ -1 entry-limit)))))))
      (entry-limit2 (+ -1 entry-limit))
      (dir-ent-list
       (make-dir-ent-list
        (string=>nats (mv-nth 0
                              (dir-ent-clusterchain-contents
                               fat32-in-memory
                               (mv-nth 0
                                       (find-dir-ent (cdr dir-ent-list)
                                                     filename)))))))
      (fat32-in-memory fat32-in-memory))
     (:instance
      (:linear lofat-to-hifat-helper-correctness-3)
      (entry-limit
       (+
        -2 entry-limit
        (-
         (hifat-entry-count
          (mv-nth
           0
           (lofat-to-hifat-helper
            fat32-in-memory
            (make-dir-ent-list
             (string=>nats (mv-nth 0
                                   (dir-ent-clusterchain-contents
                                    fat32-in-memory (car dir-ent-list)))))
            (+ -1 entry-limit)))))))
      (dir-ent-list
       (make-dir-ent-list
        (string=>nats (mv-nth 0
                              (dir-ent-clusterchain-contents
                               fat32-in-memory
                               (mv-nth 0
                                       (find-dir-ent (cdr dir-ent-list)
                                                     filename)))))))
      (fat32-in-memory fat32-in-memory))))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-remove-file-disjoint-lemma-7
  (implies
   (and
    (not-intersectp-list
     x
     (mv-nth 2
             (lofat-to-hifat-helper fat32-in-memory
                                    dir-ent-list entry-limit)))
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32-in-memory
                                          dir-ent-list entry-limit))
           0)
    (dir-ent-list-p dir-ent-list)
    (<= 2
        (dir-ent-first-cluster (mv-nth 0
                                       (find-dir-ent dir-ent-list filename))))
    (< (dir-ent-first-cluster (mv-nth 0 (find-dir-ent dir-ent-list filename)))
       (+ 2 (count-of-clusters fat32-in-memory))))
   (not
    (intersectp-equal
     x
     (mv-nth
      '0
      (dir-ent-clusterchain fat32-in-memory
                            (mv-nth '0
                                    (find-dir-ent dir-ent-list filename)))))))
  :hints
  (("goal"
    :in-theory (e/d (lofat-to-hifat-helper not-intersectp-list)
                    ((:rewrite nth-of-effective-fat)))
    :expand ((:free (x) (intersectp-equal nil x)))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and
      (not-intersectp-list
       x
       (mv-nth 2
               (lofat-to-hifat-helper fat32-in-memory
                                      dir-ent-list entry-limit)))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32-in-memory
                                            dir-ent-list entry-limit))
             0)
      (dir-ent-list-p dir-ent-list)
      (not (dir-ent-directory-p (mv-nth 0
                                        (find-dir-ent dir-ent-list filename))))
      (<= 2
          (dir-ent-first-cluster (mv-nth 0
                                         (find-dir-ent dir-ent-list filename))))
      (< (dir-ent-first-cluster (mv-nth 0 (find-dir-ent dir-ent-list filename)))
         (+ 2 (count-of-clusters fat32-in-memory))))
     (not
      (intersectp-equal
       x
       (mv-nth
        '0
        (fat32-build-index-list
         (effective-fat fat32-in-memory)
         (dir-ent-first-cluster (mv-nth '0
                                        (find-dir-ent dir-ent-list filename)))
         (dir-ent-file-size (mv-nth '0
                                    (find-dir-ent dir-ent-list filename)))
         (cluster-size fat32-in-memory))))))
    :hints
    (("goal"
      :in-theory (enable dir-ent-clusterchain))))
   (:rewrite
    :corollary
    (implies
     (and
      (not-intersectp-list
       x
       (mv-nth 2
               (lofat-to-hifat-helper fat32-in-memory
                                      dir-ent-list entry-limit)))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32-in-memory
                                            dir-ent-list entry-limit))
             0)
      (dir-ent-list-p dir-ent-list)
      (dir-ent-directory-p (mv-nth 0
                                   (find-dir-ent dir-ent-list filename)))
      (<= 2
          (dir-ent-first-cluster (mv-nth 0
                                         (find-dir-ent dir-ent-list filename))))
      (< (dir-ent-first-cluster (mv-nth 0 (find-dir-ent dir-ent-list filename)))
         (+ 2 (count-of-clusters fat32-in-memory))))
     (not
      (intersectp-equal
       x
       (mv-nth
        '0
        (fat32-build-index-list
         (effective-fat fat32-in-memory)
         (dir-ent-first-cluster (mv-nth '0
                                        (find-dir-ent dir-ent-list filename)))
         *ms-max-dir-size*
         (cluster-size fat32-in-memory))))))
    :hints
    (("goal"
      :in-theory (e/d (dir-ent-clusterchain)))))))

(defthmd
  dir-ent-clusterchain-contents-of-lofat-remove-file-disjoint-lemma-8
  (implies
   (and
    (not (natp entry-limit))
    (<=
     2
     (dir-ent-first-cluster
      (mv-nth
       0
       (find-dir-ent dir-ent-list filename)))))
   (not (equal
         (mv-nth
          3
          (lofat-to-hifat-helper
           fat32-in-memory dir-ent-list entry-limit))
         0)))
  :hints
  (("goal"
    :expand
    (lofat-to-hifat-helper
     fat32-in-memory
     dir-ent-list
     entry-limit))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-remove-file-disjoint-lemma-3
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (stringp dir-contents)
    (dir-ent-p dir-ent)
    (<= *ms-first-data-cluster*
        (dir-ent-first-cluster dir-ent))
    (dir-ent-p root-dir-ent)
    (dir-ent-directory-p root-dir-ent)
    (<= 2 (dir-ent-first-cluster root-dir-ent))
    (not (intersectp-equal
          (mv-nth '0
                  (dir-ent-clusterchain fat32-in-memory root-dir-ent))
          (mv-nth '0
                  (dir-ent-clusterchain fat32-in-memory dir-ent))))
    (equal (mv-nth '1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
           '0))
   (equal
    (dir-ent-clusterchain-contents
     (mv-nth 0
             (update-dir-contents fat32-in-memory
                                  (dir-ent-first-cluster root-dir-ent)
                                  dir-contents))
     dir-ent)
    (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
  :hints
  (("goal"
    :in-theory
    (e/d (dir-ent-clusterchain)
         (dir-ent-clusterchain-contents-of-update-dir-contents-disjoint))
    :use
    (:instance dir-ent-clusterchain-contents-of-update-dir-contents-disjoint
               (first-cluster (dir-ent-first-cluster root-dir-ent))))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-remove-file-disjoint-lemma-9
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (dir-ent-p dir-ent1)
        (dir-ent-directory-p dir-ent1)
        (dir-ent-p dir-ent2)
        (<= *ms-first-data-cluster*
            (dir-ent-first-cluster dir-ent1))
        (not (intersectp-equal
              (mv-nth '0
                      (dir-ent-clusterchain fat32-in-memory dir-ent1))
              (mv-nth '0
                      (dir-ent-clusterchain fat32-in-memory dir-ent2)))))
   (equal (dir-ent-clusterchain-contents
           (mv-nth 0
                   (clear-clusterchain fat32-in-memory
                                       (dir-ent-first-cluster dir-ent1)
                                       *ms-max-dir-size*))
           dir-ent2)
          (dir-ent-clusterchain-contents fat32-in-memory dir-ent2)))
  :hints
  (("goal"
    :in-theory (e/d (dir-ent-clusterchain)
                    (dir-ent-clusterchain-contents-of-clear-clusterchain))
    :use (:instance dir-ent-clusterchain-contents-of-clear-clusterchain
                    (dir-ent dir-ent2)
                    (masked-current-cluster (dir-ent-first-cluster dir-ent1))
                    (length *ms-max-dir-size*)))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-remove-file-disjoint-lemma-10
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (dir-ent-p dir-ent1)
        (not (dir-ent-directory-p dir-ent1))
        (dir-ent-p dir-ent2)
        (<= *ms-first-data-cluster*
            (dir-ent-first-cluster dir-ent1))
        (not (intersectp-equal
              (mv-nth '0
                      (dir-ent-clusterchain fat32-in-memory dir-ent1))
              (mv-nth '0
                      (dir-ent-clusterchain fat32-in-memory dir-ent2)))))
   (equal (dir-ent-clusterchain-contents
           (mv-nth 0
                   (clear-clusterchain fat32-in-memory
                                       (dir-ent-first-cluster dir-ent1)
                                       (dir-ent-file-size dir-ent1)))
           dir-ent2)
          (dir-ent-clusterchain-contents fat32-in-memory dir-ent2)))
  :hints
  (("goal"
    :in-theory (e/d (dir-ent-clusterchain)
                    (dir-ent-clusterchain-contents-of-clear-clusterchain))
    :use (:instance dir-ent-clusterchain-contents-of-clear-clusterchain
                    (dir-ent dir-ent2)
                    (masked-current-cluster (dir-ent-first-cluster dir-ent1))
                    (length (dir-ent-file-size dir-ent1))))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-remove-file-disjoint-lemma-11
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (stringp dir-contents)
    (dir-ent-p dir-ent)
    (<= *ms-first-data-cluster*
        (dir-ent-first-cluster dir-ent))
    (dir-ent-p root-dir-ent)
    (dir-ent-directory-p root-dir-ent)
    (<= 2 (dir-ent-first-cluster root-dir-ent))
    (not (intersectp-equal
          (mv-nth '0
                  (dir-ent-clusterchain fat32-in-memory root-dir-ent))
          (mv-nth '0
                  (dir-ent-clusterchain fat32-in-memory dir-ent))))
    (equal (mv-nth '1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
           '0))
   (equal
    (dir-ent-clusterchain
     (mv-nth 0
             (update-dir-contents fat32-in-memory
                                  (dir-ent-first-cluster root-dir-ent)
                                  dir-contents))
     dir-ent)
    (dir-ent-clusterchain fat32-in-memory dir-ent)))
  :hints
  (("goal"
    :in-theory (e/d (dir-ent-clusterchain dir-ent-clusterchain-contents)
                    (dir-ent-clusterchain-of-update-dir-contents))
    :use (:instance dir-ent-clusterchain-of-update-dir-contents
                    (first-cluster (dir-ent-first-cluster root-dir-ent))))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-remove-file-disjoint-lemma-4
  (implies
   (and
    (useful-dir-ent-list-p dir-ent-list)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32-in-memory
                                          dir-ent-list entry-limit))
           0)
    (>=
     (dir-ent-first-cluster (mv-nth 0 (find-dir-ent dir-ent-list filename)))
     *ms-first-data-cluster*)
    (> (+ *ms-first-data-cluster*
          (count-of-clusters fat32-in-memory))
       (dir-ent-first-cluster (mv-nth 0
                                      (find-dir-ent dir-ent-list filename)))))
   (and
    (equal (mv-nth 1
                   (dir-ent-clusterchain-contents
                    fat32-in-memory
                    (mv-nth 0
                            (find-dir-ent dir-ent-list filename))))
           0)
    (no-duplicatesp-equal
     (mv-nth
      0
      (dir-ent-clusterchain fat32-in-memory
                            (mv-nth 0
                                    (find-dir-ent dir-ent-list filename)))))))
  :hints
  (("goal" :in-theory
    (e/d (lofat-to-hifat-helper)
         (nth-of-effective-fat (:definition no-duplicatesp-equal))))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-remove-file-disjoint-lemma-5
  (implies
   (and (useful-dir-ent-list-p dir-ent-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32-in-memory
                                              dir-ent-list entry-limit))
               0)
        (dir-ent-directory-p (mv-nth 0
                                     (find-dir-ent dir-ent-list filename))))
   (subdir-contents-p
    (mv-nth 0
            (dir-ent-clusterchain-contents
             fat32-in-memory
             (mv-nth 0
                     (find-dir-ent dir-ent-list filename))))))
  :hints
  (("goal" :in-theory
    (e/d (lofat-to-hifat-helper)
         (nth-of-effective-fat (:definition no-duplicatesp-equal))))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-remove-file-disjoint-lemma-12
  (implies
   (equal (mv-nth 1
                  (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
          0)
   (and (<= *ms-first-data-cluster*
            (dir-ent-first-cluster dir-ent))
        (< (dir-ent-first-cluster dir-ent)
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory)))))
  :hints
  (("goal" :in-theory (enable dir-ent-clusterchain-contents)
    :expand ((get-clusterchain-contents fat32-in-memory
                                        (dir-ent-first-cluster dir-ent)
                                        (dir-ent-file-size dir-ent))
             (get-clusterchain-contents fat32-in-memory
                                        (dir-ent-first-cluster dir-ent)
                                        2097152))))
  :rule-classes :linear)

(defthm
  dir-ent-clusterchain-contents-of-lofat-remove-file-disjoint
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (<= *ms-first-data-cluster*
        (dir-ent-first-cluster root-dir-ent))
    (< (dir-ent-first-cluster root-dir-ent)
       (+ *ms-first-data-cluster*
          (count-of-clusters fat32-in-memory)))
    (dir-ent-p root-dir-ent)
    (dir-ent-directory-p root-dir-ent)
    (dir-ent-p dir-ent)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory dir-ent))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit)))
    (not (intersectp-equal
          (mv-nth 0
                  (dir-ent-clusterchain fat32-in-memory root-dir-ent))
          (mv-nth 0
                  (dir-ent-clusterchain fat32-in-memory dir-ent))))
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory root-dir-ent))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit)))
    (equal (mv-nth 1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
           0))
   (equal
    (dir-ent-clusterchain-contents
     (mv-nth 0
             (lofat-remove-file fat32-in-memory root-dir-ent pathname))
     dir-ent)
    (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
  :hints (("goal" :induct (lofat-remove-file fat32-in-memory
                                             root-dir-ent pathname))))

(defthm
  root-dir-ent-list-of-update-dir-contents
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (dir-ent-p dir-ent)
    (dir-ent-directory-p dir-ent)
    (<= *ms-first-data-cluster*
        (dir-ent-first-cluster dir-ent))
    (stringp dir-contents)
    (equal (mv-nth 1 (root-dir-ent-list fat32-in-memory))
           0)
    (not
     (intersectp-equal
      (mv-nth 0
              (dir-ent-clusterchain fat32-in-memory dir-ent))
      (mv-nth 0
              (dir-ent-clusterchain fat32-in-memory
                                    (pseudo-root-dir-ent fat32-in-memory))))))
   (equal (root-dir-ent-list
           (mv-nth 0
                   (update-dir-contents fat32-in-memory
                                        (dir-ent-first-cluster dir-ent)
                                        dir-contents)))
          (root-dir-ent-list fat32-in-memory)))
  :hints (("goal" :in-theory (enable root-dir-ent-list))))

(defthm
  count-of-clusters-of-lofat-remove-file
  (equal (count-of-clusters
          (mv-nth 0
                  (lofat-remove-file
                   fat32-in-memory rootclus pathname)))
         (count-of-clusters fat32-in-memory)))

(defthm
  cluster-size-of-lofat-remove-file
  (equal (cluster-size
          (mv-nth 0
                  (lofat-remove-file
                   fat32-in-memory rootclus pathname)))
         (cluster-size fat32-in-memory)))

(defthm
  subdir-contents-p-when-zero-length
  (implies (and (stringp contents) (equal (len (explode contents)) 0))
           (not (subdir-contents-p contents)))
  :hints (("goal" :in-theory (enable subdir-contents-p remove1-dir-ent))))

(defthm
  get-clusterchain-contents-of-lofat-remove-file-coincident-lemma-1
  (implies
   (and (useful-dir-ent-list-p dir-ent-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32-in-memory
                                              dir-ent-list entry-limit))
               0)
        (dir-ent-directory-p (mv-nth 0
                                     (find-dir-ent dir-ent-list filename))))
   (and
    (<
     0
     (len
      (explode
       (mv-nth 0
               (get-clusterchain-contents
                fat32-in-memory
                (dir-ent-first-cluster
                 (mv-nth 0 (find-dir-ent dir-ent-list filename)))
                *ms-max-dir-size*)))))
    (equal
     (mv-nth
      1
      (get-clusterchain-contents
       fat32-in-memory
       (dir-ent-first-cluster (mv-nth 0 (find-dir-ent dir-ent-list filename)))
       *ms-max-dir-size*))
     0)))
  :hints
  (("goal" :in-theory
    (e/d (lofat-to-hifat-helper dir-ent-clusterchain-contents)
         ((:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
          (:definition free-index-listp)
          (:rewrite nth-of-effective-fat)))
    :induct (lofat-to-hifat-helper fat32-in-memory
                                   dir-ent-list entry-limit)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (useful-dir-ent-list-p dir-ent-list)
          (equal (mv-nth 3
                         (lofat-to-hifat-helper fat32-in-memory
                                                dir-ent-list entry-limit))
                 0)
          (dir-ent-directory-p (mv-nth 0
                                       (find-dir-ent dir-ent-list filename))))
     (equal (mv-nth 1
                    (get-clusterchain-contents
                     fat32-in-memory
                     (dir-ent-first-cluster
                      (mv-nth 0 (find-dir-ent dir-ent-list filename)))
                     *ms-max-dir-size*))
            0)))
   (:linear
    :corollary
    (implies
     (and (useful-dir-ent-list-p dir-ent-list)
          (equal (mv-nth 3
                         (lofat-to-hifat-helper fat32-in-memory
                                                dir-ent-list entry-limit))
                 0)
          (dir-ent-directory-p (mv-nth 0
                                       (find-dir-ent dir-ent-list filename))))
     (<
      0
      (len
       (explode
        (mv-nth 0
                (get-clusterchain-contents
                 fat32-in-memory
                 (dir-ent-first-cluster
                  (mv-nth 0 (find-dir-ent dir-ent-list filename)))
                 *ms-max-dir-size*)))))))))

(defthm
  get-clusterchain-contents-of-lofat-remove-file-coincident-lemma-5
  (implies
   (and
    (dir-ent-list-p dir-ent-list)
    (<= 2
        (dir-ent-first-cluster
         (mv-nth 0
                 (find-dir-ent dir-ent-list filename))))
    (< (dir-ent-first-cluster
        (mv-nth 0 (find-dir-ent dir-ent-list filename)))
       (+ 2 (count-of-clusters fat32-in-memory)))
    (equal
     (mv-nth 3
             (lofat-to-hifat-helper fat32-in-memory
                                    dir-ent-list entry-limit))
     0)
    (not-intersectp-list
     x
     (mv-nth 2
             (lofat-to-hifat-helper fat32-in-memory
                                    dir-ent-list entry-limit))))
   (not
    (intersectp-equal
     x
     (mv-nth
      0
      (dir-ent-clusterchain
       fat32-in-memory
       (mv-nth 0
               (find-dir-ent dir-ent-list filename)))))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lofat-to-hifat-helper not-intersectp-list)
     ((:rewrite nth-of-effective-fat)
      (:rewrite integerp-of-car-when-integer-listp)
      (:definition integer-listp)
      (:definition len)))
    :induct t))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and
      (dir-ent-list-p dir-ent-list)
      (<= 2
          (dir-ent-first-cluster
           (mv-nth 0
                   (find-dir-ent dir-ent-list filename))))
      (< (dir-ent-first-cluster
          (mv-nth 0 (find-dir-ent dir-ent-list filename)))
         (+ 2 (count-of-clusters fat32-in-memory)))
      (dir-ent-directory-p
       (mv-nth 0 (find-dir-ent dir-ent-list filename)))
      (equal
       (mv-nth 3
               (lofat-to-hifat-helper fat32-in-memory
                                      dir-ent-list entry-limit))
       0)
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper fat32-in-memory
                               dir-ent-list entry-limit))))
     (not
      (intersectp-equal
       x
       (mv-nth
        0
        (fat32-build-index-list
         (effective-fat fat32-in-memory)
         (dir-ent-first-cluster
          (mv-nth 0 (find-dir-ent dir-ent-list filename)))
         *ms-max-dir-size*
         (cluster-size fat32-in-memory))))))
    :hints
    (("goal" :in-theory (enable dir-ent-clusterchain))))
   (:rewrite
    :corollary
    (implies
     (and
      (dir-ent-list-p dir-ent-list)
      (<= 2
          (dir-ent-first-cluster
           (mv-nth 0
                   (find-dir-ent dir-ent-list filename))))
      (< (dir-ent-first-cluster
          (mv-nth 0 (find-dir-ent dir-ent-list filename)))
         (+ 2 (count-of-clusters fat32-in-memory)))
      (not (dir-ent-directory-p
            (mv-nth 0 (find-dir-ent dir-ent-list filename))))
      (equal
       (mv-nth 3
               (lofat-to-hifat-helper fat32-in-memory
                                      dir-ent-list entry-limit))
       0)
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper fat32-in-memory
                               dir-ent-list entry-limit))))
     (not
      (intersectp-equal
       x
       (mv-nth
        0
        (fat32-build-index-list
         (effective-fat fat32-in-memory)
         (dir-ent-first-cluster
          (mv-nth 0 (find-dir-ent dir-ent-list filename)))
         (dir-ent-file-size
          (mv-nth 0 (find-dir-ent dir-ent-list filename)))
         (cluster-size fat32-in-memory))))))
    :hints
    (("goal" :in-theory (enable dir-ent-clusterchain))))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-remove-file-coincident-lemma-1
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (dir-ent-p dir-ent2)
        (dir-ent-p dir-ent1)
        (dir-ent-directory-p dir-ent1)
        (<= *ms-first-data-cluster*
            (dir-ent-first-cluster dir-ent1))
        (not (intersectp-equal
              (mv-nth '0
                      (dir-ent-clusterchain fat32-in-memory dir-ent1))
              (mv-nth '0
                      (dir-ent-clusterchain fat32-in-memory dir-ent2)))))
   (equal (dir-ent-clusterchain
           (mv-nth 0
                   (clear-clusterchain fat32-in-memory
                                       (dir-ent-first-cluster dir-ent1)
                                       *ms-max-dir-size*))
           dir-ent2)
          (dir-ent-clusterchain fat32-in-memory dir-ent2)))
  :hints
  (("goal"
    :in-theory (e/d (dir-ent-clusterchain)
                    (dir-ent-clusterchain-of-clear-clusterchain))
    :use (:instance dir-ent-clusterchain-of-clear-clusterchain
                    (dir-ent dir-ent2)
                    (masked-current-cluster (dir-ent-first-cluster dir-ent1))
                    (length *ms-max-dir-size*)))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-remove-file-coincident-lemma-2
  (implies
   (and
    (dir-ent-directory-p
     (mv-nth
      0
      (find-dir-ent
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       (car pathname))))
    (<=
     2
     (dir-ent-first-cluster
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents
           fat32-in-memory
           (mv-nth
            0
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth
               0
               (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
             (car pathname))))))
        (cadr pathname)))))
    (<
     (dir-ent-first-cluster
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents
           fat32-in-memory
           (mv-nth
            0
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth
               0
               (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
             (car pathname))))))
        (cadr pathname))))
     (+ 2 (count-of-clusters fat32-in-memory)))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       entry-limit))
     0))
   (not
    (intersectp-equal
     (mv-nth
      '0
      (dir-ent-clusterchain
       fat32-in-memory
       (mv-nth
        '0
        (find-dir-ent
         (make-dir-ent-list
          (mv-nth '0
                  (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
         (car pathname)))))
     (mv-nth
      '0
      (dir-ent-clusterchain
       fat32-in-memory
       (mv-nth
        '0
        (find-dir-ent
         (make-dir-ent-list
          (mv-nth
           '0
           (dir-ent-clusterchain-contents
            fat32-in-memory
            (mv-nth
             '0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                '0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
              (car pathname))))))
         (car (cdr pathname)))))))))
  :hints
  (("goal"
    :in-theory
    (disable
     (:rewrite
      get-clusterchain-contents-of-lofat-remove-file-coincident-lemma-5
      . 1))
    :use
    (:instance
     (:rewrite
      get-clusterchain-contents-of-lofat-remove-file-coincident-lemma-5
      . 1)
     (filename (cadr pathname))
     (dir-ent-list
      (make-dir-ent-list
       (mv-nth
        0
        (dir-ent-clusterchain-contents
         fat32-in-memory
         (mv-nth
          0
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth 0
                    (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
           (car pathname)))))))
     (fat32-in-memory fat32-in-memory)
     (x
      (mv-nth
       0
       (dir-ent-clusterchain
        fat32-in-memory
        (mv-nth
         0
         (find-dir-ent
          (make-dir-ent-list
           (mv-nth 0
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
          (car pathname))))))))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-remove-file-coincident-lemma-4
  (implies
   (and
    (dir-ent-directory-p
     (mv-nth
      0
      (find-dir-ent
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       (car pathname))))
    (<=
     2
     (dir-ent-first-cluster
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents
           fat32-in-memory
           (mv-nth
            0
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth
               0
               (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
             (car pathname))))))
        (cadr pathname)))))
    (<
     (dir-ent-first-cluster
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents
           fat32-in-memory
           (mv-nth
            0
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth
               0
               (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
             (car pathname))))))
        (cadr pathname))))
     (+ 2 (count-of-clusters fat32-in-memory)))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory dir-ent))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       entry-limit))))
   (not
    (intersectp-equal
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory dir-ent))
     (mv-nth
      0
      (dir-ent-clusterchain
       fat32-in-memory
       (mv-nth
        0
        (find-dir-ent
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents
            fat32-in-memory
            (mv-nth
             0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
              (car pathname))))))
         (cadr pathname))))))))
  :hints
  (("goal"
    :in-theory
    (disable
     (:rewrite
      get-clusterchain-contents-of-lofat-remove-file-coincident-lemma-5
      . 1))
    :use
    (:instance
     (:rewrite
      get-clusterchain-contents-of-lofat-remove-file-coincident-lemma-5
      . 1)
     (filename (cadr pathname))
     (dir-ent-list
      (make-dir-ent-list
       (mv-nth
        0
        (dir-ent-clusterchain-contents
         fat32-in-memory
         (mv-nth
          0
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth 0
                    (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
           (car pathname)))))))
     (fat32-in-memory fat32-in-memory)
     (x (mv-nth 0
                (dir-ent-clusterchain fat32-in-memory dir-ent)))))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-remove-file-coincident-lemma-5
  (implies
   (and
    (dir-ent-directory-p
     (mv-nth
      0
      (find-dir-ent
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       (car pathname))))
    (lofat-fs-p fat32-in-memory)
    (dir-ent-p dir-ent)
    (<= 2 (dir-ent-first-cluster dir-ent))
    (equal (mv-nth 1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
           0)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory dir-ent))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       entry-limit))))
   (equal
    (dir-ent-clusterchain-contents
     (mv-nth
      0
      (lofat-remove-file
       fat32-in-memory
       (mv-nth
        0
        (find-dir-ent
         (make-dir-ent-list
          (mv-nth 0
                  (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
         (car pathname)))
       (cdr pathname)))
     dir-ent)
    (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
  :hints
  (("goal"
    :in-theory
    (disable
     (:rewrite dir-ent-clusterchain-contents-of-lofat-remove-file-disjoint))
    :use
    (:instance
     (:rewrite dir-ent-clusterchain-contents-of-lofat-remove-file-disjoint)
     (pathname (cdr pathname))
     (root-dir-ent
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
        (car pathname))))
     (fat32-in-memory fat32-in-memory)))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-remove-file-coincident-lemma-6
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (dir-ent-p dir-ent2)
        (dir-ent-p dir-ent1)
        (not (dir-ent-directory-p dir-ent1))
        (<= *ms-first-data-cluster*
            (dir-ent-first-cluster dir-ent1))
        (not (intersectp-equal
              (mv-nth '0
                      (dir-ent-clusterchain fat32-in-memory dir-ent1))
              (mv-nth '0
                      (dir-ent-clusterchain fat32-in-memory dir-ent2)))))
   (equal (dir-ent-clusterchain
           (mv-nth 0
                   (clear-clusterchain fat32-in-memory
                                       (dir-ent-first-cluster dir-ent1)
                                       (dir-ent-file-size dir-ent1)))
           dir-ent2)
          (dir-ent-clusterchain fat32-in-memory dir-ent2)))
  :hints
  (("goal"
    :in-theory (e/d (dir-ent-clusterchain)
                    (dir-ent-clusterchain-of-clear-clusterchain))
    :use (:instance dir-ent-clusterchain-of-clear-clusterchain
                    (dir-ent dir-ent2)
                    (masked-current-cluster (dir-ent-first-cluster dir-ent1))
                    (length (dir-ent-file-size dir-ent1))))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-remove-file-coincident-lemma-3
  (implies
   (and
    (dir-ent-directory-p
     (mv-nth
      0
      (find-dir-ent
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       (car pathname))))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       entry-limit))
     0)
    (<=
     2
     (dir-ent-first-cluster
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents
           fat32-in-memory
           (mv-nth
            0
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth
               0
               (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
             (car pathname))))))
        (cadr pathname)))))
    (<
     (dir-ent-first-cluster
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents
           fat32-in-memory
           (mv-nth
            0
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth
               0
               (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
             (car pathname))))))
        (cadr pathname))))
     (+ 2 (count-of-clusters fat32-in-memory))))
   (equal
    (mv-nth
     '1
     (dir-ent-clusterchain-contents
      fat32-in-memory
      (mv-nth
       '0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth
          '0
          (dir-ent-clusterchain-contents
           fat32-in-memory
           (mv-nth
            '0
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth
               '0
               (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
             (car pathname))))))
        (car (cdr pathname))))))
    0))
  :hints
  (("goal"
    :in-theory
    (disable
     (:rewrite
      dir-ent-clusterchain-contents-of-lofat-remove-file-disjoint-lemma-4))
    :use
    (:instance
     (:rewrite
      dir-ent-clusterchain-contents-of-lofat-remove-file-disjoint-lemma-4)
     (filename (cadr pathname))
     (dir-ent-list
      (make-dir-ent-list
       (mv-nth
        0
        (dir-ent-clusterchain-contents
         fat32-in-memory
         (mv-nth
          0
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth 0
                    (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
           (car pathname)))))))
     (fat32-in-memory fat32-in-memory)))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-remove-file-coincident-lemma-7
  t
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (dir-ent-directory-p dir-ent)
          (not (intersectp-equal
                x
                (mv-nth 0
                        (dir-ent-clusterchain fat32-in-memory dir-ent)))))
     (not (member-equal (dir-ent-first-cluster dir-ent)
                        x)))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (disable intersectp-is-commutative)
      :expand
      ((:with intersectp-is-commutative
              (:free (y)
                     (intersectp-equal x
                                       (cons (dir-ent-first-cluster dir-ent)
                                             y))))
       (dir-ent-clusterchain fat32-in-memory dir-ent)
       (fat32-build-index-list (effective-fat fat32-in-memory)
                               (dir-ent-first-cluster dir-ent)
                               2097152 (cluster-size fat32-in-memory))
       (:free (y)
              (intersectp-equal (cons (dir-ent-first-cluster dir-ent) y)
                                x))))))
   (:rewrite
    :corollary
    (implies
     (and
      (dir-ent-directory-p dir-ent)
      (equal
       (fat32-entry-mask
        (nth
         (dir-ent-first-cluster dir-ent)
         (set-indices-in-fa-table
          (effective-fat fat32-in-memory)
          (mv-nth 0
                  (dir-ent-clusterchain fat32-in-memory dir-ent))
          (make-list-ac
           (len (mv-nth 0
                        (dir-ent-clusterchain fat32-in-memory dir-ent)))
           0 nil))))
       0)
      (non-free-index-listp x (effective-fat fat32-in-memory))
      (not (intersectp-equal
            x
            (mv-nth 0
                    (dir-ent-clusterchain fat32-in-memory dir-ent)))))
     (not (member-equal (dir-ent-first-cluster dir-ent)
                        x)))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (disable intersectp-is-commutative)
      :expand
      ((:with intersectp-is-commutative
              (:free (y)
                     (intersectp-equal x
                                       (cons (dir-ent-first-cluster dir-ent)
                                             y))))
       (dir-ent-clusterchain fat32-in-memory dir-ent)
       (fat32-build-index-list (effective-fat fat32-in-memory)
                               (dir-ent-first-cluster dir-ent)
                               2097152 (cluster-size fat32-in-memory))
       (:free (y)
              (intersectp-equal (cons (dir-ent-first-cluster dir-ent) y)
                                x))))))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-remove-file-coincident-lemma-8
  t
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (dir-ent-directory-p dir-ent)
          (< (dir-ent-first-cluster dir-ent)
             (+ 2 (count-of-clusters fat32-in-memory)))
          (non-free-index-listp x (effective-fat fat32-in-memory))
          (not (intersectp-equal
                x
                (mv-nth 0
                        (dir-ent-clusterchain fat32-in-memory dir-ent)))))
     (not
      (intersectp-equal
       (find-n-free-clusters
        (update-nth
         (dir-ent-first-cluster dir-ent)
         (fat32-update-lower-28 (fati (dir-ent-first-cluster dir-ent)
                                      fat32-in-memory)
                                *ms-end-of-clusterchain*)
         (set-indices-in-fa-table
          (effective-fat fat32-in-memory)
          (mv-nth 0
                  (dir-ent-clusterchain fat32-in-memory dir-ent))
          (make-list-ac
           (len (mv-nth 0
                        (dir-ent-clusterchain fat32-in-memory dir-ent)))
           0 nil)))
        (+ -1
           (len (make-clusters dir-contents
                               (cluster-size fat32-in-memory)))))
       x)))
    :hints
    (("goal"
      :use
      (:instance
       (:rewrite non-free-index-list-listp-correctness-1-lemma-1)
       (fa-table
        (update-nth
         (dir-ent-first-cluster dir-ent)
         (fat32-update-lower-28 (fati (dir-ent-first-cluster dir-ent)
                                      fat32-in-memory)
                                *ms-end-of-clusterchain*)
         (set-indices-in-fa-table
          (effective-fat fat32-in-memory)
          (mv-nth 0
                  (dir-ent-clusterchain fat32-in-memory dir-ent))
          (make-list-ac
           (len (mv-nth 0
                        (dir-ent-clusterchain fat32-in-memory dir-ent)))
           0 nil))))
       (index-list
        (find-n-free-clusters
         (update-nth
          (dir-ent-first-cluster dir-ent)
          (fat32-update-lower-28 (fati (dir-ent-first-cluster dir-ent)
                                       fat32-in-memory)
                                 *ms-end-of-clusterchain*)
          (set-indices-in-fa-table
           (effective-fat fat32-in-memory)
           (mv-nth 0
                   (dir-ent-clusterchain fat32-in-memory dir-ent))
           (make-list-ac
            (len (mv-nth 0
                         (dir-ent-clusterchain fat32-in-memory dir-ent)))
            0 nil)))
         (+ -1
            (len (make-clusters dir-contents
                                (cluster-size fat32-in-memory))))))))))
   (:rewrite
    :corollary
    (implies
     (and
      (< (dir-ent-first-cluster dir-ent)
         (+ 2 (count-of-clusters fat32-in-memory)))
      (equal
       (fat32-entry-mask
        (nth
         (dir-ent-first-cluster dir-ent)
         (set-indices-in-fa-table
          (effective-fat fat32-in-memory)
          (mv-nth 0
                  (dir-ent-clusterchain fat32-in-memory dir-ent))
          (make-list-ac
           (len (mv-nth 0
                        (dir-ent-clusterchain fat32-in-memory dir-ent)))
           0 nil))))
       0)
      (non-free-index-listp x (effective-fat fat32-in-memory))
      (not (intersectp-equal
            x
            (mv-nth 0
                    (dir-ent-clusterchain fat32-in-memory dir-ent)))))
     (not
      (intersectp-equal
       (find-n-free-clusters
        (update-nth
         (dir-ent-first-cluster dir-ent)
         (fat32-update-lower-28 (fati (dir-ent-first-cluster dir-ent)
                                      fat32-in-memory)
                                *ms-end-of-clusterchain*)
         (set-indices-in-fa-table
          (effective-fat fat32-in-memory)
          (mv-nth 0
                  (dir-ent-clusterchain fat32-in-memory dir-ent))
          (make-list-ac
           (len (mv-nth 0
                        (dir-ent-clusterchain fat32-in-memory dir-ent)))
           0 nil)))
        (+ -1
           (len (make-clusters dir-contents
                               (cluster-size fat32-in-memory)))))
       x)))
    :hints
    (("goal"
      :use
      (:instance
       (:rewrite non-free-index-list-listp-correctness-1-lemma-1)
       (fa-table
        (update-nth
         (dir-ent-first-cluster dir-ent)
         (fat32-update-lower-28 (fati (dir-ent-first-cluster dir-ent)
                                      fat32-in-memory)
                                *ms-end-of-clusterchain*)
         (set-indices-in-fa-table
          (effective-fat fat32-in-memory)
          (mv-nth 0
                  (dir-ent-clusterchain fat32-in-memory dir-ent))
          (make-list-ac
           (len (mv-nth 0
                        (dir-ent-clusterchain fat32-in-memory dir-ent)))
           0 nil))))
       (index-list
        (find-n-free-clusters
         (update-nth
          (dir-ent-first-cluster dir-ent)
          (fat32-update-lower-28 (fati (dir-ent-first-cluster dir-ent)
                                       fat32-in-memory)
                                 *ms-end-of-clusterchain*)
          (set-indices-in-fa-table
           (effective-fat fat32-in-memory)
           (mv-nth 0
                   (dir-ent-clusterchain fat32-in-memory dir-ent))
           (make-list-ac
            (len (mv-nth 0
                         (dir-ent-clusterchain fat32-in-memory dir-ent)))
            0 nil)))
         (+ -1
            (len (make-clusters dir-contents
                                (cluster-size fat32-in-memory))))))))))
   (:rewrite
    :corollary
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (dir-ent-directory-p dir-ent)
          (< (dir-ent-first-cluster dir-ent)
             (+ 2 (count-of-clusters fat32-in-memory)))
          (< 0 (len (explode dir-contents)))
          (non-free-index-listp x (effective-fat fat32-in-memory))
          (not (intersectp-equal
                x
                (mv-nth 0
                        (dir-ent-clusterchain fat32-in-memory dir-ent)))))
     (not
      (intersectp-equal
       (find-n-free-clusters
        (update-nth
         (dir-ent-first-cluster dir-ent)
         (fat32-update-lower-28 (fati (dir-ent-first-cluster dir-ent)
                                      fat32-in-memory)
                                *ms-end-of-clusterchain*)
         (effective-fat fat32-in-memory))
        (+ -1
           (len (make-clusters dir-contents
                               (cluster-size fat32-in-memory)))))
       x)))
    :hints
    (("goal"
      :use
      (:instance
       (:rewrite non-free-index-list-listp-correctness-1-lemma-1)
       (fa-table
        (update-nth
         (dir-ent-first-cluster dir-ent)
         (fat32-update-lower-28 (fati (dir-ent-first-cluster dir-ent)
                                      fat32-in-memory)
                                *ms-end-of-clusterchain*)
         (set-indices-in-fa-table
          (effective-fat fat32-in-memory)
          (mv-nth 0
                  (dir-ent-clusterchain fat32-in-memory dir-ent))
          (make-list-ac
           (len (mv-nth 0
                        (dir-ent-clusterchain fat32-in-memory dir-ent)))
           0 nil))))
       (index-list
        (find-n-free-clusters
         (update-nth
          (dir-ent-first-cluster dir-ent)
          (fat32-update-lower-28 (fati (dir-ent-first-cluster dir-ent)
                                       fat32-in-memory)
                                 *ms-end-of-clusterchain*)
          (set-indices-in-fa-table
           (effective-fat fat32-in-memory)
           (mv-nth 0
                   (dir-ent-clusterchain fat32-in-memory dir-ent))
           (make-list-ac
            (len (mv-nth 0
                         (dir-ent-clusterchain fat32-in-memory dir-ent)))
            0 nil)))
         (+ -1
            (len (make-clusters dir-contents
                                (cluster-size fat32-in-memory))))))))))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-remove-file-coincident-lemma-9
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (dir-ent-p dir-ent)
    (dir-ent-directory-p dir-ent)
    (<= *ms-first-data-cluster*
        (dir-ent-first-cluster dir-ent))
    (< (dir-ent-first-cluster dir-ent)
       (+ *ms-first-data-cluster*
          (count-of-clusters fat32-in-memory)))
    (equal
     (mv-nth
      1
      (update-dir-contents fat32-in-memory
                           (dir-ent-first-cluster dir-ent)
                           dir-contents))
     0)
    (stringp dir-contents)
    (< 0 (len (explode dir-contents)))
    (<= (len (explode dir-contents))
        *ms-max-dir-size*)
    (non-free-index-listp x (effective-fat fat32-in-memory))
    (not
     (intersectp-equal
      x
      (mv-nth '0
              (dir-ent-clusterchain fat32-in-memory dir-ent)))))
   (and
    (non-free-index-listp
     x
     (effective-fat
      (mv-nth
       0
       (update-dir-contents fat32-in-memory
                            (dir-ent-first-cluster dir-ent)
                            dir-contents))))
    (not
     (intersectp-equal
      x
      (mv-nth
       0
       (dir-ent-clusterchain
        (mv-nth
         0
         (update-dir-contents fat32-in-memory
                              (dir-ent-first-cluster dir-ent)
                              dir-contents))
        dir-ent))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (update-dir-contents)
                    (intersectp-is-commutative
                     (:definition non-free-index-listp)
                     (:definition stobj-set-clusters)))
    :expand
    ((:with
      intersectp-is-commutative
      (:free
       (y)
       (intersectp-equal x
                         (cons (dir-ent-first-cluster dir-ent)
                               y))))
     (:with
      intersectp-is-commutative
      (intersectp-equal
       (mv-nth '0
               (dir-ent-clusterchain fat32-in-memory dir-ent))
       x))
     (:free
      (y)
      (intersectp-equal (cons (dir-ent-first-cluster dir-ent) y)
                        x))))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-remove-file-coincident
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (dir-ent-p dir-ent)
    (dir-ent-directory-p dir-ent)
    (fat32-filename-list-p pathname)
    (equal (mv-nth 1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
           0)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory dir-ent))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       entry-limit))))
   (equal
    (dir-ent-clusterchain-contents
     (mv-nth 0
             (lofat-remove-file fat32-in-memory dir-ent pathname))
     dir-ent)
    (if
        (or
         (not
          (equal (mv-nth 1
                         (lofat-remove-file fat32-in-memory dir-ent pathname))
                 0))
         (consp (cdr pathname)))
        (dir-ent-clusterchain-contents fat32-in-memory dir-ent)
      (mv
       (implode
        (append
         (nats=>chars
          (clear-dir-ent
           (string=>nats
            (mv-nth 0
                    (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
           (car pathname)))
         (make-list-ac
          (+
           (-
            (len
             (explode
              (mv-nth
               0
               (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))))
           (*
            (cluster-size fat32-in-memory)
            (len
             (make-clusters
              (nats=>string
               (clear-dir-ent
                (string=>nats
                 (mv-nth
                  0
                  (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                (car pathname)))
              (cluster-size fat32-in-memory)))))
          (code-char 0)
          nil)))
       0))))
  :hints
  (("goal" :do-not-induct t
    :expand (lofat-remove-file fat32-in-memory dir-ent pathname))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    root-dir-ent-list-of-lofat-remove-file-coincident-lemma-1
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (equal (mod length (cluster-size fat32-in-memory))
                 0)
          (not (zp y))
          (equal (mod (cluster-size fat32-in-memory) y)
                 0))
     (equal
      (mod
       (len
        (explode
         (mv-nth 0
                 (get-clusterchain-contents fat32-in-memory
                                            masked-current-cluster length))))
       y)
      0))
    :hints
    (("goal" :induct (get-clusterchain-contents fat32-in-memory
                                                masked-current-cluster length)
      :in-theory (enable get-clusterchain-contents
                         (:rewrite mod-sum-cases))))))

(defthm
  root-dir-ent-list-of-lofat-remove-file-coincident-lemma-2
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (dir-ent-directory-p dir-ent)
        (not (zp y))
        (equal (mod (cluster-size fat32-in-memory) y)
               0))
   (equal
    (mod
     (len
      (explode
       (mv-nth 0
               (dir-ent-clusterchain-contents fat32-in-memory dir-ent))))
     y)
    0))
  :hints (("goal" :in-theory (enable dir-ent-clusterchain-contents))))

(defthm
  root-dir-ent-list-of-lofat-remove-file-coincident
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (fat32-filename-list-p pathname)
    (equal (mv-nth 1
                   (lofat-remove-file fat32-in-memory
                                      (pseudo-root-dir-ent fat32-in-memory)
                                      pathname))
           0)
    (equal (mv-nth 1 (lofat-to-hifat fat32-in-memory))
           0))
   (equal
    (root-dir-ent-list
     (mv-nth 0
             (lofat-remove-file fat32-in-memory
                                (pseudo-root-dir-ent fat32-in-memory)
                                pathname)))
    (if (consp (cdr pathname))
        (root-dir-ent-list fat32-in-memory)
        (mv (delete-dir-ent (mv-nth 0 (root-dir-ent-list fat32-in-memory))
                            (car pathname))
            0))))
  :hints (("goal" :in-theory (e/d (root-dir-ent-list lofat-to-hifat)
                                  ((:rewrite make-list-ac-removal)))
           :do-not-induct t)))

(defthm
  lofat-to-hifat-helper-of-delete-dir-ent-1
  (implies
   (and
    (useful-dir-ent-list-p dir-ent-list)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32-in-memory
                                          dir-ent-list entry-limit))
           0)
    (not-intersectp-list
     x
     (mv-nth 2
             (lofat-to-hifat-helper fat32-in-memory
                                    dir-ent-list entry-limit))))
   (not-intersectp-list
    x
    (mv-nth 2
            (lofat-to-hifat-helper fat32-in-memory
                                   (delete-dir-ent dir-ent-list filename)
                                   entry-limit))))
  :hints
  (("goal" :in-theory
    (e/d
     (lofat-to-hifat-helper lofat-to-hifat-helper-correctness-4
                            not-intersectp-list)
     ((:rewrite nth-of-effective-fat)
      (:definition assoc-equal)))
    :induct (lofat-to-hifat-helper fat32-in-memory
                                   dir-ent-list entry-limit))))

(defthm
  lofat-to-hifat-helper-of-delete-dir-ent-2
  (implies
   (and (useful-dir-ent-list-p dir-ent-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32-in-memory
                                              dir-ent-list entry-limit))
               0)
        (not (member-intersectp-equal
              x
              (mv-nth 2
                      (lofat-to-hifat-helper fat32-in-memory
                                             dir-ent-list entry-limit)))))
   (not
    (member-intersectp-equal
     x
     (mv-nth 2
             (lofat-to-hifat-helper fat32-in-memory
                                    (delete-dir-ent dir-ent-list filename)
                                    entry-limit)))))
  :hints
  (("goal"
    :in-theory (disable (:induction delete-dir-ent))
    :induct
    (member-intersectp-equal
     x
     (mv-nth 2
             (lofat-to-hifat-helper fat32-in-memory
                                    (delete-dir-ent dir-ent-list filename)
                                    entry-limit)))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (useful-dir-ent-list-p dir-ent-list)
          (equal (mv-nth 3
                         (lofat-to-hifat-helper fat32-in-memory
                                                dir-ent-list entry-limit))
                 0)
          (not (member-intersectp-equal
                x
                (mv-nth 2
                        (lofat-to-hifat-helper fat32-in-memory
                                               dir-ent-list entry-limit)))))
     (not
      (member-intersectp-equal
       (mv-nth 2
               (lofat-to-hifat-helper fat32-in-memory
                                      (delete-dir-ent dir-ent-list filename)
                                      entry-limit))
       x))))))

(defthm
  lofat-to-hifat-helper-of-delete-dir-ent-3
  (implies
   (and (useful-dir-ent-list-p dir-ent-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32-in-memory
                                              dir-ent-list entry-limit))
               0))
   (and
    (equal
     (mv-nth 0
             (lofat-to-hifat-helper fat32-in-memory
                                    (delete-dir-ent dir-ent-list filename)
                                    entry-limit))
     (remove-assoc-equal
      filename
      (mv-nth 0
              (lofat-to-hifat-helper fat32-in-memory
                                     dir-ent-list entry-limit))))
    (equal
     (mv-nth 3
             (lofat-to-hifat-helper fat32-in-memory
                                    (delete-dir-ent dir-ent-list filename)
                                    entry-limit))
     0)))
  :hints
  (("goal" :in-theory
    (e/d (lofat-to-hifat-helper lofat-to-hifat-helper-correctness-4)
         (nth-of-effective-fat))
    :induct (lofat-to-hifat-helper fat32-in-memory
                                   dir-ent-list entry-limit))))

(defthm
  dir-ent-clusterchain-of-lofat-remove-file-disjoint
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (<= *ms-first-data-cluster*
        (dir-ent-first-cluster root-dir-ent))
    (<= *ms-first-data-cluster*
        (dir-ent-first-cluster dir-ent))
    (< (dir-ent-first-cluster root-dir-ent)
       (+ *ms-first-data-cluster*
          (count-of-clusters fat32-in-memory)))
    (dir-ent-p root-dir-ent)
    (dir-ent-directory-p root-dir-ent)
    (dir-ent-p dir-ent)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory dir-ent))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit)))
    (not (intersectp-equal
          (mv-nth 0
                  (dir-ent-clusterchain fat32-in-memory root-dir-ent))
          (mv-nth 0
                  (dir-ent-clusterchain fat32-in-memory dir-ent))))
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory root-dir-ent))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit)))
    (equal (mv-nth 1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
           0))
   (equal
    (dir-ent-clusterchain
     (mv-nth 0
             (lofat-remove-file fat32-in-memory root-dir-ent pathname))
     dir-ent)
    (dir-ent-clusterchain fat32-in-memory dir-ent)))
  :hints (("goal" :induct (lofat-remove-file fat32-in-memory
                                             root-dir-ent pathname))))

(defthm
  lofat-to-hifat-helper-after-delete-and-clear-1-lemma-1
  (implies
   (and (useful-dir-ent-list-p dir-ent-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32-in-memory
                                              dir-ent-list entry-limit))
               0)
        (dir-ent-directory-p (mv-nth 0
                                     (find-dir-ent dir-ent-list filename))))
   (and
    (<= *ms-first-data-cluster*
        (dir-ent-first-cluster (mv-nth 0
                                       (find-dir-ent dir-ent-list filename))))
    (< (dir-ent-first-cluster (mv-nth 0 (find-dir-ent dir-ent-list filename)))
       (+ *ms-first-data-cluster*
          (count-of-clusters fat32-in-memory)))))
  :rule-classes :linear
  :hints (("goal" :in-theory (enable lofat-to-hifat-helper))))

(defthm
  lofat-to-hifat-helper-after-delete-and-clear-1-lemma-4
  (implies
   (and
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32-in-memory (cdr dir-ent-list)
                                          (+ -1 entry-limit)))
           0)
    (useful-dir-ent-list-p dir-ent-list)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
     (mv-nth 2
             (lofat-to-hifat-helper fat32-in-memory (cdr dir-ent-list)
                                    (+ -1 entry-limit))))
    (dir-ent-directory-p (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename))))
   (not
    (intersectp-equal
     (mv-nth '0
             (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
     (mv-nth
      '0
      (fat32-build-index-list
       (effective-fat fat32-in-memory)
       (dir-ent-first-cluster (mv-nth '0
                                      (find-dir-ent (cdr dir-ent-list)
                                                    filename)))
       '2097152
       (cluster-size fat32-in-memory))))))
  :hints (("goal" :in-theory (e/d (dir-ent-clusterchain)))))

(defthm
  lofat-to-hifat-helper-after-delete-and-clear-2-lemma-1
  (implies
   (and
    (dir-ent-directory-p (car dir-ent-list))
    (equal
     (mv-nth
      3
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
             (string=>nats (mv-nth 0
                                   (dir-ent-clusterchain-contents
                                    fat32-in-memory (car dir-ent-list)))))
            (+ -1 entry-limit))))))))
     0)
    (dir-ent-directory-p (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename)))
    (useful-dir-ent-list-p dir-ent-list)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
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
             (string=>nats (mv-nth 0
                                   (dir-ent-clusterchain-contents
                                    fat32-in-memory (car dir-ent-list)))))
            (+ -1 entry-limit))))))))))
   (not
    (intersectp-equal
     (mv-nth
      '0
      (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
     (mv-nth '0
             (fat32-build-index-list
              (effective-fat fat32-in-memory)
              (dir-ent-first-cluster
               (mv-nth '0
                       (find-dir-ent (cdr dir-ent-list)
                                     filename)))
              '2097152
              (cluster-size fat32-in-memory))))))
  :hints (("goal" :in-theory (enable dir-ent-clusterchain))))

;; remove-hyps says (for now) that these hypotheses are minimal.
(defthm
  lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2
  (implies
   (and
    (useful-dir-ent-list-p dir-ent-list)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32-in-memory
                                          dir-ent-list entry-limit))
           0)
    (< (dir-ent-first-cluster (mv-nth 0 (find-dir-ent dir-ent-list filename)))
       (+ *ms-first-data-cluster*
          (count-of-clusters fat32-in-memory)))
    (<= *ms-first-data-cluster*
        (dir-ent-first-cluster (mv-nth 0
                                       (find-dir-ent dir-ent-list filename))))
    (not (member-intersectp-equal
          (mv-nth 2
                  (lofat-to-hifat-helper fat32-in-memory
                                         dir-ent-list entry-limit))
          l)))
   (not-intersectp-list
    (mv-nth
     0
     (dir-ent-clusterchain fat32-in-memory
                           (mv-nth 0
                                   (find-dir-ent dir-ent-list filename))))
    l))
  :hints (("goal" :induct (lofat-to-hifat-helper fat32-in-memory
                                                 dir-ent-list entry-limit)
           :in-theory (e/d (lofat-to-hifat-helper)
                           (member-intersectp-is-commutative
                            (:rewrite nth-of-effective-fat)))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (useful-dir-ent-list-p dir-ent-list)
          (equal (mv-nth 3
                         (lofat-to-hifat-helper fat32-in-memory
                                                dir-ent-list entry-limit))
                 0)
          (not (member-intersectp-equal
                (mv-nth 2
                        (lofat-to-hifat-helper fat32-in-memory
                                               dir-ent-list entry-limit))
                l))
          (dir-ent-directory-p (mv-nth 0
                                       (find-dir-ent dir-ent-list filename))))
     (not-intersectp-list
      (mv-nth
       0
       (fat32-build-index-list
        (effective-fat fat32-in-memory)
        (dir-ent-first-cluster (mv-nth 0 (find-dir-ent dir-ent-list filename)))
        *ms-max-dir-size*
        (cluster-size fat32-in-memory)))
      l))
    :hints
    (("goal"
      :in-theory (e/d (dir-ent-clusterchain)))))
   (:rewrite
    :corollary
    (implies
     (and
      (useful-dir-ent-list-p dir-ent-list)
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32-in-memory
                                            dir-ent-list entry-limit))
             0)
      (< (dir-ent-first-cluster (mv-nth 0 (find-dir-ent dir-ent-list filename)))
         (+ *ms-first-data-cluster*
            (count-of-clusters fat32-in-memory)))
      (<= *ms-first-data-cluster*
          (dir-ent-first-cluster (mv-nth 0
                                         (find-dir-ent dir-ent-list filename))))
      (not (member-intersectp-equal
            (mv-nth 2
                    (lofat-to-hifat-helper fat32-in-memory
                                           dir-ent-list entry-limit))
            l))
      (not (dir-ent-directory-p (mv-nth 0
                                        (find-dir-ent dir-ent-list filename)))))
     (not-intersectp-list
      (mv-nth
       0
       (fat32-build-index-list
        (effective-fat fat32-in-memory)
        (dir-ent-first-cluster (mv-nth 0 (find-dir-ent dir-ent-list filename)))
        (dir-ent-file-size (mv-nth 0 (find-dir-ent dir-ent-list filename)))
        (cluster-size fat32-in-memory)))
      l))
    :hints
    (("goal"
      :in-theory (e/d (dir-ent-clusterchain)))))))

(defthm
  lofat-to-hifat-helper-after-delete-and-clear-2-lemma-3
  (implies
   (and
    (consp dir-ent-list)
    (dir-ent-directory-p (car dir-ent-list))
    (<= 2
        (dir-ent-first-cluster (car dir-ent-list)))
    (< (dir-ent-first-cluster (car dir-ent-list))
       (+ 2 (count-of-clusters fat32-in-memory)))
    (<=
     0
     (+
      -1 entry-limit
      (-
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (string=>nats (mv-nth 0
                                 (dir-ent-clusterchain-contents
                                  fat32-in-memory (car dir-ent-list)))))
          (+ -1 entry-limit)))))))
    (lofat-fs-p fat32-in-memory)
    (useful-dir-ent-list-p dir-ent-list)
    (equal
     (mv-nth
      3
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
             (string=>nats (mv-nth 0
                                   (dir-ent-clusterchain-contents
                                    fat32-in-memory (car dir-ent-list)))))
            (+ -1 entry-limit))))))))
     0)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
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
             (string=>nats (mv-nth 0
                                   (dir-ent-clusterchain-contents
                                    fat32-in-memory (car dir-ent-list)))))
            (+ -1 entry-limit)))))))))
    (not-intersectp-list
     x
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
             (string=>nats (mv-nth 0
                                   (dir-ent-clusterchain-contents
                                    fat32-in-memory (car dir-ent-list)))))
            (+ -1 entry-limit))))))))))
   (not-intersectp-list
    x
    (mv-nth
     2
     (lofat-to-hifat-helper
      (mv-nth 0
              (clear-clusterchain fat32-in-memory
                                  (dir-ent-first-cluster (car dir-ent-list))
                                  *ms-max-dir-size*))
      (cdr dir-ent-list)
      entry-limit))))
  :hints
  (("goal"
    :in-theory (enable dir-ent-clusterchain)
    :use
    (:instance
     (:rewrite lofat-to-hifat-helper-correctness-4)
     (entry-limit2 entry-limit)
     (dir-ent-list (cdr dir-ent-list))
     (entry-limit1
      (+
       -1 entry-limit
       (-
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32-in-memory
           (make-dir-ent-list
            (string=>nats (mv-nth 0
                                  (dir-ent-clusterchain-contents
                                   fat32-in-memory (car dir-ent-list)))))
           (+ -1 entry-limit)))))))))))

(defthm
  lofat-to-hifat-helper-after-delete-and-clear-1-lemma-2
  (implies
   (and
    (consp dir-ent-list)
    (dir-ent-directory-p (car dir-ent-list))
    (<= 2
        (dir-ent-first-cluster (car dir-ent-list)))
    (< (dir-ent-first-cluster (car dir-ent-list))
       (+ 2 (count-of-clusters fat32-in-memory)))
    (<=
     0
     (+
      -1 entry-limit
      (-
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (string=>nats (mv-nth 0
                                 (dir-ent-clusterchain-contents
                                  fat32-in-memory (car dir-ent-list)))))
          (+ -1 entry-limit)))))))
    (lofat-fs-p fat32-in-memory)
    (useful-dir-ent-list-p dir-ent-list)
    (equal
     (mv-nth
      3
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
             (string=>nats (mv-nth 0
                                   (dir-ent-clusterchain-contents
                                    fat32-in-memory (car dir-ent-list)))))
            (+ -1 entry-limit))))))))
     0)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
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
             (string=>nats (mv-nth 0
                                   (dir-ent-clusterchain-contents
                                    fat32-in-memory (car dir-ent-list)))))
            (+ -1 entry-limit))))))))))
   (equal
    (mv-nth
     0
     (lofat-to-hifat-helper
      (mv-nth 0
              (clear-clusterchain fat32-in-memory
                                  (dir-ent-first-cluster (car dir-ent-list))
                                  2097152))
      (cdr dir-ent-list)
      entry-limit))
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
            (string=>nats (mv-nth 0
                                  (dir-ent-clusterchain-contents
                                   fat32-in-memory (car dir-ent-list)))))
           (+ -1 entry-limit))))))))))
  :hints
  (("goal"
    :in-theory (enable dir-ent-clusterchain)
    :use
    (:instance
     (:rewrite lofat-to-hifat-helper-correctness-4)
     (entry-limit2 entry-limit)
     (dir-ent-list (cdr dir-ent-list))
     (entry-limit1
      (+
       -1 entry-limit
       (-
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32-in-memory
           (make-dir-ent-list
            (string=>nats (mv-nth 0
                                  (dir-ent-clusterchain-contents
                                   fat32-in-memory (car dir-ent-list)))))
           (+ -1 entry-limit)))))))))))

(defthm
  lofat-to-hifat-helper-after-delete-and-clear-1-lemma-3
  (implies
   (and
    (consp dir-ent-list)
    (dir-ent-directory-p (car dir-ent-list))
    (<= 2
        (dir-ent-first-cluster (car dir-ent-list)))
    (< (dir-ent-first-cluster (car dir-ent-list))
       (+ 2 (count-of-clusters fat32-in-memory)))
    (<=
     0
     (+
      -1 entry-limit
      (-
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (string=>nats (mv-nth 0
                                 (dir-ent-clusterchain-contents
                                  fat32-in-memory (car dir-ent-list)))))
          (+ -1 entry-limit)))))))
    (lofat-fs-p fat32-in-memory)
    (useful-dir-ent-list-p dir-ent-list)
    (equal
     (mv-nth
      3
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
             (string=>nats (mv-nth 0
                                   (dir-ent-clusterchain-contents
                                    fat32-in-memory (car dir-ent-list)))))
            (+ -1 entry-limit))))))))
     0)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
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
             (string=>nats (mv-nth 0
                                   (dir-ent-clusterchain-contents
                                    fat32-in-memory (car dir-ent-list)))))
            (+ -1 entry-limit))))))))))
   (equal
    (mv-nth
     3
     (lofat-to-hifat-helper
      (mv-nth 0
              (clear-clusterchain fat32-in-memory
                                  (dir-ent-first-cluster (car dir-ent-list))
                                  2097152))
      (cdr dir-ent-list)
      entry-limit))
    0))
  :hints
  (("goal"
    :in-theory (enable dir-ent-clusterchain)
    :use
    (:instance
     (:rewrite lofat-to-hifat-helper-correctness-4)
     (entry-limit2 entry-limit)
     (dir-ent-list (cdr dir-ent-list))
     (entry-limit1
      (+
       -1 entry-limit
       (-
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32-in-memory
           (make-dir-ent-list
            (string=>nats (mv-nth 0
                                  (dir-ent-clusterchain-contents
                                   fat32-in-memory (car dir-ent-list)))))
           (+ -1 entry-limit)))))))))))

(defthm
  lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-1
  (implies
   (and
    (not
     (member-intersectp-equal
      x
      (mv-nth
       2
       (lofat-to-hifat-helper fat32-in-memory
                              dir-ent-list entry-limit))))
    (equal
     (mv-nth 3
             (lofat-to-hifat-helper fat32-in-memory
                                    dir-ent-list entry-limit))
     0)
    (dir-ent-directory-p
     (mv-nth 0 (find-dir-ent dir-ent-list filename)))
    (useful-dir-ent-list-p dir-ent-list))
   (not
    (member-intersectp-equal
     x
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents
          fat32-in-memory
          (mv-nth 0
                  (find-dir-ent dir-ent-list filename)))))
       entry-limit)))))
  :hints
  (("goal" :in-theory (e/d (lofat-to-hifat-helper-correctness-4))
    :induct
    (member-intersectp-equal
     x
     (mv-nth
      2
      (lofat-to-hifat-helper fat32-in-memory
                             dir-ent-list entry-limit)))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and
      (not
       (member-intersectp-equal
        x
        (mv-nth
         2
         (lofat-to-hifat-helper fat32-in-memory
                                dir-ent-list entry-limit))))
      (equal
       (mv-nth 3
               (lofat-to-hifat-helper fat32-in-memory
                                      dir-ent-list entry-limit))
       0)
      (dir-ent-directory-p
       (mv-nth 0 (find-dir-ent dir-ent-list filename)))
      (useful-dir-ent-list-p dir-ent-list))
     (not
      (member-intersectp-equal
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32-in-memory
         (make-dir-ent-list
          (mv-nth
           0
           (get-clusterchain-contents
            fat32-in-memory
            (dir-ent-first-cluster
             (mv-nth 0 (find-dir-ent dir-ent-list filename)))
            *ms-max-dir-size*)))
         entry-limit)))))
    :hints
    (("goal"
      :in-theory (enable dir-ent-clusterchain-contents))))))

;; Slightly better than lofat-to-hifat-helper-of-update-dir-contents
(defthm
  lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-2
  (implies
   (and (useful-dir-ent-list-p dir-ent-list)
        (lofat-fs-p fat32-in-memory)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32-in-memory
                                              dir-ent-list entry-limit))
               0)
        (dir-ent-p root-dir-ent)
        (dir-ent-directory-p root-dir-ent)
        (<= *ms-first-data-cluster*
            (dir-ent-first-cluster root-dir-ent))
        (stringp dir-contents)
        (not-intersectp-list
         (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory root-dir-ent))
         (mv-nth 2
                 (lofat-to-hifat-helper fat32-in-memory
                                        dir-ent-list entry-limit))))
   (equal
    (lofat-to-hifat-helper
     (mv-nth 0
             (update-dir-contents fat32-in-memory
                                  (dir-ent-first-cluster root-dir-ent)
                                  dir-contents))
     dir-ent-list entry-limit)
    (lofat-to-hifat-helper fat32-in-memory
                           dir-ent-list entry-limit)))
  :hints
  (("goal"
    :in-theory (e/d (dir-ent-clusterchain)
                    (lofat-to-hifat-helper-of-update-dir-contents))
    :use (:instance lofat-to-hifat-helper-of-update-dir-contents
                    (first-cluster (dir-ent-first-cluster root-dir-ent))))))

;; Slightly better than lofat-to-hifat-helper-of-clear-clusterchain
(defthm
  lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-3
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (dir-ent-p dir-ent)
        (not (dir-ent-directory-p dir-ent))
        (<= *ms-first-data-cluster*
            (dir-ent-first-cluster dir-ent))
        (< (dir-ent-first-cluster dir-ent)
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory)))
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32-in-memory
                                              dir-ent-list entry-limit))
               0)
        (not-intersectp-list
         (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory dir-ent))
         (mv-nth 2
                 (lofat-to-hifat-helper fat32-in-memory
                                        dir-ent-list entry-limit))))
   (equal (lofat-to-hifat-helper
           (mv-nth 0
                   (clear-clusterchain fat32-in-memory
                                       (dir-ent-first-cluster dir-ent)
                                       (dir-ent-file-size dir-ent)))
           dir-ent-list entry-limit)
          (lofat-to-hifat-helper fat32-in-memory
                                 dir-ent-list entry-limit)))
  :hints
  (("goal"
    :in-theory (e/d (dir-ent-clusterchain)
                    (lofat-to-hifat-helper-of-clear-clusterchain))
    :use (:instance lofat-to-hifat-helper-of-clear-clusterchain
                    (masked-current-cluster (dir-ent-first-cluster dir-ent))
                    (length (dir-ent-file-size dir-ent))))))

;; Slightly better than lofat-to-hifat-helper-of-clear-clusterchain
(defthm
  lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-4
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (dir-ent-p dir-ent)
        (dir-ent-directory-p dir-ent)
        (<= *ms-first-data-cluster*
            (dir-ent-first-cluster dir-ent))
        (< (dir-ent-first-cluster dir-ent)
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory)))
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32-in-memory
                                              dir-ent-list entry-limit))
               0)
        (not-intersectp-list
         (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory dir-ent))
         (mv-nth 2
                 (lofat-to-hifat-helper fat32-in-memory
                                        dir-ent-list entry-limit))))
   (equal (lofat-to-hifat-helper
           (mv-nth 0
                   (clear-clusterchain fat32-in-memory
                                       (dir-ent-first-cluster dir-ent)
                                       *ms-max-dir-size*))
           dir-ent-list entry-limit)
          (lofat-to-hifat-helper fat32-in-memory
                                 dir-ent-list entry-limit)))
  :hints
  (("goal"
    :in-theory (e/d (dir-ent-clusterchain)
                    (lofat-to-hifat-helper-of-clear-clusterchain))
    :use (:instance lofat-to-hifat-helper-of-clear-clusterchain
                    (masked-current-cluster (dir-ent-first-cluster dir-ent))
                    (length *ms-max-dir-size*)))))

(defthm
  lofat-to-hifat-helper-of-lofat-remove-file-disjoint
  (implies
   (and
    (useful-dir-ent-list-p dir-ent-list)
    (lofat-fs-p fat32-in-memory)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32-in-memory
                                          dir-ent-list entry-limit1))
           0)
    (dir-ent-p root-dir-ent)
    (dir-ent-directory-p root-dir-ent)
    (>= (dir-ent-first-cluster root-dir-ent)
        *ms-first-data-cluster*)
    (< (dir-ent-first-cluster root-dir-ent)
       (+ *ms-first-data-cluster*
          (count-of-clusters fat32-in-memory)))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit2))
     0)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory root-dir-ent))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit2)))
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory root-dir-ent))
     (mv-nth 2
             (lofat-to-hifat-helper fat32-in-memory
                                    dir-ent-list entry-limit1)))
    (not
     (member-intersectp-equal
      (mv-nth
       2
       (lofat-to-hifat-helper
        fat32-in-memory
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
        entry-limit2))
      (mv-nth 2
              (lofat-to-hifat-helper fat32-in-memory
                                     dir-ent-list entry-limit1)))))
   (equal
    (lofat-to-hifat-helper
     (mv-nth 0
             (lofat-remove-file fat32-in-memory root-dir-ent pathname))
     dir-ent-list entry-limit1)
    (lofat-to-hifat-helper fat32-in-memory
                           dir-ent-list entry-limit1)))
  :hints (("goal" :induct (lofat-remove-file fat32-in-memory
                                             root-dir-ent pathname))))

(defthm
  no-duplicatesp-equal-of-fat32-build-index-list-of-effective-fat-of-update-dir-contents
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (fat32-masked-entry-p first-cluster)
    (stringp dir-contents)
    (< 0 (len (explode dir-contents)))
    (<= (len (explode dir-contents))
        *ms-max-dir-size*)
    (equal
     (mv-nth 1
             (get-clusterchain-contents fat32-in-memory
                                        first-cluster *ms-max-dir-size*))
     0)
    (equal (mv-nth 1
                   (update-dir-contents fat32-in-memory
                                        first-cluster dir-contents))
           0))
   (no-duplicatesp-equal
    (mv-nth
     0
     (fat32-build-index-list
      (effective-fat
       (mv-nth 0
               (update-dir-contents fat32-in-memory
                                    first-cluster dir-contents)))
      first-cluster *ms-max-dir-size*
      (cluster-size fat32-in-memory)))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (update-dir-contents
      get-clusterchain-contents-of-update-dir-contents-coincident-lemma-3)
     ((:rewrite nth-of-set-indices-in-fa-table-when-member)))
    :expand
    ((fat32-build-index-list (effective-fat fat32-in-memory)
                             first-cluster *ms-max-dir-size*
                             (cluster-size fat32-in-memory))
     (get-clusterchain-contents fat32-in-memory first-cluster 2097152))
    :use
    ((:instance
      (:rewrite nth-of-set-indices-in-fa-table-when-member)
      (val 0)
      (index-list
       (cons
        first-cluster
        (mv-nth 0
                (fat32-build-index-list
                 (effective-fat fat32-in-memory)
                 (fat32-entry-mask (fati first-cluster fat32-in-memory))
                 (+ 2097152
                    (- (cluster-size fat32-in-memory)))
                 (cluster-size fat32-in-memory)))))
      (fa-table (effective-fat fat32-in-memory))
      (n first-cluster))
     (:instance
      (:rewrite
       get-clusterchain-contents-of-update-dir-contents-coincident-lemma-2)
      (index-list
       (cons
        first-cluster
        (mv-nth 0
                (fat32-build-index-list
                 (effective-fat fat32-in-memory)
                 (fat32-entry-mask (fati first-cluster fat32-in-memory))
                 (+ 2097152
                    (- (cluster-size fat32-in-memory)))
                 (cluster-size fat32-in-memory)))))
      (fa-table (effective-fat fat32-in-memory)))))))

(defthm
  no-duplicatesp-equal-of-dir-ent-clusterchain-of-update-dir-contents-coincident
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (fat32-masked-entry-p first-cluster)
    (< 0 (len (explode dir-contents)))
    (<= (len (explode dir-contents))
        *ms-max-dir-size*)
    (equal (mv-nth 1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
           0)
    (equal (mv-nth 1
                   (update-dir-contents fat32-in-memory
                                        first-cluster dir-contents))
           0)
    (equal (dir-ent-first-cluster dir-ent)
           first-cluster)
    (dir-ent-directory-p dir-ent))
   (no-duplicatesp-equal
    (mv-nth 0
            (dir-ent-clusterchain
             (mv-nth 0
                     (update-dir-contents fat32-in-memory
                                          first-cluster dir-contents))
             dir-ent))))
  :hints
  (("goal"
    :in-theory (e/d (dir-ent-clusterchain dir-ent-clusterchain-contents)
                    (no-duplicatesp-equal-of-fat32-build-index-list-of-effective-fat-of-update-dir-contents))
    :use
    no-duplicatesp-equal-of-fat32-build-index-list-of-effective-fat-of-update-dir-contents)))

(defthm
  lofat-remove-file-correctness-1-lemma-8
  (implies
   (and (useful-dir-ent-list-p dir-ent-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32-in-memory
                                              dir-ent-list entry-limit))
               0)
        (dir-ent-directory-p (mv-nth 0
                                     (find-dir-ent dir-ent-list filename))))
   (not
    (member-intersectp-equal
     (mv-nth 2
             (lofat-to-hifat-helper fat32-in-memory
                                    (delete-dir-ent dir-ent-list filename)
                                    entry-limit))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents
                 fat32-in-memory
                 (mv-nth 0
                         (find-dir-ent dir-ent-list filename)))))
       entry-limit)))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lofat-to-hifat-helper lofat-to-hifat-helper-correctness-4
                            useful-dir-ent-list-p)
     (member-intersectp-is-commutative
      (:rewrite nth-of-effective-fat)
      (:rewrite
       dir-ent-clusterchain-contents-of-lofat-remove-file-disjoint-lemma-6)
      (:rewrite take-of-len-free)))
    :do-not-induct t
    :induct (mv (mv-nth 0
                        (lofat-to-hifat-helper fat32-in-memory
                                               dir-ent-list entry-limit))
                (mv-nth 0 (find-dir-ent dir-ent-list filename)))
    :expand
    ((:with
      member-intersectp-is-commutative
      (member-intersectp-equal
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
                       (dir-ent-clusterchain-contents
                        fat32-in-memory (car dir-ent-list))))
              (+ -1 entry-limit))))))))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32-in-memory
         (make-dir-ent-list (mv-nth 0
                                    (dir-ent-clusterchain-contents
                                     fat32-in-memory (car dir-ent-list))))
         (+ -1 entry-limit)))))))))

(defthm
  lofat-remove-file-correctness-1-lemma-18
  (implies
   (and (< (fat32-entry-mask (fati (dir-ent-first-cluster dir-ent)
                                   fat32-in-memory))
           (+ 2 (count-of-clusters fat32-in-memory)))
        (< (dir-ent-first-cluster dir-ent)
           (+ 2 (count-of-clusters fat32-in-memory))))
   (equal
    (fat32-entry-mask
     (nth
      (dir-ent-first-cluster dir-ent)
      (set-indices-in-fa-table
       (effective-fat fat32-in-memory)
       (cons
        (dir-ent-first-cluster dir-ent)
        (mv-nth '0
                (fat32-build-index-list
                 (effective-fat fat32-in-memory)
                 (fat32-entry-mask (fati (dir-ent-first-cluster dir-ent)
                                         fat32-in-memory))
                 (binary-+ '2097152
                           (binary-* '-1
                                     (cluster-size fat32-in-memory)))
                 (cluster-size fat32-in-memory))))
       (make-list-ac
        (len
         (mv-nth '0
                 (fat32-build-index-list
                  (effective-fat fat32-in-memory)
                  (fat32-entry-mask (fati (dir-ent-first-cluster dir-ent)
                                          fat32-in-memory))
                  (binary-+ '2097152
                            (binary-* '-1
                                      (cluster-size fat32-in-memory)))
                  (cluster-size fat32-in-memory))))
        '0
        '(0)))))
    '0))
  :hints
  (("goal"
    :in-theory (disable (:rewrite nth-of-set-indices-in-fa-table-when-member))
    :use
    ((:instance
      (:rewrite nth-of-set-indices-in-fa-table-when-member)
      (val 0)
      (index-list
       (cons
        (dir-ent-first-cluster dir-ent)
        (mv-nth 0
                (fat32-build-index-list
                 (effective-fat fat32-in-memory)
                 (fat32-entry-mask (fati (dir-ent-first-cluster dir-ent)
                                         fat32-in-memory))
                 (+ 2097152
                    (* -1 (cluster-size fat32-in-memory)))
                 (cluster-size fat32-in-memory)))))
      (fa-table (effective-fat fat32-in-memory))
      (n (dir-ent-first-cluster dir-ent)))))))

;; Kinda general.
(defthmd
  lofat-remove-file-correctness-1-lemma-23
  (implies
   (and
    (consp (cdr pathname))
    (lofat-fs-p fat32-in-memory)
    (<= 2 (dir-ent-first-cluster dir-ent))
    (dir-ent-p dir-ent)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth 0
                     (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
            (fat32-filename-fix (car pathname)))))))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory dir-ent))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth 0
                     (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
            (fat32-filename-fix (car pathname)))))))
       entry-limit)))
    (not
     (intersectp-equal
      (mv-nth
       0
       (dir-ent-clusterchain
        fat32-in-memory
        (mv-nth
         0
         (find-dir-ent
          (make-dir-ent-list
           (mv-nth 0
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
          (fat32-filename-fix (car pathname))))))
      (mv-nth 0
              (dir-ent-clusterchain fat32-in-memory dir-ent))))
    (not-intersectp-list
     (mv-nth
      0
      (dir-ent-clusterchain
       fat32-in-memory
       (mv-nth
        0
        (find-dir-ent
         (make-dir-ent-list
          (mv-nth 0
                  (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
         (fat32-filename-fix (car pathname))))))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth 0
                     (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
            (fat32-filename-fix (car pathname)))))))
       entry-limit)))
    (equal (mv-nth 1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
           0))
   (equal (dir-ent-clusterchain
           (mv-nth 0
                   (lofat-remove-file fat32-in-memory dir-ent pathname))
           dir-ent)
          (dir-ent-clusterchain fat32-in-memory dir-ent))))

;; The hypotheses are minimal.
(defthm
  lofat-remove-file-correctness-1-lemma-62
  (implies
   (and
    (useful-dir-ent-list-p dir-ent-list)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32-in-memory
                                          dir-ent-list entry-limit))
           0)
    (<= *ms-first-data-cluster*
        (dir-ent-first-cluster (mv-nth 0
                                       (find-dir-ent dir-ent-list filename))))
    (< (dir-ent-first-cluster (mv-nth 0 (find-dir-ent dir-ent-list filename)))
       (+ *ms-first-data-cluster*
          (count-of-clusters fat32-in-memory))))
   (not-intersectp-list
    (mv-nth
     '0
     (dir-ent-clusterchain fat32-in-memory
                           (mv-nth '0
                                   (find-dir-ent dir-ent-list filename))))
    (mv-nth '2
            (lofat-to-hifat-helper fat32-in-memory
                                   (delete-dir-ent dir-ent-list filename)
                                   entry-limit))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lofat-to-hifat-helper
      (:rewrite lofat-to-hifat-helper-correctness-4)
      not-intersectp-list)
     ((:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
      (:definition free-index-listp)
      (:rewrite nth-of-effective-fat)))
    :induct t
    :expand (:free (y) (intersectp-equal nil y)))))

(defthm
  lofat-remove-file-correctness-1-lemma-10
  (implies
   (and
    (<= 2
        (dir-ent-first-cluster (car dir-ent-list)))
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32-in-memory (cdr dir-ent-list)
                                          (+ -1 entry-limit)))
           0)
    (dir-ent-directory-p (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename)))
    (lofat-fs-p fat32-in-memory)
    (useful-dir-ent-list-p dir-ent-list)
    (equal
     (mv-nth
      1
      (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list)))
     0)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
     (mv-nth 2
             (lofat-to-hifat-helper fat32-in-memory (cdr dir-ent-list)
                                    (+ -1 entry-limit)))))
   (equal
    (dir-ent-clusterchain-contents
     (mv-nth 0
             (lofat-remove-file fat32-in-memory
                                (mv-nth 0
                                        (find-dir-ent (cdr dir-ent-list)
                                                      filename))
                                pathname))
     (car dir-ent-list))
    (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
  :hints
  (("goal"
    :in-theory
    (disable
     (:rewrite dir-ent-clusterchain-contents-of-lofat-remove-file-disjoint))
    :use
    (:instance
     (:rewrite dir-ent-clusterchain-contents-of-lofat-remove-file-disjoint)
     (dir-ent (car dir-ent-list))
     (root-dir-ent (mv-nth 0
                           (find-dir-ent (cdr dir-ent-list)
                                         filename)))
     (entry-limit (- entry-limit 1))))))

(defthm
  lofat-remove-file-correctness-1-lemma-11
  (implies
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit))))))))
     0)
    (dir-ent-directory-p (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename)))
    (lofat-fs-p fat32-in-memory)
    (useful-dir-ent-list-p dir-ent-list)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
       (+ -1 entry-limit)))
     0)
    (not
     (member-intersectp-equal
      (mv-nth
       2
       (lofat-to-hifat-helper
        fat32-in-memory
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
        (+ -1 entry-limit)))
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
                      (dir-ent-clusterchain-contents
                       fat32-in-memory (car dir-ent-list))))
             (+ -1 entry-limit)))))))))))
   (equal
    (lofat-to-hifat-helper
     (mv-nth 0
             (lofat-remove-file fat32-in-memory
                                (mv-nth 0
                                        (find-dir-ent (cdr dir-ent-list)
                                                      filename))
                                pathname))
     (make-dir-ent-list
      (mv-nth
       0
       (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
     (+ -1 entry-limit))
    (lofat-to-hifat-helper
     fat32-in-memory
     (make-dir-ent-list
      (mv-nth
       0
       (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
     (+ -1 entry-limit))))
  :hints
  (("goal"
    :in-theory
    (disable (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint))
    :use
    (:instance
     (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint)
     (entry-limit1 (+ -1 entry-limit))
     (dir-ent-list
      (make-dir-ent-list
       (mv-nth
        0
        (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list)))))
     (pathname pathname)
     (root-dir-ent (mv-nth 0
                           (find-dir-ent (cdr dir-ent-list)
                                         filename)))
     (entry-limit2
      (+
       -1 entry-limit
       (-
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  (make-dir-ent-list
                   (mv-nth 0
                           (dir-ent-clusterchain-contents
                            fat32-in-memory (car dir-ent-list))))
                  (+ -1 entry-limit)))))))))))

(defthm
  lofat-remove-file-correctness-1-lemma-12
  (implies
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit))))))))
     0)
    (dir-ent-directory-p (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename)))
    (lofat-fs-p fat32-in-memory)
    (useful-dir-ent-list-p dir-ent-list)
    (fat32-filename-list-p pathname)
    (equal (mv-nth 1
                   (lofat-remove-file fat32-in-memory
                                      (mv-nth 0
                                              (find-dir-ent (cdr dir-ent-list)
                                                            filename))
                                      pathname))
           0))
   (equal
    (dir-ent-clusterchain-contents
     (mv-nth 0
             (lofat-remove-file fat32-in-memory
                                (mv-nth 0
                                        (find-dir-ent (cdr dir-ent-list)
                                                      filename))
                                pathname))
     (mv-nth 0
             (find-dir-ent (cdr dir-ent-list)
                           filename)))
    (if
        (consp (cdr pathname))
        (dir-ent-clusterchain-contents fat32-in-memory
                                       (mv-nth 0
                                               (find-dir-ent (cdr dir-ent-list)
                                                             filename)))
      (mv
       (implode
        (append
         (nats=>chars
          (clear-dir-ent
           (string=>nats (mv-nth 0
                                 (dir-ent-clusterchain-contents
                                  fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename)))))
           (car pathname)))
         (make-list-ac
          (+
           (-
            (len (explode (mv-nth 0
                                  (dir-ent-clusterchain-contents
                                   fat32-in-memory
                                   (mv-nth 0
                                           (find-dir-ent (cdr dir-ent-list)
                                                         filename)))))))
           (*
            (cluster-size fat32-in-memory)
            (len
             (make-clusters
              (nats=>string
               (clear-dir-ent
                (string=>nats
                 (mv-nth 0
                         (dir-ent-clusterchain-contents
                          fat32-in-memory
                          (mv-nth 0
                                  (find-dir-ent (cdr dir-ent-list)
                                                filename)))))
                (car pathname)))
              (cluster-size fat32-in-memory)))))
          (code-char 0) nil)))
       0))))
  :hints
  (("goal"
    :in-theory
    (disable
     (:rewrite dir-ent-clusterchain-contents-of-lofat-remove-file-coincident))
    :use
    (:instance
     (:rewrite dir-ent-clusterchain-contents-of-lofat-remove-file-coincident)
     (pathname pathname)
     (dir-ent (mv-nth 0
                      (find-dir-ent (cdr dir-ent-list)
                                    filename)))
     (entry-limit
      (+
       -1 entry-limit
       (-
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  (make-dir-ent-list
                   (mv-nth 0
                           (dir-ent-clusterchain-contents
                            fat32-in-memory (car dir-ent-list))))
                  (+ -1 entry-limit)))))))))))

;; Hypotheses are minimal.
(defthm
  lofat-remove-file-correctness-1-lemma-13
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit))
     0)
    (fat32-filename-list-p pathname)
    (dir-ent-directory-p
     (mv-nth
      0
      (find-dir-ent
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       (car pathname)))))
   (equal
    (dir-ent-clusterchain-contents
     (mv-nth
      0
      (lofat-remove-file
       fat32-in-memory
       (mv-nth
        0
        (find-dir-ent
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
         (car pathname)))
       (cdr pathname)))
     (mv-nth
      0
      (find-dir-ent
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       (car pathname))))
    (if
     (or
      (not
       (equal
        (mv-nth
         1
         (lofat-remove-file
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              0
              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
            (car pathname)))
          (cdr pathname)))
        0))
      (consp (cddr pathname)))
     (dir-ent-clusterchain-contents
      fat32-in-memory
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
        (car pathname))))
     (mv
      (implode
       (append
        (nats=>chars
         (clear-dir-ent
          (string=>nats
           (mv-nth
            0
            (dir-ent-clusterchain-contents
             fat32-in-memory
             (mv-nth
              0
              (find-dir-ent
               (make-dir-ent-list (mv-nth 0
                                          (dir-ent-clusterchain-contents
                                           fat32-in-memory root-dir-ent)))
               (car pathname))))))
          (cadr pathname)))
        (make-list-ac
         (+
          (-
           (len
            (explode
             (mv-nth
              0
              (dir-ent-clusterchain-contents
               fat32-in-memory
               (mv-nth 0
                       (find-dir-ent
                        (make-dir-ent-list
                         (mv-nth 0
                                 (dir-ent-clusterchain-contents
                                  fat32-in-memory root-dir-ent)))
                        (car pathname))))))))
          (*
           (cluster-size fat32-in-memory)
           (len
            (make-clusters
             (nats=>string
              (clear-dir-ent
               (string=>nats
                (mv-nth
                 0
                 (dir-ent-clusterchain-contents
                  fat32-in-memory
                  (mv-nth
                   0
                   (find-dir-ent
                    (make-dir-ent-list
                     (mv-nth 0
                             (dir-ent-clusterchain-contents
                              fat32-in-memory root-dir-ent)))
                    (car pathname))))))
               (cadr pathname)))
             (cluster-size fat32-in-memory)))))
         (code-char 0)
         nil)))
      0))))
  :hints
  (("goal"
    :in-theory
    (disable
     (:rewrite dir-ent-clusterchain-contents-of-lofat-remove-file-coincident))
    :use
    (:instance
     (:rewrite dir-ent-clusterchain-contents-of-lofat-remove-file-coincident)
     (pathname (cdr pathname))
     (dir-ent
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
        (car pathname))))))))

(defthm
  lofat-remove-file-correctness-1-lemma-14
  (implies
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit))))))))
     0)
    (dir-ent-directory-p (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename1)))
    (equal
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth
        0
        (update-dir-contents
         fat32-in-memory
         (dir-ent-first-cluster (mv-nth 0
                                        (find-dir-ent (cdr dir-ent-list)
                                                      filename1)))
         (nats=>string
          (clear-dir-ent
           (string=>nats (mv-nth 0
                                 (dir-ent-clusterchain-contents
                                  fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename1)))))
           filename2))))
       (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit))))))))
     (put-assoc-equal
      filename1
      (m1-file
       (mv-nth 0
               (find-dir-ent (cdr dir-ent-list)
                             filename1))
       (remove-assoc-equal
        filename2
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (mv-nth 0
                   (dir-ent-clusterchain-contents
                    fat32-in-memory
                    (mv-nth 0
                            (find-dir-ent (cdr dir-ent-list)
                                          filename1)))))
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
                        (dir-ent-clusterchain-contents
                         fat32-in-memory (car dir-ent-list))))
               (+ -1 entry-limit))))))))))
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
                      (dir-ent-clusterchain-contents
                       fat32-in-memory (car dir-ent-list))))
             (+ -1 entry-limit))))))))))
    (useful-dir-ent-list-p dir-ent-list))
   (equal
    (mv-nth
     0
     (lofat-to-hifat-helper
      (mv-nth
       0
       (update-dir-contents
        fat32-in-memory
        (dir-ent-first-cluster (mv-nth 0
                                       (find-dir-ent (cdr dir-ent-list)
                                                     filename1)))
        (nats=>string
         (clear-dir-ent
          (string=>nats (mv-nth 0
                                (dir-ent-clusterchain-contents
                                 fat32-in-memory
                                 (mv-nth 0
                                         (find-dir-ent (cdr dir-ent-list)
                                                       filename1)))))
          filename2))))
      (cdr dir-ent-list)
      (+
       -1 entry-limit
       (-
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  (make-dir-ent-list
                   (mv-nth 0
                           (dir-ent-clusterchain-contents
                            fat32-in-memory (car dir-ent-list))))
                  (+ -1 entry-limit))))))))
    (put-assoc-equal
     filename1
     (m1-file
      (mv-nth 0
              (find-dir-ent (cdr dir-ent-list)
                            filename1))
      (remove-assoc-equal
       filename2
       (mv-nth 0
               (lofat-to-hifat-helper
                fat32-in-memory
                (make-dir-ent-list
                 (mv-nth 0
                         (dir-ent-clusterchain-contents
                          fat32-in-memory
                          (mv-nth 0
                                  (find-dir-ent (cdr dir-ent-list)
                                                filename1)))))
                entry-limit))))
     (mv-nth
      0
      (lofat-to-hifat-helper
       fat32-in-memory (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))))))
  :hints
  (("goal"
    :use
    (:instance
     (:rewrite lofat-to-hifat-helper-correctness-4)
     (entry-limit1
      (+
       -1 entry-limit
       (-
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  (make-dir-ent-list
                   (mv-nth 0
                           (dir-ent-clusterchain-contents
                            fat32-in-memory (car dir-ent-list))))
                  (+ -1 entry-limit)))))))
     (entry-limit2 entry-limit)
     (dir-ent-list (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory
                             (mv-nth 0
                                     (find-dir-ent (cdr dir-ent-list)
                                                   filename1))))))))))

(defthm
  lofat-remove-file-correctness-1-lemma-15
  (implies
   (and
    (consp dir-ent-list)
    (not (zp entry-limit))
    (<= 2
        (dir-ent-first-cluster (car dir-ent-list)))
    (dir-ent-directory-p (car dir-ent-list))
    (lofat-fs-p fat32-in-memory)
    (useful-dir-ent-list-p dir-ent-list)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
       (+ -1 entry-limit)))
     0)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit))))))))
     0)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))))
    (equal
     (mv-nth
      1
      (find-dir-ent
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
       filename2))
     0))
   (equal
    (mv-nth
     0
     (lofat-to-hifat-helper
      (mv-nth
       0
       (update-dir-contents
        fat32-in-memory
        (dir-ent-first-cluster (car dir-ent-list))
        (nats=>string
         (clear-dir-ent
          (string=>nats (mv-nth 0
                                (dir-ent-clusterchain-contents
                                 fat32-in-memory (car dir-ent-list))))
          filename2))))
      (cdr dir-ent-list)
      (+
       -1 entry-limit
       (-
        (hifat-entry-count
         (remove-assoc-equal
          filename2
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))))
    (mv-nth
     0
     (lofat-to-hifat-helper
      fat32-in-memory (cdr dir-ent-list)
      (+
       -1 entry-limit
       (-
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  (make-dir-ent-list
                   (mv-nth 0
                           (dir-ent-clusterchain-contents
                            fat32-in-memory (car dir-ent-list))))
                  (+ -1 entry-limit))))))))))
  :hints
  (("goal"
    :use
    ((:instance
      (:rewrite lofat-to-hifat-helper-correctness-4)
      (entry-limit2
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (remove-assoc-equal
           filename2
           (mv-nth
            0
            (lofat-to-hifat-helper
             fat32-in-memory
             (make-dir-ent-list
              (mv-nth 0
                      (dir-ent-clusterchain-contents
                       fat32-in-memory (car dir-ent-list))))
             (+ -1 entry-limit))))))))
      (entry-limit1
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))
      (dir-ent-list (cdr dir-ent-list))
      (fat32-in-memory fat32-in-memory))
     (:instance
      (:linear lofat-to-hifat-helper-correctness-3)
      (entry-limit
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))
      (dir-ent-list (cdr dir-ent-list))
      (fat32-in-memory fat32-in-memory))))))

(defthm
  lofat-remove-file-correctness-1-lemma-16
  (implies
   (and
    (syntaxp (variablep entry-limit))
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32-in-memory (cdr dir-ent-list)
                                          (+ -1 entry-limit)))
           0)
    (dir-ent-directory-p (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename1)))
    (<= 2
        (dir-ent-first-cluster (mv-nth 0
                                       (find-dir-ent (cdr dir-ent-list)
                                                     filename1))))
    (equal
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth
        0
        (update-dir-contents
         fat32-in-memory
         (dir-ent-first-cluster (mv-nth 0
                                        (find-dir-ent (cdr dir-ent-list)
                                                      filename1)))
         (nats=>string
          (clear-dir-ent
           (string=>nats (mv-nth 0
                                 (dir-ent-clusterchain-contents
                                  fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename1)))))
           filename2))))
       (cdr dir-ent-list)
       (+ -1 entry-limit)))
     (put-assoc-equal
      filename1
      (m1-file
       (mv-nth 0
               (find-dir-ent (cdr dir-ent-list)
                             filename1))
       (remove-assoc-equal
        filename2
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (mv-nth 0
                   (dir-ent-clusterchain-contents
                    fat32-in-memory
                    (mv-nth 0
                            (find-dir-ent (cdr dir-ent-list)
                                          filename1)))))
          (+ -1 entry-limit)))))
      (mv-nth 0
              (lofat-to-hifat-helper fat32-in-memory (cdr dir-ent-list)
                                     (+ -1 entry-limit)))))
    (useful-dir-ent-list-p dir-ent-list))
   (equal
    (mv-nth
     0
     (lofat-to-hifat-helper
      (mv-nth
       0
       (update-dir-contents
        fat32-in-memory
        (dir-ent-first-cluster (mv-nth 0
                                       (find-dir-ent (cdr dir-ent-list)
                                                     filename1)))
        (nats=>string
         (clear-dir-ent
          (string=>nats (mv-nth 0
                                (dir-ent-clusterchain-contents
                                 fat32-in-memory
                                 (mv-nth 0
                                         (find-dir-ent (cdr dir-ent-list)
                                                       filename1)))))
          filename2))))
      (cdr dir-ent-list)
      (+ -1 entry-limit)))
    (put-assoc-equal
     filename1
     (m1-file
      (mv-nth 0
              (find-dir-ent (cdr dir-ent-list)
                            filename1))
      (remove-assoc-equal
       filename2
       (mv-nth 0
               (lofat-to-hifat-helper
                fat32-in-memory
                (make-dir-ent-list
                 (mv-nth 0
                         (dir-ent-clusterchain-contents
                          fat32-in-memory
                          (mv-nth 0
                                  (find-dir-ent (cdr dir-ent-list)
                                                filename1)))))
                entry-limit))))
     (mv-nth 0
             (lofat-to-hifat-helper fat32-in-memory (cdr dir-ent-list)
                                    (+ -1 entry-limit))))))
  :hints
  (("goal"
    :in-theory (enable dir-ent-clusterchain-contents-of-lofat-remove-file-disjoint-lemma-8)
    :use
    (:instance
     (:rewrite lofat-to-hifat-helper-correctness-4)
     (entry-limit1 (- entry-limit 1))
     (entry-limit2 entry-limit)
     (dir-ent-list
      (make-dir-ent-list (mv-nth 0
                                 (dir-ent-clusterchain-contents
                                  fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename1))))))
     (fat32-in-memory fat32-in-memory)))))

(defthm
  lofat-remove-file-correctness-1-lemma-17
  (implies
   (and
    (syntaxp (variablep entry-limit))
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32-in-memory (cdr dir-ent-list)
                                          (+ -1 entry-limit)))
           0)
    (dir-ent-directory-p (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename1)))
    (<= 2
        (dir-ent-first-cluster (mv-nth 0
                                       (find-dir-ent (cdr dir-ent-list)
                                                     filename1))))
    (useful-dir-ent-list-p dir-ent-list))
   (equal
    (put-assoc-equal
     filename1
     (m1-file
      (mv-nth 0
              (find-dir-ent (cdr dir-ent-list)
                            filename1))
      (remove-assoc-equal
       filename2
       (mv-nth 0
               (lofat-to-hifat-helper
                fat32-in-memory
                (make-dir-ent-list
                 (mv-nth 0
                         (dir-ent-clusterchain-contents
                          fat32-in-memory
                          (mv-nth 0
                                  (find-dir-ent (cdr dir-ent-list)
                                                filename1)))))
                (+ -1 entry-limit)))))
     (mv-nth 0
             (lofat-to-hifat-helper fat32-in-memory (cdr dir-ent-list)
                                    (+ -1 entry-limit))))
    (put-assoc-equal
     filename1
     (m1-file
      (mv-nth 0
              (find-dir-ent (cdr dir-ent-list)
                            filename1))
      (remove-assoc-equal
       filename2
       (mv-nth 0
               (lofat-to-hifat-helper
                fat32-in-memory
                (make-dir-ent-list
                 (mv-nth 0
                         (dir-ent-clusterchain-contents
                          fat32-in-memory
                          (mv-nth 0
                                  (find-dir-ent (cdr dir-ent-list)
                                                filename1)))))
                entry-limit))))
     (mv-nth 0
             (lofat-to-hifat-helper fat32-in-memory (cdr dir-ent-list)
                                    (+ -1 entry-limit))))))
  :hints
  (("goal"
    :in-theory (enable dir-ent-clusterchain-contents-of-lofat-remove-file-disjoint-lemma-8)
    :use
    (:instance
     (:rewrite lofat-to-hifat-helper-correctness-4)
     (entry-limit1 (- entry-limit 1))
     (entry-limit2 entry-limit)
     (dir-ent-list
      (make-dir-ent-list (mv-nth 0
                                 (dir-ent-clusterchain-contents
                                  fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename1))))))
     (fat32-in-memory fat32-in-memory)))))

(defthm
  lofat-remove-file-correctness-1-lemma-19
  (implies
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit))))))))
     0)
    (dir-ent-directory-p (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename1)))
    (useful-dir-ent-list-p dir-ent-list))
   (equal
    (put-assoc-equal
     filename1
     (m1-file
      (mv-nth 0
              (find-dir-ent (cdr dir-ent-list)
                            filename1))
      (remove-assoc-equal
       filename2
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32-in-memory
         (make-dir-ent-list
          (mv-nth 0
                  (dir-ent-clusterchain-contents
                   fat32-in-memory
                   (mv-nth 0
                           (find-dir-ent (cdr dir-ent-list)
                                         filename1)))))
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
                       (dir-ent-clusterchain-contents
                        fat32-in-memory (car dir-ent-list))))
              (+ -1 entry-limit))))))))))
     (mv-nth
      0
      (lofat-to-hifat-helper
       fat32-in-memory (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))))
    (put-assoc-equal
     filename1
     (m1-file
      (mv-nth 0
              (find-dir-ent (cdr dir-ent-list)
                            filename1))
      (remove-assoc-equal
       filename2
       (mv-nth 0
               (lofat-to-hifat-helper
                fat32-in-memory
                (make-dir-ent-list
                 (mv-nth 0
                         (dir-ent-clusterchain-contents
                          fat32-in-memory
                          (mv-nth 0
                                  (find-dir-ent (cdr dir-ent-list)
                                                filename1)))))
                entry-limit))))
     (mv-nth
      0
      (lofat-to-hifat-helper
       fat32-in-memory (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))))))
  :hints
  (("goal"
    :use
    (:instance
     (:rewrite lofat-to-hifat-helper-correctness-4)
     (entry-limit1
      (+
       -1 entry-limit
       (-
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  (make-dir-ent-list
                   (mv-nth 0
                           (dir-ent-clusterchain-contents
                            fat32-in-memory (car dir-ent-list))))
                  (+ -1 entry-limit)))))))
     (entry-limit2 entry-limit)
     (dir-ent-list
      (make-dir-ent-list (mv-nth 0
                                 (dir-ent-clusterchain-contents
                                  fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename1))))))
     (fat32-in-memory fat32-in-memory)))))

(defthm
  lofat-remove-file-correctness-1-lemma-20
  (implies
   (and
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32-in-memory (cdr dir-ent-list)
                                          (+ -1 entry-limit)))
           0)
    (dir-ent-directory-p (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename1)))
    (<=
     2
     (dir-ent-first-cluster
      (mv-nth 0
              (find-dir-ent
               (make-dir-ent-list
                (mv-nth 0
                        (dir-ent-clusterchain-contents
                         fat32-in-memory
                         (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename1)))))
               filename2))))
    (<
     (dir-ent-first-cluster
      (mv-nth 0
              (find-dir-ent
               (make-dir-ent-list
                (mv-nth 0
                        (dir-ent-clusterchain-contents
                         fat32-in-memory
                         (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename1)))))
               filename2)))
     (+ 2 (count-of-clusters fat32-in-memory)))
    (useful-dir-ent-list-p dir-ent-list)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
     (mv-nth 2
             (lofat-to-hifat-helper fat32-in-memory (cdr dir-ent-list)
                                    (+ -1 entry-limit)))))
   (not
    (intersectp-equal
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
     (mv-nth
      0
      (dir-ent-clusterchain
       fat32-in-memory
       (mv-nth 0
               (find-dir-ent
                (make-dir-ent-list
                 (mv-nth 0
                         (dir-ent-clusterchain-contents
                          fat32-in-memory
                          (mv-nth 0
                                  (find-dir-ent (cdr dir-ent-list)
                                                filename1)))))
                filename2)))))))
  :hints
  (("goal"
    :use
    ((:instance
      (:rewrite
       get-clusterchain-contents-of-lofat-remove-file-coincident-lemma-5
       . 1)
      (entry-limit (- entry-limit 1))
      (filename filename2)
      (dir-ent-list (make-dir-ent-list
                     (mv-nth 0
                             (dir-ent-clusterchain-contents
                              fat32-in-memory
                              (mv-nth 0
                                      (find-dir-ent (cdr dir-ent-list)
                                                    filename1))))))
      (fat32-in-memory fat32-in-memory)
      (x (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory
                                       (car dir-ent-list)))))))))

(defthm
  lofat-remove-file-correctness-1-lemma-21
  (implies
   (and
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32-in-memory (cdr dir-ent-list)
                                          (+ -1 entry-limit)))
           0)
    (dir-ent-directory-p (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename1)))
    (<=
     2
     (dir-ent-first-cluster
      (mv-nth 0
              (find-dir-ent
               (make-dir-ent-list
                (mv-nth 0
                        (dir-ent-clusterchain-contents
                         fat32-in-memory
                         (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename1)))))
               filename2))))
    (<
     (dir-ent-first-cluster
      (mv-nth 0
              (find-dir-ent
               (make-dir-ent-list
                (mv-nth 0
                        (dir-ent-clusterchain-contents
                         fat32-in-memory
                         (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename1)))))
               filename2)))
     (+ 2 (count-of-clusters fat32-in-memory)))
    (useful-dir-ent-list-p dir-ent-list))
   (not
    (intersectp-equal
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory
                                   (mv-nth 0
                                           (find-dir-ent (cdr dir-ent-list)
                                                         filename1))))
     (mv-nth
      0
      (dir-ent-clusterchain
       fat32-in-memory
       (mv-nth 0
               (find-dir-ent
                (make-dir-ent-list
                 (mv-nth 0
                         (dir-ent-clusterchain-contents
                          fat32-in-memory
                          (mv-nth 0
                                  (find-dir-ent (cdr dir-ent-list)
                                                filename1)))))
                filename2)))))))
  :hints
  (("goal"
    :in-theory
    (disable
     (:rewrite
      get-clusterchain-contents-of-lofat-remove-file-coincident-lemma-5
      . 1))
    :use
    (:instance
     (:rewrite
      get-clusterchain-contents-of-lofat-remove-file-coincident-lemma-5
      . 1)
     (entry-limit (- entry-limit 1))
     (filename filename2)
     (dir-ent-list
      (make-dir-ent-list (mv-nth 0
                                 (dir-ent-clusterchain-contents
                                  fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename1))))))
     (fat32-in-memory fat32-in-memory)
     (x (mv-nth 0
                (dir-ent-clusterchain fat32-in-memory
                                      (mv-nth 0
                                              (find-dir-ent (cdr dir-ent-list)
                                                            filename1)))))))))

(defthm
  lofat-remove-file-correctness-1-lemma-24
  (implies
   (and
    (not (zp entry-limit))
    (useful-dir-ent-list-p dir-ent-list)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
       (+ -1 entry-limit)))
     0)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit))))))))
     0)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))))
    (equal
     (mv-nth
      1
      (find-dir-ent
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
       filename2))
     0))
   (not-intersectp-list
    (mv-nth 0
            (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
    (mv-nth
     2
     (lofat-to-hifat-helper
      fat32-in-memory (cdr dir-ent-list)
      (+
       -1 entry-limit
       (-
        (hifat-entry-count
         (remove-assoc-equal
          filename2
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))))))
  :hints
  (("goal"
    :in-theory
    (disable (:linear lofat-to-hifat-helper-correctness-3)
             (:rewrite lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2
                       . 1))
    :use
    ((:instance
      (:rewrite lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2
                . 1)
      (entry-limit (+ -1 entry-limit))
      (l
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32-in-memory (cdr dir-ent-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (remove-assoc-equal
             filename2
             (mv-nth
              0
              (lofat-to-hifat-helper
               fat32-in-memory
               (make-dir-ent-list
                (mv-nth 0
                        (dir-ent-clusterchain-contents
                         fat32-in-memory (car dir-ent-list))))
               (+ -1 entry-limit))))))))))
      (filename filename2)
      (dir-ent-list
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list)))))
      (fat32-in-memory fat32-in-memory))
     (:instance
      (:rewrite lofat-to-hifat-helper-correctness-4)
      (entry-limit1
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))
      (entry-limit2
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (remove-assoc-equal
           filename2
           (mv-nth
            0
            (lofat-to-hifat-helper
             fat32-in-memory
             (make-dir-ent-list
              (mv-nth 0
                      (dir-ent-clusterchain-contents
                       fat32-in-memory (car dir-ent-list))))
             (+ -1 entry-limit))))))))
      (dir-ent-list (cdr dir-ent-list))
      (fat32-in-memory fat32-in-memory))
     (:instance
      (:linear lofat-to-hifat-helper-correctness-3)
      (entry-limit
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))
      (dir-ent-list (cdr dir-ent-list))
      (fat32-in-memory fat32-in-memory))))))

(defthm
  lofat-remove-file-correctness-1-lemma-25
  (implies
   (and
    (not (zp entry-limit))
    (useful-dir-ent-list-p dir-ent-list)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
       (+ -1 entry-limit)))
     0)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit))))))))
     0)
    (equal
     (mv-nth
      1
      (find-dir-ent
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
       filename2))
     0))
   (equal
    (mv-nth
     0
     (lofat-to-hifat-helper
      fat32-in-memory (cdr dir-ent-list)
      (+
       -1 entry-limit
       (-
        (hifat-entry-count
         (remove-assoc-equal
          filename2
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))))
    (mv-nth
     0
     (lofat-to-hifat-helper
      fat32-in-memory (cdr dir-ent-list)
      (+
       -1 entry-limit
       (-
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  (make-dir-ent-list
                   (mv-nth 0
                           (dir-ent-clusterchain-contents
                            fat32-in-memory (car dir-ent-list))))
                  (+ -1 entry-limit))))))))))
  :hints
  (("goal"
    :in-theory (disable (:linear lofat-to-hifat-helper-correctness-3))
    :use
    ((:instance
      (:rewrite lofat-to-hifat-helper-correctness-4)
      (entry-limit2
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (remove-assoc-equal
           filename2
           (mv-nth
            0
            (lofat-to-hifat-helper
             fat32-in-memory
             (make-dir-ent-list
              (mv-nth 0
                      (dir-ent-clusterchain-contents
                       fat32-in-memory (car dir-ent-list))))
             (+ -1 entry-limit))))))))
      (entry-limit1
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))
      (dir-ent-list (cdr dir-ent-list)))
     (:instance
      (:linear lofat-to-hifat-helper-correctness-3)
      (entry-limit
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))
      (dir-ent-list (cdr dir-ent-list)))))))

;; Decently useful.
(defthm
  lofat-remove-file-correctness-1-lemma-26
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (dir-ent-p dir-ent)
        (dir-ent-directory-p dir-ent)
        (<= *ms-first-data-cluster*
            (dir-ent-first-cluster dir-ent))
        (< (dir-ent-first-cluster dir-ent)
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory)))
        (equal (mv-nth 1
                       (update-dir-contents fat32-in-memory
                                            (dir-ent-first-cluster dir-ent)
                                            dir-contents))
               0)
        (stringp dir-contents)
        (< 0 (len (explode dir-contents)))
        (<= (len (explode dir-contents))
            *ms-max-dir-size*)
        (non-free-index-list-listp x (effective-fat fat32-in-memory))
        (not-intersectp-list
         (mv-nth '0
                 (dir-ent-clusterchain fat32-in-memory dir-ent))
         x))
   (not-intersectp-list
    (mv-nth 0
            (dir-ent-clusterchain
             (mv-nth 0
                     (update-dir-contents fat32-in-memory
                                          (dir-ent-first-cluster dir-ent)
                                          dir-contents))
             dir-ent))
    x))
  :hints (("goal" :in-theory (enable not-intersectp-list))))

;; Sometimes useless, but needed by some theorems.
(defthm
  lofat-remove-file-correctness-1-lemma-27
  (implies
   (and
    (not (zp entry-limit))
    (useful-dir-ent-list-p dir-ent-list)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
       (+ -1 entry-limit)))
     0)
    (equal
     (mv-nth
      1
      (find-dir-ent
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
       filename2))
     0)
    (<=
     0
     (+
      -1 entry-limit
      (-
       (hifat-entry-count
        (remove-assoc-equal
         filename2
         (mv-nth 0
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  (make-dir-ent-list
                   (mv-nth 0
                           (dir-ent-clusterchain-contents
                            fat32-in-memory (car dir-ent-list))))
                  (+ -1 entry-limit)))))))))
   (<=
    (hifat-entry-count
     (mv-nth
      0
      (lofat-to-hifat-helper
       fat32-in-memory (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))))
    (+
     -1 entry-limit
     (-
      (hifat-entry-count
       (remove-assoc-equal
        filename2
        (mv-nth 0
                (lofat-to-hifat-helper
                 fat32-in-memory
                 (make-dir-ent-list
                  (mv-nth 0
                          (dir-ent-clusterchain-contents
                           fat32-in-memory (car dir-ent-list))))
                 (+ -1 entry-limit)))))))))
  :hints
  (("goal"
    :in-theory (disable (:linear lofat-to-hifat-helper-correctness-3))
    :use
    (:instance
     (:linear lofat-to-hifat-helper-correctness-3)
     (entry-limit
      (+
       -1 entry-limit
       (-
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  (make-dir-ent-list
                   (mv-nth 0
                           (dir-ent-clusterchain-contents
                            fat32-in-memory (car dir-ent-list))))
                  (+ -1 entry-limit)))))))
     (dir-ent-list (cdr dir-ent-list))
     (fat32-in-memory fat32-in-memory))))
  :rule-classes :linear)

(defthm
  lofat-remove-file-correctness-1-lemma-28
  (implies
   (and
    (not (zp entry-limit))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
       (+ -1 entry-limit)))
     0)
    (equal
     (mv-nth
      1
      (find-dir-ent
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
       filename2))
     0))
   (>=
    (binary-+
     '-1
     (binary-+
      entry-limit
      (unary--
       (hifat-entry-count
        (remove-assoc-equal
         filename2
         (mv-nth '0
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  (make-dir-ent-list
                   (mv-nth '0
                           (dir-ent-clusterchain-contents
                            fat32-in-memory (car dir-ent-list))))
                  (binary-+ '-1 entry-limit))))))))
    '0))
  :rule-classes (:rewrite :linear))

(defthm
  lofat-remove-file-correctness-1-lemma-29
  (implies
   (and (unsigned-byte-listp 8 dir-contents)
        (not (equal filename1 filename2))
        (not (equal (char-code (char filename2 0))
                    229)))
   (equal
    (len
     (explode
      (remove1-dir-ent
       (implode (nats=>chars (clear-dir-ent dir-contents filename1)))
       filename2)))
    (len (explode (remove1-dir-ent (nats=>string dir-contents)
                                   filename2)))))
  :hints
  (("goal"
    :in-theory (e/d (remove1-dir-ent clear-dir-ent
                                     len-when-dir-ent-p
                                     nats=>string)
                    (nats=>chars-of-take))
    :induct (clear-dir-ent dir-contents filename1)
    :expand
    ((remove1-dir-ent
      (implode (append (nats=>chars (take 32 dir-contents))
                       (nats=>chars (clear-dir-ent (nthcdr 32 dir-contents)
                                                   filename1))))
      filename2)
     (remove1-dir-ent (nats=>string dir-contents)
                      filename2)))
   ("subgoal *1/3''"
    :expand
    (remove1-dir-ent
     (implode
      (append
       (nats=>chars
        (dir-ent-set-filename
         (take 32 dir-contents)
         (nats=>string
          (update-nth
           0 229
           (string=>nats (dir-ent-filename (take 32 dir-contents)))))))
       (nats=>chars
        (clear-dir-ent (nthcdr 32 dir-contents)
                       (dir-ent-filename (take 32 dir-contents))))))
     filename2))))

(defthm lofat-remove-file-correctness-1-lemma-30
  (>= (len (explode (remove1-dir-ent dir-contents filename)))
      (- (len (explode dir-contents))
         *ms-dir-ent-length*))
  :hints (("goal" :in-theory (enable remove1-dir-ent)))
  :rule-classes :linear)

(defthm
  lofat-remove-file-correctness-1-lemma-31
  (implies
   (and (unsigned-byte-listp 8 dir-contents)
        (not (equal filename1 filename2))
        (not (equal filename1 filename3))
        (not (equal (char-code (char filename2 0))
                    229))
        (not (equal (char-code (char filename3 0))
                    229)))
   (equal
    (len
     (explode
      (remove1-dir-ent
       (remove1-dir-ent
        (implode (nats=>chars (clear-dir-ent dir-contents filename1)))
        filename2)
       filename3)))
    (len
     (explode (remove1-dir-ent (remove1-dir-ent (nats=>string dir-contents)
                                                filename2)
                               filename3)))))
  :hints
  (("goal"
    :in-theory (e/d (remove1-dir-ent clear-dir-ent
                                     len-when-dir-ent-p
                                     nats=>string)
                    (nats=>chars-of-take))
    :induct (clear-dir-ent dir-contents filename1)
    :expand
    ((remove1-dir-ent
      (implode (append (nats=>chars (take 32 dir-contents))
                       (nats=>chars (clear-dir-ent (nthcdr 32 dir-contents)
                                                   filename1))))
      filename2)))))

(make-event
 `(defthm
    lofat-remove-file-correctness-1-lemma-32
    (implies
     (and (unsigned-byte-listp 8 dir-contents)
          (not (equal filename1 filename2))
          (not (equal (char-code (char filename2 0))
                      229)))
     (equal
      (len
       (explode
        (remove1-dir-ent
         (implode (append (nats=>chars (clear-dir-ent dir-contents filename1))
                          (make-list-ac n ,(code-char 0) nil)))
         filename2)))
      (len
       (explode
        (remove1-dir-ent (implode (append (nats=>chars dir-contents)
                                          (make-list-ac n (code-char 0) nil)))
                         filename2)))))
    :hints
    (("goal"
      :in-theory (enable remove1-dir-ent clear-dir-ent
                         len-when-dir-ent-p
                         nats=>string)
      :induct (clear-dir-ent dir-contents filename1)
      :expand
      ((remove1-dir-ent
        (implode (append (nats=>chars (take 32 dir-contents))
                         (nats=>chars (clear-dir-ent (nthcdr 32 dir-contents)
                                                     filename1))))
        filename2)
       (remove1-dir-ent (nats=>string dir-contents)
                        filename2))))))

(make-event
 `(defthm
    lofat-remove-file-correctness-1-lemma-33
    (implies
     (and (unsigned-byte-listp 8 dir-contents)
          (not (equal filename1 filename2))
          (not (equal filename1 filename3))
          (not (equal (char-code (char filename2 0))
                      229))
          (not (equal (char-code (char filename3 0))
                      229)))
     (equal
      (len
       (explode
        (remove1-dir-ent
         (remove1-dir-ent
          (implode
           (append
            (nats=>chars (clear-dir-ent dir-contents filename1))
            (make-list-ac n ,(code-char 0) nil)))
          filename2)
         filename3)))
      (len
       (explode
        (remove1-dir-ent
         (remove1-dir-ent
          (implode (append (nats=>chars dir-contents)
                           (make-list-ac n (code-char 0) nil)))
          filename2)
         filename3)))))
    :hints
    (("goal"
      :in-theory (enable remove1-dir-ent clear-dir-ent
                         len-when-dir-ent-p
                         nats=>string)
      :induct (clear-dir-ent dir-contents filename1)
      :expand
      ((remove1-dir-ent
        (implode
         (append
          (nats=>chars (take 32 dir-contents))
          (nats=>chars (clear-dir-ent (nthcdr 32 dir-contents)
                                      filename1))))
        filename2))))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (make-event
   `(defthm
      lofat-remove-file-correctness-1-lemma-34
      (implies
       (and (equal (mod (len (explode dir-contents))
                        *ms-dir-ent-length*)
                   0)
            (equal (mod n *ms-dir-ent-length*) 0))
       (equal (remove1-dir-ent (implode (append (explode dir-contents)
                                                (make-list-ac n ,(code-char 0) nil)))
                               filename)
              (implode (append (explode (remove1-dir-ent dir-contents filename))
                               (make-list-ac n (code-char 0) nil)))))
      :hints (("goal" :in-theory (enable remove1-dir-ent)
               :induct (remove1-dir-ent dir-contents filename))
              ("subgoal *1/1" :expand (len (explode dir-contents))))))

  (make-event
   `(defthm
      lofat-remove-file-correctness-1-lemma-35
      (implies
       (and
        (equal (mod (length dir-contents)
                    *ms-dir-ent-length*)
               0)
        (equal (mod n *ms-dir-ent-length*) 0)
        (equal
         (len
          (explode (remove1-dir-ent (remove1-dir-ent dir-contents ".          ")
                                    "..         ")))
         (+ -64 (len (explode dir-contents)))))
       (<=
        (len
         (explode
          (remove1-dir-ent
           (remove1-dir-ent (implode (append (explode dir-contents)
                                             (make-list-ac n ,(code-char 0) nil)))
                            ".          ")
           "..         ")))
        (+
         -32
         (len
          (explode (remove1-dir-ent (implode (append (explode dir-contents)
                                                     (make-list-ac n ,(code-char 0) nil)))
                                    ".          "))))))
      :hints
      (("goal" :in-theory (enable remove1-dir-ent)
        :induct (remove1-dir-ent dir-contents ".          "))
       ("subgoal *1/4.4''"
        :in-theory (disable lofat-remove-file-correctness-1-lemma-34)
        :use
        (:instance
         lofat-remove-file-correctness-1-lemma-34
         (filename *parent-dir-fat32-name*)
         (dir-contents
          (remove1-dir-ent (implode (nthcdr 32 (explode dir-contents)))
                           *current-dir-fat32-name*))))
       ("subgoal *1/3.2'"
        :in-theory (disable lofat-remove-file-correctness-1-lemma-34)
        :use
        (:instance (:rewrite lofat-remove-file-correctness-1-lemma-34)
                   (filename "..         ")
                   (n n)
                   (dir-contents (implode (nthcdr 32 (explode dir-contents)))))))
      :rule-classes :linear)))

(make-event
 `(defthmd
    lofat-remove-file-correctness-1-lemma-36
    (implies
     (and (unsigned-byte-listp 8 dir-contents)
          (subdir-contents-p (nats=>string dir-contents))
          (fat32-filename-p filename)
          (equal (mod n 32) 0)
          (equal (mod (length dir-contents) 32)
                 0))
     (subdir-contents-p
      (implode (append (nats=>chars (clear-dir-ent dir-contents filename))
                       (make-list-ac n ,(code-char 0) nil)))))
    :hints
    (("goal"
      :in-theory (e/d (subdir-contents-p nats=>string
                                         fat32-filename-p)
                      (lofat-remove-file-correctness-1-lemma-34
                       lofat-remove-file-correctness-1-lemma-35))
      :use ((:instance (:linear lofat-remove-file-correctness-1-lemma-35)
                       (dir-contents (implode (nats=>chars dir-contents))))
            (:instance (:rewrite lofat-remove-file-correctness-1-lemma-34)
                       (filename *current-dir-fat32-name*)
                       (dir-contents (implode (nats=>chars dir-contents)))))))))

(defthm
  lofat-remove-file-correctness-1-lemma-39
  (implies
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit))))))))
     0)
    (dir-ent-directory-p (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename1)))
    (<=
     2
     (dir-ent-first-cluster
      (mv-nth 0
              (find-dir-ent
               (make-dir-ent-list
                (mv-nth 0
                        (dir-ent-clusterchain-contents
                         fat32-in-memory
                         (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename1)))))
               filename2))))
    (<
     (dir-ent-first-cluster
      (mv-nth 0
              (find-dir-ent
               (make-dir-ent-list
                (mv-nth 0
                        (dir-ent-clusterchain-contents
                         fat32-in-memory
                         (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename1)))))
               filename2)))
     (+ 2 (count-of-clusters fat32-in-memory)))
    (useful-dir-ent-list-p dir-ent-list)
    (not
     (member-intersectp-equal
      (mv-nth
       2
       (lofat-to-hifat-helper
        fat32-in-memory
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
        (+ -1 entry-limit)))
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
                      (dir-ent-clusterchain-contents
                       fat32-in-memory (car dir-ent-list))))
             (+ -1 entry-limit)))))))))))
   (not-intersectp-list
    (mv-nth
     0
     (dir-ent-clusterchain
      fat32-in-memory
      (mv-nth 0
              (find-dir-ent
               (make-dir-ent-list
                (mv-nth 0
                        (dir-ent-clusterchain-contents
                         fat32-in-memory
                         (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename1)))))
               filename2))))
    (mv-nth
     2
     (lofat-to-hifat-helper
      fat32-in-memory
      (make-dir-ent-list
       (mv-nth
        0
        (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
      (+ -1 entry-limit)))))
  :hints
  (("goal"
    :use
    (:instance
     (:rewrite lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2
               . 1)
     (entry-limit
      (+
       -1 entry-limit
       (-
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  (make-dir-ent-list
                   (mv-nth 0
                           (dir-ent-clusterchain-contents
                            fat32-in-memory (car dir-ent-list))))
                  (+ -1 entry-limit)))))))
     (l
      (mv-nth
       2
       (lofat-to-hifat-helper
        fat32-in-memory
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
        (+ -1 entry-limit))))
     (filename filename2)
     (dir-ent-list
      (make-dir-ent-list (mv-nth 0
                                 (dir-ent-clusterchain-contents
                                  fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename1))))))
     (fat32-in-memory fat32-in-memory)))))

(encapsulate
  ()

  (local (include-book "arithmetic-3/top" :dir :system))

  (set-default-hints '((nonlinearp-default-hint stable-under-simplificationp
                                                hist pspv)))

  (defthm
    lofat-remove-file-correctness-1-lemma-40
    (implies
     (lofat-fs-p fat32-in-memory)
     (integerp (binary-* '1/32
                         (cluster-size fat32-in-memory))))
    :hints (("goal" :in-theory (disable lofat-fs-p-correctness-1)
             :use lofat-fs-p-correctness-1)))

  (defthm lofat-remove-file-correctness-1-lemma-41
    (implies
     (and (lofat-fs-p fat32-in-memory)
          (dir-ent-directory-p dir-ent))
     (integerp
      (*
       1/32
       (len
        (explode
         (mv-nth
          0
          (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))))))
    :hints (("goal" :in-theory
             (disable
              root-dir-ent-list-of-lofat-remove-file-coincident-lemma-2
              lofat-fs-p-correctness-1)
             :use (lofat-fs-p-correctness-1
                   (:instance
                    root-dir-ent-list-of-lofat-remove-file-coincident-lemma-2
                    (y 32)))) )))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (make-event
   `(defthm
      lofat-remove-file-correctness-1-lemma-42
      (implies
       (and
        (dir-ent-directory-p (car dir-ent-list))
        (lofat-fs-p fat32-in-memory)
        (fat32-filename-p filename2)
        (subdir-contents-p
         (mv-nth
          0
          (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list)))))
       (subdir-contents-p
        (implode
         (append
          (nats=>chars
           (clear-dir-ent
            (string=>nats
             (mv-nth
              0
              (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
            filename2))
          (make-list-ac
           (+
            (- (len (explode (mv-nth 0
                                     (dir-ent-clusterchain-contents
                                      fat32-in-memory (car dir-ent-list))))))
            (*
             (cluster-size fat32-in-memory)
             (len
              (make-clusters
               (nats=>string
                (clear-dir-ent
                 (string=>nats (mv-nth 0
                                       (dir-ent-clusterchain-contents
                                        fat32-in-memory (car dir-ent-list))))
                 filename2))
               (cluster-size fat32-in-memory)))))
           ,(code-char 0) nil)))))
      :hints
      (("goal"
        :use
        (:instance
         (:rewrite lofat-remove-file-correctness-1-lemma-36)
         (n
          (+
           (- (len (explode (mv-nth 0
                                    (dir-ent-clusterchain-contents
                                     fat32-in-memory (car dir-ent-list))))))
           (*
            (cluster-size fat32-in-memory)
            (len
             (make-clusters
              (nats=>string
               (clear-dir-ent
                (string=>nats (mv-nth 0
                                      (dir-ent-clusterchain-contents
                                       fat32-in-memory (car dir-ent-list))))
                filename2))
              (cluster-size fat32-in-memory))))))
         (filename filename2)
         (dir-contents
          (string=>nats
           (mv-nth 0
                   (dir-ent-clusterchain-contents fat32-in-memory
                                                  (car dir-ent-list)))))))))))

(defthm
  lofat-remove-file-correctness-1-lemma-43
  (implies
   (and
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32-in-memory
                                          dir-ent-list entry-limit))
           0)
    (dir-ent-directory-p (mv-nth 0 (find-dir-ent dir-ent-list filename)))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-remove-file fat32-in-memory
                           (mv-nth 0 (find-dir-ent dir-ent-list filename))
                           pathname))
       dir-ent-list entry-limit))
     0)
    (consp (cdr pathname))
    (lofat-fs-p fat32-in-memory)
    (useful-dir-ent-list-p dir-ent-list)
    (fat32-filename-list-p pathname))
   (equal
    (mv-nth
     3
     (lofat-to-hifat-helper
      (mv-nth
       0
       (lofat-remove-file fat32-in-memory
                          (mv-nth 0 (find-dir-ent dir-ent-list filename))
                          pathname))
      (make-dir-ent-list
       (mv-nth 0
               (dir-ent-clusterchain-contents
                fat32-in-memory
                (mv-nth 0
                        (find-dir-ent dir-ent-list filename)))))
      entry-limit))
    0))
  :hints
  (("goal"
    :in-theory (disable (:rewrite lofat-find-file-correctness-1-lemma-6))
    :use
    ((:instance
      (:rewrite dir-ent-clusterchain-contents-of-lofat-remove-file-coincident)
      (pathname pathname)
      (dir-ent (mv-nth 0 (find-dir-ent dir-ent-list filename)))
      (fat32-in-memory fat32-in-memory))
     (:instance (:rewrite lofat-find-file-correctness-1-lemma-6)
                (name filename)
                (dir-ent-list dir-ent-list))
     (:instance
      (:rewrite lofat-find-file-correctness-1-lemma-6)
      (name filename)
      (fat32-in-memory
       (mv-nth
        0
        (lofat-remove-file fat32-in-memory
                           (mv-nth 0 (find-dir-ent dir-ent-list filename))
                           pathname))))))))

(defthm
  lofat-remove-file-correctness-1-lemma-44
  (implies
   (and
    (syntaxp (variablep entry-limit))
    (not (zp entry-limit))
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32-in-memory (cdr dir-ent-list)
                                          (+ -1 entry-limit)))
           0)
    (dir-ent-directory-p (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename)))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname))
       (cdr dir-ent-list)
       (+ -1 entry-limit)))
     0)
    (equal
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname))
       (cdr dir-ent-list)
       (+ -1 entry-limit)))
     (put-assoc-equal
      filename
      (m1-file
       (mv-nth 0
               (find-dir-ent (cdr dir-ent-list)
                             filename))
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-remove-file fat32-in-memory
                                    (mv-nth 0
                                            (find-dir-ent (cdr dir-ent-list)
                                                          filename))
                                    pathname))
         (make-dir-ent-list
          (mv-nth 0
                  (dir-ent-clusterchain-contents
                   fat32-in-memory
                   (mv-nth 0
                           (find-dir-ent (cdr dir-ent-list)
                                         filename)))))
         (+ -1 entry-limit))))
      (mv-nth 0
              (lofat-to-hifat-helper fat32-in-memory (cdr dir-ent-list)
                                     (+ -1 entry-limit)))))
    (consp (cdr pathname))
    (lofat-fs-p fat32-in-memory)
    (useful-dir-ent-list-p dir-ent-list)
    (fat32-filename-list-p pathname)
    (equal (mv-nth 1
                   (lofat-remove-file fat32-in-memory
                                      (mv-nth 0
                                              (find-dir-ent (cdr dir-ent-list)
                                                            filename))
                                      pathname))
           0))
   (equal
    (mv-nth
     0
     (lofat-to-hifat-helper
      (mv-nth 0
              (lofat-remove-file fat32-in-memory
                                 (mv-nth 0
                                         (find-dir-ent (cdr dir-ent-list)
                                                       filename))
                                 pathname))
      (cdr dir-ent-list)
      (+ -1 entry-limit)))
    (put-assoc-equal
     filename
     (m1-file
      (mv-nth 0
              (find-dir-ent (cdr dir-ent-list)
                            filename))
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-remove-file fat32-in-memory
                                   (mv-nth 0
                                           (find-dir-ent (cdr dir-ent-list)
                                                         filename))
                                   pathname))
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents
                  fat32-in-memory
                  (mv-nth 0
                          (find-dir-ent (cdr dir-ent-list)
                                        filename)))))
        entry-limit)))
     (mv-nth 0
             (lofat-to-hifat-helper fat32-in-memory (cdr dir-ent-list)
                                    (+ -1 entry-limit))))))
  :hints
  (("goal"
    :use
    (:instance
     (:rewrite lofat-to-hifat-helper-correctness-4)
     (entry-limit1 (- entry-limit 1))
     (entry-limit2 entry-limit)
     (dir-ent-list
      (make-dir-ent-list (mv-nth 0
                                 (dir-ent-clusterchain-contents
                                  fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))))))
     (fat32-in-memory
      (mv-nth 0
              (lofat-remove-file fat32-in-memory
                                 (mv-nth 0
                                         (find-dir-ent (cdr dir-ent-list)
                                                       filename))
                                 pathname)))))))

(defthm
  lofat-remove-file-correctness-1-lemma-45
  (implies
   (and
    (<= 2
        (dir-ent-first-cluster (car dir-ent-list)))
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32-in-memory (cdr dir-ent-list)
                                          (+ -1 entry-limit)))
           0)
    (dir-ent-directory-p (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename)))
    (lofat-fs-p fat32-in-memory)
    (useful-dir-ent-list-p dir-ent-list)
    (equal
     (mv-nth
      1
      (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list)))
     0)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
     (mv-nth 2
             (lofat-to-hifat-helper fat32-in-memory (cdr dir-ent-list)
                                    (+ -1 entry-limit)))))
   (equal
    (dir-ent-clusterchain
     (mv-nth 0
             (lofat-remove-file fat32-in-memory
                                (mv-nth 0
                                        (find-dir-ent (cdr dir-ent-list)
                                                      filename))
                                pathname))
     (car dir-ent-list))
    (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
  :hints
  (("goal"
    :in-theory
    (disable (:rewrite dir-ent-clusterchain-of-lofat-remove-file-disjoint))
    :use
    (:instance (:rewrite dir-ent-clusterchain-of-lofat-remove-file-disjoint)
               (dir-ent (car dir-ent-list))
               (entry-limit (+ -1 entry-limit))
               (root-dir-ent (mv-nth 0
                                     (find-dir-ent (cdr dir-ent-list)
                                                   filename)))))))

;; For Subgoal *1/4.376.1'22'
(defthm
  lofat-remove-file-correctness-1-lemma-46
  (implies
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit))))))))
     0)
    (dir-ent-directory-p (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename)))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname))
       (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit))))))))
     0)
    (equal
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname))
       (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit))))))))
     (put-assoc-equal
      filename
      (m1-file
       (mv-nth 0
               (find-dir-ent (cdr dir-ent-list)
                             filename))
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-remove-file fat32-in-memory
                                    (mv-nth 0
                                            (find-dir-ent (cdr dir-ent-list)
                                                          filename))
                                    pathname))
         (make-dir-ent-list
          (mv-nth 0
                  (dir-ent-clusterchain-contents
                   fat32-in-memory
                   (mv-nth 0
                           (find-dir-ent (cdr dir-ent-list)
                                         filename)))))
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
                       (dir-ent-clusterchain-contents
                        fat32-in-memory (car dir-ent-list))))
              (+ -1 entry-limit)))))))))
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
                      (dir-ent-clusterchain-contents
                       fat32-in-memory (car dir-ent-list))))
             (+ -1 entry-limit))))))))))
    (consp (cdr pathname))
    (lofat-fs-p fat32-in-memory)
    (useful-dir-ent-list-p dir-ent-list)
    (fat32-filename-list-p pathname)
    (equal (mv-nth 1
                   (lofat-remove-file fat32-in-memory
                                      (mv-nth 0
                                              (find-dir-ent (cdr dir-ent-list)
                                                            filename))
                                      pathname))
           0))
   (equal
    (mv-nth
     0
     (lofat-to-hifat-helper
      (mv-nth 0
              (lofat-remove-file fat32-in-memory
                                 (mv-nth 0
                                         (find-dir-ent (cdr dir-ent-list)
                                                       filename))
                                 pathname))
      (cdr dir-ent-list)
      (+
       -1 entry-limit
       (-
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  (make-dir-ent-list
                   (mv-nth 0
                           (dir-ent-clusterchain-contents
                            fat32-in-memory (car dir-ent-list))))
                  (+ -1 entry-limit))))))))
    (put-assoc-equal
     filename
     (m1-file
      (mv-nth 0
              (find-dir-ent (cdr dir-ent-list)
                            filename))
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-remove-file fat32-in-memory
                                   (mv-nth 0
                                           (find-dir-ent (cdr dir-ent-list)
                                                         filename))
                                   pathname))
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents
                  fat32-in-memory
                  (mv-nth 0
                          (find-dir-ent (cdr dir-ent-list)
                                        filename)))))
        entry-limit)))
     (mv-nth
      0
      (lofat-to-hifat-helper
       fat32-in-memory (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))))))
  :hints
  (("goal"
    :in-theory (disable (:linear lofat-to-hifat-helper-correctness-3))
    :use
    ((:instance
      (:rewrite lofat-to-hifat-helper-correctness-4)
      (entry-limit1
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))
      (entry-limit2 entry-limit)
      (dir-ent-list (make-dir-ent-list
                     (mv-nth 0
                             (dir-ent-clusterchain-contents
                              fat32-in-memory
                              (mv-nth 0
                                      (find-dir-ent (cdr dir-ent-list)
                                                    filename))))))
      (fat32-in-memory
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname))))
     (:instance
      (:linear lofat-to-hifat-helper-correctness-3)
      (entry-limit
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))
      (dir-ent-list (make-dir-ent-list
                     (mv-nth 0
                             (dir-ent-clusterchain-contents
                              fat32-in-memory
                              (mv-nth 0
                                      (find-dir-ent (cdr dir-ent-list)
                                                    filename))))))
      (fat32-in-memory
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname))))))))

(defthm
  lofat-remove-file-correctness-1-lemma-47
  (implies
   (and
    (dir-ent-directory-p
     (mv-nth
      0
      (find-dir-ent
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       (car pathname))))
    (lofat-fs-p fat32-in-memory)
    (dir-ent-p dir-ent)
    (<= 2 (dir-ent-first-cluster dir-ent))
    (equal (mv-nth 1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
           0)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory dir-ent))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       entry-limit)))
    (no-duplicatesp-equal
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory dir-ent))))
   (no-duplicatesp-equal
    (mv-nth
     0
     (dir-ent-clusterchain
      (mv-nth
       0
       (lofat-remove-file
        fat32-in-memory
        (mv-nth
         0
         (find-dir-ent
          (make-dir-ent-list
           (mv-nth 0
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
          (car pathname)))
        (cdr pathname)))
      dir-ent))))
  :hints
  (("goal"
    :in-theory
    (disable (:rewrite dir-ent-clusterchain-of-lofat-remove-file-disjoint))
    :use
    (:instance
     (:rewrite dir-ent-clusterchain-of-lofat-remove-file-disjoint)
     (dir-ent dir-ent)
     (pathname (cdr pathname))
     (root-dir-ent
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
        (car pathname))))
     (fat32-in-memory fat32-in-memory)))))

(defthm
  lofat-remove-file-correctness-1-lemma-22
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (dir-ent-p dir-ent)
    (dir-ent-directory-p dir-ent)
    (>= (dir-ent-first-cluster dir-ent)
        *ms-first-data-cluster*)
    (< (dir-ent-first-cluster dir-ent)
       (+ *ms-first-data-cluster*
          (count-of-clusters fat32-in-memory)))
    (fat32-filename-list-p pathname)
    (equal (mv-nth 1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
           0)
    (equal (mv-nth 1
                   (lofat-remove-file fat32-in-memory dir-ent pathname))
           0)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory dir-ent))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       entry-limit)))
    (no-duplicatesp-equal
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory dir-ent))))
   (no-duplicatesp-equal
    (mv-nth 0
            (dir-ent-clusterchain
             (mv-nth 0
                     (lofat-remove-file fat32-in-memory dir-ent pathname))
             dir-ent)))))

(defthm
  lofat-remove-file-correctness-1-lemma-49
  (implies
   (and
    (syntaxp (variablep entry-limit))
    (not (zp entry-limit))
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32-in-memory (cdr dir-ent-list)
                                          (+ -1 entry-limit)))
           0)
    (dir-ent-directory-p (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename)))
    (equal (mv-nth 1
                   (lofat-remove-file fat32-in-memory
                                      (mv-nth 0
                                              (find-dir-ent (cdr dir-ent-list)
                                                            filename))
                                      pathname))
           0)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname))
       (cdr dir-ent-list)
       (+ -1 entry-limit)))
     0)
    (consp (cdr pathname))
    (lofat-fs-p fat32-in-memory)
    (useful-dir-ent-list-p dir-ent-list)
    (fat32-filename-list-p pathname)
    (<
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-remove-file fat32-in-memory
                                   (mv-nth 0
                                           (find-dir-ent (cdr dir-ent-list)
                                                         filename))
                                   pathname))
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents
                  fat32-in-memory
                  (mv-nth 0
                          (find-dir-ent (cdr dir-ent-list)
                                        filename)))))
        entry-limit)))
     (hifat-entry-count
      (mv-nth 0
              (lofat-to-hifat-helper
               fat32-in-memory
               (make-dir-ent-list
                (mv-nth 0
                        (dir-ent-clusterchain-contents
                         fat32-in-memory
                         (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename)))))
               entry-limit)))))
   (>
    (hifat-entry-count
     (mv-nth 0
             (lofat-to-hifat-helper
              fat32-in-memory
              (make-dir-ent-list
               (mv-nth 0
                       (dir-ent-clusterchain-contents
                        fat32-in-memory
                        (mv-nth 0
                                (find-dir-ent (cdr dir-ent-list)
                                              filename)))))
              (+ -1 entry-limit))))
    (hifat-entry-count
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname))
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents
                 fat32-in-memory
                 (mv-nth 0
                         (find-dir-ent (cdr dir-ent-list)
                                       filename)))))
       (+ -1 entry-limit))))))
  :hints
  (("goal"
    :use
    ((:instance
      (:rewrite lofat-to-hifat-helper-correctness-4)
      (entry-limit1 (- entry-limit 1))
      (entry-limit2 entry-limit)
      (dir-ent-list (make-dir-ent-list
                     (mv-nth 0
                             (dir-ent-clusterchain-contents
                              fat32-in-memory
                              (mv-nth 0
                                      (find-dir-ent (cdr dir-ent-list)
                                                    filename))))))
      (fat32-in-memory
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname))))
     (:instance
      (:rewrite lofat-to-hifat-helper-correctness-4)
      (entry-limit1 (- entry-limit 1))
      (entry-limit2 entry-limit)
      (dir-ent-list (make-dir-ent-list
                     (mv-nth 0
                             (dir-ent-clusterchain-contents
                              fat32-in-memory
                              (mv-nth 0
                                      (find-dir-ent (cdr dir-ent-list)
                                                    filename))))))
      (fat32-in-memory fat32-in-memory)))))
  :rule-classes :linear)

(defthm
  lofat-remove-file-correctness-1-lemma-50
  (implies
   (and
    (syntaxp (variablep entry-limit))
    (not (zp entry-limit))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname))
       (cdr dir-ent-list)
       (+ -1 entry-limit)))
     0)
    (useful-dir-ent-list-p dir-ent-list))
   (equal
    (mv-nth
     3
     (lofat-to-hifat-helper
      (mv-nth 0
              (lofat-remove-file fat32-in-memory
                                 (mv-nth 0
                                         (find-dir-ent (cdr dir-ent-list)
                                                       filename))
                                 pathname))
      (cdr dir-ent-list)
      entry-limit))
    0))
  :hints
  (("goal"
    :use
    ((:instance
      (:rewrite lofat-to-hifat-helper-correctness-4)
      (entry-limit1 (+ -1 entry-limit))
      (entry-limit2 entry-limit)
      (dir-ent-list (cdr dir-ent-list))
      (fat32-in-memory
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname))))
     (:instance
      (:rewrite lofat-to-hifat-helper-correctness-4)
      (entry-limit1 (+ -1 entry-limit))
      (entry-limit2 entry-limit)
      (dir-ent-list (make-dir-ent-list
                     (mv-nth 0
                             (dir-ent-clusterchain-contents
                              fat32-in-memory
                              (mv-nth 0
                                      (find-dir-ent (cdr dir-ent-list)
                                                    filename))))))
      (fat32-in-memory fat32-in-memory))))))

(defthm
  lofat-remove-file-correctness-1-lemma-51
  (implies
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname))
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents
                 fat32-in-memory
                 (mv-nth 0
                         (find-dir-ent (cdr dir-ent-list)
                                       filename)))))
       entry-limit))
     0)
    (<
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-remove-file fat32-in-memory
                                   (mv-nth 0
                                           (find-dir-ent (cdr dir-ent-list)
                                                         filename))
                                   pathname))
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents
                  fat32-in-memory
                  (mv-nth 0
                          (find-dir-ent (cdr dir-ent-list)
                                        filename)))))
        entry-limit)))
     (hifat-entry-count
      (mv-nth 0
              (lofat-to-hifat-helper
               fat32-in-memory
               (make-dir-ent-list
                (mv-nth 0
                        (dir-ent-clusterchain-contents
                         fat32-in-memory
                         (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename)))))
               entry-limit)))))
   (equal
    (mv-nth
     3
     (lofat-to-hifat-helper
      (mv-nth 0
              (lofat-remove-file fat32-in-memory
                                 (mv-nth 0
                                         (find-dir-ent (cdr dir-ent-list)
                                                       filename))
                                 pathname))
      (make-dir-ent-list (mv-nth 0
                                 (dir-ent-clusterchain-contents
                                  fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename)))))
      (+ -1 entry-limit)))
    0))
  :hints
  (("goal"
    :use
    (:instance
     lofat-to-hifat-helper-correctness-4
     (entry-limit1 entry-limit)
     (entry-limit2 (+ -1 entry-limit))
     (dir-ent-list
      (make-dir-ent-list (mv-nth 0
                                 (dir-ent-clusterchain-contents
                                  fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))))))
     (fat32-in-memory
      (mv-nth 0
              (lofat-remove-file fat32-in-memory
                                 (mv-nth 0
                                         (find-dir-ent (cdr dir-ent-list)
                                                       filename))
                                 pathname)))))))

(defthm
  lofat-remove-file-correctness-1-lemma-52
  (implies
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname))
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents
                 fat32-in-memory
                 (mv-nth 0
                         (find-dir-ent (cdr dir-ent-list)
                                       filename)))))
       entry-limit))
     0)
    (useful-dir-ent-list-p dir-ent-list)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32-in-memory (cdr dir-ent-list)
                                          (+ -1 entry-limit)))
           0)
    (dir-ent-directory-p (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename)))
    (<= 2
        (dir-ent-first-cluster (mv-nth 0
                                       (find-dir-ent (cdr dir-ent-list)
                                                     filename))))
    (<
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-remove-file fat32-in-memory
                                   (mv-nth 0
                                           (find-dir-ent (cdr dir-ent-list)
                                                         filename))
                                   pathname))
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents
                  fat32-in-memory
                  (mv-nth 0
                          (find-dir-ent (cdr dir-ent-list)
                                        filename)))))
        entry-limit)))
     (hifat-entry-count
      (mv-nth 0
              (lofat-to-hifat-helper
               fat32-in-memory
               (make-dir-ent-list
                (mv-nth 0
                        (dir-ent-clusterchain-contents
                         fat32-in-memory
                         (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename)))))
               entry-limit)))))
   (>
    (hifat-entry-count
     (mv-nth 0
             (lofat-to-hifat-helper
              fat32-in-memory
              (make-dir-ent-list
               (mv-nth 0
                       (dir-ent-clusterchain-contents
                        fat32-in-memory
                        (mv-nth 0
                                (find-dir-ent (cdr dir-ent-list)
                                              filename)))))
              (+ -1 entry-limit))))
    (hifat-entry-count
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname))
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents
                 fat32-in-memory
                 (mv-nth 0
                         (find-dir-ent (cdr dir-ent-list)
                                       filename)))))
       (+ -1 entry-limit))))))
  :rule-classes :linear
  :hints
  (("goal"
    :use
    ((:instance
      lofat-to-hifat-helper-correctness-4
      (entry-limit1 entry-limit)
      (entry-limit2 (+ -1 entry-limit))
      (dir-ent-list (make-dir-ent-list
                     (mv-nth 0
                             (dir-ent-clusterchain-contents
                              fat32-in-memory
                              (mv-nth 0
                                      (find-dir-ent (cdr dir-ent-list)
                                                    filename))))))
      (fat32-in-memory
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname))))
     (:instance
      lofat-to-hifat-helper-correctness-4
      (entry-limit1 (+ -1 entry-limit))
      (entry-limit2 entry-limit)
      (dir-ent-list (make-dir-ent-list
                     (mv-nth 0
                             (dir-ent-clusterchain-contents
                              fat32-in-memory
                              (mv-nth 0
                                      (find-dir-ent (cdr dir-ent-list)
                                                    filename))))))
      (fat32-in-memory fat32-in-memory))))))

;; Sometimes useless, but needed by some theorems.
(defthm
  lofat-remove-file-correctness-1-lemma-53
  (implies
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname))
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents
                 fat32-in-memory
                 (mv-nth 0
                         (find-dir-ent (cdr dir-ent-list)
                                       filename)))))
       entry-limit))
     0)
    (useful-dir-ent-list-p dir-ent-list)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit))))))))
     0)
    (dir-ent-directory-p (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename)))
    (<
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-remove-file fat32-in-memory
                                   (mv-nth 0
                                           (find-dir-ent (cdr dir-ent-list)
                                                         filename))
                                   pathname))
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents
                  fat32-in-memory
                  (mv-nth 0
                          (find-dir-ent (cdr dir-ent-list)
                                        filename)))))
        entry-limit)))
     (hifat-entry-count
      (mv-nth 0
              (lofat-to-hifat-helper
               fat32-in-memory
               (make-dir-ent-list
                (mv-nth 0
                        (dir-ent-clusterchain-contents
                         fat32-in-memory
                         (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename)))))
               entry-limit)))))
   (equal
    (mv-nth
     3
     (lofat-to-hifat-helper
      (mv-nth 0
              (lofat-remove-file fat32-in-memory
                                 (mv-nth 0
                                         (find-dir-ent (cdr dir-ent-list)
                                                       filename))
                                 pathname))
      (make-dir-ent-list (mv-nth 0
                                 (dir-ent-clusterchain-contents
                                  fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename)))))
      (+
       -1 entry-limit
       (-
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  (make-dir-ent-list
                   (mv-nth 0
                           (dir-ent-clusterchain-contents
                            fat32-in-memory (car dir-ent-list))))
                  (+ -1 entry-limit))))))))
    0))
  :hints
  (("goal"
    :in-theory (disable lofat-find-file-correctness-1-lemma-6)
    :use
    ((:instance
      lofat-to-hifat-helper-correctness-4
      (entry-limit1 entry-limit)
      (entry-limit2
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))
      (dir-ent-list (make-dir-ent-list
                     (mv-nth 0
                             (dir-ent-clusterchain-contents
                              fat32-in-memory
                              (mv-nth 0
                                      (find-dir-ent (cdr dir-ent-list)
                                                    filename))))))
      (fat32-in-memory
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname))))
     (:instance
      lofat-find-file-correctness-1-lemma-6
      (entry-limit
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))
      (name filename)
      (dir-ent-list (cdr dir-ent-list))
      (fat32-in-memory fat32-in-memory))
     (:instance
      (:rewrite lofat-to-hifat-helper-correctness-4)
      (entry-limit1
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))
      (entry-limit2 entry-limit)
      (dir-ent-list (make-dir-ent-list
                     (mv-nth 0
                             (dir-ent-clusterchain-contents
                              fat32-in-memory
                              (mv-nth 0
                                      (find-dir-ent (cdr dir-ent-list)
                                                    filename))))))
      (fat32-in-memory fat32-in-memory))))))

(encapsulate
  ()

  (set-default-hints
   '(("goal"
      :in-theory (disable (:linear lofat-to-hifat-helper-correctness-3))
      :use
      ((:instance
        (:linear lofat-to-hifat-helper-correctness-3)
        (entry-limit (+ -1 entry-limit))
        (dir-ent-list
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list)))))
        (fat32-in-memory fat32-in-memory))
       (:instance
        (:linear lofat-to-hifat-helper-correctness-3)
        (entry-limit
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth 0
                    (lofat-to-hifat-helper
                     fat32-in-memory
                     (make-dir-ent-list
                      (mv-nth 0
                              (dir-ent-clusterchain-contents
                               fat32-in-memory (car dir-ent-list))))
                     (+ -1 entry-limit)))))))
        (dir-ent-list (cdr dir-ent-list))
        (fat32-in-memory fat32-in-memory))
       (:instance
        (:rewrite lofat-to-hifat-helper-correctness-4)
        (entry-limit1
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth 0
                    (lofat-to-hifat-helper
                     fat32-in-memory
                     (make-dir-ent-list
                      (mv-nth 0
                              (dir-ent-clusterchain-contents
                               fat32-in-memory (car dir-ent-list))))
                     (+ -1 entry-limit)))))))
        (entry-limit2
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              (mv-nth 0
                      (lofat-remove-file fat32-in-memory (car dir-ent-list)
                                         pathname))
              (make-dir-ent-list
               (mv-nth 0
                       (dir-ent-clusterchain-contents
                        fat32-in-memory (car dir-ent-list))))
              (+ -1 entry-limit)))))))
        (dir-ent-list (cdr dir-ent-list))
        (fat32-in-memory fat32-in-memory))
       (:instance
        lofat-to-hifat-helper-correctness-4
        (entry-limit1 entry-limit)
        (entry-limit2 (+ -1 entry-limit))
        (dir-ent-list
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list)))))
        (fat32-in-memory
         (mv-nth 0
                 (lofat-remove-file fat32-in-memory (car dir-ent-list)
                                    pathname))))))))

  (defthm
    lofat-remove-file-correctness-1-lemma-54
    (implies
     (and
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-remove-file fat32-in-memory (car dir-ent-list)
                                    pathname))
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
         entry-limit))
       0)
      (useful-dir-ent-list-p dir-ent-list)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32-in-memory (cdr dir-ent-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth 0
                    (lofat-to-hifat-helper
                     fat32-in-memory
                     (make-dir-ent-list
                      (mv-nth 0
                              (dir-ent-clusterchain-contents
                               fat32-in-memory (car dir-ent-list))))
                     (+ -1 entry-limit))))))))
       0)
      (<
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          (mv-nth 0
                  (lofat-remove-file fat32-in-memory (car dir-ent-list)
                                     pathname))
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
          entry-limit)))
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
          (+ -1 entry-limit))))))
     (equal
      (mv-nth
       '3
       (lofat-to-hifat-helper
        fat32-in-memory (cdr dir-ent-list)
        (binary-+
         '-1
         (binary-+
          entry-limit
          (unary--
           (hifat-entry-count
            (mv-nth
             '0
             (lofat-to-hifat-helper
              (mv-nth '0
                      (lofat-remove-file fat32-in-memory (car dir-ent-list)
                                         pathname))
              (make-dir-ent-list
               (mv-nth '0
                       (dir-ent-clusterchain-contents
                        fat32-in-memory (car dir-ent-list))))
              (binary-+ '-1 entry-limit)))))))))
      '0)))

  (defthm
    lofat-remove-file-correctness-1-lemma-55
    (implies
     (and
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-remove-file fat32-in-memory (car dir-ent-list)
                                    pathname))
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
         entry-limit))
       0)
      (useful-dir-ent-list-p dir-ent-list)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32-in-memory (cdr dir-ent-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth 0
                    (lofat-to-hifat-helper
                     fat32-in-memory
                     (make-dir-ent-list
                      (mv-nth 0
                              (dir-ent-clusterchain-contents
                               fat32-in-memory (car dir-ent-list))))
                     (+ -1 entry-limit))))))))
       0)
      (not-intersectp-list
       (mv-nth 0
               (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32-in-memory (cdr dir-ent-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth 0
                    (lofat-to-hifat-helper
                     fat32-in-memory
                     (make-dir-ent-list
                      (mv-nth 0
                              (dir-ent-clusterchain-contents
                               fat32-in-memory (car dir-ent-list))))
                     (+ -1 entry-limit)))))))))
      (<
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          (mv-nth 0
                  (lofat-remove-file fat32-in-memory (car dir-ent-list)
                                     pathname))
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
          entry-limit)))
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
          (+ -1 entry-limit))))))
     (not-intersectp-list
      (mv-nth '0
              (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
      (mv-nth
       '2
       (lofat-to-hifat-helper
        fat32-in-memory (cdr dir-ent-list)
        (binary-+
         '-1
         (binary-+
          entry-limit
          (unary--
           (hifat-entry-count
            (mv-nth
             '0
             (lofat-to-hifat-helper
              (mv-nth '0
                      (lofat-remove-file fat32-in-memory (car dir-ent-list)
                                         pathname))
              (make-dir-ent-list
               (mv-nth '0
                       (dir-ent-clusterchain-contents
                        fat32-in-memory (car dir-ent-list))))
              (binary-+ '-1 entry-limit))))))))))))

  (defthm
    lofat-remove-file-correctness-1-lemma-56
    (implies
     (and
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-remove-file fat32-in-memory (car dir-ent-list)
                                    pathname))
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
         entry-limit))
       0)
      (useful-dir-ent-list-p dir-ent-list)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32-in-memory (cdr dir-ent-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth 0
                    (lofat-to-hifat-helper
                     fat32-in-memory
                     (make-dir-ent-list
                      (mv-nth 0
                              (dir-ent-clusterchain-contents
                               fat32-in-memory (car dir-ent-list))))
                     (+ -1 entry-limit))))))))
       0)
      (not
       (member-intersectp-equal
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
          (+ -1 entry-limit)))
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
                        (dir-ent-clusterchain-contents
                         fat32-in-memory (car dir-ent-list))))
               (+ -1 entry-limit))))))))))
      (<
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          (mv-nth 0
                  (lofat-remove-file fat32-in-memory (car dir-ent-list)
                                     pathname))
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
          entry-limit)))
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
          (+ -1 entry-limit))))))
     (not
      (member-intersectp-equal
       (mv-nth
        '2
        (lofat-to-hifat-helper
         fat32-in-memory
         (make-dir-ent-list
          (mv-nth
           '0
           (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
         (binary-+ '-1 entry-limit)))
       (mv-nth
        '2
        (lofat-to-hifat-helper
         fat32-in-memory (cdr dir-ent-list)
         (binary-+
          '-1
          (binary-+
           entry-limit
           (unary--
            (hifat-entry-count
             (mv-nth
              '0
              (lofat-to-hifat-helper
               (mv-nth '0
                       (lofat-remove-file fat32-in-memory (car dir-ent-list)
                                          pathname))
               (make-dir-ent-list
                (mv-nth '0
                        (dir-ent-clusterchain-contents
                         fat32-in-memory (car dir-ent-list))))
               (binary-+ '-1 entry-limit)))))))))))))

  (defthm
    lofat-remove-file-correctness-1-lemma-57
    (implies
     (and
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-remove-file fat32-in-memory (car dir-ent-list)
                                    pathname))
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
         entry-limit))
       0)
      (useful-dir-ent-list-p dir-ent-list)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32-in-memory (cdr dir-ent-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth 0
                    (lofat-to-hifat-helper
                     fat32-in-memory
                     (make-dir-ent-list
                      (mv-nth 0
                              (dir-ent-clusterchain-contents
                               fat32-in-memory (car dir-ent-list))))
                     (+ -1 entry-limit))))))))
       0)
      (<
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          (mv-nth 0
                  (lofat-remove-file fat32-in-memory (car dir-ent-list)
                                     pathname))
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
          entry-limit)))
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
          (+ -1 entry-limit)))))
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32-in-memory (cdr dir-ent-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth 0
                    (lofat-to-hifat-helper
                     fat32-in-memory
                     (make-dir-ent-list
                      (mv-nth 0
                              (dir-ent-clusterchain-contents
                               fat32-in-memory (car dir-ent-list))))
                     (+ -1 entry-limit))))))))))
     (not-intersectp-list
      x
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
             (mv-nth 0
                     (lofat-remove-file fat32-in-memory (car dir-ent-list)
                                        pathname))
             (make-dir-ent-list
              (mv-nth 0
                      (dir-ent-clusterchain-contents
                       fat32-in-memory (car dir-ent-list))))
             (+ -1 entry-limit)))))))))))

  (defthm
    lofat-remove-file-correctness-1-lemma-58
    (implies
     (and
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-remove-file fat32-in-memory (car dir-ent-list)
                                    pathname))
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
         entry-limit))
       0)
      (useful-dir-ent-list-p dir-ent-list)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32-in-memory (cdr dir-ent-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth 0
                    (lofat-to-hifat-helper
                     fat32-in-memory
                     (make-dir-ent-list
                      (mv-nth 0
                              (dir-ent-clusterchain-contents
                               fat32-in-memory (car dir-ent-list))))
                     (+ -1 entry-limit))))))))
       0)
      (<
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          (mv-nth 0
                  (lofat-remove-file fat32-in-memory (car dir-ent-list)
                                     pathname))
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
          entry-limit)))
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
          (+ -1 entry-limit))))))
     (equal
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
             (mv-nth 0
                     (lofat-remove-file fat32-in-memory (car dir-ent-list)
                                        pathname))
             (make-dir-ent-list
              (mv-nth 0
                      (dir-ent-clusterchain-contents
                       fat32-in-memory (car dir-ent-list))))
             (+ -1 entry-limit))))))))
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32-in-memory (cdr dir-ent-list)
        (+
         -1 entry-limit
         (-
          (hifat-entry-count
           (mv-nth 0
                   (lofat-to-hifat-helper
                    fat32-in-memory
                    (make-dir-ent-list
                     (mv-nth 0
                             (dir-ent-clusterchain-contents
                              fat32-in-memory (car dir-ent-list))))
                    (+ -1 entry-limit)))))))))))

  (defthm
    lofat-remove-file-correctness-1-lemma-59
    (implies
     (and
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-remove-file fat32-in-memory (car dir-ent-list)
                                    pathname))
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
         entry-limit))
       0)
      (useful-dir-ent-list-p dir-ent-list)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32-in-memory (cdr dir-ent-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth 0
                    (lofat-to-hifat-helper
                     fat32-in-memory
                     (make-dir-ent-list
                      (mv-nth 0
                              (dir-ent-clusterchain-contents
                               fat32-in-memory (car dir-ent-list))))
                     (+ -1 entry-limit))))))))
       0)
      (<
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          (mv-nth 0
                  (lofat-remove-file fat32-in-memory (car dir-ent-list)
                                     pathname))
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
          entry-limit)))
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
          (+ -1 entry-limit))))))
     (equal
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
             (mv-nth 0
                     (lofat-remove-file fat32-in-memory (car dir-ent-list)
                                        pathname))
             (make-dir-ent-list
              (mv-nth 0
                      (dir-ent-clusterchain-contents
                       fat32-in-memory (car dir-ent-list))))
             entry-limit)))))))
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32-in-memory (cdr dir-ent-list)
        (+
         -1 entry-limit
         (-
          (hifat-entry-count
           (mv-nth 0
                   (lofat-to-hifat-helper
                    fat32-in-memory
                    (make-dir-ent-list
                     (mv-nth 0
                             (dir-ent-clusterchain-contents
                              fat32-in-memory (car dir-ent-list))))
                    (+ -1 entry-limit))))))))))))

(defthmd
  lofat-remove-file-correctness-1-lemma-61
  (implies
   (and
    (syntaxp (variablep entry-limit))
    (not (zp entry-limit))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname))
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents
                 fat32-in-memory
                 (mv-nth 0
                         (find-dir-ent (cdr dir-ent-list)
                                       filename)))))
       entry-limit))
     0)
    (<
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-remove-file fat32-in-memory
                                   (mv-nth 0
                                           (find-dir-ent (cdr dir-ent-list)
                                                         filename))
                                   pathname))
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents
                  fat32-in-memory
                  (mv-nth 0
                          (find-dir-ent (cdr dir-ent-list)
                                        filename)))))
        entry-limit)))
     (hifat-entry-count
      (mv-nth 0
              (lofat-to-hifat-helper
               fat32-in-memory
               (make-dir-ent-list
                (mv-nth 0
                        (dir-ent-clusterchain-contents
                         fat32-in-memory
                         (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename)))))
               entry-limit)))))
   (equal
    (lofat-to-hifat-helper
     (mv-nth 0
             (lofat-remove-file fat32-in-memory
                                (mv-nth 0
                                        (find-dir-ent (cdr dir-ent-list)
                                                      filename))
                                pathname))
     (make-dir-ent-list
      (mv-nth
       0
       (dir-ent-clusterchain-contents fat32-in-memory
                                      (mv-nth 0
                                              (find-dir-ent (cdr dir-ent-list)
                                                            filename)))))
     entry-limit)
    (lofat-to-hifat-helper
     (mv-nth 0
             (lofat-remove-file fat32-in-memory
                                (mv-nth 0
                                        (find-dir-ent (cdr dir-ent-list)
                                                      filename))
                                pathname))
     (make-dir-ent-list
      (mv-nth
       0
       (dir-ent-clusterchain-contents fat32-in-memory
                                      (mv-nth 0
                                              (find-dir-ent (cdr dir-ent-list)
                                                            filename)))))
     (+ -1 entry-limit))))
  :hints
  (("goal"
    :use
    (:instance
     lofat-to-hifat-helper-correctness-4
     (entry-limit1 entry-limit)
     (entry-limit2 (+ -1 entry-limit))
     (dir-ent-list
      (make-dir-ent-list (mv-nth 0
                                 (dir-ent-clusterchain-contents
                                  fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))))))
     (fat32-in-memory
      (mv-nth 0
              (lofat-remove-file fat32-in-memory
                                 (mv-nth 0
                                         (find-dir-ent (cdr dir-ent-list)
                                                       filename))
                                 pathname)))))))

;; Very handy!
(defthm
  lofat-remove-file-correctness-1-lemma-6
  (implies
   (and
    (<= 2
        (dir-ent-first-cluster (car dir-ent-list)))
    (consp (cdr pathname))
    (lofat-fs-p fat32-in-memory)
    (useful-dir-ent-list-p dir-ent-list)
    (equal
     (mv-nth
      1
      (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list)))
     0)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
       (+ -1 entry-limit)))
     0)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
       (+ -1 entry-limit))))
    (fat32-filename-list-p pathname))
   (equal (dir-ent-clusterchain
           (mv-nth 0
                   (lofat-remove-file fat32-in-memory (car dir-ent-list)
                                      pathname))
           (car dir-ent-list))
          (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
  :hints
  (("goal"
    :expand (lofat-remove-file fat32-in-memory (car dir-ent-list)
                               pathname)
    :in-theory
    (disable (:rewrite dir-ent-clusterchain-of-lofat-remove-file-disjoint))
    :use
    (:instance
     (:rewrite dir-ent-clusterchain-of-lofat-remove-file-disjoint)
     (entry-limit (- entry-limit 1))
     (dir-ent (car dir-ent-list))
     (pathname (cdr pathname))
     (root-dir-ent
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
        (car pathname))))
     (fat32-in-memory fat32-in-memory)))))

(defthm
  lofat-remove-file-correctness-1-lemma-7
  (implies
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname))
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents
                 fat32-in-memory
                 (mv-nth 0
                         (find-dir-ent (cdr dir-ent-list)
                                       filename)))))
       entry-limit))
     0)
    (useful-dir-ent-list-p dir-ent-list)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit))))))))
     0)
    (dir-ent-directory-p (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename)))
    (<
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-remove-file fat32-in-memory
                                   (mv-nth 0
                                           (find-dir-ent (cdr dir-ent-list)
                                                         filename))
                                   pathname))
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents
                  fat32-in-memory
                  (mv-nth 0
                          (find-dir-ent (cdr dir-ent-list)
                                        filename)))))
        entry-limit)))
     (hifat-entry-count
      (mv-nth 0
              (lofat-to-hifat-helper
               fat32-in-memory
               (make-dir-ent-list
                (mv-nth 0
                        (dir-ent-clusterchain-contents
                         fat32-in-memory
                         (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename)))))
               entry-limit)))))
   (>
    (hifat-entry-count
     (mv-nth
      0
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents
                 fat32-in-memory
                 (mv-nth 0
                         (find-dir-ent (cdr dir-ent-list)
                                       filename)))))
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))))
    (hifat-entry-count
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname))
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents
                 fat32-in-memory
                 (mv-nth 0
                         (find-dir-ent (cdr dir-ent-list)
                                       filename)))))
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))))))
  :rule-classes :linear
  :hints
  (("goal"
    :in-theory (disable (:linear lofat-to-hifat-helper-correctness-3))
    :use
    ((:instance
      (:rewrite lofat-to-hifat-helper-correctness-4)
      (entry-limit2 entry-limit)
      (dir-ent-list (make-dir-ent-list
                     (mv-nth 0
                             (dir-ent-clusterchain-contents
                              fat32-in-memory
                              (mv-nth 0
                                      (find-dir-ent (cdr dir-ent-list)
                                                    filename))))))
      (entry-limit1
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit))))))))
     (:instance
      (:rewrite lofat-to-hifat-helper-correctness-4)
      (entry-limit2 entry-limit)
      (dir-ent-list (make-dir-ent-list
                     (mv-nth 0
                             (dir-ent-clusterchain-contents
                              fat32-in-memory
                              (mv-nth 0
                                      (find-dir-ent (cdr dir-ent-list)
                                                    filename))))))
      (fat32-in-memory
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname)))
      (entry-limit1
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit))))))))
     (:instance
      (:linear lofat-to-hifat-helper-correctness-3)
      (entry-limit
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))
      (dir-ent-list (make-dir-ent-list
                     (mv-nth 0
                             (dir-ent-clusterchain-contents
                              fat32-in-memory
                              (mv-nth 0
                                      (find-dir-ent (cdr dir-ent-list)
                                                    filename))))))
      (fat32-in-memory
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname))))))))

;; Hypotheses minimised.
(defthm
  lofat-remove-file-correctness-1-lemma-9
  (implies
   (and
    (useful-dir-ent-list-p dir-ent-list)
    (<=
     2
     (dir-ent-first-cluster
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents
                  fat32-in-memory
                  (mv-nth 0
                          (find-dir-ent dir-ent-list filename1)))))
        filename2))))
    (<
     (dir-ent-first-cluster
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents
                  fat32-in-memory
                  (mv-nth 0
                          (find-dir-ent dir-ent-list filename1)))))
        filename2)))
     (+ 2 (count-of-clusters fat32-in-memory)))
    (equal
     (mv-nth
      1
      (update-dir-contents
       fat32-in-memory
       (dir-ent-first-cluster (mv-nth 0
                                      (find-dir-ent dir-ent-list filename1)))
       (nats=>string
        (clear-dir-ent
         (string=>nats
          (mv-nth 0
                  (dir-ent-clusterchain-contents
                   fat32-in-memory
                   (mv-nth 0
                           (find-dir-ent dir-ent-list filename1)))))
         filename2))))
     0)
    (equal
     (mv-nth
      1
      (find-dir-ent
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents
                 fat32-in-memory
                 (mv-nth 0
                         (find-dir-ent dir-ent-list filename1)))))
       filename2))
     0)
    (lofat-fs-p fat32-in-memory)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32-in-memory
                                          dir-ent-list entry-limit))
           0)
    (dir-ent-directory-p (mv-nth 0
                                 (find-dir-ent dir-ent-list filename1))))
   (not-intersectp-list
    (mv-nth
     0
     (dir-ent-clusterchain
      fat32-in-memory
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents
                  fat32-in-memory
                  (mv-nth 0
                          (find-dir-ent dir-ent-list filename1)))))
        filename2))))
    (mv-nth
     2
     (lofat-to-hifat-helper
      (mv-nth
       0
       (update-dir-contents
        fat32-in-memory
        (dir-ent-first-cluster (mv-nth 0
                                       (find-dir-ent dir-ent-list filename1)))
        (nats=>string
         (clear-dir-ent
          (string=>nats
           (mv-nth 0
                   (dir-ent-clusterchain-contents
                    fat32-in-memory
                    (mv-nth 0
                            (find-dir-ent dir-ent-list filename1)))))
          filename2))))
      dir-ent-list entry-limit))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lofat-to-hifat-helper lofat-to-hifat-helper-correctness-4
                            not-intersectp-list)
     (nth-of-effective-fat
      (:definition binary-append)
      (:rewrite remove-assoc-when-absent)
      (:definition len)
      (:rewrite lofat-to-hifat-helper-of-update-dir-contents)
      (:linear lofat-to-hifat-helper-correctness-3)
      (:linear lofat-find-file-correctness-1-lemma-11)
      (:rewrite lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2
                . 2)
      (:rewrite member-intersectp-binary-append . 1)
      (:rewrite subdir-contents-p-when-zero-length)
      (:rewrite flatten-subset-no-duplicatesp-lemma-2)
      (:rewrite member-intersectp-is-commutative-lemma-2)
      (:rewrite lofat-to-hifat-helper-of-delete-dir-ent-2
                . 1)
      (:rewrite
       get-clusterchain-contents-of-lofat-remove-file-coincident-lemma-5
       . 2)
      (:rewrite consp-of-make-list-ac)
      (:definition delete-dir-ent)
      (:rewrite delete-dir-ent-correctness-1)
      (:definition non-free-index-list-listp)
      (:definition remove-assoc-equal)
      (:rewrite subsetp-of-binary-append-3)
      (:linear count-free-clusters-correctness-1)
      (:linear make-clusters-correctness-2)
      (:rewrite clear-clusterchain-reversibility-lemma-1)
      (:linear non-free-index-listp-correctness-6-lemma-3)
      (:rewrite len-of-effective-fat)
      (:definition make-list-ac)))
    :induct (lofat-to-hifat-helper fat32-in-memory
                                   dir-ent-list entry-limit)
    :do-not-induct t
    :expand ((:free (y) (intersectp-equal nil y))
             (:free (fat32-in-memory entry-limit)
                    (lofat-to-hifat-helper fat32-in-memory
                                           dir-ent-list entry-limit))))))

(defthmd
  lofat-remove-file-correctness-1-lemma-37
  (implies
   (and
    (syntaxp (variablep entry-limit))
    (not (zp entry-limit))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-remove-file fat32-in-memory (car dir-ent-list)
                                  pathname))
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
       entry-limit))
     0)
    (<
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-remove-file fat32-in-memory (car dir-ent-list)
                                   pathname))
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
        entry-limit)))
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32-in-memory
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
        (+ -1 entry-limit))))))
   (equal
    (lofat-to-hifat-helper
     (mv-nth 0
             (lofat-remove-file fat32-in-memory (car dir-ent-list)
                                pathname))
     (make-dir-ent-list
      (mv-nth
       0
       (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
     (+ -1 entry-limit))
    (lofat-to-hifat-helper
     (mv-nth 0
             (lofat-remove-file fat32-in-memory (car dir-ent-list)
                                pathname))
     (make-dir-ent-list
      (mv-nth
       0
       (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
     entry-limit)))
  :hints
  (("goal"
    :use
    (:instance
     lofat-to-hifat-helper-correctness-4
     (entry-limit1 entry-limit)
     (entry-limit2 (+ -1 entry-limit))
     (dir-ent-list
      (make-dir-ent-list
       (mv-nth
        0
        (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list)))))
     (fat32-in-memory
      (mv-nth 0
              (lofat-remove-file fat32-in-memory (car dir-ent-list)
                                 pathname)))))))

(defthmd
  lofat-remove-file-correctness-1-lemma-38
  (implies
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname))
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents
                 fat32-in-memory
                 (mv-nth 0
                         (find-dir-ent (cdr dir-ent-list)
                                       filename)))))
       entry-limit))
     0)
    (useful-dir-ent-list-p dir-ent-list)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit))))))))
     0)
    (dir-ent-directory-p (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename)))
    (<
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-remove-file fat32-in-memory
                                   (mv-nth 0
                                           (find-dir-ent (cdr dir-ent-list)
                                                         filename))
                                   pathname))
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents
                  fat32-in-memory
                  (mv-nth 0
                          (find-dir-ent (cdr dir-ent-list)
                                        filename)))))
        entry-limit)))
     (hifat-entry-count
      (mv-nth 0
              (lofat-to-hifat-helper
               fat32-in-memory
               (make-dir-ent-list
                (mv-nth 0
                        (dir-ent-clusterchain-contents
                         fat32-in-memory
                         (mv-nth 0
                                 (find-dir-ent (cdr dir-ent-list)
                                               filename)))))
               entry-limit)))))
   (equal
    (lofat-to-hifat-helper
     (mv-nth 0
             (lofat-remove-file fat32-in-memory
                                (mv-nth 0
                                        (find-dir-ent (cdr dir-ent-list)
                                                      filename))
                                pathname))
     (make-dir-ent-list
      (mv-nth
       0
       (dir-ent-clusterchain-contents fat32-in-memory
                                      (mv-nth 0
                                              (find-dir-ent (cdr dir-ent-list)
                                                            filename)))))
     (+
      -1 entry-limit
      (-
       (hifat-entry-count
        (mv-nth 0
                (lofat-to-hifat-helper
                 fat32-in-memory
                 (make-dir-ent-list
                  (mv-nth 0
                          (dir-ent-clusterchain-contents
                           fat32-in-memory (car dir-ent-list))))
                 (+ -1 entry-limit)))))))
    (lofat-to-hifat-helper
     (mv-nth 0
             (lofat-remove-file fat32-in-memory
                                (mv-nth 0
                                        (find-dir-ent (cdr dir-ent-list)
                                                      filename))
                                pathname))
     (make-dir-ent-list
      (mv-nth
       0
       (dir-ent-clusterchain-contents fat32-in-memory
                                      (mv-nth 0
                                              (find-dir-ent (cdr dir-ent-list)
                                                            filename)))))
     entry-limit)))
  :hints
  (("goal"
    :use
    ((:instance
      lofat-to-hifat-helper-correctness-4
      (entry-limit1 entry-limit)
      (entry-limit2
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))
      (dir-ent-list (make-dir-ent-list
                     (mv-nth 0
                             (dir-ent-clusterchain-contents
                              fat32-in-memory
                              (mv-nth 0
                                      (find-dir-ent (cdr dir-ent-list)
                                                    filename))))))
      (fat32-in-memory
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname))))
     (:instance
      lofat-to-hifat-helper-correctness-4
      (entry-limit1
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))
      (entry-limit2 entry-limit)
      (dir-ent-list (make-dir-ent-list
                     (mv-nth 0
                             (dir-ent-clusterchain-contents
                              fat32-in-memory
                              (mv-nth 0
                                      (find-dir-ent (cdr dir-ent-list)
                                                    filename)))))))
     (:instance
      lofat-to-hifat-helper-correctness-4
      (entry-limit1 entry-limit)
      (entry-limit2
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))
      (dir-ent-list (make-dir-ent-list
                     (mv-nth 0
                             (dir-ent-clusterchain-contents
                              fat32-in-memory
                              (mv-nth 0
                                      (find-dir-ent (cdr dir-ent-list)
                                                    filename))))))
      (fat32-in-memory
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname))))
     (:instance
      (:linear lofat-to-hifat-helper-correctness-3)
      (entry-limit
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))
      (dir-ent-list (make-dir-ent-list
                     (mv-nth 0
                             (dir-ent-clusterchain-contents
                              fat32-in-memory
                              (mv-nth 0
                                      (find-dir-ent (cdr dir-ent-list)
                                                    filename))))))
      (fat32-in-memory fat32-in-memory))))))

(defthm
  lofat-remove-file-correctness-1-lemma-48
  (implies
   (not
    (member-intersectp-equal
     (mv-nth
      2
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname))
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents
                 fat32-in-memory
                 (mv-nth 0
                         (find-dir-ent (cdr dir-ent-list)
                                       filename)))))
       entry-limit))
     (cons
      (mv-nth 0
              (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
      (append
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32-in-memory
         (make-dir-ent-list (mv-nth 0
                                    (dir-ent-clusterchain-contents
                                     fat32-in-memory (car dir-ent-list))))
         (+ -1 entry-limit)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32-in-memory
         (delete-dir-ent (cdr dir-ent-list)
                         filename)
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
                       (dir-ent-clusterchain-contents
                        fat32-in-memory (car dir-ent-list))))
              (+ -1 entry-limit))))))))))))
   (not
    (member-intersectp-equal
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list))))
       (+ -1 entry-limit)))
     (mv-nth
      2
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (mv-nth 0
                                          (find-dir-ent (cdr dir-ent-list)
                                                        filename))
                                  pathname))
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents
                 fat32-in-memory
                 (mv-nth 0
                         (find-dir-ent (cdr dir-ent-list)
                                       filename)))))
       entry-limit)))))
  :hints
  (("goal"
    :in-theory (disable member-intersectp-is-commutative)
    :use
    ((:instance
      (:rewrite member-intersectp-is-commutative)
      (y
       (cons
        (mv-nth 0
                (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
        (append
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  (make-dir-ent-list
                   (mv-nth 0
                           (dir-ent-clusterchain-contents
                            fat32-in-memory (car dir-ent-list))))
                  (+ -1 entry-limit)))
         (mv-nth
          2
          (lofat-to-hifat-helper
           fat32-in-memory
           (delete-dir-ent (cdr dir-ent-list)
                           filename)
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
                         (dir-ent-clusterchain-contents
                          fat32-in-memory (car dir-ent-list))))
                (+ -1 entry-limit)))))))))))
      (x
       (mv-nth
        2
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-remove-file fat32-in-memory
                                    (mv-nth 0
                                            (find-dir-ent (cdr dir-ent-list)
                                                          filename))
                                    pathname))
         (make-dir-ent-list
          (mv-nth 0
                  (dir-ent-clusterchain-contents
                   fat32-in-memory
                   (mv-nth 0
                           (find-dir-ent (cdr dir-ent-list)
                                         filename)))))
         entry-limit))))))))

(encapsulate
  ()

  (local
   (defun-nx
     induction-scheme
     (dir-ent-list entry-limit fat32-in-memory x)
     (cond
      ((and
        (not (atom dir-ent-list))
        (not (zp entry-limit))
        (dir-ent-directory-p (car dir-ent-list))
        (>= (dir-ent-first-cluster (car dir-ent-list))
            2)
        (> (+ (count-of-clusters fat32-in-memory)
              2)
           (dir-ent-first-cluster (car dir-ent-list))))
       (induction-scheme
        (cdr dir-ent-list)
        (+
         entry-limit
         (-
          (+
           1
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32-in-memory
              (make-dir-ent-list
               (mv-nth 0
                       (dir-ent-clusterchain-contents
                        fat32-in-memory (car dir-ent-list))))
              (+ -1 entry-limit)))))))
        fat32-in-memory
        (append
         (mv-nth 0
                 (dir-ent-clusterchain
                  fat32-in-memory (car dir-ent-list)))
         (flatten
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32-in-memory
            (make-dir-ent-list
             (mv-nth 0
                     (dir-ent-clusterchain-contents
                      fat32-in-memory (car dir-ent-list))))
            (+ -1 entry-limit))))
         x)))
      ((and
        (not (atom dir-ent-list))
        (not (zp entry-limit))
        ;; (not (dir-ent-directory-p (car dir-ent-list)))
        (>= (dir-ent-first-cluster (car dir-ent-list))
            2)
        (> (+ (count-of-clusters fat32-in-memory)
              2)
           (dir-ent-first-cluster (car dir-ent-list))))
       (induction-scheme
        (cdr dir-ent-list)
        (- entry-limit 1)
        fat32-in-memory
        (append
         (mv-nth 0
                 (dir-ent-clusterchain
                  fat32-in-memory (car dir-ent-list)))
         x)))
      ((and
        (not (atom dir-ent-list))
        (not (zp entry-limit)))
       (induction-scheme
        (cdr dir-ent-list)
        (- entry-limit 1)
        fat32-in-memory
        x))
      (t
       (mv dir-ent-list entry-limit fat32-in-memory x)))))

  (defthm
    lofat-remove-file-correctness-1-lemma-2
    (implies
     (and
      (lofat-fs-p fat32-in-memory)
      (useful-dir-ent-list-p dir-ent-list)
      (fat32-filename-p filename1)
      (fat32-filename-p filename2)
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32-in-memory
                                            dir-ent-list entry-limit))
             0)
      (dir-ent-directory-p (mv-nth 0
                                   (find-dir-ent dir-ent-list filename1)))
      (equal
       (mv-nth
        1
        (find-dir-ent
         (make-dir-ent-list
          (mv-nth 0
                  (dir-ent-clusterchain-contents
                   fat32-in-memory
                   (mv-nth 0
                           (find-dir-ent dir-ent-list filename1)))))
         filename2))
       0)
      (equal
       (mv-nth
        1
        (update-dir-contents
         fat32-in-memory
         (dir-ent-first-cluster (mv-nth 0
                                        (find-dir-ent dir-ent-list filename1)))
         (nats=>string
          (clear-dir-ent
           (string=>nats
            (mv-nth 0
                    (dir-ent-clusterchain-contents
                     fat32-in-memory
                     (mv-nth 0
                             (find-dir-ent dir-ent-list filename1)))))
           filename2))))
       0)
      (non-free-index-listp x (effective-fat fat32-in-memory))
      (not-intersectp-list
       x
       (mv-nth 2
               (lofat-to-hifat-helper fat32-in-memory
                                      dir-ent-list entry-limit))))
     (and
      (equal
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth
          0
          (update-dir-contents
           fat32-in-memory
           (dir-ent-first-cluster (mv-nth 0
                                          (find-dir-ent dir-ent-list filename1)))
           (nats=>string
            (clear-dir-ent
             (string=>nats
              (mv-nth 0
                      (dir-ent-clusterchain-contents
                       fat32-in-memory
                       (mv-nth 0
                               (find-dir-ent dir-ent-list filename1)))))
             filename2))))
         dir-ent-list entry-limit))
       (put-assoc-equal
        filename1
        (m1-file
         (mv-nth 0 (find-dir-ent dir-ent-list filename1))
         (remove-assoc-equal
          filename2
          (mv-nth
           0
           (lofat-to-hifat-helper
            fat32-in-memory
            (make-dir-ent-list
             (mv-nth 0
                     (dir-ent-clusterchain-contents
                      fat32-in-memory
                      (mv-nth 0
                              (find-dir-ent dir-ent-list filename1)))))
            entry-limit))))
        (mv-nth 0
                (lofat-to-hifat-helper fat32-in-memory
                                       dir-ent-list entry-limit))))
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         (mv-nth
          0
          (update-dir-contents
           fat32-in-memory
           (dir-ent-first-cluster (mv-nth 0
                                          (find-dir-ent dir-ent-list filename1)))
           (nats=>string
            (clear-dir-ent
             (string=>nats
              (mv-nth 0
                      (dir-ent-clusterchain-contents
                       fat32-in-memory
                       (mv-nth 0
                               (find-dir-ent dir-ent-list filename1)))))
             filename2))))
         dir-ent-list entry-limit))
       0)
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         (mv-nth
          0
          (update-dir-contents
           fat32-in-memory
           (dir-ent-first-cluster (mv-nth 0
                                          (find-dir-ent dir-ent-list filename1)))
           (nats=>string
            (clear-dir-ent
             (string=>nats
              (mv-nth 0
                      (dir-ent-clusterchain-contents
                       fat32-in-memory
                       (mv-nth 0
                               (find-dir-ent dir-ent-list filename1)))))
             filename2))))
         dir-ent-list entry-limit)))))
    :hints
    (("goal"
      :in-theory
      (e/d (lofat-to-hifat-helper lofat-to-hifat-helper-correctness-4
                                  not-intersectp-list)
           (nth-of-effective-fat
            (:linear lofat-find-file-correctness-1-lemma-11)
            (:rewrite
             lofat-to-hifat-helper-of-update-dir-contents)))
      :induct
      (induction-scheme
       dir-ent-list entry-limit fat32-in-memory x)
      :expand (:free (fat32-in-memory entry-limit)
                     (lofat-to-hifat-helper fat32-in-memory
                                            dir-ent-list entry-limit))))
    :rule-classes
    ((:rewrite
      :corollary
      (implies
       (and
        (lofat-fs-p fat32-in-memory)
        (useful-dir-ent-list-p dir-ent-list)
        (fat32-filename-p filename1)
        (fat32-filename-p filename2)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32-in-memory
                                              dir-ent-list entry-limit))
               0)
        (dir-ent-directory-p (mv-nth 0
                                     (find-dir-ent dir-ent-list filename1)))
        (equal
         (mv-nth
          1
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth 0
                    (dir-ent-clusterchain-contents
                     fat32-in-memory
                     (mv-nth 0
                             (find-dir-ent dir-ent-list filename1)))))
           filename2))
         0)
        (equal
         (mv-nth
          1
          (update-dir-contents
           fat32-in-memory
           (dir-ent-first-cluster (mv-nth 0
                                          (find-dir-ent dir-ent-list filename1)))
           (nats=>string
            (clear-dir-ent
             (string=>nats
              (mv-nth 0
                      (dir-ent-clusterchain-contents
                       fat32-in-memory
                       (mv-nth 0
                               (find-dir-ent dir-ent-list filename1)))))
             filename2))))
         0)
        (non-free-index-listp x (effective-fat fat32-in-memory))
        (not-intersectp-list
         x
         (mv-nth 2
                 (lofat-to-hifat-helper fat32-in-memory
                                        dir-ent-list entry-limit))))
       (not-intersectp-list
        x
        (mv-nth
         2
         (lofat-to-hifat-helper
          (mv-nth
           0
           (update-dir-contents
            fat32-in-memory
            (dir-ent-first-cluster (mv-nth 0
                                           (find-dir-ent dir-ent-list filename1)))
            (nats=>string
             (clear-dir-ent
              (string=>nats
               (mv-nth 0
                       (dir-ent-clusterchain-contents
                        fat32-in-memory
                        (mv-nth 0
                                (find-dir-ent dir-ent-list filename1)))))
              filename2))))
          dir-ent-list entry-limit)))))))

  (defthm
    lofat-remove-file-correctness-1-lemma-3
    (implies
     (and
      (consp (cdr pathname))
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         (mv-nth
          0
          (lofat-remove-file fat32-in-memory
                             (mv-nth 0 (find-dir-ent dir-ent-list filename))
                             pathname))
         (make-dir-ent-list
          (mv-nth 0
                  (dir-ent-clusterchain-contents
                   fat32-in-memory
                   (mv-nth 0
                           (find-dir-ent dir-ent-list filename)))))
         entry-limit))
       0)
      (not-intersectp-list
       (mv-nth
        0
        (dir-ent-clusterchain fat32-in-memory
                              (mv-nth 0
                                      (find-dir-ent dir-ent-list filename))))
       (mv-nth
        2
        (lofat-to-hifat-helper
         (mv-nth
          0
          (lofat-remove-file fat32-in-memory
                             (mv-nth 0 (find-dir-ent dir-ent-list filename))
                             pathname))
         (make-dir-ent-list
          (mv-nth 0
                  (dir-ent-clusterchain-contents
                   fat32-in-memory
                   (mv-nth 0
                           (find-dir-ent dir-ent-list filename)))))
         entry-limit)))
      (not
       (member-intersectp-equal
        (mv-nth 2
                (lofat-to-hifat-helper fat32-in-memory
                                       (delete-dir-ent dir-ent-list filename)
                                       entry-limit))
        (mv-nth
         2
         (lofat-to-hifat-helper
          (mv-nth
           0
           (lofat-remove-file fat32-in-memory
                              (mv-nth 0 (find-dir-ent dir-ent-list filename))
                              pathname))
          (make-dir-ent-list
           (mv-nth 0
                   (dir-ent-clusterchain-contents
                    fat32-in-memory
                    (mv-nth 0
                            (find-dir-ent dir-ent-list filename)))))
          entry-limit))))
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         (mv-nth
          0
          (lofat-remove-file fat32-in-memory
                             (mv-nth 0 (find-dir-ent dir-ent-list filename))
                             pathname))
         (make-dir-ent-list
          (mv-nth 0
                  (dir-ent-clusterchain-contents
                   fat32-in-memory
                   (mv-nth 0
                           (find-dir-ent dir-ent-list filename)))))
         entry-limit)))
      (lofat-fs-p fat32-in-memory)
      (useful-dir-ent-list-p dir-ent-list)
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32-in-memory
                                            dir-ent-list entry-limit))
             0)
      (fat32-filename-list-p pathname)
      (dir-ent-directory-p (mv-nth 0 (find-dir-ent dir-ent-list filename)))
      (< (dir-ent-first-cluster (mv-nth 0 (find-dir-ent dir-ent-list filename)))
         (+ 2 (count-of-clusters fat32-in-memory)))
      (not-intersectp-list
       x
       (mv-nth 2
               (lofat-to-hifat-helper fat32-in-memory
                                      dir-ent-list entry-limit)))
      (<
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          (mv-nth
           0
           (lofat-remove-file fat32-in-memory
                              (mv-nth 0 (find-dir-ent dir-ent-list filename))
                              pathname))
          (make-dir-ent-list
           (mv-nth 0
                   (dir-ent-clusterchain-contents
                    fat32-in-memory
                    (mv-nth 0
                            (find-dir-ent dir-ent-list filename)))))
          entry-limit)))
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (mv-nth 0
                   (dir-ent-clusterchain-contents
                    fat32-in-memory
                    (mv-nth 0
                            (find-dir-ent dir-ent-list filename)))))
          entry-limit)))))
     (and
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         (mv-nth
          0
          (lofat-remove-file fat32-in-memory
                             (mv-nth 0 (find-dir-ent dir-ent-list filename))
                             pathname))
         dir-ent-list entry-limit))
       0)
      (equal
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth
          0
          (lofat-remove-file fat32-in-memory
                             (mv-nth 0 (find-dir-ent dir-ent-list filename))
                             pathname))
         dir-ent-list entry-limit))
       (put-assoc-equal
        filename
        (m1-file
         (mv-nth 0 (find-dir-ent dir-ent-list filename))
         (mv-nth
          0
          (lofat-to-hifat-helper
           (mv-nth
            0
            (lofat-remove-file fat32-in-memory
                               (mv-nth 0 (find-dir-ent dir-ent-list filename))
                               pathname))
           (make-dir-ent-list
            (mv-nth 0
                    (dir-ent-clusterchain-contents
                     fat32-in-memory
                     (mv-nth 0
                             (find-dir-ent dir-ent-list filename)))))
           entry-limit)))
        (mv-nth 0
                (lofat-to-hifat-helper fat32-in-memory
                                       dir-ent-list entry-limit))))
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         (mv-nth
          0
          (lofat-remove-file fat32-in-memory
                             (mv-nth 0 (find-dir-ent dir-ent-list filename))
                             pathname))
         dir-ent-list entry-limit)))))
    :hints
    (("goal"
      :do-not-induct t
      :induct (induction-scheme dir-ent-list
                                entry-limit fat32-in-memory x)
      :in-theory
      (e/d
       (lofat-to-hifat-helper lofat-to-hifat-helper-correctness-4
                              hifat-entry-count useful-dir-ent-list-p
                              lofat-remove-file-correctness-1-lemma-61
                              lofat-remove-file-correctness-1-lemma-37
                              lofat-remove-file-correctness-1-lemma-38)
       (lofat-remove-file
        nth-of-effective-fat
        (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
        (:definition no-duplicatesp-equal)
        (:definition hifat-file-alist-fix)
        (:rewrite lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2
                  . 1)
        (:rewrite assoc-of-car-when-member)
        (:rewrite subsetp-car-member)
        (:definition binary-append)
        (:rewrite dir-ent-clusterchain-contents-of-lofat-remove-file-disjoint)
        (:rewrite dir-ent-clusterchain-of-lofat-remove-file-disjoint)
        (:rewrite take-of-len-free)
        (:rewrite assoc-equal-when-member-equal)
        (:rewrite
         dir-ent-clusterchain-contents-of-lofat-remove-file-disjoint-lemma-2)
        (:rewrite dir-ent-p-when-member-equal-of-dir-ent-list-p)
        (:rewrite lofat-to-hifat-helper-of-delete-dir-ent-2
                  . 2)
        (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-1
                  . 1)
        (:rewrite hifat-to-lofat-inversion-lemma-2)
        (:definition assoc-equal)
        (:rewrite not-intersectp-list-when-atom)
        (:rewrite subdir-contents-p-when-zero-length)
        (:rewrite hifat-no-dups-p-of-cdr)
        (:rewrite free-index-list-listp-correctness-1)
        (:rewrite m1-file-alist-p-when-subsetp-equal)
        (:rewrite hifat-subsetp-preserves-assoc-equal)
        (:linear hifat-entry-count-when-hifat-subsetp)
        (:rewrite lofat-remove-file-correctness-1-lemma-53)
        (:rewrite remove-assoc-when-absent)
        (:definition remove-assoc-equal)
        (:linear lofat-remove-file-correctness-1-lemma-27)
        (:definition alistp)
        (:rewrite m1-file-alist-p-of-remove-assoc-equal)
        (:definition len)
        (:definition take)
        (:rewrite m1-file-alist-p-of-lofat-to-hifat-helper-lemma-1)))
      :expand ((:free (fat32-in-memory entry-limit)
                      (lofat-to-hifat-helper fat32-in-memory
                                             dir-ent-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (intersectp-equal nil x))))
    :rule-classes
    ((:rewrite
      :corollary
      (implies
       (and
        (consp (cdr pathname))
        (equal
         (mv-nth
          3
          (lofat-to-hifat-helper
           (mv-nth
            0
            (lofat-remove-file fat32-in-memory
                               (mv-nth 0 (find-dir-ent dir-ent-list filename))
                               pathname))
           (make-dir-ent-list
            (mv-nth 0
                    (dir-ent-clusterchain-contents
                     fat32-in-memory
                     (mv-nth 0
                             (find-dir-ent dir-ent-list filename)))))
           entry-limit))
         0)
        (not-intersectp-list
         (mv-nth
          0
          (dir-ent-clusterchain fat32-in-memory
                                (mv-nth 0
                                        (find-dir-ent dir-ent-list filename))))
         (mv-nth
          2
          (lofat-to-hifat-helper
           (mv-nth
            0
            (lofat-remove-file fat32-in-memory
                               (mv-nth 0 (find-dir-ent dir-ent-list filename))
                               pathname))
           (make-dir-ent-list
            (mv-nth 0
                    (dir-ent-clusterchain-contents
                     fat32-in-memory
                     (mv-nth 0
                             (find-dir-ent dir-ent-list filename)))))
           entry-limit)))
        (not
         (member-intersectp-equal
          (mv-nth 2
                  (lofat-to-hifat-helper fat32-in-memory
                                         (delete-dir-ent dir-ent-list filename)
                                         entry-limit))
          (mv-nth
           2
           (lofat-to-hifat-helper
            (mv-nth
             0
             (lofat-remove-file fat32-in-memory
                                (mv-nth 0 (find-dir-ent dir-ent-list filename))
                                pathname))
            (make-dir-ent-list
             (mv-nth 0
                     (dir-ent-clusterchain-contents
                      fat32-in-memory
                      (mv-nth 0
                              (find-dir-ent dir-ent-list filename)))))
            entry-limit))))
        (not-intersectp-list
         x
         (mv-nth
          2
          (lofat-to-hifat-helper
           (mv-nth
            0
            (lofat-remove-file fat32-in-memory
                               (mv-nth 0 (find-dir-ent dir-ent-list filename))
                               pathname))
           (make-dir-ent-list
            (mv-nth 0
                    (dir-ent-clusterchain-contents
                     fat32-in-memory
                     (mv-nth 0
                             (find-dir-ent dir-ent-list filename)))))
           entry-limit)))
        (lofat-fs-p fat32-in-memory)
        (useful-dir-ent-list-p dir-ent-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32-in-memory
                                              dir-ent-list entry-limit))
               0)
        (fat32-filename-list-p pathname)
        (dir-ent-directory-p (mv-nth 0 (find-dir-ent dir-ent-list filename)))
        (< (dir-ent-first-cluster (mv-nth 0 (find-dir-ent dir-ent-list filename)))
           (+ 2 (count-of-clusters fat32-in-memory)))
        (not-intersectp-list
         x
         (mv-nth 2
                 (lofat-to-hifat-helper fat32-in-memory
                                        dir-ent-list entry-limit)))
        (<
         (hifat-entry-count
          (mv-nth
           0
           (lofat-to-hifat-helper
            (mv-nth
             0
             (lofat-remove-file fat32-in-memory
                                (mv-nth 0 (find-dir-ent dir-ent-list filename))
                                pathname))
            (make-dir-ent-list
             (mv-nth 0
                     (dir-ent-clusterchain-contents
                      fat32-in-memory
                      (mv-nth 0
                              (find-dir-ent dir-ent-list filename)))))
            entry-limit)))
         (hifat-entry-count
          (mv-nth
           0
           (lofat-to-hifat-helper
            fat32-in-memory
            (make-dir-ent-list
             (mv-nth 0
                     (dir-ent-clusterchain-contents
                      fat32-in-memory
                      (mv-nth 0
                              (find-dir-ent dir-ent-list filename)))))
            entry-limit)))))
       (not-intersectp-list
        x
        (mv-nth
         2
         (lofat-to-hifat-helper
          (mv-nth
           0
           (lofat-remove-file fat32-in-memory
                              (mv-nth 0 (find-dir-ent dir-ent-list filename))
                              pathname))
          dir-ent-list entry-limit))))))))

(defthm
  lofat-remove-file-correctness-1-lemma-4
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (useful-dir-ent-list-p dir-ent-list)
    (fat32-filename-p filename1)
    (fat32-filename-p filename2)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32-in-memory
                                          dir-ent-list entry-limit))
           0)
    (dir-ent-directory-p (mv-nth 0
                                 (find-dir-ent dir-ent-list filename1)))
    (equal
     (mv-nth
      1
      (find-dir-ent
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents
                 fat32-in-memory
                 (mv-nth 0
                         (find-dir-ent dir-ent-list filename1)))))
       filename2))
     0)
    (equal
     (mv-nth
      1
      (update-dir-contents
       fat32-in-memory
       (dir-ent-first-cluster (mv-nth 0
                                      (find-dir-ent dir-ent-list filename1)))
       (nats=>string
        (clear-dir-ent
         (string=>nats
          (mv-nth 0
                  (dir-ent-clusterchain-contents
                   fat32-in-memory
                   (mv-nth 0
                           (find-dir-ent dir-ent-list filename1)))))
         filename2))))
     0))
   (and
    (equal
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth
        0
        (update-dir-contents
         fat32-in-memory
         (dir-ent-first-cluster (mv-nth 0
                                        (find-dir-ent dir-ent-list filename1)))
         (nats=>string
          (clear-dir-ent
           (string=>nats
            (mv-nth 0
                    (dir-ent-clusterchain-contents
                     fat32-in-memory
                     (mv-nth 0
                             (find-dir-ent dir-ent-list filename1)))))
           filename2))))
       dir-ent-list entry-limit))
     (put-assoc-equal
      filename1
      (m1-file
       (mv-nth 0 (find-dir-ent dir-ent-list filename1))
       (remove-assoc-equal
        filename2
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (mv-nth 0
                   (dir-ent-clusterchain-contents
                    fat32-in-memory
                    (mv-nth 0
                            (find-dir-ent dir-ent-list filename1)))))
          entry-limit))))
      (mv-nth 0
              (lofat-to-hifat-helper fat32-in-memory
                                     dir-ent-list entry-limit))))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth
        0
        (update-dir-contents
         fat32-in-memory
         (dir-ent-first-cluster (mv-nth 0
                                        (find-dir-ent dir-ent-list filename1)))
         (nats=>string
          (clear-dir-ent
           (string=>nats
            (mv-nth 0
                    (dir-ent-clusterchain-contents
                     fat32-in-memory
                     (mv-nth 0
                             (find-dir-ent dir-ent-list filename1)))))
           filename2))))
       dir-ent-list entry-limit))
     0)))
  :hints
  (("goal" :in-theory (disable
                       lofat-remove-file-correctness-1-lemma-2)
    :use (:instance
          lofat-remove-file-correctness-1-lemma-2
          (x nil)))))

;; The hypotheses for this lemma have been trimmed to the extent that
;; remove-hyps can handle.
(defthm
  lofat-remove-file-correctness-1-lemma-5
  (implies
   (and
    (consp (cdr pathname))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-remove-file fat32-in-memory
                           (mv-nth 0 (find-dir-ent dir-ent-list filename))
                           pathname))
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents
                 fat32-in-memory
                 (mv-nth 0
                         (find-dir-ent dir-ent-list filename)))))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth
      0
      (dir-ent-clusterchain fat32-in-memory
                            (mv-nth 0
                                    (find-dir-ent dir-ent-list filename))))
     (mv-nth
      2
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-remove-file fat32-in-memory
                           (mv-nth 0 (find-dir-ent dir-ent-list filename))
                           pathname))
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents
                 fat32-in-memory
                 (mv-nth 0
                         (find-dir-ent dir-ent-list filename)))))
       entry-limit)))
    (not
     (member-intersectp-equal
      (mv-nth 2
              (lofat-to-hifat-helper fat32-in-memory
                                     (delete-dir-ent dir-ent-list filename)
                                     entry-limit))
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth
         0
         (lofat-remove-file fat32-in-memory
                            (mv-nth 0 (find-dir-ent dir-ent-list filename))
                            pathname))
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents
                  fat32-in-memory
                  (mv-nth 0
                          (find-dir-ent dir-ent-list filename)))))
        entry-limit))))
    (lofat-fs-p fat32-in-memory)
    (useful-dir-ent-list-p dir-ent-list)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32-in-memory
                                          dir-ent-list entry-limit))
           0)
    (fat32-filename-list-p pathname)
    (dir-ent-directory-p (mv-nth 0 (find-dir-ent dir-ent-list filename)))
    (<
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth
         0
         (lofat-remove-file fat32-in-memory
                            (mv-nth 0 (find-dir-ent dir-ent-list filename))
                            pathname))
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents
                  fat32-in-memory
                  (mv-nth 0
                          (find-dir-ent dir-ent-list filename)))))
        entry-limit)))
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32-in-memory
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents
                  fat32-in-memory
                  (mv-nth 0
                          (find-dir-ent dir-ent-list filename)))))
        entry-limit)))))
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-remove-file fat32-in-memory
                           (mv-nth 0 (find-dir-ent dir-ent-list filename))
                           pathname))
       dir-ent-list entry-limit))
     0)
    (equal
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-remove-file fat32-in-memory
                           (mv-nth 0 (find-dir-ent dir-ent-list filename))
                           pathname))
       dir-ent-list entry-limit))
     (put-assoc-equal
      filename
      (m1-file
       (mv-nth 0 (find-dir-ent dir-ent-list filename))
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth
          0
          (lofat-remove-file fat32-in-memory
                             (mv-nth 0 (find-dir-ent dir-ent-list filename))
                             pathname))
         (make-dir-ent-list
          (mv-nth 0
                  (dir-ent-clusterchain-contents
                   fat32-in-memory
                   (mv-nth 0
                           (find-dir-ent dir-ent-list filename)))))
         entry-limit)))
      (mv-nth 0
              (lofat-to-hifat-helper fat32-in-memory
                                     dir-ent-list entry-limit))))))
  :hints (("goal" :in-theory (disable lofat-remove-file-correctness-1-lemma-3)
           :use (:instance lofat-remove-file-correctness-1-lemma-3
                           (x nil)))))

(defthm
  lofat-remove-file-correctness-1-lemma-63
  (implies
   (and
    (<= 2 (dir-ent-first-cluster dir-ent))
    (equal (mv-nth 1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
           0))
   (member-equal (dir-ent-first-cluster dir-ent)
                 (mv-nth 0
                         (dir-ent-clusterchain fat32-in-memory dir-ent))))
  :hints (("goal" :in-theory (enable dir-ent-clusterchain
                                     dir-ent-clusterchain-contents))))

(defthm
  lofat-remove-file-correctness-1-lemma-60
  (implies
   (and (dir-ent-p dir-ent)
        (< (dir-ent-first-cluster dir-ent)
           (len (effective-fat fat32-in-memory))))
   (bounded-nat-listp (mv-nth '0
                              (dir-ent-clusterchain fat32-in-memory dir-ent))
                      (binary-+ '2
                                (count-of-clusters fat32-in-memory))))
  :hints (("goal" :in-theory (enable dir-ent-clusterchain))))

(defthm
  lofat-remove-file-correctness-1-lemma-64
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (dir-ent-p dir-ent)
    (dir-ent-directory-p dir-ent)
    (<= *ms-first-data-cluster*
        (dir-ent-first-cluster dir-ent))
    (> (+ *ms-first-data-cluster*
          (count-of-clusters fat32-in-memory))
       (dir-ent-first-cluster dir-ent))
    (stringp dir-contents)
    (equal (mv-nth 1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
           0)
    (no-duplicatesp-equal
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory dir-ent))))
   (equal
    (mv-nth 1
            (update-dir-contents fat32-in-memory
                                 (dir-ent-first-cluster dir-ent)
                                 dir-contents))
    (if
     (and (< 0 (len (explode dir-contents)))
          (< (+ (count-free-clusters (effective-fat fat32-in-memory))
                (len (mv-nth 0
                             (dir-ent-clusterchain fat32-in-memory dir-ent))))
             (len (make-clusters dir-contents
                                 (cluster-size fat32-in-memory)))))
     *enospc* 0)))
  :hints
  (("goal"
    :in-theory
    (enable
     update-dir-contents
     dir-ent-clusterchain-contents
     (:rewrite
      get-clusterchain-contents-of-update-dir-contents-coincident-lemma-2)
     clear-clusterchain-correctness-1))))

(defthm
  lofat-remove-file-correctness-1-lemma-65
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (equal (mv-nth 1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
           0))
   (equal
    (floor
     (+
      -1 (cluster-size fat32-in-memory)
      (len
       (explode
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))))
     (cluster-size fat32-in-memory))
    (len (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory dir-ent)))))
  :hints
  (("goal"
    :in-theory (enable dir-ent-clusterchain-contents dir-ent-clusterchain))))

;; Hypotheses minimised.
(defthm
  lofat-remove-file-correctness-1-lemma-66
  (b*
      (((mv & error-code)
        (hifat-remove-file
         (mv-nth 0
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  (make-dir-ent-list
                   (mv-nth 0 (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
                  entry-limit))
         pathname)))
    (implies
     (and
      (lofat-fs-p fat32-in-memory)
      (dir-ent-p root-dir-ent)
      (dir-ent-directory-p root-dir-ent)
      (equal (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32-in-memory
                      (make-dir-ent-list
                       (mv-nth 0 (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
                      entry-limit))
             0)
      (<= *ms-first-data-cluster* (dir-ent-first-cluster root-dir-ent))
      (< (dir-ent-first-cluster root-dir-ent)
         (+ *ms-first-data-cluster* (count-of-clusters fat32-in-memory)))
      (equal
       (mv-nth 1 (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent))
       0)
      (no-duplicatesp-equal
       (mv-nth '0
               (dir-ent-clusterchain fat32-in-memory root-dir-ent))))
      (equal
       (mv-nth
        1
        (lofat-remove-file fat32-in-memory root-dir-ent pathname))
       error-code)))
  :hints
  (("goal"
    :induct (lofat-remove-file fat32-in-memory root-dir-ent pathname)
    :expand
    (lofat-remove-file fat32-in-memory root-dir-ent pathname)
    :in-theory (enable hifat-remove-file
                       (:rewrite hifat-to-lofat-inversion-lemma-17)
                       (:rewrite lofat-to-hifat-inversion-lemma-4)))))

(defthm
  lofat-remove-file-correctness-1-lemma-67
  (implies
   (and
    (consp (cddr pathname))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-remove-file
         fat32-in-memory
         (mv-nth
          0
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth
             0
             (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
           (car pathname)))
         (cdr pathname)))
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              0
              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
            (car pathname))))))
       entry-limit))
     0)
    (equal
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-remove-file
         fat32-in-memory
         (mv-nth
          0
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth
             0
             (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
           (car pathname)))
         (cdr pathname)))
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              0
              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
            (car pathname))))))
       entry-limit))
     (mv-nth
      0
      (hifat-remove-file
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32-in-memory
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents
            fat32-in-memory
            (mv-nth
             0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
              (car pathname))))))
         entry-limit))
       (cdr pathname))))
    (not-intersectp-list
     (mv-nth
      0
      (dir-ent-clusterchain
       fat32-in-memory
       (mv-nth
        0
        (find-dir-ent
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
         (car pathname)))))
     (mv-nth
      2
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-remove-file
         fat32-in-memory
         (mv-nth
          0
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth
             0
             (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
           (car pathname)))
         (cdr pathname)))
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              0
              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
            (car pathname))))))
       entry-limit)))
    (not
     (member-intersectp-equal
      (mv-nth
       2
       (lofat-to-hifat-helper
        fat32-in-memory
        (delete-dir-ent
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
         (car pathname))
        entry-limit))
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth
         0
         (lofat-remove-file
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              0
              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
            (car pathname)))
          (cdr pathname)))
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents
           fat32-in-memory
           (mv-nth
            0
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth
               0
               (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
             (car pathname))))))
        entry-limit))))
    (lofat-fs-p fat32-in-memory)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit))
     0)
    (fat32-filename-list-p pathname)
    (dir-ent-directory-p
     (mv-nth
      0
      (find-dir-ent
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       (car pathname)))))
   (equal
    (mv-nth
     3
     (lofat-to-hifat-helper
      (mv-nth
       0
       (lofat-remove-file
        fat32-in-memory
        (mv-nth
         0
         (find-dir-ent
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
          (car pathname)))
        (cdr pathname)))
      (make-dir-ent-list
       (mv-nth 0
               (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
      entry-limit))
    0))
  :hints
  (("goal"
    :cases
    ((equal
      (mv-nth
       1
       (lofat-remove-file
        fat32-in-memory
        (mv-nth
         0
         (find-dir-ent
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
          (car pathname)))
        (cdr pathname)))
      0))
    :in-theory (disable (:rewrite lofat-remove-file-correctness-1-lemma-66))
    :use
    ((:instance
      (:rewrite lofat-remove-file-correctness-1-lemma-66)
      (pathname (cdr pathname))
      (root-dir-ent
       (mv-nth
        0
        (find-dir-ent
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
         (car pathname))))
      (fat32-in-memory fat32-in-memory))
     (:instance
      (:linear hifat-entry-count-of-hifat-remove-file)
      (pathname (cdr pathname))
      (fs
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32-in-memory
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents
            fat32-in-memory
            (mv-nth
             0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
              (car pathname))))))
         entry-limit))))))))

(defthm
  lofat-remove-file-correctness-1-lemma-68
  (implies
   (and
    (consp (cddr pathname))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-remove-file
         fat32-in-memory
         (mv-nth
          0
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth
             0
             (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
           (car pathname)))
         (cdr pathname)))
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              0
              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
            (car pathname))))))
       entry-limit))
     0)
    (equal
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-remove-file
         fat32-in-memory
         (mv-nth
          0
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth
             0
             (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
           (car pathname)))
         (cdr pathname)))
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              0
              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
            (car pathname))))))
       entry-limit))
     (mv-nth
      0
      (hifat-remove-file
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32-in-memory
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents
            fat32-in-memory
            (mv-nth
             0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
              (car pathname))))))
         entry-limit))
       (cdr pathname))))
    (not-intersectp-list
     (mv-nth
      0
      (dir-ent-clusterchain
       fat32-in-memory
       (mv-nth
        0
        (find-dir-ent
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
         (car pathname)))))
     (mv-nth
      2
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-remove-file
         fat32-in-memory
         (mv-nth
          0
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth
             0
             (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
           (car pathname)))
         (cdr pathname)))
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              0
              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
            (car pathname))))))
       entry-limit)))
    (not
     (member-intersectp-equal
      (mv-nth
       2
       (lofat-to-hifat-helper
        fat32-in-memory
        (delete-dir-ent
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
         (car pathname))
        entry-limit))
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth
         0
         (lofat-remove-file
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              0
              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
            (car pathname)))
          (cdr pathname)))
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents
           fat32-in-memory
           (mv-nth
            0
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth
               0
               (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
             (car pathname))))))
        entry-limit))))
    (not-intersectp-list
     x
     (mv-nth
      2
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-remove-file
         fat32-in-memory
         (mv-nth
          0
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth
             0
             (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
           (car pathname)))
         (cdr pathname)))
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              0
              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
            (car pathname))))))
       entry-limit)))
    (lofat-fs-p fat32-in-memory)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit))
     0)
    (fat32-filename-list-p pathname)
    (not-intersectp-list
     x
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit)))
    (dir-ent-directory-p
     (mv-nth
      0
      (find-dir-ent
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       (car pathname))))
    (<
     (dir-ent-first-cluster
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
        (car pathname))))
     (+ 2 (count-of-clusters fat32-in-memory))))
   (not-intersectp-list
    x
    (mv-nth
     2
     (lofat-to-hifat-helper
      (mv-nth
       0
       (lofat-remove-file
        fat32-in-memory
        (mv-nth
         0
         (find-dir-ent
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
          (car pathname)))
        (cdr pathname)))
      (make-dir-ent-list
       (mv-nth 0
               (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
      entry-limit))))
  :hints
  (("goal"
    :cases
    ((equal
      (mv-nth
       1
       (lofat-remove-file
        fat32-in-memory
        (mv-nth
         0
         (find-dir-ent
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
          (car pathname)))
        (cdr pathname)))
      0))
    :in-theory (disable (:rewrite lofat-remove-file-correctness-1-lemma-66))
    :use
    ((:instance
      (:rewrite lofat-remove-file-correctness-1-lemma-66)
      (pathname (cdr pathname))
      (root-dir-ent
       (mv-nth
        0
        (find-dir-ent
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
         (car pathname))))
      (fat32-in-memory fat32-in-memory))
     (:instance
      (:linear hifat-entry-count-of-hifat-remove-file)
      (pathname (cdr pathname))
      (fs
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32-in-memory
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents
            fat32-in-memory
            (mv-nth
             0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
              (car pathname))))))
         entry-limit))))))))

(defthm
  lofat-remove-file-correctness-1-lemma-69
  (implies
   (and
    (consp (cddr pathname))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-remove-file
         fat32-in-memory
         (mv-nth
          0
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth
             0
             (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
           (car pathname)))
         (cdr pathname)))
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              0
              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
            (car pathname))))))
       entry-limit))
     0)
    (equal
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-remove-file
         fat32-in-memory
         (mv-nth
          0
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth
             0
             (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
           (car pathname)))
         (cdr pathname)))
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              0
              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
            (car pathname))))))
       entry-limit))
     (mv-nth
      0
      (hifat-remove-file
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32-in-memory
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents
            fat32-in-memory
            (mv-nth
             0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
              (car pathname))))))
         entry-limit))
       (cdr pathname))))
    (not-intersectp-list
     (mv-nth
      0
      (dir-ent-clusterchain
       fat32-in-memory
       (mv-nth
        0
        (find-dir-ent
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
         (car pathname)))))
     (mv-nth
      2
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-remove-file
         fat32-in-memory
         (mv-nth
          0
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth
             0
             (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
           (car pathname)))
         (cdr pathname)))
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              0
              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
            (car pathname))))))
       entry-limit)))
    (not
     (member-intersectp-equal
      (mv-nth
       2
       (lofat-to-hifat-helper
        fat32-in-memory
        (delete-dir-ent
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
         (car pathname))
        entry-limit))
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth
         0
         (lofat-remove-file
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              0
              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
            (car pathname)))
          (cdr pathname)))
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents
           fat32-in-memory
           (mv-nth
            0
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth
               0
               (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
             (car pathname))))))
        entry-limit))))
    (lofat-fs-p fat32-in-memory)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit))
     0)
    (fat32-filename-list-p pathname)
    (dir-ent-directory-p
     (mv-nth
      0
      (find-dir-ent
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       (car pathname)))))
   (equal
    (mv-nth
     0
     (lofat-to-hifat-helper
      (mv-nth
       0
       (lofat-remove-file
        fat32-in-memory
        (mv-nth
         0
         (find-dir-ent
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
          (car pathname)))
        (cdr pathname)))
      (make-dir-ent-list
       (mv-nth 0
               (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
      entry-limit))
    (put-assoc-equal
     (car pathname)
     (m1-file
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
        (car pathname)))
      (mv-nth
       0
       (hifat-remove-file
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents
             fat32-in-memory
             (mv-nth
              0
              (find-dir-ent
               (make-dir-ent-list (mv-nth 0
                                          (dir-ent-clusterchain-contents
                                           fat32-in-memory root-dir-ent)))
               (car pathname))))))
          entry-limit))
        (cdr pathname))))
     (mv-nth
      0
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit)))))
  :hints
  (("goal"
    :cases
    ((equal
      (mv-nth
       1
       (hifat-remove-file
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents
             fat32-in-memory
             (mv-nth
              0
              (find-dir-ent
               (make-dir-ent-list (mv-nth 0
                                          (dir-ent-clusterchain-contents
                                           fat32-in-memory root-dir-ent)))
               (car pathname))))))
          entry-limit))
        (cdr pathname)))
      0))
    :in-theory (disable (:rewrite lofat-remove-file-correctness-2)
                        (:rewrite lofat-remove-file-correctness-1-lemma-66)
                        (:rewrite lofat-remove-file-correctness-1-lemma-5))
    :use
    ((:instance
      (:rewrite lofat-remove-file-correctness-2)
      (pathname (cdr pathname))
      (root-dir-ent
       (mv-nth
        0
        (find-dir-ent
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
         (car pathname))))
      (fat32-in-memory fat32-in-memory))
     (:instance
      (:rewrite lofat-remove-file-correctness-1-lemma-66)
      (pathname (cdr pathname))
      (root-dir-ent
       (mv-nth
        0
        (find-dir-ent
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
         (car pathname))))
      (fat32-in-memory fat32-in-memory))
     (:instance
      (:rewrite lofat-remove-file-correctness-1-lemma-5)
      (entry-limit entry-limit)
      (pathname (cdr pathname))
      (filename (car pathname))
      (dir-ent-list
       (make-dir-ent-list
        (mv-nth
         0
         (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent))))
      (fat32-in-memory fat32-in-memory))))))

(encapsulate
  ()

  (local
   (defun-nx
     induction-scheme
     (entry-limit fat32-in-memory pathname root-dir-ent x)
     (cond
      ((and
        (consp pathname)
        (equal
         (mv-nth
          1
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth 0
                    (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
           (fat32-filename-fix (car pathname))))
         0)
        (dir-ent-directory-p
         (mv-nth
          0
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth
             0
             (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
           (fat32-filename-fix (car pathname)))))
        (consp (cdr pathname)))
       (induction-scheme
        entry-limit
        fat32-in-memory (cdr pathname)
        (mv-nth
         0
         (find-dir-ent
          (make-dir-ent-list
           (mv-nth 0
                   (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
          (fat32-filename-fix (car pathname))))
        (append
         (mv-nth
          0
          (dir-ent-clusterchain
           fat32-in-memory
           (mv-nth
            0
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth 0
                      (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
             (fat32-filename-fix (car pathname))))))
         (flatten
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32-in-memory
            (delete-dir-ent
             (make-dir-ent-list
              (mv-nth 0
                      (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
             (fat32-filename-fix (car pathname)))
            entry-limit)))
         x)))
      (t
       (mv entry-limit fat32-in-memory pathname root-dir-ent x)))))

  ;; Hypotheses trimmed.
  (defthm
    lofat-remove-file-correctness-1-lemma-1
    (b*
        (((mv fs &)
          (hifat-remove-file
           (mv-nth 0
                   (lofat-to-hifat-helper
                    fat32-in-memory
                    (make-dir-ent-list
                     (mv-nth 0 (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
                    entry-limit))
           pathname)))
      (implies
       (and
        (lofat-fs-p fat32-in-memory)
        (dir-ent-p root-dir-ent)
        (dir-ent-directory-p root-dir-ent)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper
                        fat32-in-memory
                        (make-dir-ent-list
                         (mv-nth 0 (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
                        entry-limit))
               0)
        (<= *ms-first-data-cluster* (dir-ent-first-cluster root-dir-ent))
        (< (dir-ent-first-cluster root-dir-ent)
           (+ *ms-first-data-cluster* (count-of-clusters fat32-in-memory)))
        (fat32-filename-list-p pathname)
        (not-intersectp-list
         (mv-nth 0 (dir-ent-clusterchain fat32-in-memory root-dir-ent))
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  (make-dir-ent-list
                   (mv-nth 0 (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
                  entry-limit)))
        (equal
         (mv-nth 1 (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent))
         0)
        (no-duplicatesp-equal
         (mv-nth '0
                 (dir-ent-clusterchain fat32-in-memory root-dir-ent)))
        (non-free-index-listp x (effective-fat fat32-in-memory))
        (not-intersectp-list
         x
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  (make-dir-ent-list
                   (mv-nth 0 (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
                  entry-limit))))
       (and
        (equal
         (mv-nth 3
                 (lofat-to-hifat-helper
                  (mv-nth
                   0
                   (lofat-remove-file fat32-in-memory root-dir-ent pathname))
                  (make-dir-ent-list
                   (mv-nth 0
                           (dir-ent-clusterchain-contents
                            (mv-nth
                             0
                             (lofat-remove-file fat32-in-memory root-dir-ent pathname))
                            root-dir-ent)))
                  entry-limit))
         0)
        (equal
         (mv-nth 0
                 (lofat-to-hifat-helper
                  (mv-nth
                   0
                   (lofat-remove-file fat32-in-memory root-dir-ent pathname))
                  (make-dir-ent-list
                   (mv-nth 0
                           (dir-ent-clusterchain-contents
                            (mv-nth
                             0
                             (lofat-remove-file fat32-in-memory root-dir-ent pathname))
                            root-dir-ent)))
                  entry-limit))
         fs)
        (not-intersectp-list
         x
         (mv-nth 2
                 (lofat-to-hifat-helper
                  (mv-nth
                   0
                   (lofat-remove-file fat32-in-memory root-dir-ent pathname))
                  (make-dir-ent-list
                   (mv-nth 0
                           (dir-ent-clusterchain-contents
                            (mv-nth
                             0
                             (lofat-remove-file fat32-in-memory root-dir-ent pathname))
                            root-dir-ent)))
                  entry-limit))))))
    :hints
    (("goal"
      :induct
      (induction-scheme
       entry-limit fat32-in-memory pathname root-dir-ent x)
      :expand
      (lofat-remove-file fat32-in-memory root-dir-ent pathname)
      :in-theory (enable hifat-remove-file
                         (:rewrite hifat-to-lofat-inversion-lemma-17)
                         (:rewrite lofat-to-hifat-inversion-lemma-4))))
    :rule-classes
    ((:rewrite
      :corollary
      (b*
          (((mv & &)
            (hifat-remove-file
             (mv-nth 0
                     (lofat-to-hifat-helper
                      fat32-in-memory
                      (make-dir-ent-list
                       (mv-nth 0 (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
                      entry-limit))
             pathname)))
        (implies
         (and
          (lofat-fs-p fat32-in-memory)
          (dir-ent-p root-dir-ent)
          (dir-ent-directory-p root-dir-ent)
          (equal (mv-nth 3
                         (lofat-to-hifat-helper
                          fat32-in-memory
                          (make-dir-ent-list
                           (mv-nth 0 (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
                          entry-limit))
                 0)
          (<= *ms-first-data-cluster* (dir-ent-first-cluster root-dir-ent))
          (< (dir-ent-first-cluster root-dir-ent)
             (+ *ms-first-data-cluster* (count-of-clusters fat32-in-memory)))
          (fat32-filename-list-p pathname)
          (not-intersectp-list
           (mv-nth 0 (dir-ent-clusterchain fat32-in-memory root-dir-ent))
           (mv-nth 2
                   (lofat-to-hifat-helper
                    fat32-in-memory
                    (make-dir-ent-list
                     (mv-nth 0 (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
                    entry-limit)))
          (equal
           (mv-nth 1 (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent))
           0)
          (no-duplicatesp-equal
           (mv-nth '0
                   (dir-ent-clusterchain fat32-in-memory root-dir-ent)))
          (non-free-index-listp x (effective-fat fat32-in-memory))
          (not-intersectp-list
           x
           (mv-nth 2
                   (lofat-to-hifat-helper
                    fat32-in-memory
                    (make-dir-ent-list
                     (mv-nth 0 (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
                    entry-limit))))
         (not-intersectp-list
          x
          (mv-nth 2
                  (lofat-to-hifat-helper
                   (mv-nth
                    0
                    (lofat-remove-file fat32-in-memory root-dir-ent pathname))
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             (mv-nth
                              0
                              (lofat-remove-file fat32-in-memory root-dir-ent pathname))
                             root-dir-ent)))
                   entry-limit)))))))))

;; Hypotheses trimmed.
(defthm
  lofat-remove-file-correctness-1
  (b*
      (((mv fs &)
        (hifat-remove-file
         (mv-nth 0
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  (make-dir-ent-list
                   (mv-nth 0 (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
                  entry-limit))
         pathname)))
    (implies
     (and
      (lofat-fs-p fat32-in-memory)
      (dir-ent-p root-dir-ent)
      (dir-ent-directory-p root-dir-ent)
      (equal (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32-in-memory
                      (make-dir-ent-list
                       (mv-nth 0 (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
                      entry-limit))
             0)
      (<= *ms-first-data-cluster* (dir-ent-first-cluster root-dir-ent))
      (< (dir-ent-first-cluster root-dir-ent)
         (+ *ms-first-data-cluster* (count-of-clusters fat32-in-memory)))
      (fat32-filename-list-p pathname)
      (not-intersectp-list
       (mv-nth 0 (dir-ent-clusterchain fat32-in-memory root-dir-ent))
       (mv-nth 2
               (lofat-to-hifat-helper
                fat32-in-memory
                (make-dir-ent-list
                 (mv-nth 0 (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
                entry-limit)))
      (equal
       (mv-nth 1 (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent))
       0)
      (no-duplicatesp-equal
       (mv-nth '0
               (dir-ent-clusterchain fat32-in-memory root-dir-ent))))
     (and
      (equal
       (mv-nth 3
               (lofat-to-hifat-helper
                (mv-nth
                 0
                 (lofat-remove-file fat32-in-memory root-dir-ent pathname))
                (make-dir-ent-list
                 (mv-nth 0
                         (dir-ent-clusterchain-contents
                          (mv-nth
                           0
                           (lofat-remove-file fat32-in-memory root-dir-ent pathname))
                          root-dir-ent)))
                entry-limit))
       0)
      (equal
       (mv-nth 0
               (lofat-to-hifat-helper
                (mv-nth
                 0
                 (lofat-remove-file fat32-in-memory root-dir-ent pathname))
                (make-dir-ent-list
                 (mv-nth 0
                         (dir-ent-clusterchain-contents
                          (mv-nth
                           0
                           (lofat-remove-file fat32-in-memory root-dir-ent pathname))
                          root-dir-ent)))
                entry-limit))
       fs))))
  :hints
  (("goal"
    :in-theory (e/d (hifat-remove-file)
                    (lofat-remove-file-correctness-1-lemma-1))
    :use
    (:instance
     lofat-remove-file-correctness-1-lemma-1
     (x nil)))))

(defund
  insert-dir-ent (dir-contents dir-ent)
  (declare
   (xargs :measure (len dir-contents)
          :guard (and (dir-ent-p dir-ent)
                      (unsigned-byte-listp 8 dir-contents))
          :guard-hints (("goal" :in-theory (enable dir-ent-p)))
          :guard-debug t))
  (b*
      ((dir-ent (mbe :logic (dir-ent-fix dir-ent) :exec dir-ent))
       ((when (< (len dir-contents)
                 *ms-dir-ent-length*))
        (append dir-ent dir-contents))
       (head-dir-ent (take *ms-dir-ent-length* dir-contents))
       ((when (equal (dir-ent-filename head-dir-ent)
                     (dir-ent-filename dir-ent)))
        (append
         dir-ent
         (nthcdr *ms-dir-ent-length* dir-contents)))
       ((when (equal (char (dir-ent-filename head-dir-ent) 0)
                     (code-char 0)))
        (append dir-ent dir-contents)))
    (append
     head-dir-ent
     (insert-dir-ent (nthcdr *ms-dir-ent-length* dir-contents)
                     dir-ent))))

(defthm
  unsigned-byte-listp-of-insert-dir-ent
  (implies
   (unsigned-byte-listp 8 dir-contents)
   (unsigned-byte-listp 8
                        (insert-dir-ent dir-contents dir-ent)))
  :hints (("goal" :in-theory (enable insert-dir-ent))))

(defthm insert-dir-ent-of-dir-ent-fix
  (equal (insert-dir-ent dir-contents (dir-ent-fix dir-ent))
         (insert-dir-ent dir-contents dir-ent))
  :hints (("goal" :in-theory (enable insert-dir-ent))))

(defcong
  dir-ent-equiv equal
  (insert-dir-ent dir-contents dir-ent)
  2
  :hints
  (("goal"
    :in-theory
    (disable (:rewrite insert-dir-ent-of-dir-ent-fix))
    :use ((:rewrite insert-dir-ent-of-dir-ent-fix)
          (:instance (:rewrite insert-dir-ent-of-dir-ent-fix)
                     (dir-ent dir-ent-equiv))))))

(defthm len-of-insert-dir-ent-lemma-1
  (implies (and (not (useless-dir-ent-p (dir-ent-fix dir-ent)))
                (useless-dir-ent-p (take 32 dir-contents)))
           (not (equal (dir-ent-filename (take 32 dir-contents))
                       (dir-ent-filename dir-ent))))
  :hints (("goal" :in-theory (enable useless-dir-ent-p))))

(defthm
  len-of-insert-dir-ent-lemma-2
  (implies
   (and (equal (dir-ent-filename (take 32 dir-contents))
               (dir-ent-filename dir-ent))
        (unsigned-byte-listp 8 dir-contents)
        (not (useless-dir-ent-p (dir-ent-fix dir-ent)))
        (not (equal (nth 0 (explode (dir-ent-filename dir-ent)))
                    (code-char 0)))
        (<= 0 (+ -32 (len dir-contents))))
   (equal
    (mv-nth
     1
     (find-dir-ent (make-dir-ent-list (implode (nats=>chars dir-contents)))
                   (dir-ent-filename dir-ent)))
    0))
  :hints
  (("goal"
    :in-theory (e/d (insert-dir-ent len-when-dir-ent-p
                                    make-dir-ent-list nats=>string))
    :expand
    ((find-dir-ent (make-dir-ent-list (implode (nats=>chars dir-contents)))
                   (dir-ent-filename dir-ent))
     (make-dir-ent-list (implode (nats=>chars dir-contents)))))))

;; Consider removing the unsigned-byte-listp hypothesis, it's not there in the
;; other one.
(defthm
  len-of-insert-dir-ent
  (implies
   (and (unsigned-byte-listp 8 dir-contents)
        (not (useless-dir-ent-p (dir-ent-fix dir-ent)))
        (not (equal (nth 0 (explode (dir-ent-filename dir-ent)))
                    (code-char 0))))
   (equal
    (len (insert-dir-ent dir-contents dir-ent))
    (if
     (zp (mv-nth 1
                 (find-dir-ent (make-dir-ent-list (nats=>string dir-contents))
                               (dir-ent-filename dir-ent))))
     (len dir-contents)
     (+ *ms-dir-ent-length*
        (len dir-contents)))))
  :hints
  (("goal" :in-theory (e/d (insert-dir-ent len-when-dir-ent-p
                                           make-dir-ent-list nats=>string))
    :induct (insert-dir-ent dir-contents dir-ent))))

(defthm make-dir-ent-list-of-insert-dir-ent-lemma-1
  (implies (< (nfix n) *ms-dir-ent-length*)
           (natp (nth n (dir-ent-fix dir-ent))))
  :hints (("goal" :in-theory (disable (:linear nth-when-dir-ent-p))
           :use (:instance (:linear nth-when-dir-ent-p)
                           (dir-ent (dir-ent-fix dir-ent)))))
  :rule-classes :type-prescription)

(defthm
  make-dir-ent-list-of-insert-dir-ent-lemma-2
  (implies
   (and (<= 32 (len (explode dir-contents)))
        (equal (nth 0 (explode dir-contents))
               (code-char 0))
        (not (equal (nth 0 (explode (dir-ent-filename dir-ent)))
                    (code-char 0))))
   (not (equal (dir-ent-filename (take 32
                                       (chars=>nats (explode dir-contents))))
               (dir-ent-filename dir-ent))))
  :instructions
  ((:bash
    ("goal"
     :in-theory (e/d (useless-dir-ent-p dir-ent-filename
                                        nats=>string len-when-dir-ent-p)
                     ((:rewrite nth-of-take)))
     :use ((:instance (:rewrite nth-of-take)
                      (l (nats=>chars (dir-ent-fix dir-ent)))
                      (n 11)
                      (i 0))
           (:instance (:rewrite nth-of-take)
                      (l (explode dir-contents))
                      (n 11)
                      (i 0)))))
   (:claim (not (equal (nth 0
                            (take 11 (nats=>chars (dir-ent-fix dir-ent))))
                       (code-char 0))))
   :bash))

(defthm
  make-dir-ent-list-of-insert-dir-ent-lemma-3
  (implies
   (and (not (equal (nth 0 (explode (dir-ent-filename dir-ent)))
                    (code-char 0)))
        (not (useless-dir-ent-p (dir-ent-fix dir-ent))))
   (equal (make-dir-ent-list (implode (nats=>chars (dir-ent-fix dir-ent))))
          (list (dir-ent-fix dir-ent))))
  :hints
  (("goal"
    :in-theory (enable make-dir-ent-list
                       insert-dir-ent string=>nats
                       nats=>string nthcdr-when->=-n-len-l
                       len-when-dir-ent-p)
    :do-not-induct t
    :expand
    (make-dir-ent-list (implode (nats=>chars (dir-ent-fix dir-ent)))))))

;; Hypotheses are minimal
(defthm
  make-dir-ent-list-of-insert-dir-ent
  (implies
   (and (not (equal (nth 0 (explode (dir-ent-filename dir-ent)))
                    (code-char 0)))
        (not (useless-dir-ent-p (dir-ent-fix dir-ent))))
   (equal (make-dir-ent-list
           (nats=>string (insert-dir-ent (string=>nats dir-contents)
                                         dir-ent)))
          (place-dir-ent (make-dir-ent-list dir-contents)
                         dir-ent)))
  :hints (("goal" :in-theory (enable make-dir-ent-list insert-dir-ent
                                     string=>nats nats=>string)
           :induct (make-dir-ent-list dir-contents)
           :expand (insert-dir-ent (chars=>nats (explode dir-contents))
                                   dir-ent))))

(defthm stringp-of-insert-dir-ent
  (implies (unsigned-byte-listp 8 dir-contents)
           (unsigned-byte-listp 8
                                (insert-dir-ent dir-contents dir-ent)))
  :hints (("goal" :in-theory (enable insert-dir-ent))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  ;; Hypotheses are minimal.
  (make-event
   `(defthm
      make-dir-ent-list-of-append-4
      (implies
       (and (dir-ent-p dir-ent)
            (not (useless-dir-ent-p dir-ent))
            (fat32-filename-p (dir-ent-filename dir-ent))
            (equal (mod (len (explode dir-contents))
                        *ms-dir-ent-length*)
                   0))
       (equal
        (make-dir-ent-list
         (implode
          (append
           (nats=>chars (insert-dir-ent (string=>nats dir-contents)
                                        dir-ent))
           (make-list-ac n ,(code-char 0) nil))))
        (place-dir-ent (make-dir-ent-list dir-contents)
                       dir-ent)))
      :hints
      (("goal"
        :induct (make-dir-ent-list dir-contents)
        :in-theory
        (e/d (make-dir-ent-list dir-ent-fix
                                insert-dir-ent string=>nats fat32-filename-p))
        :expand ((make-dir-ent-list dir-contents)
                 (insert-dir-ent (string=>nats dir-contents)
                                 dir-ent)))))))

(defun
    lofat-place-file
    (fat32-in-memory root-dir-ent pathname file)
  (declare
   (xargs
    :guard (and (lofat-fs-p fat32-in-memory)
                (dir-ent-p root-dir-ent)
                (>= (dir-ent-first-cluster root-dir-ent) *ms-first-data-cluster*)
                (< (dir-ent-first-cluster root-dir-ent)
                   (+ *ms-first-data-cluster*
                      (count-of-clusters fat32-in-memory)))
                (fat32-filename-list-p pathname)
                (lofat-file-p file)
                (implies (not (lofat-regular-file-p file))
                         (unsigned-byte-p 32
                                          (* 32 (len (lofat-file->contents file))))))
    :measure (acl2-count pathname)
    :stobjs fat32-in-memory
    :verify-guards nil))
  (b* (((unless (consp pathname)) (mv fat32-in-memory *enoent*))
       ;; Design choice - calls which ask for the entire root directory to be affected will fail.
       (name (mbe :logic (fat32-filename-fix (car pathname)) :exec (car pathname)))
       ((mv dir-contents &) (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent))
       (dir-ent-list (make-dir-ent-list dir-contents))
       ((mv dir-ent error-code) (find-dir-ent dir-ent-list name))
       ;; If it's not there, it's a new file. In either case, though, we shouldn't give it the name
       ;; of the old file, that is, we shouldn't be inserting a directory entry with the name of
       ;; the old file. We may be moving a file and changing its name in the process.
       (dir-ent (if (equal error-code 0) dir-ent (dir-ent-set-filename (dir-ent-fix nil) name)))
       ;; ENOTDIR - can't act on anything that supposedly exists inside a regular file.
       ((when (and (consp (cdr pathname)) (not (dir-ent-directory-p dir-ent))))
        (mv fat32-in-memory *enotdir*))
       (first-cluster (dir-ent-first-cluster dir-ent))
       ((when (and (or (< first-cluster *ms-first-data-cluster*)
                       (<= (+ *ms-first-data-cluster* (count-of-clusters fat32-in-memory))
                           first-cluster))
                   (consp (cdr pathname))))
        (mv fat32-in-memory *eio*))
        ;; Recursion
       ((when(consp (cdr pathname)))(lofat-place-file fat32-in-memory dir-ent (cdr pathname) file))
       ;; After these conditionals, the only remaining possibility is that (cdr pathname)
       ;; is an atom, which means we need to place a regular file or an empty directory, which
       ;; we have hopefully ensured in the guard or something.
       (length (if (dir-ent-directory-p dir-ent) *ms-max-dir-size* (dir-ent-file-size dir-ent)))
       ((mv fat32-in-memory &)
        (if (or (< first-cluster *ms-first-data-cluster*)
                (<= (+ *ms-first-data-cluster* (count-of-clusters fat32-in-memory)) first-cluster))
            (mv fat32-in-memory 0)
          (clear-clusterchain fat32-in-memory first-cluster length)))
       (contents (if (lofat-regular-file-p file)
                     (lofat-file->contents file)
                     (nats=>string (flatten (lofat-file->contents file)))))
       (file-length (length contents))
       (new-dir-contents (nats=>string (insert-dir-ent
                                        (string=>nats dir-contents)
                                        (dir-ent-set-first-cluster-file-size dir-ent 0 0))))
       ((when (and (zp file-length) (<= (length new-dir-contents) *ms-max-dir-size*)))
        (update-dir-contents fat32-in-memory (dir-ent-first-cluster root-dir-ent)new-dir-contents))
       ((when (zp file-length)) (mv fat32-in-memory *enospc*))
       (indices (stobj-find-n-free-clusters fat32-in-memory 1))
       ((when (< (len indices) 1)) (mv fat32-in-memory *enospc*))
       (first-cluster (nth 0 indices))
       ;; Mark this cluster as used, without possibly interfering with any
       ;; existing clusterchains.
       (fat32-in-memory
        (update-fati
         first-cluster
         (fat32-update-lower-28 (fati first-cluster fat32-in-memory)
                                *ms-end-of-clusterchain*)
         fat32-in-memory))
       ((mv fat32-in-memory dir-ent error-code &)
        (place-contents fat32-in-memory dir-ent contents file-length (nth 0 indices)))
       ((unless (zp error-code)) (mv fat32-in-memory error-code))
       (new-dir-contents (nats=>string (insert-dir-ent
                                        (string=>nats dir-contents)
                                        (dir-ent-set-first-cluster-file-size
                                         dir-ent (nth 0 indices) file-length))))
       ((unless (<= (length new-dir-contents) *ms-max-dir-size*)) (mv fat32-in-memory *enospc*)))
    (update-dir-contents fat32-in-memory (dir-ent-first-cluster root-dir-ent) new-dir-contents)))

(defthm
  count-of-clusters-of-lofat-place-file
  (equal
   (count-of-clusters
    (mv-nth
     0
     (lofat-place-file
      fat32-in-memory root-dir-ent pathname file)))
   (count-of-clusters fat32-in-memory)))

(defthm
  lofat-fs-p-of-lofat-place-file-lemma-1
  (implies (lofat-file-p file)
           (iff (stringp (lofat-file->contents file))
                (not (lofat-directory-file-p file))))
  :hints
  (("goal" :in-theory (enable lofat-directory-file-p
                              lofat-file-p lofat-file-contents-p
                              lofat-file->contents))))

(defthm
  lofat-fs-p-of-lofat-place-file-lemma-2
  (implies
   (<=
    1
    (count-free-clusters
     (set-indices-in-fa-table
      (effective-fat fat32-in-memory)
      (mv-nth
       0
       (dir-ent-clusterchain
        fat32-in-memory
        (mv-nth
         0
         (find-dir-ent
          (make-dir-ent-list
           (mv-nth 0
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
          (fat32-filename-fix (car pathname))))))
      (make-list-ac
       (len
        (mv-nth
         0
         (dir-ent-clusterchain
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              0
              (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
            (fat32-filename-fix (car pathname)))))))
       0 nil))))
   (<
    (nfix 0)
    (len
     (find-n-free-clusters
      (set-indices-in-fa-table
       (effective-fat fat32-in-memory)
       (mv-nth
        '0
        (dir-ent-clusterchain
         fat32-in-memory
         (mv-nth
          '0
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth '0
                    (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
           (fat32-filename-fix (car pathname))))))
       (make-list-ac
        (len
         (mv-nth
          '0
          (dir-ent-clusterchain
           fat32-in-memory
           (mv-nth
            '0
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth
               '0
               (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
             (fat32-filename-fix (car pathname)))))))
        '0
        'nil))
      1))))
  :rule-classes :linear)

(defthm
  lofat-fs-p-of-lofat-place-file-lemma-3
  (implies (<= 1
               (count-free-clusters (effective-fat fat32-in-memory)))
           (<= *ms-first-data-cluster*
               (nth '0
                    (find-n-free-clusters (effective-fat fat32-in-memory)
                                          '1)))))

(defthm
  lofat-fs-p-of-lofat-place-file-lemma-4
  (implies
   (<=
    1
    (count-free-clusters
     (set-indices-in-fa-table
      (effective-fat fat32-in-memory)
      (mv-nth
       0
       (dir-ent-clusterchain
        fat32-in-memory
        (mv-nth
         0
         (find-dir-ent
          (make-dir-ent-list
           (mv-nth 0
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
          (fat32-filename-fix (car pathname))))))
      (make-list-ac
       (len
        (mv-nth
         0
         (dir-ent-clusterchain
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              0
              (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
            (fat32-filename-fix (car pathname)))))))
       0 nil))))
   (not
    (<
     (nth
      '0
      (find-n-free-clusters
       (set-indices-in-fa-table
        (effective-fat fat32-in-memory)
        (mv-nth
         '0
         (dir-ent-clusterchain
          fat32-in-memory
          (mv-nth
           '0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              '0
              (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
            (fat32-filename-fix (car pathname))))))
        (make-list-ac
         (len
          (mv-nth
           '0
           (dir-ent-clusterchain
            fat32-in-memory
            (mv-nth
             '0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                '0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
              (fat32-filename-fix (car pathname)))))))
         '0
         'nil))
       '1))
     '2))))

(defthm
  lofat-fs-p-of-lofat-place-file-lemma-5
  (implies
   (<=
    1
    (count-free-clusters
     (set-indices-in-fa-table
      (effective-fat fat32-in-memory)
      (mv-nth
       0
       (dir-ent-clusterchain
        fat32-in-memory
        (dir-ent-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                              (fat32-filename-fix (car pathname)))))
      (make-list-ac
       (len
        (mv-nth
         0
         (dir-ent-clusterchain
          fat32-in-memory
          (dir-ent-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                (fat32-filename-fix (car pathname))))))
       0 nil))))
   (<=
    *ms-first-data-cluster*
    (nth
     '0
     (find-n-free-clusters
      (set-indices-in-fa-table
       (effective-fat fat32-in-memory)
       (mv-nth
        '0
        (dir-ent-clusterchain
         fat32-in-memory
         (dir-ent-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                                   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                               (fat32-filename-fix (car pathname)))))
       (make-list-ac
        (len
         (mv-nth
          '0
          (dir-ent-clusterchain
           fat32-in-memory
           (dir-ent-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                 (fat32-filename-fix (car pathname))))))
        '0
        'nil))
      '1))))
  :hints
  (("goal"
    :in-theory (disable (:linear find-n-free-clusters-correctness-7))
    :use
    (:instance
     (:linear find-n-free-clusters-correctness-7)
     (n 1)
     (fa-table
      (set-indices-in-fa-table
       (effective-fat fat32-in-memory)
       (mv-nth
        0
        (dir-ent-clusterchain
         fat32-in-memory
         (dir-ent-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                                   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                               (fat32-filename-fix (car pathname)))))
       (make-list-ac
        (len
         (mv-nth
          0
          (dir-ent-clusterchain
           fat32-in-memory
           (dir-ent-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                 (fat32-filename-fix (car pathname))))))
        0 nil)))
     (m 0))))
  :rule-classes :linear)

(defthm
  lofat-fs-p-of-lofat-place-file-lemma-6
  (implies
   (<=
    1
    (count-free-clusters
     (set-indices-in-fa-table
      (effective-fat fat32-in-memory)
      (mv-nth
       0
       (fat32-build-index-list
        (effective-fat fat32-in-memory)
        (dir-ent-first-cluster
         (dir-ent-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                                   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                               (fat32-filename-fix (car pathname))))
        0 (cluster-size fat32-in-memory)))
      (make-list-ac
       (len
        (mv-nth
         0
         (fat32-build-index-list
          (effective-fat fat32-in-memory)
          (dir-ent-first-cluster
           (dir-ent-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                 (fat32-filename-fix (car pathname))))
          0 (cluster-size fat32-in-memory))))
       0 nil))))
   (<=
    *ms-first-data-cluster*
    (nth
     '0
     (find-n-free-clusters
      (set-indices-in-fa-table
       (effective-fat fat32-in-memory)
       (mv-nth
        '0
        (fat32-build-index-list
         (effective-fat fat32-in-memory)
         (dir-ent-first-cluster
          (dir-ent-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                (fat32-filename-fix (car pathname))))
         '0
         (cluster-size fat32-in-memory)))
       (make-list-ac
        (len
         (mv-nth
          '0
          (fat32-build-index-list
           (effective-fat fat32-in-memory)
           (dir-ent-first-cluster
            (dir-ent-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                  (fat32-filename-fix (car pathname))))
           '0
           (cluster-size fat32-in-memory))))
        '0
        'nil))
      '1))))
  :hints
  (("goal"
    :in-theory (enable (:linear find-n-free-clusters-correctness-7))
    :use
    (:instance
     (:linear find-n-free-clusters-correctness-7)
     (n 1)
     (fa-table
      (set-indices-in-fa-table
       (effective-fat fat32-in-memory)
       (mv-nth
        0
        (fat32-build-index-list
         (effective-fat fat32-in-memory)
         (dir-ent-first-cluster
          (dir-ent-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                (fat32-filename-fix (car pathname))))
         0 (cluster-size fat32-in-memory)))
       (make-list-ac
        (len
         (mv-nth
          0
          (fat32-build-index-list
           (effective-fat fat32-in-memory)
           (dir-ent-first-cluster
            (dir-ent-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                  (fat32-filename-fix (car pathname))))
           0 (cluster-size fat32-in-memory))))
        0 nil)))
     (m 0))))
  :rule-classes :linear)

;; Consider making this linear, later.
(defthm
  lofat-fs-p-of-lofat-place-file-lemma-7
  (implies
   (<=
    1
    (count-free-clusters
     (set-indices-in-fa-table
      (effective-fat fat32-in-memory)
      (mv-nth
       0
       (dir-ent-clusterchain
        fat32-in-memory
        (mv-nth
         0
         (find-dir-ent
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
          (fat32-filename-fix (car pathname))))))
      (make-list-ac
       (len
        (mv-nth
         0
         (dir-ent-clusterchain
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              0
              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
            (fat32-filename-fix (car pathname)))))))
       0 nil))))
   (not
    (<
     (nth
      '0
      (find-n-free-clusters
       (set-indices-in-fa-table
        (effective-fat fat32-in-memory)
        (mv-nth
         '0
         (dir-ent-clusterchain
          fat32-in-memory
          (mv-nth
           '0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              '0
              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
            (fat32-filename-fix (car pathname))))))
        (make-list-ac
         (len
          (mv-nth
           '0
           (dir-ent-clusterchain
            fat32-in-memory
            (mv-nth
             '0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                '0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
              (fat32-filename-fix (car pathname)))))))
         '0
         'nil))
       '1))
     '0))))

;; Consider making this linear, later.
(defthm
  lofat-fs-p-of-lofat-place-file-lemma-8
  (implies (<= 1
               (count-free-clusters (effective-fat fat32-in-memory)))
           (not (< (nth '0
                        (find-n-free-clusters (effective-fat fat32-in-memory)
                                              '1))
                   '0))))

(defthm
  lofat-fs-p-of-lofat-place-file
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (dir-ent-p root-dir-ent)
        (>= (dir-ent-first-cluster root-dir-ent)
            *ms-first-data-cluster*)
        (< (dir-ent-first-cluster root-dir-ent)
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory))))
   (lofat-fs-p (mv-nth 0
                       (lofat-place-file fat32-in-memory
                                         root-dir-ent pathname file))))
  :hints (("goal" :induct (lofat-place-file fat32-in-memory
                                            root-dir-ent pathname file))))

(defthm
  lofat-place-file-guard-lemma-1
  (implies (lofat-regular-file-p file)
           (unsigned-byte-p
            32
            (len (explode (lofat-file->contents file)))))
  :hints (("goal" :in-theory (enable lofat-regular-file-p))))

(defthm
  lofat-place-file-guard-lemma-2
  (implies (and (lofat-file-p file)
                (not (lofat-directory-file-p file)))
           (lofat-regular-file-p file))
  :hints
  (("goal" :in-theory (enable lofat-file-p lofat-regular-file-p
                              lofat-directory-file-p
                              lofat-file-contents-p
                              lofat-file->contents))))

(defthm
  lofat-place-file-guard-lemma-3
  (implies (lofat-directory-file-p file)
           (dir-ent-list-p (lofat-file->contents file)))
  :hints (("goal" :in-theory (enable lofat-directory-file-p))))

(defthm
  lofat-place-file-guard-lemma-4
  (implies
   (<=
    1
    (count-free-clusters
     (set-indices-in-fa-table
      (effective-fat fat32-in-memory)
      (mv-nth
       0
       (dir-ent-clusterchain
        fat32-in-memory
        (mv-nth
         0
         (find-dir-ent
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
          (car pathname)))))
      (make-list-ac
       (len
        (mv-nth
         0
         (dir-ent-clusterchain
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              0
              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
            (car pathname))))))
       0 nil))))
   (<=
    2
    (nth
     0
     (find-n-free-clusters
      (set-indices-in-fa-table
       (effective-fat fat32-in-memory)
       (mv-nth
        0
        (dir-ent-clusterchain
         fat32-in-memory
         (mv-nth
          0
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth
             0
             (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
           (car pathname)))))
       (make-list-ac
        (len
         (mv-nth
          0
          (dir-ent-clusterchain
           fat32-in-memory
           (mv-nth
            0
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth
               0
               (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
             (car pathname))))))
        0 nil))
      1)))))

(defthm
  lofat-place-file-guard-lemma-5
  (implies
   (<=
    1
    (count-free-clusters
     (set-indices-in-fa-table
      (effective-fat fat32-in-memory)
      (mv-nth
       0
       (fat32-build-index-list
        (effective-fat fat32-in-memory)
        (dir-ent-first-cluster
         (dir-ent-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                                   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                               (car pathname)))
        0 (cluster-size fat32-in-memory)))
      (make-list-ac
       (len
        (mv-nth
         0
         (fat32-build-index-list
          (effective-fat fat32-in-memory)
          (dir-ent-first-cluster
           (dir-ent-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                 (car pathname)))
          0 (cluster-size fat32-in-memory))))
       0 nil))))
   (<=
    *ms-first-data-cluster*
    (nth
     '0
     (find-n-free-clusters
      (set-indices-in-fa-table
       (effective-fat fat32-in-memory)
       (mv-nth
        '0
        (fat32-build-index-list
         (effective-fat fat32-in-memory)
         (dir-ent-first-cluster
          (dir-ent-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                (car pathname)))
         '0
         (cluster-size fat32-in-memory)))
       (make-list-ac
        (len
         (mv-nth
          '0
          (fat32-build-index-list
           (effective-fat fat32-in-memory)
           (dir-ent-first-cluster
            (dir-ent-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                  (car pathname)))
           '0
           (cluster-size fat32-in-memory))))
        '0
        'nil))
      '1))))
  :rule-classes :linear
  :hints
  (("goal"
    :in-theory (disable (:linear find-n-free-clusters-correctness-7))
    :use
    (:instance
     (:linear find-n-free-clusters-correctness-7)
     (n 1)
     (fa-table
      (set-indices-in-fa-table
       (effective-fat fat32-in-memory)
       (mv-nth
        0
        (fat32-build-index-list
         (effective-fat fat32-in-memory)
         (dir-ent-first-cluster
          (dir-ent-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                (car pathname)))
         0 (cluster-size fat32-in-memory)))
       (make-list-ac
        (len
         (mv-nth
          0
          (fat32-build-index-list
           (effective-fat fat32-in-memory)
           (dir-ent-first-cluster
            (dir-ent-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                  (car pathname)))
           0 (cluster-size fat32-in-memory))))
        0 nil)))
     (m 0)))))

;; Consider making this linear, later.
(defthm
  lofat-place-file-guard-lemma-6
  (implies
   (<=
    1
    (count-free-clusters
     (set-indices-in-fa-table
      (effective-fat fat32-in-memory)
      (mv-nth
       0
       (dir-ent-clusterchain
        fat32-in-memory
        (mv-nth
         0
         (find-dir-ent
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
          (car pathname)))))
      (make-list-ac
       (len
        (mv-nth
         0
         (dir-ent-clusterchain
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              0
              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
            (car pathname))))))
       0 nil))))
   (not
    (<
     (nth
      '0
      (find-n-free-clusters
       (set-indices-in-fa-table
        (effective-fat fat32-in-memory)
        (mv-nth
         '0
         (dir-ent-clusterchain
          fat32-in-memory
          (mv-nth
           '0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              '0
              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
            (car pathname)))))
        (make-list-ac
         (len
          (mv-nth
           '0
           (dir-ent-clusterchain
            fat32-in-memory
            (mv-nth
             '0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                '0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
              (car pathname))))))
         '0
         'nil))
       '1))
     '0))))

(verify-guards
  lofat-place-file
  :hints
  (("goal" :in-theory (disable unsigned-byte-p))))

(defthm natp-of-lofat-place-file
  (natp (mv-nth 1
                (lofat-place-file fat32-in-memory
                                  root-dir-ent pathname file)))
  :rule-classes :type-prescription)

;; Kinda general
(defthm lofat-place-file-correctness-1-lemma-2
  (implies (not (zp (mv-nth 1 (hifat-place-file fs pathname file))))
           (equal (mv-nth 0 (hifat-place-file fs pathname file))
                  (hifat-file-alist-fix fs)))
  :hints (("goal" :in-theory (enable hifat-place-file))))

(defthm
  hifat-cluster-count-of-put-assoc
  (implies
   (m1-file-alist-p fs)
   (equal (hifat-cluster-count (put-assoc-equal name file fs)
                               cluster-size)
          (b* ((new-contents (m1-file->contents file))
               ((when (and (atom (assoc-equal name fs))
                           (m1-regular-file-p file)))
                (+ (hifat-cluster-count fs cluster-size)
                   (len (make-clusters new-contents cluster-size))))
               ((when (atom (assoc-equal name fs)))
                (+ (hifat-cluster-count fs cluster-size)
                   (+ (hifat-cluster-count new-contents cluster-size)
                      (nfix (floor (+ (* 32 (+ 2 (len new-contents)))
                                      cluster-size -1)
                                   cluster-size)))))
               (old-contents (m1-file->contents (cdr (assoc-equal name fs))))
               ((when (and (m1-directory-file-p (cdr (assoc-equal name fs)))
                           (m1-regular-file-p file)))
                (+ (hifat-cluster-count fs cluster-size)
                   (len (make-clusters new-contents cluster-size))
                   (- (hifat-cluster-count old-contents cluster-size))
                   (- (nfix (floor (+ (* 32 (+ 2 (len old-contents)))
                                      cluster-size -1)
                                   cluster-size)))))
               ((when (m1-directory-file-p (cdr (assoc-equal name fs))))
                (+ (hifat-cluster-count fs cluster-size)
                   (hifat-cluster-count new-contents cluster-size)
                   (nfix (floor (+ (* 32 (+ 2 (len new-contents)))
                                   cluster-size -1)
                                cluster-size))
                   (- (hifat-cluster-count old-contents cluster-size))
                   (- (nfix (floor (+ (* 32 (+ 2 (len old-contents)))
                                      cluster-size -1)
                                   cluster-size)))))
               ((when (m1-regular-file-p file))
                (+ (hifat-cluster-count fs cluster-size)
                   (len (make-clusters new-contents cluster-size))
                   (- (len (make-clusters old-contents cluster-size))))))
            (+ (hifat-cluster-count fs cluster-size)
               (hifat-cluster-count new-contents cluster-size)
               (nfix (floor (+ (* 32 (+ 2 (len new-contents)))
                               cluster-size -1)
                            cluster-size))
               (- (len (make-clusters old-contents cluster-size)))))))
  :hints (("goal" :in-theory (enable hifat-cluster-count)
           :induct (put-assoc-equal name file fs))))

;; Rather general
(defthm lofat-place-file-correctness-1-lemma-3
  (and
   (natp (mv-nth 1 (hifat-place-file fs pathname file)))
   (not (stringp (mv-nth 0 (hifat-place-file fs pathname file)))))
  :hints (("goal" :in-theory (enable hifat-place-file)))
  :rule-classes
  ((:type-prescription :corollary
    (natp (mv-nth 1 (hifat-place-file fs pathname file))))
   (:type-prescription :corollary
    (not (stringp (mv-nth 0 (hifat-place-file fs pathname file)))))))

;; Rather general
(defthm lofat-place-file-correctness-1-lemma-4
  (natp (mv-nth 1 (hifat-find-file fs pathname)))
  :hints (("goal" :in-theory (enable hifat-find-file)))
  :rule-classes :type-prescription)

(defthm len-of-put-assoc-equal-of-fat32-filename-fix
  (equal (len (put-assoc-equal (fat32-filename-fix x)
                               val alist))
         (if (consp (assoc-equal (fat32-filename-fix x)
                                 alist))
             (len alist)
             (+ 1 (len alist)))))

;; Move later
(defthm
  len-of-hifat-place-file
  (equal (len (mv-nth 0 (hifat-place-file fs pathname file)))
         (if (and (consp pathname)
                  (atom (cdr pathname))
                  (atom (assoc-equal (fat32-filename-fix (car pathname))
                                     (hifat-file-alist-fix fs))))
             (+ 1 (len (hifat-file-alist-fix fs)))
             (len (hifat-file-alist-fix fs))))
  :hints (("goal" :in-theory (enable hifat-place-file))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthmd painful-debugging-lemma-18
    (implies (and (integerp i) (not (zp j)))
             (equal (floor i j)
                    (+ (floor (- i j) j) 1)))))

(defthm
  hifat-cluster-count-of-hifat-place-file-lemma-1
  (implies
   (and
    (consp pathname)
    (m1-directory-file-p (cdr (assoc-equal (car pathname) fs)))
    (< 1 (len (cdr pathname)))
    (equal
     (hifat-cluster-count
      (mv-nth 0
              (hifat-place-file
               (m1-file->contents (cdr (assoc-equal (car pathname) fs)))
               (cdr pathname)
               file))
      cluster-size)
     (+
      (hifat-cluster-count (m1-file->contents file)
                           cluster-size)
      (hifat-cluster-count
       (m1-file->contents (cdr (assoc-equal (car pathname) fs)))
       cluster-size)
      (floor (+ 63 cluster-size
                (* 32 (len (m1-file->contents file))))
             cluster-size)
      (-
       (floor
        (+
         63 cluster-size
         (*
          32
          (len
           (m1-file->contents
            (mv-nth
             0
             (hifat-find-file
              (m1-file->contents (cdr (assoc-equal (car pathname) fs)))
              (take (+ -1 (len (cdr pathname)))
                    (cdr pathname))))))))
        cluster-size))
      (floor
       (+
        95 cluster-size
        (*
         32
         (len
          (m1-file->contents
           (mv-nth
            0
            (hifat-find-file
             (m1-file->contents (cdr (assoc-equal (car pathname) fs)))
             (take (+ -1 (len (cdr pathname)))
                   (cdr pathname))))))))
       cluster-size)))
    (m1-file-alist-p fs)
    (hifat-no-dups-p fs)
    (fat32-filename-list-p pathname))
   (equal
    (+
     (hifat-cluster-count fs cluster-size)
     (- (hifat-cluster-count
         (m1-file->contents (cdr (assoc-equal (car pathname) fs)))
         cluster-size))
     (hifat-cluster-count
      (mv-nth 0
              (hifat-place-file
               (m1-file->contents (cdr (assoc-equal (car pathname) fs)))
               (cdr pathname)
               file))
      cluster-size))
    (+
     (hifat-cluster-count fs cluster-size)
     (hifat-cluster-count (m1-file->contents file)
                          cluster-size)
     (floor (+ 63 cluster-size
               (* 32 (len (m1-file->contents file))))
            cluster-size)
     (-
      (floor
       (+ 63 cluster-size
          (* 32
             (len (m1-file->contents
                   (mv-nth 0
                           (hifat-find-file fs
                                            (take (len (cdr pathname))
                                                  pathname)))))))
       cluster-size))
     (floor
      (+ 95 cluster-size
         (* 32
            (len (m1-file->contents
                  (mv-nth 0
                          (hifat-find-file fs
                                           (take (len (cdr pathname))
                                                 pathname)))))))
      cluster-size))))
  :hints (("goal" :expand ((:free (pathname)
                                  (hifat-find-file fs pathname))
                           (:free (n) (take n pathname))))))

(defthm
  hifat-cluster-count-of-hifat-place-file-lemma-2
  (implies
   (and
    (equal (len (cdr pathname)) 1)
    (m1-directory-file-p (cdr (assoc-equal (car pathname) fs)))
    (m1-file-alist-p fs)
    (hifat-no-dups-p fs)
    (fat32-filename-list-p pathname)
    (consp
     (assoc-equal (cadr pathname)
                  (m1-file->contents (cdr (assoc-equal (car pathname) fs))))))
   (equal
    (mv-nth 1
            (hifat-find-file
             (m1-file->contents (cdr (assoc-equal (car pathname) fs)))
             (cdr pathname)))
    0))
  :hints
  (("goal"
    :expand ((hifat-find-file
              (m1-file->contents (cdr (assoc-equal (car pathname) fs)))
              (cdr pathname))
             (len (cdr pathname))
             (len (cddr pathname))))))

(defthmd hifat-cluster-count-of-hifat-place-file-lemma-3
  (implies (equal (+ 1 (len (cddr pathname))) 1)
           (not (consp (cddr pathname))))
  :hints (("goal" :expand (len (cddr pathname)))))

(defthm
  hifat-cluster-count-of-hifat-place-file-lemma-4
  (implies
   (and
    (consp pathname)
    (m1-directory-file-p (cdr (assoc-equal (car pathname) fs)))
    (< 1 (+ 1 (len (cddr pathname))))
    (equal
     (hifat-cluster-count
      (mv-nth 0
              (hifat-place-file
               (m1-file->contents (cdr (assoc-equal (car pathname) fs)))
               (cdr pathname)
               file))
      cluster-size)
     (+
      (len (make-clusters (m1-file->contents file)
                          cluster-size))
      (hifat-cluster-count
       (m1-file->contents (cdr (assoc-equal (car pathname) fs)))
       cluster-size)
      (-
       (floor
        (+
         63 cluster-size
         (*
          32
          (len
           (m1-file->contents
            (mv-nth
             0
             (hifat-find-file
              (m1-file->contents (cdr (assoc-equal (car pathname) fs)))
              (take (len (cddr pathname))
                    (cdr pathname))))))))
        cluster-size))
      (floor
       (+
        95 cluster-size
        (*
         32
         (len
          (m1-file->contents
           (mv-nth
            0
            (hifat-find-file
             (m1-file->contents (cdr (assoc-equal (car pathname) fs)))
             (take (len (cddr pathname))
                   (cdr pathname))))))))
       cluster-size)))
    (m1-file-alist-p fs)
    (hifat-no-dups-p fs)
    (fat32-filename-list-p pathname))
   (equal
    (+
     (hifat-cluster-count fs cluster-size)
     (- (hifat-cluster-count
         (m1-file->contents (cdr (assoc-equal (car pathname) fs)))
         cluster-size))
     (hifat-cluster-count
      (mv-nth 0
              (hifat-place-file
               (m1-file->contents (cdr (assoc-equal (car pathname) fs)))
               (cdr pathname)
               file))
      cluster-size))
    (+
     (hifat-cluster-count fs cluster-size)
     (len (make-clusters (m1-file->contents file)
                         cluster-size))
     (-
      (floor
       (+
        63 cluster-size
        (*
         32
         (len (m1-file->contents
               (mv-nth 0
                       (hifat-find-file fs
                                        (take (+ 1 (len (cddr pathname)))
                                              pathname)))))))
       cluster-size))
     (floor
      (+
       95 cluster-size
       (* 32
          (len (m1-file->contents
                (mv-nth 0
                        (hifat-find-file fs
                                         (take (+ 1 (len (cddr pathname)))
                                               pathname)))))))
      cluster-size))))
  :hints (("goal" :expand ((:free (pathname)
                                  (hifat-find-file fs pathname))
                           (:free (n) (take n pathname))))))

(defthm
  hifat-cluster-count-of-hifat-place-file-lemma-5
  (implies
   (and
    (consp pathname)
    (m1-directory-file-p (cdr (assoc-equal (car pathname) fs)))
    (< 1 (len (cdr pathname)))
    (equal
     (hifat-cluster-count
      (mv-nth 0
              (hifat-place-file
               (m1-file->contents (cdr (assoc-equal (car pathname) fs)))
               (cdr pathname)
               file))
      cluster-size)
     (+
      (len (make-clusters (m1-file->contents file)
                          cluster-size))
      (hifat-cluster-count
       (m1-file->contents (cdr (assoc-equal (car pathname) fs)))
       cluster-size)
      (-
       (floor
        (+
         63 cluster-size
         (*
          32
          (len
           (m1-file->contents
            (mv-nth
             0
             (hifat-find-file
              (m1-file->contents (cdr (assoc-equal (car pathname) fs)))
              (take (+ -1 (len (cdr pathname)))
                    (cdr pathname))))))))
        cluster-size))
      (floor
       (+
        95 cluster-size
        (*
         32
         (len
          (m1-file->contents
           (mv-nth
            0
            (hifat-find-file
             (m1-file->contents (cdr (assoc-equal (car pathname) fs)))
             (take (+ -1 (len (cdr pathname)))
                   (cdr pathname))))))))
       cluster-size)))
    (m1-file-alist-p fs)
    (hifat-no-dups-p fs)
    (fat32-filename-list-p pathname))
   (equal
    (+
     (hifat-cluster-count fs cluster-size)
     (- (hifat-cluster-count
         (m1-file->contents (cdr (assoc-equal (car pathname) fs)))
         cluster-size))
     (hifat-cluster-count
      (mv-nth 0
              (hifat-place-file
               (m1-file->contents (cdr (assoc-equal (car pathname) fs)))
               (cdr pathname)
               file))
      cluster-size))
    (+
     (hifat-cluster-count fs cluster-size)
     (len (make-clusters (m1-file->contents file)
                         cluster-size))
     (-
      (floor
       (+ 63 cluster-size
          (* 32
             (len (m1-file->contents
                   (mv-nth 0
                           (hifat-find-file fs
                                            (take (len (cdr pathname))
                                                  pathname)))))))
       cluster-size))
     (floor
      (+ 95 cluster-size
         (* 32
            (len (m1-file->contents
                  (mv-nth 0
                          (hifat-find-file fs
                                           (take (len (cdr pathname))
                                                 pathname)))))))
      cluster-size))))
  :hints (("goal" :expand ((:free (pathname)
                                  (hifat-find-file fs pathname))
                           (:free (n) (take n pathname))))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    hifat-cluster-count-of-hifat-place-file-lemma-6
    (implies (and (integerp cluster-size)
                  (<= 512 cluster-size))
             (and
              (equal (floor (+ 63 cluster-size) cluster-size)
                     1)
              (equal (floor (+ 95 cluster-size) cluster-size)
                     1)))))

(encapsulate
  ()

  (local
   (defthmd
     hifat-cluster-count-of-hifat-place-file-lemma-7
     (implies
      (and (m1-file-alist-p fs)
           (hifat-no-dups-p fs)
           (fat32-filename-list-p pathname)
           (m1-file-p file)
           (integerp cluster-size)
           (<= 512 cluster-size))
      (equal
       (hifat-cluster-count
        (mv-nth 0 (hifat-place-file fs pathname file))
        cluster-size)
       (b*
           ((new-contents (m1-file->contents file))
            ((when
                 (not (zp (mv-nth 1
                                  (hifat-place-file fs pathname file)))))
             (hifat-cluster-count fs cluster-size))
            ;; This may be inaccurate because the parent directory's length
            ;; will change.
            ((when
                 (and (not (zp (mv-nth 1 (hifat-find-file fs pathname))))
                      (m1-regular-file-p file)))
             (+
              (hifat-cluster-count fs cluster-size)
              (len (make-clusters new-contents cluster-size))
              (nfix
               (floor
                (+
                 (*
                  32
                  (+
                   3
                   (len
                    (m1-file->contents
                     (mv-nth
                      0
                      (hifat-find-file fs (butlast pathname 1)))))))
                 cluster-size -1)
                cluster-size))
              (-
               (nfix
                (floor
                 (+
                  (*
                   32
                   (+
                    2
                    (len
                     (m1-file->contents
                      (mv-nth
                       0
                       (hifat-find-file fs (butlast pathname 1)))))))
                  cluster-size -1)
                 cluster-size)))))
            ;; This may be inaccurate because the parent directory's length
            ;; will change.
            ((when
                 (not (zp (mv-nth 1 (hifat-find-file fs pathname)))))
             (+ (hifat-cluster-count fs cluster-size)
                (hifat-cluster-count new-contents cluster-size)
                (nfix (floor (+ (* 32 (+ 2 (len new-contents)))
                                cluster-size -1)
                             cluster-size))
                (nfix
                 (floor
                  (+
                   (*
                    32
                    (+
                     3
                     (len
                      (m1-file->contents
                       (mv-nth
                        0
                        (hifat-find-file fs (butlast pathname 1)))))))
                   cluster-size -1)
                  cluster-size))
                (-
                 (nfix
                  (floor
                   (+
                    (*
                     32
                     (+
                      2
                      (len
                       (m1-file->contents
                        (mv-nth
                         0
                         (hifat-find-file fs (butlast pathname 1)))))))
                    cluster-size -1)
                   cluster-size)))))
            (old-file (mv-nth 0 (hifat-find-file fs pathname)))
            (old-contents (m1-file->contents old-file))
            ((when (and (m1-regular-file-p file)
                        (m1-regular-file-p old-file)))
             (+ (hifat-cluster-count fs cluster-size)
                (len (make-clusters new-contents cluster-size))
                (- (len (make-clusters old-contents cluster-size)))))
            ((when (m1-regular-file-p file))
             (+ (hifat-cluster-count fs cluster-size)
                (len (make-clusters new-contents cluster-size))
                (- (hifat-cluster-count old-contents cluster-size))
                (- (nfix (floor (+ (* 32 (+ 2 (len old-contents)))
                                   cluster-size -1)
                                cluster-size)))))
            ((when (m1-regular-file-p old-file))
             (+ (hifat-cluster-count fs cluster-size)
                (hifat-cluster-count new-contents cluster-size)
                (nfix (floor (+ (* 32 (+ 2 (len new-contents)))
                                cluster-size -1)
                             cluster-size))
                (- (len (make-clusters old-contents cluster-size))))))
         (+ (hifat-cluster-count fs cluster-size)
            (hifat-cluster-count new-contents cluster-size)
            (nfix (floor (+ (* 32 (+ 2 (len new-contents)))
                            cluster-size -1)
                         cluster-size))
            (- (hifat-cluster-count old-contents cluster-size))
            (- (nfix (floor (+ (* 32 (+ 2 (len old-contents)))
                               cluster-size -1)
                            cluster-size)))))))
     :hints
     (("goal" :in-theory (enable hifat-place-file hifat-find-file
                                 hifat-cluster-count-of-hifat-place-file-lemma-3)
       :induct (hifat-place-file fs pathname file)))))

  (defthm
    hifat-cluster-count-of-hifat-place-file
    (implies
     (and (integerp cluster-size)
          (<= 512 cluster-size))
     (equal
      (hifat-cluster-count
       (mv-nth 0 (hifat-place-file fs pathname file))
       cluster-size)
      (b*
          ((new-contents (m1-file->contents file))
           (fs (hifat-file-alist-fix fs))
           (pathname (fat32-filename-list-fix pathname))
           (file (m1-file-fix file))
           ((when
                (not (zp (mv-nth 1
                                 (hifat-place-file fs pathname file)))))
            (hifat-cluster-count fs cluster-size))
           ;; This may be inaccurate because the parent directory's length
           ;; will change.
           ((when
                (and (not (zp (mv-nth 1 (hifat-find-file fs pathname))))
                     (m1-regular-file-p file)))
            (+
             (hifat-cluster-count fs cluster-size)
             (len (make-clusters new-contents cluster-size))
             (nfix
              (floor
               (+
                (*
                 32
                 (+
                  3
                  (len
                   (m1-file->contents
                    (mv-nth
                     0
                     (hifat-find-file fs (butlast pathname 1)))))))
                cluster-size -1)
               cluster-size))
             (-
              (nfix
               (floor
                (+
                 (*
                  32
                  (+
                   2
                   (len
                    (m1-file->contents
                     (mv-nth
                      0
                      (hifat-find-file fs (butlast pathname 1)))))))
                 cluster-size -1)
                cluster-size)))))
           ;; This may be inaccurate because the parent directory's length
           ;; will change.
           ((when
                (not (zp (mv-nth 1 (hifat-find-file fs pathname)))))
            (+ (hifat-cluster-count fs cluster-size)
               (hifat-cluster-count new-contents cluster-size)
               (nfix (floor (+ (* 32 (+ 2 (len new-contents)))
                               cluster-size -1)
                            cluster-size))
               (nfix
                (floor
                 (+
                  (*
                   32
                   (+
                    3
                    (len
                     (m1-file->contents
                      (mv-nth
                       0
                       (hifat-find-file fs (butlast pathname 1)))))))
                  cluster-size -1)
                 cluster-size))
               (-
                (nfix
                 (floor
                  (+
                   (*
                    32
                    (+
                     2
                     (len
                      (m1-file->contents
                       (mv-nth
                        0
                        (hifat-find-file fs (butlast pathname 1)))))))
                   cluster-size -1)
                  cluster-size)))))
           (old-file (mv-nth 0 (hifat-find-file fs pathname)))
           (old-contents (m1-file->contents old-file))
           ((when (and (m1-regular-file-p file)
                       (m1-regular-file-p old-file)))
            (+ (hifat-cluster-count fs cluster-size)
               (len (make-clusters new-contents cluster-size))
               (- (len (make-clusters old-contents cluster-size)))))
           ((when (m1-regular-file-p file))
            (+ (hifat-cluster-count fs cluster-size)
               (len (make-clusters new-contents cluster-size))
               (- (hifat-cluster-count old-contents cluster-size))
               (- (nfix (floor (+ (* 32 (+ 2 (len old-contents)))
                                  cluster-size -1)
                               cluster-size)))))
           ((when (m1-regular-file-p old-file))
            (+ (hifat-cluster-count fs cluster-size)
               (hifat-cluster-count new-contents cluster-size)
               (nfix (floor (+ (* 32 (+ 2 (len new-contents)))
                               cluster-size -1)
                            cluster-size))
               (- (len (make-clusters old-contents cluster-size))))))
        (+ (hifat-cluster-count fs cluster-size)
           (hifat-cluster-count new-contents cluster-size)
           (nfix (floor (+ (* 32 (+ 2 (len new-contents)))
                           cluster-size -1)
                        cluster-size))
           (- (hifat-cluster-count old-contents cluster-size))
           (- (nfix (floor (+ (* 32 (+ 2 (len old-contents)))
                              cluster-size -1)
                           cluster-size)))))))
    :hints
    (("goal"
      :use (:instance
            hifat-cluster-count-of-hifat-place-file-lemma-7
            (fs (hifat-file-alist-fix fs))
            (pathname (fat32-filename-list-fix pathname))
            (file (m1-file-fix file)))))))

(defthm lofat-place-file-correctness-1-lemma-5
  (implies (lofat-regular-file-p file)
           (> 4294967296
              (len (explode (lofat-file->contents file)))))
  :hints (("goal" :in-theory (enable lofat-regular-file-p
                                     lofat-file->contents)))
  :rule-classes :linear)

(defthm
  lofat-place-file-correctness-1-lemma-6
  (implies
   (and
    (equal
     (mv-nth
      1
      (hifat-find-file
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32-in-memory
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
         entry-limit))
       pathname))
     0)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit))
     0)
    (fat32-filename-list-p pathname))
   (equal
    (mv-nth
     1
     (find-dir-ent
      (make-dir-ent-list
       (mv-nth 0
               (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
      (car pathname)))
    0))
  :hints
  (("goal"
    :expand
    (hifat-find-file
     (mv-nth
      0
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit))
     pathname))))

(defthm
  lofat-place-file-correctness-1-lemma-7
  (implies
   (and
    (equal
     (mv-nth
      1
      (hifat-place-file
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32-in-memory
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
         entry-limit))
       pathname
       (m1-file dir-ent (lofat-file->contents file))))
     0)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit))
     0)
    (fat32-filename-list-p pathname)
    (< 1 (+ 1 (len (cdr pathname)))))
   (equal
    (mv-nth
     1
     (find-dir-ent
      (make-dir-ent-list
       (mv-nth 0
               (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
      (car pathname)))
    0))
  :hints
  (("goal"
    :expand
    (hifat-place-file
     (mv-nth
      0
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit))
     pathname
     (m1-file dir-ent (lofat-file->contents file))))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-place-file-disjoint-lemma-1
  (implies
   (and (>= (dir-ent-first-cluster dir-ent)
            *ms-first-data-cluster*)
        (equal (mv-nth 1
                       (dir-ent-clusterchain fat32-in-memory dir-ent))
               0)
        (< (dir-ent-first-cluster dir-ent)
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32-in-memory)))
        (< (nfix n1)
           (len (find-n-free-clusters (effective-fat fat32-in-memory)
                                      n2)))
        (lofat-fs-p fat32-in-memory))
   (not
    (member-equal (nth n1
                       (find-n-free-clusters (effective-fat fat32-in-memory)
                                             n2))
                  (mv-nth 0
                          (dir-ent-clusterchain fat32-in-memory dir-ent)))))
  :hints
  (("goal"
    :in-theory (disable non-free-index-listp-correctness-2)
    :use
    (:instance non-free-index-listp-correctness-2
               (fa-table (effective-fat fat32-in-memory))
               (x (mv-nth 0
                          (dir-ent-clusterchain fat32-in-memory dir-ent)))
               (key (nth n1
                         (find-n-free-clusters (effective-fat fat32-in-memory)
                                               n2)))))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-place-file-disjoint-lemma-2
  (implies
   (and
    (dir-ent-directory-p
     (mv-nth
      0
      (find-dir-ent
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       (fat32-filename-fix (car pathname)))))
    (<= 2 (dir-ent-first-cluster dir-ent))
    (< (dir-ent-first-cluster dir-ent)
       (+ 2 (count-of-clusters fat32-in-memory)))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory dir-ent))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit)))
    (equal (mv-nth 1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
           0)
    (<=
     1
     (count-free-clusters
      (set-indices-in-fa-table
       (effective-fat fat32-in-memory)
       (mv-nth
        0
        (dir-ent-clusterchain
         fat32-in-memory
         (mv-nth
          0
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth
             0
             (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
           (fat32-filename-fix (car pathname))))))
       (make-list-ac
        (len
         (mv-nth
          0
          (dir-ent-clusterchain
           fat32-in-memory
           (mv-nth
            0
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth
               0
               (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
             (fat32-filename-fix (car pathname)))))))
        0 nil)))))
   (not
    (member-equal
     (nth
      '0
      (find-n-free-clusters
       (set-indices-in-fa-table
        (effective-fat fat32-in-memory)
        (mv-nth
         '0
         (dir-ent-clusterchain
          fat32-in-memory
          (mv-nth
           '0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              '0
              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
            (fat32-filename-fix (car pathname))))))
        (make-list-ac
         (len
          (mv-nth
           '0
           (dir-ent-clusterchain
            fat32-in-memory
            (mv-nth
             '0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                '0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
              (fat32-filename-fix (car pathname)))))))
         '0
         'nil))
       '1))
     (mv-nth '0
             (dir-ent-clusterchain fat32-in-memory dir-ent)))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite non-free-index-listp-correctness-2 . 1))
    :use
    ((:instance
      (:rewrite non-free-index-listp-correctness-2 . 1)
      (fa-table
       (set-indices-in-fa-table
        (effective-fat fat32-in-memory)
        (mv-nth
         0
         (dir-ent-clusterchain
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              0
              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
            (fat32-filename-fix (car pathname))))))
        (make-list-ac
         (len
          (mv-nth
           0
           (dir-ent-clusterchain
            fat32-in-memory
            (mv-nth
             0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
              (fat32-filename-fix (car pathname)))))))
         0 nil)))
      (x (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory dir-ent)))
      (key
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32-in-memory)
          (mv-nth
           0
           (dir-ent-clusterchain
            fat32-in-memory
            (mv-nth
             0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
              (fat32-filename-fix (car pathname))))))
          (make-list-ac
           (len
            (mv-nth
             0
             (dir-ent-clusterchain
              fat32-in-memory
              (mv-nth
               0
               (find-dir-ent (make-dir-ent-list
                              (mv-nth 0
                                      (dir-ent-clusterchain-contents
                                       fat32-in-memory root-dir-ent)))
                             (fat32-filename-fix (car pathname)))))))
           0 nil))
         1))))))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-place-file-disjoint-lemma-3
  (implies
   (and
    (<=
     2
     (dir-ent-first-cluster
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
        (fat32-filename-fix (car pathname))))))
    (<
     (dir-ent-first-cluster
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
        (fat32-filename-fix (car pathname)))))
     (+ 2 (count-of-clusters fat32-in-memory)))
    (<= 2 (dir-ent-first-cluster root-dir-ent))
    (< (dir-ent-first-cluster root-dir-ent)
       (+ 2 (count-of-clusters fat32-in-memory)))
    (equal
     (mv-nth 1
             (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent))
     0)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory root-dir-ent))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit)))
    (<=
     1
     (count-free-clusters
      (set-indices-in-fa-table
       (effective-fat fat32-in-memory)
       (mv-nth
        0
        (dir-ent-clusterchain
         fat32-in-memory
         (mv-nth
          0
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth
             0
             (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
           (fat32-filename-fix (car pathname))))))
       (make-list-ac
        (len
         (mv-nth
          0
          (dir-ent-clusterchain
           fat32-in-memory
           (mv-nth
            0
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth
               0
               (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
             (fat32-filename-fix (car pathname)))))))
        0 nil)))))
   (not
    (member-equal
     (nth
      '0
      (find-n-free-clusters
       (set-indices-in-fa-table
        (effective-fat fat32-in-memory)
        (mv-nth
         '0
         (dir-ent-clusterchain
          fat32-in-memory
          (mv-nth
           '0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              '0
              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
            (fat32-filename-fix (car pathname))))))
        (make-list-ac
         (len
          (mv-nth
           '0
           (dir-ent-clusterchain
            fat32-in-memory
            (mv-nth
             '0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                '0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
              (fat32-filename-fix (car pathname)))))))
         '0
         'nil))
       '1))
     (mv-nth '0
             (dir-ent-clusterchain fat32-in-memory root-dir-ent)))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite non-free-index-listp-correctness-2 . 1))
    :use
    ((:instance
      (:rewrite non-free-index-listp-correctness-2 . 1)
      (x (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory root-dir-ent)))
      (key
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32-in-memory)
          (mv-nth
           0
           (dir-ent-clusterchain
            fat32-in-memory
            (mv-nth
             0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
              (fat32-filename-fix (car pathname))))))
          (make-list-ac
           (len
            (mv-nth
             0
             (dir-ent-clusterchain
              fat32-in-memory
              (mv-nth
               0
               (find-dir-ent (make-dir-ent-list
                              (mv-nth 0
                                      (dir-ent-clusterchain-contents
                                       fat32-in-memory root-dir-ent)))
                             (fat32-filename-fix (car pathname)))))))
           0 nil))
         1)))
      (fa-table
       (set-indices-in-fa-table
        (effective-fat fat32-in-memory)
        (mv-nth
         0
         (dir-ent-clusterchain
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              0
              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
            (fat32-filename-fix (car pathname))))))
        (make-list-ac
         (len
          (mv-nth
           0
           (dir-ent-clusterchain
            fat32-in-memory
            (mv-nth
             0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
              (fat32-filename-fix (car pathname)))))))
         0 nil))))))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-place-file-disjoint-lemma-4
  (implies
   (and
    (<=
     2
     (dir-ent-first-cluster
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
        (fat32-filename-fix (car pathname))))))
    (<
     (dir-ent-first-cluster
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
        (fat32-filename-fix (car pathname)))))
     (+ 2 (count-of-clusters fat32-in-memory)))
    (<= 2 (dir-ent-first-cluster dir-ent))
    (< (dir-ent-first-cluster dir-ent)
       (+ 2 (count-of-clusters fat32-in-memory)))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory dir-ent))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit)))
    (equal (mv-nth 1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
           0)
    (<=
     1
     (count-free-clusters
      (set-indices-in-fa-table
       (effective-fat fat32-in-memory)
       (mv-nth
        0
        (dir-ent-clusterchain
         fat32-in-memory
         (mv-nth
          0
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth
             0
             (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
           (fat32-filename-fix (car pathname))))))
       (make-list-ac
        (len
         (mv-nth
          0
          (dir-ent-clusterchain
           fat32-in-memory
           (mv-nth
            0
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth
               0
               (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
             (fat32-filename-fix (car pathname)))))))
        0 nil)))))
   (not
    (member-equal
     (nth
      '0
      (find-n-free-clusters
       (set-indices-in-fa-table
        (effective-fat fat32-in-memory)
        (mv-nth
         '0
         (dir-ent-clusterchain
          fat32-in-memory
          (mv-nth
           '0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              '0
              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
            (fat32-filename-fix (car pathname))))))
        (make-list-ac
         (len
          (mv-nth
           '0
           (dir-ent-clusterchain
            fat32-in-memory
            (mv-nth
             '0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                '0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
              (fat32-filename-fix (car pathname)))))))
         '0
         'nil))
       '1))
     (mv-nth '0
             (dir-ent-clusterchain fat32-in-memory dir-ent)))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite non-free-index-listp-correctness-2 . 1))
    :use
    ((:instance
      (:rewrite non-free-index-listp-correctness-2 . 1)
      (x (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory dir-ent)))
      (key
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32-in-memory)
          (mv-nth
           0
           (dir-ent-clusterchain
            fat32-in-memory
            (mv-nth
             0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
              (fat32-filename-fix (car pathname))))))
          (make-list-ac
           (len
            (mv-nth
             0
             (dir-ent-clusterchain
              fat32-in-memory
              (mv-nth
               0
               (find-dir-ent (make-dir-ent-list
                              (mv-nth 0
                                      (dir-ent-clusterchain-contents
                                       fat32-in-memory root-dir-ent)))
                             (fat32-filename-fix (car pathname)))))))
           0 nil))
         1)))
      (fa-table
       (set-indices-in-fa-table
        (effective-fat fat32-in-memory)
        (mv-nth
         0
         (dir-ent-clusterchain
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              0
              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
            (fat32-filename-fix (car pathname))))))
        (make-list-ac
         (len
          (mv-nth
           0
           (dir-ent-clusterchain
            fat32-in-memory
            (mv-nth
             0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
              (fat32-filename-fix (car pathname)))))))
         0 nil))))))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-place-file-disjoint
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (dir-ent-p root-dir-ent)
    (dir-ent-directory-p root-dir-ent)
    (dir-ent-p dir-ent)
    (equal
     (mv-nth '1
             (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent))
     '0)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory dir-ent))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit)))
    (not (intersectp-equal
          (mv-nth 0
                  (dir-ent-clusterchain fat32-in-memory root-dir-ent))
          (mv-nth 0
                  (dir-ent-clusterchain fat32-in-memory dir-ent))))
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory root-dir-ent))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit)))
    (equal (mv-nth 1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
           0))
   (equal (dir-ent-clusterchain-contents
           (mv-nth 0
                   (lofat-place-file fat32-in-memory
                                     root-dir-ent pathname file))
           dir-ent)
          (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
  :hints (("goal" :induct (lofat-place-file fat32-in-memory
                                            root-dir-ent pathname file))))

(defthm
  lofat-place-file-correctness-1-lemma-8
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (dir-ent-p root-dir-ent)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory root-dir-ent))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit)))
    (equal
     (mv-nth 1
             (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent))
     0)
    (dir-ent-directory-p
     (mv-nth
      0
      (find-dir-ent
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       (car pathname)))))
   (equal
    (dir-ent-clusterchain-contents
     (mv-nth
      '0
      (lofat-place-file
       fat32-in-memory
       (mv-nth
        '0
        (find-dir-ent
         (make-dir-ent-list
          (mv-nth
           '0
           (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
         (car pathname)))
       (cdr pathname)
       file))
     root-dir-ent)
    (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
  :hints
  (("goal"
    :in-theory
    (disable
     (:rewrite dir-ent-clusterchain-contents-of-lofat-place-file-disjoint))
    :use
    ((:instance
      (:rewrite dir-ent-clusterchain-contents-of-lofat-place-file-disjoint)
      (dir-ent root-dir-ent)
      (file file)
      (pathname (cdr pathname))
      (root-dir-ent
       (mv-nth
        0
        (find-dir-ent
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
         (car pathname))))
      (fat32-in-memory fat32-in-memory))))))

(defthm lofat-place-file-correctness-1-lemma-9
  (implies (and (not (zp (cluster-size fat32-in-memory)))
                (< 0 (length (lofat-file->contents file))))
           (< 0
              (len (make-clusters (lofat-file->contents file)
                                  (cluster-size fat32-in-memory)))))
  :hints (("goal" :in-theory (enable make-clusters)))
  :rule-classes :linear)

(defthm
  dir-ent-clusterchain-contents-of-lofat-place-file-coincident-lemma-1
  (implies
   (and
    (<=
     2
     (dir-ent-first-cluster
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
        (car pathname)))))
    (<
     (dir-ent-first-cluster
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
        (car pathname))))
     (+ 2 (count-of-clusters fat32-in-memory)))
    (equal (mv-nth 1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
           0)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory dir-ent))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       entry-limit)))
    (<=
     1
     (count-free-clusters
      (set-indices-in-fa-table
       (effective-fat fat32-in-memory)
       (mv-nth
        0
        (dir-ent-clusterchain
         fat32-in-memory
         (mv-nth
          0
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth 0
                    (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
           (car pathname)))))
       (make-list-ac
        (len
         (mv-nth
          0
          (dir-ent-clusterchain
           fat32-in-memory
           (mv-nth
            0
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth
               0
               (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
             (car pathname))))))
        0 nil)))))
   (not
    (member-equal
     (nth
      '0
      (find-n-free-clusters
       (set-indices-in-fa-table
        (effective-fat fat32-in-memory)
        (mv-nth
         '0
         (dir-ent-clusterchain
          fat32-in-memory
          (mv-nth
           '0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth '0
                     (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
            (car pathname)))))
        (make-list-ac
         (len
          (mv-nth
           '0
           (dir-ent-clusterchain
            fat32-in-memory
            (mv-nth
             '0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                '0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
              (car pathname))))))
         '0
         'nil))
       '1))
     (mv-nth '0
             (dir-ent-clusterchain fat32-in-memory dir-ent)))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite non-free-index-listp-correctness-2 . 1))
    :use
    ((:instance
      (:rewrite non-free-index-listp-correctness-2 . 1)
      (x (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory dir-ent)))
      (key
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32-in-memory)
          (mv-nth
           0
           (dir-ent-clusterchain
            fat32-in-memory
            (mv-nth
             0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
              (car pathname)))))
          (make-list-ac
           (len
            (mv-nth
             0
             (dir-ent-clusterchain
              fat32-in-memory
              (mv-nth
               0
               (find-dir-ent
                (make-dir-ent-list
                 (mv-nth
                  0
                  (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                (car pathname))))))
           0 nil))
         1)))
      (fa-table
       (set-indices-in-fa-table
        (effective-fat fat32-in-memory)
        (mv-nth
         0
         (dir-ent-clusterchain
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth 0
                     (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
            (car pathname)))))
        (make-list-ac
         (len
          (mv-nth
           0
           (dir-ent-clusterchain
            fat32-in-memory
            (mv-nth
             0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
              (car pathname))))))
         0 nil))))))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-place-file-coincident-lemma-2
  (implies
   (and
    (dir-ent-directory-p
     (mv-nth
      0
      (find-dir-ent
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       (car pathname))))
    (<=
     1
     (count-free-clusters
      (set-indices-in-fa-table
       (effective-fat fat32-in-memory)
       (mv-nth
        0
        (dir-ent-clusterchain
         fat32-in-memory
         (mv-nth
          0
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth
             0
             (dir-ent-clusterchain-contents
              fat32-in-memory
              (mv-nth
               0
               (find-dir-ent
                (make-dir-ent-list
                 (mv-nth
                  0
                  (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                (car pathname))))))
           (cadr pathname)))))
       (make-list-ac
        (len
         (mv-nth
          0
          (dir-ent-clusterchain
           fat32-in-memory
           (mv-nth
            0
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth
               0
               (dir-ent-clusterchain-contents
                fat32-in-memory
                (mv-nth
                 0
                 (find-dir-ent
                  (make-dir-ent-list
                   (mv-nth
                    0
                    (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                  (car pathname))))))
             (cadr pathname))))))
        0 nil))))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       entry-limit))
     0)
    (<=
     2
     (dir-ent-first-cluster
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents
           fat32-in-memory
           (mv-nth
            0
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth
               0
               (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
             (car pathname))))))
        (cadr pathname)))))
    (<
     (dir-ent-first-cluster
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents
           fat32-in-memory
           (mv-nth
            0
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth
               0
               (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
             (car pathname))))))
        (cadr pathname))))
     (+ 2 (count-of-clusters fat32-in-memory))))
   (not
    (member-equal
     (nth
      '0
      (find-n-free-clusters
       (set-indices-in-fa-table
        (effective-fat fat32-in-memory)
        (mv-nth
         '0
         (dir-ent-clusterchain
          fat32-in-memory
          (mv-nth
           '0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              '0
              (dir-ent-clusterchain-contents
               fat32-in-memory
               (mv-nth
                '0
                (find-dir-ent
                 (make-dir-ent-list
                  (mv-nth
                   '0
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                 (car pathname))))))
            (car (cdr pathname))))))
        (make-list-ac
         (len
          (mv-nth
           '0
           (dir-ent-clusterchain
            fat32-in-memory
            (mv-nth
             '0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                '0
                (dir-ent-clusterchain-contents
                 fat32-in-memory
                 (mv-nth
                  '0
                  (find-dir-ent
                   (make-dir-ent-list
                    (mv-nth
                     '0
                     (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                   (car pathname))))))
              (car (cdr pathname)))))))
         '0
         'nil))
       '1))
     (mv-nth
      '0
      (dir-ent-clusterchain
       fat32-in-memory
       (mv-nth
        '0
        (find-dir-ent
         (make-dir-ent-list
          (mv-nth '0
                  (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
         (car pathname))))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite non-free-index-listp-correctness-2 . 1))
    :use
    ((:instance
      (:rewrite non-free-index-listp-correctness-2 . 1)
      (x
       (mv-nth
        0
        (dir-ent-clusterchain
         fat32-in-memory
         (mv-nth
          0
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth 0
                    (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
           (car pathname))))))
      (key
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32-in-memory)
          (mv-nth
           0
           (dir-ent-clusterchain
            fat32-in-memory
            (mv-nth
             0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                0
                (dir-ent-clusterchain-contents
                 fat32-in-memory
                 (mv-nth
                  0
                  (find-dir-ent
                   (make-dir-ent-list
                    (mv-nth
                     0
                     (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                   (car pathname))))))
              (cadr pathname)))))
          (make-list-ac
           (len
            (mv-nth
             0
             (dir-ent-clusterchain
              fat32-in-memory
              (mv-nth
               0
               (find-dir-ent
                (make-dir-ent-list
                 (mv-nth
                  0
                  (dir-ent-clusterchain-contents
                   fat32-in-memory
                   (mv-nth
                    0
                    (find-dir-ent (make-dir-ent-list
                                   (mv-nth 0
                                           (dir-ent-clusterchain-contents
                                            fat32-in-memory dir-ent)))
                                  (car pathname))))))
                (cadr pathname))))))
           0 nil))
         1)))
      (fa-table
       (set-indices-in-fa-table
        (effective-fat fat32-in-memory)
        (mv-nth
         0
         (dir-ent-clusterchain
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              0
              (dir-ent-clusterchain-contents
               fat32-in-memory
               (mv-nth
                0
                (find-dir-ent
                 (make-dir-ent-list
                  (mv-nth
                   0
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                 (car pathname))))))
            (cadr pathname)))))
        (make-list-ac
         (len
          (mv-nth
           0
           (dir-ent-clusterchain
            fat32-in-memory
            (mv-nth
             0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                0
                (dir-ent-clusterchain-contents
                 fat32-in-memory
                 (mv-nth
                  0
                  (find-dir-ent
                   (make-dir-ent-list
                    (mv-nth
                     0
                     (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                   (car pathname))))))
              (cadr pathname))))))
         0 nil))))))))

;; (defthm
;;   dir-ent-clusterchain-contents-of-lofat-place-file-coincident-lemma-3
;;   (implies
;;    (<=
;;     1
;;     (count-free-clusters
;;      (set-indices-in-fa-table
;;       (effective-fat fat32-in-memory)
;;       (mv-nth
;;        0
;;        (fat32-build-index-list
;;         (effective-fat fat32-in-memory)
;;         (dir-ent-first-cluster
;;          (mv-nth
;;           0
;;           (find-dir-ent
;;            (make-dir-ent-list
;;             (mv-nth
;;              0
;;              (dir-ent-clusterchain-contents
;;               fat32-in-memory
;;               (mv-nth
;;                0
;;                (find-dir-ent
;;                 (make-dir-ent-list
;;                  (mv-nth
;;                   0
;;                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
;;                 (car pathname))))))
;;            (cadr pathname))))
;;         (dir-ent-file-size
;;          (mv-nth
;;           0
;;           (find-dir-ent
;;            (make-dir-ent-list
;;             (mv-nth
;;              0
;;              (dir-ent-clusterchain-contents
;;               fat32-in-memory
;;               (mv-nth
;;                0
;;                (find-dir-ent
;;                 (make-dir-ent-list
;;                  (mv-nth
;;                   0
;;                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
;;                 (car pathname))))))
;;            (cadr pathname))))
;;         (cluster-size fat32-in-memory)))
;;       (make-list-ac
;;        (len
;;         (mv-nth
;;          0
;;          (fat32-build-index-list
;;           (effective-fat fat32-in-memory)
;;           (dir-ent-first-cluster
;;            (mv-nth
;;             0
;;             (find-dir-ent
;;              (make-dir-ent-list
;;               (mv-nth
;;                0
;;                (dir-ent-clusterchain-contents
;;                 fat32-in-memory
;;                 (mv-nth
;;                  0
;;                  (find-dir-ent
;;                   (make-dir-ent-list
;;                    (mv-nth
;;                     0
;;                     (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
;;                   (car pathname))))))
;;              (cadr pathname))))
;;           (dir-ent-file-size
;;            (mv-nth
;;             0
;;             (find-dir-ent
;;              (make-dir-ent-list
;;               (mv-nth
;;                0
;;                (dir-ent-clusterchain-contents
;;                 fat32-in-memory
;;                 (mv-nth
;;                  0
;;                  (find-dir-ent
;;                   (make-dir-ent-list
;;                    (mv-nth
;;                     0
;;                     (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
;;                   (car pathname))))))
;;              (cadr pathname))))
;;           (cluster-size fat32-in-memory))))
;;        0 nil))))
;;    (<=
;;     *ms-first-data-cluster*
;;     (nth
;;      '0
;;      (find-n-free-clusters
;;       (set-indices-in-fa-table
;;        (effective-fat fat32-in-memory)
;;        (mv-nth
;;         '0
;;         (fat32-build-index-list
;;          (effective-fat fat32-in-memory)
;;          (dir-ent-first-cluster
;;           (mv-nth
;;            '0
;;            (find-dir-ent
;;             (make-dir-ent-list
;;              (mv-nth
;;               '0
;;               (dir-ent-clusterchain-contents
;;                fat32-in-memory
;;                (mv-nth
;;                 '0
;;                 (find-dir-ent
;;                  (make-dir-ent-list
;;                   (mv-nth
;;                    '0
;;                    (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
;;                  (car pathname))))))
;;             (car (cdr pathname)))))
;;          (dir-ent-file-size
;;           (mv-nth
;;            '0
;;            (find-dir-ent
;;             (make-dir-ent-list
;;              (mv-nth
;;               '0
;;               (dir-ent-clusterchain-contents
;;                fat32-in-memory
;;                (mv-nth
;;                 '0
;;                 (find-dir-ent
;;                  (make-dir-ent-list
;;                   (mv-nth
;;                    '0
;;                    (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
;;                  (car pathname))))))
;;             (car (cdr pathname)))))
;;          (cluster-size fat32-in-memory)))
;;        (make-list-ac
;;         (len
;;          (mv-nth
;;           '0
;;           (fat32-build-index-list
;;            (effective-fat fat32-in-memory)
;;            (dir-ent-first-cluster
;;             (mv-nth
;;              '0
;;              (find-dir-ent
;;               (make-dir-ent-list
;;                (mv-nth
;;                 '0
;;                 (dir-ent-clusterchain-contents
;;                  fat32-in-memory
;;                  (mv-nth
;;                   '0
;;                   (find-dir-ent
;;                    (make-dir-ent-list
;;                     (mv-nth
;;                      '0
;;                      (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
;;                    (car pathname))))))
;;               (car (cdr pathname)))))
;;            (dir-ent-file-size
;;             (mv-nth
;;              '0
;;              (find-dir-ent
;;               (make-dir-ent-list
;;                (mv-nth
;;                 '0
;;                 (dir-ent-clusterchain-contents
;;                  fat32-in-memory
;;                  (mv-nth
;;                   '0
;;                   (find-dir-ent
;;                    (make-dir-ent-list
;;                     (mv-nth
;;                      '0
;;                      (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
;;                    (car pathname))))))
;;               (car (cdr pathname)))))
;;            (cluster-size fat32-in-memory))))
;;         '0
;;         'nil))
;;       '1))))
;;   :rule-classes :linear)

(defthm
  dir-ent-clusterchain-contents-of-lofat-place-file-coincident-lemma-4
  (implies (equal (mv-nth 1 (find-dir-ent dir-ent-list filename))
                  0)
           (< 0 (len dir-ent-list)))
  :rule-classes
  (:linear
   (:linear
    :corollary
    (implies (and (equal (mv-nth 1 (find-dir-ent dir-ent-list filename))
                         0)
                  (not (zp x)))
             (< 0 (* x (len dir-ent-list)))))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-place-file-coincident-lemma-5
  (implies
   (and (<= 2 (dir-ent-first-cluster dir-ent))
        (equal (mv-nth 1
                       (dir-ent-clusterchain fat32-in-memory dir-ent))
               0)
        (no-duplicatesp-equal
         (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory dir-ent))))
   (equal
    (count-free-clusters
     (set-indices-in-fa-table
      (effective-fat fat32-in-memory)
      (mv-nth 0
              (dir-ent-clusterchain fat32-in-memory dir-ent))
      (make-list-ac
       (len (mv-nth 0
                    (dir-ent-clusterchain fat32-in-memory dir-ent)))
       0 nil)))
    (+ (count-free-clusters (effective-fat fat32-in-memory))
       (len (mv-nth 0
                    (dir-ent-clusterchain fat32-in-memory dir-ent))))))
  :hints
  (("goal"
    :use
    (:instance
     get-clusterchain-contents-of-update-dir-contents-coincident-lemma-2
     (fa-table (effective-fat fat32-in-memory))
     (index-list (mv-nth 0
                         (dir-ent-clusterchain fat32-in-memory dir-ent)))))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-place-file-coincident-lemma-6
  (and
   (implies
    (and (dir-ent-directory-p dir-ent)
         (<= 2 (dir-ent-first-cluster dir-ent)))
    (equal (mv-nth 1
                   (clear-clusterchain fat32-in-memory
                                       (dir-ent-first-cluster dir-ent)
                                       *ms-max-dir-size*))
           (mv-nth 1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent))))
   (implies
    (and (not (dir-ent-directory-p dir-ent))
         (<= 2 (dir-ent-first-cluster dir-ent)))
    (equal (mv-nth 1
                   (clear-clusterchain fat32-in-memory
                                       (dir-ent-first-cluster dir-ent)
                                       (dir-ent-file-size dir-ent)))
           (mv-nth 1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))))
  :hints (("goal" :in-theory (enable dir-ent-clusterchain-contents
                                     clear-clusterchain-correctness-1))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-place-file-coincident-lemma-7
  t
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (<= 2 (dir-ent-first-cluster dir-ent))
          (lofat-fs-p fat32-in-memory)
          (dir-ent-directory-p dir-ent))
     (equal
      (effective-fat (mv-nth 0
                             (clear-clusterchain fat32-in-memory
                                                 (dir-ent-first-cluster dir-ent)
                                                 *ms-max-dir-size*)))
      (if
       (equal (mv-nth 1
                      (clear-clusterchain fat32-in-memory
                                          (dir-ent-first-cluster dir-ent)
                                          *ms-max-dir-size*))
              0)
       (set-indices-in-fa-table
        (effective-fat fat32-in-memory)
        (mv-nth 0
                (dir-ent-clusterchain fat32-in-memory dir-ent))
        (make-list-ac
         (len (mv-nth 0
                      (dir-ent-clusterchain fat32-in-memory dir-ent)))
         0 nil))
       (effective-fat fat32-in-memory))))
    :hints (("goal" :in-theory (enable dir-ent-clusterchain
                                       dir-ent-clusterchain-contents))))
   (:rewrite
    :corollary
    (implies
     (and (<= 2 (dir-ent-first-cluster dir-ent))
          (lofat-fs-p fat32-in-memory)
          (not (dir-ent-directory-p dir-ent)))
     (equal
      (effective-fat (mv-nth 0
                             (clear-clusterchain fat32-in-memory
                                                 (dir-ent-first-cluster dir-ent)
                                                 (dir-ent-file-size dir-ent))))
      (if
       (equal (mv-nth 1
                      (clear-clusterchain fat32-in-memory
                                          (dir-ent-first-cluster dir-ent)
                                          (dir-ent-file-size dir-ent)))
              0)
       (set-indices-in-fa-table
        (effective-fat fat32-in-memory)
        (mv-nth 0
                (dir-ent-clusterchain fat32-in-memory dir-ent))
        (make-list-ac
         (len (mv-nth 0
                      (dir-ent-clusterchain fat32-in-memory dir-ent)))
         0 nil))
       (effective-fat fat32-in-memory))))
    :hints (("goal" :in-theory (enable dir-ent-clusterchain
                                       dir-ent-clusterchain-contents))))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-place-file-coincident-lemma-8
  (implies
   (and
    (<=
     1
     (+
      (count-free-clusters (effective-fat fat32-in-memory))
      (len
       (mv-nth
        0
        (dir-ent-clusterchain
         fat32-in-memory
         (mv-nth
          0
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth 0
                    (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
           (car pathname))))))))
    (equal (mv-nth 1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
           0)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       entry-limit))
     0)
    (dir-ent-directory-p
     (mv-nth
      0
      (find-dir-ent
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       (car pathname))))
    (not
     (intersectp-equal
      (mv-nth 0
              (dir-ent-clusterchain fat32-in-memory dir-ent))
      (mv-nth
       0
       (dir-ent-clusterchain
        fat32-in-memory
        (mv-nth
         0
         (find-dir-ent
          (make-dir-ent-list
           (mv-nth 0
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
          (car pathname))))))))
   (not
    (member-equal
     (nth
      0
      (find-n-free-clusters
       (set-indices-in-fa-table
        (effective-fat fat32-in-memory)
        (mv-nth
         0
         (dir-ent-clusterchain
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth 0
                     (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
            (car pathname)))))
        (make-list-ac
         (len
          (mv-nth
           0
           (dir-ent-clusterchain
            fat32-in-memory
            (mv-nth
             0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
              (car pathname))))))
         0 nil))
       1))
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory dir-ent)))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite non-free-index-listp-correctness-2 . 1))
    :use
    ((:instance
      (:rewrite non-free-index-listp-correctness-2 . 1)
      (x (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory dir-ent)))
      (key
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32-in-memory)
          (mv-nth
           0
           (dir-ent-clusterchain
            fat32-in-memory
            (mv-nth
             0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
              (car pathname)))))
          (make-list-ac
           (len
            (mv-nth
             0
             (dir-ent-clusterchain
              fat32-in-memory
              (mv-nth
               0
               (find-dir-ent
                (make-dir-ent-list
                 (mv-nth
                  0
                  (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                (car pathname))))))
           0 nil))
         1)))
      (fa-table
       (set-indices-in-fa-table
        (effective-fat fat32-in-memory)
        (mv-nth
         0
         (dir-ent-clusterchain
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth 0
                     (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
            (car pathname)))))
        (make-list-ac
         (len
          (mv-nth
           0
           (dir-ent-clusterchain
            fat32-in-memory
            (mv-nth
             0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
              (car pathname))))))
         0 nil))))))))

;; Kinda general.
(defthm
  dir-ent-clusterchain-contents-of-lofat-place-file-coincident-lemma-9
  (implies
   (equal (mv-nth 1 (find-dir-ent dir-ent-list filename))
          0)
   (equal (dir-ent-filename (mv-nth 0 (find-dir-ent dir-ent-list filename)))
          filename)))

;; Move later
(defthm not-stringp-of-dir-ent-fix
  (not (stringp (dir-ent-fix dir-ent)))
  :hints (("goal" :in-theory (enable dir-ent-p dir-ent-fix)))
  :rule-classes :type-prescription)

(defthm
  dir-ent-set-first-cluster-file-size-of-dir-ent-set-first-cluster-file-size-lemma-1
  (implies (fat32-masked-entry-p masked-entry)
           (equal (logtail 16
                           (fat32-update-lower-28 entry masked-entry))
                  (logapp 12 (logtail 16 masked-entry)
                          (logtail 28 entry))))
  :hints (("goal" :in-theory (e/d (fat32-update-lower-28)
                                  (logapp)))))

(defthm
  dir-ent-set-first-cluster-file-size-of-dir-ent-set-first-cluster-file-size-lemma-2
  (implies (fat32-masked-entry-p masked-entry)
           (equal (logtail 24
                           (fat32-update-lower-28 entry masked-entry))
                  (logapp 4 (logtail 24 masked-entry)
                          (logtail 28 entry))))
  :hints (("goal" :in-theory (e/d (fat32-update-lower-28)
                                  (logapp)))))

(defthm
  dir-ent-set-first-cluster-file-size-of-dir-ent-set-first-cluster-file-size-lemma-3
  (implies (fat32-masked-entry-p masked-entry)
           (equal (logtail 8
                           (fat32-update-lower-28 entry masked-entry))
                  (logapp 20 (logtail 8 masked-entry)
                          (logtail 28 entry))))
  :hints (("goal" :in-theory (e/d (fat32-update-lower-28)
                                  (logapp)))))

(defthm
  dir-ent-set-first-cluster-file-size-of-dir-ent-set-first-cluster-file-size-lemma-4
  (implies (fat32-masked-entry-p masked-entry)
           (equal (loghead 8
                           (fat32-update-lower-28 entry masked-entry))
                  (loghead 8 masked-entry)))
  :hints (("goal" :in-theory (e/d (fat32-update-lower-28)
                                  (logapp)))))

;; Move later
(encapsulate
  ()

  (local (include-book "centaur/bitops/ihsext-basics" :dir :system))

  (defthm logtail-of-logior
    (equal (logtail pos (logior i j))
           (logior (logtail pos i)
                   (logtail pos j)))
    :hints (("goal" :in-theory (enable* ihsext-recursive-redefs
                                        ihsext-inductions))))

  (defthm logtail-of-ash
    (implies (and (integerp pos)
                  (<= 0 pos)
                  (integerp c))
             (equal (logtail pos (ash i c))
                    (if (>= pos c)
                        (logtail (- pos c) i)
                        (ash i (- c pos)))))
    :hints (("goal" :in-theory (enable* ihsext-recursive-redefs
                                        ihsext-inductions)))))

;; The hypotheses are somewhat weaker than this, but getting to them needs the
;; unsigned-byte-p terms to be expanded...
(defthm
  dir-ent-set-first-cluster-file-size-of-dir-ent-set-first-cluster-file-size-lemma-5
  (implies (and (unsigned-byte-p 8 a3)
                (unsigned-byte-p 8 a2)
                (unsigned-byte-p 8 a1)
                (unsigned-byte-p 8 a0))
           (equal (logtail 28 (combine32u a3 a2 a1 a0))
                  (logtail 4 a3)))
  :hints (("goal" :in-theory (e/d (combine32u) (logior ash)))))

;; Move later - and consider changing the definition of
;; dir-ent-set-first-cluster to fix first-cluster argument...
(defthm
  dir-ent-set-first-cluster-file-size-of-dir-ent-set-first-cluster-file-size
  (implies (and (fat32-masked-entry-p first-cluster1)
                (fat32-masked-entry-p first-cluster2))
           (equal (dir-ent-set-first-cluster-file-size
                   (dir-ent-set-first-cluster-file-size
                    dir-ent first-cluster1 file-size1)
                   first-cluster2 file-size2)
                  (dir-ent-set-first-cluster-file-size
                   dir-ent first-cluster2 file-size2)))
  :hints
  (("goal" :in-theory
    (e/d (dir-ent-set-first-cluster-file-size
          dir-ent-p-of-append len-when-dir-ent-p)
         (logapp)))))

;; Consider changing to remove free variables...
(defthm
  dir-ent-clusterchain-contents-of-lofat-place-file-coincident-lemma-10
  (implies (<= 2
               (dir-ent-first-cluster
                (mv-nth 0
                        (find-dir-ent dir-ent-list (car pathname)))))
           (> (len dir-ent-list) 0))
  :rule-classes :linear)

(defthm
  dir-ent-clusterchain-contents-of-lofat-place-file-coincident-lemma-11
  (implies
   (and
    (dir-ent-directory-p
     (mv-nth
      0
      (find-dir-ent
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       (car pathname))))
    (<=
     2
     (dir-ent-first-cluster
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents
           fat32-in-memory
           (mv-nth
            0
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth
               0
               (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
             (car pathname))))))
        (cadr pathname)))))
    (<
     (dir-ent-first-cluster
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents
           fat32-in-memory
           (mv-nth
            0
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth
               0
               (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
             (car pathname))))))
        (cadr pathname))))
     (+ 2 (count-of-clusters fat32-in-memory)))
    (<=
     1
     (count-free-clusters
      (set-indices-in-fa-table
       (effective-fat fat32-in-memory)
       (mv-nth
        0
        (dir-ent-clusterchain
         fat32-in-memory
         (mv-nth
          0
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth
             0
             (dir-ent-clusterchain-contents
              fat32-in-memory
              (mv-nth
               0
               (find-dir-ent
                (make-dir-ent-list
                 (mv-nth
                  0
                  (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                (car pathname))))))
           (cadr pathname)))))
       (make-list-ac
        (len
         (mv-nth
          0
          (dir-ent-clusterchain
           fat32-in-memory
           (mv-nth
            0
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth
               0
               (dir-ent-clusterchain-contents
                fat32-in-memory
                (mv-nth
                 0
                 (find-dir-ent
                  (make-dir-ent-list
                   (mv-nth
                    0
                    (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                  (car pathname))))))
             (cadr pathname))))))
        0 nil))))
    (equal (mv-nth 1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
           0)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory dir-ent))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       entry-limit))))
   (not
    (member-equal
     (nth
      0
      (find-n-free-clusters
       (set-indices-in-fa-table
        (effective-fat fat32-in-memory)
        (mv-nth
         0
         (dir-ent-clusterchain
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              0
              (dir-ent-clusterchain-contents
               fat32-in-memory
               (mv-nth
                0
                (find-dir-ent
                 (make-dir-ent-list
                  (mv-nth
                   0
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                 (car pathname))))))
            (cadr pathname)))))
        (make-list-ac
         (len
          (mv-nth
           0
           (dir-ent-clusterchain
            fat32-in-memory
            (mv-nth
             0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                0
                (dir-ent-clusterchain-contents
                 fat32-in-memory
                 (mv-nth
                  0
                  (find-dir-ent
                   (make-dir-ent-list
                    (mv-nth
                     0
                     (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                   (car pathname))))))
              (cadr pathname))))))
         0 nil))
       1))
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory dir-ent)))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite non-free-index-listp-correctness-2 . 1))
    :use
    ((:instance
      (:rewrite non-free-index-listp-correctness-2 . 1)
      (x (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory dir-ent)))
      (key
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32-in-memory)
          (mv-nth
           0
           (dir-ent-clusterchain
            fat32-in-memory
            (mv-nth
             0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                0
                (dir-ent-clusterchain-contents
                 fat32-in-memory
                 (mv-nth
                  0
                  (find-dir-ent
                   (make-dir-ent-list
                    (mv-nth
                     0
                     (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                   (car pathname))))))
              (cadr pathname)))))
          (make-list-ac
           (len
            (mv-nth
             0
             (dir-ent-clusterchain
              fat32-in-memory
              (mv-nth
               0
               (find-dir-ent
                (make-dir-ent-list
                 (mv-nth
                  0
                  (dir-ent-clusterchain-contents
                   fat32-in-memory
                   (mv-nth
                    0
                    (find-dir-ent (make-dir-ent-list
                                   (mv-nth 0
                                           (dir-ent-clusterchain-contents
                                            fat32-in-memory dir-ent)))
                                  (car pathname))))))
                (cadr pathname))))))
           0 nil))
         1)))
      (fa-table
       (set-indices-in-fa-table
        (effective-fat fat32-in-memory)
        (mv-nth
         0
         (dir-ent-clusterchain
          fat32-in-memory
          (mv-nth
           0
           (find-dir-ent
            (make-dir-ent-list
             (mv-nth
              0
              (dir-ent-clusterchain-contents
               fat32-in-memory
               (mv-nth
                0
                (find-dir-ent
                 (make-dir-ent-list
                  (mv-nth
                   0
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                 (car pathname))))))
            (cadr pathname)))))
        (make-list-ac
         (len
          (mv-nth
           0
           (dir-ent-clusterchain
            fat32-in-memory
            (mv-nth
             0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth
                0
                (dir-ent-clusterchain-contents
                 fat32-in-memory
                 (mv-nth
                  0
                  (find-dir-ent
                   (make-dir-ent-list
                    (mv-nth
                     0
                     (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                   (car pathname))))))
              (cadr pathname))))))
         0 nil))))))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-place-file-coincident-lemma-12
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (dir-ent-p dir-ent)
    (dir-ent-directory-p dir-ent)
    (equal (mv-nth 1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
           0)
    (<=
     (+
      32
      (*
       32
       (len
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents fat32-in-memory dir-ent))))))
     2097152)
    (equal
     (mv-nth
      1
      (update-dir-contents
       fat32-in-memory
       (dir-ent-first-cluster dir-ent)
       (nats=>string
        (flatten
         (place-dir-ent
          (make-dir-ent-list
           (mv-nth 0
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
          (dir-ent-set-first-cluster-file-size
           (dir-ent-set-filename
            '(0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
            (dir-ent-filename (lofat-file->dir-ent file)))
           0 0))))))
     0))
   (equal
    (dir-ent-clusterchain-contents
     (mv-nth
      0
      (update-dir-contents
       fat32-in-memory
       (dir-ent-first-cluster dir-ent)
       (nats=>string
        (flatten
         (place-dir-ent
          (make-dir-ent-list
           (mv-nth 0
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
          (dir-ent-set-first-cluster-file-size
           (dir-ent-set-filename
            '(0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
            (dir-ent-filename (lofat-file->dir-ent file)))
           0 0))))))
     dir-ent)
    (if
     (equal
      (mv-nth
       1
       (update-dir-contents
        fat32-in-memory
        (dir-ent-first-cluster dir-ent)
        (nats=>string
         (flatten
          (place-dir-ent
           (make-dir-ent-list
            (mv-nth 0
                    (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
           (dir-ent-set-first-cluster-file-size
            (dir-ent-set-filename
             '(0 0 0 0 0 0 0 0 0 0 0 0
                 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
             (dir-ent-filename (lofat-file->dir-ent file)))
            0 0))))))
      0)
     (cons
      (implode
       (append
        (explode
         (nats=>string
          (flatten
           (place-dir-ent
            (make-dir-ent-list
             (mv-nth 0
                     (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
            (dir-ent-set-first-cluster-file-size
             (dir-ent-set-filename
              '(0 0 0 0 0 0 0 0 0 0 0 0
                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
              (dir-ent-filename (lofat-file->dir-ent file)))
             0 0)))))
        (make-list-ac
         (+
          (-
           (len
            (explode
             (nats=>string
              (flatten
               (place-dir-ent
                (make-dir-ent-list
                 (mv-nth
                  0
                  (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                (dir-ent-set-first-cluster-file-size
                 (dir-ent-set-filename
                  '(0 0 0 0 0 0 0 0 0 0 0 0
                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                  (dir-ent-filename (lofat-file->dir-ent file)))
                 0 0)))))))
          (*
           (cluster-size fat32-in-memory)
           (len
            (make-clusters
             (nats=>string
              (flatten
               (place-dir-ent
                (make-dir-ent-list
                 (mv-nth
                  0
                  (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
                (dir-ent-set-first-cluster-file-size
                 (dir-ent-set-filename
                  '(0 0 0 0 0 0 0 0 0 0 0 0
                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                  (dir-ent-filename (lofat-file->dir-ent file)))
                 0 0))))
             (cluster-size fat32-in-memory)))))
         (code-char 0) nil)))
      '(0))
     (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))))

;; Move later
(defthm
  useless-dir-ent-p-of-find-dir-ent
  (implies
   (useful-dir-ent-list-p dir-ent-list)
   (not (useless-dir-ent-p (mv-nth 0
                                   (find-dir-ent dir-ent-list filename)))))
  :hints (("goal" :in-theory (enable useful-dir-ent-list-p))))

(make-event
 `(defthm
    dir-ent-clusterchain-contents-of-lofat-place-file-coincident-lemma-13
    (implies (and (equal (nth 0 (explode filename))
                         (code-char 0))
                  (useful-dir-ent-list-p dir-ent-list))
             (equal (mv-nth 1 (find-dir-ent dir-ent-list filename))
                    *enoent*))
    :hints (("goal" :in-theory (enable useful-dir-ent-list-p)))
    :rule-classes
    (:rewrite
     (:rewrite
      :corollary
      (implies (and (equal (mv-nth 1 (find-dir-ent dir-ent-list filename))
                           0)
                    (useful-dir-ent-list-p dir-ent-list))
               (not (equal (nth 0 (explode filename))
                           ,(code-char 0))))))))

;; The unsigned-byte-listp 8 hypothesis can go, maybe...
(defthm
  dir-ent-clusterchain-contents-of-lofat-place-file-coincident-lemma-14
  (implies
   (and
    (unsigned-byte-listp 8 dir-contents)
    (not (useless-dir-ent-p (dir-ent-fix dir-ent)))
    (not (equal (nth 0 (explode (dir-ent-filename dir-ent)))
                (code-char 0)))
    (equal
     (mv-nth 1
             (find-dir-ent (make-dir-ent-list (nats=>string dir-contents))
                           (dir-ent-filename dir-ent)))
     0)
    (not (zp cluster-size)))
   (equal
    (len (make-clusters (implode (nats=>chars (insert-dir-ent dir-contents dir-ent)))
                        cluster-size))
    (len (make-clusters (nats=>string dir-contents)
                        cluster-size))))
  :hints (("goal" :in-theory (enable len-of-make-clusters nats=>string)
           :do-not-induct t))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and
      (unsigned-byte-listp 8 dir-contents)
      (not (useless-dir-ent-p (dir-ent-fix dir-ent)))
      (not (equal (nth 0 (explode (dir-ent-filename dir-ent)))
                  (code-char 0)))
      (equal
       (mv-nth 1
               (find-dir-ent (make-dir-ent-list (nats=>string dir-contents))
                             (dir-ent-filename dir-ent)))
       0)
      (not (zp cluster-size)))
     (equal
      (len (make-clusters (nats=>string (insert-dir-ent dir-contents dir-ent))
                          cluster-size))
      (len (make-clusters (nats=>string dir-contents)
                          cluster-size))))
    :hints (("Goal" :in-theory (enable nats=>string)) ))))

;; Move later and rename.
(defthm dir-ent-clusterchain-contents-of-lofat-place-file-coincident-lemma-15
  (implies (not (equal (mv-nth 1 (find-dir-ent dir-ent-list filename))
                       0))
           (equal (mv-nth 0 (find-dir-ent dir-ent-list filename))
                  (dir-ent-fix nil))))

(defthm
  dir-ent-clusterchain-contents-of-lofat-place-file-coincident-1
  (b*
      (((mv clusterchain-contents error-code)
        (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
       (new-dir-ent
        (if
         (< 0
            (len (explode (lofat-file->contents file))))
         (if
          (<=
           2
           (dir-ent-first-cluster
            (mv-nth
             0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth 0
                       (dir-ent-clusterchain-contents
                        fat32-in-memory dir-ent)))
              (car pathname)))))
          (if
           (<
            (dir-ent-first-cluster
             (mv-nth
              0
              (find-dir-ent
               (make-dir-ent-list
                (mv-nth 0
                        (dir-ent-clusterchain-contents
                         fat32-in-memory dir-ent)))
               (car pathname))))
            (+ 2 (count-of-clusters fat32-in-memory)))
           (dir-ent-set-first-cluster-file-size
            (mv-nth
             0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth 0
                       (dir-ent-clusterchain-contents
                        fat32-in-memory dir-ent)))
              (car pathname)))
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32-in-memory)
               (mv-nth
                0
                (dir-ent-clusterchain
                 fat32-in-memory
                 (mv-nth
                  0
                  (find-dir-ent
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory dir-ent)))
                   (car pathname)))))
               (make-list-ac
                (len
                 (mv-nth
                  0
                  (dir-ent-clusterchain
                   fat32-in-memory
                   (mv-nth
                    0
                    (find-dir-ent
                     (make-dir-ent-list
                      (mv-nth 0
                              (dir-ent-clusterchain-contents
                               fat32-in-memory dir-ent)))
                     (car pathname))))))
                0 nil))
              1))
            (len (explode (lofat-file->contents file))))
           (dir-ent-set-first-cluster-file-size
            (mv-nth
             0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth 0
                       (dir-ent-clusterchain-contents
                        fat32-in-memory dir-ent)))
              (car pathname)))
            (nth
             0
             (find-n-free-clusters (effective-fat fat32-in-memory)
                                   1))
            (len (explode (lofat-file->contents file)))))
          (if
           (equal
            (mv-nth
             1
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth 0
                       (dir-ent-clusterchain-contents
                        fat32-in-memory dir-ent)))
              (car pathname)))
            0)
           (dir-ent-set-first-cluster-file-size
            (mv-nth
             0
             (find-dir-ent
              (make-dir-ent-list
               (mv-nth 0
                       (dir-ent-clusterchain-contents
                        fat32-in-memory dir-ent)))
              (car pathname)))
            (nth
             0
             (find-n-free-clusters (effective-fat fat32-in-memory)
                                   1))
            (len (explode (lofat-file->contents file))))
           (dir-ent-set-first-cluster-file-size
            (dir-ent-set-filename (dir-ent-fix nil)
                                  (car pathname))
            (nth
             0
             (find-n-free-clusters (effective-fat fat32-in-memory)
                                   1))
            (len (explode (lofat-file->contents file))))))
         (if
          (equal
           (mv-nth
            1
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth 0
                      (dir-ent-clusterchain-contents
                       fat32-in-memory dir-ent)))
             (car pathname)))
           0)
          (dir-ent-set-first-cluster-file-size
           (mv-nth
            0
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth 0
                      (dir-ent-clusterchain-contents
                       fat32-in-memory dir-ent)))
             (car pathname)))
           0 0)
          (dir-ent-set-first-cluster-file-size
           (dir-ent-set-filename (dir-ent-fix nil)
                                 (car pathname))
           0 0))))
       (new-contents
        (nats=>chars
         (insert-dir-ent (string=>nats clusterchain-contents)
                         new-dir-ent))))
    (implies
     (and
      (lofat-fs-p fat32-in-memory)
      (dir-ent-p dir-ent)
      (dir-ent-directory-p dir-ent)
      (fat32-filename-list-p pathname)
      (equal error-code 0)
      (equal
       (mv-nth 3
               (lofat-to-hifat-helper
                fat32-in-memory
                (make-dir-ent-list clusterchain-contents)
                entry-limit))
       0)
      (not-intersectp-list
       (mv-nth 0
               (dir-ent-clusterchain fat32-in-memory dir-ent))
       (mv-nth 2
               (lofat-to-hifat-helper
                fat32-in-memory
                (make-dir-ent-list clusterchain-contents)
                entry-limit)))
      (not
       (<
        '2097152
        (binary-+
         '32
         (len (explode$inline
               (mv-nth '0
                       (dir-ent-clusterchain-contents
                        fat32-in-memory dir-ent)))))))
      (equal
       (mv-nth
        1
        (lofat-place-file fat32-in-memory dir-ent pathname file))
       0)
      (lofat-regular-file-p file))
     (equal
      (dir-ent-clusterchain-contents
       (mv-nth
        0
        (lofat-place-file fat32-in-memory dir-ent pathname file))
       dir-ent)
      (if
       (atom (cdr pathname))
       (mv
        (implode
         (append
          new-contents
          (make-list-ac
           (-
            (*
             (cluster-size fat32-in-memory)
             (len
              (make-clusters (implode new-contents)
                             (cluster-size fat32-in-memory))))
            (len new-contents))
           (code-char 0)
           nil)))
        0)
       (dir-ent-clusterchain-contents
        fat32-in-memory dir-ent)))))
  :hints
  (("goal"
    :expand
    (lofat-place-file fat32-in-memory dir-ent pathname file)
    :do-not-induct t
    :in-theory
    (e/d (update-dir-contents-correctness-1
          nats=>string)
         (explode-of-dir-ent-filename
          clear-clusterchain-correctness-1
          effective-fat-of-clear-clusterchain)))))

(defthm
  lofat-place-file-correctness-1-lemma-10
  (implies
   (and
    (syntaxp (variablep entry-limit))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit))))))))
     0)
    (useful-dir-ent-list-p dir-ent-list)
    (<
     (+
      1
      (hifat-entry-count
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32-in-memory
         (make-dir-ent-list (mv-nth 0
                                    (dir-ent-clusterchain-contents
                                     fat32-in-memory (car dir-ent-list))))
         (+ -1 entry-limit))))
      (hifat-entry-count
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
                       (dir-ent-clusterchain-contents
                        fat32-in-memory (car dir-ent-list))))
              (+ -1 entry-limit))))))))))
     entry-limit))
   (equal
    (mv-nth
     0
     (lofat-to-hifat-helper
      fat32-in-memory (cdr dir-ent-list)
      (+
       -1 entry-limit
       (-
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  (make-dir-ent-list
                   (mv-nth 0
                           (dir-ent-clusterchain-contents
                            fat32-in-memory (car dir-ent-list))))
                  (+ -1 entry-limit))))))))
    (mv-nth 0
            (lofat-to-hifat-helper fat32-in-memory (cdr dir-ent-list)
                                   (+ -1 entry-limit)))))
  :hints
  (("goal"
    :use
    (:instance
     lofat-to-hifat-helper-correctness-4
     (entry-limit2 (+ -1 entry-limit))
     (dir-ent-list (cdr dir-ent-list))
     (entry-limit1
      (+
       -1 entry-limit
       (-
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  (make-dir-ent-list
                   (mv-nth 0
                           (dir-ent-clusterchain-contents
                            fat32-in-memory (car dir-ent-list))))
                  (+ -1 entry-limit)))))))))))

(defthm
  lofat-place-file-correctness-1-lemma-11
  (implies
   (and (useful-dir-ent-list-p dir-ent-list)
        (not (dir-ent-directory-p (dir-ent-fix dir-ent)))
        (zp (mv-nth 3
                    (lofat-to-hifat-helper fat32-in-memory
                                           dir-ent-list entry-limit)))
        (force
         (> (nfix entry-limit)
            (hifat-entry-count
             (mv-nth 0
                     (lofat-to-hifat-helper fat32-in-memory
                                            dir-ent-list entry-limit))))))
   (equal
    (mv-nth 0
            (lofat-to-hifat-helper fat32-in-memory
                                   (place-dir-ent dir-ent-list dir-ent)
                                   entry-limit))
    (put-assoc-equal
     (dir-ent-filename dir-ent)
     (m1-file
      dir-ent
      (if (or (< (dir-ent-first-cluster (dir-ent-fix dir-ent))
                 2)
              (<= (+ 2 (count-of-clusters fat32-in-memory))
                  (dir-ent-first-cluster (dir-ent-fix dir-ent))))
          ""
          (mv-nth 0
                  (dir-ent-clusterchain-contents fat32-in-memory
                                                 (dir-ent-fix dir-ent)))))
     (mv-nth 0
             (lofat-to-hifat-helper fat32-in-memory
                                    dir-ent-list
                                    entry-limit)))))
  :hints
  (("goal" :in-theory
    (e/d (lofat-to-hifat-helper hifat-entry-count)
         ((:rewrite
           dir-ent-clusterchain-contents-of-lofat-place-file-coincident-lemma-13
           . 1)
          (:rewrite nth-of-effective-fat)
          (:rewrite nth-of-nats=>chars)
          (:linear nth-when-dir-ent-p)
          (:rewrite explode-of-dir-ent-filename)
          (:rewrite take-of-len-free)
          (:rewrite
           hifat-entry-count-of-lofat-to-hifat-helper-of-delete-dir-ent-lemma-3)
          (:linear count-free-clusters-correctness-1)
          (:rewrite put-assoc-equal-without-change . 2)
          (:rewrite nats=>chars-of-take)))
    :induct (lofat-to-hifat-helper fat32-in-memory
                                   dir-ent-list entry-limit)
    :do-not-induct t
    :expand (:free (fat32-in-memory dir-ent dir-ent-list entry-limit)
                   (lofat-to-hifat-helper fat32-in-memory
                                          (cons dir-ent dir-ent-list)
                                          entry-limit)))))

(defthm
  lofat-place-file-correctness-1-lemma-12
  (implies
   (and
    (syntaxp (variablep entry-limit))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit))))))))
     0)
    (useful-dir-ent-list-p dir-ent-list)
    (<
     (+
      1
      (hifat-entry-count
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32-in-memory
         (make-dir-ent-list (mv-nth 0
                                    (dir-ent-clusterchain-contents
                                     fat32-in-memory (car dir-ent-list))))
         (+ -1 entry-limit))))
      (hifat-entry-count
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
                       (dir-ent-clusterchain-contents
                        fat32-in-memory (car dir-ent-list))))
              (+ -1 entry-limit))))))))))
     entry-limit)
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory (dir-ent-fix dir-ent)))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit)))))))))
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32-in-memory (cdr dir-ent-list)
                                          (+ -1 entry-limit)))
           0))
   (not-intersectp-list
    (mv-nth 0
            (dir-ent-clusterchain fat32-in-memory (dir-ent-fix dir-ent)))
    (mv-nth 2
            (lofat-to-hifat-helper fat32-in-memory (cdr dir-ent-list)
                                   (+ -1 entry-limit)))))
  :hints
  (("goal"
    :use
    (:instance
     lofat-to-hifat-helper-correctness-4
     (entry-limit1 (+ -1 entry-limit))
     (entry-limit2
      (+
       -1 entry-limit
       (-
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  (make-dir-ent-list
                   (mv-nth 0
                           (dir-ent-clusterchain-contents
                            fat32-in-memory (car dir-ent-list))))
                  (+ -1 entry-limit)))))))
     (dir-ent-list (cdr dir-ent-list))
     (fat32-in-memory fat32-in-memory)))))

(defthm
  lofat-place-file-correctness-1-lemma-13
  (implies
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit))))))))
     0)
    (useful-dir-ent-list-p dir-ent-list)
    (<
     (+
      1
      (hifat-entry-count
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32-in-memory
         (make-dir-ent-list (mv-nth 0
                                    (dir-ent-clusterchain-contents
                                     fat32-in-memory (car dir-ent-list))))
         (+ -1 entry-limit))))
      (hifat-entry-count
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
                       (dir-ent-clusterchain-contents
                        fat32-in-memory (car dir-ent-list))))
              (+ -1 entry-limit))))))))))
     entry-limit))
   (equal (mv-nth 3
                  (lofat-to-hifat-helper fat32-in-memory (cdr dir-ent-list)
                                         (+ -1 entry-limit)))
          0))
  :hints
  (("goal"
    :use
    (:instance
     (:rewrite lofat-to-hifat-helper-correctness-4)
     (entry-limit1
      (+
       -1 entry-limit
       (-
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  (make-dir-ent-list
                   (mv-nth 0
                           (dir-ent-clusterchain-contents
                            fat32-in-memory (car dir-ent-list))))
                  (+ -1 entry-limit)))))))
     (entry-limit2 (+ -1 entry-limit))
     (dir-ent-list (cdr dir-ent-list))
     (fat32-in-memory fat32-in-memory)))))

(defthm
  lofat-place-file-correctness-1-lemma-14
  (implies
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit))))))))
     0)
    (useful-dir-ent-list-p dir-ent-list)
    (<
     (+
      1
      (hifat-entry-count
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32-in-memory
         (make-dir-ent-list (mv-nth 0
                                    (dir-ent-clusterchain-contents
                                     fat32-in-memory (car dir-ent-list))))
         (+ -1 entry-limit))))
      (hifat-entry-count
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
                       (dir-ent-clusterchain-contents
                        fat32-in-memory (car dir-ent-list))))
              (+ -1 entry-limit))))))))))
     entry-limit)
    (not-intersectp-list
     x
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32-in-memory (cdr dir-ent-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper
                   fat32-in-memory
                   (make-dir-ent-list
                    (mv-nth 0
                            (dir-ent-clusterchain-contents
                             fat32-in-memory (car dir-ent-list))))
                   (+ -1 entry-limit))))))))))
   (not-intersectp-list
    x
    (mv-nth 2
            (lofat-to-hifat-helper fat32-in-memory (cdr dir-ent-list)
                                   (+ -1 entry-limit)))))
  :hints
  (("goal"
    :use
    (:instance
     (:rewrite lofat-to-hifat-helper-correctness-4)
     (entry-limit1
      (+
       -1 entry-limit
       (-
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper
                  fat32-in-memory
                  (make-dir-ent-list
                   (mv-nth 0
                           (dir-ent-clusterchain-contents
                            fat32-in-memory (car dir-ent-list))))
                  (+ -1 entry-limit)))))))
     (entry-limit2 (+ -1 entry-limit))
     (dir-ent-list (cdr dir-ent-list))))))

;; Hypotheses are minimal.
(defthm
  lofat-place-file-correctness-1-lemma-15
  (implies
   (and
    (useful-dir-ent-list-p dir-ent-list)
    (not (dir-ent-directory-p (dir-ent-fix dir-ent)))
    (zp (mv-nth 3
                (lofat-to-hifat-helper fat32-in-memory
                                       dir-ent-list entry-limit)))
    (force
     (> (nfix entry-limit)
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper fat32-in-memory
                                        dir-ent-list entry-limit)))))
    (or
     (< (dir-ent-first-cluster (dir-ent-fix dir-ent))
        2)
     (<= (+ 2 (count-of-clusters fat32-in-memory))
         (dir-ent-first-cluster (dir-ent-fix dir-ent)))
     (and
      (equal
       (mv-nth
        1
        (dir-ent-clusterchain-contents fat32-in-memory (dir-ent-fix dir-ent)))
       0)
      (not
       (intersectp-equal x
                         (mv-nth 0
                                 (dir-ent-clusterchain fat32-in-memory
                                                       (dir-ent-fix dir-ent)))))))
    (not-intersectp-list
     x
     (mv-nth 2
             (lofat-to-hifat-helper fat32-in-memory
                                    dir-ent-list entry-limit))))
   (not-intersectp-list
    x
    (mv-nth 2
            (lofat-to-hifat-helper fat32-in-memory
                                   (place-dir-ent dir-ent-list dir-ent)
                                   entry-limit))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lofat-to-hifat-helper hifat-entry-count not-intersectp-list)
     ((:rewrite
       dir-ent-clusterchain-contents-of-lofat-place-file-coincident-lemma-13
       . 1)
      (:rewrite nth-of-effective-fat)
      (:rewrite nth-of-nats=>chars)
      (:linear nth-when-dir-ent-p)
      (:rewrite explode-of-dir-ent-filename)
      (:rewrite take-of-len-free)
      (:rewrite
       hifat-entry-count-of-lofat-to-hifat-helper-of-delete-dir-ent-lemma-3)
      (:linear count-free-clusters-correctness-1)
      (:rewrite put-assoc-equal-without-change . 2)
      (:rewrite nats=>chars-of-take)
      (:rewrite hifat-to-lofat-inversion-lemma-2)))
    :induct (lofat-to-hifat-helper fat32-in-memory
                                   dir-ent-list entry-limit)
    :expand ((:free (fat32-in-memory dir-ent dir-ent-list entry-limit)
                    (lofat-to-hifat-helper fat32-in-memory
                                           (cons dir-ent dir-ent-list)
                                           entry-limit))
             (:free (x) (intersectp-equal nil x))))))

;; Hypotheses are minimal.
(defthm
  lofat-place-file-correctness-1-lemma-16
  (implies
   (and
    (useful-dir-ent-list-p dir-ent-list)
    (not (dir-ent-directory-p (dir-ent-fix dir-ent)))
    (zp (mv-nth 3
                (lofat-to-hifat-helper fat32-in-memory
                                       dir-ent-list entry-limit)))
    (force
     (> (nfix entry-limit)
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper fat32-in-memory
                                        dir-ent-list entry-limit)))))
    (or
     (< (dir-ent-first-cluster (dir-ent-fix dir-ent))
        2)
     (<= (+ 2 (count-of-clusters fat32-in-memory))
         (dir-ent-first-cluster (dir-ent-fix dir-ent)))
     (and
      (equal
       (mv-nth
        1
        (dir-ent-clusterchain-contents fat32-in-memory (dir-ent-fix dir-ent)))
       0)
      (not-intersectp-list
       (mv-nth 0
               (dir-ent-clusterchain fat32-in-memory (dir-ent-fix dir-ent)))
       x)))
    (not (member-intersectp-equal
          x
          (mv-nth 2
                  (lofat-to-hifat-helper fat32-in-memory
                                         dir-ent-list entry-limit)))))
   (not
    (member-intersectp-equal
     x
     (mv-nth 2
             (lofat-to-hifat-helper fat32-in-memory
                                    (place-dir-ent dir-ent-list dir-ent)
                                    entry-limit)))))
  :hints
  (("goal"
    :induct (member-intersectp-equal
             x
             (mv-nth 2
                     (lofat-to-hifat-helper fat32-in-memory
                                            dir-ent-list entry-limit)))
    :in-theory (enable not-intersectp-list))))

;; Hypotheses are minimal.
(defthm
  lofat-place-file-correctness-1-lemma-17
  (implies
   (and
    (useful-dir-ent-list-p dir-ent-list)
    (not (dir-ent-directory-p (dir-ent-fix dir-ent)))
    (zp (mv-nth 3
                (lofat-to-hifat-helper fat32-in-memory
                                       dir-ent-list entry-limit)))
    (force
     (> (nfix entry-limit)
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper fat32-in-memory
                                        dir-ent-list entry-limit)))))
    (or
     (< (dir-ent-first-cluster (dir-ent-fix dir-ent))
        2)
     (<= (+ 2 (count-of-clusters fat32-in-memory))
         (dir-ent-first-cluster (dir-ent-fix dir-ent)))
     (and
      (equal
       (mv-nth
        1
        (dir-ent-clusterchain-contents fat32-in-memory (dir-ent-fix dir-ent)))
       0)
      (no-duplicatesp-equal
       (mv-nth 0
               (dir-ent-clusterchain fat32-in-memory (dir-ent-fix dir-ent))))
      (not-intersectp-list
       (mv-nth 0
               (dir-ent-clusterchain fat32-in-memory (dir-ent-fix dir-ent)))
       (mv-nth 2
               (lofat-to-hifat-helper fat32-in-memory
                                      dir-ent-list entry-limit))))))
   (equal (mv-nth 3
                  (lofat-to-hifat-helper fat32-in-memory
                                         (place-dir-ent dir-ent-list dir-ent)
                                         entry-limit))
          0))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lofat-to-hifat-helper hifat-entry-count not-intersectp-list)
     ((:rewrite
       dir-ent-clusterchain-contents-of-lofat-place-file-coincident-lemma-13
       . 1)
      (:rewrite nth-of-effective-fat)
      (:rewrite nth-of-nats=>chars)
      (:linear nth-when-dir-ent-p)
      (:rewrite explode-of-dir-ent-filename)
      (:rewrite take-of-len-free)
      (:rewrite
       hifat-entry-count-of-lofat-to-hifat-helper-of-delete-dir-ent-lemma-3)
      (:linear count-free-clusters-correctness-1)
      (:rewrite put-assoc-equal-without-change . 2)
      (:rewrite nats=>chars-of-take)
      (:definition hifat-file-alist-fix)
      (:rewrite hifat-subsetp-reflexive-lemma-3)))
    :induct (lofat-to-hifat-helper fat32-in-memory
                                   dir-ent-list entry-limit)
    :do-not-induct t
    :expand (:free (fat32-in-memory dir-ent dir-ent-list entry-limit)
                   (lofat-to-hifat-helper fat32-in-memory
                                          (cons dir-ent dir-ent-list)
                                          entry-limit)))))

(defthm
  lofat-place-file-correctness-1-lemma-18
  (implies
   (and (< (dir-ent-first-cluster root-dir-ent)
           (+ 2 (count-of-clusters fat32-in-memory)))
        (<= 1
            (count-free-clusters (effective-fat fat32-in-memory))))
   (not
    (< (binary-+ '2
                 (count-of-clusters fat32-in-memory))
       (binary-+ '1
                 (nth '0
                      (find-n-free-clusters (effective-fat fat32-in-memory)
                                            '1))))))
  :hints
  (("goal"
    :do-not-induct t
    :use
    (:instance (:rewrite painful-debugging-lemma-13)
               (x (nth 0
                       (find-n-free-clusters (effective-fat fat32-in-memory)
                                             1)))
               (y (+ 2
                     (count-of-clusters fat32-in-memory)))))))

;; (defthm
;;   dir-ent-clusterchain-contents-of-lofat-place-file-coincident-lemma-25
;;   (implies
;;    (<=
;;     1
;;     (count-free-clusters
;;      (set-indices-in-fa-table
;;       (effective-fat fat32-in-memory)
;;       (mv-nth
;;        0
;;        (fat32-build-index-list
;;         (effective-fat fat32-in-memory)
;;         (dir-ent-first-cluster
;;          (mv-nth
;;           0
;;           (find-dir-ent
;;            (make-dir-ent-list
;;             (mv-nth
;;              0
;;              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;            (car pathname))))
;;         (dir-ent-file-size
;;          (mv-nth
;;           0
;;           (find-dir-ent
;;            (make-dir-ent-list
;;             (mv-nth
;;              0
;;              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;            (car pathname))))
;;         (cluster-size fat32-in-memory)))
;;       (make-list-ac
;;        (len
;;         (mv-nth
;;          0
;;          (fat32-build-index-list
;;           (effective-fat fat32-in-memory)
;;           (dir-ent-first-cluster
;;            (mv-nth
;;             0
;;             (find-dir-ent
;;              (make-dir-ent-list
;;               (mv-nth
;;                0
;;                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;              (car pathname))))
;;           (dir-ent-file-size
;;            (mv-nth
;;             0
;;             (find-dir-ent
;;              (make-dir-ent-list
;;               (mv-nth
;;                0
;;                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;              (car pathname))))
;;           (cluster-size fat32-in-memory))))
;;        0 nil))))
;;    (not
;;     (<
;;      (nth
;;       '0
;;       (find-n-free-clusters
;;        (set-indices-in-fa-table
;;         (effective-fat fat32-in-memory)
;;         (mv-nth
;;          '0
;;          (fat32-build-index-list
;;           (effective-fat fat32-in-memory)
;;           (dir-ent-first-cluster
;;            (mv-nth
;;             '0
;;             (find-dir-ent
;;              (make-dir-ent-list
;;               (mv-nth
;;                '0
;;                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;              (car pathname))))
;;           (dir-ent-file-size
;;            (mv-nth
;;             '0
;;             (find-dir-ent
;;              (make-dir-ent-list
;;               (mv-nth
;;                '0
;;                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;              (car pathname))))
;;           (cluster-size fat32-in-memory)))
;;         (make-list-ac
;;          (len
;;           (mv-nth
;;            '0
;;            (fat32-build-index-list
;;             (effective-fat fat32-in-memory)
;;             (dir-ent-first-cluster
;;              (mv-nth
;;               '0
;;               (find-dir-ent
;;                (make-dir-ent-list (mv-nth '0
;;                                           (dir-ent-clusterchain-contents
;;                                            fat32-in-memory root-dir-ent)))
;;                (car pathname))))
;;             (dir-ent-file-size
;;              (mv-nth
;;               '0
;;               (find-dir-ent
;;                (make-dir-ent-list (mv-nth '0
;;                                           (dir-ent-clusterchain-contents
;;                                            fat32-in-memory root-dir-ent)))
;;                (car pathname))))
;;             (cluster-size fat32-in-memory))))
;;          '0
;;          'nil))
;;        '1))
;;      '0))))

;; (defthm
;;   dir-ent-clusterchain-contents-of-lofat-place-file-coincident-lemma-26
;;   (implies
;;    (and
;;     (equal
;;      (mv-nth
;;       3
;;       (lofat-to-hifat-helper
;;        fat32-in-memory
;;        (make-dir-ent-list
;;         (mv-nth 0
;;                 (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;        entry-limit))
;;      0)
;;     (not-intersectp-list
;;      (mv-nth 0
;;              (dir-ent-clusterchain fat32-in-memory root-dir-ent))
;;      (mv-nth
;;       2
;;       (lofat-to-hifat-helper
;;        fat32-in-memory
;;        (make-dir-ent-list
;;         (mv-nth 0
;;                 (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;        entry-limit)))
;;     (equal
;;      (mv-nth 1
;;              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent))
;;      0)
;;     (<=
;;      2
;;      (dir-ent-first-cluster
;;       (mv-nth
;;        0
;;        (find-dir-ent
;;         (make-dir-ent-list
;;          (mv-nth
;;           0
;;           (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;         (car pathname)))))
;;     (<
;;      (dir-ent-first-cluster
;;       (mv-nth
;;        0
;;        (find-dir-ent
;;         (make-dir-ent-list
;;          (mv-nth
;;           0
;;           (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;         (car pathname))))
;;      (+ 2 (count-of-clusters fat32-in-memory)))
;;     (not
;;      (dir-ent-directory-p
;;       (mv-nth
;;        0
;;        (find-dir-ent
;;         (make-dir-ent-list
;;          (mv-nth
;;           0
;;           (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;         (car pathname)))))
;;     (<=
;;      1
;;      (count-free-clusters
;;       (set-indices-in-fa-table
;;        (effective-fat fat32-in-memory)
;;        (mv-nth
;;         0
;;         (fat32-build-index-list
;;          (effective-fat fat32-in-memory)
;;          (dir-ent-first-cluster
;;           (mv-nth
;;            0
;;            (find-dir-ent
;;             (make-dir-ent-list
;;              (mv-nth
;;               0
;;               (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;             (car pathname))))
;;          (dir-ent-file-size
;;           (mv-nth
;;            0
;;            (find-dir-ent
;;             (make-dir-ent-list
;;              (mv-nth
;;               0
;;               (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;             (car pathname))))
;;          (cluster-size fat32-in-memory)))
;;        (make-list-ac
;;         (len
;;          (mv-nth
;;           0
;;           (fat32-build-index-list
;;            (effective-fat fat32-in-memory)
;;            (dir-ent-first-cluster
;;             (mv-nth
;;              0
;;              (find-dir-ent
;;               (make-dir-ent-list
;;                (mv-nth
;;                 0
;;                 (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;               (car pathname))))
;;            (dir-ent-file-size
;;             (mv-nth
;;              0
;;              (find-dir-ent
;;               (make-dir-ent-list
;;                (mv-nth
;;                 0
;;                 (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;               (car pathname))))
;;            (cluster-size fat32-in-memory))))
;;         0 nil)))))
;;    (not
;;     (member-equal
;;      (nth
;;       '0
;;       (find-n-free-clusters
;;        (set-indices-in-fa-table
;;         (effective-fat fat32-in-memory)
;;         (mv-nth
;;          '0
;;          (fat32-build-index-list
;;           (effective-fat fat32-in-memory)
;;           (dir-ent-first-cluster
;;            (mv-nth
;;             '0
;;             (find-dir-ent
;;              (make-dir-ent-list
;;               (mv-nth
;;                '0
;;                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;              (car pathname))))
;;           (dir-ent-file-size
;;            (mv-nth
;;             '0
;;             (find-dir-ent
;;              (make-dir-ent-list
;;               (mv-nth
;;                '0
;;                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;              (car pathname))))
;;           (cluster-size fat32-in-memory)))
;;         (make-list-ac
;;          (len
;;           (mv-nth
;;            '0
;;            (fat32-build-index-list
;;             (effective-fat fat32-in-memory)
;;             (dir-ent-first-cluster
;;              (mv-nth
;;               '0
;;               (find-dir-ent
;;                (make-dir-ent-list (mv-nth '0
;;                                           (dir-ent-clusterchain-contents
;;                                            fat32-in-memory root-dir-ent)))
;;                (car pathname))))
;;             (dir-ent-file-size
;;              (mv-nth
;;               '0
;;               (find-dir-ent
;;                (make-dir-ent-list (mv-nth '0
;;                                           (dir-ent-clusterchain-contents
;;                                            fat32-in-memory root-dir-ent)))
;;                (car pathname))))
;;             (cluster-size fat32-in-memory))))
;;          '0
;;          'nil))
;;        '1))
;;      (mv-nth '0
;;              (dir-ent-clusterchain fat32-in-memory root-dir-ent)))))
;;   :hints
;;   (("goal"
;;     :in-theory (disable (:rewrite non-free-index-listp-correctness-2 . 1))
;;     :use
;;     ((:instance
;;       (:rewrite non-free-index-listp-correctness-2 . 1)
;;       (x (mv-nth 0
;;                  (dir-ent-clusterchain fat32-in-memory root-dir-ent)))
;;       (key
;;        (nth
;;         0
;;         (find-n-free-clusters
;;          (set-indices-in-fa-table
;;           (effective-fat fat32-in-memory)
;;           (mv-nth
;;            0
;;            (fat32-build-index-list
;;             (effective-fat fat32-in-memory)
;;             (dir-ent-first-cluster
;;              (mv-nth
;;               0
;;               (find-dir-ent
;;                (make-dir-ent-list (mv-nth 0
;;                                           (dir-ent-clusterchain-contents
;;                                            fat32-in-memory root-dir-ent)))
;;                (car pathname))))
;;             (dir-ent-file-size
;;              (mv-nth
;;               0
;;               (find-dir-ent
;;                (make-dir-ent-list (mv-nth 0
;;                                           (dir-ent-clusterchain-contents
;;                                            fat32-in-memory root-dir-ent)))
;;                (car pathname))))
;;             (cluster-size fat32-in-memory)))
;;           (make-list-ac
;;            (len
;;             (mv-nth
;;              0
;;              (fat32-build-index-list
;;               (effective-fat fat32-in-memory)
;;               (dir-ent-first-cluster
;;                (mv-nth 0
;;                        (find-dir-ent
;;                         (make-dir-ent-list
;;                          (mv-nth 0
;;                                  (dir-ent-clusterchain-contents
;;                                   fat32-in-memory root-dir-ent)))
;;                         (car pathname))))
;;               (dir-ent-file-size
;;                (mv-nth 0
;;                        (find-dir-ent
;;                         (make-dir-ent-list
;;                          (mv-nth 0
;;                                  (dir-ent-clusterchain-contents
;;                                   fat32-in-memory root-dir-ent)))
;;                         (car pathname))))
;;               (cluster-size fat32-in-memory))))
;;            0 nil))
;;          1)))
;;       (fa-table
;;        (set-indices-in-fa-table
;;         (effective-fat fat32-in-memory)
;;         (mv-nth
;;          0
;;          (fat32-build-index-list
;;           (effective-fat fat32-in-memory)
;;           (dir-ent-first-cluster
;;            (mv-nth
;;             0
;;             (find-dir-ent
;;              (make-dir-ent-list
;;               (mv-nth
;;                0
;;                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;              (car pathname))))
;;           (dir-ent-file-size
;;            (mv-nth
;;             0
;;             (find-dir-ent
;;              (make-dir-ent-list
;;               (mv-nth
;;                0
;;                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;              (car pathname))))
;;           (cluster-size fat32-in-memory)))
;;         (make-list-ac
;;          (len
;;           (mv-nth
;;            0
;;            (fat32-build-index-list
;;             (effective-fat fat32-in-memory)
;;             (dir-ent-first-cluster
;;              (mv-nth
;;               0
;;               (find-dir-ent
;;                (make-dir-ent-list (mv-nth 0
;;                                           (dir-ent-clusterchain-contents
;;                                            fat32-in-memory root-dir-ent)))
;;                (car pathname))))
;;             (dir-ent-file-size
;;              (mv-nth
;;               0
;;               (find-dir-ent
;;                (make-dir-ent-list (mv-nth 0
;;                                           (dir-ent-clusterchain-contents
;;                                            fat32-in-memory root-dir-ent)))
;;                (car pathname))))
;;             (cluster-size fat32-in-memory))))
;;          0 nil))))))))

;; (defthm
;;   dir-ent-clusterchain-contents-of-lofat-place-file-coincident-lemma-27
;;   (implies
;;    (and
;;     (equal
;;      (+
;;       1
;;       (count-free-clusters (effective-fat fat32-in-memory))
;;       (len
;;        (mv-nth
;;         0
;;         (dir-ent-clusterchain
;;          fat32-in-memory
;;          (mv-nth
;;           0
;;           (find-dir-ent
;;            (make-dir-ent-list
;;             (mv-nth
;;              0
;;              (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;            (car pathname)))))))
;;      (len (make-clusters (lofat-file->contents file)
;;                          (cluster-size fat32-in-memory))))
;;     (lofat-fs-p fat32-in-memory)
;;     (equal
;;      (mv-nth
;;       3
;;       (lofat-to-hifat-helper
;;        fat32-in-memory
;;        (make-dir-ent-list
;;         (mv-nth 0
;;                 (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;        entry-limit))
;;      0)
;;     (<=
;;      (+
;;       (len (make-clusters (lofat-file->contents file)
;;                           (cluster-size fat32-in-memory)))
;;       (hifat-cluster-count
;;        (mv-nth
;;         0
;;         (lofat-to-hifat-helper
;;          fat32-in-memory
;;          (make-dir-ent-list
;;           (mv-nth
;;            0
;;            (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;          entry-limit))
;;        (cluster-size fat32-in-memory))
;;       (-
;;        (hifat-cluster-count
;;         (mv-nth
;;          0
;;          (lofat-to-hifat-helper
;;           fat32-in-memory
;;           (make-dir-ent-list
;;            (mv-nth
;;             0
;;             (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;           entry-limit))
;;         (cluster-size fat32-in-memory)))
;;       (-
;;        (len
;;         (make-clusters
;;          (mv-nth
;;           0
;;           (dir-ent-clusterchain-contents
;;            fat32-in-memory
;;            (mv-nth
;;             0
;;             (find-dir-ent
;;              (make-dir-ent-list
;;               (mv-nth
;;                0
;;                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;              (car pathname)))))
;;          (cluster-size fat32-in-memory)))))
;;      (count-free-clusters (effective-fat fat32-in-memory)))
;;     (<=
;;      2
;;      (dir-ent-first-cluster
;;       (mv-nth
;;        0
;;        (find-dir-ent
;;         (make-dir-ent-list
;;          (mv-nth
;;           0
;;           (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;         (car pathname)))))
;;     (<
;;      (dir-ent-first-cluster
;;       (mv-nth
;;        0
;;        (find-dir-ent
;;         (make-dir-ent-list
;;          (mv-nth
;;           0
;;           (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;         (car pathname))))
;;      (+ 2 (count-of-clusters fat32-in-memory))))
;;    (not-intersectp-list
;;     x
;;     (mv-nth
;;      2
;;      (lofat-to-hifat-helper
;;       (mv-nth
;;        0
;;        (update-dir-contents
;;         (mv-nth
;;          0
;;          (place-contents
;;           (update-fati
;;            (nth
;;             0
;;             (find-n-free-clusters
;;              (set-indices-in-fa-table
;;               (effective-fat fat32-in-memory)
;;               (mv-nth
;;                0
;;                (fat32-build-index-list
;;                 (effective-fat fat32-in-memory)
;;                 (dir-ent-first-cluster
;;                  (mv-nth
;;                   0
;;                   (find-dir-ent
;;                    (make-dir-ent-list
;;                     (mv-nth 0
;;                             (dir-ent-clusterchain-contents
;;                              fat32-in-memory root-dir-ent)))
;;                    (car pathname))))
;;                 (dir-ent-file-size
;;                  (mv-nth
;;                   0
;;                   (find-dir-ent
;;                    (make-dir-ent-list
;;                     (mv-nth 0
;;                             (dir-ent-clusterchain-contents
;;                              fat32-in-memory root-dir-ent)))
;;                    (car pathname))))
;;                 (cluster-size fat32-in-memory)))
;;               (make-list-ac
;;                (len
;;                 (mv-nth
;;                  0
;;                  (fat32-build-index-list
;;                   (effective-fat fat32-in-memory)
;;                   (dir-ent-first-cluster
;;                    (mv-nth
;;                     0
;;                     (find-dir-ent
;;                      (make-dir-ent-list
;;                       (mv-nth 0
;;                               (dir-ent-clusterchain-contents
;;                                fat32-in-memory root-dir-ent)))
;;                      (car pathname))))
;;                   (dir-ent-file-size
;;                    (mv-nth
;;                     0
;;                     (find-dir-ent
;;                      (make-dir-ent-list
;;                       (mv-nth 0
;;                               (dir-ent-clusterchain-contents
;;                                fat32-in-memory root-dir-ent)))
;;                      (car pathname))))
;;                   (cluster-size fat32-in-memory))))
;;                0 nil))
;;              1))
;;            (fat32-update-lower-28
;;             (fati
;;              (nth
;;               0
;;               (find-n-free-clusters
;;                (set-indices-in-fa-table
;;                 (effective-fat fat32-in-memory)
;;                 (mv-nth
;;                  0
;;                  (fat32-build-index-list
;;                   (effective-fat fat32-in-memory)
;;                   (dir-ent-first-cluster
;;                    (mv-nth
;;                     0
;;                     (find-dir-ent
;;                      (make-dir-ent-list
;;                       (mv-nth 0
;;                               (dir-ent-clusterchain-contents
;;                                fat32-in-memory root-dir-ent)))
;;                      (car pathname))))
;;                   (dir-ent-file-size
;;                    (mv-nth
;;                     0
;;                     (find-dir-ent
;;                      (make-dir-ent-list
;;                       (mv-nth 0
;;                               (dir-ent-clusterchain-contents
;;                                fat32-in-memory root-dir-ent)))
;;                      (car pathname))))
;;                   (cluster-size fat32-in-memory)))
;;                 (make-list-ac
;;                  (len
;;                   (mv-nth
;;                    0
;;                    (fat32-build-index-list
;;                     (effective-fat fat32-in-memory)
;;                     (dir-ent-first-cluster
;;                      (mv-nth
;;                       0
;;                       (find-dir-ent
;;                        (make-dir-ent-list
;;                         (mv-nth 0
;;                                 (dir-ent-clusterchain-contents
;;                                  fat32-in-memory root-dir-ent)))
;;                        (car pathname))))
;;                     (dir-ent-file-size
;;                      (mv-nth
;;                       0
;;                       (find-dir-ent
;;                        (make-dir-ent-list
;;                         (mv-nth 0
;;                                 (dir-ent-clusterchain-contents
;;                                  fat32-in-memory root-dir-ent)))
;;                        (car pathname))))
;;                     (cluster-size fat32-in-memory))))
;;                  0 nil))
;;                1))
;;              fat32-in-memory)
;;             268435455)
;;            (mv-nth
;;             0
;;             (clear-clusterchain
;;              fat32-in-memory
;;              (dir-ent-first-cluster
;;               (mv-nth
;;                0
;;                (find-dir-ent (make-dir-ent-list
;;                               (mv-nth 0
;;                                       (dir-ent-clusterchain-contents
;;                                        fat32-in-memory root-dir-ent)))
;;                              (car pathname))))
;;              (dir-ent-file-size
;;               (mv-nth
;;                0
;;                (find-dir-ent (make-dir-ent-list
;;                               (mv-nth 0
;;                                       (dir-ent-clusterchain-contents
;;                                        fat32-in-memory root-dir-ent)))
;;                              (car pathname)))))))
;;           (mv-nth
;;            0
;;            (find-dir-ent
;;             (make-dir-ent-list
;;              (mv-nth
;;               0
;;               (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;             (car pathname)))
;;           (lofat-file->contents file)
;;           (len (explode (lofat-file->contents file)))
;;           (nth
;;            0
;;            (find-n-free-clusters
;;             (set-indices-in-fa-table
;;              (effective-fat fat32-in-memory)
;;              (mv-nth
;;               0
;;               (fat32-build-index-list
;;                (effective-fat fat32-in-memory)
;;                (dir-ent-first-cluster
;;                 (mv-nth 0
;;                         (find-dir-ent
;;                          (make-dir-ent-list
;;                           (mv-nth 0
;;                                   (dir-ent-clusterchain-contents
;;                                    fat32-in-memory root-dir-ent)))
;;                          (car pathname))))
;;                (dir-ent-file-size
;;                 (mv-nth 0
;;                         (find-dir-ent
;;                          (make-dir-ent-list
;;                           (mv-nth 0
;;                                   (dir-ent-clusterchain-contents
;;                                    fat32-in-memory root-dir-ent)))
;;                          (car pathname))))
;;                (cluster-size fat32-in-memory)))
;;              (make-list-ac
;;               (len
;;                (mv-nth
;;                 0
;;                 (fat32-build-index-list
;;                  (effective-fat fat32-in-memory)
;;                  (dir-ent-first-cluster
;;                   (mv-nth
;;                    0
;;                    (find-dir-ent
;;                     (make-dir-ent-list
;;                      (mv-nth 0
;;                              (dir-ent-clusterchain-contents
;;                               fat32-in-memory root-dir-ent)))
;;                     (car pathname))))
;;                  (dir-ent-file-size
;;                   (mv-nth
;;                    0
;;                    (find-dir-ent
;;                     (make-dir-ent-list
;;                      (mv-nth 0
;;                              (dir-ent-clusterchain-contents
;;                               fat32-in-memory root-dir-ent)))
;;                     (car pathname))))
;;                  (cluster-size fat32-in-memory))))
;;               0 nil))
;;             1))))
;;         (dir-ent-first-cluster root-dir-ent)
;;         (nats=>string
;;          (insert-dir-ent
;;           (string=>nats
;;            (mv-nth
;;             0
;;             (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;           (dir-ent-set-first-cluster-file-size
;;            (mv-nth
;;             0
;;             (find-dir-ent
;;              (make-dir-ent-list
;;               (mv-nth
;;                0
;;                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;              (car pathname)))
;;            (nth
;;             0
;;             (find-n-free-clusters
;;              (set-indices-in-fa-table
;;               (effective-fat fat32-in-memory)
;;               (mv-nth
;;                0
;;                (fat32-build-index-list
;;                 (effective-fat fat32-in-memory)
;;                 (dir-ent-first-cluster
;;                  (mv-nth
;;                   0
;;                   (find-dir-ent
;;                    (make-dir-ent-list
;;                     (mv-nth 0
;;                             (dir-ent-clusterchain-contents
;;                              fat32-in-memory root-dir-ent)))
;;                    (car pathname))))
;;                 (dir-ent-file-size
;;                  (mv-nth
;;                   0
;;                   (find-dir-ent
;;                    (make-dir-ent-list
;;                     (mv-nth 0
;;                             (dir-ent-clusterchain-contents
;;                              fat32-in-memory root-dir-ent)))
;;                    (car pathname))))
;;                 (cluster-size fat32-in-memory)))
;;               (make-list-ac
;;                (len
;;                 (mv-nth
;;                  0
;;                  (fat32-build-index-list
;;                   (effective-fat fat32-in-memory)
;;                   (dir-ent-first-cluster
;;                    (mv-nth
;;                     0
;;                     (find-dir-ent
;;                      (make-dir-ent-list
;;                       (mv-nth 0
;;                               (dir-ent-clusterchain-contents
;;                                fat32-in-memory root-dir-ent)))
;;                      (car pathname))))
;;                   (dir-ent-file-size
;;                    (mv-nth
;;                     0
;;                     (find-dir-ent
;;                      (make-dir-ent-list
;;                       (mv-nth 0
;;                               (dir-ent-clusterchain-contents
;;                                fat32-in-memory root-dir-ent)))
;;                      (car pathname))))
;;                   (cluster-size fat32-in-memory))))
;;                0 nil))
;;              1))
;;            (len (explode (lofat-file->contents file))))))))
;;       (make-dir-ent-list
;;        (mv-nth
;;         0
;;         (dir-ent-clusterchain-contents
;;          (mv-nth
;;           0
;;           (update-dir-contents
;;            (mv-nth
;;             0
;;             (place-contents
;;              (update-fati
;;               (nth
;;                0
;;                (find-n-free-clusters
;;                 (set-indices-in-fa-table
;;                  (effective-fat fat32-in-memory)
;;                  (mv-nth
;;                   0
;;                   (fat32-build-index-list
;;                    (effective-fat fat32-in-memory)
;;                    (dir-ent-first-cluster
;;                     (mv-nth
;;                      0
;;                      (find-dir-ent
;;                       (make-dir-ent-list
;;                        (mv-nth 0
;;                                (dir-ent-clusterchain-contents
;;                                 fat32-in-memory root-dir-ent)))
;;                       (car pathname))))
;;                    (dir-ent-file-size
;;                     (mv-nth
;;                      0
;;                      (find-dir-ent
;;                       (make-dir-ent-list
;;                        (mv-nth 0
;;                                (dir-ent-clusterchain-contents
;;                                 fat32-in-memory root-dir-ent)))
;;                       (car pathname))))
;;                    (cluster-size fat32-in-memory)))
;;                  (make-list-ac
;;                   (len
;;                    (mv-nth
;;                     0
;;                     (fat32-build-index-list
;;                      (effective-fat fat32-in-memory)
;;                      (dir-ent-first-cluster
;;                       (mv-nth
;;                        0
;;                        (find-dir-ent
;;                         (make-dir-ent-list
;;                          (mv-nth 0
;;                                  (dir-ent-clusterchain-contents
;;                                   fat32-in-memory root-dir-ent)))
;;                         (car pathname))))
;;                      (dir-ent-file-size
;;                       (mv-nth
;;                        0
;;                        (find-dir-ent
;;                         (make-dir-ent-list
;;                          (mv-nth 0
;;                                  (dir-ent-clusterchain-contents
;;                                   fat32-in-memory root-dir-ent)))
;;                         (car pathname))))
;;                      (cluster-size fat32-in-memory))))
;;                   0 nil))
;;                 1))
;;               (fat32-update-lower-28
;;                (fati
;;                 (nth
;;                  0
;;                  (find-n-free-clusters
;;                   (set-indices-in-fa-table
;;                    (effective-fat fat32-in-memory)
;;                    (mv-nth
;;                     0
;;                     (fat32-build-index-list
;;                      (effective-fat fat32-in-memory)
;;                      (dir-ent-first-cluster
;;                       (mv-nth
;;                        0
;;                        (find-dir-ent
;;                         (make-dir-ent-list
;;                          (mv-nth 0
;;                                  (dir-ent-clusterchain-contents
;;                                   fat32-in-memory root-dir-ent)))
;;                         (car pathname))))
;;                      (dir-ent-file-size
;;                       (mv-nth
;;                        0
;;                        (find-dir-ent
;;                         (make-dir-ent-list
;;                          (mv-nth 0
;;                                  (dir-ent-clusterchain-contents
;;                                   fat32-in-memory root-dir-ent)))
;;                         (car pathname))))
;;                      (cluster-size fat32-in-memory)))
;;                    (make-list-ac
;;                     (len
;;                      (mv-nth
;;                       0
;;                       (fat32-build-index-list
;;                        (effective-fat fat32-in-memory)
;;                        (dir-ent-first-cluster
;;                         (mv-nth
;;                          0
;;                          (find-dir-ent
;;                           (make-dir-ent-list
;;                            (mv-nth 0
;;                                    (dir-ent-clusterchain-contents
;;                                     fat32-in-memory root-dir-ent)))
;;                           (car pathname))))
;;                        (dir-ent-file-size
;;                         (mv-nth
;;                          0
;;                          (find-dir-ent
;;                           (make-dir-ent-list
;;                            (mv-nth 0
;;                                    (dir-ent-clusterchain-contents
;;                                     fat32-in-memory root-dir-ent)))
;;                           (car pathname))))
;;                        (cluster-size fat32-in-memory))))
;;                     0 nil))
;;                   1))
;;                 fat32-in-memory)
;;                268435455)
;;               (mv-nth
;;                0
;;                (clear-clusterchain
;;                 fat32-in-memory
;;                 (dir-ent-first-cluster
;;                  (mv-nth
;;                   0
;;                   (find-dir-ent
;;                    (make-dir-ent-list
;;                     (mv-nth 0
;;                             (dir-ent-clusterchain-contents
;;                              fat32-in-memory root-dir-ent)))
;;                    (car pathname))))
;;                 (dir-ent-file-size
;;                  (mv-nth
;;                   0
;;                   (find-dir-ent
;;                    (make-dir-ent-list
;;                     (mv-nth 0
;;                             (dir-ent-clusterchain-contents
;;                              fat32-in-memory root-dir-ent)))
;;                    (car pathname)))))))
;;              (mv-nth
;;               0
;;               (find-dir-ent
;;                (make-dir-ent-list (mv-nth 0
;;                                           (dir-ent-clusterchain-contents
;;                                            fat32-in-memory root-dir-ent)))
;;                (car pathname)))
;;              (lofat-file->contents file)
;;              (len (explode (lofat-file->contents file)))
;;              (nth
;;               0
;;               (find-n-free-clusters
;;                (set-indices-in-fa-table
;;                 (effective-fat fat32-in-memory)
;;                 (mv-nth
;;                  0
;;                  (fat32-build-index-list
;;                   (effective-fat fat32-in-memory)
;;                   (dir-ent-first-cluster
;;                    (mv-nth
;;                     0
;;                     (find-dir-ent
;;                      (make-dir-ent-list
;;                       (mv-nth 0
;;                               (dir-ent-clusterchain-contents
;;                                fat32-in-memory root-dir-ent)))
;;                      (car pathname))))
;;                   (dir-ent-file-size
;;                    (mv-nth
;;                     0
;;                     (find-dir-ent
;;                      (make-dir-ent-list
;;                       (mv-nth 0
;;                               (dir-ent-clusterchain-contents
;;                                fat32-in-memory root-dir-ent)))
;;                      (car pathname))))
;;                   (cluster-size fat32-in-memory)))
;;                 (make-list-ac
;;                  (len
;;                   (mv-nth
;;                    0
;;                    (fat32-build-index-list
;;                     (effective-fat fat32-in-memory)
;;                     (dir-ent-first-cluster
;;                      (mv-nth
;;                       0
;;                       (find-dir-ent
;;                        (make-dir-ent-list
;;                         (mv-nth 0
;;                                 (dir-ent-clusterchain-contents
;;                                  fat32-in-memory root-dir-ent)))
;;                        (car pathname))))
;;                     (dir-ent-file-size
;;                      (mv-nth
;;                       0
;;                       (find-dir-ent
;;                        (make-dir-ent-list
;;                         (mv-nth 0
;;                                 (dir-ent-clusterchain-contents
;;                                  fat32-in-memory root-dir-ent)))
;;                        (car pathname))))
;;                     (cluster-size fat32-in-memory))))
;;                  0 nil))
;;                1))))
;;            (dir-ent-first-cluster root-dir-ent)
;;            (nats=>string
;;             (insert-dir-ent
;;              (string=>nats
;;               (mv-nth
;;                0
;;                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
;;              (dir-ent-set-first-cluster-file-size
;;               (mv-nth
;;                0
;;                (find-dir-ent (make-dir-ent-list
;;                               (mv-nth 0
;;                                       (dir-ent-clusterchain-contents
;;                                        fat32-in-memory root-dir-ent)))
;;                              (car pathname)))
;;               (nth
;;                0
;;                (find-n-free-clusters
;;                 (set-indices-in-fa-table
;;                  (effective-fat fat32-in-memory)
;;                  (mv-nth
;;                   0
;;                   (fat32-build-index-list
;;                    (effective-fat fat32-in-memory)
;;                    (dir-ent-first-cluster
;;                     (mv-nth
;;                      0
;;                      (find-dir-ent
;;                       (make-dir-ent-list
;;                        (mv-nth 0
;;                                (dir-ent-clusterchain-contents
;;                                 fat32-in-memory root-dir-ent)))
;;                       (car pathname))))
;;                    (dir-ent-file-size
;;                     (mv-nth
;;                      0
;;                      (find-dir-ent
;;                       (make-dir-ent-list
;;                        (mv-nth 0
;;                                (dir-ent-clusterchain-contents
;;                                 fat32-in-memory root-dir-ent)))
;;                       (car pathname))))
;;                    (cluster-size fat32-in-memory)))
;;                  (make-list-ac
;;                   (len
;;                    (mv-nth
;;                     0
;;                     (fat32-build-index-list
;;                      (effective-fat fat32-in-memory)
;;                      (dir-ent-first-cluster
;;                       (mv-nth
;;                        0
;;                        (find-dir-ent
;;                         (make-dir-ent-list
;;                          (mv-nth 0
;;                                  (dir-ent-clusterchain-contents
;;                                   fat32-in-memory root-dir-ent)))
;;                         (car pathname))))
;;                      (dir-ent-file-size
;;                       (mv-nth
;;                        0
;;                        (find-dir-ent
;;                         (make-dir-ent-list
;;                          (mv-nth 0
;;                                  (dir-ent-clusterchain-contents
;;                                   fat32-in-memory root-dir-ent)))
;;                         (car pathname))))
;;                      (cluster-size fat32-in-memory))))
;;                   0 nil))
;;                 1))
;;               (len (explode (lofat-file->contents file))))))))
;;          root-dir-ent)))
;;       entry-limit))))
;;   :hints (("goal" :in-theory (enable len-of-make-clusters))))

(defthm
  lofat-place-file-correctness-1-lemma-19
  (implies
   (and
    (<= (+ -1
           (len (make-clusters (lofat-file->contents file)
                               (cluster-size fat32-in-memory))))
        (+ -1
           (count-free-clusters (effective-fat fat32-in-memory))))
    (lofat-fs-p fat32-in-memory)
    (equal
     (mv-nth 1
             (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent))
     0))
   (not
    (<
     (+ (count-free-clusters (effective-fat fat32-in-memory))
        (len (mv-nth 0
                     (dir-ent-clusterchain fat32-in-memory root-dir-ent)))
        (- (len (make-clusters (lofat-file->contents file)
                               (cluster-size fat32-in-memory)))))
     (len
      (make-clusters
       (mv-nth 0
               (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent))
       (cluster-size fat32-in-memory))))))
  :hints (("goal" :in-theory (enable len-of-make-clusters))))

;; Introduce a rewrite rule gingerly...
(defthm
  lofat-place-file-correctness-1-lemma-20
  (implies (lofat-regular-file-p file)
           (iff (equal (len (explode (lofat-file->contents file)))
                       0)
                (equal (lofat-file->contents file) "")))
  :hints (("goal" :expand (len (explode (lofat-file->contents file))))))

(defthm
  lofat-place-file-correctness-1-lemma-21
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit))
     0)
    (equal
     (mv-nth 1
             (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent))
     0)
    (<=
     (+
      (len (make-clusters (lofat-file->contents file)
                          (cluster-size fat32-in-memory)))
      (hifat-cluster-count
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32-in-memory
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
         entry-limit))
       (cluster-size fat32-in-memory))
      (-
       (hifat-cluster-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
          entry-limit))
        (cluster-size fat32-in-memory)))
      (-
       (len
        (make-clusters
         (mv-nth
          0
          (dir-ent-clusterchain-contents
           fat32-in-memory
           (mv-nth
            0
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth
               0
               (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
             (car pathname)))))
         (cluster-size fat32-in-memory)))))
     (count-free-clusters (effective-fat fat32-in-memory)))
    (<=
     2
     (dir-ent-first-cluster
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
        (car pathname)))))
    (<
     (dir-ent-first-cluster
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
        (car pathname))))
     (+ 2 (count-of-clusters fat32-in-memory))))
   (not
    (<
     (+
      (count-free-clusters (effective-fat fat32-in-memory))
      (len (mv-nth 0
                   (dir-ent-clusterchain fat32-in-memory root-dir-ent)))
      (- (len (make-clusters (lofat-file->contents file)
                             (cluster-size fat32-in-memory))))
      (len
       (mv-nth
        0
        (dir-ent-clusterchain
         fat32-in-memory
         (mv-nth
          0
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth
             0
             (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
           (car pathname)))))))
     (len
      (make-clusters
       (mv-nth 0
               (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent))
       (cluster-size fat32-in-memory))))))
  :hints (("goal" :in-theory (enable len-of-make-clusters))))

(defthm
  lofat-place-file-correctness-1-lemma-22
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
       entry-limit))
     0)
    (equal
     (mv-nth 1
             (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent))
     0)
    (<=
     (+
      (len (make-clusters (lofat-file->contents file)
                          (cluster-size fat32-in-memory)))
      (hifat-cluster-count
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32-in-memory
         (make-dir-ent-list
          (mv-nth
           0
           (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
         entry-limit))
       (cluster-size fat32-in-memory))
      (-
       (hifat-cluster-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32-in-memory
          (make-dir-ent-list
           (mv-nth
            0
            (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
          entry-limit))
        (cluster-size fat32-in-memory)))
      (-
       (len
        (make-clusters
         (mv-nth
          0
          (dir-ent-clusterchain-contents
           fat32-in-memory
           (mv-nth
            0
            (find-dir-ent
             (make-dir-ent-list
              (mv-nth
               0
               (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
             (car pathname)))))
         (cluster-size fat32-in-memory)))))
     (count-free-clusters (effective-fat fat32-in-memory)))
    (<=
     2
     (dir-ent-first-cluster
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
        (car pathname)))))
    (<
     (dir-ent-first-cluster
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth
          0
          (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
        (car pathname))))
     (+ 2 (count-of-clusters fat32-in-memory))))
   (not
    (<
     (+
      1
      (count-free-clusters (effective-fat fat32-in-memory))
      (len (mv-nth 0
                   (dir-ent-clusterchain fat32-in-memory root-dir-ent)))
      (- (len (make-clusters (lofat-file->contents file)
                             (cluster-size fat32-in-memory))))
      (len
       (mv-nth
        0
        (dir-ent-clusterchain
         fat32-in-memory
         (mv-nth
          0
          (find-dir-ent
           (make-dir-ent-list
            (mv-nth
             0
             (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent)))
           (car pathname)))))))
     (len
      (make-clusters
       (mv-nth 0
               (dir-ent-clusterchain-contents fat32-in-memory root-dir-ent))
       (cluster-size fat32-in-memory))))))
  :hints (("goal" :in-theory (enable len-of-make-clusters))))

(defthm
  lofat-place-file-correctness-1-lemma-24
  (equal
   (<
    (binary-+
     (count-free-clusters (effective-fat fat32-in-memory))
     (len (mv-nth '0
                  (dir-ent-clusterchain fat32-in-memory dir-ent))))
    '1)
   (and
    (equal (mv-nth '0
                   (dir-ent-clusterchain fat32-in-memory dir-ent))
           nil)
    (equal (count-free-clusters (effective-fat fat32-in-memory))
           0)))
  :hints
  (("goal"
    :expand
    (len (mv-nth '0
                 (dir-ent-clusterchain fat32-in-memory dir-ent)))
    :in-theory (disable (:rewrite true-listp-of-dir-ent-clusterchain))
    :use (:rewrite true-listp-of-dir-ent-clusterchain))))

;; I don't like this...
(defthm
  lofat-place-file-correctness-1-lemma-25
  (implies (equal (mv-nth 1
                          (dir-ent-clusterchain fat32-in-memory dir-ent))
                  0)
           (mv-nth 0
                   (dir-ent-clusterchain fat32-in-memory dir-ent)))
  :hints
  (("goal"
    :in-theory (enable dir-ent-clusterchain
                       fat32-build-index-list)
    :expand ((fat32-build-index-list (effective-fat fat32-in-memory)
                                     (dir-ent-first-cluster dir-ent)
                                     (dir-ent-file-size dir-ent)
                                     (cluster-size fat32-in-memory))
             (fat32-build-index-list (effective-fat fat32-in-memory)
                                     (dir-ent-first-cluster dir-ent)
                                     2097152
                                     (cluster-size fat32-in-memory))))))

(defthm
  lofat-place-file-correctness-1-lemma-26
  (implies
   (lofat-fs-p fat32-in-memory)
   (fat32-entry-p
    (fat32-update-lower-28
     (fati
      (nth
       '0
       (find-n-free-clusters
        (set-indices-in-fa-table
         (effective-fat fat32-in-memory)
         (mv-nth '0
                 (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
         (make-list-ac
          (len
           (mv-nth '0
                   (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
          '0
          'nil))
        '1))
      fat32-in-memory)
     '268435455)))
  :hints
  (("goal"
    :in-theory (disable (:rewrite fat32-update-lower-28-correctness-1
                                  . 1))
    :use
    ((:instance
      (:rewrite fat32-update-lower-28-correctness-1 . 1)
      (masked-entry 268435455)
      (entry
       (fati
        (nth
         0
         (find-n-free-clusters
          (set-indices-in-fa-table
           (effective-fat fat32-in-memory)
           (mv-nth 0
                   (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
           (make-list-ac
            (len
             (mv-nth
              0
              (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
            0 nil))
          1))
        fat32-in-memory)))))))

;; I don't see why this subgoal hint was necessary.
(defthm
  lofat-place-file-correctness-1-lemma-27
  (implies
   (and
    (consp dir-ent-list)
    (lofat-fs-p fat32-in-memory)
    (useful-dir-ent-list-p dir-ent-list)
    (equal
     (mv-nth
      1
      (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list)))
     0)
    (no-duplicatesp-equal
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))))
   (equal
    (mv-nth
     2
     (place-contents
      (update-fati
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32-in-memory)
          (mv-nth 0
                  (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
          (make-list-ac
           (len
            (mv-nth
             0
             (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
           0 nil))
         1))
       (fat32-update-lower-28
        (fati
         (nth
          0
          (find-n-free-clusters
           (set-indices-in-fa-table
            (effective-fat fat32-in-memory)
            (mv-nth 0
                    (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
            (make-list-ac
             (len
              (mv-nth
               0
               (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
             0 nil))
           1))
         fat32-in-memory)
        268435455)
       (mv-nth 0
               (clear-clusterchain fat32-in-memory
                                   (dir-ent-first-cluster (car dir-ent-list))
                                   (dir-ent-file-size (car dir-ent-list)))))
      (car dir-ent-list)
      (lofat-file->contents file)
      (len (explode (lofat-file->contents file)))
      (nth
       0
       (find-n-free-clusters
        (set-indices-in-fa-table
         (effective-fat fat32-in-memory)
         (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
         (make-list-ac
          (len
           (mv-nth 0
                   (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
          0 nil))
        1))))
    (if
     (equal
      (+
       1
       (len
        (stobj-find-n-free-clusters
         (update-fati
          (nth
           0
           (find-n-free-clusters
            (set-indices-in-fa-table
             (effective-fat fat32-in-memory)
             (mv-nth
              0
              (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
             (make-list-ac
              (len
               (mv-nth
                0
                (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
              0 nil))
            1))
          (fat32-update-lower-28
           (fati
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32-in-memory)
               (mv-nth
                0
                (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
               (make-list-ac
                (len
                 (mv-nth
                  0
                  (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
                0 nil))
              1))
            fat32-in-memory)
           268435455)
          (mv-nth
           0
           (clear-clusterchain fat32-in-memory
                               (dir-ent-first-cluster (car dir-ent-list))
                               (dir-ent-file-size (car dir-ent-list)))))
         (+
          -1
          (len
           (make-clusters
            (lofat-file->contents file)
            (cluster-size
             (update-fati
              (nth
               0
               (find-n-free-clusters
                (set-indices-in-fa-table
                 (effective-fat fat32-in-memory)
                 (mv-nth
                  0
                  (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
                 (make-list-ac
                  (len (mv-nth 0
                               (dir-ent-clusterchain
                                fat32-in-memory (car dir-ent-list))))
                  0 nil))
                1))
              (fat32-update-lower-28
               (fati
                (nth
                 0
                 (find-n-free-clusters
                  (set-indices-in-fa-table
                   (effective-fat fat32-in-memory)
                   (mv-nth
                    0
                    (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
                   (make-list-ac
                    (len (mv-nth 0
                                 (dir-ent-clusterchain
                                  fat32-in-memory (car dir-ent-list))))
                    0 nil))
                  1))
                fat32-in-memory)
               268435455)
              (mv-nth 0
                      (clear-clusterchain
                       fat32-in-memory
                       (dir-ent-first-cluster (car dir-ent-list))
                       (dir-ent-file-size (car dir-ent-list))))))))))))
      (len
       (make-clusters
        (lofat-file->contents file)
        (cluster-size
         (update-fati
          (nth
           0
           (find-n-free-clusters
            (set-indices-in-fa-table
             (effective-fat fat32-in-memory)
             (mv-nth
              0
              (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
             (make-list-ac
              (len
               (mv-nth
                0
                (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
              0 nil))
            1))
          (fat32-update-lower-28
           (fati
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32-in-memory)
               (mv-nth
                0
                (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
               (make-list-ac
                (len
                 (mv-nth
                  0
                  (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
                0 nil))
              1))
            fat32-in-memory)
           268435455)
          (mv-nth
           0
           (clear-clusterchain fat32-in-memory
                               (dir-ent-first-cluster (car dir-ent-list))
                               (dir-ent-file-size (car dir-ent-list)))))))))
     0 *enospc*)))
  :hints
  (("goal"
    :in-theory (disable (:rewrite place-contents-expansion-2))
    :use
    (:instance
     (:rewrite place-contents-expansion-2)
     (first-cluster
      (nth
       0
       (find-n-free-clusters
        (set-indices-in-fa-table
         (effective-fat fat32-in-memory)
         (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
         (make-list-ac
          (len
           (mv-nth 0
                   (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
          0 nil))
        1)))
     (file-length (len (explode (lofat-file->contents file))))
     (contents (lofat-file->contents file))
     (dir-ent (car dir-ent-list))
     (fat32-in-memory
      (update-fati
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32-in-memory)
          (mv-nth 0
                  (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
          (make-list-ac
           (len
            (mv-nth
             0
             (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
           0 nil))
         1))
       (fat32-update-lower-28
        (fati
         (nth
          0
          (find-n-free-clusters
           (set-indices-in-fa-table
            (effective-fat fat32-in-memory)
            (mv-nth 0
                    (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
            (make-list-ac
             (len
              (mv-nth
               0
               (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
             0 nil))
           1))
         fat32-in-memory)
        268435455)
       (mv-nth
        0
        (clear-clusterchain fat32-in-memory
                            (dir-ent-first-cluster (car dir-ent-list))
                            (dir-ent-file-size (car dir-ent-list))))))))))

;; I don't see why this subgoal hint was necessary.
(defthm
  lofat-place-file-correctness-1-lemma-28
  (implies
   (and
    (consp dir-ent-list)
    (lofat-fs-p fat32-in-memory)
    (useful-dir-ent-list-p dir-ent-list)
    (equal
     (mv-nth
      1
      (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list)))
     0)
    (no-duplicatesp-equal
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))))
   (equal
    (dir-ent-first-cluster
     (dir-ent-set-first-cluster-file-size
      (car dir-ent-list)
      (nth
       0
       (find-n-free-clusters
        (set-indices-in-fa-table
         (effective-fat fat32-in-memory)
         (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
         (make-list-ac
          (len
           (mv-nth 0
                   (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
          0 nil))
        1))
      (len (explode (lofat-file->contents file)))))
    (nth
     0
     (find-n-free-clusters
      (set-indices-in-fa-table
       (effective-fat fat32-in-memory)
       (mv-nth 0
               (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
       (make-list-ac
        (len
         (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
        0 nil))
      1))))
  :hints
  (("goal"
    :in-theory
    (disable
     (:rewrite dir-ent-first-cluster-of-dir-ent-set-first-cluster-file-size))
    :use
    (:instance
     (:rewrite dir-ent-first-cluster-of-dir-ent-set-first-cluster-file-size)
     (file-size (len (explode (lofat-file->contents file))))
     (first-cluster
      (nth
       0
       (find-n-free-clusters
        (set-indices-in-fa-table
         (effective-fat fat32-in-memory)
         (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
         (make-list-ac
          (len
           (mv-nth 0
                   (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
          0 nil))
        1)))
     (dir-ent (car dir-ent-list))))))

(defthm
  lofat-place-file-correctness-1-lemma-29
  (implies
   (and
    (equal
     (mv-nth
      1
      (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list)))
     0)
    (no-duplicatesp-equal
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
    (<
     (nth
      0
      (find-n-free-clusters
       (set-indices-in-fa-table
        (effective-fat fat32-in-memory)
        (mv-nth 0
                (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
        (make-list-ac
         (len
          (mv-nth 0
                  (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
         0 nil))
       1))
     (+ 2 (count-of-clusters fat32-in-memory))))
   (not
    (<
     (binary-+ '2
               (count-of-clusters fat32-in-memory))
     (binary-+
      '1
      (nth
       '0
       (find-n-free-clusters
        (set-indices-in-fa-table
         (effective-fat fat32-in-memory)
         (mv-nth '0
                 (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
         (make-list-ac
          (len
           (mv-nth '0
                   (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
          '0
          'nil))
        '1))))))
  :hints
  (("goal"
    :use
    ((:instance
      (:rewrite painful-debugging-lemma-13)
      (x
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32-in-memory)
          (mv-nth 0
                  (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
          (make-list-ac
           (len
            (mv-nth
             0
             (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
           0 nil))
         1)))
      (y (+ 2
            (count-of-clusters fat32-in-memory))))))))

(defthm
  lofat-place-file-correctness-1-lemma-30
  (implies
   (and
    (equal
     (mv-nth
      1
      (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list)))
     0)
    (no-duplicatesp-equal
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))))
   (equal
    (count-free-clusters
     (update-nth
      (nth
       0
       (find-n-free-clusters
        (set-indices-in-fa-table
         (effective-fat fat32-in-memory)
         (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
         (make-list-ac
          (len
           (mv-nth 0
                   (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
          0 nil))
        1))
      (fat32-update-lower-28
       (fati
        (nth
         0
         (find-n-free-clusters
          (set-indices-in-fa-table
           (effective-fat fat32-in-memory)
           (mv-nth 0
                   (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
           (make-list-ac
            (len
             (mv-nth
              0
              (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
            0 nil))
          1))
        fat32-in-memory)
       268435455)
      (set-indices-in-fa-table
       (effective-fat fat32-in-memory)
       (mv-nth 0
               (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
       (make-list-ac
        (len
         (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
        0 nil))))
    (if
     (equal
      (fat32-entry-mask
       (nth
        (nth
         0
         (find-n-free-clusters
          (set-indices-in-fa-table
           (effective-fat fat32-in-memory)
           (mv-nth 0
                   (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
           (make-list-ac
            (len
             (mv-nth
              0
              (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
            0 nil))
          1))
        (set-indices-in-fa-table
         (effective-fat fat32-in-memory)
         (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
         (make-list-ac
          (len
           (mv-nth 0
                   (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
          0 nil))))
      0)
     (+
      -1
      (count-free-clusters
       (set-indices-in-fa-table
        (effective-fat fat32-in-memory)
        (mv-nth 0
                (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
        (make-list-ac
         (len
          (mv-nth 0
                  (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
         0 nil))))
     (count-free-clusters
      (set-indices-in-fa-table
       (effective-fat fat32-in-memory)
       (mv-nth 0
               (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
       (make-list-ac
        (len
         (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
        0 nil))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite lofat-place-file-correctness-1-lemma-25))
    :use (:instance (:rewrite lofat-place-file-correctness-1-lemma-25)
                    (dir-ent (car dir-ent-list))
                    (fat32-in-memory fat32-in-memory)))))

(defthm
  lofat-place-file-correctness-1-lemma-31
  (implies
   (and
    (consp dir-ent-list)
    (useful-dir-ent-list-p dir-ent-list)
    (equal
     (mv-nth
      1
      (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list)))
     0)
    (no-duplicatesp-equal
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
    (lofat-regular-file-p file))
   (equal
    (dir-ent-file-size
     (dir-ent-set-first-cluster-file-size
      (car dir-ent-list)
      (nth
       0
       (find-n-free-clusters
        (set-indices-in-fa-table
         (effective-fat fat32-in-memory)
         (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
         (make-list-ac
          (len
           (mv-nth 0
                   (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
          0 nil))
        1))
      (len (explode (lofat-file->contents file)))))
    (len (explode (lofat-file->contents file)))))
  :hints
  (("goal"
    :in-theory
    (disable
     (:rewrite dir-ent-file-size-of-dir-ent-set-first-cluster-file-size))
    :use
    (:instance
     (:rewrite dir-ent-file-size-of-dir-ent-set-first-cluster-file-size)
     (file-size (len (explode (lofat-file->contents file))))
     (first-cluster
      (nth
       0
       (find-n-free-clusters
        (set-indices-in-fa-table
         (effective-fat fat32-in-memory)
         (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
         (make-list-ac
          (len
           (mv-nth 0
                   (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
          0 nil))
        1)))
     (dir-ent (car dir-ent-list))))))

(defthm
  lofat-place-file-correctness-1-lemma-32
  (implies
   (and
    (consp dir-ent-list)
    (< (dir-ent-first-cluster (car dir-ent-list))
       (+ 2 (count-of-clusters fat32-in-memory)))
    (not (dir-ent-directory-p (car dir-ent-list)))
    (< 0
       (len (explode (lofat-file->contents file))))
    (lofat-fs-p fat32-in-memory)
    (useful-dir-ent-list-p dir-ent-list)
    (equal
     (mv-nth
      1
      (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list)))
     0)
    (no-duplicatesp-equal
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
    (lofat-regular-file-p file)
    (<=
     (+ -1
        (len (make-clusters (lofat-file->contents file)
                            (cluster-size fat32-in-memory))))
     (+
      -1
      (count-free-clusters (effective-fat fat32-in-memory))
      (len
       (mv-nth 0
               (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))))))
   (equal
    (dir-ent-clusterchain
     (mv-nth
      0
      (place-contents
       (update-fati
        (nth
         0
         (find-n-free-clusters
          (set-indices-in-fa-table
           (effective-fat fat32-in-memory)
           (mv-nth 0
                   (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
           (make-list-ac
            (len
             (mv-nth
              0
              (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
            0 nil))
          1))
        (fat32-update-lower-28
         (fati
          (nth
           0
           (find-n-free-clusters
            (set-indices-in-fa-table
             (effective-fat fat32-in-memory)
             (mv-nth
              0
              (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
             (make-list-ac
              (len
               (mv-nth
                0
                (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
              0 nil))
            1))
          fat32-in-memory)
         268435455)
        (mv-nth 0
                (clear-clusterchain fat32-in-memory
                                    (dir-ent-first-cluster (car dir-ent-list))
                                    (dir-ent-file-size (car dir-ent-list)))))
       (car dir-ent-list)
       (lofat-file->contents file)
       (len (explode (lofat-file->contents file)))
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32-in-memory)
          (mv-nth 0
                  (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
          (make-list-ac
           (len
            (mv-nth
             0
             (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
           0 nil))
         1))))
     (dir-ent-set-first-cluster-file-size
      (car dir-ent-list)
      (nth
       0
       (find-n-free-clusters
        (set-indices-in-fa-table
         (effective-fat fat32-in-memory)
         (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
         (make-list-ac
          (len
           (mv-nth 0
                   (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
          0 nil))
        1))
      (len (explode (lofat-file->contents file)))))
    (mv
     (cons
      (nth
       0
       (find-n-free-clusters
        (set-indices-in-fa-table
         (effective-fat fat32-in-memory)
         (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
         (make-list-ac
          (len
           (mv-nth 0
                   (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
          0 nil))
        1))
      (find-n-free-clusters
       (effective-fat
        (update-fati
         (nth
          0
          (find-n-free-clusters
           (set-indices-in-fa-table
            (effective-fat fat32-in-memory)
            (mv-nth 0
                    (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
            (make-list-ac
             (len
              (mv-nth
               0
               (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
             0 nil))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (set-indices-in-fa-table
              (effective-fat fat32-in-memory)
              (mv-nth
               0
               (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
              (make-list-ac
               (len
                (mv-nth
                 0
                 (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
               0 nil))
             1))
           fat32-in-memory)
          268435455)
         (mv-nth
          0
          (clear-clusterchain fat32-in-memory
                              (dir-ent-first-cluster (car dir-ent-list))
                              (dir-ent-file-size (car dir-ent-list))))))
       (+
        -1
        (len
         (make-clusters
          (lofat-file->contents file)
          (cluster-size
           (update-fati
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32-in-memory)
               (mv-nth
                0
                (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
               (make-list-ac
                (len
                 (mv-nth
                  0
                  (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
                0 nil))
              1))
            (fat32-update-lower-28
             (fati
              (nth
               0
               (find-n-free-clusters
                (set-indices-in-fa-table
                 (effective-fat fat32-in-memory)
                 (mv-nth
                  0
                  (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
                 (make-list-ac
                  (len (mv-nth 0
                               (dir-ent-clusterchain
                                fat32-in-memory (car dir-ent-list))))
                  0 nil))
                1))
              fat32-in-memory)
             268435455)
            (mv-nth 0
                    (clear-clusterchain
                     fat32-in-memory
                     (dir-ent-first-cluster (car dir-ent-list))
                     (dir-ent-file-size (car dir-ent-list)))))))))))
     0)))
  :hints
  (("goal"
    :in-theory (disable (:rewrite lofat-place-file-correctness-1-lemma-25))
    :use (:instance (:rewrite lofat-place-file-correctness-1-lemma-25)
                    (dir-ent (car dir-ent-list))
                    (fat32-in-memory fat32-in-memory)))))

(defthm
  lofat-place-file-correctness-1-lemma-33
  (implies
   (and
    (consp dir-ent-list)
    (< (dir-ent-first-cluster (car dir-ent-list))
       (+ 2 (count-of-clusters fat32-in-memory)))
    (not (dir-ent-directory-p (car dir-ent-list)))
    (< 0
       (len (explode (lofat-file->contents file))))
    (lofat-fs-p fat32-in-memory)
    (useful-dir-ent-list-p dir-ent-list)
    (equal
     (mv-nth
      1
      (dir-ent-clusterchain-contents fat32-in-memory (car dir-ent-list)))
     0)
    (no-duplicatesp-equal
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
    (lofat-regular-file-p file)
    (<=
     (+ -1
        (len (make-clusters (lofat-file->contents file)
                            (cluster-size fat32-in-memory))))
     (+
      -1
      (count-free-clusters (effective-fat fat32-in-memory))
      (len
       (mv-nth 0
               (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))))
    (<=
     2
     (nth
      0
      (find-n-free-clusters
       (set-indices-in-fa-table
        (effective-fat fat32-in-memory)
        (mv-nth 0
                (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
        (make-list-ac
         (len
          (mv-nth 0
                  (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
         0 nil))
       1))))
   (equal
    (dir-ent-clusterchain-contents
     (mv-nth
      0
      (place-contents
       (update-fati
        (nth
         0
         (find-n-free-clusters
          (set-indices-in-fa-table
           (effective-fat fat32-in-memory)
           (mv-nth 0
                   (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
           (make-list-ac
            (len
             (mv-nth
              0
              (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
            0 nil))
          1))
        (fat32-update-lower-28
         (fati
          (nth
           0
           (find-n-free-clusters
            (set-indices-in-fa-table
             (effective-fat fat32-in-memory)
             (mv-nth
              0
              (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
             (make-list-ac
              (len
               (mv-nth
                0
                (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
              0 nil))
            1))
          fat32-in-memory)
         268435455)
        (mv-nth 0
                (clear-clusterchain fat32-in-memory
                                    (dir-ent-first-cluster (car dir-ent-list))
                                    (dir-ent-file-size (car dir-ent-list)))))
       (car dir-ent-list)
       (lofat-file->contents file)
       (len (explode (lofat-file->contents file)))
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32-in-memory)
          (mv-nth 0
                  (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
          (make-list-ac
           (len
            (mv-nth
             0
             (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
           0 nil))
         1))))
     (dir-ent-set-first-cluster-file-size
      (car dir-ent-list)
      (nth
       0
       (find-n-free-clusters
        (set-indices-in-fa-table
         (effective-fat fat32-in-memory)
         (mv-nth 0
                 (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
         (make-list-ac
          (len
           (mv-nth 0
                   (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
          0 nil))
        1))
      (len (explode (lofat-file->contents file)))))
    (mv
     (implode
      (append
       (explode (lofat-file->contents file))
       (make-list-ac
        (+
         (min
          (dir-ent-file-size
           (dir-ent-set-first-cluster-file-size
            (car dir-ent-list)
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32-in-memory)
               (mv-nth
                0
                (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
               (make-list-ac
                (len
                 (mv-nth
                  0
                  (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
                0 nil))
              1))
            (len (explode (lofat-file->contents file)))))
          (*
           (len
            (make-clusters
             (lofat-file->contents file)
             (cluster-size
              (update-fati
               (nth
                0
                (find-n-free-clusters
                 (set-indices-in-fa-table
                  (effective-fat fat32-in-memory)
                  (mv-nth
                   0
                   (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
                  (make-list-ac
                   (len (mv-nth 0
                                (dir-ent-clusterchain
                                 fat32-in-memory (car dir-ent-list))))
                   0 nil))
                 1))
               (fat32-update-lower-28
                (fati
                 (nth
                  0
                  (find-n-free-clusters
                   (set-indices-in-fa-table
                    (effective-fat fat32-in-memory)
                    (mv-nth 0
                            (dir-ent-clusterchain
                             fat32-in-memory (car dir-ent-list)))
                    (make-list-ac
                     (len (mv-nth 0
                                  (dir-ent-clusterchain
                                   fat32-in-memory (car dir-ent-list))))
                     0 nil))
                   1))
                 fat32-in-memory)
                268435455)
               (mv-nth 0
                       (clear-clusterchain
                        fat32-in-memory
                        (dir-ent-first-cluster (car dir-ent-list))
                        (dir-ent-file-size (car dir-ent-list))))))))
           (cluster-size
            (update-fati
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32-in-memory)
                (mv-nth
                 0
                 (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
                (make-list-ac
                 (len
                  (mv-nth
                   0
                   (dir-ent-clusterchain fat32-in-memory (car dir-ent-list))))
                 0 nil))
               1))
             (fat32-update-lower-28
              (fati
               (nth
                0
                (find-n-free-clusters
                 (set-indices-in-fa-table
                  (effective-fat fat32-in-memory)
                  (mv-nth
                   0
                   (dir-ent-clusterchain fat32-in-memory (car dir-ent-list)))
                  (make-list-ac
                   (len (mv-nth 0
                                (dir-ent-clusterchain
                                 fat32-in-memory (car dir-ent-list))))
                   0 nil))
                 1))
               fat32-in-memory)
              268435455)
             (mv-nth
              0
              (clear-clusterchain fat32-in-memory
                                  (dir-ent-first-cluster (car dir-ent-list))
                                  (dir-ent-file-size (car dir-ent-list))))))))
         (- (length (lofat-file->contents file))))
        (code-char 0)
        nil)))
     0)))
  :hints
  (("goal"
    :in-theory (disable (:rewrite lofat-place-file-correctness-1-lemma-25))
    :use (:instance (:rewrite lofat-place-file-correctness-1-lemma-25)
                    (dir-ent (car dir-ent-list))
                    (fat32-in-memory fat32-in-memory)))))
