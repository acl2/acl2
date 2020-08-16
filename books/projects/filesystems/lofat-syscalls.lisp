(in-package "ACL2")

;  lofat-syscalls.lisp                                 Mihir Mehta

; Syscalls for LoFAT. These syscalls usually return, among other things, a
; return value (corresponding to the C return value) and an errno.

(include-book "lofat")
(include-book "hifat-syscalls")

(defund lofat-open (path fd-table file-table)
  (declare (xargs :guard (and (fat32-filename-list-p path)
                              (fd-table-p fd-table)
                              (file-table-p file-table))))
  (hifat-open path fd-table file-table))

(defthmd
  lofat-open-refinement
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (equal (mv-nth 1 (lofat-to-hifat fat32-in-memory))
               0))
   (equal
    (lofat-open path fd-table file-table)
    (hifat-open path
                fd-table file-table)))
  :hints
  (("goal"
    :in-theory
    (e/d (lofat-open)))))

(defthm
  fd-table-p-of-lofat-open
  (fd-table-p (mv-nth 0
                      (lofat-open path fd-table file-table)))
  :hints (("goal" :in-theory (enable lofat-open))))

(defthm
  file-table-p-of-lofat-open
  (file-table-p (mv-nth 1
                        (lofat-open path fd-table file-table)))
  :hints (("goal" :in-theory (enable lofat-open))))

(defthm integerp-of-lofat-open
  (integerp (mv-nth 2
                    (lofat-open path fd-table file-table)))
  :hints (("goal" :in-theory (enable lofat-open))))

(defund
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
       (path (file-table-element->fid (cdr file-table-entry)))
       ((mv root-dir-ent-list &) (root-dir-ent-list fat32-in-memory))
       ((mv file error-code)
        (lofat-find-file
         fat32-in-memory
         root-dir-ent-list
         path))
       ((unless (and (equal error-code 0)
                     (lofat-regular-file-p file)))
        (mv "" -1 error-code))
       (file-contents (lofat-file->contents file))
       (new-offset (min (+ offset count)
                        (length file-contents)))
       (buf (subseq file-contents
                    (min offset
                         (length file-contents))
                    new-offset)))
    (mv buf (length buf) 0)))

(defthm
  lofat-pread-correctness-1
  (mv-let (buf ret error-code)
    (lofat-pread fd count offset
                 fat32-in-memory fd-table file-table)
    (and (stringp buf)
         (integerp ret)
         (integerp error-code)
         (implies (>= ret 0)
                  (equal (length buf) ret))))
  :hints (("goal" :in-theory (enable lofat-pread)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (<=
      0
      (mv-nth
       1
       (lofat-pread fd count offset
                    fat32-in-memory fd-table file-table)))
     (equal
      (length
       (mv-nth
        0
        (lofat-pread fd count offset
                     fat32-in-memory fd-table file-table)))
      (mv-nth
       1
       (lofat-pread fd count offset
                    fat32-in-memory fd-table file-table)))))
   (:type-prescription
    :corollary
    (stringp
     (mv-nth
      0
      (lofat-pread fd count offset
                   fat32-in-memory fd-table file-table))))
   (:type-prescription
    :corollary
    (integerp
     (mv-nth
      1
      (lofat-pread fd count offset
                   fat32-in-memory fd-table file-table))))
   (:type-prescription
    :corollary
    (integerp
     (mv-nth 2
             (lofat-pread fd count offset fat32-in-memory
                          fd-table file-table))))))

(defthm
  lofat-pread-refinement-lemma-1
  (implies
   (and
    (useful-dir-ent-list-p dir-ent-list)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32-in-memory
                                          dir-ent-list entry-limit))
           0)
    (<=
     (+ 2 (count-of-clusters fat32-in-memory))
     (dir-ent-first-cluster (mv-nth 0
                                    (find-dir-ent dir-ent-list filename)))))
   (not (dir-ent-directory-p (mv-nth 0
                                     (find-dir-ent dir-ent-list filename)))))
  :hints
  (("goal"
    :in-theory
    (e/d (lofat-to-hifat-helper find-dir-ent useful-dir-ent-list-p)
         ((:definition no-duplicatesp-equal)
          (:rewrite useful-dir-ent-list-p-of-cdr)
          (:definition member-equal)
          (:rewrite take-of-len-free)
          (:definition take)
          (:definition assoc-equal))))))

(defthm
  lofat-pread-refinement-lemma-2
  (b*
      (((mv file &)
        (hifat-find-file
         (mv-nth
          0
          (lofat-to-hifat-helper fat32-in-memory
                                 dir-ent-list entry-limit))
         path)))
    (implies
     (and
      (lofat-fs-p fat32-in-memory)
      (useful-dir-ent-list-p dir-ent-list)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper fat32-in-memory
                               dir-ent-list entry-limit))
       0))
     (equal
      (m1-directory-file-p file)
      (lofat-directory-file-p
       (mv-nth
        0
        (lofat-find-file fat32-in-memory
                         dir-ent-list path))))))
  :hints
  (("Goal" :in-theory (enable hifat-find-file))))

(defthm
  lofat-pread-refinement
  (implies
   (and (equal (mv-nth 1 (lofat-to-hifat fat32-in-memory))
               0)
        (lofat-fs-p fat32-in-memory))
   (equal
    (lofat-pread fd count offset
                 fat32-in-memory fd-table file-table)
    (hifat-pread fd count offset
                 (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                 fd-table file-table)))
  :hints
  (("goal"
    :in-theory
    (e/d (lofat-to-hifat lofat-pread hifat-pread)
         ((:rewrite lofat-find-file-correctness-1)
          (:rewrite lofat-directory-file-p-when-lofat-file-p)
          (:rewrite m1-directory-file-p-when-m1-file-p)
          (:rewrite lofat-pread-refinement-lemma-2)
          ;; from accumulated-persistence
          (:definition find-dir-ent)
          (:definition lofat-find-file)))
    :use
    ((:instance
      (:rewrite lofat-find-file-correctness-1)
      (path
       (file-table-element->fid
        (cdr (assoc-equal (cdr (assoc-equal fd fd-table))
                          file-table))))
      (dir-ent-list
       (mv-nth 0 (root-dir-ent-list fat32-in-memory)))
      (entry-limit (max-entry-count fat32-in-memory)))
     (:instance
      (:rewrite lofat-directory-file-p-when-lofat-file-p)
      (file
       (mv-nth
        0
        (lofat-find-file
         fat32-in-memory
         (mv-nth 0 (root-dir-ent-list fat32-in-memory))
         (file-table-element->fid
          (cdr (assoc-equal (cdr (assoc-equal fd fd-table))
                            file-table)))))))
     (:instance
      (:rewrite m1-directory-file-p-when-m1-file-p)
      (x
       (mv-nth
        0
        (hifat-find-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32-in-memory
           (mv-nth 0 (root-dir-ent-list fat32-in-memory))
           (max-entry-count fat32-in-memory)))
         (file-table-element->fid
          (cdr (assoc-equal (cdr (assoc-equal fd fd-table))
                            file-table)))))))
     (:instance
      (:rewrite lofat-pread-refinement-lemma-2)
      (path
       (file-table-element->fid
        (cdr (assoc-equal (cdr (assoc-equal fd fd-table))
                          file-table))))
      (entry-limit (max-entry-count fat32-in-memory))
      (dir-ent-list
       (mv-nth 0 (root-dir-ent-list fat32-in-memory)))
      (fat32-in-memory fat32-in-memory))))))

(defund lofat-lstat (fat32-in-memory path)
  (declare (xargs :guard (and (lofat-fs-p fat32-in-memory)
                              (fat32-filename-list-p path))
                  :stobjs fat32-in-memory))
  (b*
      (((mv root-dir-ent-list &)
        (root-dir-ent-list
         fat32-in-memory))
       ((mv file errno)
        (lofat-find-file
         fat32-in-memory
         root-dir-ent-list
         path))
       ((when (not (equal errno 0)))
        (mv (make-struct-stat) -1 errno))
       (st_size (if (lofat-directory-file-p file)
                    *ms-max-dir-size*
                  (length (lofat-file->contents file)))))
    (mv
     (make-struct-stat
      :st_size st_size)
     0 0)))

(defthmd
  lofat-lstat-refinement-lemma-1
  (implies
   (and
    (stringp x)
    (unsigned-byte-p 32 (length x)))
   (equal (lofat-file-contents-fix x) x)))

(defthm
  struct-stat-p-of-lofat-lstat
  (struct-stat-p
   (mv-nth 0
           (lofat-lstat fat32-in-memory
                        (path-to-fat32-path (explode path)))))
  :hints (("goal" :in-theory (enable lofat-lstat))))

(defthm
  lofat-lstat-refinement
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (equal (mv-nth 1 (lofat-to-hifat fat32-in-memory))
               0))
   (equal
    (lofat-lstat fat32-in-memory path)
    (hifat-lstat (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                 path)))
  :hints
  (("goal"
    :in-theory
    (e/d (lofat-to-hifat lofat-lstat hifat-lstat
                         lofat-lstat-refinement-lemma-1)
         ((:rewrite lofat-find-file-correctness-1)
          (:rewrite lofat-pread-refinement-lemma-2)
          unsigned-byte-p
          (:rewrite m1-directory-file-p-when-m1-file-p)))
    :use
    ((:instance
      (:rewrite lofat-find-file-correctness-1)
      (dir-ent-list
       (mv-nth 0 (root-dir-ent-list fat32-in-memory)))
      (entry-limit (max-entry-count fat32-in-memory)))
     (:instance
      (:rewrite lofat-pread-refinement-lemma-2)
      (path path)
      (entry-limit (max-entry-count fat32-in-memory))
      (dir-ent-list
       (mv-nth 0 (root-dir-ent-list fat32-in-memory)))
      (fat32-in-memory fat32-in-memory))
     (:instance
      (:rewrite m1-directory-file-p-when-m1-file-p)
      (x
       (mv-nth
        0
        (hifat-find-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32-in-memory
           (mv-nth 0 (root-dir-ent-list fat32-in-memory))
           (max-entry-count fat32-in-memory)))
         path))))))))

(defund
  lofat-unlink (fat32-in-memory path)
  (declare
   (xargs :stobjs fat32-in-memory
          :guard (and (lofat-fs-p fat32-in-memory)
                      (fat32-filename-list-p path))))
  (b* (((mv root-dir-ent-list &)
        (root-dir-ent-list fat32-in-memory))
       ((mv file error-code)
        (lofat-find-file fat32-in-memory
                         root-dir-ent-list path))
       ((unless (equal error-code 0))
        (mv fat32-in-memory -1 *enoent*))
       ((unless (lofat-regular-file-p file))
        (mv fat32-in-memory -1 *eisdir*))
       ((mv fat32-in-memory error-code)
        (lofat-remove-file fat32-in-memory
                           (pseudo-root-dir-ent fat32-in-memory)
                           path))
       ((unless (equal error-code 0))
        (mv fat32-in-memory -1 error-code)))
    (mv fat32-in-memory 0 0)))

(defthm lofat-fs-p-of-lofat-unlink
  (implies (lofat-fs-p fat32-in-memory)
           (lofat-fs-p
            (mv-nth 0 (lofat-unlink fat32-in-memory path))))
  :hints (("Goal" :in-theory (enable lofat-unlink)) ))

(defthm
  lofat-unlink-refinement-lemma-1
  (and (implies (equal (mv-nth 1 (hifat-find-file fs path))
                       *enoent*)
                (equal (hifat-remove-file fs path)
                       (mv (hifat-file-alist-fix fs)
                           *enoent*)))
       (implies (equal (mv-nth 1 (hifat-find-file fs path))
                       *enotdir*)
                (equal (hifat-remove-file fs path)
                       (mv (hifat-file-alist-fix fs)
                           *enotdir*))))
  :hints
  (("goal"
    :induct (hifat-find-file fs path)
    :in-theory (enable hifat-remove-file hifat-find-file))))

(defthmd
  lofat-unlink-refinement-lemma-2
  (implies (equal (mv-nth 1 (hifat-find-file fs path))
                  0)
           (equal (mv-nth 1 (hifat-remove-file fs path))
                  0))
  :hints
  (("goal"
    :induct (hifat-find-file fs path)
    :in-theory (enable hifat-remove-file hifat-find-file))))

(defthmd
  lofat-unlink-refinement-lemma-3
  (or (equal (mv-nth 1 (hifat-find-file fs path))
             0)
      (equal (mv-nth 1 (hifat-find-file fs path))
             *enoent*)
      (equal (mv-nth 1 (hifat-find-file fs path))
             *enotdir*))
  :hints
  (("goal"
    :in-theory (enable hifat-find-file))))

(defthm
  lofat-unlink-refinement-lemma-4
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (useful-dir-ent-list-p dir-ent-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32-in-memory
                                              dir-ent-list entry-limit))
               0))
   (equal
    (lofat-regular-file-p
     (mv-nth 0
             (lofat-find-file fat32-in-memory dir-ent-list path)))
    (m1-regular-file-p
     (mv-nth 0
             (hifat-find-file
              (mv-nth 0
                      (lofat-to-hifat-helper fat32-in-memory
                                             dir-ent-list entry-limit))
              path)))))
  :hints
  (("goal" :induct (lofat-find-file fat32-in-memory dir-ent-list path)
    :in-theory (enable lofat-find-file hifat-find-file))))

(defthm
  lofat-unlink-refinement-lemma-5
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (fat32-masked-entry-p first-cluster)
    (stringp dir-contents)
    (< 0 (len (explode dir-contents)))
    (<= (len (explode dir-contents))
        *ms-max-dir-size*)
    (equal (mv-nth 1
                   (get-clusterchain-contents
                    fat32-in-memory
                    first-cluster *ms-max-dir-size*))
           0)
    (no-duplicatesp-equal
     (mv-nth
      0
      (fat32-build-index-list (effective-fat fat32-in-memory)
                              first-cluster *ms-max-dir-size*
                              (cluster-size fat32-in-memory))))
    (< first-cluster
       (+ *ms-first-data-cluster*
          (count-of-clusters fat32-in-memory))))
   (no-duplicatesp-equal
    (mv-nth
     0
     (fat32-build-index-list
      (effective-fat
       (mv-nth
        0
        (update-dir-contents fat32-in-memory
                             first-cluster dir-contents)))
      first-cluster *ms-max-dir-size*
      (cluster-size fat32-in-memory)))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (update-dir-contents-correctness-1)
     (no-duplicatesp-equal-of-fat32-build-index-list-of-effective-fat-of-update-dir-contents
      (:rewrite get-clusterchain-contents-correctness-2)))
    :expand (get-clusterchain-contents
             fat32-in-memory first-cluster 2097152)
    :use
    (no-duplicatesp-equal-of-fat32-build-index-list-of-effective-fat-of-update-dir-contents
     (:instance
      (:rewrite get-clusterchain-contents-correctness-2)
      (length 2097152)
      (masked-current-cluster first-cluster))))))

(defthm
  lofat-unlink-refinement-lemma-6
  (implies
   (and
    (dir-ent-p dir-ent)
    (<= 2 (dir-ent-first-cluster dir-ent))
    (consp (cdr path))
    (lofat-fs-p fat32-in-memory)
    (fat32-filename-list-p path)
    (equal (mv-nth 1
                   (dir-ent-clusterchain-contents fat32-in-memory dir-ent))
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
       (max-entry-count fat32-in-memory))))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32-in-memory
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
       (max-entry-count fat32-in-memory)))
     0))
   (equal (dir-ent-clusterchain
           (mv-nth 0
                   (lofat-remove-file fat32-in-memory dir-ent path))
           dir-ent)
          (dir-ent-clusterchain fat32-in-memory dir-ent)))
  :hints
  (("goal"
    :do-not-induct t
    :expand (lofat-remove-file fat32-in-memory dir-ent path)
    :in-theory
    (disable (:rewrite dir-ent-clusterchain-of-lofat-remove-file-disjoint))
    :use
    (:instance
     (:rewrite dir-ent-clusterchain-of-lofat-remove-file-disjoint)
     (entry-limit (max-entry-count fat32-in-memory))
     (path (cdr path))
     (root-dir-ent
      (mv-nth
       0
       (find-dir-ent
        (make-dir-ent-list
         (mv-nth 0
                 (dir-ent-clusterchain-contents fat32-in-memory dir-ent)))
        (car path))))))))

(defthm
  lofat-unlink-refinement-lemma-7
  (implies
   (and
    (consp (cdr path))
    (lofat-fs-p fat32-in-memory)
    (fat32-filename-list-p path)
    (equal
     (mv-nth
      1
      (dir-ent-clusterchain-contents fat32-in-memory
                                     (pseudo-root-dir-ent fat32-in-memory)))
     0)
    (no-duplicatesp-equal
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory
                                   (pseudo-root-dir-ent fat32-in-memory))))
    (not-intersectp-list
     (mv-nth 0
             (dir-ent-clusterchain fat32-in-memory
                                   (pseudo-root-dir-ent fat32-in-memory)))
     (mv-nth 2
             (lofat-to-hifat-helper
              fat32-in-memory
              (make-dir-ent-list
               (mv-nth 0
                       (dir-ent-clusterchain-contents
                        fat32-in-memory
                        (pseudo-root-dir-ent fat32-in-memory))))
              (max-entry-count fat32-in-memory))))
    (equal
     (mv-nth 3
             (lofat-to-hifat-helper
              fat32-in-memory
              (make-dir-ent-list
               (mv-nth 0
                       (dir-ent-clusterchain-contents
                        fat32-in-memory
                        (pseudo-root-dir-ent fat32-in-memory))))
              (max-entry-count fat32-in-memory)))
     0))
   (not-intersectp-list
    (mv-nth 0
            (dir-ent-clusterchain fat32-in-memory
                                  (pseudo-root-dir-ent fat32-in-memory)))
    (mv-nth
     2
     (lofat-to-hifat-helper
      (mv-nth 0
              (lofat-remove-file fat32-in-memory
                                 (pseudo-root-dir-ent fat32-in-memory)
                                 path))
      (make-dir-ent-list (mv-nth 0
                                 (dir-ent-clusterchain-contents
                                  fat32-in-memory
                                  (pseudo-root-dir-ent fat32-in-memory))))
      (max-entry-count fat32-in-memory)))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite lofat-remove-file-correctness-1-lemma-1))
    :use
    (:instance
     (:rewrite lofat-remove-file-correctness-1-lemma-1)
     (entry-limit
      (max-entry-count
       (mv-nth
        0
        (lofat-remove-file
         fat32-in-memory
         (pseudo-root-dir-ent
          (mv-nth 0
                  (lofat-remove-file fat32-in-memory
                                     (pseudo-root-dir-ent fat32-in-memory)
                                     path)))
         path))))
     (path path)
     (root-dir-ent
      (pseudo-root-dir-ent
       (mv-nth 0
               (lofat-remove-file fat32-in-memory
                                  (pseudo-root-dir-ent fat32-in-memory)
                                  path))))
     (fat32-in-memory fat32-in-memory)
     (x
      (mv-nth
       0
       (dir-ent-clusterchain
        (mv-nth
         0
         (lofat-remove-file
          fat32-in-memory
          (pseudo-root-dir-ent
           (mv-nth 0
                   (lofat-remove-file fat32-in-memory
                                      (pseudo-root-dir-ent fat32-in-memory)
                                      path)))
          path))
        (pseudo-root-dir-ent
         (mv-nth 0
                 (lofat-remove-file fat32-in-memory
                                    (pseudo-root-dir-ent fat32-in-memory)
                                    path))))))))))

(defthm
  lofat-unlink-refinement
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (fat32-filename-list-p path)
        (equal (mv-nth 1 (lofat-to-hifat fat32-in-memory))
               0))
   (and
    (equal
     (mv-nth
      1
      (lofat-to-hifat (mv-nth 0
                              (lofat-unlink fat32-in-memory path))))
     0)
    (equal
     (mv-nth
      0
      (lofat-to-hifat (mv-nth 0
                              (lofat-unlink fat32-in-memory path))))
     (mv-nth 0
             (hifat-unlink (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                           path)))
    (equal (mv-nth 1
                   (lofat-unlink fat32-in-memory path))
           (mv-nth 1
                   (hifat-unlink (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                                 path)))))
  :hints
  (("goal"
    :in-theory (e/d (lofat-unlink lofat-to-hifat root-dir-ent-list
                                  update-dir-contents-correctness-1)
                    ((:rewrite lofat-remove-file-correctness-1)
                     make-list-ac-removal
                     (:rewrite lofat-remove-file-correctness-1-lemma-64)
                     (:rewrite lofat-find-file-correctness-1)
                     lofat-unlink-refinement-lemma-1
                     (:rewrite
                      dir-ent-clusterchain-contents-of-lofat-place-file-coincident-lemma-15)
                     (:rewrite lofat-place-file-correctness-1-lemma-6)
                     (:linear
                      dir-ent-clusterchain-contents-of-lofat-remove-file-disjoint-lemma-12)))
    :do-not-induct t
    :use
    ((:instance (:rewrite lofat-remove-file-correctness-1)
                (entry-limit (max-entry-count fat32-in-memory))
                (path path)
                (root-dir-ent (pseudo-root-dir-ent fat32-in-memory))
                (fat32-in-memory fat32-in-memory))
     (:instance
      (:rewrite lofat-find-file-correctness-1)
      (dir-ent-list
       (make-dir-ent-list
        (mv-nth 0
                (dir-ent-clusterchain-contents
                 fat32-in-memory
                 (pseudo-root-dir-ent fat32-in-memory)))))
      (entry-limit (max-entry-count fat32-in-memory)))
     (:instance
      (:rewrite lofat-unlink-refinement-lemma-3)
      (fs
       (mv-nth 0
               (lofat-to-hifat-helper
                fat32-in-memory
                (make-dir-ent-list
                 (mv-nth 0
                         (dir-ent-clusterchain-contents
                          fat32-in-memory
                          (pseudo-root-dir-ent fat32-in-memory))))
                (max-entry-count fat32-in-memory)))))
     (:instance
      (:rewrite lofat-unlink-refinement-lemma-2)
      (fs
       (mv-nth 0
               (lofat-to-hifat-helper
                fat32-in-memory
                (make-dir-ent-list
                 (mv-nth 0
                         (dir-ent-clusterchain-contents
                          fat32-in-memory
                          (pseudo-root-dir-ent fat32-in-memory))))
                (max-entry-count fat32-in-memory)))))
     (:instance
      lofat-unlink-refinement-lemma-1
      (fs
       (mv-nth 0
               (lofat-to-hifat-helper
                fat32-in-memory
                (make-dir-ent-list
                 (mv-nth 0
                         (dir-ent-clusterchain-contents
                          fat32-in-memory
                          (pseudo-root-dir-ent fat32-in-memory))))
                (max-entry-count fat32-in-memory)))))))))

(defund lofat-rmdir (fat32-in-memory path)
  (declare (xargs :stobjs fat32-in-memory
                  :guard (and (lofat-fs-p fat32-in-memory)
                              (fat32-filename-list-p path))))
  (b*
      (((mv fs error-code) (lofat-to-hifat fat32-in-memory))
       ((unless (equal error-code 0)) (mv fat32-in-memory *eio*))
       ((mv fs & error-code) (hifat-rmdir fs path))
       ((mv fat32-in-memory &) (hifat-to-lofat fat32-in-memory fs)))
    (mv fat32-in-memory error-code)))

(defund lofat-truncate (fat32-in-memory path size)
  (declare (xargs :stobjs fat32-in-memory
                  :guard (and (lofat-fs-p fat32-in-memory)
                              (fat32-filename-list-p path)
                              (natp size))))
  (b*
      (((mv fs error-code) (lofat-to-hifat fat32-in-memory))
       ((unless (equal error-code 0)) (mv fat32-in-memory -1 *eio*))
       ((mv fs retval error-code) (hifat-truncate fs path size))
       ((mv fat32-in-memory &) (hifat-to-lofat fat32-in-memory fs)))
    (mv fat32-in-memory retval error-code)))

(defthm lofat-fs-p-of-lofat-truncate
  (implies
   (lofat-fs-p fat32-in-memory)
   (lofat-fs-p (mv-nth 0 (lofat-truncate fat32-in-memory path size))))
  :hints (("Goal" :in-theory (enable lofat-truncate)) ))

(defun lofat-statfs (fat32-in-memory)
  (declare (xargs :stobjs (fat32-in-memory)
                  :guard (lofat-fs-p fat32-in-memory)))
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

(defund lofat-pwrite (fd buf offset fat32-in-memory fd-table file-table)
  (declare (xargs :stobjs fat32-in-memory
                  :guard (and (lofat-fs-p fat32-in-memory)
                              (natp fd)
                              (stringp buf)
                              (natp offset)
                              (fd-table-p fd-table)
                              (file-table-p file-table))))
  (b*
      (((mv fs error-code) (lofat-to-hifat fat32-in-memory))
       ((unless (equal error-code 0)) (mv fat32-in-memory -1 *eio*))
       ((mv fs retval error-code)
        (hifat-pwrite fd buf offset fs fd-table file-table))
       ((mv fat32-in-memory &) (hifat-to-lofat fat32-in-memory fs)))
    (mv fat32-in-memory retval error-code)))

(defthm integerp-of-lofat-pwrite
  (integerp (mv-nth 1 (lofat-pwrite fd buf offset fat32-in-memory fd-table
                                    file-table)))
  :hints (("Goal" :in-theory (enable lofat-pwrite)) )
  :rule-classes :type-prescription)

(defthm lofat-fs-p-of-lofat-pwrite
  (implies
   (lofat-fs-p fat32-in-memory)
   (lofat-fs-p (mv-nth 0 (lofat-pwrite fd buf offset fat32-in-memory fd-table
                                       file-table))))
  :hints (("Goal" :in-theory (enable lofat-pwrite)) ))

(defund lofat-close (fd fd-table file-table)
  (declare (xargs :guard (and (fd-table-p fd-table)
                              (file-table-p file-table))))
  (hifat-close fd fd-table file-table))

(defund lofat-truncate (fat32-in-memory path size)
  (declare (xargs :stobjs fat32-in-memory
                  :guard (and (lofat-fs-p fat32-in-memory)
                              (fat32-filename-list-p path)
                              (natp size))))
  (b*
      (((mv fs error-code) (lofat-to-hifat fat32-in-memory))
       ((unless (equal error-code 0)) (mv fat32-in-memory -1 *eio*))
       ((mv fs retval error-code) (hifat-truncate fs path size))
       ((mv fat32-in-memory &) (hifat-to-lofat fat32-in-memory fs)))
    (mv fat32-in-memory retval error-code)))

(defund lofat-mkdir (fat32-in-memory path)
  (declare (xargs :stobjs fat32-in-memory
                  :guard (and (lofat-fs-p fat32-in-memory)
                              (fat32-filename-list-p path))))
  (b*
      (((mv fs error-code) (lofat-to-hifat fat32-in-memory))
       ((unless (equal error-code 0)) (mv fat32-in-memory -1 *eio*))
       ((mv fs retval error-code) (hifat-mkdir fs path))
       ((mv fat32-in-memory &) (hifat-to-lofat fat32-in-memory fs)))
    (mv fat32-in-memory retval error-code)))

(defthm integerp-of-lofat-mkdir
  (integerp (mv-nth 1 (lofat-mkdir fat32-in-memory path)))
  :hints (("Goal" :in-theory (enable lofat-mkdir)) ))

(defthm lofat-fs-p-of-lofat-mkdir
  (implies
   (lofat-fs-p fat32-in-memory)
   (lofat-fs-p (mv-nth 0 (lofat-mkdir fat32-in-memory path))))
  :hints (("Goal" :in-theory (enable lofat-mkdir)) ))

;; Semantics under consideration: each directory stream is a list of directory
;; entries, and each readdir operation removes a directory entry from the front
;; of the list, never to be seen again until a new directory stream should be
;; opened.
(fty::defalist
 dirstream-table
 :key-type nat
 :val-type dir-ent-list
 :true-listp t)

(defthm dirstream-table-p-correctness-1
  (implies (dirstream-table-p dirstream-table)
           (nat-listp (strip-cars dirstream-table))))

;; The dirstream-table has to be returned, since it is potentially changed.
(defund lofat-opendir (fat32-in-memory dirstream-table path)
  (declare (xargs :stobjs fat32-in-memory
                  :guard (and (lofat-fs-p fat32-in-memory)
                              (dirstream-table-p dirstream-table)
                              (fat32-filename-list-p path))
                  :guard-debug t))
  (b*
      ((dirstream-table (mbe :exec dirstream-table
                             :logic (dirstream-table-fix dirstream-table)))
       ((mv root-dir-ent-list &) (root-dir-ent-list fat32-in-memory))
       ((mv file error-code)
        (lofat-find-file fat32-in-memory root-dir-ent-list path))
       ((unless (zp error-code)) (mv dirstream-table -1 error-code))
       ((unless (lofat-directory-file-p file)) (mv dirstream-table -1 *ENOTDIR*))
       (dirstream-table-index
        (find-new-index (strip-cars dirstream-table))))
    (mv
     (cons (cons dirstream-table-index (lofat-file->contents file))
      dirstream-table-index)
     dirstream-table-index
     0)))
