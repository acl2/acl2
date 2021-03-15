(in-package "ACL2")

;  lofat-syscalls.lisp                                 Mihir Mehta

; Syscalls for LoFAT. These syscalls usually return, among other things, a
; return value (corresponding to the C return value) and an errno.

(include-book "lofat/lofat-pwrite")
(include-book "lofat/lofat-mkdir")

(local (in-theory (disable make-list-ac-removal)))

(defund lofat-open (path fd-table file-table)
  (declare (xargs :guard (and (fat32-filename-list-p path)
                              (fd-table-p fd-table)
                              (file-table-p file-table))))
  (hifat-open path fd-table file-table))

(defthm lofat-open-correctness-1
  (and
   (natp (mv-nth 2
                 (lofat-open path fd-table file-table)))
   (integerp (mv-nth 3
                     (lofat-open path fd-table file-table))))
  :hints (("goal" :in-theory (enable lofat-open hifat-open)))
  :rule-classes
  ((:type-prescription
    :corollary
    (natp (mv-nth 2
                  (lofat-open path fd-table file-table))))
   (:type-prescription
    :corollary
    (integerp (mv-nth 3
                      (lofat-open path fd-table file-table))))))

(defthmd
  lofat-open-refinement
  (implies
   (and (lofat-fs-p fat32$c)
        (equal (mv-nth 1 (lofat-to-hifat fat32$c))
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
  (fd count offset fat32$c fd-table file-table)
  (declare (xargs :guard (and (natp fd)
                              (natp count)
                              (natp offset)
                              (fd-table-p fd-table)
                              (file-table-p file-table)
                              (lofat-fs-p fat32$c))
                  :stobjs fat32$c))
  (b*
      ((fd-table (mbe :logic (fd-table-fix fd-table) :exec fd-table))
       (file-table (mbe :logic (file-table-fix file-table) :exec file-table))
       (fd-table-entry (assoc-equal fd fd-table))
       ((unless (consp fd-table-entry))
        (mv "" -1 *ebadf*))
       (file-table-entry (assoc-equal (cdr fd-table-entry)
                                      file-table))
       ((unless (consp file-table-entry))
        (mv "" -1 *ebadf*))
       (path (file-table-element->fid (cdr file-table-entry)))
       ((mv root-d-e-list &) (root-d-e-list fat32$c))
       ((mv file error-code)
        (lofat-find-file
         fat32$c
         root-d-e-list
         path))
       ((unless (lofat-regular-file-p file))
        (mv "" -1 *eisdir*))
       ((unless (equal error-code 0))
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
                 fat32$c fd-table file-table)
    (and (stringp buf)
         (integerp ret)
         (natp error-code)
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
                    fat32$c fd-table file-table)))
     (equal
      (length
       (mv-nth
        0
        (lofat-pread fd count offset
                     fat32$c fd-table file-table)))
      (mv-nth
       1
       (lofat-pread fd count offset
                    fat32$c fd-table file-table)))))
   (:type-prescription
    :corollary
    (stringp
     (mv-nth
      0
      (lofat-pread fd count offset
                   fat32$c fd-table file-table))))
   (:type-prescription
    :corollary
    (integerp
     (mv-nth
      1
      (lofat-pread fd count offset
                   fat32$c fd-table file-table))))
   (:type-prescription
    :corollary
    (natp
     (mv-nth 2
             (lofat-pread fd count offset fat32$c
                          fd-table file-table))))))

(defthm
  lofat-pread-refinement-lemma-2
  (b*
      (((mv file &)
        (hifat-find-file
         (mv-nth
          0
          (lofat-to-hifat-helper fat32$c
                                 d-e-list entry-limit))
         path)))
    (implies
     (and
      (lofat-fs-p fat32$c)
      (useful-d-e-list-p d-e-list)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper fat32$c
                               d-e-list entry-limit))
       0))
     (equal
      (m1-directory-file-p file)
      (lofat-directory-file-p
       (mv-nth
        0
        (lofat-find-file fat32$c
                         d-e-list path))))))
  :hints
  (("Goal" :in-theory (enable hifat-find-file))))

(defthm
  lofat-pread-refinement
  (implies (and (equal (mv-nth 1 (lofat-to-hifat fat32$c))
                       0)
                (lofat-fs-p fat32$c))
           (equal (lofat-pread fd count offset
                               fat32$c fd-table file-table)
                  (hifat-pread fd count offset
                               (mv-nth 0 (lofat-to-hifat fat32$c))
                               fd-table file-table)))
  :hints
  (("goal"
    :in-theory (e/d (lofat-to-hifat lofat-pread hifat-pread)
                    ((:rewrite lofat-find-file-correctness-1)
                     (:rewrite lofat-directory-file-p-when-lofat-file-p)
                     (:rewrite m1-directory-file-p-when-m1-file-p)
                     (:rewrite lofat-pread-refinement-lemma-2)
                     (:definition find-d-e)
                     (:definition lofat-find-file)))
    :use
    ((:instance
      (:rewrite lofat-find-file-correctness-1)
      (path
       (file-table-element->fid
        (cdr (assoc-equal (cdr (assoc-equal fd (fd-table-fix fd-table)))
                          (file-table-fix file-table)))))
      (d-e-list (mv-nth 0 (root-d-e-list fat32$c)))
      (entry-limit (max-entry-count fat32$c)))
     (:instance
      (:rewrite lofat-directory-file-p-when-lofat-file-p)
      (file
       (mv-nth
        0
        (lofat-find-file
         fat32$c
         (mv-nth 0 (root-d-e-list fat32$c))
         (file-table-element->fid
          (cdr (assoc-equal (cdr (assoc-equal fd (fd-table-fix fd-table)))
                            (file-table-fix file-table))))))))
     (:instance
      (:rewrite m1-directory-file-p-when-m1-file-p)
      (x
       (mv-nth
        0
        (hifat-find-file
         (mv-nth 0
                 (lofat-to-hifat-helper
                  fat32$c
                  (mv-nth 0 (root-d-e-list fat32$c))
                  (max-entry-count fat32$c)))
         (file-table-element->fid
          (cdr (assoc-equal (cdr (assoc-equal fd (fd-table-fix fd-table)))
                            (file-table-fix file-table))))))))
     (:instance
      (:rewrite lofat-pread-refinement-lemma-2)
      (path
       (file-table-element->fid
        (cdr (assoc-equal (cdr (assoc-equal fd (fd-table-fix fd-table)))
                          (file-table-fix file-table)))))
      (entry-limit (max-entry-count fat32$c))
      (d-e-list (mv-nth 0 (root-d-e-list fat32$c)))
      (fat32$c fat32$c))))))

(defund lofat-lstat (fat32$c path)
  (declare (xargs :guard (and (lofat-fs-p fat32$c)
                              (fat32-filename-list-p path))
                  :stobjs fat32$c))
  (b*
      (((mv root-d-e-list &)
        (root-d-e-list
         fat32$c))
       ((mv file errno)
        (lofat-find-file
         fat32$c
         root-d-e-list
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

(defthm lofat-lstat-correctness-1
  (and
   (struct-stat-p (mv-nth 0 (lofat-lstat fat32$c path)))
   (integerp (mv-nth 1 (lofat-lstat fat32$c path)))
   (natp (mv-nth 2 (lofat-lstat fat32$c path))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-lstat)))
  :rule-classes
  ((:rewrite
    :corollary
    (struct-stat-p (mv-nth 0 (lofat-lstat fat32$c path))))
   (:type-prescription
    :corollary
    (integerp (mv-nth 1 (lofat-lstat fat32$c path))))
   (:type-prescription
    :corollary
    (natp (mv-nth 2 (lofat-lstat fat32$c path))))))

(defthm
  lofat-lstat-refinement
  (implies
   (and (lofat-fs-p fat32$c)
        (equal (mv-nth 1 (lofat-to-hifat fat32$c))
               0))
   (equal
    (lofat-lstat fat32$c path)
    (hifat-lstat (mv-nth 0 (lofat-to-hifat fat32$c))
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
      (d-e-list
       (mv-nth 0 (root-d-e-list fat32$c)))
      (entry-limit (max-entry-count fat32$c)))
     (:instance
      (:rewrite lofat-pread-refinement-lemma-2)
      (path path)
      (entry-limit (max-entry-count fat32$c))
      (d-e-list
       (mv-nth 0 (root-d-e-list fat32$c)))
      (fat32$c fat32$c))
     (:instance
      (:rewrite m1-directory-file-p-when-m1-file-p)
      (x
       (mv-nth
        0
        (hifat-find-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (mv-nth 0 (root-d-e-list fat32$c))
           (max-entry-count fat32$c)))
         path))))))))

(defund
  lofat-unlink (fat32$c path)
  (declare (xargs :stobjs fat32$c
                  :guard (and (lofat-fs-p fat32$c)
                              (fat32-filename-list-p path))))
  (b* (((mv root-d-e-list &)
        (root-d-e-list fat32$c))
       ((mv file error-code)
        (lofat-find-file fat32$c root-d-e-list path))
       ((unless (equal error-code 0))
        (mv fat32$c -1 *enoent*))
       ((unless (lofat-regular-file-p file))
        (mv fat32$c -1 *eisdir*))
       ((mv fat32$c error-code)
        (lofat-remove-file fat32$c (pseudo-root-d-e fat32$c)
                               path))
       ((unless (equal error-code 0))
        (mv fat32$c -1 error-code)))
    (mv fat32$c 0 0)))

(defthm lofat-fs-p-of-lofat-unlink
  (implies (lofat-fs-p fat32$c)
           (lofat-fs-p
            (mv-nth 0 (lofat-unlink fat32$c path))))
  :hints (("Goal" :in-theory (enable lofat-unlink)) ))

(defthm lofat-unlink-correctness-1
  (and
   (integerp (mv-nth 1
                     (lofat-unlink fat32$c path)))
   (natp (mv-nth 2
                 (lofat-unlink fat32$c path))))
  :hints (("goal" :in-theory (enable lofat-unlink)))
  :rule-classes
  ((:type-prescription
    :corollary
    (integerp (mv-nth 1
                      (lofat-unlink fat32$c path))))
   (:type-prescription
    :corollary
    (natp (mv-nth 2
                  (lofat-unlink fat32$c path))))))

(defthm
  lofat-unlink-refinement-lemma-1
  (implies
   (and (m1-file-p file)
        (equal (hifat-file-alist-fix (m1-file->contents file))
               (m1-file->contents file)))
   (equal (equal (m1-file-hifat-file-alist-fix (m1-file->d-e file)
                                               (m1-file->contents file))
                 file)
          t))
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d (m1-file-hifat-file-alist-fix)
                    (m1-file-hifat-file-alist-fix-normalisation)))))

(defthmd
  lofat-unlink-refinement-lemma-8
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
  lofat-unlink-refinement-lemma-5
  (implies
   (and
    (d-e-p d-e)
    (consp (cdr path))
    (lofat-fs-p fat32$c)
    (fat32-filename-list-p path)
    (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
           0)
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c d-e))
     (mv-nth 2
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (max-entry-count fat32$c))))
    (equal
     (mv-nth 3
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (max-entry-count fat32$c)))
     0))
   (equal (d-e-cc (mv-nth 0
                          (lofat-remove-file fat32$c d-e path))
                  d-e)
          (d-e-cc fat32$c d-e)))
  :hints
  (("goal"
    :do-not-induct t
    :expand (lofat-remove-file fat32$c d-e path)
    :in-theory (disable (:rewrite d-e-cc-of-lofat-remove-file-disjoint))
    :use
    (:instance
     (:rewrite d-e-cc-of-lofat-remove-file-disjoint)
     (entry-limit (max-entry-count fat32$c))
     (path (cdr path))
     (root-d-e
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path))))))))

(defthm
  lofat-unlink-refinement-lemma-7
  (implies
   (and
    (consp (cdr path))
    (lofat-fs-p fat32$c)
    (fat32-filename-list-p path)
    (equal (mv-nth 1
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))
           0)
    (no-duplicatesp-equal (mv-nth 0
                                  (d-e-cc fat32$c (pseudo-root-d-e fat32$c))))
    (not-intersectp-list
     (mv-nth 0
             (d-e-cc fat32$c (pseudo-root-d-e fat32$c)))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (max-entry-count fat32$c))))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (max-entry-count fat32$c)))
     0))
   (not-intersectp-list
    (mv-nth 0
            (d-e-cc fat32$c (pseudo-root-d-e fat32$c)))
    (mv-nth
     2
     (lofat-to-hifat-helper
      (mv-nth 0
              (lofat-remove-file fat32$c (pseudo-root-d-e fat32$c)
                                     path))
      (make-d-e-list
       (mv-nth 0
               (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
      (max-entry-count fat32$c)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable lofat-remove-file-correctness-lemma-1)
    :use (:instance lofat-remove-file-correctness-lemma-1
                    (root-d-e (pseudo-root-d-e fat32$c))
                    (x (mv-nth 0
                               (d-e-cc fat32$c (pseudo-root-d-e fat32$c))))
                    (entry-limit (max-entry-count fat32$c))))))

(encapsulate ()
  (local (include-book "std/lists/intersectp" :dir :system))

  (defthm
    lofat-unlink-refinement-lemma-6
    (implies
     (and
      (equal
       (mv-nth
        1
        (hifat-remove-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
           (max-entry-count fat32$c)))
         path))
       0)
      (equal
       (lofat-find-file
        fat32$c
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        path)
       (list
        (lofat-file
         (m1-file->d-e
          (mv-nth
           0
           (hifat-find-file
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (max-entry-count fat32$c)))
            path)))
         (m1-file->contents
          (mv-nth
           0
           (hifat-find-file
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (max-entry-count fat32$c)))
            path))))
        (mv-nth
         1
         (hifat-find-file
          (mv-nth
           0
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (max-entry-count fat32$c)))
          path))))
      (lofat-fs-p fat32$c)
      (fat32-filename-list-p path)
      (equal (mv-nth 1
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))
             0)
      (no-duplicatesp-equal (mv-nth 0
                                    (d-e-cc fat32$c (pseudo-root-d-e fat32$c))))
      (not-intersectp-list
       (mv-nth 0
               (d-e-cc fat32$c (pseudo-root-d-e fat32$c)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (max-entry-count fat32$c))))
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (max-entry-count fat32$c)))
       0)
      (m1-regular-file-p
       (mv-nth
        0
        (hifat-find-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
           (max-entry-count fat32$c)))
         path))))
     (no-duplicatesp-equal
      (mv-nth
       0
       (d-e-cc (mv-nth 0
                       (lofat-remove-file fat32$c (pseudo-root-d-e fat32$c)
                                              path))
               (pseudo-root-d-e fat32$c)))))
    :hints
    (("goal"
      :do-not-induct t
      :expand (lofat-remove-file fat32$c (pseudo-root-d-e fat32$c)
                                     path)
      :in-theory
      (e/d
       (lofat-remove-file lofat-remove-file-helper)
       ((:rewrite d-e-cc-contents-of-lofat-remove-file-coincident-lemma-6)))
      :use
      (:instance
       (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident-lemma-6)
       (d-e2 (pseudo-root-d-e fat32$c))
       (d-e1
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path))))
       (fat32$c
        (mv-nth
         0
         (update-dir-contents
          fat32$c
          (d-e-first-cluster (pseudo-root-d-e fat32$c))
          (nats=>string
           (clear-d-e
            (string=>nats
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (car path))))))))))

  (defthm
    lofat-unlink-refinement-lemma-14
    (implies
     (and
      (equal (mv-nth 1
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))
             0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (max-entry-count fat32$c)))
       0)
      (lofat-fs-p fat32$c)
      (fat32-filename-list-p path)
      (no-duplicatesp-equal (mv-nth 0
                                    (d-e-cc fat32$c (pseudo-root-d-e fat32$c))))
      (not-intersectp-list
       (mv-nth 0
               (d-e-cc fat32$c (pseudo-root-d-e fat32$c)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (max-entry-count fat32$c))))
      (not
       (d-e-directory-p
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path))))))
     (not-intersectp-list
      (mv-nth
       0
       (d-e-cc
        (mv-nth 0
                (lofat-remove-file-helper fat32$c (pseudo-root-d-e fat32$c)
                                          path))
        (pseudo-root-d-e fat32$c)))
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-remove-file-helper fat32$c (pseudo-root-d-e fat32$c)
                                          path))
        (delete-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (car path))
        (max-entry-count fat32$c)))))
    :hints (("goal" :do-not-induct t
             :in-theory (enable lofat-remove-file-helper))))

  (defthm
    lofat-unlink-refinement-lemma-15
    (implies
     (and
      (equal (mv-nth 1
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))
             0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (max-entry-count fat32$c)))
       0)
      (lofat-fs-p fat32$c)
      (fat32-filename-list-p path)
      (no-duplicatesp-equal (mv-nth 0
                                    (d-e-cc fat32$c (pseudo-root-d-e fat32$c))))
      (not-intersectp-list
       (mv-nth 0
               (d-e-cc fat32$c (pseudo-root-d-e fat32$c)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (max-entry-count fat32$c))))
      (not
       (d-e-directory-p
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path)))))
      (<
       (d-e-first-cluster
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path))))
       (+ 2 (count-of-clusters fat32$c))))
     (no-duplicatesp-equal
      (mv-nth
       0
       (d-e-cc
        (mv-nth 0
                (lofat-remove-file-helper fat32$c (pseudo-root-d-e fat32$c)
                                          path))
        (pseudo-root-d-e fat32$c)))))
    :hints (("goal" :do-not-induct t
             :in-theory (enable lofat-remove-file-helper))))

  (defthm
    lofat-unlink-refinement-lemma-16
    (implies
     (and
      (equal (mv-nth 1
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))
             0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (max-entry-count fat32$c)))
       0)
      (lofat-fs-p fat32$c)
      (fat32-filename-list-p path)
      (no-duplicatesp-equal (mv-nth 0
                                    (d-e-cc fat32$c (pseudo-root-d-e fat32$c))))
      (not-intersectp-list
       (mv-nth 0
               (d-e-cc fat32$c (pseudo-root-d-e fat32$c)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (max-entry-count fat32$c))))
      (<=
       (+ 2 (count-of-clusters fat32$c))
       (d-e-first-cluster
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path))))))
     (not-intersectp-list
      (mv-nth
       0
       (d-e-cc
        (mv-nth 0
                (lofat-remove-file-helper fat32$c (pseudo-root-d-e fat32$c)
                                          path))
        (pseudo-root-d-e fat32$c)))
      (mv-nth
       2
       (lofat-to-hifat-helper
        fat32$c
        (delete-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (car path))
        (max-entry-count fat32$c)))))
    :hints (("goal" :do-not-induct t
             :in-theory (enable lofat-remove-file-helper))))

  (defthm
    lofat-unlink-refinement-lemma-17
    (implies
     (and
      (equal (mv-nth 1
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))
             0)
      (lofat-fs-p fat32$c)
      (fat32-filename-list-p path)
      (no-duplicatesp-equal (mv-nth 0
                                    (d-e-cc fat32$c (pseudo-root-d-e fat32$c))))
      (<=
       (+ 2 (count-of-clusters fat32$c))
       (d-e-first-cluster
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path))))))
     (no-duplicatesp-equal
      (mv-nth
       0
       (d-e-cc
        (mv-nth 0
                (lofat-remove-file-helper fat32$c (pseudo-root-d-e fat32$c)
                                          path))
        (pseudo-root-d-e fat32$c)))))
    :hints (("goal" :do-not-induct t
             :in-theory (enable lofat-remove-file-helper)))))

(defthm
  lofat-unlink-refinement-lemma-11
  (implies
   (and
    (<
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (car path))))
     2)
    (lofat-fs-p fat32$c)
    (fat32-filename-list-p path)
    (equal (mv-nth 1
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))
           0)
    (no-duplicatesp-equal (mv-nth 0
                                  (d-e-cc fat32$c (pseudo-root-d-e fat32$c))))
    (not-intersectp-list
     (mv-nth 0
             (d-e-cc fat32$c (pseudo-root-d-e fat32$c)))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (max-entry-count fat32$c))))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (max-entry-count fat32$c)))
     0))
   (not-intersectp-list
    (mv-nth
     0
     (d-e-cc
      (mv-nth 0
              (lofat-remove-file-helper fat32$c (pseudo-root-d-e fat32$c)
                                        path))
      (pseudo-root-d-e fat32$c)))
    (mv-nth
     2
     (lofat-to-hifat-helper
      fat32$c
      (delete-d-e
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (car path))
      (max-entry-count fat32$c)))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

(defthm
  lofat-unlink-refinement-lemma-12
  (implies
   (and
    (equal (mv-nth 1
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))
           0)
    (lofat-fs-p fat32$c)
    (fat32-filename-list-p path)
    (no-duplicatesp-equal (mv-nth 0
                                  (d-e-cc fat32$c (pseudo-root-d-e fat32$c))))
    (<
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (car path))))
     2))
   (no-duplicatesp-equal
    (mv-nth
     0
     (d-e-cc
      (mv-nth 0
              (lofat-remove-file-helper fat32$c (pseudo-root-d-e fat32$c)
                                        path))
      (pseudo-root-d-e fat32$c)))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

(defthm
  lofat-unlink-refinement-lemma-13
  (implies
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (max-entry-count fat32$c)))
     0)
    (lofat-fs-p fat32$c)
    (fat32-filename-list-p path)
    (not-intersectp-list
     (mv-nth 0
             (d-e-cc fat32$c (pseudo-root-d-e fat32$c)))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (max-entry-count fat32$c))))
    (equal
     (mv-nth
      1
      (find-d-e
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (car path)))
     0)
    (not
     (d-e-directory-p
      (mv-nth
       0
       (find-d-e
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (car path)))))
    (<
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (car path))))
     (+ 2 (count-of-clusters fat32$c))))
   (equal
    (mv-nth
     3
     (lofat-to-hifat-helper
      (mv-nth 0
              (lofat-remove-file-helper fat32$c (pseudo-root-d-e fat32$c)
                                        path))
      (delete-d-e
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (car path))
      (max-entry-count fat32$c)))
    0))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

(defthm
  lofat-unlink-refinement-lemma-18
  (implies
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (max-entry-count fat32$c)))
     0)
    (not (consp (cdr path)))
    (consp path)
    (fat32-filename-list-p path)
    (equal
     (mv-nth
      1
      (find-d-e
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (car path)))
     0)
    (<
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (car path))))
     2))
   (m1-regular-file-p
    (mv-nth
     0
     (hifat-find-file
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (max-entry-count fat32$c)))
      path))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (hifat-find-file)
                           ((:rewrite abs-pwrite-correctness-lemma-37))))))

(defthm
  lofat-unlink-refinement-lemma-19
  (implies
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (max-entry-count fat32$c)))
     0)
    (not (consp (cdr path)))
    (fat32-filename-list-p path)
    (d-e-directory-p
     (mv-nth
      0
      (find-d-e
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (car path)))))
   (not
    (m1-regular-file-p
     (mv-nth
      0
      (hifat-find-file
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (max-entry-count fat32$c)))
       path)))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (hifat-find-file)
                           ((:rewrite abs-pwrite-correctness-lemma-37))))))

(defthm
  lofat-unlink-refinement-lemma-20
  (implies
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (max-entry-count fat32$c)))
     0)
    (not (consp (cdr path)))
    (consp path)
    (lofat-fs-p fat32$c)
    (fat32-filename-list-p path)
    (not
     (d-e-directory-p
      (mv-nth
       0
       (find-d-e
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (car path)))))
    (<=
     2
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (car path)))))
    (<
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (car path))))
     (+ 2 (count-of-clusters fat32$c))))
   (m1-regular-file-p
    (mv-nth
     0
     (hifat-find-file
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (max-entry-count fat32$c)))
      path))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (hifat-find-file)
                           ((:rewrite abs-pwrite-correctness-lemma-37))))))

(defthm
  lofat-unlink-refinement-lemma-21
  (implies
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (max-entry-count fat32$c)))
     0)
    (not (consp (cdr path)))
    (consp path)
    (fat32-filename-list-p path)
    (equal
     (mv-nth
      1
      (find-d-e
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (car path)))
     0)
    (<=
     (+ 2 (count-of-clusters fat32$c))
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (car path))))))
   (m1-regular-file-p
    (mv-nth
     0
     (hifat-find-file
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (max-entry-count fat32$c)))
      path))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (hifat-find-file)
                           ((:rewrite abs-pwrite-correctness-lemma-37))))))

(encapsulate
  ()

  (local
   (in-theory
    (e/d
     (lofat-unlink
      lofat-to-hifat root-d-e-list
      update-dir-contents-correctness-1)
     ((:rewrite lofat-remove-file-correctness-1)
      (:rewrite lofat-find-file-correctness-1)
      (:rewrite
       d-e-cc-contents-of-lofat-place-file-coincident-lemma-15)
      (:linear
       d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-12)))))

  (defthm
    lofat-unlink-refinement
    (implies
     (and (lofat-fs-p fat32$c)
          (fat32-filename-list-p path)
          (equal (mv-nth 1 (lofat-to-hifat fat32$c))
                 0))
     (and
      (equal
       (mv-nth
        1
        (lofat-to-hifat (mv-nth 0 (lofat-unlink fat32$c path))))
       0)
      (equal
       (mv-nth
        0
        (lofat-to-hifat (mv-nth 0 (lofat-unlink fat32$c path))))
       (mv-nth 0
               (hifat-unlink (mv-nth 0 (lofat-to-hifat fat32$c))
                             path)))
      (equal
       (mv-nth 1 (lofat-unlink fat32$c path))
       (mv-nth 1
               (hifat-unlink (mv-nth 0 (lofat-to-hifat fat32$c))
                             path)))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d (lofat-remove-file)
           ((:rewrite d-e-cc-of-update-dir-contents-coincident)
            (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident)))
      :use
      ((:instance (:rewrite lofat-remove-file-correctness-1)
                  (entry-limit (max-entry-count fat32$c))
                  (path path)
                  (root-d-e (pseudo-root-d-e fat32$c))
                  (fat32$c fat32$c))
       (:instance
        (:rewrite lofat-find-file-correctness-1)
        (d-e-list
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))))
        (entry-limit (max-entry-count fat32$c)))
       (:instance
        (:rewrite lofat-unlink-refinement-lemma-3)
        (fs
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents
                     fat32$c (pseudo-root-d-e fat32$c))))
           (max-entry-count fat32$c)))))
       (:instance
        (:rewrite lofat-unlink-refinement-lemma-2)
        (fs
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents
                     fat32$c (pseudo-root-d-e fat32$c))))
           (max-entry-count fat32$c)))))
       (:instance
        lofat-unlink-refinement-lemma-8
        (fs
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents
                     fat32$c (pseudo-root-d-e fat32$c))))
           (max-entry-count fat32$c))))) (:instance
        (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident) (path path)
        (d-e (pseudo-root-d-e fat32$c))
        (fat32$c fat32$c) (entry-limit (max-entry-count fat32$c))))))))

;; This one needs some work.
(defund lofat-rmdir (fat32$c path)
  (declare (xargs :stobjs fat32$c
                  :guard (and (lofat-fs-p fat32$c)
                              (fat32-filename-list-p path))))
  (b*
      (((mv fs error-code) (lofat-to-hifat fat32$c))
       ((unless (equal error-code 0)) (mv fat32$c *eio*))
       ((mv fs & error-code) (hifat-rmdir fs path))
       ((mv fat32$c &) (hifat-to-lofat fat32$c fs)))
    (mv fat32$c error-code)))

(defund lofat-truncate (fat32$c path size)
  (declare (xargs :stobjs fat32$c
                  :guard (and (lofat-fs-p fat32$c)
                              (fat32-filename-list-p path)
                              (natp size))))
  (b*
      (((unless (unsigned-byte-p 32 size))
        (mv fat32$c -1 *enospc*))
       ((mv root-d-e-list &)
        (root-d-e-list fat32$c))
       ((mv file error-code)
        (lofat-find-file fat32$c root-d-e-list path))
       ((when (and (equal error-code 0)
                   (lofat-directory-file-p file)))
        ;; Can't truncate a directory file.
        (mv fat32$c -1 *eisdir*))
       ((mv oldtext d-e)
        (if (equal error-code 0)
            ;; Regular file
            (mv (coerce (lofat-file->contents file) 'list)
                (lofat-file->d-e file))
          ;; Nonexistent file
          (mv nil (d-e-fix nil))))
       (file
        (make-lofat-file
         :d-e d-e
         :contents (coerce (make-character-list
                            (take size oldtext))
                           'string)))
       ((mv fat32$c error-code)
        (lofat-place-file fat32$c (pseudo-root-d-e fat32$c) path file)))
    (mv fat32$c (if (equal error-code 0) 0 -1)
        error-code)))

(defthm lofat-fs-p-of-lofat-truncate
  (implies
   (lofat-fs-p fat32$c)
   (lofat-fs-p (mv-nth 0 (lofat-truncate fat32$c path size))))
  :hints (("Goal" :in-theory (enable lofat-truncate)) ))

(defun lofat-statfs (fat32$c)
  (declare (xargs :stobjs (fat32$c)
                  :guard (lofat-fs-p fat32$c)))
  (b*
      ((total_blocks (count-of-clusters fat32$c))
       (available_blocks
        (len (stobj-find-n-free-clusters
              fat32$c
              (count-of-clusters fat32$c)))))
    (make-struct-statfs
     :f_type *S_MAGIC_FUSEBLK*
     :f_bsize (cluster-size fat32$c)
     :f_blocks total_blocks
     :f_bfree available_blocks
     :f_bavail available_blocks
     :f_files 0
     :f_ffree 0
     :f_fsid 0
     :f_namelen 72)))

(defund lofat-close (fd fd-table file-table)
  (declare (xargs :guard (and (fd-table-p fd-table)
                              (file-table-p file-table))))
  (hifat-close fd fd-table file-table))

(defthm dir-stream-table-p-correctness-1
  (implies (dir-stream-table-p dir-stream-table)
           (nat-listp (strip-cars dir-stream-table))))

;; Not sure how to define this! But I definitely do want a property of the
;; output satisfying fat32-filename-list-p.
(defund names-from-d-e-list (d-e-list)
  (declare (xargs :guard (d-e-list-p d-e-list)
                  :measure (len d-e-list)))
  (b*
      ((d-e-list (mbe :exec d-e-list :logic (d-e-list-fix d-e-list)))
       ((when (atom d-e-list)) nil)
       ((unless (fat32-filename-p (d-e-filename (car d-e-list))))
        (names-from-d-e-list (cdr d-e-list))))
    (cons (d-e-filename (car d-e-list))
          (names-from-d-e-list (cdr d-e-list)))))

(defthm fat32-filename-list-p-of-names-from-d-e-list
  (fat32-filename-list-p (names-from-d-e-list d-e-list))
  :hints (("goal" :in-theory (enable names-from-d-e-list))))

;; The dir-stream-table has to be returned, since it is potentially changed.
(defund lofat-opendir (fat32$c dir-stream-table path)
  (declare (xargs :stobjs fat32$c
                  :guard (and (lofat-fs-p fat32$c)
                              (dir-stream-table-p dir-stream-table)
                              (fat32-filename-list-p path))
                  :guard-debug t
                  :guard-hints
                  (("Goal"
                    :in-theory (enable alistp-when-m1-file-alist-p-rewrite)))))
  (b*
      ((dir-stream-table (mbe :exec dir-stream-table
                             :logic (dir-stream-table-fix dir-stream-table)))
       ((mv root-d-e-list &) (root-d-e-list fat32$c))
       ((mv file error-code)
        (lofat-find-file fat32$c root-d-e-list path))
       ;; There was a bug here - previously we returned the error code as is,
       ;; but the man page opendir(3) says ENOENT is the right error code
       ;; regardless of the reason for the directory not being found.
       ((unless (zp error-code)) (mv dir-stream-table -1 *enoent*))
       ((unless (lofat-directory-file-p file)) (mv dir-stream-table -1 *ENOTDIR*))
       (dir-stream-table-index
        (find-new-index (strip-cars dir-stream-table))))
    (mv
     (cons
      (cons dir-stream-table-index
            (make-dir-stream
             :file-list
             (<<-sort
              (names-from-d-e-list (lofat-file->contents file)))))
      dir-stream-table)
     dir-stream-table-index
     0)))

(defthm lofat-opendir-correctness-1
  (and
   (dir-stream-table-p (mv-nth 0
                              (lofat-opendir fat32$c dir-stream-table path)))
   (integerp (mv-nth 1
                     (lofat-opendir fat32$c dir-stream-table path)))
   (integerp (mv-nth 2
                     (lofat-opendir fat32$c dir-stream-table path))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-opendir)))
  :rule-classes
  ((:rewrite :corollary
             (dir-stream-table-p (mv-nth 0
                                        (lofat-opendir fat32$c dir-stream-table path))))
   (:type-prescription
    :corollary
    (integerp (mv-nth 1
                      (lofat-opendir fat32$c dir-stream-table path))))
   (:type-prescription
    :corollary
    (integerp (mv-nth 2
                      (lofat-opendir fat32$c dir-stream-table path))))))

(defthm
  lofat-opendir-correctness-lemma-1
  (implies
   (and (useful-d-e-list-p d-e-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               0))
   (equal
    (lofat-directory-file-p (mv-nth 0
                                    (lofat-find-file fat32$c d-e-list path)))
    (m1-directory-file-p
     (mv-nth
      0
      (hifat-find-file
       (mv-nth 0
               (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
       path)))))
  :hints (("goal" :induct (lofat-find-file fat32$c d-e-list path)
           :in-theory (enable lofat-find-file hifat-find-file))))

(defthmd
  lofat-opendir-correctness-2
  (implies (equal (mv-nth 1 (lofat-to-hifat fat32$c))
                  0)
           (and
            (equal (mv-nth 1
                           (lofat-opendir fat32$c dir-stream-table path))
                   (mv-nth 0
                           (hifat-opendir (mv-nth 0 (lofat-to-hifat fat32$c))
                                          path dir-stream-table)))
            (equal (mv-nth 2
                           (lofat-opendir fat32$c dir-stream-table path))
                   (mv-nth 2
                           (hifat-opendir (mv-nth 0 (lofat-to-hifat fat32$c))
                                          path dir-stream-table)))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (lofat-opendir hifat-opendir lofat-to-hifat)
                           (lofat-pread-refinement-lemma-2)))))

(defthm
  lofat-opendir-correctness-lemma-2
  (implies
   (and (useful-d-e-list-p d-e-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               0))
   (equal
    (strip-cars (mv-nth 0
                        (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
    (names-from-d-e-list d-e-list)))
  :hints (("goal" :in-theory (enable lofat-to-hifat-helper
                                     names-from-d-e-list))))

(defthm
  lofat-opendir-correctness-lemma-3
  (implies
   (and
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c
                                          (mv-nth 0 (root-d-e-list fat32$c))
                                          (max-entry-count fat32$c)))
           0)
    (lofat-fs-p fat32$c)
    (m1-directory-file-p
     (mv-nth
      0
      (hifat-find-file
       (mv-nth 0
               (lofat-to-hifat-helper fat32$c
                                      (mv-nth 0 (root-d-e-list fat32$c))
                                      (max-entry-count fat32$c)))
       path))))
   (equal
    (<<-sort
     (strip-cars
      (m1-file->contents
       (mv-nth
        0
        (hifat-find-file
         (mv-nth 0
                 (lofat-to-hifat-helper fat32$c
                                        (mv-nth 0 (root-d-e-list fat32$c))
                                        (max-entry-count fat32$c)))
         path)))))
    (<<-sort
     (names-from-d-e-list
      (lofat-file->contents
       (mv-nth 0
               (lofat-find-file fat32$c
                                (mv-nth 0 (root-d-e-list fat32$c))
                                path)))))))
  :hints
  (("goal" :do-not-induct t
    :in-theory (disable (:rewrite lofat-find-file-correctness-2)
                        lofat-pread-refinement-lemma-2)
    :use (:instance (:rewrite lofat-find-file-correctness-2)
                    (entry-limit (max-entry-count fat32$c))
                    (path path)
                    (d-e-list (mv-nth 0 (root-d-e-list fat32$c)))
                    (fat32$c fat32$c)))))

(defthmd
  lofat-opendir-correctness-3
  (implies (and (equal (mv-nth 1 (lofat-to-hifat fat32$c))
                       0)
                (lofat-fs-p fat32$c))
           (equal (mv-nth 0
                          (lofat-opendir fat32$c dir-stream-table path))
                  (mv-nth 1
                          (hifat-opendir (mv-nth 0 (lofat-to-hifat fat32$c))
                                         path dir-stream-table))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (lofat-opendir hifat-opendir lofat-to-hifat)
                           (lofat-pread-refinement-lemma-2)))))
