(in-package "ACL2")

;  hifat-syscalls.lisp                                 Mihir Mehta

; Syscalls for HiFAT. These syscalls usually return, among other things, a
; return value (corresponding to the C return value) and an errno.

(include-book "utilities/insert-text")
(include-book "hifat/hifat-equiv")

;; This implementation of basename+dirname is not exactly compliant with the
;; man pages basename(3)/dirname(3) - it assumes all paths provided to it are
;; absolute paths (thus, the empty path is treated like "/"), and further
;; it expects its argument to be a list of FAT32 names, which means there is
;; not much hope for formulating a particularly coherent relation between this
;; and the friendly command line programs basename(1)/dirname(1).

;; From the common man page basename(3)/dirname(3):
;; --
;; If  path  does  not contain a slash, dirname() returns the string "." while
;; basename() returns a copy of path.  If path is the string  "/",  then  both
;; dirname()  and basename() return the string "/".  If path is a NULL pointer
;; or points to an empty string, then both dirname() and basename() return the
;; string ".".
;; --
;; Of course, an empty list means something went wrong with the parsing code,
;; because even in the case of an empty path string, (list "") should be passed
;; to these functions. Still, we do the default thing, because neither of these
;; functions sets errno.

;; Also, an empty string right in the beginning indicates that the path began
;; with a "/". While not documented properly in the man page, for a path such
;; as "/home" or "/tmp", the dirname will be "/".

(defund dirname (path)
  (declare (xargs :guard (fat32-filename-list-p path)))
  (fat32-filename-list-fix (butlast path 1)))

(defthm fat32-filename-list-p-of-dirname
  (fat32-filename-list-p (dirname path))
  :hints (("goal" :in-theory (enable dirname))))

(defcong
  fat32-filename-list-equiv equal
  (dirname path)
  1
  :hints
  (("goal" :in-theory (enable dirname))))

(defthm len-of-dirname
  (equal (len (dirname path))
         (nfix (- (len path) 1)))
  :hints (("goal" :in-theory (enable dirname))))

(defthm consp-of-dirname
  (equal (consp (dirname path))
         (consp (cdr path)))
  :hints (("goal" :in-theory (enable dirname)
           :expand ((len (cdr path)) (len path)))))

(defund basename (path)
  (declare (xargs :guard (fat32-filename-list-p path)
                  :guard-debug t))
  (mbe :logic (fat32-filename-fix (car (last path)))
       :exec (if (consp path)
                 (fat32-filename-fix (car (last path)))
                 *empty-fat32-name*)))

(defthm fat32-filename-p-of-basename
  (fat32-filename-p (basename path))
  :hints (("goal" :in-theory (enable basename))))

(defcong
  fat32-filename-list-equiv equal
  (basename path)
  1
  :hints
  (("goal" :in-theory (enable basename))))

(defthm
  append-nthcdr-dirname-basename-lemma-1
  (implies (consp path)
           (equal (append (dirname path)
                          (list (basename path)))
                  (fat32-filename-list-fix path)))
  :hints (("goal" :in-theory (enable dirname basename fat32-filename-list-fix
                                     fat32-filename-list-equiv)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary (iff (fat32-filename-list-equiv (dirname path)
                                               path)
                    (atom path))
    :hints
    (("goal" :in-theory (e/d (basename dirname fat32-filename-list-equiv
                                       fat32-filename-list-fix)
                             (len-of-dirname))
      :use len-of-dirname)))
   (:rewrite
    :corollary (implies (and (consp path)
                             (nat-equiv n (len (dirname path))))
                        (fat32-filename-list-equiv (nthcdr n path)
                                                   (list (basename path))))
    :hints
    (("goal" :in-theory (e/d (basename dirname fat32-filename-list-equiv
                                       fat32-filename-list-fix)
                             nil))))))

(defthm
  append-nthcdr-dirname-basename
  (implies (and (consp path)
                (<= (nfix n) (len (dirname path))))
           (equal (append (nthcdr n (dirname path))
                          (list (basename path)))
                  (fat32-filename-list-fix (nthcdr n path))))
  :hints (("goal" :in-theory (disable (:rewrite nthcdr-of-append))
           :use (:instance (:rewrite nthcdr-of-append)
                           (b (list (basename path)))
                           (a (dirname path))
                           (n n)))))

(defthm
  abs-pwrite-correctness-lemma-37
  (implies (and (fat32-filename-list-p path)
                (consp path)
                (not (consp (cdr path))))
           (equal (assoc-equal (car path) fs)
                  (assoc-equal (basename path) fs)))
  :hints (("goal" :in-theory (enable basename)
           :do-not-induct t)))

(defund hifat-lstat (fs path)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (hifat-no-dups-p fs)
                              (fat32-filename-list-p path))))
  (b*
      (((mv file errno)
        (hifat-find-file fs path))
       ((when (not (equal errno 0)))
        (mv (make-struct-stat) -1 errno))
       (st_size (if (m1-directory-file-p file)
                    *ms-max-dir-size*
                  (length (m1-file->contents file)))))
    (mv
     (make-struct-stat
      :st_size st_size)
     0 0)))

(defthm struct-stat-p-of-hifat-lstat
  (struct-stat-p (mv-nth 0 (hifat-lstat fs path)))
  :hints (("goal" :in-theory (enable hifat-lstat))))

(defthm
  hifat-lstat-correctness-3
  (and (integerp (mv-nth 1 (hifat-lstat fs path)))
       (natp (mv-nth 2 (hifat-lstat fs path))))
  :hints (("Goal" :in-theory (enable hifat-lstat)))
  :rule-classes
  ((:type-prescription :corollary (integerp (mv-nth 1 (hifat-lstat fs path))))
   (:type-prescription :corollary (natp (mv-nth 2 (hifat-lstat fs path))))))

;; By default, we aren't going to check whether the file exists.
(defund hifat-open (path fd-table file-table)
  (declare (xargs :guard (and (fat32-filename-list-p path)
                              (fd-table-p fd-table)
                              (file-table-p file-table))))
  (b*
      ((fd-table (mbe :logic (fd-table-fix fd-table) :exec fd-table))
       (file-table (mbe :logic (file-table-fix file-table) :exec file-table))
       (file-table-index
        (find-new-index (strip-cars file-table)))
       (fd-table-index
        (find-new-index (strip-cars fd-table))))
    (mv
     (cons
      (cons fd-table-index file-table-index)
      fd-table)
     (cons
      (cons file-table-index (make-file-table-element :pos 0 :fid path))
      file-table)
     fd-table-index 0)))

(defthm hifat-open-correctness-1
  (b*
      (((mv fd-table file-table fd &) (hifat-open path fd-table file-table)))
    (and
     (fd-table-p fd-table)
     (file-table-p file-table)
     (integerp fd)))
  :rule-classes
  ((:rewrite
    :corollary
    (b*
        (((mv fd-table file-table & &) (hifat-open path fd-table file-table)))
      (and
       (fd-table-p fd-table)
       (file-table-p file-table))))
   (:type-prescription
    :corollary
    (b*
        (((mv & & fd &) (hifat-open path fd-table file-table)))
      (integerp fd))))
  :hints (("Goal" :in-theory (enable hifat-open))))

(defthm
  hifat-open-correctness-2
  (implies (no-duplicatesp (strip-cars (fd-table-fix fd-table)))
           (b* (((mv fd-table & & &)
                 (hifat-open path fd-table file-table)))
             (no-duplicatesp (strip-cars fd-table))))
  :hints (("Goal" :in-theory (enable hifat-open))))

(defthm
  hifat-open-correctness-3
  (implies
   (no-duplicatesp (strip-cars (file-table-fix file-table)))
   (b* (((mv & file-table & &)
         (hifat-open path fd-table file-table)))
     (no-duplicatesp (strip-cars file-table))))
  :hints (("Goal" :in-theory (enable hifat-open))))

(defthm hifat-open-correctness-4
  (and
   (natp (mv-nth 2
                 (hifat-open path fd-table file-table)))
   (natp (mv-nth 3
                 (hifat-open path fd-table file-table))))
  :hints (("goal" :in-theory (enable hifat-open)))
  :rule-classes
  ((:type-prescription :corollary
                       (natp (mv-nth 2
                                     (hifat-open path fd-table file-table))))
   (:type-prescription :corollary
                       (natp (mv-nth 3
                                     (hifat-open path fd-table file-table))))))

;; Per the man page pread(2), this should not change the offset of the file
;; descriptor in the file table. Thus, there's no need for the file table to be
;; an argument.
(defund
    hifat-pread
    (fd count offset fs fd-table file-table)
  (declare (xargs :guard (and (natp fd)
                              (natp count)
                              (natp offset)
                              (fd-table-p fd-table)
                              (file-table-p file-table)
                              (m1-file-alist-p fs)
                              (hifat-no-dups-p fs))))
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
       ((mv file error-code)
        (hifat-find-file fs path))
       ((unless (m1-regular-file-p file))
        (mv "" -1 *EISDIR*))
       ((unless (equal error-code 0))
        (mv "" -1 error-code))
       (new-offset (min (+ offset count)
                        (length (m1-file->contents file))))
       (buf (subseq (m1-file->contents file)
                    (min offset
                         (length (m1-file->contents file)))
                    new-offset)))
    (mv buf (length buf) 0)))

(defthm
  hifat-pread-correctness-1
  (mv-let (buf ret error-code)
    (hifat-pread fd count offset fs fd-table file-table)
    (and (stringp buf)
         (integerp ret)
         (integerp error-code)
         (implies (>= ret 0)
                  (equal (length buf) ret))))
  :hints (("Goal" :in-theory (enable hifat-pread))))

(defthm
  natp-of-hifat-pread
  (natp
   (mv-nth 2
           (hifat-pread fd count offset fs fd-table file-table)))
  :hints (("goal" :in-theory (enable hifat-pread)))
  :rule-classes :type-prescription)

(defcong
  fd-table-equiv equal (hifat-pread fd count offset fs fd-table file-table) 5
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-pread))))

(defcong
  file-table-equiv equal (hifat-pread fd count offset fs fd-table file-table) 6
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-pread))))

(defcong hifat-equiv equal
  (hifat-pread fd count offset fs fd-table file-table)
  4
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-pread))))

(defun
    hifat-pwrite
    (fd buf offset fs fd-table file-table)
  (declare (xargs :guard (and (natp fd)
                              (stringp buf)
                              (natp offset)
                              (fd-table-p fd-table)
                              (file-table-p file-table)
                              (m1-file-alist-p fs)
                              (hifat-no-dups-p fs))
                  :guard-hints (("goal" :in-theory
                                 (e/d (len-of-insert-text)
                                      (unsigned-byte-p
                                       consp-assoc-equal))
                                 :use (:instance consp-assoc-equal
                                                 (name (cdr (car fd-table)))
                                                 (l
                                                  file-table))))))
  (b*
      ((fd-table-entry (assoc-equal fd fd-table))
       ((unless (consp fd-table-entry))
        (mv fs -1 *ebadf*))
       (file-table-entry (assoc-equal (cdr fd-table-entry)
                                      file-table))
       ((unless (consp file-table-entry))
        (mv fs -1 *ebadf*))
       (path (file-table-element->fid (cdr file-table-entry)))
       ((mv file error-code)
        (hifat-find-file fs path))
       ((mv oldtext d-e)
        (if (and (equal error-code 0)
                 (m1-regular-file-p file))
            (mv (coerce (m1-file->contents file) 'list)
                (m1-file->d-e file))
          (mv nil (d-e-fix nil))))
       ((unless (unsigned-byte-p 32 (+ offset (length buf))))
        (mv fs -1 *enospc*))
       (file
        (make-m1-file
         :d-e d-e
         :contents (coerce (insert-text oldtext offset buf)
                           'string)))
       ((mv fs error-code)
        (hifat-place-file fs path file)))
    (mv fs (if (equal error-code 0) 0 -1)
        error-code)))

(defthm hifat-pwrite-correctness-1
 (implies
  (hifat-equiv fs1 fs2)
  (hifat-equiv
   (mv-nth 0
           (hifat-pwrite fd buf offset fs1 fd-table file-table))
   (mv-nth 0
           (hifat-pwrite fd buf offset fs2 fd-table file-table))))
 :hints (("Goal" :do-not-induct t
          :in-theory (enable hifat-no-dups-p)))
 :rule-classes :congruence)

(defthm
  hifat-pwrite-correctness-2
  (implies
   (hifat-equiv fs1 fs2)
   (equal
    (mv-nth
     1
     (hifat-pwrite fd buf offset fs1 fd-table file-table))
    (mv-nth 1
            (hifat-pwrite fd
                          buf offset fs2 fd-table file-table))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-no-dups-p)))
  :rule-classes :congruence)

(defthm
  hifat-pwrite-correctness-3
  (and
   (integerp
    (mv-nth
     1
     (hifat-pwrite fd buf offset fs1 fd-table file-table)))
   (natp
    (mv-nth
     2
     (hifat-pwrite fd buf offset fs1 fd-table file-table))))
  :rule-classes
  ((:type-prescription
    :corollary
    (integerp
     (mv-nth
      1
      (hifat-pwrite fd buf offset fs1 fd-table file-table))))
   (:type-prescription
    :corollary
    (natp
     (mv-nth
      2
      (hifat-pwrite fd buf offset fs1 fd-table file-table))))))

(defthm
  hifat-pwrite-correctness-4
  (implies
   (hifat-equiv fs1 fs2)
   (equal
    (mv-nth
     2
     (hifat-pwrite fd buf offset fs1 fd-table file-table))
    (mv-nth 2
            (hifat-pwrite fd
                          buf offset fs2 fd-table file-table))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-no-dups-p)))
  :rule-classes :congruence)

(defun
    hifat-mkdir (fs path)
  (declare
   (xargs
    :guard (and (m1-file-alist-p fs)
                (hifat-no-dups-p fs)
                (fat32-filename-list-p path))))
  (b* ((dirname (dirname path))
       ;; Never pass relative paths to syscalls - make them always begin
       ;; with "/".
       ((mv parent-dir errno)
        (hifat-find-file fs dirname))
       ((unless (or (atom dirname)
                    (and (equal errno 0)
                         (m1-directory-file-p parent-dir))))
        (mv fs -1 *enoent*))
       ((mv & errno)
        (hifat-find-file fs path))
       ((when (equal errno 0))
        (mv fs -1 *eexist*))
       (basename (basename path))
       ((unless (equal (length basename) 11))
        (mv fs -1 *enametoolong*))
       (d-e
        (d-e-install-directory-bit
         (d-e-fix nil)
         t))
       (file (make-m1-file :d-e d-e
                           :contents nil))
       ((mv fs error-code)
        (hifat-place-file fs path file))
       ((unless (equal error-code 0))
        (mv fs -1 error-code)))
    (mv fs 0 0)))

(defthm
  hifat-mkdir-correctness-1
  (implies (hifat-equiv fs1 fs2)
           (hifat-equiv (mv-nth 0 (hifat-mkdir fs1 path))
                        (mv-nth 0 (hifat-mkdir fs2 path))))
  :rule-classes
  :congruence)

(defthm
  hifat-mkdir-correctness-2
  (implies
   (hifat-equiv fs1 fs2)
   (equal
    (mv-nth
     1
     (hifat-mkdir fs1 path))
    (mv-nth 1
            (hifat-mkdir fs2 path))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-no-dups-p)))
  :rule-classes :congruence)

(defthm
  hifat-mkdir-correctness-3
  (and (integerp (mv-nth 1 (hifat-mkdir fs path)))
       (natp (mv-nth 2 (hifat-mkdir fs path))))
  :rule-classes
  ((:type-prescription :corollary (integerp (mv-nth 1 (hifat-mkdir fs path))))
   (:type-prescription
    :corollary (natp (mv-nth 2 (hifat-mkdir fs path))))))

(defthm
  hifat-mkdir-correctness-4
  (implies
   (hifat-equiv fs1 fs2)
   (equal
    (mv-nth
     2
     (hifat-mkdir fs1 path))
    (mv-nth 2
            (hifat-mkdir fs2 path))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-no-dups-p)))
  :rule-classes :congruence)

(defun
    hifat-mknod (fs path)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (hifat-no-dups-p fs)
                              (fat32-filename-list-p path))))
  (b* ((dirname (dirname path))
       (basename (basename path))
       ((mv parent-dir errno)
        (hifat-find-file fs dirname))
       ((unless (or (atom dirname)
                    (and (equal errno 0)
                         (m1-directory-file-p parent-dir))))
        (mv fs -1 *enoent*))
       ((mv & errno)
        (hifat-find-file fs path))
       ((unless (not (equal errno 0)))
        (mv fs -1 *eexist*))
       ((unless (equal (length basename) 11))
        (mv fs -1 *enametoolong*))
       (d-e (d-e-set-filename (d-e-fix nil)
                                      basename))
       (file (make-m1-file :d-e d-e
                           :contents ""))
       ((mv fs error-code)
        (hifat-place-file fs path file))
       ((unless (equal error-code 0))
        (mv fs -1 error-code)))
    (mv fs 0 0)))

;; The fat driver in Linux actually keeps the directory entries of files it is
;; deleting, while removing links to their contents. Thus, in the special case
;; where the last file is deleted from the root directory, the root directory
;; will still occupy one cluster, which in turn contains one entry which
;; points to the deleted file, with the filename's first character changed to
;; #xe5, which signifies a deleted file, its file length changed to 0, and
;; the first cluster changed to 0. This may even hold for other directories
;; than root.

;; This may be a place where co-simulation of statfs may have to be
;; compromised... because, now, we delete the file from our tree representation
;; and as a result we have a little more extra space than an implementation
;; which simply marks the file as removed. The way forward, I think, is to
;; delete the file from the tree, and make an m2-unlink that provably does the
;; same thing as hifat-unlink while actually just marking files as deleted.
(defun
    hifat-unlink (fs path)
  (declare
   (xargs
    :guard (and (m1-file-alist-p fs)
                (hifat-no-dups-p fs)
                (fat32-filename-list-p path))))
  (b* (((mv file error-code)
        (hifat-find-file fs path))
       ((unless (equal error-code 0)) (mv fs -1 *ENOENT*))
       ((unless (m1-regular-file-p file)) (mv fs -1 *EISDIR*))
       ((mv fs error-code)
        (hifat-remove-file fs path))
       ((unless (equal error-code 0))
        (mv fs -1 error-code)))
    (mv fs 0 0)))

;; This is rather ad hoc - there is no such system call that I'm exactly aware
;; of, but for now it beats making a recursive function at the application
;; level.

;; This may be a place where co-simulation of statfs has to be
;; compromised... because, now, we delete the file from our tree representation
;; and as a result we have a little more extra space than an implementation
;; which simply marks the file as removed. The way forward, I think, is to
;; delete the file from the tree, and make an m2-unlink that provably does the
;; same thing as hifat-unlink while actually just marking files as deleted.
(defun
    hifat-unlink-recursive (fs path)
  (declare
   (xargs
    :guard (and (m1-file-alist-p fs)
                (hifat-no-dups-p fs)
                (fat32-filename-list-p path))))
  (b* (((mv file error-code)
        (hifat-find-file fs path))
       ((unless (equal error-code 0)) (mv fs -1 *ENOENT*))
       ((unless (m1-directory-file-p file)) (mv fs -1 *ENOTDIR*))
       ((mv fs error-code)
        (hifat-remove-file fs path))
       ((unless (equal error-code 0))
        (mv fs -1 error-code)))
    (mv fs 0 0)))

;; This may be a place where co-simulation of statfs may have to be
;; compromised... because, now, we delete the file from our tree representation
;; and as a result we have a little more extra space than an implementation
;; which simply marks the file as removed. The way forward, I think, is to
;; delete the file from the tree, and make an m2-unlink that provably does the
;; same thing as hifat-unlink while actually just marking files as deleted.
(defun
    hifat-rmdir (fs path)
  (declare
   (xargs
    :guard (and (m1-file-alist-p fs)
                (hifat-no-dups-p fs)
                (fat32-filename-list-p path))))
  (b* (((mv file error-code)
        (hifat-find-file fs path))
       ((unless (equal error-code 0)) (mv fs -1 *ENOENT*))
       ((unless (m1-directory-file-p file)) (mv fs -1 *ENOTDIR*))
       ((unless (atom (m1-file->contents file))) (mv fs -1 *EEXIST*))
       ((mv fs error-code)
        (hifat-remove-file fs path))
       ((unless (equal error-code 0))
        (mv fs -1 error-code)))
    (mv fs 0 0)))

(defun
    hifat-rename (fs oldpath newpath)
  (declare
   (xargs
    :guard (and (m1-file-alist-p fs)
                (hifat-no-dups-p fs)
                (fat32-filename-list-p oldpath)
                (fat32-filename-list-p newpath))))
  (b* (((mv file error-code)
        (hifat-find-file fs oldpath))
       ((unless (equal error-code 0)) (mv fs -1 *ENOENT*))
       ((mv fs error-code)
        (hifat-remove-file fs oldpath))
       ((unless (equal error-code 0))
        (mv fs -1 error-code))
       (dirname (dirname newpath))
       ((mv dir error-code)
        (hifat-find-file fs dirname))
       ((unless (and (equal error-code 0) (m1-directory-file-p dir)))
        (mv fs -1 error-code))
       ((mv fs error-code)
        (hifat-place-file fs newpath file))
       ((unless (equal error-code 0))
        (mv fs -1 error-code)))
    (mv fs 0 0)))

(defund hifat-close (fd fd-table file-table)
  (declare (xargs :guard (and (fd-table-p fd-table)
                              (file-table-p file-table))))
  (b*
      ((fd-table (fd-table-fix fd-table))
       (file-table (file-table-fix file-table))
       (fd-table-entry (assoc fd fd-table))
       ;; FD not found.
       ((unless (consp fd-table-entry)) (mv fd-table file-table *EBADF*))
       (file-table-entry (assoc (cdr fd-table-entry) file-table))
       ;; File table entry not found.
       ((unless (consp file-table-entry)) (mv fd-table file-table *EBADF*)))
    (mv
     (remove-assoc fd fd-table)
     (remove-assoc (cdr fd-table-entry) file-table)
     0)))

(defthm hifat-close-correctness-1
  (b* (((mv fd-table file-table &)
        (hifat-close fd fd-table file-table)))
    (and (fd-table-p fd-table)
         (file-table-p file-table)))
  :hints (("Goal" :in-theory (enable hifat-close))))

(defthm hifat-close-correctness-2
  (implies (and (fd-table-p fd-table)
                (no-duplicatesp (strip-cars fd-table)))
           (b* (((mv fd-table & &)
                 (hifat-close fd fd-table file-table)))
             (no-duplicatesp (strip-cars fd-table))))
  :hints (("Goal" :in-theory (enable hifat-close))))

(defthm
  hifat-close-correctness-3
  (implies (and (file-table-p file-table)
                (no-duplicatesp (strip-cars file-table)))
           (b* (((mv & file-table &)
                 (hifat-close fd fd-table file-table)))
             (no-duplicatesp (strip-cars file-table))))
  :hints (("Goal" :in-theory (enable hifat-close))))

(defun
    hifat-truncate
    (fs path size)
  (declare (xargs :guard (and (natp size)
                              (m1-file-alist-p fs)
                              (hifat-no-dups-p fs)
                              (fat32-filename-list-p path))
                  :guard-hints (("goal" :in-theory
                                 (e/d (len-of-insert-text)
                                      (unsigned-byte-p
                                       consp-assoc-equal))
                                 :use (:instance consp-assoc-equal
                                                 (name (cdr (car fd-table)))
                                                 (l
                                                  file-table))))))
  (b*
      (((unless (unsigned-byte-p 32 size))
        (mv fs -1 *enospc*))
       ((mv file error-code)
        (hifat-find-file fs path))
       ((when (and (equal error-code 0)
                   (m1-directory-file-p file)))
        ;; Can't truncate a directory file.
        (mv fs -1 *eisdir*))
       ((mv oldtext d-e)
        (if (equal error-code 0)
            ;; Regular file
            (mv (coerce (m1-file->contents file) 'list)
                (m1-file->d-e file))
          ;; Nonexistent file
          (mv nil (d-e-fix nil))))
       (file
        (make-m1-file
         :d-e d-e
         :contents (coerce (make-character-list
                            (take size oldtext))
                           'string)))
       ((mv fs error-code)
        (hifat-place-file fs path file)))
    (mv fs (if (equal error-code 0) 0 -1)
        error-code)))

(defthm
  hifat-find-file-correctness-lemma-7
  (implies
   (and (m1-file-alist-p m1-file-alist1)
        (hifat-no-dups-p m1-file-alist1)
        (m1-file-alist-p m1-file-alist2)
        (hifat-no-dups-p m1-file-alist2)
        (hifat-subsetp m1-file-alist1 m1-file-alist2))
   (mv-let
     (file error-code)
     (hifat-find-file m1-file-alist1 path)
     (implies
      (and (equal error-code 0)
           (m1-directory-file-p file))
      (m1-directory-file-p
       (mv-nth
        0
        (hifat-find-file m1-file-alist2 path))))))
  :hints
  (("goal"
    :induct
    (mv
     (mv-nth 1
             (hifat-find-file m1-file-alist1 path))
     (mv-nth 1
             (hifat-find-file m1-file-alist2 path)))
    :in-theory (enable m1-file-alist-p hifat-find-file))))

(defthm
  hifat-find-file-correctness-lemma-5
  (implies
   (and (m1-file-alist-p m1-file-alist1)
        (hifat-no-dups-p m1-file-alist1)
        (m1-file-alist-p m1-file-alist2)
        (hifat-no-dups-p m1-file-alist2)
        (hifat-subsetp m1-file-alist1 m1-file-alist2))
   (mv-let
     (file error-code)
     (hifat-find-file m1-file-alist1 path)
     (declare (ignore error-code))
     (implies
      (m1-directory-file-p file)
      (hifat-subsetp
       (m1-file->contents file)
       (m1-file->contents (mv-nth 0
                                  (hifat-find-file m1-file-alist2 path)))))))
  :hints (("goal" :induct (mv (mv-nth 1 (hifat-find-file m1-file-alist1 path))
                              (mv-nth 1
                                      (hifat-find-file m1-file-alist2 path)))
           :in-theory (enable m1-file-alist-p
                              hifat-find-file hifat-subsetp))))

(local
 (defthm
   hifat-find-file-correctness-lemma-2
   (implies
    (and
     (hifat-equiv m1-file-alist1 m1-file-alist2)
     (m1-file-alist-p m1-file-alist1)
     (hifat-no-dups-p m1-file-alist1)
     (m1-file-alist-p m1-file-alist2)
     (hifat-no-dups-p m1-file-alist2)
     (consp (assoc-equal (fat32-filename-fix (car path))
                         m1-file-alist1))
     (m1-directory-file-p (cdr (assoc-equal (fat32-filename-fix (car path))
                                            m1-file-alist1))))
    (m1-directory-file-p (cdr (assoc-equal (fat32-filename-fix (car path))
                                           m1-file-alist2))))
   :hints (("goal" :in-theory (enable hifat-equiv)
            :do-not-induct t))))

(defthm
  hifat-find-file-correctness-lemma-3
  (implies
   (and
    (hifat-equiv m1-file-alist1 m1-file-alist2)
    (syntaxp (not (term-order m1-file-alist1 m1-file-alist2)))
    (m1-directory-file-p (cdr (assoc-equal (fat32-filename-fix (car path))
                                           m1-file-alist2)))
    (m1-file-alist-p m1-file-alist1)
    (hifat-no-dups-p m1-file-alist1)
    (m1-file-alist-p m1-file-alist2)
    (hifat-no-dups-p m1-file-alist2)
    (consp (assoc-equal (fat32-filename-fix (car path))
                        m1-file-alist1)))
   (hifat-equiv
    (m1-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                         m1-file-alist1)))
    (m1-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                         m1-file-alist2)))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-equiv))))

(defthm
  hifat-find-file-correctness-lemma-4
  (implies (and (hifat-equiv m1-file-alist1 m1-file-alist2)
                (m1-file-alist-p m1-file-alist1)
                (hifat-no-dups-p m1-file-alist1)
                (m1-file-alist-p m1-file-alist2)
                (hifat-no-dups-p m1-file-alist2)
                (consp (assoc-equal (fat32-filename-fix (car path))
                                    m1-file-alist1)))
           (consp (assoc-equal (fat32-filename-fix (car path))
                               m1-file-alist2)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-equiv))))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies
      (and
       (hifat-equiv m1-file-alist1 m1-file-alist2)
       (m1-file-alist-p m1-file-alist1)
       (hifat-no-dups-p m1-file-alist1)
       (m1-file-alist-p m1-file-alist2)
       (hifat-no-dups-p m1-file-alist2)
       (m1-directory-file-p (mv-nth 0
                                    (hifat-find-file m1-file-alist1 path))))
      (hifat-equiv
       (m1-file->contents (mv-nth 0
                                  (hifat-find-file m1-file-alist1 path)))
       (m1-file->contents (mv-nth 0
                                  (hifat-find-file m1-file-alist2 path)))))
     :hints (("goal" :in-theory (enable m1-file-alist-p hifat-find-file)))))

  (defthm
    hifat-find-file-correctness-4
    (implies
     (hifat-equiv m1-file-alist1 m1-file-alist2)
     (hifat-equiv
      (m1-file->contents (mv-nth 0
                                 (hifat-find-file m1-file-alist1 path)))
      (m1-file->contents (mv-nth 0
                                 (hifat-find-file m1-file-alist2 path)))))
    :hints
    (("goal"
      :use ((:instance lemma
                       (m1-file-alist1 (hifat-file-alist-fix m1-file-alist1))
                       (m1-file-alist2 (hifat-file-alist-fix m1-file-alist2)))
            (:instance lemma
                       (m1-file-alist1 (hifat-file-alist-fix m1-file-alist2))
                       (m1-file-alist2 (hifat-file-alist-fix m1-file-alist1)))
            (:instance (:rewrite hifat-find-file-correctness-1)
                       (path path)
                       (fs m1-file-alist1))
            (:instance (:rewrite hifat-find-file-correctness-1)
                       (path path)
                       (fs m1-file-alist2)))
      :do-not-induct t
      :in-theory (e/d (m1-file-p m1-directory-file-p m1-file-contents-p
                                 m1-file->contents hifat-equiv hifat-file-alist-fix)
                      ((:rewrite hifat-find-file-correctness-1)))))
    :rule-classes :congruence))

(fty::defprod
 dir-stream
 ((file-list fat32-filename-list-p)))

(fty::defalist
 dir-stream-table
 :key-type nat
 :val-type dir-stream
 :true-listp t)

(defthm fat32-filename-list-p-of-strip-cars-when-m1-file-alist-p
  (implies (m1-file-alist-p fs)
           (fat32-filename-list-p (strip-cars fs))))

(defthm nat-listp-of-strip-cars-when-dir-stream-table-p
  (implies (dir-stream-table-p dir-stream-table)
           (nat-listp (strip-cars dir-stream-table))))

;; Here's an interesting example that gives the lie to the idea that set-equiv
;; means much of anything when the sort is stable:
;; (b* ((alist '((5 . 1) (6 . 1) (7 . 2))) (l1 (list 5 6)) (l2 (list 6 5)))
;;   (and (set-equiv l1 l2) (not (equal (intval-alist-sort l1 alist)
;;                                      (intval-alist-sort l2 alist)))))
(encapsulate
  ()

  (local (include-book "defsort/examples" :dir :system))

  (defund string-less-p (x y)
    (declare (xargs :guard (and (stringp x) (stringp y))))
    (if (string< x y) t nil))

  (defsort :comparablep stringp
    :compare< string-less-p
    :prefix string2
    :comparable-listp string-listp
    :true-listp t)

  (defthm fat32-filename-list-p-of-<<-merge
    (implies (and (fat32-filename-list-p x) (fat32-filename-list-p y))
             (fat32-filename-list-p (<<-merge x y)))
    :hints (("Goal" :in-theory (e/d (<<-merge)
                                    (floor len)))))

  (local (include-book "ihs/ihs-lemmas" :dir :system))

  (defthm fat32-filename-list-p-of-<<-sort-when-fat32-filename-list-p
    (implies
     (fat32-filename-list-p x)
     (fat32-filename-list-p (<<-sort x)))
    :hints (("Goal" :in-theory (e/d (<<-sort
                                     floor-bounded-by-/)
                                    (floor len
                                           <<-mergesort-equals-insertsort)))))

  (defthm
    common-<<-sort-for-perms
    (implies (set-equiv x y)
             (equal (<<-sort (remove-duplicates-equal x))
                    (<<-sort (remove-duplicates-equal y))))
    :rule-classes :congruence))

(defthm string-listp-when-fat32-filename-list-p
  (implies (fat32-filename-list-p x)
           (string-listp x)))

;; There were a couple of bugs here because we were returning 0 in error cases
;; when -1, as a stand-in for NULL, would have been appropriate.
(defund hifat-opendir (fs path dir-stream-table)
  (declare (xargs :guard (and (dir-stream-table-p dir-stream-table)
                              (m1-file-alist-p fs)
                              (hifat-no-dups-p fs)
                              (fat32-filename-list-p path))
                  :guard-debug t
                  :guard-hints
                  (("Goal"
                    :in-theory
                    (disable
                     alistp-when-m1-file-alist-p)
                    :use
                    (:instance
                     alistp-when-m1-file-alist-p
                     (x (m1-file->contents (mv-nth 0 (hifat-find-file fs path)))))))))
  (b*
      ((dir-stream-table
        (mbe :exec dir-stream-table :logic (dir-stream-table-fix dir-stream-table)))
       ((mv file error-code)
        (hifat-find-file fs path))
       ((unless (equal error-code 0))
        (mv -1 dir-stream-table *enoent*))
       ((unless (m1-directory-file-p file))
        ;; The -1 is because that's our stand-in for NULL.
        (mv -1 dir-stream-table *enotdir*))
       (dir-stream-table-index
        (find-new-index (strip-cars dir-stream-table))))
    (mv
     dir-stream-table-index
     (cons
      (cons dir-stream-table-index
            (make-dir-stream
             :file-list
             (<<-sort
              (strip-cars (m1-file->contents file)))))
      dir-stream-table)
     0)))

(defthm dir-stream-table-p-of-hifat-opendir
  (dir-stream-table-p
   (mv-nth 1 (hifat-opendir fs path dir-stream-table)))
  :hints (("Goal" :in-theory (enable hifat-opendir))))

(defthm hifat-opendir-correctness-2
  (integerp (mv-nth 0
                    (hifat-opendir fs path dir-stream-table)))
  :hints (("goal" :in-theory (enable hifat-opendir)))
  :rule-classes :type-prescription)

(defcong
  dir-stream-table-equiv equal (hifat-opendir fs path dir-stream-table) 3
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-opendir))))

(defthm hifat-opendir-correctness-lemma-1
  (implies (and (set-equiv x y)
                (no-duplicatesp-equal x)
                (no-duplicatesp-equal y)
                (true-listp x)
                (true-listp y))
           (equal (equal (<<-sort x) (<<-sort y))
                  t))
  :hints (("goal" :do-not-induct t
           :in-theory (disable common-<<-sort-for-perms)
           :use common-<<-sort-for-perms)))

(defthm
  hifat-opendir-correctness-lemma-2
  (implies (and (hifat-equiv fs1 fs2)
                (fat32-filename-list-p (strip-cars fs1))
                (fat32-filename-list-p (strip-cars fs2)))
           (equal (set-equiv (strip-cars fs1)
                             (strip-cars fs2))
                  t))
  :hints
  (("goal" :in-theory (disable hifat-equiv-implies-set-equiv-strip-cars-1)
    :use hifat-equiv-implies-set-equiv-strip-cars-1)))

(defthm
  hifat-opendir-correctness-1
  (integerp (mv-nth 2
                    (hifat-opendir fs path dir-stream-table)))
  :hints (("goal" :in-theory (enable hifat-opendir)))
  :rule-classes :type-prescription)

(encapsulate
  ()

  (local
   (defthm
     lemma
     (implies
      (hifat-equiv fs1 fs2)
      (equal
       (hifat-opendir fs1 path dir-stream-table)
       (hifat-opendir fs2 path dir-stream-table)))
     :hints (("goal" :in-theory (enable hifat-opendir)
              :expand
              ((:with
                fat32-filename-list-fix-when-fat32-filename-list-p
                (fat32-filename-list-fix
                 (<<-sort
                  (strip-cars (m1-file->contents (mv-nth 0 (hifat-find-file fs2
                                                                            path)))))))
               (:with
                (:rewrite fat32-filename-list-p-of-<<-sort-when-fat32-filename-list-p)
                (fat32-filename-list-p
                 (<<-sort
                  (strip-cars
                   (m1-file->contents (mv-nth 0 (hifat-find-file fs2 path)))))))
               (:with
                (:rewrite fat32-filename-list-p-of-strip-cars-when-m1-file-alist-p)
                (fat32-filename-list-p
                 (strip-cars (m1-file->contents (mv-nth 0 (hifat-find-file fs2
                                                                           path))))))
               (:with
                (:rewrite m1-file-alist-p-of-m1-file->contents)
                (m1-file-alist-p
                 (m1-file->contents (mv-nth 0 (hifat-find-file fs2 path)))))
               (:with
                (:rewrite hifat-opendir-correctness-lemma-1)
                (equal
                 (<<-sort
                  (strip-cars (m1-file->contents (mv-nth 0 (hifat-find-file fs2 path)))))
                 (<<-sort
                  (strip-cars (m1-file->contents (mv-nth 0 (hifat-find-file fs1
                                                                            path)))))))
               (:with
                (:rewrite no-duplicatesp-of-strip-cars-when-hifat-no-dups-p)
                (no-duplicatesp-equal
                 (strip-cars (m1-file->contents (mv-nth 0 (hifat-find-file fs2
                                                                           path))))))
               (:with
                hifat-opendir-correctness-lemma-2
                (set-equiv
                 (strip-cars (m1-file->contents (mv-nth 0 (hifat-find-file fs1 path))))
                 (strip-cars (m1-file->contents (mv-nth 0 (hifat-find-file fs2
                                                                           path)))))))))
     :rule-classes :congruence))

  ;; Move later.
  (defcong
    hifat-equiv equal
    (hifat-opendir fs path dir-stream-table)
    1))

(assert-event
 (b*
     (((mv dirp dir-stream-table errno)
       (hifat-opendir
        '(("INITRD  IMG" (D-E 0 0 0 0 0 0 0 0 0 0 0 0
                                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (CONTENTS . ""))
          ("RUN        "
           (D-E 0 0 0 0 0 0 0 0 0 0 0 0
                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (CONTENTS ("RSYSLOGDPID" (D-E 0 0 0 0 0 0 0 0 0 0 0 0
                                             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                      (CONTENTS . ""))))
          ("USR        "
           (D-E 0 0 0 0 0 0 0 0 0 0 0 0
                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (CONTENTS
            ("LOCAL      " (D-E 0 0 0 0 0 0 0 0 0 0 0 0
                                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
             (CONTENTS))
            ("LIB        " (D-E 0 0 0 0 0 0 0 0 0 0 0 0
                                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
             (CONTENTS))
            ("SHARE      " (D-E 0 0 0 0 0 0 0 0 0 0 0 0
                                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
             (CONTENTS))
            ("BIN        "
             (D-E 0 0 0 0 0 0 0 0 0 0 0 0
                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
             (CONTENTS
              ("CAT        " (D-E 0 0 0 0 0 0 0 0 0 0 0 0
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
               (CONTENTS . ""))
              ("TAC        " (D-E 0 0 0 0 0 0 0 0 0 0 0 0
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
               (CONTENTS . ""))
              ("COL        " (D-E 0 0 0 0 0 0 0 0 0 0 0 0
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
               (CONTENTS . "")))))))
        (list "USR        ")
        nil)))
   (and
    (equal dirp 0)
    (equal dir-stream-table
           '((0 (FILE-LIST "BIN        " "LIB        "
                           "LOCAL      " "SHARE      "))))
    (equal errno 0))))

;; This function is not going to return a pure filename as its (mv-nth 0
;; ...). We'll let the chips fall where they may. But we really need to be able
;; to return nil to signal clearly that we have reached the end of the stream.
(defund hifat-readdir (dirp dir-stream-table)
  (declare (xargs :guard (and (dir-stream-table-p dir-stream-table)
                              (natp dirp))
                  :guard-debug t))
  (b*
      ((dirp (mbe :exec dirp :logic (nfix dirp)))
       (dir-stream-table
        (mbe :exec dir-stream-table
             :logic (dir-stream-table-fix dir-stream-table)))
       (alist-elem
        (assoc-equal dirp dir-stream-table))
       ((unless (consp alist-elem))
        (mv nil *ebadf* dir-stream-table))
       ((unless (consp (dir-stream->file-list (cdr alist-elem))))
        (mv nil 0 dir-stream-table)))
    (mv
     (car (dir-stream->file-list (cdr alist-elem)))
     0
     (put-assoc-equal
      dirp
      (change-dir-stream
       (cdr alist-elem)
       :file-list
       (cdr (dir-stream->file-list (cdr alist-elem))))
      dir-stream-table))))

(assert-event
 (b*
     (((mv name errno dir-stream-table)
       (hifat-readdir 0
                      '((0 (FILE-LIST "BIN        " "LIB        "
                                      "LOCAL      " "SHARE      "))))))
   (and
    (equal name "BIN        ")
    (equal errno 0)
    (equal
     dir-stream-table
     '((0  (FILE-LIST "LIB        "
                      "LOCAL      " "SHARE      ")))))))

(defthm dir-stream-table-p-of-hifat-readdir
  (dir-stream-table-p (mv-nth 2
                              (hifat-readdir dirp dir-stream-table)))
  :hints (("goal" :in-theory (enable hifat-readdir))))

(defund hifat-closedir (dirp dir-stream-table)
  (declare (xargs :guard (dir-stream-table-p dir-stream-table)))
  (b*
      ((dir-stream-table (mbe :exec dir-stream-table :logic
                              (dir-stream-table-fix dir-stream-table)))
       (alist-elem
        (assoc-equal dirp dir-stream-table))
       ((unless (consp alist-elem))
        (mv *ebadf* dir-stream-table)))
    (mv
     0
     (remove-assoc-equal
      dirp
      dir-stream-table))))

(defthm dir-stream-table-p-of-hifat-closedir
  (dir-stream-table-p (mv-nth 1 (hifat-closedir dirp dir-stream-table)))
  :hints (("Goal" :in-theory (enable hifat-closedir))))

(assert-event
 (b*
     (((mv errno dir-stream-table)
       (hifat-closedir
        0
        '((0 (FILE-LIST "LOCAL      " "LIB        "
                        "SHARE      " "BIN        "))))))
   (and
    (equal errno 0)
    (equal
     dir-stream-table nil))))
