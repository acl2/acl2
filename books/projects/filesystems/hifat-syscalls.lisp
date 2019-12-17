(in-package "ACL2")

;  hifat-syscalls.lisp                                 Mihir Mehta

; Syscalls for HiFAT. These syscalls usually return, among other things, a
; return value (corresponding to the C return value) and an errno.

(include-book "hifat")

;; This implementation of basename+dirname is not exactly compliant with the
;; man pages basename(3)/dirname(3) - it assumes all paths provided to it are
;; absolute paths (thus, the empty pathname is treated like "/"), and further
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
(defund
  hifat-basename-dirname-helper (path)
  (declare (xargs :guard (fat32-filename-list-p path)
                  :guard-hints (("Goal" :in-theory (disable
                                                    make-list-ac-removal)))))
  (b*
      (;; Under the assumption that all pathnames begin with a /, this really
       ;; is the case where there's a / and nothing else.
       ((when (atom path))
        (mv *empty-fat32-name* nil))
       ((when (atom (cdr path)))
        (mv
         (fat32-filename-fix (car path))
         nil))
       ((mv tail-basename tail-dirname)
        (hifat-basename-dirname-helper (cdr path))))
    (mv tail-basename
        (list* (fat32-filename-fix (car path))
               tail-dirname))))

(defthm
  hifat-basename-dirname-helper-correctness-1
  (mv-let (basename dirname)
    (hifat-basename-dirname-helper path)
    (and (fat32-filename-p basename)
         (fat32-filename-list-p dirname)))
  :hints
  (("goal" :induct (hifat-basename-dirname-helper path)
    :in-theory (enable hifat-basename-dirname-helper)))
  :rule-classes
  (:rewrite
   (:type-prescription
    :corollary
    (stringp (mv-nth 0 (hifat-basename-dirname-helper path))))
   (:type-prescription
    :corollary
    (true-listp (mv-nth 1 (hifat-basename-dirname-helper path))))))

(defun hifat-basename (path)
  (declare (xargs :guard (fat32-filename-list-p path)))
  (mv-let (basename dirname)
    (hifat-basename-dirname-helper path)
    (declare (ignore dirname))
    basename))

(defun hifat-dirname (path)
  (declare (xargs :guard (fat32-filename-list-p path)))
  (mv-let (basename dirname)
    (hifat-basename-dirname-helper path)
    (declare (ignore basename))
    dirname))

(defun hifat-lstat (fs pathname)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (hifat-no-dups-p fs)
                              (fat32-filename-list-p pathname))))
  (b*
      (((mv file errno)
        (hifat-find-file fs pathname))
       ((when (not (equal errno 0)))
        (mv (make-struct-stat) -1 errno))
       (st_size (if (m1-directory-file-p file)
                    *ms-max-dir-size*
                  (length (m1-file->contents file)))))
    (mv
     (make-struct-stat
      :st_size st_size)
     0 0)))

;; By default, we aren't going to check whether the file exists.
(defun hifat-open (pathname fd-table file-table)
  (declare (xargs :guard (and (fat32-filename-list-p pathname)
                              (fd-table-p fd-table)
                              (file-table-p file-table))))
  (b*
      ((fd-table (fd-table-fix fd-table))
       (file-table (file-table-fix file-table))
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

(defthm hifat-open-correctness-1
  (b*
      (((mv fd-table file-table fd &) (hifat-open pathname fd-table file-table)))
    (and
     (fd-table-p fd-table)
     (file-table-p file-table)
     (integerp fd)))
  :rule-classes
  ((:rewrite
    :corollary
    (b*
        (((mv fd-table file-table & &) (hifat-open pathname fd-table file-table)))
      (and
       (fd-table-p fd-table)
       (file-table-p file-table))))
   (:type-prescription
    :corollary
    (b*
        (((mv & & fd &) (hifat-open pathname fd-table file-table)))
      (integerp fd)))))

(defthm
  hifat-open-correctness-2
  (implies (no-duplicatesp (strip-cars (fd-table-fix fd-table)))
           (b* (((mv fd-table & & &)
                 (hifat-open pathname fd-table file-table)))
             (no-duplicatesp (strip-cars fd-table)))))

(defthm
  hifat-open-correctness-3
  (implies
   (no-duplicatesp (strip-cars (file-table-fix file-table)))
   (b* (((mv & file-table & &)
         (hifat-open pathname fd-table file-table)))
     (no-duplicatesp (strip-cars file-table)))))

;; Per the man page pread(2), this should not change the offset of the file
;; descriptor in the file table. Thus, there's no need for the file table to be
;; an argument.
(defun
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
      ((fd-table-entry (assoc-equal fd fd-table))
       ((unless (consp fd-table-entry))
        (mv "" -1 *ebadf*))
       (file-table-entry (assoc-equal (cdr fd-table-entry)
                                      file-table))
       ((unless (consp file-table-entry))
        (mv "" -1 *ebadf*))
       (pathname (file-table-element->fid (cdr file-table-entry)))
       ((mv file error-code)
        (hifat-find-file fs pathname))
       ((unless (and (equal error-code 0)
                     (m1-regular-file-p file)))
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
                  (equal (length buf) ret)))))

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
       (pathname (file-table-element->fid (cdr file-table-entry)))
       ((mv file error-code)
        (hifat-find-file fs pathname))
       ((mv oldtext dir-ent)
        (if (and (equal error-code 0)
                 (m1-regular-file-p file))
            (mv (coerce (m1-file->contents file) 'list)
                (m1-file->dir-ent file))
          (mv nil (dir-ent-fix nil))))
       ((unless (unsigned-byte-p 32 (+ OFFSET (length BUF))))
        (mv fs -1 *enospc*))
       (file
        (make-m1-file
         :dir-ent dir-ent
         :contents (coerce (insert-text oldtext offset buf)
                           'string)))
       ((mv fs error-code)
        (hifat-place-file fs pathname file)))
    (mv fs (if (equal error-code 0) 0 -1)
        error-code)))

(defun
    hifat-mkdir (fs pathname)
  (declare
   (xargs
    :guard (and (m1-file-alist-p fs)
                (hifat-no-dups-p fs)
                (fat32-filename-list-p pathname))
    :guard-hints
    (("goal"
      :in-theory
      (disable
       (:rewrite hifat-basename-dirname-helper-correctness-1))
      :use
      (:instance
       (:rewrite hifat-basename-dirname-helper-correctness-1)
       (path pathname))))))
  (b* ((dirname (hifat-dirname pathname))
       ;; Never pass relative pathnames to syscalls - make them always begin
       ;; with "/".
       ((mv parent-dir errno)
        (hifat-find-file fs dirname))
       ((unless (or (atom dirname)
                    (and (equal errno 0)
                         (m1-directory-file-p parent-dir))))
        (mv fs -1 *enoent*))
       ((mv & errno)
        (hifat-find-file fs pathname))
       ((unless (not (equal errno 0)))
        (mv fs -1 *eexist*))
       (basename (hifat-basename pathname))
       ((unless (equal (length basename) 11))
        (mv fs -1 *enametoolong*))
       (dir-ent
        (dir-ent-install-directory-bit
         (dir-ent-fix nil)
         t))
       (file (make-m1-file :dir-ent dir-ent
                           :contents nil))
       ((mv fs error-code)
        (hifat-place-file fs pathname file))
       ((unless (equal error-code 0))
        (mv fs -1 error-code)))
    (mv fs 0 0)))

(defun
    hifat-mknod (fs pathname)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (hifat-no-dups-p fs)
                              (fat32-filename-list-p pathname))))
  (b* ((dirname (hifat-dirname pathname))
       (basename (hifat-basename pathname))
       ((mv parent-dir errno)
        (hifat-find-file fs dirname))
       ((unless (or (atom dirname)
                    (and (equal errno 0)
                         (m1-directory-file-p parent-dir))))
        (mv fs -1 *enoent*))
       ((mv & errno)
        (hifat-find-file fs pathname))
       ((unless (not (equal errno 0)))
        (mv fs -1 *eexist*))
       ((unless (equal (length basename) 11))
        (mv fs -1 *enametoolong*))
       (dir-ent (dir-ent-set-filename (dir-ent-fix nil)
                                      basename))
       (file (make-m1-file :dir-ent dir-ent
                           :contents nil))
       ((mv fs error-code)
        (hifat-place-file fs pathname file))
       ((unless (equal error-code 0))
        (mv fs -1 error-code)))
    (mv fs 0 0)))

(defthm
  hifat-unlink-guard-lemma-1
  (implies (m1-file-p file)
           (and
            (true-listp (m1-file->dir-ent file))
            (equal (len (m1-file->dir-ent file)) *ms-dir-ent-length*)
            (unsigned-byte-listp 8 (m1-file->dir-ent file))))
  :hints
  (("goal" :in-theory (e/d (dir-ent-p)
                           (dir-ent-p-of-m1-file->dir-ent))
    :use (:instance dir-ent-p-of-m1-file->dir-ent
                    (x file)))))

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
    hifat-unlink (fs pathname)
  (declare
   (xargs
    :guard (and (m1-file-alist-p fs)
                (hifat-no-dups-p fs)
                (fat32-filename-list-p pathname))))
  (b* (((mv file error-code)
        (hifat-find-file fs pathname))
       ((unless (equal error-code 0)) (mv fs -1 *ENOENT*))
       ((unless (m1-regular-file-p file)) (mv fs -1 *EISDIR*))
       ((mv fs error-code)
        (hifat-remove-file fs pathname))
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
    hifat-unlink-recursive (fs pathname)
  (declare
   (xargs
    :guard (and (m1-file-alist-p fs)
                (hifat-no-dups-p fs)
                (fat32-filename-list-p pathname))))
  (b* (((mv file error-code)
        (hifat-find-file fs pathname))
       ((unless (equal error-code 0)) (mv fs -1 *ENOENT*))
       ((unless (m1-directory-file-p file)) (mv fs -1 *ENOTDIR*))
       ((mv fs error-code)
        (hifat-remove-file fs pathname))
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
    hifat-rmdir (fs pathname)
  (declare
   (xargs
    :guard (and (m1-file-alist-p fs)
                (hifat-no-dups-p fs)
                (fat32-filename-list-p pathname))))
  (b* (((mv file error-code)
        (hifat-find-file fs pathname))
       ((unless (equal error-code 0)) (mv fs -1 *ENOENT*))
       ((unless (m1-directory-file-p file)) (mv fs -1 *ENOTDIR*))
       ((unless (atom (m1-file->contents file))) (mv fs -1 *EEXIST*))
       ((mv fs error-code)
        (hifat-remove-file fs pathname))
       ((unless (equal error-code 0))
        (mv fs -1 error-code)))
    (mv fs 0 0)))

(defun
    hifat-rename (fs oldpathname newpathname)
  (declare
   (xargs
    :guard (and (m1-file-alist-p fs)
                (hifat-no-dups-p fs)
                (fat32-filename-list-p oldpathname)
                (fat32-filename-list-p newpathname))))
  (b* (((mv file error-code)
        (hifat-find-file fs oldpathname))
       ((unless (equal error-code 0)) (mv fs -1 *ENOENT*))
       ((mv fs error-code)
        (hifat-remove-file fs oldpathname))
       ((unless (equal error-code 0))
        (mv fs -1 error-code))
       (dirname (hifat-dirname newpathname))
       ((mv dir error-code)
        (hifat-find-file fs dirname))
       ((unless (and (equal error-code 0) (m1-directory-file-p dir)))
        (mv fs -1 error-code))
       ((mv fs error-code)
        (hifat-place-file fs newpathname file))
       ((unless (equal error-code 0))
        (mv fs -1 error-code)))
    (mv fs 0 0)))

(defun hifat-close (fd fd-table file-table)
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

(defthm
  fd-table-p-of-remove-assoc
  (implies (fd-table-p fd-table)
           (fd-table-p (remove-assoc-equal fd fd-table))))

(defthm
  file-table-p-of-remove-assoc
  (implies (file-table-p file-table)
           (file-table-p (remove-assoc-equal fd file-table))))

(defthm hifat-close-correctness-1
  (b* (((mv fd-table file-table &)
        (hifat-close fd fd-table file-table)))
    (and (fd-table-p fd-table)
         (file-table-p file-table))))

(defthm hifat-close-correctness-2
  (implies (and (fd-table-p fd-table)
                (no-duplicatesp (strip-cars fd-table)))
           (b* (((mv fd-table & &)
                 (hifat-close fd fd-table file-table)))
             (no-duplicatesp (strip-cars fd-table)))))

(defthm
  hifat-close-correctness-3
  (implies (and (file-table-p file-table)
                (no-duplicatesp (strip-cars file-table)))
           (b* (((mv & file-table &)
                 (hifat-close fd fd-table file-table)))
             (no-duplicatesp (strip-cars file-table)))))

(defun
    hifat-truncate
    (fs pathname size)
  (declare (xargs :guard (and (natp size)
                              (m1-file-alist-p fs)
                              (hifat-no-dups-p fs)
                              (fat32-filename-list-p pathname))
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
        (hifat-find-file fs pathname))
       ((when (and (equal error-code 0)
                   (m1-directory-file-p file)))
        ;; Can't truncate a directory file.
        (mv fs -1 *eisdir*))
       ((mv oldtext dir-ent)
        (if (equal error-code 0)
            ;; Regular file
            (mv (coerce (m1-file->contents file) 'list)
                (m1-file->dir-ent file))
          ;; Nonexistent file
          (mv nil (dir-ent-fix nil))))
       (file
        (make-m1-file
         :dir-ent dir-ent
         :contents (coerce (make-character-list
                            (take size oldtext))
                           'string)))
       ((mv fs error-code)
        (hifat-place-file fs pathname file)))
    (mv fs (if (equal error-code 0) 0 -1)
        error-code)))
