; Copyright (C) 2017, Regents of the University of Texas
; Written by Mihir Mehta
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

;  file-system-m1.lisp                                 Mihir Mehta

; An abstract model used, for the time being, for doing file operations such as
; lstat on the filesystem.

(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)
(include-book "std/io/read-ints" :dir :system)
(local (include-book "ihs/logops-lemmas" :dir :system))
(local (include-book "rtl/rel9/arithmetic/top" :dir :system))
(include-book "kestrel/utilities/strings/top" :dir :system)

(include-book "insert-text")
(include-book "fat32")

;; This was moved to one of the main books, but still kept
(defthm unsigned-byte-listp-of-update-nth
  (implies (and (unsigned-byte-listp n l)
                (< key (len l)))
           (equal (unsigned-byte-listp n (update-nth key val l))
                  (unsigned-byte-p n val)))
  :hints (("goal" :in-theory (enable unsigned-byte-listp))))

;; This was taken from Alessandro Coglio's book at
;; books/kestrel/utilities/typed-list-theorems.lisp
(defthm unsigned-byte-listp-of-rev
  (equal (unsigned-byte-listp n (rev bytes))
         (unsigned-byte-listp n (list-fix bytes)))
  :hints (("goal" :in-theory (enable unsigned-byte-listp rev))))

(defthm nth-of-unsigned-byte-list
  (implies (and (unsigned-byte-listp bits l)
                (natp n)
                (< n (len l)))
           (unsigned-byte-p bits (nth n l))))

(defthm nth-of-string=>nats
  (equal (nth n (string=>nats string))
         (if (< (nfix n) (len (explode string)))
             (char-code (char string n))
             nil))
  :hints (("goal" :in-theory (enable string=>nats))))

(defun dir-ent-p (x)
  (declare (xargs :guard t))
  (and (unsigned-byte-listp 8 x)
       (equal (len x) *ms-dir-ent-length*)))

(defun dir-ent-fix (x)
  (declare (xargs :guard t))
  (if
      (dir-ent-p x)
      x
    (make-list *ms-dir-ent-length* :initial-element 0)))

(fty::deffixtype
 dir-ent
 :pred dir-ent-p
 :fix dir-ent-fix
 :equiv dir-ent-equiv
 :define t
 :forward t)

(defun dir-ent-first-cluster (dir-ent)
  (declare
   (xargs :guard (dir-ent-p dir-ent)))
  (combine32u (nth 21 dir-ent)
              (nth 20 dir-ent)
              (nth 27 dir-ent)
              (nth 26 dir-ent)))

(defun dir-ent-file-size (dir-ent)
  (declare
   (xargs :guard (dir-ent-p dir-ent)))
  (combine32u (nth 31 dir-ent)
              (nth 30 dir-ent)
              (nth 29 dir-ent)
              (nth 28 dir-ent)))

(encapsulate
  ()

  (local
   (defthmd dir-ent-directory-p-guard-lemma-1
     (implies (and (natp n)
                   (not (integerp (nth n l)))
                   (unsigned-byte-listp bits l))
              (<= (len l) n))
     :rule-classes :linear))

  (local
   (defthm
     dir-ent-directory-p-guard-lemma-2
     (implies (and (not (integerp (nth 11 l)))
                   (unsigned-byte-listp 8 l))
              (<= (len l) 11))
     :hints
     (("goal"
       :use (:instance dir-ent-directory-p-guard-lemma-1 (n 11)
                       (bits 8))))
     :rule-classes :linear))

  (defund dir-ent-directory-p (dir-ent)
    (declare
     (xargs :guard (dir-ent-p dir-ent)
            :guard-hints (("Goal" :in-theory (disable unsigned-byte-p)
                           :use (:instance unsigned-byte-p-logand
                                           (size 8)
                                           (i #x10)
                                           (j (nth 11 dir-ent)))) )))
    (not (zp (logand #x10 (nth 11 dir-ent))))))

(fty::defprod m1-file
  ((dir-ent dir-ent-p :default (dir-ent-fix nil))
   (contents any-p :default nil)))

(defund m1-regular-file-p (file)
  (declare (xargs :guard t))
  (and
   (m1-file-p file)
   (stringp (m1-file->contents file))))

(defthm
  m1-regular-file-p-correctness-1
  (implies (m1-regular-file-p file)
           (stringp (m1-file->contents file)))
  :hints (("goal" :in-theory (enable m1-regular-file-p))))

(fty::defalist m1-file-alist
      :key-type string
      :val-type m1-file
      :true-listp t)

(defun m1-directory-file-p (file)
  (declare (xargs :guard t))
  (and
   (m1-file-p file)
   (m1-file-alist-p (m1-file->contents file))))

(fty::defprod
 struct-stat
 ;; Currently, this is the only thing I can decipher.
 ((st_size natp :default 0)))

;; This data structure may change later.
(fty::defprod
 file-table-element
 ((pos natp) ;; index within the file
  ;; mode ?
  (fid string-listp) ;; pathname of the file
  ))

(fty::defalist
 file-table
 :key-type nat
 :val-type file-table-element
 :true-listp t)

;; This data structure may change later.
(fty::defalist fd-table
               :key-type nat ;; index into the fd-table
               :val-type nat ;; index into the file-table
               :true-listp t)

(defthm lstat-guard-lemma-1
  (implies (and (m1-file-alist-p fs)
                (consp (assoc-equal filename fs)))
           (m1-file-p (cdr (assoc-equal filename fs)))))

(defthm lstat-guard-lemma-2
  (implies (m1-file-alist-p fs)
           (alistp fs)))

(defun find-file-by-pathname (fs pathname)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (string-listp pathname))
                  :measure (acl2-count pathname)))
  (b* ((fs (m1-file-alist-fix fs))
       ((unless (consp pathname))
        (mv (make-m1-file) *enoent*))
       (name (str-fix (car pathname)))
       (alist-elem (assoc-equal name fs))
       ((unless (consp alist-elem))
        (mv (make-m1-file) *enoent*))
       ((when (m1-directory-file-p (cdr alist-elem)))
        (if (atom (cdr pathname))
            (mv (cdr alist-elem) 0)
            (find-file-by-pathname
             (m1-file->contents (cdr alist-elem))
             (cdr pathname))))
       ((unless (atom (cdr pathname)))
        (mv (make-m1-file) *enotdir*)))
    (mv (cdr alist-elem) 0)))

(defthm
  find-file-by-pathname-correctness-1
  (mv-let (file error-code)
    (find-file-by-pathname fs pathname)
    (and (m1-file-p file)
         (integerp error-code)))
  :hints (("goal" :induct (find-file-by-pathname fs pathname))))

(defthm find-file-by-pathname-correctness-2
  (equal
    (find-file-by-pathname fs (str::string-list-fix pathname))
    (find-file-by-pathname fs pathname)))

(defcong m1-file-alist-equiv equal (find-file-by-pathname fs pathname) 1)

(defcong str::string-list-equiv equal (find-file-by-pathname fs pathname) 2
  :hints
  (("goal'"
    :in-theory (disable find-file-by-pathname-correctness-2)
    :use (find-file-by-pathname-correctness-2
          (:instance find-file-by-pathname-correctness-2
                     (pathname pathname-equiv))))))
;; This function should continue to take pathnames which refer to top-level
;; fs... but what happens when "." and ".." appear in a pathname? We'll have to
;; modify the code to deal with that.
(defun
  place-file-by-pathname
  (fs pathname file)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (string-listp pathname)
                              (m1-file-p file))
                  :measure (acl2-count pathname)))
  (b*
      ((fs (m1-file-alist-fix fs))
       (file (m1-file-fix file))
       ((unless (consp pathname))
        (mv fs *enoent*))
       (name (str-fix (car pathname)))
       (alist-elem (assoc-equal name fs)))
    (if
        (consp alist-elem)
        (if
         (m1-directory-file-p (cdr alist-elem))
         (mv-let
           (new-contents error-code)
           (place-file-by-pathname
            (m1-file->contents (cdr alist-elem))
            (cdr pathname)
            file)
           (mv
            (put-assoc-equal
             name
             (make-m1-file
              :dir-ent (m1-file->dir-ent (cdr alist-elem))
              :contents new-contents)
             fs)
            error-code))
         (if (or
              (consp (cdr pathname))
              ;; this is the case where a regular file could get replaced by a
              ;; directory, which is a bad idea
              (m1-directory-file-p file))
             (mv fs *enotdir*)
           (mv (put-assoc-equal name file fs) 0)))
      (if (atom (cdr pathname))
          (mv (put-assoc-equal name file fs) 0)
        (mv fs *enotdir*)))))

(defthm
  place-file-by-pathname-correctness-1-lemma-1
  (implies
   (m1-file-alist-p alist)
   (equal (m1-file-alist-p (put-assoc-equal name val alist))
          (and (stringp name) (m1-file-p val)))))

(defthm
  place-file-by-pathname-correctness-1
  (mv-let (fs error-code)
    (place-file-by-pathname fs pathname file)
    (and (m1-file-alist-p fs)
         (integerp error-code)))
  :hints
  (("goal" :induct (place-file-by-pathname fs pathname file))))

(defthm
  place-file-by-pathname-correctness-2
  (equal
   (place-file-by-pathname fs (str::string-list-fix pathname)
                           file)
   (place-file-by-pathname fs pathname file)))

(defcong m1-file-alist-equiv equal
  (place-file-by-pathname fs pathname file) 1)

(defcong str::string-list-equiv equal
  (place-file-by-pathname fs pathname file) 2
  :hints
  (("goal'"
    :in-theory (disable place-file-by-pathname-correctness-2)
    :use (place-file-by-pathname-correctness-2
          (:instance place-file-by-pathname-correctness-2
                     (pathname pathname-equiv))))))

(defcong m1-file-equiv equal
  (place-file-by-pathname fs pathname file) 3)

(defthm
  m1-read-after-write-lemma-1
  (implies
   (and (m1-file-alist-p alist)
        (stringp name))
   (equal (m1-file-alist-fix (put-assoc-equal name val alist))
          (put-assoc-equal name (m1-file-fix val)
                           (m1-file-alist-fix alist))))
  :hints (("goal" :in-theory (enable m1-file-alist-fix))))

(defun string-list-prefixp (x y)
  (declare (xargs :guard (and (string-listp x)
                              (string-listp y))))
  (if (consp x)
      (and (consp y)
           (streqv (car x) (car y))
           (string-list-prefixp (cdr x) (cdr y)))
    t))

(encapsulate
  ()

  (local
   (defun
       induction-scheme
       (pathname1 pathname2 fs)
     (declare (xargs :guard (and (string-listp pathname1)
                                 (string-listp pathname2)
                                 (m1-file-alist-p fs))))
     (if
         (or (atom pathname1) (atom pathname2))
         1
       (if
           (not (streqv (car pathname2) (car pathname1)))
           2
         (let*
             ((fs (m1-file-alist-fix fs))
              (alist-elem (assoc-equal (str-fix (car pathname1)) fs)))
           (if
               (atom alist-elem)
               3
             (if
                 (m1-directory-file-p (cdr alist-elem))
                 (induction-scheme (cdr pathname1)
                                   (cdr pathname2)
                                   (m1-file->contents (cdr alist-elem)))
               4)))))))

  (defthm
    m1-read-after-write
    (implies
     (m1-regular-file-p file2)
     (b* (((mv original-file original-error-code)
           (find-file-by-pathname fs pathname1))
          ((unless (and (equal original-error-code 0)
                        (m1-regular-file-p original-file)))
           t)
          ((mv new-fs new-error-code)
           (place-file-by-pathname fs pathname2 file2))
          ((unless (equal new-error-code 0)) t))
       (equal (find-file-by-pathname new-fs pathname1)
              (if (str::string-list-equiv pathname1 pathname2)
                  (mv (m1-file-fix file2) 0)
                (find-file-by-pathname fs pathname1)))))
    :hints
    (("goal" :induct (induction-scheme pathname1 pathname2 fs)
      :in-theory (enable streqv str::string-list-fix
                         m1-regular-file-p))))

  (defthm
    m1-read-after-create
    (implies
     (and
      (m1-regular-file-p file2)
      ;; This is to avoid an odd situation where a query which would return
      ;; a "file not found" error earlier now returns "not a directory".
      (or (not (string-list-prefixp pathname2 pathname1))
          (equal pathname2 pathname1)))
     (b* (((mv & original-error-code)
           (find-file-by-pathname fs pathname1))
          ((unless (not (equal original-error-code 0)))
           t)
          ((mv new-fs new-error-code)
           (place-file-by-pathname fs pathname2 file2))
          ((unless (equal new-error-code 0)) t))
       (equal (find-file-by-pathname new-fs pathname1)
              (if (str::string-list-equiv pathname1 pathname2)
                  (mv (m1-file-fix file2) 0)
                (find-file-by-pathname fs pathname1)))))
    :hints
    (("goal" :induct (induction-scheme pathname1 pathname2 fs)
      :in-theory (enable streqv str::string-list-fix
                         m1-regular-file-p)))))

(defun m1-lstat (fs pathname)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (string-listp pathname))))
  (mv-let
    (file errno)
    (find-file-by-pathname fs pathname)
    (if (not (equal errno 0))
        (mv (make-struct-stat) -1 errno)
      (mv
       (make-struct-stat
        :st_size (dir-ent-file-size
                  (m1-file->dir-ent file)))
       0 0))))

(defun
  find-new-index-helper (fd-list ac)
  (declare (xargs :guard (and (nat-listp fd-list) (natp ac))
                  :measure (len fd-list)))
  (let ((snipped-list (remove ac fd-list)))
       (if (equal (len snipped-list) (len fd-list))
           ac
           (find-new-index-helper snipped-list (+ ac 1)))))

(defthm find-new-index-helper-correctness-1-lemma-1
  (>= (find-new-index-helper fd-list ac) ac)
  :rule-classes :linear)

(defthm
  find-new-index-helper-correctness-1-lemma-2
  (implies (integerp ac)
           (integerp (find-new-index-helper fd-list ac))))

(encapsulate
  ()

  (local (include-book "std/lists/remove" :dir :system))
  (local (include-book "std/lists/duplicity" :dir :system))

  (defthm
    find-new-index-helper-correctness-1
    (not (member-equal
          (find-new-index-helper fd-list ac)
          fd-list))))

(defund
  find-new-index (fd-list)
  (declare (xargs :guard (nat-listp fd-list)))
  (find-new-index-helper fd-list 0))

(defthm find-new-index-correctness-1-lemma-1
  (>= (find-new-index fd-list) 0)
  :hints (("Goal" :in-theory (enable find-new-index)))
  :rule-classes :linear)

(defthm
  find-new-index-correctness-1-lemma-2
  (integerp (find-new-index fd-list))
  :hints (("Goal" :in-theory (enable find-new-index))))

(defthm m1-open-guard-lemma-1
  (implies (fd-table-p fd-table)
           (alistp fd-table)))

(defun m1-open (pathname fs fd-table file-table)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (string-listp pathname)
                              (fd-table-p fd-table)
                              (file-table-p file-table))))
  (b*
      ((fd-table (fd-table-fix fd-table))
       (file-table (file-table-fix file-table))
       ((mv & errno)
        (find-file-by-pathname fs pathname))
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
     0 0)))

(defthm m1-open-correctness-1
  (b*
      (((mv fd-table file-table & &) (m1-open pathname fs fd-table file-table)))
    (and
     (fd-table-p fd-table)
     (file-table-p file-table))))

(defthm
  m1-pread-guard-lemma-1
  (implies
   (and (file-table-p file-table)
        (consp (assoc-equal x file-table)))
   (file-table-element-p (cdr (assoc-equal x file-table)))))

;; Per the man page pread(2), this should not change the offset of the file
;; descriptor in the file table. Thus, there's no need for the file table to be
;; an argument.
(defun
  m1-pread
  (fd count offset fs fd-table file-table)
  (declare (xargs :guard (and (natp fd)
                              (natp count)
                              (natp offset)
                              (fd-table-p fd-table)
                              (file-table-p file-table)
                              (m1-file-alist-p fs))
                  :guard-debug t))
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
        (find-file-by-pathname fs pathname))
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
  m1-pread-correctness-1
  (mv-let (buf ret error-code)
    (m1-pread fd count offset fs fd-table file-table)
    (and (stringp buf)
         (integerp ret)
         (integerp error-code)
         (implies (>= ret 0)
                  (equal (length buf) ret)))))

(defun
  m1-pwrite
  (fd buf offset fs fd-table file-table)
  (declare (xargs :guard (and (natp fd)
                              (stringp buf)
                              (natp offset)
                              (fd-table-p fd-table)
                              (file-table-p file-table)
                              (m1-file-alist-p fs))))
  (b*
      ((fd-table-entry (assoc-equal fd fd-table))
       (fs (m1-file-alist-fix fs))
       ((unless (consp fd-table-entry))
        (mv fs -1 *ebadf*))
       (file-table-entry (assoc-equal (cdr fd-table-entry)
                                      file-table))
       ((unless (consp file-table-entry))
        (mv fs -1 *ebadf*))
       (pathname (file-table-element->fid (cdr file-table-entry)))
       ((mv file error-code)
        (find-file-by-pathname fs pathname))
       ((mv oldtext dir-ent)
        (if (and (equal error-code 0)
                 (m1-regular-file-p file))
            (mv (coerce (m1-file->contents file) 'list)
                (m1-file->dir-ent file))
            (mv nil (dir-ent-fix nil))))
       (file
        (make-m1-file
         :dir-ent dir-ent
         :contents (coerce (insert-text oldtext offset buf)
                           'string)))
       ((mv fs error-code)
        (place-file-by-pathname fs pathname file)))
    (mv fs (if (equal error-code 0) 0 -1)
        error-code)))

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
  m1-basename-dirname-helper (path)
  (declare (xargs :guard (string-listp path)))
  (if (atom path)
      (mv "." (list "."))
      (if (or (atom (cdr path))
              (and (not (streqv (car path) ""))
                   (atom (cddr path))
                   (streqv (cadr path) "")))
          (mv (str-fix (car path)) (list "."))
          (if (atom (cddr path))
              (mv (str-fix (cadr path))
                  (list (str-fix (car path))))
              (mv-let (tail-basename tail-dirname)
                (m1-basename-dirname-helper (cdr path))
                (mv tail-basename
                    (list* (str-fix (car path))
                           tail-dirname)))))))

(defthm
  m1-basename-dirname-helper-correctness-1
  (mv-let (basename dirname)
    (m1-basename-dirname-helper path)
    (and (stringp basename)
         (string-listp dirname)))
  :hints
  (("goal" :in-theory (enable m1-basename-dirname-helper)))
  :rule-classes
  (:rewrite
   (:type-prescription
    :corollary
    (stringp (mv-nth 0 (m1-basename-dirname-helper path))))
   (:type-prescription
    :corollary
    (true-listp (mv-nth 1 (m1-basename-dirname-helper path))))))

(defun m1-basename (path)
  (declare (xargs :guard (string-listp path)))
  (mv-let (basename dirname)
    (m1-basename-dirname-helper path)
    (declare (ignore dirname))
    basename))

(defun m1-dirname (path)
  (declare (xargs :guard (string-listp path)))
  (mv-let (basename dirname)
    (m1-basename-dirname-helper path)
    (declare (ignore basename))
    dirname))

(defun
    m1-mkdir (fs pathname)
  (declare
   (xargs
    :guard (and (m1-file-alist-p fs)
                (string-listp pathname))
    :guard-hints
    (("goal"
      :in-theory
      (disable
       (:rewrite m1-basename-dirname-helper-correctness-1))
      :use
      (:instance
       (:rewrite m1-basename-dirname-helper-correctness-1)
       (path pathname))))))
  (b* ((dirname (m1-dirname pathname))
       ;; It's OK to strip out the leading "" when the pathname begins with /,
       ;; but what about when it doesn't and the pathname is relative to the
       ;; current working directory?
       (dirname (if (and (consp dirname)
                         (equal (car dirname) ""))
                    (cdr dirname)
                  dirname))
       ((mv parent-dir errno)
        (find-file-by-pathname fs dirname))
       ((unless (or (atom dirname)
                    (and (equal errno 0)
                         (m1-directory-file-p parent-dir))))
        (mv fs -1 *enoent*))
       ((mv & errno)
        (find-file-by-pathname fs pathname))
       ((unless (not (equal errno 0)))
        (mv fs -1 *eexist*))
       (basename (m1-basename pathname))
       ((unless (equal (length basename) 11))
        (mv fs -1 *enametoolong*))
       (dir-ent
        (update-nth 11 (ash 1 4)
                    (append (string=>nats basename)
                            (nthcdr 11 (dir-ent-fix nil)))))
       (file (make-m1-file :dir-ent dir-ent
                           :contents nil))
       (pathname (append dirname (list basename)))
       ((mv fs error-code)
        (place-file-by-pathname fs pathname file))
       ((unless (equal error-code 0))
        (mv fs -1 error-code)))
    (mv fs 0 0)))

(defun
    m1-mknod (fs pathname)
  (declare
   (xargs
    :guard (and (m1-file-alist-p fs)
                (string-listp pathname))
    :guard-hints
    (("goal"
      :in-theory
      (disable
       (:rewrite m1-basename-dirname-helper-correctness-1))
      :use
      (:instance
       (:rewrite m1-basename-dirname-helper-correctness-1)
       (path pathname))))))
  (b* ((dirname (m1-dirname pathname))
       ;; It's OK to strip out the leading "" when the pathname begins with /,
       ;; but what about when it doesn't and the pathname is relative to the
       ;; current working directory?
       (dirname (if (and (consp dirname)
                         (equal (car dirname) ""))
                    (cdr dirname)
                  dirname))
       ((mv parent-dir errno)
        (find-file-by-pathname fs dirname))
       ((unless (or (atom dirname)
                    (and (equal errno 0)
                         (m1-directory-file-p parent-dir))))
        (mv fs -1 *enoent*))
       ((mv & errno)
        (find-file-by-pathname fs pathname))
       ((unless (not (equal errno 0)))
        (mv fs -1 *eexist*))
       (basename (m1-basename pathname))
       ((unless (equal (length basename) 11))
        (mv fs -1 *enametoolong*))
       (dir-ent (append (string=>nats basename)
                        (nthcdr 11 (dir-ent-fix nil))))
       (file (make-m1-file :dir-ent dir-ent
                           :contents nil))
       (pathname (append dirname (list basename)))
       ((mv fs error-code)
        (place-file-by-pathname fs pathname file))
       ((unless (equal error-code 0))
        (mv fs -1 error-code)))
    (mv fs 0 0)))
