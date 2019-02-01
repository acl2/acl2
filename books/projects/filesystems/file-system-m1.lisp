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
(include-book "std/strings/case-conversion" :dir :system)

(include-book "insert-text")
(include-book "fat32")

;; This was taken from rtl/rel9/arithmetic/top with thanks.
(defthm product-less-than-zero
  (implies (case-split (or (not (complex-rationalp x))
                           (not (complex-rationalp y))))
           (equal (< (* x y) 0)
                  (if (< x 0)
                      (< 0 y)
                      (if (equal 0 x)
                          nil
                          (if (not (acl2-numberp x))
                              nil (< y 0)))))))

(defthm
  down-alpha-p-of-upcase-char
  (not (str::down-alpha-p (str::upcase-char x)))
  :hints
  (("goal"
    :in-theory (enable str::upcase-char str::down-alpha-p))))

(defthm
  charlist-has-some-down-alpha-p-of-upcase-charlist
  (not (str::charlist-has-some-down-alpha-p
        (str::upcase-charlist x)))
  :hints
  (("goal"
    :in-theory (enable str::charlist-has-some-down-alpha-p
                       str::upcase-charlist))))

(defund dir-ent-p (x)
  (declare (xargs :guard t))
  (and (unsigned-byte-listp 8 x)
       (equal (len x) *ms-dir-ent-length*)))

(defthm dir-ent-p-correctness-1
  (implies (dir-ent-p x)
           (not (stringp x)))
  :hints (("goal" :in-theory (enable dir-ent-p)))
  :rule-classes :forward-chaining)

(defthm dir-ent-p-of-update-nth
  (implies (dir-ent-p l)
           (equal (dir-ent-p (update-nth key val l))
                  (and (< (nfix key) *ms-dir-ent-length*)
                       (unsigned-byte-p 8 val))))
  :hints (("goal" :in-theory (enable dir-ent-p))))

(defthm dir-ent-p-of-append
  (equal (dir-ent-p (binary-append x y))
         (and (equal (+ (len x) (len y))
                     *ms-dir-ent-length*)
              (unsigned-byte-listp 8 y)
              (unsigned-byte-listp 8 (true-list-fix x))))
  :hints (("goal" :in-theory (enable dir-ent-p))))

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
   (xargs :guard (dir-ent-p dir-ent)
          :guard-hints (("Goal" :in-theory (enable dir-ent-p)))))
  (combine32u (nth 21 dir-ent)
              (nth 20 dir-ent)
              (nth 27 dir-ent)
              (nth 26 dir-ent)))

(defun dir-ent-file-size (dir-ent)
  (declare
   (xargs :guard (dir-ent-p dir-ent)
          :guard-hints (("Goal" :in-theory (enable dir-ent-p)))))
  (combine32u (nth 31 dir-ent)
              (nth 30 dir-ent)
              (nth 29 dir-ent)
              (nth 28 dir-ent)))

(defund
  dir-ent-set-first-cluster-file-size
    (dir-ent first-cluster file-size)
  (declare (xargs :guard (and (dir-ent-p dir-ent)
                              (fat32-masked-entry-p first-cluster)
                              (unsigned-byte-p 32 file-size))
                  :guard-hints (("Goal" :in-theory (enable dir-ent-p)))))
  (let
      ((dir-ent (dir-ent-fix dir-ent))
       (first-cluster (fat32-masked-entry-fix first-cluster))
       (file-size (if (not (unsigned-byte-p 32 file-size)) 0 file-size)))
   (append
    (subseq dir-ent 0 20)
    (list* (logtail 16 (loghead 24 first-cluster))
           (logtail 24 first-cluster)
           (append (subseq dir-ent 22 26)
                   (list (loghead 8 first-cluster)
                         (logtail 8 (loghead 16 first-cluster))
                         (loghead 8 file-size)
                         (logtail 8 (loghead 16 file-size))
                         (logtail 16 (loghead 24 file-size))
                         (logtail 24 file-size)))))))

(defthm
  dir-ent-first-cluster-of-dir-ent-set-first-cluster-file-size
  (implies (and (dir-ent-p dir-ent)
                (fat32-masked-entry-p first-cluster)
                (natp file-size))
           (equal (dir-ent-first-cluster
                   (dir-ent-set-first-cluster-file-size
                    dir-ent first-cluster file-size))
                  first-cluster))
  :hints
  (("goal" :in-theory (e/d (dir-ent-set-first-cluster-file-size)
                           (loghead logtail)))))

(defthm
  dir-ent-file-size-of-dir-ent-set-first-cluster-file-size
  (implies (and (dir-ent-p dir-ent)
                (unsigned-byte-p 32 file-size)
                (natp first-cluster))
           (equal (dir-ent-file-size
                   (dir-ent-set-first-cluster-file-size
                    dir-ent first-cluster file-size))
                  file-size))
  :hints
  (("goal" :in-theory (e/d (dir-ent-set-first-cluster-file-size)
                           (loghead logtail)))))

(encapsulate
  ()

  (local (include-book "ihs/logops-lemmas" :dir :system))

  (defthm dir-ent-set-first-cluster-file-size-correctness-1
    (dir-ent-p (dir-ent-set-first-cluster-file-size dir-ent first-cluster file-size))
    :hints (("goal" :in-theory (e/d (dir-ent-p
                                     dir-ent-set-first-cluster-file-size
                                     fat32-masked-entry-fix fat32-masked-entry-p)
                                    (loghead logtail))))))

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
            :guard-hints (("Goal" :in-theory (e/d (dir-ent-p) (unsigned-byte-p))
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

(defthm
  m1-file-alist-p-of-remove1-assoc-equal
  (implies (m1-file-alist-p fs)
           (m1-file-alist-p (remove1-assoc-equal key fs))))

(defun m1-directory-file-p (file)
  (declare (xargs :guard t))
  (and
   (m1-file-p file)
   (m1-file-alist-p (m1-file->contents file))))

(fty::defprod
 struct-stat
 ;; Currently, this is the only thing I can decipher.
 ((st_size natp :default 0)))

(fty::defprod
 struct-statfs
 ((f_type natp :default 0)
  (f_bsize natp :default 0)
  (f_blocks natp :default 0)
  (f_bfree natp :default 0)
  (f_bavail natp :default 0)
  (f_files natp :default 0)
  (f_ffree natp :default 0)
  (f_fsid natp :default 0)
  (f_namelen natp :default 72)))

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
                     (pathname str::pathname-equiv))))))

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
                     (pathname str::pathname-equiv))))))

(defcong m1-file-equiv equal
  (place-file-by-pathname fs pathname file) 3)

;; This function should continue to take pathnames which refer to top-level
;; fs... but what happens when "." and ".." appear in a pathname? We'll have to
;; modify the code to deal with that.
(defun
    remove-file-by-pathname
    (fs pathname)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (string-listp pathname))
                  :measure (acl2-count pathname)))
  (b*
      ((fs (m1-file-alist-fix fs))
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
              (remove-file-by-pathname
               (m1-file->contents (cdr alist-elem))
               (cdr pathname))
              (mv
               (put-assoc-equal
                name
                (make-m1-file
                 :dir-ent (m1-file->dir-ent (cdr alist-elem))
                 :contents new-contents)
                fs)
               error-code))
          (if (consp (cdr pathname))
              (mv fs *enotdir*)
            (mv (remove1-assoc-equal name fs) 0)))
      ;; if it's not there, it can't be removed
      (mv fs *enoent*))))

(defthm
  remove-file-by-pathname-correctness-1
  (mv-let (fs error-code)
    (remove-file-by-pathname fs pathname)
    (and (m1-file-alist-p fs)
         (integerp error-code)))
  :hints
  (("goal" :induct (remove-file-by-pathname fs pathname))))

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
     fd-table-index 0)))

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
  (declare (xargs :guard (string-listp path)
                  :guard-hints (("Goal" :in-theory (disable
                                                    make-list-ac-removal)))
                  :guard-debug t))
  (b*
      (((when (atom path))
        (mv *current-dir-fat32-name* (list *current-dir-fat32-name*)))
       (coerced-basename
        (if
            (or (atom (cdr path))
                (and (not (streqv (car path) ""))
                     (atom (cddr path))
                     (streqv (cadr path) "")))
            (coerce (str-fix (car path)) 'list)
          (coerce (str-fix (cadr path)) 'list)))
       (basename
        (coerce
         (append
          (take (min 11 (len coerced-basename)) coerced-basename)
          (make-list
           (nfix (- 11 (len coerced-basename)))
           :initial-element (code-char 0)))
         'string))
       ((when (or (atom (cdr path))
                  (and (not (streqv (car path) ""))
                       (atom (cddr path))
                       (streqv (cadr path) ""))))
        (mv
         basename
         (list *current-dir-fat32-name*)))
       ((when (atom (cddr path)))
        (mv basename
            (list (str-fix (car path))))))
    (mv-let (tail-basename tail-dirname)
      (m1-basename-dirname-helper (cdr path))
      (mv tail-basename
          (list* (str-fix (car path))
                 tail-dirname)))))

(defthm
  m1-basename-dirname-helper-correctness-1
  (mv-let (basename dirname)
    (m1-basename-dirname-helper path)
    (and (stringp basename)
         (equal (len (explode basename)) 11)
         (string-listp dirname)))
  :hints
  (("goal" :induct (m1-basename-dirname-helper path)
    :in-theory (enable m1-basename-dirname-helper)))
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
                         (equal (car dirname) *empty-fat32-name*))
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

(defthm
  m1-unlink-guard-lemma-1
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
;; #xe5, which signifies a deleted file, its the file length changed to 0, and
;; the first cluster changed to 0. This may even hold for other directories
;; than root.
(defun
    m1-unlink (fs pathname)
  (declare
   (xargs
    :guard (and (m1-file-alist-p fs)
                (string-listp pathname))
    :guard-debug t
    :guard-hints
    (("goal"
      :in-theory
      (disable
       (:rewrite m1-basename-dirname-helper-correctness-1)
       return-type-of-string=>nats update-nth)
      :use
      ((:instance
        (:rewrite m1-basename-dirname-helper-correctness-1)
        (path pathname))
       (:instance return-type-of-string=>nats
                  (string
                   (mv-nth 0
                           (m1-basename-dirname-helper pathname)))))))))
  (b* ((dirname (m1-dirname pathname))
       ;; It's OK to strip out the leading "" when the pathname begins with /,
       ;; but what about when it doesn't and the pathname is relative to the
       ;; current working directory?
       (dirname (if (and (consp dirname)
                         (or
                          (equal (car dirname) *empty-fat32-name*)
                          (equal (car dirname) *current-dir-fat32-name*)))
                    (cdr dirname)
                  dirname))
       ;; ((mv parent-dir errno)
       ;;  (find-file-by-pathname fs dirname))
       ;; ((unless (or (atom dirname)
       ;;              (and (equal errno 0)
       ;;                   (m1-directory-file-p parent-dir))))
       ;;  (mv fs -1 *enoent*))
       ((mv file errno)
        (find-file-by-pathname fs pathname))
       ((unless (equal errno 0))
        (mv fs -1 *enoent*))
       (basename (m1-basename pathname))
       (pathname (append dirname (list basename)))
       ((mv fs error-code)
        (remove-file-by-pathname fs pathname))
       ((unless (equal error-code 0))
        (mv fs -1 error-code))
       ;; the byte #xe5 marks deleted files, according to the spec
       (coerced-basename-after-deletion (update-nth 0 #xe5
                                                    (string=>nats basename)))
       (dir-ent-after-deletion
        (append coerced-basename-after-deletion
                (nthcdr 11 (m1-file->dir-ent file))))
       ;; zeroing out the first cluster and file size
       (dir-ent-after-deletion
        (dir-ent-set-first-cluster-file-size
         dir-ent-after-deletion 0 0))
       (file-after-deletion
        (make-m1-file :dir-ent dir-ent-after-deletion
                      :contents nil))
       (pathname (append dirname (list (nats=>string
                                        coerced-basename-after-deletion))))
       ((mv fs error-code)
        (place-file-by-pathname fs pathname file-after-deletion))
       ((unless (equal error-code 0))
        (mv fs -1 error-code)))
    (mv fs 0 0)))

(defun
    name-to-fat32-name-helper
    (character-list n)
  (declare
   (xargs :guard (and (natp n)
                      (character-listp character-list))))
  (if (zp n)
      nil
    (if (atom character-list)
        (make-list n :initial-element #\space)
      (cons (str::upcase-char (car character-list))
            (name-to-fat32-name-helper (cdr character-list)
                                     (- n 1))))))

(defthm
  len-of-name-to-fat32-name-helper
  (equal (len (name-to-fat32-name-helper character-list n))
         (nfix n)))

;; (defthm name-to-fat32-name-helper-correctness-1
;;   (implies (member x (name-to-fat32-name-helper
;;                       character-list n))
;;            (or (equal x #\space) (str::up-alpha-p x))))

(defthm
  character-listp-of-name-to-fat32-name-helper
  (character-listp (name-to-fat32-name-helper character-list n))
  :hints (("goal" :in-theory (disable make-list-ac-removal))))

(defun
    name-to-fat32-name (character-list)
  (declare (xargs :guard (character-listp character-list)))
  (b*
      (((when (equal (coerce character-list 'string) *current-dir-name*))
        (coerce *current-dir-fat32-name* 'list))
       ((when (equal (coerce character-list 'string) *parent-dir-name*))
        (coerce *parent-dir-fat32-name* 'list))
       (dot-and-later-characters (member #\. character-list))
       (characters-before-dot
        (take (- (len character-list) (len dot-and-later-characters))
              character-list))
       (normalised-characters-before-dot
        (name-to-fat32-name-helper characters-before-dot 8))
       ((when (atom dot-and-later-characters))
        (append normalised-characters-before-dot
                (make-list 3 :initial-element #\space)))
       (characters-after-dot (cdr dot-and-later-characters))
       (second-dot-and-later-characters (member #\. characters-after-dot))
       (extension (take (- (len characters-after-dot)
                           (len second-dot-and-later-characters))
                        characters-after-dot))
       (normalised-extension
        (name-to-fat32-name-helper extension 3)))
    (append normalised-characters-before-dot normalised-extension)))

(assert-event
 (and
  (equal (name-to-fat32-name (coerce "6chars" 'list))
         (coerce "6CHARS     " 'list))
  (equal (name-to-fat32-name (coerce "6chars.h" 'list))
         (coerce "6CHARS  H  " 'list))
  (equal (name-to-fat32-name (coerce "6chars.txt" 'list))
         (coerce "6CHARS  TXT" 'list))
  (equal (name-to-fat32-name (coerce "6chars.6chars" 'list))
         (coerce "6CHARS  6CH" 'list))
  (equal (name-to-fat32-name (coerce "6chars.6ch" 'list))
         (coerce "6CHARS  6CH" 'list))
  (equal (name-to-fat32-name (coerce "11characters.6chars" 'list))
         (coerce "11CHARAC6CH" 'list))
  (equal (name-to-fat32-name (coerce "11characters.1.1.1" 'list))
         (coerce "11CHARAC1  " 'list))
  (equal (name-to-fat32-name (coerce "11characters.1.1" 'list))
         (coerce "11CHARAC1  " 'list))))

(defun
  fat32-name-to-name-helper
  (character-list n)
  (declare (xargs :guard (and (natp n)
                              (character-listp character-list)
                              (<= n (len character-list)))))
  (if (zp n)
      nil
      (if (equal (nth (- n 1) character-list)
                 #\space)
          (fat32-name-to-name-helper character-list (- n 1))
          (str::downcase-charlist (take n character-list)))))

(defthm
  character-listp-of-fat32-name-to-name-helper
  (character-listp
   (fat32-name-to-name-helper
    character-list n)))

(defun fat32-name-to-name (character-list)
  (declare (xargs :guard (and (character-listp character-list)
                              (equal (len character-list) 11))))
  (b*
      (((when (equal (coerce character-list 'string) *current-dir-fat32-name*))
        (coerce *current-dir-name* 'list))
       ((when (equal (coerce character-list 'string) *parent-dir-fat32-name*))
        (coerce *parent-dir-name* 'list))
       (characters-before-dot
        (fat32-name-to-name-helper (take 8 character-list) 8))
       (characters-after-dot
        (fat32-name-to-name-helper (subseq character-list 8 11) 3))
       ((when (atom characters-after-dot))
        characters-before-dot))
    (append characters-before-dot (list #\.) characters-after-dot)))

(assert-event
 (and
  (equal (fat32-name-to-name (coerce "6CHARS     " 'list))
         (coerce "6chars" 'list))
  (equal (fat32-name-to-name (coerce "6CHARS  H  " 'list))
         (coerce "6chars.h" 'list))
  (equal (fat32-name-to-name (coerce "6CHARS  TXT" 'list))
         (coerce "6chars.txt" 'list))
  (equal (fat32-name-to-name (coerce "6CHARS  6CH" 'list))
         (coerce "6chars.6ch" 'list))
  (equal (fat32-name-to-name (coerce "11CHARAC6CH" 'list))
         (coerce "11charac.6ch" 'list))
  (equal (fat32-name-to-name (coerce "11CHARAC1  " 'list))
         (coerce "11charac.1" 'list))))

(defun pathname-to-fat32-pathname (character-list)
  (declare (xargs :guard (character-listp character-list)))
  (b*
      ((slash-and-later-characters
        (member #\/ character-list))
       (characters-before-slash (take (- (len character-list)
                                         (len slash-and-later-characters))
                                      character-list))
       ((when (atom slash-and-later-characters))
        (list
         (coerce (name-to-fat32-name characters-before-slash) 'string))))
    (cons
     (coerce (name-to-fat32-name characters-before-slash) 'string)
     (pathname-to-fat32-pathname (cdr slash-and-later-characters)))))

(assert-event
 (and
  (equal (pathname-to-fat32-pathname (coerce "/bin/mkdir" 'list))
         (list "           " "BIN        " "MKDIR      "))
  (equal (pathname-to-fat32-pathname (coerce "books/build/cert.pl" 'list))
   (list "BOOKS      " "BUILD      " "CERT    PL "))))

(defun fat32-pathname-to-name (string-list)
  ;; (declare (xargs :guard (string-listp string-list)))
  (if (atom string-list)
      nil
    (append (fat32-name-to-name (coerce (car string-list) 'list))
            (if (atom (cdr string-list))
                nil
              (list* #\/
                     (fat32-pathname-to-name (cdr string-list)))))))

(assert-event
 (and
  (equal (coerce (fat32-pathname-to-name (list "BOOKS      " "BUILD      "
                                               "CERT    PL ")) 'string)
         "books/build/cert.pl")
  (equal (coerce (fat32-pathname-to-name (list "           " "BIN        "
                                               "MKDIR      ")) 'string)
         "/bin/mkdir")))

(defthm character-listp-of-fat32-pathname-to-name
  (character-listp (fat32-pathname-to-name string-list)))

(defun m1-dir-subsetp (m1-file-alist1 m1-file-alist2)
  (declare
   (xargs
    :guard (and (m1-file-alist-p m1-file-alist1)
                (m1-file-alist-p m1-file-alist2))
    :hints (("goal" :in-theory (enable m1-file->contents)))))
  (b* (((when (atom m1-file-alist1))
        t)
       ((when (or (atom (car m1-file-alist1))
                  (not (stringp (car (car m1-file-alist1))))))
        (and (member-equal (car m1-file-alist1)
                           m1-file-alist2)
             (m1-dir-subsetp
              (cdr m1-file-alist1)
              m1-file-alist2)))
       (name (caar m1-file-alist1))
       (file1 (cdar m1-file-alist1))
       ((unless (consp (assoc-equal name m1-file-alist2)))
        nil)
       (file2 (cdr (assoc-equal name m1-file-alist2))))
    (if (not (m1-directory-file-p file1))
        (and (not (m1-directory-file-p file2))
             (m1-dir-subsetp (cdr m1-file-alist1) m1-file-alist2)
             (equal (m1-file->contents file1)
                    (m1-file->contents file2)))
      (and (m1-directory-file-p file2)
           (m1-dir-subsetp (cdr m1-file-alist1) m1-file-alist2)
           (m1-dir-subsetp (m1-file->contents file1)
                           (m1-file->contents file2))))))

(defun m1-file-no-dups-p (m1-file-alist)
  (declare
   (xargs
    :guard (m1-file-alist-p m1-file-alist)
    :hints (("goal" :in-theory (enable m1-file->contents)))))
  (cond ((atom m1-file-alist)
         t)
        ((not (m1-file-no-dups-p (cdr m1-file-alist)))
         nil)
        ((or (atom (car m1-file-alist))
             (not (stringp (car (car m1-file-alist)))))
         (not (member-equal (car m1-file-alist)
                            (cdr m1-file-alist))))
        ((assoc-equal (caar m1-file-alist) (cdr m1-file-alist))
         nil)
        ((m1-directory-file-p (cdar m1-file-alist))
         (m1-file-no-dups-p (m1-file->contents (cdar m1-file-alist))))
        (t t)))

(defun m1-dir-equiv (m1-file-alist1 m1-file-alist2)
  (declare (xargs :guard t))
  (or (equal m1-file-alist1 m1-file-alist2)
      (let ((good1 (and (m1-file-alist-p m1-file-alist1)
                        (m1-file-no-dups-p m1-file-alist1)))
            (good2 (and (m1-file-alist-p m1-file-alist2)
                        (m1-file-no-dups-p m1-file-alist2))))
        (cond ((not good1) (not good2)) ; all bad objects are equivalent
              ((not good2) nil) ; one good, one bad; hence, not equivalent
              (t                ; both good
               (and (m1-dir-subsetp m1-file-alist1 m1-file-alist2)
                    (m1-dir-subsetp m1-file-alist2 m1-file-alist1)))))))

(defthm m1-dir-subsetp-preserves-assoc-equal
  (implies (and (m1-dir-subsetp x y)
                (stringp file)
                (consp (assoc-equal file x)))
           (consp (assoc-equal file y))))

(defthm
  m1-dir-subsetp-transitive-lemma-1
  (implies
   (and (m1-file-alist-p y)
        (consp (assoc-equal key y))
        (m1-dir-subsetp y z))
   (iff (m1-directory-file-p (cdr (assoc-equal key z)))
        (m1-directory-file-p (cdr (assoc-equal key y)))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (m1-file-alist-p y)
          (consp (assoc-equal key y))
          (m1-dir-subsetp y z)
          (m1-directory-file-p (cdr (assoc-equal key y))))
     (m1-directory-file-p (cdr (assoc-equal key z)))))))

(defthm
  m1-dir-subsetp-transitive-lemma-2
  (implies (and (m1-file-alist-p z)
                (m1-file-no-dups-p z)
                (consp (assoc-equal key z))
                (m1-directory-file-p (cdr (assoc-equal key z))))
           (m1-file-no-dups-p
            (m1-file->contents (cdr (assoc-equal key z))))))

(defthm
  m1-dir-subsetp-transitive-lemma-3
  (implies (and (m1-file-alist-p y)
                (consp (assoc-equal key y))
                (m1-directory-file-p (cdr (assoc-equal key y)))
                (m1-dir-subsetp y z))
           (m1-dir-subsetp
            (m1-file->contents (cdr (assoc-equal key y)))
            (m1-file->contents (cdr (assoc-equal key z))))))

(defthm
  m1-dir-subsetp-transitive-lemma-4
  (implies
   (and (m1-file-alist-p y)
        (consp (assoc-equal key y))
        (not (m1-directory-file-p (cdr (assoc-equal key y))))
        (m1-dir-subsetp y z))
   (equal (m1-file->contents (cdr (assoc-equal key y)))
          (m1-file->contents (cdr (assoc-equal key z))))))

(defthm
  m1-dir-subsetp-transitive
  (implies (and (m1-file-alist-p x)
                (m1-file-no-dups-p x)
                (m1-file-alist-p y)
                (m1-file-no-dups-p y)
                (m1-file-alist-p z)
                (m1-file-no-dups-p z)
                (m1-dir-subsetp x y)
                (m1-dir-subsetp y z))
           (m1-dir-subsetp x z))
  :hints
  (("subgoal *1/9'''"
    :in-theory (disable m1-dir-subsetp-transitive-lemma-1)
    :use (:instance m1-dir-subsetp-transitive-lemma-1
                    (key (car (car x)))))
   ("subgoal *1/6'''"
    :in-theory (disable m1-dir-subsetp-transitive-lemma-1)
    :use (:instance m1-dir-subsetp-transitive-lemma-1
                    (key (car (car x)))))))

(defequiv
  m1-dir-equiv)
