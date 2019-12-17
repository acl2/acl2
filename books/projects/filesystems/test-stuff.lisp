(in-package "ACL2")

(include-book "lofat-syscalls")
(include-book "centaur/getopt/top" :dir :system)

(defoptions mkdir-opts
  :parents (demo2)
  :tag :demo2
  ((parents    "no error if existing, make parent directories as needed"
               booleanp
               :rule-classes :type-prescription
               :alias #\p)))

(defun mkdir-list (fs name-list exit-status)
  (b*
      (((when (atom name-list))
        (mv fs exit-status))
       (fat32-pathname
        (pathname-to-fat32-pathname (coerce (car name-list) 'list)))
       ;; It doesn't really matter for these purposes what the errno is. We're
       ;; not trying to match this program for its stderr output.
       ((mv fs retval &)
        (hifat-mkdir fs fat32-pathname))
       (exit-status (if (equal retval 0) exit-status 1)))
    (mkdir-list fs (cdr name-list) exit-status)))

(defoptions rm-opts
  :parents (demo2)
  :tag :demo2
  ((recursive    "Recursively delete a directory"
                 booleanp
                 :rule-classes :type-prescription
                 :alias #\r)))

(defun
  rm-list (fat32-in-memory name-list exit-status)
  (declare (xargs :stobjs fat32-in-memory
                  :guard (and (lofat-fs-p fat32-in-memory)
                              (string-listp name-list))))
  (b* (((when (atom name-list))
        (mv fat32-in-memory exit-status))
       (fat32-pathname (pathname-to-fat32-pathname
                        (coerce (car name-list) 'list)))
       ((mv fat32-in-memory retval &)
        (if (not (fat32-filename-list-p fat32-pathname))
            (mv fat32-in-memory 1 *enoent*)
          (lofat-unlink fat32-in-memory fat32-pathname)))
       (exit-status (if (equal retval 0) exit-status 1)))
    (rm-list fat32-in-memory (cdr name-list) exit-status)))

(defthm
  lofat-fs-p-of-rm-list
  (implies
   (and (lofat-fs-p fat32-in-memory))
   (lofat-fs-p (mv-nth 0
                       (rm-list fat32-in-memory
                                name-list exit-status)))))

(defund
  rm-1
  (fat32-in-memory disk-image-string rm-pathnames)
  (declare (xargs :guard (and (lofat-fs-p fat32-in-memory)
                              (string-listp rm-pathnames)
                              (stringp disk-image-string)
                              (>= (length disk-image-string) *initialbytcnt*))
                  :stobjs fat32-in-memory))
  (b* (((mv fat32-in-memory error-code)
        (string-to-lofat fat32-in-memory disk-image-string))
       ((unless (equal error-code 0))
        (mv fat32-in-memory disk-image-string 1))
       ((mv fat32-in-memory exit-status)
        (rm-list fat32-in-memory rm-pathnames 0))
       (disk-image-string (lofat-to-string fat32-in-memory)))
    (mv fat32-in-memory disk-image-string exit-status)))

(defthm
  rm-2-guard-lemma-1
  (implies
   (not (equal (mv-nth 1 (rm-list fs name-list exit-status))
               exit-status))
   (equal (mv-nth 1 (rm-list fs name-list exit-status))
          1)))

(defun rm-2 (fat32-in-memory state disk-path output-path rm-pathnames)
  (declare (xargs :stobjs (state fat32-in-memory)
                  :guard (and (fat32-in-memoryp fat32-in-memory)
                              (string-listp rm-pathnames)
                              (stringp disk-path)
                              (stringp output-path)
                              (state-p state))
                  :guard-hints (("Goal" :in-theory (e/d (rm-1)
                                                        (read-file-into-string2))))))
  (mbe :logic
       (b*
           ((disk-image-string (read-file-into-string disk-path))
            ((mv fat32-in-memory disk-image-string exit-status)
             (rm-1 fat32-in-memory disk-image-string rm-pathnames))
            ((unless (equal exit-status 0)) (mv fat32-in-memory state 1))
            ((mv channel state)
             (open-output-channel output-path
                                  :character state))
            ((when (null channel)) (mv fat32-in-memory state 1))
            (state
             (princ$ disk-image-string channel state))
            (state (close-output-channel channel state)))
         (mv fat32-in-memory state exit-status))
       :exec
       (b*
           (((mv fat32-in-memory error-code)
             (disk-image-to-lofat
              fat32-in-memory disk-path state))
            ((unless (equal error-code 0))
             (mv fat32-in-memory state 1))
            ((mv fat32-in-memory exit-status)
             (rm-list fat32-in-memory rm-pathnames 0))
            ((unless (equal exit-status 0)) (mv fat32-in-memory state 1))
            ((mv state error-code)
             (lofat-to-disk-image
              fat32-in-memory output-path state))
            (exit-status (if (equal error-code 0) exit-status 1)))
         (mv fat32-in-memory state exit-status))))

(defoptions rmdir-opts
  :parents (demo2)
  :tag :demo2
  ((parents    "no error if existing, make parent directories as needed"
               booleanp
               :rule-classes :type-prescription
               :alias #\p)))

(defun rmdir-list (fs name-list exit-status)
  (b*
      (((when (atom name-list))
        (mv fs exit-status))
       (fat32-pathname
        (pathname-to-fat32-pathname (coerce (car name-list) 'list)))
       ;; It doesn't really matter for these purposes what the errno is. We're
       ;; not trying to match this program for its stderr output.
       ((mv fs retval &)
        (hifat-rmdir fs fat32-pathname))
       (exit-status (if (equal retval 0) exit-status 1)))
    (rmdir-list fs (cdr name-list) exit-status)))

(defoptions wc-opts
  :parents (demo2)
  :tag :demo2
  ((bytes    "Count bytes"
             booleanp
             :rule-classes :type-prescription
             :alias #\c)
   (lines "Count lines"
          booleanp
          :rule-classes :type-prescription
          :alias #\l)
   (words "Count words"
          booleanp
          :rule-classes :type-prescription
          :alias #\w)))

(defun
  wc-helper
  (text nl nw nc beginning-of-word-p pos)
  (declare (xargs :measure (nfix (- (length text) pos))
                  :guard (and (stringp text)
                              (natp pos)
                              (natp nc)
                              (natp nw)
                              (natp nl)
                              (<= pos (length text)))))
  (if (zp (- (length text) pos))
      (mv nl nw nc)
      (b* ((c (char text pos))
           (nc (+ nc 1))
           (nl (if (equal c #\newline) (+ nl 1) nl))
           ((mv beginning-of-word-p nw)
            (if (or (equal c #\space)
                    (equal c #\newline)
                    (equal c #\tab))
                (mv t nw)
                (if beginning-of-word-p (mv nil (+ nw 1))
                    (mv beginning-of-word-p nw)))))
        (wc-helper text nl
                   nw nc beginning-of-word-p (+ pos 1)))))

(defthm
   wc-helper-correctness-1
   (implies (and (integerp pos)
                 (<= pos (length text))
                 (integerp nc))
            (equal (mv-nth 2
                           (wc-helper text nl nw nc beginning-of-word-p pos))
                   (+ nc (length text) (- pos)))))

(defund wc-1 (fat32-in-memory pathname)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (and (stringp pathname)
                (lofat-fs-p fat32-in-memory))
    :guard-hints
    (("goal" :in-theory
      (enable lofat-open lofat-lstat)))))
  (b*
      ((fat32-pathname (pathname-to-fat32-pathname (coerce pathname 'list)))
       ;; It would be nice to eliminate this check by proving a theorem, but
       ;; it's not at all simple to ensure that a string given to us is free of
       ;; filenames indicating deleted files and such which are not allowed in
       ;; a pathname satisfying fat32-filename-list-p.
       ((unless (fat32-filename-list-p fat32-pathname))
        (mv 0 0 0 1))
       ((mv val error-code &)
        (lofat-lstat fat32-in-memory fat32-pathname))
       ((unless (equal error-code 0))
        (mv 0 0 0 error-code))
       (file-length (struct-stat->st_size val))
       ((mv fd-table file-table fd &)
        (lofat-open fat32-pathname nil nil))
       ((mv file-text file-read-length &)
        (lofat-pread
         fd file-length 0 fat32-in-memory fd-table file-table))
       ((unless (equal file-read-length file-length))
        (mv 0 0 0 1))
       ((mv nl nw nc)
        (wc-helper file-text 0 0 0 t 0)))
    (mv nl nw nc 0)))

(defoptions ls-opts
  :parents (demo2)
  :tag :demo2
  ((directory    "Recursively delete a directory"
                 booleanp
                 :rule-classes :type-prescription
                 :alias #\d)))

(defun ls-list (fat32-in-memory name-list exit-status)
  (declare (xargs :stobjs fat32-in-memory
                  :guard (and
                          (lofat-fs-p fat32-in-memory) (string-listp name-list))))
  (b*
      (((when (atom name-list)) (mv nil exit-status))
       (fat32-pathname
        (pathname-to-fat32-pathname (coerce (car name-list) 'list)))
       ;; It doesn't really matter for these purposes what the errno is. We're
       ;; not trying to match this program for its stderr output.
       ((unless
            (fat32-filename-list-p fat32-pathname))
        (ls-list fat32-in-memory (cdr name-list) 2))
       ((mv & retval &)
        (lofat-lstat fat32-in-memory fat32-pathname))
       ((unless (equal retval 0))
        (ls-list fat32-in-memory (cdr name-list) 2))
       ((mv tail-list exit-status) (ls-list fat32-in-memory (cdr name-list) exit-status)))
    (mv (cons (car name-list) tail-list) exit-status)))

(defund
  ls-1
  (fat32-in-memory ls-pathnames disk-image-string)
  (declare (xargs :guard (and (lofat-fs-p fat32-in-memory)
                              (string-listp ls-pathnames)
                              (stringp disk-image-string)
                              (>= (length disk-image-string)
                                  *initialbytcnt*))
                  :stobjs fat32-in-memory))
  (b* (((mv fat32-in-memory error-code)
        (string-to-lofat fat32-in-memory disk-image-string))
       ((unless (equal error-code 0))
        (mv fat32-in-memory nil 2))
       ((mv ls-list exit-status)
        (ls-list fat32-in-memory ls-pathnames 0)))
    (mv fat32-in-memory ls-list exit-status)))

(defun
  ls-2
  (fat32-in-memory state ls-pathnames disk-path)
  (declare
   (xargs :stobjs (state fat32-in-memory)
          :guard (and (fat32-in-memoryp fat32-in-memory)
                      (state-p state)
                      (string-listp ls-pathnames)
                      (stringp disk-path))
          :guard-hints
          (("goal" :in-theory (e/d (ls-1)
                                   (read-file-into-string2))))))
  (mbe
   :logic
   (b* ((disk-image-string (read-file-into-string disk-path))
        ((mv fat32-in-memory ls-list exit-status)
         (ls-1 fat32-in-memory
               ls-pathnames disk-image-string)))
     (mv fat32-in-memory ls-list exit-status))
   :exec
   (b* (((mv fat32-in-memory error-code)
         (disk-image-to-lofat fat32-in-memory disk-path state))
        ((unless (equal error-code 0))
         (mv fat32-in-memory nil 2))
        ((mv ls-list exit-status)
         (ls-list fat32-in-memory ls-pathnames 0)))
     (mv fat32-in-memory ls-list exit-status))))

(defoptions truncate-opts
  :parents (demo2)
  :tag :demo2
  ((size       "set or adjust the file size by SIZE bytes"
               natp
               :rule-classes :type-prescription
               :alias #\s
               :default 0)))

(defun
  truncate-list (fat32-in-memory name-list size exit-status)
  (declare (xargs :stobjs fat32-in-memory
                  :guard (and (lofat-fs-p fat32-in-memory)
                              (string-listp name-list)
                              (natp size))))
  (b* (((when (atom name-list))
        (mv fat32-in-memory exit-status))
       (fat32-pathname (pathname-to-fat32-pathname
                        (coerce (car name-list) 'list)))
       ((mv fat32-in-memory retval &)
        (if (not (fat32-filename-list-p fat32-pathname))
            (mv fat32-in-memory 1 *enoent*)
          (lofat-truncate fat32-in-memory fat32-pathname size)))
       (exit-status (if (equal retval 0) exit-status 1)))
    (truncate-list fat32-in-memory (cdr name-list) size exit-status)))

(defun compare-disks (image-path1 image-path2 fat32-in-memory state)
  (declare (xargs :stobjs (fat32-in-memory state)
                  :guard (and (fat32-in-memoryp fat32-in-memory)
                              (stringp image-path1)
                              (stringp image-path2))
                  :guard-hints (("Goal" :in-theory (disable
                                                    read-file-into-string2)))))
  (b*
      (((mv fat32-in-memory error-code1)
        (disk-image-to-lofat
         fat32-in-memory image-path1 state))
       ((mv fs-ref error-code2)
        (if
            (not (equal error-code1 0))
            (mv nil *EIO*)
          (lofat-to-hifat fat32-in-memory)))
       ((mv fat32-in-memory error-code3)
        (disk-image-to-lofat
         fat32-in-memory image-path2 state))
       ((mv fs error-code4)
        (if
            (or (not (equal error-code1 0)) (not (equal error-code3 0)))
            (mv nil *EIO*)
          (lofat-to-hifat fat32-in-memory)))
       ((unless (or (equal error-code1 0) (equal error-code3 0)))
        (mv t fat32-in-memory))
       ((unless (and (equal error-code1 0) (equal error-code3 0)))
        (mv nil fat32-in-memory))
       ((unless (or (equal error-code2 0) (equal error-code4 0)))
        (mv t fat32-in-memory))
       ((unless (and (equal error-code2 0) (equal error-code4 0)))
        (mv nil fat32-in-memory))
       ((unless (hifat-equiv fs-ref fs))
        (mv nil fat32-in-memory)))
    (mv t fat32-in-memory)))

(defthm
  compare-disks-correctness-1-lemma-1
  (implies
   (not (stringp str))
   (not (equal (mv-nth 1 (string-to-lofat-nx str))
               0)))
  :hints (("goal" :in-theory (enable string-to-lofat string-to-lofat-nx))))

(defthm
  compare-disks-correctness-1
  (let*
      ((str1 (read-file-into-string image-path1))
       (str2 (read-file-into-string image-path2)))
    (implies
     (fat32-in-memoryp fat32-in-memory)
     (equal
      (mv-nth 0
              (compare-disks image-path1
                             image-path2 fat32-in-memory state))
      (eqfat str1 str2))))
  :hints
  (("goal"
    :in-theory
    (e/d (eqfat string-to-lofat-ignore-lemma-14
                lofat-equiv)
         (read-file-into-string2 (:e string-to-lofat-nx)))
    :expand (hide (string-to-lofat-nx nil)))))
