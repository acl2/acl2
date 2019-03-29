(in-package "ACL2")

(include-book "lofat")
(include-book "m1-syscalls")
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
        (m1-mkdir fs fat32-pathname))
       (exit-status (if (equal retval 0) exit-status 1)))
    (mkdir-list fs (cdr name-list) exit-status)))

(defoptions rm-opts
  :parents (demo2)
  :tag :demo2
  ((recursive    "Recursively delete a directory"
                 booleanp
                 :rule-classes :type-prescription
                 :alias #\r)))

(defun rm-list (fs r name-list exit-status)
  (b*
      (((when (atom name-list))
        (mv fs exit-status))
       (fat32-pathname
        (pathname-to-fat32-pathname (coerce (car name-list) 'list)))
       ;; It doesn't really matter for these purposes what the errno is. We're
       ;; not trying to match this program for its stderr output.
       ((mv fs retval &)
        (if r
            (m1-unlink-recursive fs fat32-pathname)
          (m1-unlink fs fat32-pathname)))
       (exit-status (if (equal retval 0) exit-status 1)))
    (rm-list fs r (cdr name-list) exit-status)))

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
        (m1-rmdir fs fat32-pathname))
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

(defun wc-helper (text nl nw nc beginning-of-word-p pos)
  (declare (xargs :measure (nfix (- (length text) pos))))
  (if
      (zp (- (length text) pos))
      (mv nl nw nc)
    (b*
        ((c (char text pos))
         (nc (+ nc 1))
         (nl (if (equal c #\newline) (+ nl 1) nl))
         ((mv beginning-of-word-p nw)
          (if (or (equal c #\space) (equal c #\newline) (equal c #\tab))
              (mv t nw)
            (if beginning-of-word-p
                (mv nil (+ nw 1))
              (mv beginning-of-word-p nw)))))
      (wc-helper text nl nw nc beginning-of-word-p (+ pos 1)))))

(defun compare-disks (image-path1 image-path2 fat32-in-memory state)
  (declare (xargs :stobjs (fat32-in-memory state)
                  :guard-debug t
                  :guard (and (fat32-in-memoryp fat32-in-memory)
                              (stringp image-path1)
                              (stringp image-path2))
                  :guard-hints (("Goal" :in-theory (disable
                                                    read-file-into-string2)) )
                  :otf-flg t))
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
      (mv (good-bye 0) fat32-in-memory))
     ((unless (and (equal error-code1 0) (equal error-code3 0)))
      (mv (good-bye 1) fat32-in-memory))
     ((unless (or (equal error-code2 0) (equal error-code4 0)))
      (mv (good-bye 0) fat32-in-memory))
     ((unless (and (equal error-code2 0) (equal error-code4 0)))
      (mv (good-bye 1) fat32-in-memory))
     ((unless (hifat-equiv fs-ref fs))
      (mv (good-bye 1) fat32-in-memory)))
  (mv (good-bye 0) fat32-in-memory)))
