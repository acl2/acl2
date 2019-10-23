(in-package "ACL2")

(include-book "test-stuff")
(include-book "abstract-separate")

(defun
    rm-list-extra-hypothesis
    (name-list)
  (declare (xargs :guard (string-listp name-list)))
  (b*
      (((when (atom name-list))
        t)
       (fat32-pathname (pathname-to-fat32-pathname
                        (coerce (car name-list) 'list)))
       ((unless (fat32-filename-list-p fat32-pathname))
        nil))
    (rm-list-extra-hypothesis (cdr name-list))))

(defthm rm-list-correctness-1-lemma-1
  (equal (mv-nth 1 (rm-list fat32-in-memory pathname-list 1))
         1))

(defthm
  rm-list-correctness-1-lemma-2
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (equal
     (mv-nth 1
             (hifat-find-file
              (mv-nth 0 (lofat-to-hifat fat32-in-memory))
              fat32-pathname))
     *enoent*)
    (equal (mv-nth 1 (lofat-to-hifat fat32-in-memory))
           0))
   (equal
    (mv-nth
     1
     (hifat-find-file
      (mv-nth
       0
       (lofat-to-hifat
        (mv-nth 0
                (rm-list fat32-in-memory
                         pathname-list exit-status))))
      fat32-pathname))
    *enoent*))
  :hints (("goal" :in-theory (e/d nil (hifat-find-file))
           :induct (rm-list fat32-in-memory
                            pathname-list exit-status))))

(defthm
  rm-list-correctness-1
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (member-equal pathname pathname-list)
    (equal (mv-nth 1
                   (rm-list fat32-in-memory
                            pathname-list exit-status))
           0)
    (rm-list-extra-hypothesis pathname-list)
    (equal
     (mv-nth '1
             (lofat-to-hifat fat32-in-memory))
     '0)
    (equal
     (mv-nth '1
             (lofat-to-hifat
              (mv-nth '0
                      (rm-list fat32-in-memory
                               pathname-list exit-status))))
     '0))
   (not
    (equal
     (mv-nth
      1
      (lofat-lstat
       (mv-nth 0
               (rm-list fat32-in-memory
                        pathname-list exit-status))
       (pathname-to-fat32-pathname (explode pathname))))
     0)))
  :hints
  (("goal"
    :in-theory (e/d ()
                    ((:rewrite take-of-take-split)
                     (:linear len-of-member-equal))))))

(defthm ls-list-correctness-1-lemma-1
  (implies (not
            (equal
             (mv-nth
              1
              (ls-list fat32-in-memory name-list exit-status))
             exit-status))
           (equal
            (mv-nth
             1
             (ls-list fat32-in-memory name-list exit-status))
            2))
  :rule-classes :linear)

;; Not currently used.
(defthmd ls-list-correctness-1-lemma-2
  (implies
   (not (equal (mv-nth 1
                       (lofat-lstat fat32-in-memory pathname))
               0))
   (equal (mv-nth 1
                  (lofat-lstat fat32-in-memory pathname))
          -1))
  :hints (("goal" :in-theory (enable lofat-lstat))))

(defthm
  ls-list-correctness-1
  (implies
   (and
    (member-equal pathname name-list)
    (not
     (equal
      (mv-nth 1
              (ls-list fat32-in-memory name-list exit-status))
      2)))
   (and
    (fat32-filename-list-p
     (pathname-to-fat32-pathname (explode pathname)))
    (equal
     (mv-nth
      1
      (lofat-lstat
       fat32-in-memory
       (pathname-to-fat32-pathname (explode pathname))))
     0))))

(defthm lstat-after-unlink-1
  (implies (and (lofat-fs-p fat32-in-memory)
                (fat32-filename-list-p pathname)
                (equal (mv-nth 1 (lofat-to-hifat fat32-in-memory))
                       0))
           (b* (((mv fat32-in-memory unlink-errno)
                 (lofat-unlink fat32-in-memory pathname))
                ((mv & lstat-errno)
                 (lofat-lstat fat32-in-memory pathname)))
             (implies (equal unlink-errno 0)
                      (equal lstat-errno -1))))
  :hints (("goal" :do-not-induct t)))

(defthm
  ls-1-after-rm-1
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (< 0
       (len (intersection-equal ls-pathnames rm-pathnames)))
    (rm-list-extra-hypothesis
     rm-pathnames)
    (equal
     (mv-nth
      '1
      (lofat-to-hifat
       (mv-nth
        '0
        (rm-list
         (mv-nth
          '0
          (string-to-lofat fat32-in-memory disk-image-string))
         rm-pathnames '0))))
     '0)
    (equal
     (mv-nth
      1
      (lofat-to-hifat
       (mv-nth 0
               (string-to-lofat fat32-in-memory disk-image-string))))
     0))
   (b* (((mv fat32-in-memory
             disk-image-string rm-exit-status)
         (rm-1 fat32-in-memory
               disk-image-string rm-pathnames))
        ((mv & & ls-exit-status)
         (ls-1 fat32-in-memory
               ls-pathnames disk-image-string)))
     (implies (equal rm-exit-status 0)
              (equal ls-exit-status 2))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (rm-1 ls-1)
                    ((:rewrite rm-list-correctness-1)
                     ls-list-correctness-1 nth
                     (:definition rm-list)))
    :use
    ((:instance
      (:rewrite rm-list-correctness-1)
      (pathname
       (nth 0
            (intersection-equal ls-pathnames rm-pathnames)))
      (exit-status 0)
      (pathname-list rm-pathnames)
      (fat32-in-memory
       (mv-nth
        0
        (string-to-lofat fat32-in-memory disk-image-string))))
     (:instance
      (:rewrite ls-list-correctness-1)
      (exit-status 0)
      (pathname
       (nth 0
            (intersection-equal ls-pathnames rm-pathnames)))
      (name-list ls-pathnames)
      (fat32-in-memory
       (mv-nth
        0
        (rm-list
         (mv-nth
          0
          (string-to-lofat fat32-in-memory disk-image-string))
         rm-pathnames 0))))))))

;; This guard conjecture takes 12 seconds...
(defund
  absfat-find-file-helper (fs relpath)
  (declare
   (xargs
    :guard (and (abs-file-alist-p fs)
                (fat32-filename-list-p relpath))
    :guard-hints
    (("goal" :in-theory (enable abs-file-alist-p
                                abs-file-p abs-file-fix)))))
  (b*
      (((when (atom relpath))
        (mv (make-abs-file) *enoent*))
       (head (car relpath))
       ((unless (consp (abs-assoc head fs)))
        (mv (make-abs-file) *enoent*))
       ((when (atom (cdr relpath)))
        (mv (mbe :exec (cdr (abs-assoc head fs))
                 :logic (abs-file-fix (cdr (abs-assoc head fs))))
            0))
       ((unless (abs-directory-file-p (cdr (abs-assoc head fs))))
        (mv (make-abs-file) *enotdir*)))
    (absfat-find-file-helper
     (abs-file->contents (cdr (abs-assoc head fs)))
     (cdr relpath))))

(defthm absfat-find-file-helper-correctness-1
  (mv-let
    (file retval)
    (absfat-find-file-helper fs relpath)
    (and (abs-file-p file) (natp retval)))
  :hints (("Goal" :in-theory (enable absfat-find-file-helper)) ))

(defund absfat-find-file (frame path)
  (declare (xargs :guard (and (fat32-filename-list-p path)
                              (frame-p frame))))
  (b*
      (((when (atom frame)) (mv (make-abs-file) *enoent*))
       (head-frame-val (cdar frame))
       ((mv file retval)
        (absfat-find-file-helper
         (frame-val->dir head-frame-val)
         (nthcdr (len (frame-val->path head-frame-val)) path)))
       ((unless (equal retval *enoent*)) (mv file retval)))
    (absfat-find-file (cdr frame) path)))

;; This theorem is important, but not yet proved...
#|
(defthm
  hifat-find-file-of-abs-collapse-1
  (implies
   (and (frame-p frame)
        (no-duplicatesp-equal (strip-cars frame))
        (abs-file-alist-p root)
        (no-duplicatesp-equal (abs-addrs root))
        (subsetp (abs-addrs root)
                 (frame-addrs-root frame))
        (abs-separate (frame-with-root root frame)))
   (b*
       (((mv fs result) (collapse root frame))
        ((mv file error-code)
         (absfat-find-file (frame-with-root root frame)
                           path)))
     (implies
      (equal result t)
      (and
       (equal error-code
              (mv-nth 1 (hifat-find-file fs path)))
       (equal (abs-directory-file-p file)
              (m1-directory-file-p
               (mv-nth 1 (hifat-find-file fs path)))))))))
|#
