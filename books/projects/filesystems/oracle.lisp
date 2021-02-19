(in-package "ACL2")

;  oracle.lisp                                         Mihir Mehta

(include-book "lofat-syscalls")
(include-book "abs-syscalls")

(local (in-theory (disable nth make-list-ac-removal)))

(fty::defprod lofat-st
              ((fd natp)
               (buf stringp)
               (offset natp)
               (count natp)
               (retval integerp)
               (errno natp)
               (path fat32-filename-list-p)
               (stat struct-stat-p)
               (statfs struct-statfs-p)
               (dirp integerp) ;; This is interesting. We try to mimic the
               ;; NULL-returning behaviour of the actual opendir by making it
               ;; return -1 at precisely those times. That means this cannot be
               ;; assumed to be a natural number.
               (fd-table fd-table-p)
               (file-table file-table-p)
               (dir-stream-table dir-stream-table-p)))

;; We aren't going to put statfs in this. It'll just make things pointlessly
;; complicated.
(defund lofat-oracle-single-step (fat32$c syscall-sym st)
  (declare (xargs :stobjs fat32$c
                  :guard (and (lofat-fs-p fat32$c)
                              (lofat-st-p st))
                  :guard-debug t))
  (b*
      ((st (mbe :logic (lofat-st-fix st) :exec st))
       ((when (eq syscall-sym :pwrite))
        (b*
            (((mv fat32$c retval errno)
              (lofat-pwrite
               (lofat-st->fd st)
               (lofat-st->buf st)
               (lofat-st->offset st)
               fat32$c
               (lofat-st->fd-table st)
               (lofat-st->file-table st))))
          (mv fat32$c
              (change-lofat-st
               st :retval retval :errno errno))))
       ((when (eq syscall-sym :pread))
        (b*
            (((mv buf retval errno)
              (lofat-pread
               (lofat-st->fd st)
               (lofat-st->count st)
               (lofat-st->offset st)
               fat32$c
               (lofat-st->fd-table st)
               (lofat-st->file-table st))))
          (mv fat32$c
              (change-lofat-st
               st :buf buf :retval retval :errno errno))))
       ((when (eq syscall-sym :open))
        (b*
            (((mv fd-table file-table fd retval)
              (lofat-open
               (lofat-st->path st)
               (lofat-st->fd-table st)
               (lofat-st->file-table st))))
          (mv fat32$c
              (change-lofat-st
               st :fd fd :retval retval :errno 0 :file-table file-table
               :fd-table fd-table))))
       ((when (eq syscall-sym :lstat))
        (b*
            (((mv stat retval errno)
              (lofat-lstat
               fat32$c
               (lofat-st->path st))))
          (mv fat32$c
              (change-lofat-st
               st :stat stat :retval retval :errno errno))))
       ;; ((when (eq syscall-sym :unlink))
       ;;  (b*
       ;;      (((mv fat32$c retval errno)
       ;;        (lofat-unlink
       ;;         fat32$c
       ;;         (lofat-st->path st))))
       ;;    (mv fat32$c
       ;;        (change-lofat-st
       ;;         st :retval retval :errno errno))))
       ;; ((when (eq syscall-sym :truncate))
       ;;  (b*
       ;;      (((mv fat32$c retval errno)
       ;;        (lofat-unlink
       ;;         fat32$c
       ;;         (lofat-st->path st))))
       ;;    (mv fat32$c
       ;;        (change-lofat-st
       ;;         st :retval retval :errno errno))))
       ((when (eq syscall-sym :mkdir))
        (b*
            (((mv fat32$c retval errno)
              (lofat-mkdir
               fat32$c
               (lofat-st->path st))))
          (mv fat32$c
              (change-lofat-st
               st :retval retval :errno errno))))
       ((when (eq syscall-sym :opendir))
        (b*
            (((mv dir-stream-table dirp retval)
              (lofat-opendir
               fat32$c
               (lofat-st->dir-stream-table st)
               (lofat-st->path st))))
          (mv fat32$c
              (change-lofat-st
               st :dir-stream-table dir-stream-table :dirp dirp
               :retval retval :errno 0)))))
    (mv fat32$c st)))

;; We aren't going to put statfs in this. It'll just make things pointlessly
;; complicated.
(defund absfat-oracle-single-step (frame syscall-sym st)
  (declare (xargs :guard (and (frame-p frame)
                              (lofat-st-p st)
                              (consp (assoc-equal 0 frame))
                              (no-duplicatesp-equal (strip-cars frame)))
                  :guard-debug t))
  (b*
      ((st (mbe :logic (lofat-st-fix st) :exec st))
       ((when (eq syscall-sym :pwrite))
        (b*
            (((mv frame retval errno)
              (abs-pwrite
               (lofat-st->fd st)
               (lofat-st->buf st)
               (lofat-st->offset st)
               frame
               (lofat-st->fd-table st)
               (lofat-st->file-table st))))
          (mv frame
              (change-lofat-st
               st :retval retval :errno errno))))
       ((when (eq syscall-sym :pread))
        (b*
            (((mv buf retval errno)
              (abs-pread
               (lofat-st->fd st)
               (lofat-st->count st)
               (lofat-st->offset st)
               frame
               (lofat-st->fd-table st)
               (lofat-st->file-table st))))
          (mv frame
              (change-lofat-st
               st :buf buf :retval retval :errno errno))))
       ((when (eq syscall-sym :open))
        (b*
            (((mv fd-table file-table fd retval)
              (abs-open
               (lofat-st->path st)
               (lofat-st->fd-table st)
               (lofat-st->file-table st))))
          (mv frame
              (change-lofat-st
               st :fd fd :retval retval :errno 0 :file-table file-table
               :fd-table fd-table))))
       ((when (eq syscall-sym :lstat))
        (b*
            (((mv stat retval errno)
              (abs-lstat
               frame
               (lofat-st->path st))))
          (mv frame
              (change-lofat-st
               st :stat stat :retval retval :errno errno))))
       ;; ((when (eq syscall-sym :unlink))
       ;;  (b*
       ;;      (((mv fat32$c retval errno)
       ;;        (lofat-unlink
       ;;         fat32$c
       ;;         (lofat-st->path st))))
       ;;    (mv fat32$c
       ;;        (change-lofat-st
       ;;         st :retval retval :errno errno))))
       ;; ((when (eq syscall-sym :truncate))
       ;;  (b*
       ;;      (((mv fat32$c retval errno)
       ;;        (lofat-unlink
       ;;         fat32$c
       ;;         (lofat-st->path st))))
       ;;    (mv fat32$c
       ;;        (change-lofat-st
       ;;         st :retval retval :errno errno))))
       ((when (eq syscall-sym :mkdir))
        (b*
            (((mv frame retval errno)
              (abs-mkdir
               frame
               (lofat-st->path st))))
          (mv frame
              (change-lofat-st
               st :retval retval :errno errno))))
       ;; This is an interesting case! Basically, this command does not modify
       ;; the state of the filesystem but does change the frame.
       ((when (eq syscall-sym :opendir))
        (b*
            (((mv dirp dir-stream-table retval frame)
              (abs-opendir
               frame
               (lofat-st->path st)
               (lofat-st->dir-stream-table st))))
          (mv frame
              (change-lofat-st
               st :dir-stream-table dir-stream-table :dirp dirp
               :retval retval :errno 0)))))
    (mv frame st)))

(defthm
  lofat-mkdir-refinement-lemma-1
  (implies
   (and
    (good-root-d-e-p (pseudo-root-d-e fat32$c)
                     fat32$c)
    (fat32-filename-list-p path)
    (equal (mv-nth 1 (lofat-to-hifat fat32$c))
           0)
    (lofat-file-p file)
    (or (and (lofat-regular-file-p file)
             (<= (len (make-clusters (lofat-file->contents file)
                                     (cluster-size fat32$c)))
                 (count-free-clusters (effective-fat fat32$c))))
        (and (equal (lofat-file->contents file) nil)
             (<= 1
                 (count-free-clusters (effective-fat fat32$c)))))
    (not (equal (mv-nth 1
                        (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                          path file))
                28))
    (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
       (max-entry-count fat32$c)))
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                 path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth 0
                  (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                    path file))
          (pseudo-root-d-e fat32$c))))
       (max-entry-count fat32$c)))
     0)
    (hifat-equiv
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                 path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth 0
                  (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                    path file))
          (pseudo-root-d-e fat32$c))))
       (max-entry-count fat32$c)))
     (mv-nth 0
             (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                               path
                               (m1-file d-e (lofat-file->contents file)))))
    (equal
     (mv-nth 1
             (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                               path
                               (m1-file d-e (lofat-file->contents file))))
     (mv-nth 1
             (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                               path file)))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (lofat-to-hifat root-d-e-list)
                           (lofat-place-file-correctness-1))
           :use (:instance lofat-place-file-correctness-1
                           (entry-limit (max-entry-count fat32$c))
                           (root-d-e (pseudo-root-d-e fat32$c))))))

(encapsulate
  ()

  (local
   (defthm
     lemma-1
     (implies (or (and (stringp (m1-file->contents file))
                       (<= (len (make-clusters (m1-file->contents file)
                                               (cluster-size fat32$c)))
                           (count-free-clusters (effective-fat fat32$c))))
                  (and (equal (m1-file->contents file) nil)
                       (<= 1
                           (count-free-clusters (effective-fat fat32$c)))))
              (lofat-file-contents-p (m1-file->contents file)))
     :hints
     (("goal"
       :do-not-induct t
       :in-theory (disable lofat-mkdir-refinement-lemma-1)
       :use
       (:instance lofat-mkdir-refinement-lemma-1
                  (file (make-lofat-file :d-e nil
                                         :contents (m1-file->contents file)))
                  (d-e (m1-file->d-e file)))))))

  (defthm
    lofat-mkdir-refinement-lemma-2
    (implies
     (and
      (good-root-d-e-p (pseudo-root-d-e fat32$c)
                       fat32$c)
      (fat32-filename-list-p path)
      (equal (mv-nth 1 (lofat-to-hifat fat32$c))
             0)
      (or (and (stringp (m1-file->contents file))
               (<= (len (make-clusters (m1-file->contents file)
                                       (cluster-size fat32$c)))
                   (count-free-clusters (effective-fat fat32$c))))
          (and (equal (m1-file->contents file) nil)
               (<= 1
                   (count-free-clusters (effective-fat fat32$c)))))
      (not
       (equal
        (mv-nth 1
                (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                  path
                                  (lofat-file nil (m1-file->contents file))))
        28))
      (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
         (max-entry-count fat32$c)))
     (equal
      (mv-nth 1
              (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                                path file))
      (mv-nth 1
              (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                path
                                (lofat-file nil (m1-file->contents file))))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (disable lofat-mkdir-refinement-lemma-1)
      :use
      (:instance lofat-mkdir-refinement-lemma-1
                 (file (make-lofat-file :d-e nil
                                        :contents (m1-file->contents file)))
                 (d-e (m1-file->d-e file)))))))

(encapsulate
  ()

  (local
   (defthm
     lemma-1
     (implies
      (and (lofat-fs-p fat32$c)
           (equal (mv-nth 1 (lofat-to-hifat fat32$c))
                  0)
           (lofat-directory-file-p
            (mv-nth 0
                    (lofat-find-file fat32$c
                                     (mv-nth 0 (root-d-e-list fat32$c))
                                     path))))
      (equal
       (hifat-find-file (mv-nth 0 (lofat-to-hifat fat32$c))
                        path)
       (mv
        (make-m1-file
         :d-e (lofat-file->d-e
               (mv-nth 0
                       (lofat-find-file fat32$c
                                        (mv-nth 0 (root-d-e-list fat32$c))
                                        path)))
         :contents
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (lofat-file->contents
            (mv-nth 0
                    (lofat-find-file fat32$c
                                     (mv-nth 0 (root-d-e-list fat32$c))
                                     path)))
           (max-entry-count fat32$c))))
        (mv-nth 1
                (lofat-find-file fat32$c
                                 (mv-nth 0 (root-d-e-list fat32$c))
                                 path)))))
     :hints
     (("goal" :in-theory (e/d (lofat-to-hifat)
                              (lofat-find-file-correctness-2))
       :use ((:instance lofat-find-file-correctness-2
                        (d-e-list (mv-nth 0 (root-d-e-list fat32$c)))
                        (entry-limit (max-entry-count fat32$c)))
             (:instance (:rewrite hifat-find-file-correctness-2)
                        (path path)
                        (fs (mv-nth 0 (lofat-to-hifat fat32$c)))))
       :do-not-induct t))))

  (local
   (defthm
     lemma-2
     (implies
      (and (lofat-fs-p fat32$c)
           (equal (mv-nth 1 (lofat-to-hifat fat32$c))
                  0)
           (lofat-regular-file-p
            (mv-nth 0
                    (lofat-find-file fat32$c
                                     (mv-nth 0 (root-d-e-list fat32$c))
                                     path))))
      (equal
       (hifat-find-file (mv-nth 0 (lofat-to-hifat fat32$c))
                        path)
       (mv
        (make-m1-file
         :contents
         (lofat-file->contents
          (mv-nth 0
                  (lofat-find-file fat32$c
                                   (mv-nth 0 (root-d-e-list fat32$c))
                                   path)))
         :d-e (lofat-file->d-e
               (mv-nth 0
                       (lofat-find-file fat32$c
                                        (mv-nth 0 (root-d-e-list fat32$c))
                                        path))))
        (mv-nth 1
                (lofat-find-file fat32$c
                                 (mv-nth 0 (root-d-e-list fat32$c))
                                 path)))))
     :hints
     (("goal" :do-not-induct t
       :in-theory (e/d (lofat-to-hifat)
                       (lofat-find-file-correctness-1))
       :use ((:instance lofat-find-file-correctness-1
                        (d-e-list (mv-nth 0 (root-d-e-list fat32$c)))
                        (entry-limit (max-entry-count fat32$c)))
             (:instance (:rewrite hifat-find-file-correctness-2)
                        (path path)
                        (fs (mv-nth 0 (lofat-to-hifat fat32$c)))))))))

  (defthm
    lofat-mkdir-refinement-lemma-3
   (implies
    (and (lofat-fs-p fat32$c)
         (equal (mv-nth 1 (lofat-to-hifat fat32$c))
                0))
    (equal
     (hifat-find-file (mv-nth 0 (lofat-to-hifat fat32$c))
                      path)
     (if
         (lofat-directory-file-p
          (mv-nth 0
                  (lofat-find-file fat32$c
                                   (mv-nth 0 (root-d-e-list fat32$c))
                                   path)))
         (mv
          (make-m1-file
           :d-e (lofat-file->d-e
                 (mv-nth 0
                         (lofat-find-file fat32$c
                                          (mv-nth 0 (root-d-e-list fat32$c))
                                          path)))
           :contents
           (mv-nth
            0
            (lofat-to-hifat-helper
             fat32$c
             (lofat-file->contents
              (mv-nth 0
                      (lofat-find-file fat32$c
                                       (mv-nth 0 (root-d-e-list fat32$c))
                                       path)))
             (max-entry-count fat32$c))))
          (mv-nth 1
                  (lofat-find-file fat32$c
                                   (mv-nth 0 (root-d-e-list fat32$c))
                                   path)))
       (mv
        (make-m1-file
         :contents
         (lofat-file->contents
          (mv-nth 0
                  (lofat-find-file fat32$c
                                   (mv-nth 0 (root-d-e-list fat32$c))
                                   path)))
         :d-e (lofat-file->d-e
               (mv-nth 0
                       (lofat-find-file fat32$c
                                        (mv-nth 0 (root-d-e-list fat32$c))
                                        path))))
        (mv-nth 1
                (lofat-find-file fat32$c
                                 (mv-nth 0 (root-d-e-list fat32$c))
                                 path))))))
   :hints (("goal" :do-not-induct t
            :in-theory (disable
                        lemma-1
                        lemma-2)
            :use
            (lemma-1
             lemma-2))))

  (defthm
    lofat-mkdir-refinement-lemma-5
    (implies
     (or
      (lofat-directory-file-p (mv-nth 0
                                      (lofat-find-file fat32$c d-e-list path)))
      (not
       (lofat-regular-file-p (mv-nth 0
                                     (lofat-find-file fat32$c d-e-list path)))))
     (useful-d-e-list-p
      (lofat-file->contents (mv-nth 0
                                    (lofat-find-file fat32$c d-e-list path)))))
    :hints (("goal" :in-theory (enable lofat-find-file))))

  ;; This will probably be useful later.
  (defthm
    lofat-mkdir-refinement-lemma-4
    (implies
     (and (lofat-fs-p fat32$c)
          (equal (mv-nth 1 (lofat-to-hifat fat32$c))
                 0))
     (iff (m1-regular-file-p
           (mv-nth 0
                   (hifat-find-file (mv-nth 0 (lofat-to-hifat fat32$c))
                                    path)))
          (lofat-regular-file-p
           (mv-nth 0
                   (lofat-find-file fat32$c
                                    (mv-nth 0 (root-d-e-list fat32$c))
                                    path)))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (disable lemma-1
                          lemma-2)
      :use (lemma-1 lemma-2)))
    :rule-classes
    ((:rewrite
      :corollary
      (implies
       (and (lofat-fs-p fat32$c)
            (equal (mv-nth 1 (lofat-to-hifat fat32$c))
                   0))
       (equal (m1-regular-file-p
               (mv-nth 0
                       (hifat-find-file (mv-nth 0 (lofat-to-hifat fat32$c))
                                        path)))
              (lofat-regular-file-p
               (mv-nth 0
                       (lofat-find-file fat32$c
                                        (mv-nth 0 (root-d-e-list fat32$c))
                                        path))))))
     (:rewrite
      :corollary
      (implies
       (and (lofat-fs-p fat32$c)
            (equal (mv-nth 1 (lofat-to-hifat fat32$c))
                   0))
       (equal (m1-directory-file-p
               (mv-nth 0
                       (hifat-find-file (mv-nth 0 (lofat-to-hifat fat32$c))
                                        path)))
              (lofat-directory-file-p
               (mv-nth 0
                       (lofat-find-file fat32$c
                                        (mv-nth 0 (root-d-e-list fat32$c))
                                        path)))))))))

(defthm
  lofat-mkdir-refinement-lemma-7
  (implies
   (and (fat32-filename-list-p path)
        (consp (cdr path))
        (equal (mv-nth 1
                       (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                         path file))
               0))
   (d-e-directory-p
    (mv-nth
     '0
     (find-d-e
      (make-d-e-list
       (mv-nth '0
               (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
      (car path)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (lofat-to-hifat root-d-e-list
                                    lofat-place-file-correctness-lemma-25
                                    d-e-cc-of-lofat-place-file-coincident-1
                                    lofat-place-file hifat-place-file)
                    (lofat-place-file-correctness-1)))))

(defthm
  lofat-mkdir-refinement-lemma-8
  (implies
   (and
    (good-root-d-e-p (pseudo-root-d-e fat32$c)
                     fat32$c)
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
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (max-entry-count fat32$c)))
     0)
    (lofat-file-p file)
    (lofat-regular-file-p file)
    (<= (len (make-clusters (lofat-file->contents file)
                            (cluster-size fat32$c)))
        (count-free-clusters (effective-fat fat32$c)))
    (not (equal (mv-nth 1
                        (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                          path file))
                28))
    (<
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (max-entry-count fat32$c))))
     (max-entry-count fat32$c))
    (consp (cdr path)))
   (not-intersectp-list
    (mv-nth 0
            (d-e-cc fat32$c (pseudo-root-d-e fat32$c)))
    (mv-nth
     2
     (lofat-to-hifat-helper
      (mv-nth 0
              (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                path file))
      (make-d-e-list
       (mv-nth 0
               (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
      (max-entry-count fat32$c)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable lofat-place-file-correctness-1-lemma-1)
    :use (:instance lofat-place-file-correctness-1-lemma-1
                    (x (mv-nth 0
                               (d-e-cc fat32$c (pseudo-root-d-e fat32$c))))
                    (root-d-e (pseudo-root-d-e fat32$c))
                    (entry-limit (max-entry-count fat32$c)))
    :expand (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                              path file))))

(defthm
  lofat-mkdir-refinement-lemma-9
  (implies
   (and
    (good-root-d-e-p (pseudo-root-d-e fat32$c)
                     fat32$c)
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
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (max-entry-count fat32$c)))
     0)
    (lofat-file-p file)
    (not (lofat-file->contents file))
    (<= 1
        (count-free-clusters (effective-fat fat32$c)))
    (not (equal (mv-nth 1
                        (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                          path file))
                28))
    (<
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (max-entry-count fat32$c))))
     (max-entry-count fat32$c))
    (consp (cdr path)))
   (not-intersectp-list
    (mv-nth 0
            (d-e-cc fat32$c (pseudo-root-d-e fat32$c)))
    (mv-nth
     2
     (lofat-to-hifat-helper
      (mv-nth 0
              (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                path file))
      (make-d-e-list
       (mv-nth 0
               (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
      (max-entry-count fat32$c)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable lofat-place-file-correctness-1-lemma-1)
    :use (:instance lofat-place-file-correctness-1-lemma-1
                    (x (mv-nth 0
                               (d-e-cc fat32$c (pseudo-root-d-e fat32$c))))
                    (root-d-e (pseudo-root-d-e fat32$c))
                    (entry-limit (max-entry-count fat32$c)))
    :expand (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                              path file))))

(defthm
  lofat-mkdir-refinement-lemma-6
  (implies (and (equal (mv-nth 1
                               (lofat-place-file fat32$c root-d-e path file1))
                       0)
                (equal (lofat-file->contents file1)
                       (lofat-file->contents file2))
                (lofat-file-p file1)
                (lofat-file-p file2))
           (equal (mv-nth 1
                          (lofat-place-file fat32$c root-d-e path file2))
                  0))
  :hints (("goal" :in-theory (enable lofat-place-file
                                     lofat-place-file-helper))
          (if (not stable-under-simplificationp)
              nil
              '(:in-theory (enable lofat-place-file lofat-place-file-helper
                                   lofat-regular-file-p
                                   lofat-directory-file-p)))))

(defthm
  lofat-mkdir-refinement-lemma-10
  (implies
   (and
    (good-root-d-e-p (pseudo-root-d-e fat32$c)
                     fat32$c)
    (fat32-filename-list-p path)
    (equal (mv-nth 1 (lofat-to-hifat fat32$c))
           0)
    (lofat-file-p file)
    (or (and (lofat-regular-file-p file)
             (<= (len (make-clusters (lofat-file->contents file)
                                     (cluster-size fat32$c)))
                 (count-free-clusters (effective-fat fat32$c))))
        (and (equal (lofat-file->contents file) nil)
             (<= 1
                 (count-free-clusters (effective-fat fat32$c)))))
    (not (equal (mv-nth 1
                        (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                          path file))
                28))
    (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
       (max-entry-count fat32$c))
    (consp (cdr path)))
   (and
    (equal
     (mv-nth 1
             (lofat-to-hifat
              (mv-nth 0
                      (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                        path file))))
     0)
    (hifat-equiv
     (mv-nth 0
             (lofat-to-hifat
              (mv-nth 0
                      (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                        path file))))
     (mv-nth 0
             (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                               path
                               (m1-file d-e (lofat-file->contents file)))))
    (equal
     (mv-nth 1
             (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                               path
                               (m1-file d-e (lofat-file->contents file))))
     (mv-nth 1
             (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                               path file)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (lofat-to-hifat root-d-e-list
                                    d-e-cc-of-lofat-place-file-coincident-1)
                    (lofat-place-file-correctness-1))
    :use (:instance lofat-place-file-correctness-1
                    (root-d-e (pseudo-root-d-e fat32$c))
                    (entry-limit (max-entry-count fat32$c))))))

(defthm
  lofat-mkdir-refinement-lemma-13
  (implies
   (lofat-fs-p fat32$c)
   (equal
    (mv-nth
     '2
     (place-contents
      (update-fati
       (nth '0
            (find-n-free-clusters (effective-fat fat32$c)
                                  '1))
       (fat32-update-lower-28
        (fati (nth '0
                   (find-n-free-clusters (effective-fat fat32$c)
                                         '1))
              fat32$c)
        '268435455)
       fat32$c)
      (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                 'nil)
      (make-empty-subdir-contents
       (nth '0
            (find-n-free-clusters (effective-fat fat32$c)
                                  '1))
       (d-e-first-cluster (pseudo-root-d-e fat32$c)))
      '0
      (nth '0
           (find-n-free-clusters (effective-fat fat32$c)
                                 '1))))
    '0))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable (:rewrite place-contents-expansion-2))
    :use
    (:instance
     (:rewrite place-contents-expansion-2)
     (first-cluster (nth 0
                         (find-n-free-clusters (effective-fat fat32$c)
                                               1)))
     (file-length 0)
     (contents (make-empty-subdir-contents
                (nth 0
                     (find-n-free-clusters (effective-fat fat32$c)
                                           1))
                (d-e-first-cluster (pseudo-root-d-e fat32$c))))
     (d-e (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                     nil))
     (fat32$c
      (update-fati
       (nth 0
            (find-n-free-clusters (effective-fat fat32$c)
                                  1))
       (fat32-update-lower-28
        (fati (nth 0
                   (find-n-free-clusters (effective-fat fat32$c)
                                         1))
              fat32$c)
        268435455)
       fat32$c))))))

(defthm
  lofat-mkdir-refinement-lemma-11
  (implies
   (and
    (lofat-fs-p fat32$c)
    (fat32-filename-list-p path)
    (not
     (equal
      (mv-nth
       1
       (find-d-e
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (car path)))
      0))
    (equal (mv-nth 1
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))
           0)
    (no-duplicatesp-equal
     (mv-nth 0
             (d-e-cc fat32$c (pseudo-root-d-e fat32$c)))))
   (no-duplicatesp-equal
    (mv-nth
     0
     (d-e-cc (mv-nth 0
                     (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                       path file))
             (pseudo-root-d-e fat32$c)))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (lofat-to-hifat root-d-e-list)
                           nil))))

(defthm
  lofat-mkdir-refinement-lemma-16
  (implies
   (and
    (equal
     (len (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))))
     65534)
    (fat32-filename-list-p path)
    (not
     (equal
      (mv-nth
       1
       (find-d-e
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (car path)))
      0)))
   (not (equal (mv-nth 1
                       (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                         path file))
               0)))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (lofat-to-hifat root-d-e-list)
                           nil)))
  :rule-classes :type-prescription)

(defthm
  lofat-mkdir-refinement-lemma-17
  (implies
   (and
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
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (max-entry-count fat32$c)))
     0)
    (not
     (equal
      (mv-nth
       1
       (find-d-e
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (car path)))
      0))
    (equal (mv-nth 1
                   (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                     path file))
           0)
    (equal (mv-nth 1
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))
           0)
    (<
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (max-entry-count fat32$c))))
     (max-entry-count fat32$c))
    (lofat-directory-file-p file))
   (equal
    (mv-nth
     3
     (lofat-to-hifat-helper
      (mv-nth 0
              (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                path file))
      (place-d-e
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (d-e-set-first-cluster-file-size
        (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                   t)
        (nth 0
             (find-n-free-clusters (effective-fat fat32$c)
                                   1))
        0))
      (max-entry-count fat32$c)))
    0))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (lofat-to-hifat root-d-e-list)
                           nil))))

(defthm
  lofat-mkdir-refinement-lemma-18
  (implies
   (and
    (equal (lofat-file->contents file) "")
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
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (max-entry-count fat32$c)))
     0)
    (not
     (equal
      (mv-nth
       1
       (find-d-e
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (car path)))
      0))
    (<
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (max-entry-count fat32$c))))
     (max-entry-count fat32$c))
    (lofat-regular-file-p file))
   (equal
    (mv-nth
     3
     (lofat-to-hifat-helper
      (mv-nth 0
              (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                path file))
      (place-d-e
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (d-e-set-first-cluster-file-size
        (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                   nil)
        0 0))
      (max-entry-count fat32$c)))
    0))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (lofat-to-hifat root-d-e-list) nil)
    :restrict ((not-intersectp-list-when-subsetp-1
                ((y (mv-nth 0
                            (d-e-cc fat32$c
                                    (pseudo-root-d-e fat32$c))))))))))

(defthm
  lofat-mkdir-refinement-lemma-19
  (implies
   (and
    (equal (lofat-file->contents file) "")
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
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (max-entry-count fat32$c)))
     0)
    (not
     (equal
      (mv-nth
       1
       (find-d-e
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (car path)))
      0))
    (equal (mv-nth 1
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))
           0)
    (no-duplicatesp-equal (mv-nth 0
                                  (d-e-cc fat32$c (pseudo-root-d-e fat32$c))))
    (lofat-regular-file-p file))
   (not-intersectp-list
    (mv-nth
     0
     (d-e-cc (mv-nth 0
                     (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                       path file))
             (pseudo-root-d-e fat32$c)))
    (mv-nth
     2
     (lofat-to-hifat-helper
      (mv-nth 0
              (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                path file))
      (place-d-e
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (d-e-set-first-cluster-file-size
        (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                   nil)
        0 0))
      (max-entry-count fat32$c)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (lofat-to-hifat root-d-e-list
                                    d-e-cc-of-lofat-place-file-coincident-1)
                    nil)
    :restrict ((not-intersectp-list-when-subsetp-1
                ((y (mv-nth 0
                            (d-e-cc fat32$c
                                    (pseudo-root-d-e fat32$c))))))))))

(defthm
  lofat-mkdir-refinement-lemma-20
  (implies
   (and
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
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (max-entry-count fat32$c)))
     0)
    (not
     (equal
      (mv-nth
       1
       (find-d-e
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (car path)))
      0))
    (equal (mv-nth 1
                   (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                     path file))
           0)
    (equal (mv-nth 1
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))
           0)
    (<
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (max-entry-count fat32$c))))
     (max-entry-count fat32$c))
    (lofat-regular-file-p file)
    (< 0
       (len (explode (lofat-file->contents file)))))
   (equal
    (mv-nth
     3
     (lofat-to-hifat-helper
      (mv-nth 0
              (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                path file))
      (place-d-e
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (d-e-set-first-cluster-file-size
        (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                   nil)
        (nth 0
             (find-n-free-clusters (effective-fat fat32$c)
                                   1))
        (len (explode (lofat-file->contents file)))))
      (max-entry-count fat32$c)))
    0))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (lofat-to-hifat root-d-e-list) nil)
    :restrict ((not-intersectp-list-when-subsetp-1
                ((y (mv-nth 0
                            (d-e-cc fat32$c
                                    (pseudo-root-d-e fat32$c))))))))))

(defthm
  lofat-mkdir-refinement-lemma-21
  (implies
   (and
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
    (not
     (equal
      (mv-nth
       1
       (find-d-e
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (car path)))
      0))
    (equal (mv-nth 1
                   (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                     path file))
           0)
    (equal (mv-nth 1
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))
           0)
    (<
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (max-entry-count fat32$c))))
     (max-entry-count fat32$c))
    (lofat-regular-file-p file)
    (< 0
       (len (explode (lofat-file->contents file)))))
   (not-intersectp-list
    (mv-nth
     0
     (d-e-cc (mv-nth 0
                     (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                       path file))
             (pseudo-root-d-e fat32$c)))
    (mv-nth
     2
     (lofat-to-hifat-helper
      (mv-nth 0
              (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                path file))
      (place-d-e
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (d-e-set-first-cluster-file-size
        (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                   nil)
        (nth 0
             (find-n-free-clusters (effective-fat fat32$c)
                                   1))
        (len (explode (lofat-file->contents file)))))
      (max-entry-count fat32$c)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (lofat-to-hifat root-d-e-list
                                    d-e-cc-of-lofat-place-file-coincident-1)
                    nil)
    :restrict ((not-intersectp-list-when-subsetp-1
                ((y (mv-nth 0
                            (d-e-cc fat32$c
                                    (pseudo-root-d-e fat32$c))))))))))

(defthm
  lofat-mkdir-refinement-lemma-22
  (implies
   (and
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
    (not
     (equal
      (mv-nth
       1
       (find-d-e
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (car path)))
      0))
    (equal (mv-nth 1
                   (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                     path file))
           0)
    (equal (mv-nth 1
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))
           0)
    (<
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (max-entry-count fat32$c))))
     (max-entry-count fat32$c))
    (lofat-directory-file-p file))
   (not-intersectp-list
    (mv-nth
     0
     (d-e-cc (mv-nth 0
                     (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                       path file))
             (pseudo-root-d-e fat32$c)))
    (mv-nth
     2
     (lofat-to-hifat-helper
      (mv-nth 0
              (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                path file))
      (place-d-e
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (d-e-set-first-cluster-file-size
        (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                   t)
        (nth 0
             (find-n-free-clusters (effective-fat fat32$c)
                                   1))
        0))
      (max-entry-count fat32$c)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (lofat-to-hifat root-d-e-list
                                    d-e-cc-of-lofat-place-file-coincident-1)
                    nil)
    :restrict ((not-intersectp-list-when-subsetp-1
                ((y (mv-nth 0
                            (d-e-cc fat32$c
                                    (pseudo-root-d-e fat32$c))))))))))

(defthm
  lofat-mkdir-refinement-lemma-23
  (implies
   (and (lofat-fs-p fat32$c)
        (fat32-filename-list-p path)
        (equal (mv-nth 1 (lofat-to-hifat fat32$c))
               0)
        (consp path)
        (not (equal (mv-nth 1
                            (find-d-e (mv-nth 0 (root-d-e-list fat32$c))
                                      (car path)))
                    0))
        (equal (mv-nth 1
                       (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                         path file))
               0)
        (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
           (max-entry-count fat32$c))
        (lofat-file-p file))
   (equal
    (mv-nth 1
            (lofat-to-hifat
             (mv-nth 0
                     (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                       path file))))
    0))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (lofat-to-hifat root-d-e-list)
                    (lofat-place-file))
    :restrict ((not-intersectp-list-when-subsetp-1
                ((y (mv-nth 0
                            (d-e-cc fat32$c
                                    (pseudo-root-d-e fat32$c))))))))))

;; Counterexample, but for regular files which we aren't really thinking about
(thm
 (implies
  (and
   (lofat-fs-p fat32$c)
   (fat32-filename-list-p path)
   (not
    (equal
     (mv-nth
      1
      (find-d-e
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (car path)))
     0))
   (equal (mv-nth 1
                  (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                    path file))
          0)
   (equal (mv-nth 1
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))
          0)
   (no-duplicatesp-equal (mv-nth 0
                                 (d-e-cc fat32$c (pseudo-root-d-e fat32$c))))
   (lofat-regular-file-p file)
   (< 0
      (len (explode (lofat-file->contents file)))))
  (and
   (hifat-equiv
    (mv-nth 0
            (lofat-to-hifat
             (mv-nth 0
                     (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                       path file))))
    (mv-nth
     0
     (lofat-to-hifat-helper
      (mv-nth 0
              (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                path file))
      (place-d-e
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (d-e-set-first-cluster-file-size
        (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                   nil)
        (nth 0
             (find-n-free-clusters (effective-fat fat32$c)
                                   1))
        (len (explode (lofat-file->contents file)))))
      (max-entry-count fat32$c))))
   (hifat-equiv
    (mv-nth
     0
     (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                       path
                       (make-m1-file :d-e (lofat-file->d-e file)
                                     :contents (lofat-file->contents file))))
    (mv-nth
     0
     (hifat-place-file
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (max-entry-count fat32$c)))
      path
      (m1-file (lofat-file->d-e file)
               (lofat-file->contents file)))))))
 :hints
 (("goal"
   :do-not-induct t
   :in-theory
   (e/d (lofat-to-hifat root-d-e-list hifat-place-file)
        ((:rewrite hifat-to-lofat-inversion-lemma-2)
         (:rewrite absfat-subsetp-transitivity-lemma-7)
         (:rewrite abs-directory-file-p-when-m1-file-p)
         (:rewrite m1-regular-file-p-correctness-1)
         (:definition find-d-e)
         (:rewrite str::consp-of-explode)
         (:rewrite abs-mkdir-correctness-lemma-228)
         (:rewrite str::explode-when-not-stringp)
         (:rewrite hifat-find-file-correctness-1-lemma-1)
         (:rewrite nfix-when-zp)
         (:rewrite abs-directory-file-p-correctness-1)
         (:rewrite lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2)
         (:rewrite lofat-find-file-correctness-lemma-2)
         (:rewrite d-e-p-of-car-when-d-e-list-p)
         (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-2)
         (:linear m1-regular-file-p-correctness-2)
         (:rewrite lofat-pread-refinement-lemma-1)
         (:definition member-intersectp-equal)
         (:rewrite lofat-find-file-correctness-lemma-1)
         (:definition assoc-equal)))
   :restrict ((not-intersectp-list-when-subsetp-1
               ((y (mv-nth 0
                           (d-e-cc fat32$c
                                   (pseudo-root-d-e fat32$c))))))))))

(defthm
  lofat-mkdir-refinement-lemma-25
  (implies
   (and
    (fat32-filename-list-p path)
    (not (consp (cdr path)))
    (consp path)
    (equal
     (mv-nth
      1
      (find-d-e
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (basename path)))
     0))
   (equal
    (mv-nth
     1
     (find-d-e
      (make-d-e-list
       (mv-nth 0
               (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
      (car path)))
    0))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (lofat-to-hifat root-d-e-list hifat-place-file basename)
                    nil)
    :restrict ((not-intersectp-list-when-subsetp-1
                ((y (mv-nth 0
                            (d-e-cc fat32$c
                                    (pseudo-root-d-e fat32$c))))))))))

(defthm
  lofat-mkdir-refinement-lemma-26
  (implies
   (and
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
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (max-entry-count fat32$c)))
     0)
    (not
     (equal
      (mv-nth
       1
       (find-d-e
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (car path)))
      0))
    (equal (mv-nth 1
                   (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                     path file))
           0)
    (equal (mv-nth 1
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))
           0)
    (<
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (max-entry-count fat32$c))))
     (max-entry-count fat32$c))
    (lofat-directory-file-p file))
   (hifat-equiv
    (mv-nth
     0
     (lofat-to-hifat-helper
      (mv-nth 0
              (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                path file))
      (place-d-e
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (d-e-set-first-cluster-file-size
        (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                   t)
        (nth 0
             (find-n-free-clusters (effective-fat fat32$c)
                                   1))
        0))
      (max-entry-count fat32$c)))
    (mv-nth
     0
     (hifat-place-file
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
        (max-entry-count fat32$c)))
      path
      '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
        (contents))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (lofat-to-hifat root-d-e-list hifat-place-file)
                    nil)
    :restrict ((not-intersectp-list-when-subsetp-1
                ((y (mv-nth 0
                            (d-e-cc fat32$c
                                    (pseudo-root-d-e fat32$c))))))))))

(defthm
  lofat-mkdir-refinement-lemma-12
  (implies
   (and
    (lofat-fs-p fat32$c)
    (fat32-filename-list-p path)
    (not (consp (cdr path)))
    (consp path)
    (not (equal (mv-nth 1
                        (find-d-e (mv-nth 0 (root-d-e-list fat32$c))
                                  (car path)))
                0))
    (equal (mv-nth 1
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))
           0)
    (no-duplicatesp-equal (mv-nth 0
                                  (d-e-cc fat32$c (pseudo-root-d-e fat32$c))))
    (not
     (equal
      (mv-nth
       1
       (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                         path
                         '((d-e 0 0 0 0 0 0 0 0 0 0 0 16
                                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (contents))))
      28)))
   (equal
    (mv-nth 1
            (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                              path
                              '((d-e 0 0 0 0 0 0 0 0 0 0 0 16
                                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                (contents))))
    0))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (lofat-to-hifat root-d-e-list hifat-place-file)
                    nil)
    :restrict ((not-intersectp-list-when-subsetp-1
                ((y (mv-nth 0
                            (d-e-cc fat32$c
                                    (pseudo-root-d-e fat32$c))))))))))

(defthm
  lofat-mkdir-refinement-lemma-29
  (implies
   (and
    (lofat-fs-p fat32$c)
    (fat32-filename-list-p path)
    (not (consp (cdr path)))
    (consp path)
    (not (equal (mv-nth 1
                        (find-d-e (mv-nth 0 (root-d-e-list fat32$c))
                                  (car path)))
                0))
    (equal (mv-nth 1
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))
           0)
    (no-duplicatesp-equal (mv-nth 0
                                  (d-e-cc fat32$c (pseudo-root-d-e fat32$c))))
    (not
     (equal
      (mv-nth
       1
       (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                         path
                         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (contents))))
      28)))
   (equal
    (mv-nth 1
            (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                              path
                              '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                (contents))))
    0))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (lofat-to-hifat root-d-e-list hifat-place-file)
                    nil)
    :restrict ((not-intersectp-list-when-subsetp-1
                ((y (mv-nth 0
                            (d-e-cc fat32$c
                                    (pseudo-root-d-e fat32$c))))))))))

(defthm
  lofat-mkdir-refinement-lemma-30
  (implies
   (and
    (lofat-fs-p fat32$c)
    (fat32-filename-list-p path)
    (equal (mv-nth 1 (lofat-to-hifat fat32$c))
           0)
    (not (equal (mv-nth 1
                        (find-d-e (mv-nth 0 (root-d-e-list fat32$c))
                                  (car path)))
                0))
    (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
       (max-entry-count fat32$c))
    (not
     (equal
      (mv-nth
       1
       (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                         path
                         '((d-e 0 0 0 0 0 0 0 0 0 0 0 16
                                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (contents))))
      28)))
   (hifat-equiv
    (mv-nth
     0
     (lofat-to-hifat
      (mv-nth
       0
       (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                         path
                         '((d-e 0 0 0 0 0 0 0 0 0 0 0 16
                                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (contents))))))
    (mv-nth 0
            (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                              path
                              '((d-e 0 0 0 0 0 0 0 0 0 0 0 16
                                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                (contents))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (lofat-to-hifat root-d-e-list hifat-place-file)
                    nil)
    :restrict ((not-intersectp-list-when-subsetp-1
                ((y (mv-nth 0
                            (d-e-cc fat32$c
                                    (pseudo-root-d-e fat32$c))))))))))

;; This was a counterexample.
;; (thm
;;  (implies
;;   (and
;;    (lofat-fs-p fat32$c)
;;    (fat32-filename-list-p path)
;;    (equal (mv-nth 1 (lofat-to-hifat fat32$c))
;;           0)
;;    (consp (cdr path))
;;    (equal
;;     (mv-nth 1
;;             (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
;;                               path
;;                               '((d-e 0 0 0 0 0 0 0 0 0 0 0 16
;;                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;                                 (contents))))
;;     0)
;;    (equal (mv-nth 1
;;                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))
;;           0)
;;    (no-duplicatesp-equal (mv-nth 0
;;                                  (d-e-cc fat32$c (pseudo-root-d-e fat32$c))))
;;    (<= 1
;;        (count-free-clusters (effective-fat fat32$c)))
;;    (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
;;       (max-entry-count fat32$c))
;;    (not (m1-directory-file-p
;;          (mv-nth 0
;;                  (lofat-find-file fat32$c
;;                                   (mv-nth 0 (root-d-e-list fat32$c))
;;                                   (dirname path)))))
;;    (lofat-directory-file-p
;;     (mv-nth 0
;;             (lofat-find-file fat32$c
;;                              (mv-nth 0 (root-d-e-list fat32$c))
;;                              (dirname path))))
;;    (equal (mv-nth 1
;;                   (lofat-find-file fat32$c
;;                                    (mv-nth 0 (root-d-e-list fat32$c))
;;                                    (dirname path)))
;;           0)
;;    (not (equal (mv-nth 1
;;                        (lofat-find-file fat32$c
;;                                         (mv-nth 0 (root-d-e-list fat32$c))
;;                                         path))
;;                0)))
;;   (and (equal (mv-nth 1 (lofat-mkdir fat32$c path))
;;               -1)
;;        (equal (mv-nth 1
;;                       (hifat-mkdir (mv-nth 0 (lofat-to-hifat fat32$c))
;;                                    path))
;;               0)))
;;  :hints
;;  (("goal" :do-not-induct t
;;    :in-theory
;;    (e/d (lofat-mkdir)
;;         ((:rewrite d-e-cc-of-update-dir-contents-coincident)
;;          (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident)))
;;    :expand ((:free (fs) (hifat-find-file fs nil))
;;             (:free (fs file)
;;                    (hifat-place-file fs nil file))))))

(defthm
  lofat-mkdir-refinement
  (implies
   (and
    (lofat-fs-p fat32$c)
    (fat32-filename-list-p path)
    (equal (mv-nth 1 (lofat-to-hifat fat32$c))
           0)
    (equal (mv-nth 1
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))
           0)
    (no-duplicatesp-equal (mv-nth 0
                                  (d-e-cc fat32$c (pseudo-root-d-e fat32$c))))
    (not (< (count-free-clusters (effective-fat fat32$c))
            1))
    (not
     (equal
      (mv-nth
       1
       (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                         path
                         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (contents))))
      28))
    (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
       (max-entry-count fat32$c))
    (not
     (equal
      (mv-nth
       1
       (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                         path
                         '((d-e 0 0 0 0 0 0 0 0 0 0 0 16
                                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (contents))))
      28)))
   (and (equal (mv-nth 1
                       (lofat-to-hifat (mv-nth 0 (lofat-mkdir fat32$c path))))
               0)
        (hifat-equiv
         (mv-nth 0
                 (lofat-to-hifat (mv-nth 0 (lofat-mkdir fat32$c path))))
         (mv-nth 0
                 (hifat-mkdir (mv-nth 0 (lofat-to-hifat fat32$c))
                              path)))
        (equal (mv-nth 1 (lofat-mkdir fat32$c path))
               (mv-nth 1
                       (hifat-mkdir (mv-nth 0 (lofat-to-hifat fat32$c))
                                    path)))))
  :hints
  (("goal" :do-not-induct t
    :in-theory
    (e/d (lofat-mkdir)
         ((:rewrite d-e-cc-of-update-dir-contents-coincident)
          (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident)
          lofat-place-file))
    :expand ((:free (fs) (hifat-find-file fs nil))
             (:free (fs file)
                    (hifat-place-file fs nil file))
             (:free (fat32$c file root-d-e)
                    (lofat-place-file fat32$c root-d-e nil file))))))
