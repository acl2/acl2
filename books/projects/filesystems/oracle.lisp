(in-package "ACL2")

;  oracle.lisp                                         Mihir Mehta

(include-book "lofat-syscalls")
(include-book "abs-syscalls")

(local (in-theory (disable nth make-list-ac-removal last
                           make-list-ac)))

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
  lofat-mkdir-refinement-lemma-14
  (equal
   (lofat-place-file fat32$c root-d-e path
                     (list (cons 'd-e d-e1)
                           (cons 'contents contents)))
   (lofat-place-file fat32$c root-d-e path
                     (list (cons 'd-e d-e2)
                           (cons 'contents contents))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lofat-place-file lofat-place-file-helper
                       lofat-regular-file-p
                       lofat-directory-file-p
                       lofat-file-p lofat-file->contents
                       m1-file-hifat-file-alist-fix m1-file)
     (m1-file-hifat-file-alist-fix-normalisation
      abs-mkdir-correctness-lemma-36
      (:rewrite lofat-file-contents-fix-when-lofat-file-contents-p)
      (:rewrite d-e-cc-contents-of-lofat-place-file-coincident-lemma-4)
      (:rewrite fat32-filename-p-correctness-1)
      (:rewrite lofat-file-contents-p-when-stringp)
      (:linear nth-when-d-e-p)
      (:linear len-of-explode-when-m1-file-contents-p-1)
      (:rewrite lofat-file-fix-when-lofat-file-p)
      (:rewrite lofat-file-contents-p-when-d-e-listp)
      (:rewrite nth-of-nats=>chars)
      (:rewrite m1-file-contents-p-when-stringp)
      (:type-prescription hifat-bounded-file-alist-p)
      (:rewrite stringp-when-nonempty-stringp)))))
  :rule-classes
  (:rewrite
   (:congruence
    :corollary
    (implies
     (true-equiv d-e1 d-e2)
     (equal
      (lofat-place-file fat32$c root-d-e path
                        (list (cons 'd-e d-e1)
                              (cons 'contents contents)))
      (lofat-place-file fat32$c root-d-e path
                        (list (cons 'd-e d-e2)
                              (cons 'contents contents))))))))

(in-theory (disable (:r
                     lofat-mkdir-refinement-lemma-14)))

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
    (or (stringp (lofat-file->contents file))
        (equal (lofat-file->contents file) nil))
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
      (or (stringp (m1-file->contents file))
          (equal (m1-file->contents file) nil))
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
  lofat-mkdir-refinement-lemma-6
  (implies (and (equal (lofat-file->contents file1)
                       (lofat-file->contents file2))
                (lofat-file-p file1)
                (lofat-file-p file2))
           (equal (mv-nth 1
                          (lofat-place-file fat32$c root-d-e path file2))
                  (mv-nth 1
                          (lofat-place-file fat32$c root-d-e path file1))))
  :hints (("goal" :in-theory (enable lofat-place-file lofat-place-file-helper
                                     lofat-regular-file-p
                                     lofat-directory-file-p)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (and (equal (mv-nth 1
                                 (lofat-place-file fat32$c root-d-e path file1))
                         0)
                  (equal (lofat-file->contents file1)
                         (lofat-file->contents file2))
                  (lofat-file-p file1)
                  (lofat-file-p file2))
             (equal (mv-nth 1
                            (lofat-place-file fat32$c root-d-e path file2))
                    0)))))

(encapsulate
  ()

  (local
   (in-theory
    (e/d (lofat-to-hifat root-d-e-list
                         d-e-cc-of-lofat-place-file-coincident-1
                         hifat-place-file)
         (lofat-place-file-correctness-1
          (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                    . 5)))))

  (set-default-hints '(("Goal" :do-not-induct t)))

  (defthm
    lofat-pwrite-refinement-lemma-30
    (implies
     (and
      (<=
       (len (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))))
       65534)
      (good-root-d-e-p (pseudo-root-d-e fat32$c)
                       fat32$c)
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
     (<=
      (len
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents
                 (mv-nth 0
                         (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                           path file))
                 (pseudo-root-d-e fat32$c)))))
      65534))
    :hints
    (("goal"
      :cases ((consp (cdr path)))))
    :rule-classes :linear)

  (defthm
    lofat-pwrite-refinement-lemma-32
    (implies
     (and
      (good-root-d-e-p (pseudo-root-d-e fat32$c)
                       fat32$c)
      (fat32-filename-list-p path)
      (lofat-file-p file)
      (equal (mv-nth 1
                     (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                       path file))
             0)
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
       2)
      (< 0
         (len (explode (lofat-file->contents file)))))
     (>=
      (+ (count-free-clusters (effective-fat fat32$c))
         (- (len (make-clusters (lofat-file->contents file)
                                (cluster-size fat32$c))))
         (len (mv-nth 0
                      (d-e-cc fat32$c (pseudo-root-d-e fat32$c)))))
      (len
       (make-clusters
        (nats=>string
         (insert-d-e
          (string=>nats
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (d-e-set-first-cluster-file-size
           (mv-nth
            0
            (find-d-e
             (make-d-e-list
              (mv-nth 0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
             (car path)))
           (nth 0
                (find-n-free-clusters (effective-fat fat32$c)
                                      1))
           (len (explode (lofat-file->contents file))))))
        (cluster-size fat32$c)))))
    :hints (("goal" :cases ((consp (cdr path)))))
    :rule-classes :linear)

  (defthm
    lofat-pwrite-refinement-lemma-36
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
      (equal (mv-nth 1
                     (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                       path file))
             0)
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
       2)
      (not (equal (lofat-file->contents file) "")))
     (not-intersectp-list
      (list (d-e-first-cluster (pseudo-root-d-e fat32$c)))
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
          (mv-nth
           0
           (find-d-e
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (car path)))
          (nth 0
               (find-n-free-clusters (effective-fat fat32$c)
                                     1))
          (len (explode (lofat-file->contents file)))))
        (max-entry-count fat32$c)))))
    :hints
    (("goal"
      :cases ((consp (cdr path)))
      :restrict ((not-intersectp-list-when-subsetp-1
                  ((y (mv-nth 0
                              (d-e-cc fat32$c
                                      (pseudo-root-d-e fat32$c))))))))))

  (defthm
    lofat-pwrite-refinement-lemma-46
    (implies
     (and
      (equal (len (make-clusters (lofat-file->contents file)
                                 (cluster-size fat32$c)))
             (count-free-clusters (effective-fat fat32$c)))
      (good-root-d-e-p (pseudo-root-d-e fat32$c)
                       fat32$c)
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
      (not (lofat-directory-file-p file))
      (<=
       (+ 2 (count-of-clusters fat32$c))
       (d-e-first-cluster
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path)))))
      (< 0
         (len (explode (lofat-file->contents file)))))
     (not-intersectp-list
      (list (d-e-first-cluster (pseudo-root-d-e fat32$c)))
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth
         0
         (place-contents
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
           fat32$c)
          (mv-nth
           0
           (find-d-e
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (car path)))
          (lofat-file->contents file)
          (len (explode (lofat-file->contents file)))
          (nth 0
               (find-n-free-clusters (effective-fat fat32$c)
                                     1))))
        (place-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (d-e-set-first-cluster-file-size
          (mv-nth
           0
           (find-d-e
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (car path)))
          (nth 0
               (find-n-free-clusters (effective-fat fat32$c)
                                     1))
          (len (explode (lofat-file->contents file)))))
        (max-entry-count fat32$c)))))
    :hints
    (("goal"
      :restrict ((not-intersectp-list-when-subsetp-1
                  ((y (mv-nth 0
                              (d-e-cc fat32$c
                                      (pseudo-root-d-e fat32$c))))))))))

  (defthm
    lofat-pwrite-refinement-lemma-47
    (implies
     (and
      (good-root-d-e-p (pseudo-root-d-e fat32$c)
                       fat32$c)
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
      (not (lofat-directory-file-p file))
      (<=
       (+ 2 (count-of-clusters fat32$c))
       (d-e-first-cluster
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path)))))
      (< 0
         (len (explode (lofat-file->contents file))))
      (<= (+ -1
             (len (make-clusters (lofat-file->contents file)
                                 (cluster-size fat32$c))))
          (+ -1
             (count-free-clusters (effective-fat fat32$c)))))
     (not-intersectp-list
      (list (d-e-first-cluster (pseudo-root-d-e fat32$c)))
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth
         0
         (place-contents
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
           fat32$c)
          (mv-nth
           0
           (find-d-e
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (car path)))
          (lofat-file->contents file)
          (len (explode (lofat-file->contents file)))
          (nth 0
               (find-n-free-clusters (effective-fat fat32$c)
                                     1))))
        (place-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (d-e-set-first-cluster-file-size
          (mv-nth
           0
           (find-d-e
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (car path)))
          (nth 0
               (find-n-free-clusters (effective-fat fat32$c)
                                     1))
          (len (explode (lofat-file->contents file)))))
        (max-entry-count fat32$c)))))
    :hints
    (("goal"
      :restrict ((not-intersectp-list-when-subsetp-1
                  ((y (mv-nth 0
                              (d-e-cc fat32$c
                                      (pseudo-root-d-e fat32$c))))))))))

  (defthm
    lofat-pwrite-refinement-lemma-31
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
      (not (lofat-directory-file-p file))
      (not
       (d-e-directory-p
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path)))))
      (consp path)
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
       (+ 2 (count-of-clusters fat32$c)))
      (<
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32$c)
          (mv-nth
           0
           (d-e-cc
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))))
          (make-list-ac
           (len
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path))))))
           0 nil))
         1))
       (+ 2 (count-of-clusters fat32$c)))
      (<=
       (+ -1
          (len (make-clusters (lofat-file->contents file)
                              (cluster-size fat32$c))))
       (+
        -1
        (count-free-clusters (effective-fat fat32$c))
        (len
         (mv-nth
          0
          (d-e-cc
           fat32$c
           (mv-nth
            0
            (find-d-e
             (make-d-e-list
              (mv-nth 0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
             (car path))))))))
      (< 0
         (len (explode (lofat-file->contents file)))))
     (not-intersectp-list
      (mv-nth 0
              (d-e-cc fat32$c (pseudo-root-d-e fat32$c)))
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth
         0
         (update-dir-contents
          (mv-nth
           0
           (place-contents
            (update-fati
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path)))))
                (make-list-ac
                 (len
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path))))))
                 0 nil))
               1))
             (fat32-update-lower-28
              (fati
               (nth
                0
                (find-n-free-clusters
                 (set-indices-in-fa-table
                  (effective-fat fat32$c)
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path)))))
                  (make-list-ac
                   (len
                    (mv-nth
                     0
                     (d-e-cc
                      fat32$c
                      (mv-nth
                       0
                       (find-d-e
                        (make-d-e-list
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c (pseudo-root-d-e fat32$c))))
                        (car path))))))
                   0 nil))
                 1))
               fat32$c)
              268435455)
             (mv-nth
              0
              (clear-cc
               fat32$c
               (d-e-first-cluster
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path))))
               (d-e-file-size
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))))
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))
            (lofat-file->contents file)
            (len (explode (lofat-file->contents file)))
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32$c)
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path)))))
               (make-list-ac
                (len
                 (mv-nth
                  0
                  (d-e-cc
                   fat32$c
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list
                      (mv-nth
                       0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                     (car path))))))
                0 nil))
              1))))
          (d-e-first-cluster (pseudo-root-d-e fat32$c))
          (nats=>string
           (insert-d-e
            (string=>nats
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (d-e-set-first-cluster-file-size
             (mv-nth
              0
              (find-d-e
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
               (car path)))
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path)))))
                (make-list-ac
                 (len
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path))))))
                 0 nil))
               1))
             (len (explode (lofat-file->contents file))))))))
        (place-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (d-e-set-first-cluster-file-size
          (mv-nth
           0
           (find-d-e
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (car path)))
          (nth
           0
           (find-n-free-clusters
            (set-indices-in-fa-table
             (effective-fat fat32$c)
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth
                   0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                 (car path)))))
             (make-list-ac
              (len
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path))))))
              0 nil))
            1))
          (len (explode (lofat-file->contents file)))))
        (max-entry-count fat32$c)))))
    :hints
    (("goal"
      :in-theory
      (e/d (update-dir-contents-correctness-1 place-contents-correctness-1)
           ((:rewrite place-contents-expansion-2)))
      :use
      (:instance
       (:rewrite place-contents-expansion-2)
       (first-cluster
        (nth
         0
         (find-n-free-clusters
          (set-indices-in-fa-table
           (effective-fat fat32$c)
           (mv-nth
            0
            (d-e-cc
             fat32$c
             (mv-nth
              0
              (find-d-e
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
               (car path)))))
           (make-list-ac
            (len
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth 0
                          (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                 (car path))))))
            0 nil))
          1)))
       (file-length (len (explode (lofat-file->contents file))))
       (contents (lofat-file->contents file))
       (d-e
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path))))
       (fat32$c
        (update-fati
         (nth
          0
          (find-n-free-clusters
           (set-indices-in-fa-table
            (effective-fat fat32$c)
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path)))))
            (make-list-ac
             (len
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth 0
                           (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path))))))
             0 nil))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (set-indices-in-fa-table
              (effective-fat fat32$c)
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth 0
                           (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))
              (make-list-ac
               (len
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path))))))
               0 nil))
             1))
           fat32$c)
          268435455)
         (mv-nth
          0
          (clear-cc
           fat32$c
           (d-e-first-cluster
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path))))
           (d-e-file-size
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path))))))))))))

  (defthm
    lofat-pwrite-refinement-lemma-33
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
      (not (lofat-directory-file-p file))
      (not
       (d-e-directory-p
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path)))))
      (consp path)
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
       (+ 2 (count-of-clusters fat32$c)))
      (<
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32$c)
          (mv-nth
           0
           (d-e-cc
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))))
          (make-list-ac
           (len
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path))))))
           0 nil))
         1))
       (+ 2 (count-of-clusters fat32$c)))
      (<=
       (+ -1
          (len (make-clusters (lofat-file->contents file)
                              (cluster-size fat32$c))))
       (+
        -1
        (count-free-clusters (effective-fat fat32$c))
        (len
         (mv-nth
          0
          (d-e-cc
           fat32$c
           (mv-nth
            0
            (find-d-e
             (make-d-e-list
              (mv-nth 0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
             (car path))))))))
      (< 0
         (len (explode (lofat-file->contents file)))))
     (equal
      (mv-nth
       3
       (lofat-to-hifat-helper
        (mv-nth
         0
         (update-dir-contents
          (mv-nth
           0
           (place-contents
            (update-fati
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path)))))
                (make-list-ac
                 (len
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path))))))
                 0 nil))
               1))
             (fat32-update-lower-28
              (fati
               (nth
                0
                (find-n-free-clusters
                 (set-indices-in-fa-table
                  (effective-fat fat32$c)
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path)))))
                  (make-list-ac
                   (len
                    (mv-nth
                     0
                     (d-e-cc
                      fat32$c
                      (mv-nth
                       0
                       (find-d-e
                        (make-d-e-list
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c (pseudo-root-d-e fat32$c))))
                        (car path))))))
                   0 nil))
                 1))
               fat32$c)
              268435455)
             (mv-nth
              0
              (clear-cc
               fat32$c
               (d-e-first-cluster
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path))))
               (d-e-file-size
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))))
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))
            (lofat-file->contents file)
            (len (explode (lofat-file->contents file)))
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32$c)
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path)))))
               (make-list-ac
                (len
                 (mv-nth
                  0
                  (d-e-cc
                   fat32$c
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list
                      (mv-nth
                       0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                     (car path))))))
                0 nil))
              1))))
          (d-e-first-cluster (pseudo-root-d-e fat32$c))
          (nats=>string
           (insert-d-e
            (string=>nats
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (d-e-set-first-cluster-file-size
             (mv-nth
              0
              (find-d-e
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
               (car path)))
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path)))))
                (make-list-ac
                 (len
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path))))))
                 0 nil))
               1))
             (len (explode (lofat-file->contents file))))))))
        (place-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (d-e-set-first-cluster-file-size
          (mv-nth
           0
           (find-d-e
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (car path)))
          (nth
           0
           (find-n-free-clusters
            (set-indices-in-fa-table
             (effective-fat fat32$c)
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth
                   0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                 (car path)))))
             (make-list-ac
              (len
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path))))))
              0 nil))
            1))
          (len (explode (lofat-file->contents file)))))
        (max-entry-count fat32$c)))
      0))
    :hints
    (("goal"
      :in-theory
      (e/d (update-dir-contents-correctness-1 place-contents-correctness-1)
           ((:rewrite place-contents-expansion-2)))
      :use
      (:instance
       (:rewrite place-contents-expansion-2)
       (first-cluster
        (nth
         0
         (find-n-free-clusters
          (set-indices-in-fa-table
           (effective-fat fat32$c)
           (mv-nth
            0
            (d-e-cc
             fat32$c
             (mv-nth
              0
              (find-d-e
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
               (car path)))))
           (make-list-ac
            (len
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth 0
                          (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                 (car path))))))
            0 nil))
          1)))
       (file-length (len (explode (lofat-file->contents file))))
       (contents (lofat-file->contents file))
       (d-e
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path))))
       (fat32$c
        (update-fati
         (nth
          0
          (find-n-free-clusters
           (set-indices-in-fa-table
            (effective-fat fat32$c)
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path)))))
            (make-list-ac
             (len
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth 0
                           (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path))))))
             0 nil))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (set-indices-in-fa-table
              (effective-fat fat32$c)
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth 0
                           (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))
              (make-list-ac
               (len
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path))))))
               0 nil))
             1))
           fat32$c)
          268435455)
         (mv-nth
          0
          (clear-cc
           fat32$c
           (d-e-first-cluster
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path))))
           (d-e-file-size
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path))))))))))))

  (defthm
    lofat-pwrite-refinement-lemma-34
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
      (not (lofat-directory-file-p file))
      (consp path)
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
       (+ 2 (count-of-clusters fat32$c)))
      (<
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32$c)
          (mv-nth
           0
           (d-e-cc
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))))
          (make-list-ac
           (len
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path))))))
           0 nil))
         1))
       (+ 2 (count-of-clusters fat32$c)))
      (<=
       (+ -1
          (len (make-clusters (lofat-file->contents file)
                              (cluster-size fat32$c))))
       (+
        -1
        (count-free-clusters (effective-fat fat32$c))
        (len
         (mv-nth
          0
          (d-e-cc
           fat32$c
           (mv-nth
            0
            (find-d-e
             (make-d-e-list
              (mv-nth 0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
             (car path))))))))
      (< 0
         (len (explode (lofat-file->contents file))))
      (member-equal
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32$c)
          (mv-nth
           0
           (d-e-cc
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))))
          (make-list-ac
           (len
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path))))))
           0 nil))
         1))
       (mv-nth
        0
        (d-e-cc
         fat32$c
         (mv-nth
          0
          (find-d-e
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
           (car path)))))))
     (not-intersectp-list
      (list (d-e-first-cluster (pseudo-root-d-e fat32$c)))
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth
         0
         (update-dir-contents
          (mv-nth
           0
           (place-contents
            (update-fati
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path)))))
                (make-list-ac
                 (len
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path))))))
                 0 nil))
               1))
             (fat32-update-lower-28
              (fati
               (nth
                0
                (find-n-free-clusters
                 (set-indices-in-fa-table
                  (effective-fat fat32$c)
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path)))))
                  (make-list-ac
                   (len
                    (mv-nth
                     0
                     (d-e-cc
                      fat32$c
                      (mv-nth
                       0
                       (find-d-e
                        (make-d-e-list
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c (pseudo-root-d-e fat32$c))))
                        (car path))))))
                   0 nil))
                 1))
               fat32$c)
              268435455)
             (mv-nth
              0
              (clear-cc
               fat32$c
               (d-e-first-cluster
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path))))
               (d-e-file-size
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))))
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))
            (lofat-file->contents file)
            (len (explode (lofat-file->contents file)))
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32$c)
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path)))))
               (make-list-ac
                (len
                 (mv-nth
                  0
                  (d-e-cc
                   fat32$c
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list
                      (mv-nth
                       0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                     (car path))))))
                0 nil))
              1))))
          (d-e-first-cluster (pseudo-root-d-e fat32$c))
          (nats=>string
           (insert-d-e
            (string=>nats
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (d-e-set-first-cluster-file-size
             (mv-nth
              0
              (find-d-e
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
               (car path)))
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path)))))
                (make-list-ac
                 (len
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path))))))
                 0 nil))
               1))
             (len (explode (lofat-file->contents file))))))))
        (place-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (d-e-set-first-cluster-file-size
          (mv-nth
           0
           (find-d-e
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (car path)))
          (nth
           0
           (find-n-free-clusters
            (set-indices-in-fa-table
             (effective-fat fat32$c)
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth
                   0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                 (car path)))))
             (make-list-ac
              (len
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path))))))
              0 nil))
            1))
          (len (explode (lofat-file->contents file)))))
        (max-entry-count fat32$c)))))
    :hints
    (("goal"
      :in-theory
      (e/d (update-dir-contents-correctness-1 place-contents-correctness-1)
           ((:rewrite place-contents-expansion-2)))
      :use
      (:instance
       (:rewrite place-contents-expansion-2)
       (first-cluster
        (nth
         0
         (find-n-free-clusters
          (set-indices-in-fa-table
           (effective-fat fat32$c)
           (mv-nth
            0
            (d-e-cc
             fat32$c
             (mv-nth
              0
              (find-d-e
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
               (car path)))))
           (make-list-ac
            (len
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth 0
                          (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                 (car path))))))
            0 nil))
          1)))
       (file-length (len (explode (lofat-file->contents file))))
       (contents (lofat-file->contents file))
       (d-e
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path))))
       (fat32$c
        (update-fati
         (nth
          0
          (find-n-free-clusters
           (set-indices-in-fa-table
            (effective-fat fat32$c)
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path)))))
            (make-list-ac
             (len
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth 0
                           (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path))))))
             0 nil))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (set-indices-in-fa-table
              (effective-fat fat32$c)
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth 0
                           (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))
              (make-list-ac
               (len
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path))))))
               0 nil))
             1))
           fat32$c)
          268435455)
         (mv-nth
          0
          (clear-cc
           fat32$c
           (d-e-first-cluster
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path))))
           (d-e-file-size
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))))))))
      :restrict ((not-intersectp-list-when-subsetp-1
                  ((y (mv-nth 0
                              (d-e-cc fat32$c
                                      (pseudo-root-d-e fat32$c))))))))))

  (defthm
    lofat-pwrite-refinement-lemma-35
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
      (not (lofat-directory-file-p file))
      (consp path)
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
       (+ 2 (count-of-clusters fat32$c)))
      (<
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32$c)
          (mv-nth
           0
           (d-e-cc
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))))
          (make-list-ac
           (len
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path))))))
           0 nil))
         1))
       (+ 2 (count-of-clusters fat32$c)))
      (<=
       (+ -1
          (len (make-clusters (lofat-file->contents file)
                              (cluster-size fat32$c))))
       (+
        -1
        (count-free-clusters (effective-fat fat32$c))
        (len
         (mv-nth
          0
          (d-e-cc
           fat32$c
           (mv-nth
            0
            (find-d-e
             (make-d-e-list
              (mv-nth 0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
             (car path))))))))
      (< 0
         (len (explode (lofat-file->contents file))))
      (member-equal
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32$c)
          (mv-nth
           0
           (d-e-cc
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))))
          (make-list-ac
           (len
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path))))))
           0 nil))
         1))
       (mv-nth
        0
        (d-e-cc
         fat32$c
         (mv-nth
          0
          (find-d-e
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
           (car path)))))))
     (not-intersectp-list
      (find-n-free-clusters
       (update-nth
        (d-e-first-cluster (pseudo-root-d-e fat32$c))
        (fat32-update-lower-28
         (fati
          (d-e-first-cluster (pseudo-root-d-e fat32$c))
          (mv-nth
           0
           (place-contents
            (update-fati
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path)))))
                (make-list-ac
                 (len
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path))))))
                 0 nil))
               1))
             (fat32-update-lower-28
              (fati
               (nth
                0
                (find-n-free-clusters
                 (set-indices-in-fa-table
                  (effective-fat fat32$c)
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path)))))
                  (make-list-ac
                   (len
                    (mv-nth
                     0
                     (d-e-cc
                      fat32$c
                      (mv-nth
                       0
                       (find-d-e
                        (make-d-e-list
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c (pseudo-root-d-e fat32$c))))
                        (car path))))))
                   0 nil))
                 1))
               fat32$c)
              268435455)
             (mv-nth
              0
              (clear-cc
               fat32$c
               (d-e-first-cluster
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path))))
               (d-e-file-size
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))))
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))
            (lofat-file->contents file)
            (len (explode (lofat-file->contents file)))
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32$c)
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path)))))
               (make-list-ac
                (len
                 (mv-nth
                  0
                  (d-e-cc
                   fat32$c
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list
                      (mv-nth
                       0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                     (car path))))))
                0 nil))
              1)))))
         268435455)
        (set-indices-in-fa-table
         (effective-fat
          (mv-nth
           0
           (place-contents
            (update-fati
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path)))))
                (make-list-ac
                 (len
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path))))))
                 0 nil))
               1))
             (fat32-update-lower-28
              (fati
               (nth
                0
                (find-n-free-clusters
                 (set-indices-in-fa-table
                  (effective-fat fat32$c)
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path)))))
                  (make-list-ac
                   (len
                    (mv-nth
                     0
                     (d-e-cc
                      fat32$c
                      (mv-nth
                       0
                       (find-d-e
                        (make-d-e-list
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c (pseudo-root-d-e fat32$c))))
                        (car path))))))
                   0 nil))
                 1))
               fat32$c)
              268435455)
             (mv-nth
              0
              (clear-cc
               fat32$c
               (d-e-first-cluster
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path))))
               (d-e-file-size
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))))
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))
            (lofat-file->contents file)
            (len (explode (lofat-file->contents file)))
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32$c)
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path)))))
               (make-list-ac
                (len
                 (mv-nth
                  0
                  (d-e-cc
                   fat32$c
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list
                      (mv-nth
                       0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                     (car path))))))
                0 nil))
              1)))))
         (mv-nth 0
                 (d-e-cc fat32$c (pseudo-root-d-e fat32$c)))
         (make-list-ac
          (len (mv-nth 0
                       (d-e-cc fat32$c (pseudo-root-d-e fat32$c))))
          0 nil)))
       (+
        -1
        (len
         (make-clusters
          (implode
           (nats=>chars
            (insert-d-e
             (string=>nats
              (mv-nth 0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
             (d-e-set-first-cluster-file-size
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path)))
              (nth
               0
               (find-n-free-clusters
                (set-indices-in-fa-table
                 (effective-fat fat32$c)
                 (mv-nth
                  0
                  (d-e-cc
                   fat32$c
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list
                      (mv-nth
                       0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                     (car path)))))
                 (make-list-ac
                  (len
                   (mv-nth
                    0
                    (d-e-cc
                     fat32$c
                     (mv-nth
                      0
                      (find-d-e
                       (make-d-e-list
                        (mv-nth
                         0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                       (car path))))))
                  0 nil))
                1))
              (len (explode (lofat-file->contents file)))))))
          (cluster-size fat32$c)))))
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth
         0
         (update-dir-contents
          (mv-nth
           0
           (place-contents
            (update-fati
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path)))))
                (make-list-ac
                 (len
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path))))))
                 0 nil))
               1))
             (fat32-update-lower-28
              (fati
               (nth
                0
                (find-n-free-clusters
                 (set-indices-in-fa-table
                  (effective-fat fat32$c)
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path)))))
                  (make-list-ac
                   (len
                    (mv-nth
                     0
                     (d-e-cc
                      fat32$c
                      (mv-nth
                       0
                       (find-d-e
                        (make-d-e-list
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c (pseudo-root-d-e fat32$c))))
                        (car path))))))
                   0 nil))
                 1))
               fat32$c)
              268435455)
             (mv-nth
              0
              (clear-cc
               fat32$c
               (d-e-first-cluster
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path))))
               (d-e-file-size
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))))
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))
            (lofat-file->contents file)
            (len (explode (lofat-file->contents file)))
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32$c)
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path)))))
               (make-list-ac
                (len
                 (mv-nth
                  0
                  (d-e-cc
                   fat32$c
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list
                      (mv-nth
                       0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                     (car path))))))
                0 nil))
              1))))
          (d-e-first-cluster (pseudo-root-d-e fat32$c))
          (nats=>string
           (insert-d-e
            (string=>nats
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (d-e-set-first-cluster-file-size
             (mv-nth
              0
              (find-d-e
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
               (car path)))
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path)))))
                (make-list-ac
                 (len
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path))))))
                 0 nil))
               1))
             (len (explode (lofat-file->contents file))))))))
        (place-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (d-e-set-first-cluster-file-size
          (mv-nth
           0
           (find-d-e
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (car path)))
          (nth
           0
           (find-n-free-clusters
            (set-indices-in-fa-table
             (effective-fat fat32$c)
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth
                   0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                 (car path)))))
             (make-list-ac
              (len
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path))))))
              0 nil))
            1))
          (len (explode (lofat-file->contents file)))))
        (max-entry-count fat32$c)))))
    :hints
    (("goal"
      :in-theory (disable (:rewrite place-contents-expansion-2))
      :use
      (:instance
       (:rewrite place-contents-expansion-2)
       (first-cluster
        (nth
         0
         (find-n-free-clusters
          (set-indices-in-fa-table
           (effective-fat fat32$c)
           (mv-nth
            0
            (d-e-cc
             fat32$c
             (mv-nth
              0
              (find-d-e
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
               (car path)))))
           (make-list-ac
            (len
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth 0
                          (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                 (car path))))))
            0 nil))
          1)))
       (file-length (len (explode (lofat-file->contents file))))
       (contents (lofat-file->contents file))
       (d-e
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path))))
       (fat32$c
        (update-fati
         (nth
          0
          (find-n-free-clusters
           (set-indices-in-fa-table
            (effective-fat fat32$c)
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path)))))
            (make-list-ac
             (len
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth 0
                           (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path))))))
             0 nil))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (set-indices-in-fa-table
              (effective-fat fat32$c)
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth 0
                           (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))
              (make-list-ac
               (len
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path))))))
               0 nil))
             1))
           fat32$c)
          268435455)
         (mv-nth
          0
          (clear-cc
           fat32$c
           (d-e-first-cluster
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path))))
           (d-e-file-size
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path))))))))))))

  (defthm
    lofat-pwrite-refinement-lemma-37
    (implies
     (and
      (good-root-d-e-p (pseudo-root-d-e fat32$c)
                       fat32$c)
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
      (not (lofat-directory-file-p file))
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
       (+ 2 (count-of-clusters fat32$c)))
      (<
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32$c)
          (mv-nth
           0
           (d-e-cc
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))))
          (make-list-ac
           (len
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path))))))
           0 nil))
         1))
       (+ 2 (count-of-clusters fat32$c)))
      (equal
       (fat32-entry-mask
        (fati
         (nth
          0
          (find-n-free-clusters
           (set-indices-in-fa-table
            (effective-fat fat32$c)
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path)))))
            (make-list-ac
             (len
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth 0
                           (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path))))))
             0 nil))
           1))
         fat32$c))
       0)
      (<=
       (+ -1
          (len (make-clusters (lofat-file->contents file)
                              (cluster-size fat32$c))))
       (+
        -1
        (count-free-clusters (effective-fat fat32$c))
        (len
         (mv-nth
          0
          (d-e-cc
           fat32$c
           (mv-nth
            0
            (find-d-e
             (make-d-e-list
              (mv-nth 0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
             (car path))))))))
      (< 0
         (len (explode (lofat-file->contents file)))))
     (not-intersectp-list
      (list (d-e-first-cluster (pseudo-root-d-e fat32$c)))
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth
         0
         (place-contents
          (update-fati
           (nth
            0
            (find-n-free-clusters
             (set-indices-in-fa-table
              (effective-fat fat32$c)
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))
              (make-list-ac
               (len
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path))))))
               0 nil))
             1))
           (fat32-update-lower-28
            (fati
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path)))))
                (make-list-ac
                 (len
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path))))))
                 0 nil))
               1))
             fat32$c)
            268435455)
           (mv-nth
            0
            (clear-cc
             fat32$c
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path))))
             (d-e-file-size
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path)))))))
          (mv-nth
           0
           (find-d-e
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (car path)))
          (lofat-file->contents file)
          (len (explode (lofat-file->contents file)))
          (nth
           0
           (find-n-free-clusters
            (set-indices-in-fa-table
             (effective-fat fat32$c)
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth
                   0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                 (car path)))))
             (make-list-ac
              (len
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path))))))
              0 nil))
            1))))
        (place-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (d-e-set-first-cluster-file-size
          (mv-nth
           0
           (find-d-e
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (car path)))
          (nth
           0
           (find-n-free-clusters
            (set-indices-in-fa-table
             (effective-fat fat32$c)
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth
                   0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                 (car path)))))
             (make-list-ac
              (len
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path))))))
              0 nil))
            1))
          (len (explode (lofat-file->contents file)))))
        (max-entry-count fat32$c)))))
    :hints
    (("goal"
      :restrict ((not-intersectp-list-when-subsetp-1
                  ((y (mv-nth 0
                              (d-e-cc fat32$c
                                      (pseudo-root-d-e fat32$c))))))))))

  (defthm
    lofat-pwrite-refinement-lemma-38
    (implies
     (and
      (good-root-d-e-p (pseudo-root-d-e fat32$c)
                       fat32$c)
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
      (not (lofat-directory-file-p file))
      (< 0
         (len (explode (lofat-file->contents file))))
      (<= (+ -1
             (len (make-clusters (lofat-file->contents file)
                                 (cluster-size fat32$c))))
          (+ -1
             (count-free-clusters (effective-fat fat32$c)))))
     (not-intersectp-list
      (list (d-e-first-cluster (pseudo-root-d-e fat32$c)))
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth
         0
         (place-contents
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
           fat32$c)
          (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                     nil)
          (lofat-file->contents file)
          (len (explode (lofat-file->contents file)))
          (nth 0
               (find-n-free-clusters (effective-fat fat32$c)
                                     1))))
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
      :restrict ((not-intersectp-list-when-subsetp-1
                  ((y (mv-nth 0
                              (d-e-cc fat32$c
                                      (pseudo-root-d-e fat32$c))))))))))

  (defthm
    lofat-pwrite-refinement-lemma-39
    (implies
     (and
      (not (consp (cdr path)))
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
      (not (lofat-directory-file-p file))
      (not
       (d-e-directory-p
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path)))))
      (consp path)
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
       (+ 2 (count-of-clusters fat32$c)))
      (<=
       (+ -1
          (len (make-clusters (lofat-file->contents file)
                              (cluster-size fat32$c))))
       (+
        -1
        (count-free-clusters (effective-fat fat32$c))
        (len
         (mv-nth
          0
          (d-e-cc
           fat32$c
           (mv-nth
            0
            (find-d-e
             (make-d-e-list
              (mv-nth 0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
             (car path))))))))
      (< 0
         (len (explode (lofat-file->contents file))))
      (member-equal
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32$c)
          (mv-nth
           0
           (d-e-cc
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))))
          (make-list-ac
           (len
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path))))))
           0 nil))
         1))
       (mv-nth
        0
        (d-e-cc
         fat32$c
         (mv-nth
          0
          (find-d-e
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
           (car path)))))))
     (hifat-equiv
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth
         0
         (update-dir-contents
          (mv-nth
           0
           (place-contents
            (update-fati
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path)))))
                (make-list-ac
                 (len
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path))))))
                 0 nil))
               1))
             (fat32-update-lower-28
              (fati
               (nth
                0
                (find-n-free-clusters
                 (set-indices-in-fa-table
                  (effective-fat fat32$c)
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path)))))
                  (make-list-ac
                   (len
                    (mv-nth
                     0
                     (d-e-cc
                      fat32$c
                      (mv-nth
                       0
                       (find-d-e
                        (make-d-e-list
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c (pseudo-root-d-e fat32$c))))
                        (car path))))))
                   0 nil))
                 1))
               fat32$c)
              268435455)
             (mv-nth
              0
              (clear-cc
               fat32$c
               (d-e-first-cluster
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path))))
               (d-e-file-size
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))))
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))
            (lofat-file->contents file)
            (len (explode (lofat-file->contents file)))
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32$c)
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path)))))
               (make-list-ac
                (len
                 (mv-nth
                  0
                  (d-e-cc
                   fat32$c
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list
                      (mv-nth
                       0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                     (car path))))))
                0 nil))
              1))))
          (d-e-first-cluster (pseudo-root-d-e fat32$c))
          (nats=>string
           (insert-d-e
            (string=>nats
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (d-e-set-first-cluster-file-size
             (mv-nth
              0
              (find-d-e
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
               (car path)))
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path)))))
                (make-list-ac
                 (len
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path))))))
                 0 nil))
               1))
             (len (explode (lofat-file->contents file))))))))
        (place-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (d-e-set-first-cluster-file-size
          (mv-nth
           0
           (find-d-e
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (car path)))
          (nth
           0
           (find-n-free-clusters
            (set-indices-in-fa-table
             (effective-fat fat32$c)
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth
                   0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                 (car path)))))
             (make-list-ac
              (len
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path))))))
              0 nil))
            1))
          (len (explode (lofat-file->contents file)))))
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
        (m1-file d-e (lofat-file->contents file))))))
    :hints
    (("goal"
      :in-theory (e/d nil
                      ((:rewrite place-contents-expansion-2)))
      :use
      (:instance
       (:rewrite place-contents-expansion-2)
       (first-cluster
        (nth
         0
         (find-n-free-clusters
          (set-indices-in-fa-table
           (effective-fat fat32$c)
           (mv-nth
            0
            (d-e-cc
             fat32$c
             (mv-nth
              0
              (find-d-e
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
               (car path)))))
           (make-list-ac
            (len
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth 0
                          (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                 (car path))))))
            0 nil))
          1)))
       (file-length (len (explode (lofat-file->contents file))))
       (contents (lofat-file->contents file))
       (d-e
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path))))
       (fat32$c
        (update-fati
         (nth
          0
          (find-n-free-clusters
           (set-indices-in-fa-table
            (effective-fat fat32$c)
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path)))))
            (make-list-ac
             (len
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth 0
                           (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path))))))
             0 nil))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (set-indices-in-fa-table
              (effective-fat fat32$c)
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth 0
                           (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))
              (make-list-ac
               (len
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path))))))
               0 nil))
             1))
           fat32$c)
          268435455)
         (mv-nth
          0
          (clear-cc
           fat32$c
           (d-e-first-cluster
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path))))
           (d-e-file-size
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path))))))))))))

  (defthm
    lofat-pwrite-refinement-lemma-40
    (implies
     (and
      (equal
       (len
        (mv-nth
         0
         (d-e-cc
          fat32$c
          (mv-nth
           0
           (find-d-e
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (car path))))))
       1)
      (good-root-d-e-p (pseudo-root-d-e fat32$c)
                       fat32$c)
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
      (<=
       1
       (count-free-clusters
        (set-indices-in-fa-table
         (effective-fat fat32$c)
         (mv-nth
          0
          (d-e-cc
           fat32$c
           (mv-nth
            0
            (find-d-e
             (make-d-e-list
              (mv-nth 0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
             (car path)))))
         '(0))))
      (d-e-directory-p
       (mv-nth
        0
        (find-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (car path))))
      (member-equal
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32$c)
          (mv-nth
           0
           (d-e-cc
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))))
          '(0))
         1))
       (mv-nth
        0
        (d-e-cc
         fat32$c
         (mv-nth
          0
          (find-d-e
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
           (car path)))))))
     (not-intersectp-list
      (list (d-e-first-cluster (pseudo-root-d-e fat32$c)))
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth
         0
         (place-contents
          (update-fati
           (nth
            0
            (find-n-free-clusters
             (set-indices-in-fa-table
              (effective-fat fat32$c)
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))
              '(0))
             1))
           (fat32-update-lower-28
            (fati
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path)))))
                '(0))
               1))
             fat32$c)
            268435455)
           (mv-nth
            0
            (clear-cc
             fat32$c
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path))))
             2097152)))
          (mv-nth
           0
           (find-d-e
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (car path)))
          (make-empty-subdir-contents
           (nth
            0
            (find-n-free-clusters
             (set-indices-in-fa-table
              (effective-fat fat32$c)
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))
              '(0))
             1))
           (d-e-first-cluster (pseudo-root-d-e fat32$c)))
          0
          (nth
           0
           (find-n-free-clusters
            (set-indices-in-fa-table
             (effective-fat fat32$c)
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth
                   0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                 (car path)))))
             '(0))
            1))))
        (place-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (d-e-set-first-cluster-file-size
          (mv-nth
           0
           (find-d-e
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (car path)))
          (nth
           0
           (find-n-free-clusters
            (set-indices-in-fa-table
             (effective-fat fat32$c)
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth
                   0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                 (car path)))))
             '(0))
            1))
          0))
        (max-entry-count fat32$c)))))
    :hints
    (("goal"
      :restrict ((not-intersectp-list-when-subsetp-1
                  ((y (mv-nth 0
                              (d-e-cc fat32$c
                                      (pseudo-root-d-e fat32$c))))))))))

  (defthm
    lofat-pwrite-refinement-lemma-41
    (implies
     (and
      (good-root-d-e-p (pseudo-root-d-e fat32$c)
                       fat32$c)
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
      (d-e-directory-p
       (mv-nth
        0
        (find-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (car path))))
      (<
       (d-e-first-cluster
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path))))
       (+ 2 (count-of-clusters fat32$c)))
      (member-equal
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32$c)
          (mv-nth
           0
           (d-e-cc
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))))
          (make-list-ac
           (len
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path))))))
           0 nil))
         1))
       (mv-nth
        0
        (d-e-cc
         fat32$c
         (mv-nth
          0
          (find-d-e
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
           (car path)))))))
     (not-intersectp-list
      (list (d-e-first-cluster (pseudo-root-d-e fat32$c)))
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth
         0
         (place-contents
          (update-fati
           (nth
            0
            (find-n-free-clusters
             (set-indices-in-fa-table
              (effective-fat fat32$c)
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))
              (make-list-ac
               (len
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path))))))
               0 nil))
             1))
           (fat32-update-lower-28
            (fati
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path)))))
                (make-list-ac
                 (len
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path))))))
                 0 nil))
               1))
             fat32$c)
            268435455)
           (mv-nth
            0
            (clear-cc
             fat32$c
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path))))
             2097152)))
          (mv-nth
           0
           (find-d-e
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (car path)))
          (make-empty-subdir-contents
           (nth
            0
            (find-n-free-clusters
             (set-indices-in-fa-table
              (effective-fat fat32$c)
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))
              (make-list-ac
               (len
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path))))))
               0 nil))
             1))
           (d-e-first-cluster (pseudo-root-d-e fat32$c)))
          0
          (nth
           0
           (find-n-free-clusters
            (set-indices-in-fa-table
             (effective-fat fat32$c)
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth
                   0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                 (car path)))))
             (make-list-ac
              (len
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path))))))
              0 nil))
            1))))
        (place-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (d-e-set-first-cluster-file-size
          (mv-nth
           0
           (find-d-e
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (car path)))
          (nth
           0
           (find-n-free-clusters
            (set-indices-in-fa-table
             (effective-fat fat32$c)
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth
                   0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                 (car path)))))
             (make-list-ac
              (len
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path))))))
              0 nil))
            1))
          0))
        (max-entry-count fat32$c)))))
    :hints
    (("goal"
      :restrict ((not-intersectp-list-when-subsetp-1
                  ((y (mv-nth 0
                              (d-e-cc fat32$c
                                      (pseudo-root-d-e fat32$c))))))))))

  (defthm
    lofat-pwrite-refinement-lemma-42
    (implies
     (and
      (good-root-d-e-p (pseudo-root-d-e fat32$c)
                       fat32$c)
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
      (d-e-directory-p
       (mv-nth
        0
        (find-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (car path))))
      (<
       (d-e-first-cluster
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path))))
       (+ 2 (count-of-clusters fat32$c)))
      (<
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32$c)
          (mv-nth
           0
           (d-e-cc
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))))
          (make-list-ac
           (len
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path))))))
           0 nil))
         1))
       (+ 2 (count-of-clusters fat32$c)))
      (equal
       (fat32-entry-mask
        (fati
         (nth
          0
          (find-n-free-clusters
           (set-indices-in-fa-table
            (effective-fat fat32$c)
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path)))))
            (make-list-ac
             (len
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth 0
                           (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path))))))
             0 nil))
           1))
         fat32$c))
       0))
     (not-intersectp-list
      (list (d-e-first-cluster (pseudo-root-d-e fat32$c)))
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth
         0
         (place-contents
          (update-fati
           (nth
            0
            (find-n-free-clusters
             (set-indices-in-fa-table
              (effective-fat fat32$c)
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))
              (make-list-ac
               (len
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path))))))
               0 nil))
             1))
           (fat32-update-lower-28
            (fati
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path)))))
                (make-list-ac
                 (len
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path))))))
                 0 nil))
               1))
             fat32$c)
            268435455)
           (mv-nth
            0
            (clear-cc
             fat32$c
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path))))
             2097152)))
          (mv-nth
           0
           (find-d-e
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (car path)))
          (make-empty-subdir-contents
           (nth
            0
            (find-n-free-clusters
             (set-indices-in-fa-table
              (effective-fat fat32$c)
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))
              (make-list-ac
               (len
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path))))))
               0 nil))
             1))
           (d-e-first-cluster (pseudo-root-d-e fat32$c)))
          0
          (nth
           0
           (find-n-free-clusters
            (set-indices-in-fa-table
             (effective-fat fat32$c)
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth
                   0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                 (car path)))))
             (make-list-ac
              (len
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path))))))
              0 nil))
            1))))
        (place-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (d-e-set-first-cluster-file-size
          (mv-nth
           0
           (find-d-e
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (car path)))
          (nth
           0
           (find-n-free-clusters
            (set-indices-in-fa-table
             (effective-fat fat32$c)
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth
                   0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                 (car path)))))
             (make-list-ac
              (len
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path))))))
              0 nil))
            1))
          0))
        (max-entry-count fat32$c)))))
    :hints
    (("goal"
      :restrict ((not-intersectp-list-when-subsetp-1
                  ((y (mv-nth 0
                              (d-e-cc fat32$c
                                      (pseudo-root-d-e fat32$c))))))))))

  (defthm
    lofat-pwrite-refinement-lemma-43
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
      (consp path)
      (<= 1
          (count-free-clusters (effective-fat fat32$c))))
     (not-intersectp-list
      (list (d-e-first-cluster (pseudo-root-d-e fat32$c)))
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth
         0
         (place-contents
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
           fat32$c)
          (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                     t)
          (make-empty-subdir-contents
           (nth 0
                (find-n-free-clusters (effective-fat fat32$c)
                                      1))
           (d-e-first-cluster (pseudo-root-d-e fat32$c)))
          0
          (nth 0
               (find-n-free-clusters (effective-fat fat32$c)
                                     1))))
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
      :restrict ((not-intersectp-list-when-subsetp-1
                  ((y (mv-nth 0
                              (d-e-cc fat32$c
                                      (pseudo-root-d-e fat32$c))))))))))

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
      (or (stringp (lofat-file->contents file))
          (equal (lofat-file->contents file) nil))
      (not
       (equal
        (mv-nth 1
                (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                  path file))
        28))
      (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
         (max-entry-count fat32$c)))
     (and
      (equal
       (mv-nth
        1
        (lofat-to-hifat
         (mv-nth 0
                 (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                   path file))))
       0)
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat
         (mv-nth 0
                 (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                   path file))))
       (mv-nth
        0
        (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                          path
                          (m1-file d-e (lofat-file->contents file)))))
      (equal
       (mv-nth
        1
        (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                          path
                          (m1-file d-e (lofat-file->contents file))))
       (mv-nth 1
               (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                 path file)))))
    :hints
    (("goal"
      :do-not-induct t
      :cases ((atom (cdr path)))
      :in-theory (disable lofat-place-file hifat-place-file)
      :use (:instance lofat-place-file-correctness-1
                      (root-d-e (pseudo-root-d-e fat32$c))
                      (entry-limit (max-entry-count fat32$c)))
      :expand (:free (fat32$c file root-d-e)
                     (lofat-place-file fat32$c root-d-e nil file)))
     (if (not stable-under-simplificationp)
         nil
       '(:in-theory (enable lofat-place-file hifat-place-file))))
    :otf-flg t))

(defthm
  lofat-mkdir-refinement-lemma-8
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
                                    (pseudo-root-d-e fat32$c)))))))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (lofat-fs-p fat32$c)
          (fat32-filename-list-p path)
          (equal (mv-nth 1 (lofat-to-hifat fat32$c))
                 0)
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
      0)))))

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
  lofat-mkdir-refinement-lemma-9
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
    (or (lofat-regular-file-p file)
        (equal (lofat-file->contents file) nil))
    (not (equal (mv-nth 1
                        (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                          path file))
                28)))
   (hifat-equiv
    (mv-nth 0
            (lofat-to-hifat
             (mv-nth 0
                     (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                       path file))))
    (mv-nth
     0
     (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                       path
                       (make-m1-file :contents (lofat-file->contents file)
                                     :d-e (lofat-file->d-e file))))))
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
  lofat-mkdir-refinement-lemma-15
  (implies
   (not (equal d-e (d-e-fix nil)))
   (equal
    (mv-nth 1
            (lofat-place-file fat32$c root-d-e path
                              (list (cons 'd-e d-e)
                                    (cons 'contents contents))))
    (mv-nth 1
            (lofat-place-file fat32$c root-d-e path
                              (list (cons 'd-e (d-e-fix nil))
                                    (cons 'contents contents))))))
  :hints (("goal" :do-not-induct t
           :in-theory (disable lofat-mkdir-refinement-lemma-14)
           :use (:instance lofat-mkdir-refinement-lemma-14
                           (d-e1 d-e)
                           (d-e2 (d-e-fix nil))))))

(defthmd
  lofat-mkdir-refinement-lemma-12
  (true-equiv (true-fix x) x)
  :rule-classes :rewrite-quoted-constant)

(defthm
  lofat-mkdir-refinement-lemma-13
  (implies
   (and (lofat-fs-p fat32$c)
        (equal (mv-nth 1 (lofat-to-hifat fat32$c))
               0))
   (and
    (no-duplicatesp-equal (mv-nth 0
                                  (d-e-cc fat32$c (pseudo-root-d-e fat32$c))))
    (equal (mv-nth 1
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))
           0)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-to-hifat))))

(defthm
  lofat-mkdir-refinement-lemma-27
  (implies
   (and (fat32-filename-list-p path)
        (equal (mv-nth 1 (lofat-to-hifat fat32$c))
               0)
        (not (consp (cdr path)))
        (consp path)
        (not (equal (mv-nth 1
                            (find-d-e (mv-nth 0 (root-d-e-list fat32$c))
                                      (car path)))
                    0)))
   (equal
    (mv-nth 1
            (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                              path
                              '((d-e 0 0 0 0 0 0 0 0 0 0 0 16
                                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                (contents))))
    0))
  :hints
  (("goal" :do-not-induct t
    :in-theory
    (e/d (lofat-mkdir hifat-place-file root-d-e-list
                      lofat-place-file-helper lofat-to-hifat)
         ((:rewrite d-e-cc-of-update-dir-contents-coincident)
          (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident)))
    :expand ((:free (fs) (hifat-find-file fs nil))
             (:free (fs file)
                    (hifat-place-file fs nil file))
             (:free (fat32$c file root-d-e)
                    (lofat-place-file fat32$c root-d-e nil file))))))

(defthm
  lofat-mkdir-refinement-lemma-28
  (implies
   (and
    (equal (count-free-clusters (effective-fat fat32$c))
           0)
    (lofat-fs-p fat32$c)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       (max-entry-count fat32$c)))
     0)
    (consp (cdr path))
    (equal
     (mv-nth
      1
      (hifat-find-file
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         (max-entry-count fat32$c)))
       (dirname path)))
     0)
    (lofat-directory-file-p
     (mv-nth
      0
      (lofat-find-file
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       (dirname path))))
    (not
     (equal
      (mv-nth
       1
       (hifat-find-file
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
          (max-entry-count fat32$c)))
        path))
      0)))
   (equal
    (mv-nth 1
            (lofat-place-file fat32$c root-d-e path
                              '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                (contents))))
    28))
  :hints (("goal" :in-theory (e/d (dirname lofat-place-file
                                           hifat-find-file basename)
                                  (abs-pwrite-correctness-lemma-37)))
          ("subgoal *1/4.10" :expand ((len (cddr path)))))
  :rule-classes
  (:rewrite
   (:linear
    :corollary
    (implies
     (and
      (not
       (equal
        (mv-nth 1
                (lofat-place-file fat32$c root-d-e path
                                  '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                                         0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                    (contents))))
        28))
      (lofat-fs-p fat32$c)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         (max-entry-count fat32$c)))
       0)
      (consp (cdr path))
      (equal
       (mv-nth
        1
        (hifat-find-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (max-entry-count fat32$c)))
         (dirname path)))
       0)
      (lofat-directory-file-p
       (mv-nth
        0
        (lofat-find-file
         fat32$c
         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         (dirname path))))
      (not
       (equal
        (mv-nth
         1
         (hifat-find-file
          (mv-nth
           0
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (max-entry-count fat32$c)))
          path))
        0)))
     (> (count-free-clusters (effective-fat fat32$c))
        0)))))

(defthm
  lofat-mkdir-refinement-lemma-31
  (implies
   (and
    (lofat-fs-p fat32$c)
    (equal (mv-nth 1 (lofat-to-hifat fat32$c))
           0)
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
    (consp (cdr path))
    (equal (mv-nth 1
                   (lofat-find-file fat32$c
                                    (mv-nth 0 (root-d-e-list fat32$c))
                                    (dirname path)))
           0)
    (lofat-directory-file-p
     (mv-nth 0
             (lofat-find-file fat32$c
                              (mv-nth 0 (root-d-e-list fat32$c))
                              (dirname path))))
    (not (equal (mv-nth 1
                        (lofat-find-file fat32$c
                                         (mv-nth 0 (root-d-e-list fat32$c))
                                         path))
                0))
    (lofat-directory-file-p
     (mv-nth 0
             (lofat-find-file fat32$c
                              (mv-nth 0 (root-d-e-list fat32$c))
                              path))))
   (not (< (count-free-clusters (effective-fat fat32$c))
           1)))
  :hints
  (("goal" :do-not-induct t
    :in-theory
    (e/d (lofat-mkdir hifat-place-file root-d-e-list
                      lofat-place-file-helper lofat-to-hifat)
         ((:rewrite d-e-cc-of-update-dir-contents-coincident)
          (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident)))
    :expand ((:free (fs) (hifat-find-file fs nil))
             (:free (fs file)
                    (hifat-place-file fs nil file))
             (:free (fat32$c file root-d-e)
                    (lofat-place-file fat32$c root-d-e nil file)))))
  :rule-classes
  (:rewrite :linear))

(defthm
  lofat-mkdir-refinement-lemma-32
  (implies
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       (max-entry-count fat32$c)))
     0)
    (not
     (equal
      (mv-nth
       1
       (lofat-place-file fat32$c root-d-e path
                         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (contents))))
      28))
    (consp (cdr path))
    (not
     (equal
      (mv-nth
       1
       (lofat-find-file
        fat32$c
        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
        path))
      0)))
   (lofat-directory-file-p
    (mv-nth 0
            (lofat-find-file
             fat32$c
             (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
             path))))
  :hints (("goal" :in-theory (e/d (dirname lofat-place-file
                                           hifat-find-file basename)
                                  (abs-pwrite-correctness-lemma-37)))))

(defthm
  lofat-mkdir-refinement-lemma-11
  (implies
   (and
    (equal (count-free-clusters (effective-fat fat32$c))
           0)
    (lofat-fs-p fat32$c)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       (max-entry-count fat32$c)))
     0)
    (not
     (equal
      (mv-nth
       1
       (lofat-place-file fat32$c root-d-e path
                         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (contents))))
      28))
    (consp (cdr path))
    (equal
     (mv-nth
      1
      (hifat-find-file
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         (max-entry-count fat32$c)))
       (dirname path)))
     0)
    (lofat-directory-file-p
     (mv-nth
      0
      (lofat-find-file
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       (dirname path)))))
   (equal
    (mv-nth 1
            (lofat-find-file
             fat32$c
             (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
             path))
    0))
  :hints (("goal" :in-theory (e/d (dirname lofat-place-file
                                           hifat-find-file basename)
                                  (abs-pwrite-correctness-lemma-37)))))

(defthm
  lofat-mkdir-refinement-lemma-35
  (implies
   (and
    (lofat-fs-p fat32$c)
    (equal (mv-nth 1 (lofat-to-hifat fat32$c))
           0)
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
    (equal (mv-nth 1
                   (lofat-find-file fat32$c
                                    (mv-nth 0 (root-d-e-list fat32$c))
                                    (dirname path)))
           0)
    (consp (cdr path))
    (lofat-directory-file-p
     (mv-nth 0
             (lofat-find-file fat32$c
                              (mv-nth 0 (root-d-e-list fat32$c))
                              (dirname path))))
    (not (equal (mv-nth 1
                        (lofat-find-file fat32$c
                                         (mv-nth 0 (root-d-e-list fat32$c))
                                         path))
                0)))
   (>= (count-free-clusters (effective-fat fat32$c))
       '1))
  :hints
  (("goal" :do-not-induct t
    :in-theory
    (e/d (lofat-mkdir hifat-place-file root-d-e-list
                      lofat-place-file-helper lofat-to-hifat)
         ((:rewrite d-e-cc-of-update-dir-contents-coincident)
          (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident)))
    :expand ((:free (fs) (hifat-find-file fs nil))
             (:free (fs file)
                    (hifat-place-file fs nil file))
             (:free (fat32$c file root-d-e)
                    (lofat-place-file fat32$c root-d-e nil file)))))
  :rule-classes
  (:linear
   (:linear
    :corollary
    (implies
     (and
      (lofat-fs-p fat32$c)
      (equal (mv-nth 1 (lofat-to-hifat fat32$c))
             0)
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
      (consp (cdr path))
      (equal (mv-nth 1
                     (lofat-find-file fat32$c
                                      (mv-nth 0 (root-d-e-list fat32$c))
                                      (dirname path)))
             0)
      (lofat-directory-file-p
       (mv-nth 0
               (lofat-find-file fat32$c
                                (mv-nth 0 (root-d-e-list fat32$c))
                                (dirname path))))
      (not (equal (mv-nth 1
                          (lofat-find-file fat32$c
                                           (mv-nth 0 (root-d-e-list fat32$c))
                                           path))
                  0)))
     (>= (count-free-clusters (effective-fat fat32$c))
         '1)))))

(defthm
  lofat-mkdir-refinement-lemma-36
  (implies
   (and
    (lofat-fs-p fat32$c)
    (equal (mv-nth 1 (lofat-to-hifat fat32$c))
           0)
    (consp (cdr path))
    (equal (mv-nth 1
                   (lofat-find-file fat32$c
                                    (mv-nth 0 (root-d-e-list fat32$c))
                                    (dirname path)))
           0)
    (lofat-directory-file-p
     (mv-nth 0
             (lofat-find-file fat32$c
                              (mv-nth 0 (root-d-e-list fat32$c))
                              (dirname path))))
    (not (equal (mv-nth 1
                        (lofat-find-file fat32$c
                                         (mv-nth 0 (root-d-e-list fat32$c))
                                         path))
                0))
    (equal
     (mv-nth 1
             (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                               path
                               '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                 (contents))))
     0))
   (not (< (count-free-clusters (effective-fat fat32$c))
           '1)))
  :rule-classes :linear
  :hints
  (("goal" :do-not-induct t
    :in-theory
    (e/d (lofat-mkdir hifat-place-file root-d-e-list
                      lofat-place-file-helper lofat-to-hifat)
         ((:rewrite d-e-cc-of-update-dir-contents-coincident)
          (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident)))
    :expand ((:free (fs) (hifat-find-file fs nil))
             (:free (fs file)
                    (hifat-place-file fs nil file))
             (:free (fat32$c file root-d-e)
                    (lofat-place-file fat32$c root-d-e nil file)))))
  :otf-flg t)

(encapsulate
  ()

  (local
   ;; The following event raises a question as to whether congruential
   ;; rewriting of quoted constants is happening as expected. It should go
   ;; through without any hints or instructions, I think, but the reader can
   ;; check that it doesn't by submitting it without instructions. The
   ;; instructions, very simply, illustrate the rewrite I expect to happen
   ;; automatically - the rewriter should use the rule
   ;; (:congruence lofat-mkdir-refinement-lemma-14),
   ;; which is identical (except for a vacuous hypothesis) to the rule
   ;; (:rewrite lofat-mkdir-refinement-lemma-14)
   ;; used in these instructions, to descend to the subexpression
   ;; '(0 0 0 0 0 0 0 0 0 0 0 16 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0),
   ;; a constant, and rewrite it with the expression
   ;; (true-fix '(0 0 0 0 0 0 0 0 0 0 0 16 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
   ;; as dictated by the rule
   ;; (:rewrite-quoted-constant lofat-mkdir-refinement-lemma-12).
   ;; That should allow an equality substitution by making use of the
   ;; hypothesis which completes the proof. Is there a simple explanation I'm
   ;; missing as to why this doesn't happen?
   (defthm
     lemma
     (implies
      (equal
       (mv-nth
        1
        (lofat-to-hifat
         (mv-nth
          0
          (lofat-place-file
           fat32$c (pseudo-root-d-e fat32$c)
           path
           (cons (cons 'd-e
                       (true-fix '(0 0 0 0 0 0 0 0 0 0 0 16 0
                                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)))
                 '((contents)))))))
       0)
      (equal
       (mv-nth
        1
        (lofat-to-hifat
         (mv-nth
          0
          (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                            path
                            '((d-e 0 0 0 0 0 0 0 0 0 0 0 16
                                   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                              (contents))))))
       0))
     :instructions
     (:promote
      (:dive 1 2 1 2)
      (:rewrite lofat-mkdir-refinement-lemma-14
                ((d-e2 (true-fix '(0 0 0 0 0 0 0 0 0 0 0 16 0 0
                                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)))))
      :top (:dive 1)
      :=))))

(defthm
  lofat-mkdir-refinement
  (implies
   (and
    (lofat-fs-p fat32$c)
    (fat32-filename-list-p path)
    (equal (mv-nth 1 (lofat-to-hifat fat32$c))
           0)
    ;; Let's discuss this hypothesis.
    ;;
    ;; This is something that we actually should
    ;; be able to derive from the structure of lofat-to-hifat-helper. That is,
    ;; we should be able to say that if we're able to do lofat-to-hifat-helper
    ;; with the max-entry-count parameter after the lofat-place-file operation,
    ;; then obviously we must have the capacity for that number of entries. And
    ;; if we don't have the capacity for that number of entries, then we must
    ;; be contradicting the hypothesis about the error code of lofat-place-file
    ;; being other than EIO. That is, this hypothesis should be implied by
    ;; that one, because in the case where that one holds, we must have gotten
    ;; away without an error while creating the new entry, and that means we
    ;; couldn't have exceeded the max entry count!
    ;;
    ;; That kind of reasoning, however, is exactly the kind of thing we gave up
    ;; on a while earlier. Now is not a great time to start either.
    (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
       (max-entry-count fat32$c))
    (not
     (equal
      (mv-nth 2 (lofat-mkdir fat32$c path))
      *enospc*)))
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
                                    path)))
        (equal (mv-nth 2 (lofat-mkdir fat32$c path))
               (mv-nth 2
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
;; (defthm
;;   lofat-mkdir-refinement
;;   (implies
;;    (and
;;     (lofat-fs-p fat32$c)
;;     (fat32-filename-list-p path)
;;     (equal (mv-nth 1 (lofat-to-hifat fat32$c))
;;            0)
;;     Let's discuss this hypothesis.

;;     This is something that we actually should
;;     be able to derive from the structure of lofat-to-hifat-helper. That is,
;;     we should be able to say that if we're able to do lofat-to-hifat-helper
;;     with the max-entry-count parameter after the lofat-place-file operation,
;;     then obviously we must have the capacity for that number of entries. And
;;     if we don't have the capacity for that number of entries, then we must
;;     be contradicting the hypothesis about the error code of lofat-place-file
;;     being other than EIO. That is, this hypothesis should be implied by
;;     that one, because in the case where that one holds, we must have gotten
;;     away without an error while creating the new entry, and that means we
;;     couldn't have exceeded the max entry count!

;;     That kind of reasoning, however, is exactly the kind of thing we gave up
;;     on a while earlier. Now is not a great time to start either.
;;     (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
;;        (max-entry-count fat32$c))
;;     (not
;;      (equal
;;       (mv-nth 2 (lofat-mkdir fat32$c path))
;;       *enospc*)))
;;    (and (equal (mv-nth 1
;;                        (lofat-to-hifat (mv-nth 0 (lofat-mkdir fat32$c path))))
;;                0)
;;         (hifat-equiv
;;          (mv-nth 0
;;                  (lofat-to-hifat (mv-nth 0 (lofat-mkdir fat32$c path))))
;;          (mv-nth 0
;;                  (hifat-mkdir (mv-nth 0 (lofat-to-hifat fat32$c))
;;                               path)))
;;         (equal (mv-nth 1 (lofat-mkdir fat32$c path))
;;                (mv-nth 1
;;                        (hifat-mkdir (mv-nth 0 (lofat-to-hifat fat32$c))
;;                                     path)))
;;         (equal (mv-nth 2 (lofat-mkdir fat32$c path))
;;                (mv-nth 2
;;                        (hifat-mkdir (mv-nth 0 (lofat-to-hifat fat32$c))
;;                                     path)))))
;;   :hints
;;   (("goal" :do-not-induct t
;;     :in-theory
;;     (e/d (lofat-mkdir lofat-mkdir-refinement-lemma-12)
;;          ((:rewrite d-e-cc-of-update-dir-contents-coincident)
;;           (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident)
;;           lofat-place-file
;;           lofat-mkdir-refinement-lemma-15))
;;     :expand ((:free (fs) (hifat-find-file fs nil))
;;              (:free (fs file)
;;                     (hifat-place-file fs nil file))
;;              (:free (fat32$c file root-d-e)
;;                     (lofat-place-file fat32$c root-d-e nil file))))))

;; Counterexample. Three theorems below indicate what is going wrong.
;; (thm
;;  (implies
;;   (and
;;    (consp path)
;;    (not (consp (cdr path)))
;;    (not (d-e-p d-e1))
;;    (d-e-directory-p
;;     (mv-nth
;;      0
;;      (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
;;                (fat32-filename-fix (car path)))))
;;    (<
;;     2097152
;;     (+
;;      64
;;      (* 32
;;         (len (make-d-e-list (mv-nth 0
;;                                     (d-e-cc-contents fat32$c root-d-e)))))))
;;    (d-e-p d-e2)
;;    (stringp contents)
;;    (> 4294967296 (len (explode contents))))
;;   (and (equal (mv-nth 1
;;                       (lofat-place-file fat32$c root-d-e path
;;                                         (list (cons 'd-e d-e1)
;;                                               (cons 'contents contents))))
;;               *enospc*)
;;        (equal (mv-nth 1
;;                       (lofat-place-file fat32$c root-d-e path
;;                                         (list (cons 'd-e d-e2)
;;                                               (cons 'contents contents))))
;;               *enoent*)))
;;  :hints
;;  (("goal"
;;    :do-not-induct t
;;    :in-theory (e/d (lofat-place-file lofat-place-file-helper
;;                                      lofat-regular-file-p
;;                                      lofat-directory-file-p
;;                                      lofat-file-p lofat-file->contents
;;                                      m1-file-hifat-file-alist-fix m1-file)
;;                    (m1-file-hifat-file-alist-fix-normalisation
;;                     abs-mkdir-correctness-lemma-36)))))
;; (thm
;;  (implies
;;   (and
;;    (consp path)
;;    (not (consp (cdr path)))
;;    (not (d-e-p d-e1))
;;    (d-e-directory-p
;;     (mv-nth
;;      0
;;      (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
;;                (fat32-filename-fix (car path)))))
;;    (<
;;     2097152
;;     (+
;;      64
;;      (* 32
;;         (len (make-d-e-list (mv-nth 0
;;                                     (d-e-cc-contents fat32$c root-d-e))))))))
;;   (b*
;;       ((file (list (cons 'd-e d-e1)
;;                    (cons 'contents contents)))
;;        (update-dir-contents-error-code
;;         (lofat-place-file-helper fat32$c root-d-e path file))
;;        ((unless (consp path)) nil)
;;        (name (mbe :logic (fat32-filename-fix (car path))
;;                   :exec (car path)))
;;        ((mv dir-contents &)
;;         (d-e-cc-contents fat32$c root-d-e))
;;        (d-e-list (make-d-e-list dir-contents))
;;        ((mv d-e error-code)
;;         (find-d-e d-e-list name))
;;        (d-e (if (equal error-code 0)
;;                 d-e (make-d-e-with-filename name)))
;;        (d-e (if (equal error-code 0)
;;                 d-e
;;                 (d-e-install-directory-bit d-e (lofat-directory-file-p file))))
;;        ((when (and (not (equal error-code 0))
;;                    (consp (cdr path))))
;;         nil)
;;        ((when (and (consp (cdr path))
;;                    (not (d-e-directory-p d-e))))
;;         nil)
;;        (first-cluster (d-e-first-cluster d-e))
;;        ((when (and (not (equal error-code 0))
;;                    (consp (cdr path))))
;;         nil)
;;        ((when (and (or (< first-cluster 2)
;;                        (<= (+ 2 (count-of-clusters fat32$c))
;;                            first-cluster))
;;                    (consp (cdr path))))
;;         nil)
;;        ((when (consp (cdr path))) nil)
;;        (length (if (d-e-directory-p d-e)
;;                    *ms-max-dir-size* (d-e-file-size d-e)))
;;        ((when (and (d-e-directory-p d-e)
;;                    (lofat-regular-file-p file)))
;;         nil)
;;        ((when (and (not (d-e-directory-p d-e))
;;                    (lofat-directory-file-p file)))
;;         nil)
;;        ((mv fat32$c &)
;;         (if (or (< first-cluster 2)
;;                 (<= (+ 2 (count-of-clusters fat32$c))
;;                     first-cluster))
;;             (mv fat32$c 0)
;;             (clear-cc fat32$c first-cluster length)))
;;        (file-length (if (lofat-regular-file-p file)
;;                         (length (lofat-file->contents file))
;;                         (+ *ms-d-e-length* *ms-d-e-length*)))
;;        (new-dir-contents
;;         (nats=>string (insert-d-e (string=>nats dir-contents)
;;                                   (d-e-set-first-cluster-file-size d-e 0 0))))
;;        ((when (and (zp file-length)
;;                    (<= (length new-dir-contents)
;;                        *ms-max-dir-size*)))
;;         nil)
;;        ((when (zp file-length)) nil)
;;        (indices (stobj-find-n-free-clusters fat32$c 1))
;;        ((when (< (len indices) 1)) t)
;;        (new-dir-contents-length
;;         (b* (((mv & error-code)
;;               (find-d-e (make-d-e-list dir-contents)
;;                         (d-e-filename d-e))))
;;           (if (zp error-code)
;;               (+ 64
;;                  (* 32 (len (make-d-e-list dir-contents))))
;;               (+ 96
;;                  (* 32
;;                     (len (make-d-e-list dir-contents)))))))
;;        ((unless (and (<= new-dir-contents-length
;;                          *ms-max-dir-size*)
;;                      (equal update-dir-contents-error-code 0)))
;;         t))
;;     nil))
;;  :hints
;;  (("goal"
;;    :do-not-induct t
;;    :in-theory (e/d (lofat-place-file lofat-place-file-helper
;;                                      lofat-regular-file-p
;;                                      lofat-directory-file-p
;;                                      lofat-file-p lofat-file->contents
;;                                      m1-file-hifat-file-alist-fix m1-file)
;;                    (m1-file-hifat-file-alist-fix-normalisation
;;                     abs-mkdir-correctness-lemma-36)))))
;; (thm
;;  (implies
;;   (and
;;    (consp path)
;;    (not (consp (cdr path)))
;;    (d-e-directory-p
;;     (mv-nth
;;      0
;;      (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
;;                (fat32-filename-fix (car path)))))
;;    (d-e-p d-e2)
;;    (stringp contents)
;;    (> 4294967296 (len (explode contents))))
;;   (b*
;;       ((file (list (cons 'd-e d-e2)
;;                    (cons 'contents contents)))
;;        ((unless (consp path)) nil)
;;        (name (mbe :logic (fat32-filename-fix (car path))
;;                   :exec (car path)))
;;        ((mv dir-contents &)
;;         (d-e-cc-contents fat32$c root-d-e))
;;        (d-e-list (make-d-e-list dir-contents))
;;        ((mv d-e error-code)
;;         (find-d-e d-e-list name))
;;        (d-e (if (equal error-code 0)
;;                 d-e (make-d-e-with-filename name)))
;;        (d-e (if (equal error-code 0)
;;                 d-e
;;                 (d-e-install-directory-bit d-e (lofat-directory-file-p file))))
;;        ((when (and (not (equal error-code 0))
;;                    (consp (cdr path))))
;;         nil)
;;        ((when (and (consp (cdr path))
;;                    (not (d-e-directory-p d-e))))
;;         nil)
;;        (first-cluster (d-e-first-cluster d-e))
;;        ((when (and (not (equal error-code 0))
;;                    (consp (cdr path))))
;;         nil)
;;        ((when (and (or (< first-cluster 2)
;;                        (<= (+ 2 (count-of-clusters fat32$c))
;;                            first-cluster))
;;                    (consp (cdr path))))
;;         nil)
;;        ((when (consp (cdr path))) nil)
;;        ((when (and (d-e-directory-p d-e)
;;                    (lofat-regular-file-p file)))
;;         t))
;;     nil))
;;  :hints
;;  (("goal"
;;    :do-not-induct t
;;    :in-theory (e/d (lofat-place-file lofat-place-file-helper
;;                                      lofat-regular-file-p
;;                                      lofat-directory-file-p
;;                                      lofat-file-p lofat-file->contents
;;                                      m1-file-hifat-file-alist-fix m1-file)
;;                    (m1-file-hifat-file-alist-fix-normalisation
;;                     abs-mkdir-correctness-lemma-36)))))

(defthm
  absfat-oracle-single-step-refinement-lemma-1
  (implies
   (frame-reps-fs frame
                  (mv-nth 0 (lofat-to-hifat fat32$c)))
   (frame-reps-fs (mv-nth 0 (abs-mkdir frame (lofat-st->path st)))
                  (mv-nth 0
                          (hifat-mkdir (mv-nth 0 (lofat-to-hifat fat32$c))
                                       (lofat-st->path st)))))
  :hints (("goal" :do-not-induct t
           :in-theory (disable abs-mkdir-correctness-2 hifat-mkdir)
           :use (:instance abs-mkdir-correctness-2
                           (path (lofat-st->path st))))))

(defthm
  absfat-oracle-single-step-refinement-lemma-2
  (implies
   (frame-reps-fs frame
                  (mv-nth 0 (lofat-to-hifat fat32$c)))
   (frame-reps-fs (mv-nth 0
                          (abs-pwrite (lofat-st->fd st)
                                      (lofat-st->buf st)
                                      (lofat-st->offset st)
                                      frame
                                      (lofat-st->fd-table st)
                                      (lofat-st->file-table st)))
                  (mv-nth 0
                          (hifat-pwrite (lofat-st->fd st)
                                        (lofat-st->buf st)
                                        (lofat-st->offset st)
                                        (mv-nth 0 (lofat-to-hifat fat32$c))
                                        (lofat-st->fd-table st)
                                        (lofat-st->file-table st)))))
  :hints (("goal" :do-not-induct t
           :in-theory (disable abs-pwrite-correctness-1 hifat-pwrite)
           :use (:instance abs-pwrite-correctness-1
                           (fd (lofat-st->fd st))
                           (buf (lofat-st->buf st))
                           (offset (lofat-st->offset st))
                           (fd-table (lofat-st->fd-table st))
                           (file-table (lofat-st->file-table st))))))

(defthm
  lofat-pwrite-refinement-lemma-1
  (implies
   (and
    (equal
     (len
      (explode
       (lofat-file-contents-fix (implode (insert-text nil offset buf)))))
     0)
    (not (stringp buf)))
   (<=
    (len (make-clusters
          (lofat-file-contents-fix (implode (insert-text nil offset buf)))
          (cluster-size fat32$c)))
    (count-free-clusters (effective-fat fat32$c))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-file-contents-fix insert-text)))
  :rule-classes :linear)

(defthm
  lofat-pwrite-refinement-lemma-2
  (implies
   (and
    (consp path)
    (not
     (equal
      (mv-nth
       1
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 (car path)))
      0))
    (equal (lofat-place-file-helper
            fat32$c root-d-e path
            (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                        (implode (insert-text nil offset buf))))
           0)
    (lofat-fs-p fat32$c)
    (fat32-filename-list-p path)
    (not (stringp buf)))
   (<=
    (len
     (make-clusters
      (lofat-file-contents-fix (implode (insert-text nil offset buf)))
      (cluster-size fat32$c)))
    (count-free-clusters (effective-fat fat32$c))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-file-contents-fix
                              insert-text lofat-place-file-helper)))
  :rule-classes :linear)

(defthm
  lofat-pwrite-refinement-lemma-3
  (implies
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       (max-entry-count fat32$c)))
     0)
    (not
     (m1-regular-file-p
      (mv-nth
       0
       (hifat-find-file
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
          (max-entry-count fat32$c)))
        path))))
    (fat32-filename-list-p path)
    (equal
     (mv-nth 1
             (lofat-place-file
              fat32$c root-d-e path
              (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                              0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                          (implode (insert-text nil offset buf)))))
     0)
    (not (stringp buf))
    (case-split
     (lofat-fs-p fat32$c)))
   (<=
    (len (make-clusters
          (lofat-file-contents-fix (implode (insert-text nil offset buf)))
          (cluster-size fat32$c)))
    (count-free-clusters (effective-fat fat32$c))))
  :hints (("goal" :in-theory (e/d (dirname lofat-place-file
                                           hifat-find-file basename)
                                  (abs-pwrite-correctness-lemma-37))))
  :rule-classes :linear)

(defthm
  lofat-pwrite-refinement-lemma-4
  (implies
   (and
    (lofat-fs-p fat32$c)
    (equal (mv-nth 1 (lofat-to-hifat fat32$c))
           0)
    (not
     (lofat-regular-file-p
      (mv-nth
       0
       (lofat-find-file fat32$c
                        (mv-nth 0 (root-d-e-list fat32$c))
                        (file-table-element->fid
                         (cdr (assoc-equal (cdr (assoc-equal fd fd-table))
                                           file-table)))))))
    (equal
     (mv-nth 1
             (lofat-place-file
              fat32$c (pseudo-root-d-e fat32$c)
              (file-table-element->fid
               (cdr (assoc-equal (cdr (assoc-equal fd fd-table))
                                 file-table)))
              (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                              0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                          (implode (insert-text nil offset buf)))))
     0)
    (not (stringp buf)))
   (not
    (<
     (count-free-clusters (effective-fat fat32$c))
     (len
      (make-clusters
       (lofat-file-contents-fix (implode$inline (insert-text nil offset buf)))
       (cluster-size fat32$c))))))
  :hints
  (("goal" :do-not-induct t
    :in-theory
    (e/d (lofat-mkdir hifat-place-file root-d-e-list
                      lofat-place-file-helper lofat-to-hifat)
         ((:rewrite d-e-cc-of-update-dir-contents-coincident)
          (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident)))
    :expand ((:free (fs) (hifat-find-file fs nil))
             (:free (fs file)
                    (hifat-place-file fs nil file))
             (:free (fat32$c file root-d-e)
                    (lofat-place-file fat32$c root-d-e nil file)))))
  :rule-classes :linear)

(defthm
  lofat-pwrite-refinement-lemma-5
  (implies
   (and
    (< (count-free-clusters (effective-fat fat32$c))
       (len (make-clusters (lofat-file->contents file)
                           (cluster-size fat32$c))))
    (lofat-regular-file-p file)
    (not (equal (mv-nth 1
                        (lofat-place-file fat32$c root-d-e path file))
                28))
    (lofat-fs-p fat32$c)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       (max-entry-count fat32$c)))
     0)
    (equal
     (mv-nth 1
             (lofat-place-file
              fat32$c root-d-e path
              (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                              0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                          (implode (insert-text nil offset buf)))))
     0)
    (consp (cdr path)))
   (m1-regular-file-p
    (mv-nth
     0
     (hifat-find-file
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
        (max-entry-count fat32$c)))
      path))))
  :hints
  (("goal"
    :in-theory (e/d (dirname lofat-place-file
                             hifat-find-file basename)
                    (abs-pwrite-correctness-lemma-37 (:i len)
                                                     (:i assoc-equal)))
    :induct
    (lofat-place-file fat32$c root-d-e path
                      (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                  (implode (insert-text nil offset buf))))
    :do-not-induct t))
  :rule-classes
  (:rewrite
   (:linear
    :corollary
    (implies
     (and
      (lofat-regular-file-p file)
      (not (equal (mv-nth 1
                          (lofat-place-file fat32$c root-d-e path file))
                  28))
      (lofat-fs-p fat32$c)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         (max-entry-count fat32$c)))
       0)
      (not
       (m1-regular-file-p
        (mv-nth
         0
         (hifat-find-file
          (mv-nth
           0
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (max-entry-count fat32$c)))
          path))))
      (equal
       (mv-nth 1
               (lofat-place-file
                fat32$c root-d-e path
                (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                            (implode (insert-text nil offset buf)))))
       0)
      (consp (cdr path)))
     (>= (count-free-clusters (effective-fat fat32$c))
         (len (make-clusters (lofat-file->contents file)
                             (cluster-size fat32$c))))))))

(defthm
  lofat-pwrite-refinement-lemma-6
  (implies
   (and
    (equal
     (len
      (explode
       (lofat-file-contents-fix (implode (insert-text nil offset buf)))))
     0)
    (not (stringp buf))
    (< (+ offset (len buf)) 4294967296))
   (hifat-equiv
    (put-assoc-equal
     name2
     (m1-file (d-e-set-first-cluster-file-size
               (d-e-install-directory-bit (make-d-e-with-filename name2)
                                          nil)
               0 0)
              "")
     (mv-nth
      0
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (max-entry-count fat32$c))))
    (put-assoc-equal
     name2
     (m1-file '(0 0 0 0 0 0 0 0 0 0 0 0
                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
              (implode (insert-text nil offset buf)))
     (mv-nth
      0
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (max-entry-count fat32$c))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (lofat-to-hifat root-d-e-list hifat-place-file
                                    insert-text lofat-file-contents-fix))
    :restrict ((not-intersectp-list-when-subsetp-1
                ((y (mv-nth 0
                            (d-e-cc fat32$c
                                    (pseudo-root-d-e fat32$c))))))))))

(defthm
  lofat-pwrite-refinement-lemma-7
  (implies (and (not (stringp buf))
                (< (+ offset (len buf)) 4294967296))
           (lofat-file-contents-p (implode (insert-text nil offset buf))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (e/d
     (lofat-to-hifat root-d-e-list hifat-place-file
                     lofat-file-contents-p insert-text)
     (lofat-mkdir-refinement-lemma-10
      (:rewrite lofat-place-file-correctness-lemma-27)
      (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-3)
      (:rewrite m1-file->contents-of-m1-file)
      (:rewrite m1-file-contents-fix-when-m1-file-contents-p)
      (:rewrite hifat-to-lofat-inversion-lemma-2)
      (:rewrite member-of-nth-when-not-intersectp)
      (:rewrite
       lofat-to-hifat-helper-of-hifat-to-lofat-helper-disjoint-lemma-1)
      (:definition non-free-index-listp)
      (:definition member-equal)
      (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident-lemma-8)
      (:rewrite d-e-cc-of-place-contents-disjoint)
      (:linear length-of-d-e-cc-contents . 1)
      (:rewrite lofat-mkdir-refinement-lemma-31)
      (:rewrite d-e-cc-contents-of-update-fati)
      (:rewrite d-e-first-cluster-of-d-e-set-first-cluster-file-size)
      (:rewrite fat32-masked-entry-fix-when-fat32-masked-entry-p)
      (:rewrite fat32-masked-entry-p-of-nth-when-fat32-masked-entry-list-p)
      (:rewrite d-e-cc-contents-of-place-contents-disjoint)))
    :restrict ((not-intersectp-list-when-subsetp-1
                ((y (mv-nth 0
                            (d-e-cc fat32$c
                                    (pseudo-root-d-e fat32$c))))))))))

(defthm
  lofat-pwrite-refinement-lemma-8
  (implies
   (and
    (< (count-free-clusters (effective-fat fat32$c))
       (len (make-clusters (implode (insert-text nil offset buf))
                           (cluster-size fat32$c))))
    (lofat-fs-p fat32$c)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       (max-entry-count fat32$c)))
     0)
    (equal
     (mv-nth 1
             (lofat-place-file
              fat32$c root-d-e path
              (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                              0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                          (implode (insert-text nil offset buf)))))
     0)
    (not (stringp buf))
    (< (+ offset (len buf)) 4294967296)
    (consp (cdr path)))
   (m1-regular-file-p
    (mv-nth
     0
     (hifat-find-file
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
        (max-entry-count fat32$c)))
      path))))
 :hints (("goal" :in-theory (e/d (dirname lofat-place-file
                                          hifat-find-file basename)
                                 (abs-pwrite-correctness-lemma-37))))
 :rule-classes
 (:rewrite
  (:linear
   :corollary
   (implies
    (and
     (not
      (m1-regular-file-p
       (mv-nth
        0
        (hifat-find-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (max-entry-count fat32$c)))
         path))))
     (lofat-fs-p fat32$c)
     (equal
      (mv-nth
       3
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
        (max-entry-count fat32$c)))
      0)
     (equal
      (mv-nth 1
              (lofat-place-file
               fat32$c root-d-e path
               (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (implode (insert-text nil offset buf)))))
      0)
     (not (stringp buf))
     (< (+ offset (len buf)) 4294967296)
     (consp (cdr path)))
    (>= (count-free-clusters (effective-fat fat32$c))
        (len (make-clusters (implode (insert-text nil offset buf))
                            (cluster-size fat32$c))))))))

(defthm
  lofat-pwrite-refinement-lemma-9
  (implies (and (not (stringp buf))
                (< (+ offset (len buf)) 4294967296))
           (m1-file-contents-p (implode$inline (insert-text nil offset buf))))
  :hints
  (("goal" :do-not-induct t
    :in-theory
    (e/d (lofat-pwrite m1-file-contents-p insert-text)
         ((:rewrite d-e-cc-of-update-dir-contents-coincident)
          (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident)
          lofat-place-file))
    :expand ((:free (fs) (hifat-find-file fs nil))
             (:free (fs file)
                    (hifat-place-file fs nil file))
             (:free (fat32$c file root-d-e)
                    (lofat-place-file fat32$c root-d-e nil file))))))

(defthm lofat-pwrite-refinement-lemma-11
  (implies (lofat-directory-file-p file)
           (true-listp (lofat-file->contents file)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-directory-file-p)))
  :rule-classes :type-prescription)

;; Should we just rewrite the basename to the car under these hypotheses?
(defthm
  lofat-pwrite-refinement-lemma-12
  (implies
   (and
    (fat32-filename-list-p path)
    (equal
     (mv-nth
      1
      (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                (car path)))
     0)
    (consp path)
    (not (consp (cdr path))))
   (equal
    (mv-nth
     1
     (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
               (basename path)))
    0))
  :hints (("goal" :do-not-induct t
           :in-theory (enable basename))))

(defthm
  lofat-pwrite-refinement-lemma-13
  (implies
   (and
    (consp path)
    (d-e-directory-p
     (mv-nth
      0
      (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                (car path))))
    (fat32-filename-list-p path)
    (not (consp (cdr path))))
   (d-e-directory-p
    (mv-nth
     0
     (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
               (basename path)))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable basename))))

(defthm lofat-pwrite-refinement-lemma-10
  (implies (and (not (stringp buf))
                (< (+ offset (len buf)) 4294967296))
           (< (len (insert-text nil offset buf))
              4294967296))
  :hints (("goal" :do-not-induct t
           :in-theory (enable insert-text)))
  :rule-classes :linear)

(defthm
  lofat-pwrite-refinement-lemma-14
  (implies
   (and
    (fat32-filename-list-p path)
    (lofat-fs-p fat32$c)
    (equal (mv-nth 1 (lofat-to-hifat fat32$c))
           0)
    (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
       (max-entry-count fat32$c))
    (not (equal (mv-nth 1
                        (lofat-find-file fat32$c
                                         (mv-nth 0 (root-d-e-list fat32$c))
                                         path))
                0))
    (not
     (equal
      (mv-nth 1
              (lofat-place-file
               fat32$c (pseudo-root-d-e fat32$c)
               path
               (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (implode (insert-text nil offset buf)))))
      28))
    (not (stringp buf))
    (< (+ offset (len buf)) 4294967296)
    (not (lofat-directory-file-p
          (mv-nth 0
                  (lofat-find-file fat32$c
                                   (mv-nth 0 (root-d-e-list fat32$c))
                                   path)))))
   (hifat-equiv
    (mv-nth
     0
     (lofat-to-hifat
      (mv-nth 0
              (lofat-place-file
               fat32$c (pseudo-root-d-e fat32$c)
               path
               (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (implode (insert-text nil offset buf)))))))
    (mv-nth
     0
     (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                       path
                       (m1-file '(0 0 0 0 0 0 0 0 0 0 0 0
                                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                (implode (insert-text nil offset buf)))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable (:rewrite lofat-mkdir-refinement-lemma-30)
                        (:rewrite lofat-mkdir-refinement-lemma-10))
    :use
    ((:instance (:rewrite lofat-mkdir-refinement-lemma-10)
                (file (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                  (implode (insert-text nil offset buf))))
                (path path)
                (fat32$c fat32$c))
     (:instance (:rewrite lofat-mkdir-refinement-lemma-30)
                (file (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                  (implode (insert-text nil offset buf))))
                (path path)
                (fat32$c fat32$c))))))

(defthm
  lofat-pwrite-refinement-lemma-15
  (implies
   (and
    (fat32-filename-list-p path)
    (lofat-fs-p fat32$c)
    (equal (mv-nth 1 (lofat-to-hifat fat32$c))
           0)
    (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
       (max-entry-count fat32$c))
    (not (equal (mv-nth 1
                        (lofat-find-file fat32$c
                                         (mv-nth 0 (root-d-e-list fat32$c))
                                         path))
                0))
    (not
     (equal
      (mv-nth 1
              (lofat-place-file
               fat32$c (pseudo-root-d-e fat32$c)
               path
               (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (implode (insert-text nil offset buf)))))
      28))
    (not (stringp buf))
    (< (+ offset (len buf)) 4294967296))
   (hifat-equiv
    (mv-nth
     0
     (lofat-to-hifat
      (mv-nth 0
              (lofat-place-file
               fat32$c (pseudo-root-d-e fat32$c)
               path
               (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (implode (insert-text nil offset buf)))))))
    (mv-nth
     0
     (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                       path
                       (m1-file '(0 0 0 0 0 0 0 0 0 0 0 0
                                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                (implode (insert-text nil offset buf)))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite lofat-mkdir-refinement-lemma-10)
                        (:rewrite lofat-mkdir-refinement-lemma-30))
    :use
    ((:instance (:rewrite lofat-mkdir-refinement-lemma-30)
                (file (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                  (implode (insert-text nil offset buf))))
                (path path)
                (fat32$c fat32$c))
     (:instance (:rewrite lofat-mkdir-refinement-lemma-10)
                (file (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                  (implode (insert-text nil offset buf))))
                (path path)
                (fat32$c fat32$c))))))

(defthm
  lofat-pwrite-refinement-lemma-16
  (implies
   (and (not (d-e-directory-p d-e))
        (lofat-fs-p fat32$c)
        (fat32-masked-entry-p (d-e-first-cluster d-e))
        (<= 2 (d-e-first-cluster d-e))
        (< (d-e-first-cluster d-e)
           (+ (count-of-clusters fat32$c) 2)))
   (equal
    (stobj-set-indices-in-fa-table
     (mv-nth 0
             (clear-cc fat32$c (d-e-first-cluster d-e)
                       (d-e-file-size d-e)))
     (mv-nth 0 (d-e-cc fat32$c d-e))
     (append
      (cdr (mv-nth 0 (d-e-cc fat32$c d-e)))
      (list
       (fat32-entry-mask (fati (car (last (mv-nth 0 (d-e-cc fat32$c d-e))))
                               fat32$c)))))
    fat32$c))
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d (d-e-cc) (clear-cc-reversibility))
    :use (:instance clear-cc-reversibility
                    (masked-current-cluster (d-e-first-cluster d-e))
                    (length (d-e-file-size d-e))))))

(defthm
  lofat-pwrite-refinement-lemma-17
  (implies
   (and (good-root-d-e-p (pseudo-root-d-e fat32$c)
                         fat32$c)
        (equal (mv-nth 1 (lofat-to-hifat fat32$c))
               0)
        (lofat-file-p file)
        (or (lofat-regular-file-p file)
            (equal (lofat-file->contents file) nil))
        (not (zp (mv-nth 1
                         (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                           path file)))))
   (equal (mv-nth 0
                  (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                    path file))
          fat32$c))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (lofat-to-hifat root-d-e-list)
                           (lofat-place-file-correctness-2))
           :use (:instance lofat-place-file-correctness-2
                           (root-d-e (pseudo-root-d-e fat32$c))
                           (entry-limit (max-entry-count fat32$c))))))

(defthm
  lofat-pwrite-refinement-lemma-18
  (implies
   (and (lofat-fs-p fat32$c)
        (fat32-filename-list-p path)
        (equal (mv-nth 1 (lofat-to-hifat fat32$c))
               0)
        (not (equal (mv-nth 1
                            (find-d-e (mv-nth 0 (root-d-e-list fat32$c))
                                      (car path)))
                    0))
        (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
           (max-entry-count fat32$c))
        (lofat-file-p file)
        (or (lofat-regular-file-p file)
            (equal (lofat-file->contents$inline file)
                   'nil)))
   (equal
    (mv-nth 1
            (lofat-to-hifat
             (mv-nth 0
                     (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                       path file))))
    0))
  :hints (("goal" :do-not-induct t
           :in-theory (disable lofat-mkdir-refinement-lemma-23)
           :use lofat-mkdir-refinement-lemma-23)))

(defthm
  lofat-pwrite-refinement-lemma-19
  (implies
   (and
    (fat32-filename-list-p path)
    (lofat-fs-p fat32$c)
    (equal (mv-nth 1 (lofat-to-hifat fat32$c))
           0)
    (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
       (max-entry-count fat32$c))
    (not (equal (mv-nth 1
                        (lofat-find-file fat32$c
                                         (mv-nth 0 (root-d-e-list fat32$c))
                                         path))
                0)))
   (equal
    (mv-nth
     1
     (lofat-to-hifat
      (mv-nth 0
              (lofat-place-file
               fat32$c (pseudo-root-d-e fat32$c)
               path
               (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (implode (insert-text nil offset buf)))))))
    0))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (update-dir-contents-correctness-1)
                    ((:rewrite lofat-mkdir-refinement-lemma-10)
                     lofat-place-file))
    :expand (:free (fat32$c root-d-e file)
                   (lofat-place-file fat32$c root-d-e nil file))
    :use ((:instance
           (:rewrite lofat-mkdir-refinement-lemma-10)
           (file (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                                 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                             (implode (insert-text nil offset buf)))))))))

(defthm
  lofat-pwrite-refinement-lemma-20
  (implies (and (natp offset)
                (< (+ offset (len (explode buf)))
                   4294967296))
           (m1-file-contents-p (implode$inline (insert-text nil offset buf))))
  :hints
  (("goal" :do-not-induct t
    :in-theory
    (e/d (lofat-pwrite m1-file-contents-p insert-text)
         ((:rewrite d-e-cc-of-update-dir-contents-coincident)
          (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident)
          lofat-place-file))
    :expand ((:free (fs) (hifat-find-file fs nil))
             (:free (fs file)
                    (hifat-place-file fs nil file))
             (:free (fat32$c file root-d-e)
                    (lofat-place-file fat32$c root-d-e nil file))))))

(defthm
  lofat-pwrite-refinement-lemma-21
  (implies (and (<= 0 offset)
                (< (+ offset (len (explode buf)))
                   4294967296))
           (lofat-file-contents-p (implode (insert-text nil offset buf))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-file-contents-p insert-text))))

(defthm lofat-pwrite-refinement-lemma-22
  (implies (and (<= 0 offset)
                (< (+ offset (len (explode buf)))
                   4294967296))
           (< (len (insert-text nil offset buf))
              4294967296))
  :rule-classes :linear
  :hints (("goal" :do-not-induct t
           :in-theory (enable insert-text))))

(defthm
  lofat-pwrite-refinement-lemma-23
  (implies
   (and
    (fat32-filename-list-p path)
    (<= 0 offset)
    (lofat-fs-p fat32$c)
    (equal (mv-nth 1 (lofat-to-hifat fat32$c))
           0)
    (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
       (max-entry-count fat32$c))
    (not (equal (mv-nth 1
                        (lofat-find-file fat32$c
                                         (mv-nth 0 (root-d-e-list fat32$c))
                                         path))
                0))
    (not
     (equal
      (mv-nth 1
              (lofat-place-file
               fat32$c (pseudo-root-d-e fat32$c)
               path
               (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (implode (insert-text nil offset buf)))))
      28))
    (< (+ offset (len (explode buf)))
       4294967296)
    (not (lofat-directory-file-p
          (mv-nth 0
                  (lofat-find-file fat32$c
                                   (mv-nth 0 (root-d-e-list fat32$c))
                                   path)))))
   (hifat-equiv
    (mv-nth
     0
     (lofat-to-hifat
      (mv-nth 0
              (lofat-place-file
               fat32$c (pseudo-root-d-e fat32$c)
               path
               (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (implode (insert-text nil offset buf)))))))
    (mv-nth
     0
     (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                       path
                       (m1-file '(0 0 0 0 0 0 0 0 0 0 0 0
                                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                (implode (insert-text nil offset buf)))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable (:rewrite lofat-mkdir-refinement-lemma-10)
                        (:rewrite lofat-mkdir-refinement-lemma-30))
    :use
    ((:instance (:rewrite lofat-mkdir-refinement-lemma-10)
                (file (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                  (implode (insert-text nil offset buf)))))
     (:instance
      (:rewrite lofat-mkdir-refinement-lemma-30)
      (file (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                        (implode (insert-text nil offset buf)))))))))

(defthm
  lofat-pwrite-refinement-lemma-24
  (implies
   (and
    (fat32-filename-list-p path)
    (<= 0 offset)
    (lofat-fs-p fat32$c)
    (equal (mv-nth 1 (lofat-to-hifat fat32$c))
           0)
    (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
       (max-entry-count fat32$c))
    (not (equal (mv-nth 1
                        (lofat-find-file fat32$c
                                         (mv-nth 0 (root-d-e-list fat32$c))
                                         path))
                0))
    (not
     (equal
      (mv-nth 1
              (lofat-place-file
               fat32$c (pseudo-root-d-e fat32$c)
               path
               (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (implode (insert-text nil offset buf)))))
      28))
    (< (+ offset (len (explode buf)))
       4294967296))
   (hifat-equiv
    (mv-nth
     0
     (lofat-to-hifat
      (mv-nth 0
              (lofat-place-file
               fat32$c (pseudo-root-d-e fat32$c)
               path
               (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (implode (insert-text nil offset buf)))))))
    (mv-nth
     0
     (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                       path
                       (m1-file '(0 0 0 0 0 0 0 0 0 0 0 0
                                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                (implode (insert-text nil offset buf)))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable (:rewrite lofat-mkdir-refinement-lemma-10)
                        (:rewrite lofat-mkdir-refinement-lemma-30))
    :use
    ((:instance (:rewrite lofat-mkdir-refinement-lemma-10)
                (file (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                  (implode (insert-text nil offset buf)))))
     (:instance
      (:rewrite lofat-mkdir-refinement-lemma-30)
      (file (lofat-file '(0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                        (implode (insert-text nil offset buf)))))))))

(defthm
  lofat-pwrite-refinement-lemma-25
  (implies
   (and
    (integerp offset)
    (<= 0 offset)
    (lofat-regular-file-p
     (mv-nth
      0
      (lofat-find-file fat32$c
                       (mv-nth 0 (root-d-e-list fat32$c))
                       (file-table-element->fid
                        (cdr (assoc-equal (cdr (assoc-equal fd fd-table))
                                          file-table))))))
    (stringp buf)
    (< (+ offset (len (explode buf)))
       4294967296))
   (m1-file-contents-p
    (implode
     (insert-text
      (explode
       (lofat-file->contents
        (mv-nth 0
                (lofat-find-file
                 fat32$c
                 (mv-nth 0 (root-d-e-list fat32$c))
                 (file-table-element->fid
                  (cdr (assoc-equal (cdr (assoc-equal fd fd-table))
                                    file-table)))))))
      offset buf))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable m1-file-contents-p
                              len-of-insert-text))))

(defthm
  lofat-pwrite-refinement-lemma-26
  (equal (lofat-place-file fat32$c root-d-e
                           path (lofat-file d-e1 contents))
         (lofat-place-file fat32$c root-d-e
                           path (lofat-file d-e2 contents)))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lofat-place-file lofat-place-file-helper
                       lofat-regular-file-p
                       lofat-directory-file-p
                       lofat-file-p lofat-file->contents
                       m1-file-hifat-file-alist-fix m1-file)
     (m1-file-hifat-file-alist-fix-normalisation
      abs-mkdir-correctness-lemma-36
      (:rewrite lofat-file-contents-fix-when-lofat-file-contents-p)
      (:rewrite d-e-cc-contents-of-lofat-place-file-coincident-lemma-4)
      (:rewrite fat32-filename-p-correctness-1)
      (:rewrite lofat-file-contents-p-when-stringp)
      (:linear nth-when-d-e-p)
      (:linear len-of-explode-when-m1-file-contents-p-1)
      (:rewrite lofat-file-fix-when-lofat-file-p)
      (:rewrite lofat-file-contents-p-when-d-e-listp)
      (:rewrite nth-of-nats=>chars)
      (:rewrite m1-file-contents-p-when-stringp)
      (:type-prescription hifat-bounded-file-alist-p)
      (:rewrite stringp-when-nonempty-stringp)))))
  :rule-classes
  ((:congruence
    :corollary
    (implies (true-equiv d-e1 d-e2)
             (equal (lofat-place-file fat32$c root-d-e
                                      path (lofat-file d-e1 contents))
                    (lofat-place-file fat32$c root-d-e
                                      path (lofat-file d-e2 contents)))))))

(defthm lofat-pwrite-refinement-lemma-27 (true-equiv (lofat-file->d-e x) t))

(defthm lofat-pwrite-refinement-lemma-28
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
            (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                              path
                              (m1-file d-e (lofat-file->contents file))))
    (mv-nth 1
            (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                              path file))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (lofat-to-hifat root-d-e-list hifat-place-file)
                    nil)
    :restrict ((not-intersectp-list-when-subsetp-1
                ((y (mv-nth 0
                            (d-e-cc fat32$c
                                    (pseudo-root-d-e fat32$c)))))))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (lofat-fs-p fat32$c)
          (fat32-filename-list-p path)
          (equal (mv-nth 1 (lofat-to-hifat fat32$c))
                 0)
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
              (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                                path
                                (m1-file d-e (lofat-file->contents file))))
      (mv-nth 1
              (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                path file)))))))

(defthm
  lofat-pwrite-refinement-lemma-29
  (implies
   (and
    (good-root-d-e-p (pseudo-root-d-e fat32$c)
                     fat32$c)
    (non-free-index-listp x (effective-fat fat32$c))
    (fat32-filename-list-p path)
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
    (not-intersectp-list
     x
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
       (max-entry-count fat32$c))))
    (lofat-file-p file)
    (or (stringp (lofat-file->contents file))
        (equal (lofat-file->contents file) nil))
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
     (max-entry-count fat32$c)))
   (not-intersectp-list
    x
    (mv-nth
     2
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
      (max-entry-count fat32$c)))))
  :hints
  (("goal" :in-theory (disable lofat-place-file-correctness-lemma-116)
    :use (:instance (:rewrite lofat-place-file-correctness-lemma-116)
                    (entry-limit (max-entry-count fat32$c))
                    (root-d-e (pseudo-root-d-e fat32$c))))))

(defthm
  lofat-pwrite-refinement-lemma-44
  (implies
   (and
    (integerp offset)
    (<= 0 offset)
    (lofat-regular-file-p
     (mv-nth
      0
      (lofat-find-file fat32$c
                       (mv-nth 0 (root-d-e-list fat32$c))
                       (file-table-element->fid
                        (cdr (assoc-equal (cdr (assoc-equal fd fd-table))
                                          file-table))))))
    (stringp buf)
    (< (+ offset (len (explode buf)))
       4294967296))
   (lofat-file-contents-p
    (implode
     (insert-text
      (explode
       (lofat-file->contents
        (mv-nth 0
                (lofat-find-file
                 fat32$c
                 (mv-nth 0 (root-d-e-list fat32$c))
                 (file-table-element->fid
                  (cdr (assoc-equal (cdr (assoc-equal fd fd-table))
                                    file-table)))))))
      offset buf))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-file-contents-p
                              len-of-insert-text))))

(defthm
  lofat-pwrite-refinement-lemma-45
  (implies
   (and
    (integerp offset)
    (<= 0 offset)
    (lofat-regular-file-p
     (mv-nth
      0
      (lofat-find-file fat32$c
                       (mv-nth 0 (root-d-e-list fat32$c))
                       (file-table-element->fid
                        (cdr (assoc-equal (cdr (assoc-equal fd fd-table))
                                          file-table))))))
    (stringp buf)
    (< (+ offset (len (explode buf)))
       4294967296))
   (<
    (len
     (insert-text
      (explode$inline
       (lofat-file->contents$inline
        (mv-nth 0
                (lofat-find-file
                 fat32$c
                 (mv-nth 0 (root-d-e-list fat32$c))
                 (file-table-element->fid$inline
                  (cdr (assoc-equal (cdr (assoc-equal fd fd-table))
                                    file-table)))))))
      offset buf))
    4294967296))
  :hints
  (("goal" :do-not-induct t
    :in-theory
    (e/d (lofat-pwrite lofat-mkdir-refinement-lemma-12
                       len-of-insert-text)
         ((:rewrite d-e-cc-of-update-dir-contents-coincident)
          (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident)
          lofat-place-file
          lofat-mkdir-refinement-lemma-15))
    :expand ((:free (fs) (hifat-find-file fs nil))
             (:free (fs file)
                    (hifat-place-file fs nil file))
             (:free (fat32$c file root-d-e)
                    (lofat-place-file fat32$c root-d-e nil file)))))
  :rule-classes :linear)

(defthm
  lofat-pwrite-refinement-lemma-48
  (implies
   (and
    (<= 0 offset)
    (lofat-regular-file-p
     (mv-nth
      0
      (lofat-find-file fat32$c
                       (mv-nth 0 (root-d-e-list fat32$c))
                       path)))
    (not (stringp buf))
    (< (+ offset (len buf)) 4294967296))
   (m1-file-contents-p
    (implode$inline
     (insert-text
      (explode$inline
       (lofat-file->contents$inline
        (mv-nth 0
                (lofat-find-file
                 fat32$c
                 (mv-nth 0 (root-d-e-list fat32$c))
                 path))))
      offset buf))))
  :hints
  (("goal" :do-not-induct t
    :in-theory
    (enable m1-file-contents-p insert-text))))

(defthm
  lofat-pwrite-refinement-lemma-49
  (implies
   (and (integerp offset)
        (<= 0 offset)
        (lofat-regular-file-p
         (mv-nth 0
                 (lofat-find-file fat32$c
                                  (mv-nth 0 (root-d-e-list fat32$c))
                                  path)))
        (not (stringp buf))
        (< (+ offset (len buf)) 4294967296))
   (lofat-file-contents-p
    (implode
     (insert-text
      (explode
       (lofat-file->contents
        (mv-nth 0
                (lofat-find-file fat32$c
                                 (mv-nth 0 (root-d-e-list fat32$c))
                                 path))))
      offset buf))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-file-contents-p insert-text))))

(defthm
  lofat-pwrite-refinement-lemma-50
  (implies
   (and (integerp offset)
        (<= 0 offset)
        (lofat-regular-file-p
         (mv-nth 0
                 (lofat-find-file fat32$c
                                  (mv-nth 0 (root-d-e-list fat32$c))
                                  path)))
        (not (stringp buf))
        (< (+ offset (len buf)) 4294967296))
   (<
    (len
     (insert-text
      (explode$inline
       (lofat-file->contents$inline
        (mv-nth 0
                (lofat-find-file fat32$c
                                 (mv-nth 0 (root-d-e-list fat32$c))
                                 path))))
      offset buf))
    4294967296))
  :hints (("goal" :do-not-induct t
           :in-theory (enable insert-text)))
  :rule-classes :linear)

(defthm
  lofat-pwrite-refinement
  (implies
   (and
    ;; This needs to go.
    (natp offset)
    (lofat-fs-p fat32$c)
    (equal (mv-nth 1 (lofat-to-hifat fat32$c))
           0)
    ;; Let's discuss this hypothesis.
    ;;
    ;; This is something that we actually should
    ;; be able to derive from the structure of lofat-to-hifat-helper. That is,
    ;; we should be able to say that if we're able to do lofat-to-hifat-helper
    ;; with the max-entry-count parameter after the lofat-place-file operation,
    ;; then obviously we must have the capacity for that number of entries. And
    ;; if we don't have the capacity for that number of entries, then we must
    ;; be contradicting the hypothesis about the error code of lofat-place-file
    ;; being other than EIO. That is, this hypothesis should be implied by
    ;; that one, because in the case where that one holds, we must have gotten
    ;; away without an error while creating the new entry, and that means we
    ;; couldn't have exceeded the max entry count!
    ;;
    ;; That kind of reasoning, however, is exactly the kind of thing we gave up
    ;; on a while earlier. Now is not a great time to start either.
    (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
       (max-entry-count fat32$c))
    (not (equal (mv-nth 2 (lofat-pwrite fd buf offset fat32$c fd-table file-table)) *enospc*)))
   (and (equal (mv-nth 1
                       (lofat-to-hifat (mv-nth 0 (lofat-pwrite fd buf offset fat32$c fd-table file-table))))
               0)
        (hifat-equiv
         (mv-nth 0
                 (lofat-to-hifat (mv-nth 0 (lofat-pwrite fd buf offset fat32$c fd-table file-table))))
         (mv-nth 0
                 (hifat-pwrite fd buf offset (mv-nth 0 (lofat-to-hifat fat32$c)) fd-table file-table)))
        (equal (mv-nth 1 (lofat-pwrite fd buf offset fat32$c fd-table file-table))
               (mv-nth 1
                       (hifat-pwrite fd buf offset (mv-nth 0 (lofat-to-hifat fat32$c)) fd-table file-table)))
        (equal (mv-nth 2 (lofat-pwrite fd buf offset fat32$c fd-table file-table))
               (mv-nth 2
                       (hifat-pwrite fd buf offset (mv-nth 0 (lofat-to-hifat fat32$c)) fd-table file-table)))))
  :hints
  (("goal" :do-not-induct t
    :in-theory
    (e/d (lofat-pwrite
          lofat-mkdir-refinement-lemma-12)
         ((:rewrite d-e-cc-of-update-dir-contents-coincident)
          (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident)
          lofat-place-file
          lofat-mkdir-refinement-lemma-15))
    :expand ((:free (fs) (hifat-find-file fs nil))
             (:free (fs file)
                    (hifat-place-file fs nil file))
             (:free (fat32$c file root-d-e)
                    (lofat-place-file fat32$c root-d-e nil file)))))
  :otf-flg t)

;; How do we prove this? The best way seems to be to open up the definitions of
;; the single-step functions and proceed from there.
(defthm absfat-oracle-single-step-refinement
  (implies
   (and
    (lofat-fs-p fat32$c)
    (equal (mv-nth '1 (lofat-to-hifat fat32$c)) '0)
    (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
       (max-entry-count fat32$c))
    (not (equal (lofat-st->errno
                 (mv-nth 1
                         (lofat-oracle-single-step fat32$c syscall-sym
                                                   st)))
                *enospc*))
    (frame-reps-fs
     frame
     (mv-nth 0
             (lofat-to-hifat fat32$c))))
   (frame-reps-fs
    (mv-nth 0 (absfat-oracle-single-step frame syscall-sym st))
    (mv-nth 0
            (lofat-to-hifat (mv-nth 0 (lofat-oracle-single-step fat32$c syscall-sym
                                                                st))))))
  :hints (("Goal" :do-not-induct t
           :in-theory
           (e/d (absfat-oracle-single-step
                 lofat-oracle-single-step)
                (hifat-mkdir
                 hifat-pwrite))))
  :otf-flg t)
