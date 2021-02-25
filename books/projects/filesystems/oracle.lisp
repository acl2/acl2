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

;; This is just a cool lemma to have.
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

;; This, again, seems like a useful lemma to keep around.
(defthm lofat-pwrite-refinement-lemma-28
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
                              path file))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (lofat-to-hifat root-d-e-list hifat-place-file)
                    nil)
    :restrict ((not-intersectp-list-when-subsetp-1
                ((y (mv-nth 0
                            (d-e-cc fat32$c
                                    (pseudo-root-d-e fat32$c)))))))
    :cases ((consp path)))))

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
