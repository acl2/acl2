(in-package "ACL2")

;  oracle.lisp                                         Mihir Mehta

(include-book "lofat-syscalls")
(include-book "abs-syscalls")

(local (in-theory (disable nth make-list-ac-removal last
                           make-list-ac
                           (:definition true-listp)
                           (:rewrite true-listp-when-string-list)
                           (:definition string-listp)
                           (:rewrite
                            fat32-filename-list-p-of-cdr-when-fat32-filename-list-p)
                           (:rewrite
                            string-listp-when-fat32-filename-list-p)
                           (:rewrite true-listp-when-abs-file-alist-p)
                           (:rewrite true-list-fix-when-true-listp)
                           (:rewrite abs-fs-p-correctness-1)
                           (:rewrite abs-fs-p-when-hifat-no-dups-p)
                           (:rewrite
                            m1-file-alist-p-of-cdr-when-m1-file-alist-p)
                           (:rewrite fat32-filename-p-correctness-1)
                           (:definition member-equal)
                           (:rewrite list-fix-when-not-consp)
                           (:definition acl2-number-listp)
                           (:definition rational-listp)
                           (:rewrite
                            acl2-numberp-of-car-when-acl2-number-listp)
                           (:rewrite
                            integer-listp-of-cdr-when-integer-listp)
                           (:rewrite update-nth-of-update-nth-1)
                           (:rewrite
                            nat-listp-if-fat32-masked-entry-list-p)
                           (:rewrite
                            rational-listp-of-cdr-when-rational-listp)
                           (:rewrite nat-listp-of-cdr-when-nat-listp)
                           (:rewrite no-duplicatesp-of-member)
                           (:rewrite
                            rationalp-of-car-when-rational-listp)
                           (:rewrite
                            fat32-masked-entry-list-p-of-cdr-when-fat32-masked-entry-list-p)
                           (:rewrite len-update-nth)
                           (:rewrite integerp-of-car-when-integer-listp)
                           (:rewrite
                            acl2-number-listp-of-cdr-when-acl2-number-listp)
                           (:rewrite
                            fat32-masked-entry-list-p-when-not-consp))))

;; Move later.
(defund
  abs-close (fd fd-table file-table)
  (declare (xargs :guard (and (fd-table-p fd-table)
                              (file-table-p file-table))))
  (hifat-close fd fd-table file-table))

(defund
  abs-pwrit1
  (fd buf offset frame fd-table file-table)
  (declare
   (xargs
    :guard (and (frame-p frame)
                (fd-table-p fd-table)
                (file-table-p file-table)
                (natp fd)
                (stringp buf)
                (natp offset)
                (consp (assoc-equal 0 frame)))
    :guard-hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d
       (len-of-insert-text abs-no-dups-file-p abs-no-dups-p abs-pwrite)
       (unsigned-byte-p))
      :expand
      (:with
       m1-file-contents-fix-when-m1-file-contents-p
       (:free
        (oldtext)
        (m1-file-contents-fix
         (implode (insert-text oldtext offset buf)))))))))
  (b*
      ((fd-table-entry (assoc-equal fd fd-table))
       ((unless (consp fd-table-entry))
        (mv frame -1 *ebadf*))
       (file-table-entry (assoc-equal (cdr fd-table-entry)
                                      file-table))
       ((unless (consp file-table-entry))
        (mv frame -1 *ebadf*))
       ((unless (unsigned-byte-p 32 (+ offset (length buf))))
        (mv frame -1 *enospc*))
       (path (file-table-element->fid (cdr file-table-entry)))
       ((unless (consp path))
        (mv frame -1 *enoent*))
       (dirname (dirname path))
       ((mv frame retval errno)
        (abs-pwrite
         fd buf offset frame fd-table file-table))
       (frame (partial-collapse frame dirname)))
    (mv frame retval errno)))

(skip-proofs
 (defthm
   good-frame-p-of-abs-pwrite
   (implies
    (good-frame-p frame)
    (good-frame-p
     (mv-nth
      0
      (abs-pwrite fd
                  buf offset frame fd-table file-table))))
   :hints
   (("goal" :do-not-induct t
     :in-theory (enable abs-pwrite good-frame-p)))))

(defthm
  abs-pwrit1-correctness-1
  (implies
   (good-frame-p frame)
   (and (collapse-equiv
         (mv-nth 0
                 (abs-pwrit1 fd
                             buf offset frame fd-table file-table))
         (mv-nth 0
                 (abs-pwrite fd
                             buf offset frame fd-table file-table)))
        (equal (mv-nth 1
                       (abs-pwrit1 fd
                                   buf offset frame fd-table file-table))
               (mv-nth 1
                       (abs-pwrite fd
                                   buf offset frame fd-table file-table)))
        (equal (mv-nth 2
                       (abs-pwrit1 fd
                                   buf offset frame fd-table file-table))
               (mv-nth 2
                       (abs-pwrite fd buf
                                   offset frame fd-table file-table)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (abs-pwrit1 hifat-find-file hifat-place-file)
                    ((:rewrite-quoted-constant true-fix-under-true-equiv))))
   (if (not stable-under-simplificationp)
       nil
       '(:in-theory
         (e/d (abs-pwrite abs-pwrit1
                          hifat-find-file hifat-place-file)
              ((:rewrite-quoted-constant true-fix-under-true-equiv))))))
  :otf-flg t)

(defthm good-frame-p-of-partial-collapse
  (implies (good-frame-p frame)
           (good-frame-p (partial-collapse frame pathname)))
  :hints (("goal" :in-theory (enable good-frame-p)
           :do-not-induct t)))

(defthm
  good-frame-p-of-abs-pwrit1
  (implies
   (good-frame-p frame)
   (good-frame-p
    (mv-nth
     0
     (abs-pwrit1 fd
                 buf offset frame fd-table file-table))))
  :hints
  (("goal" :do-not-induct t
    :in-theory (enable abs-pwrit1)
    :use good-frame-p-of-abs-pwrite)))

(fty::defprod fat-st
              ((fd natp :default 0)
               (buf stringp :default "")
               (offset natp :default 0)
               (count natp :default 0)
               (retval integerp :default 0)
               (errno natp :default 0)
               (path fat32-filename-list-p :default nil)
               (stat struct-stat-p :default (make-struct-stat))
               (statfs struct-statfs-p :default (make-struct-statfs))
               (dirp integerp :default 0)
               ;; This is interesting. We try to mimic the NULL-returning
               ;; behaviour of the actual opendir by making it return -1 at
               ;; precisely those times. That means this cannot be assumed to
               ;; be a natural number.
               (fd-table fd-table-p :default nil)
               (file-table file-table-p :default nil)
               (dir-stream-table dir-stream-table-p :default nil)
               (oracle nat-list :default nil)))

;; We aren't going to put statfs in this. It'll just make things pointlessly
;; complicated.
(defund lofat-oracle-single-step (fat32$c syscall-sym st)
  (declare (xargs :stobjs fat32$c
                  :guard (and (lofat-fs-p fat32$c)
                              (fat-st-p st))
                  :verify-guards nil))
  (b*
      ((st (mbe :logic (fat-st-fix st) :exec st))
       ((when (eq syscall-sym :pwrite))
        (b*
            (((mv fat32$c retval errno)
              (lofat-pwrite
               (fat-st->fd st)
               (fat-st->buf st)
               (fat-st->offset st)
               fat32$c
               (fat-st->fd-table st)
               (fat-st->file-table st))))
          (mv fat32$c
              (change-fat-st
               st :retval retval :errno errno))))
       ((when (eq syscall-sym :pread))
        (b*
            (((mv buf retval errno)
              (lofat-pread
               (fat-st->fd st)
               (fat-st->count st)
               (fat-st->offset st)
               fat32$c
               (fat-st->fd-table st)
               (fat-st->file-table st))))
          (mv fat32$c
              (change-fat-st
               st :buf buf :retval retval :errno errno))))
       ((when (eq syscall-sym :open))
        (b*
            (((mv fd-table file-table fd retval)
              (lofat-open
               (fat-st->path st)
               (fat-st->fd-table st)
               (fat-st->file-table st))))
          (mv fat32$c
              (change-fat-st
               st :fd fd :retval retval :errno 0 :file-table file-table
               :fd-table fd-table))))
       ((when (eq syscall-sym :lstat))
        (b*
            (((mv stat retval errno)
              (lofat-lstat
               fat32$c
               (fat-st->path st))))
          (mv fat32$c
              (change-fat-st
               st :stat stat :retval retval :errno errno))))
       ;; ((when (eq syscall-sym :unlink))
       ;;  (b*
       ;;      (((mv fat32$c retval errno)
       ;;        (lofat-unlink
       ;;         fat32$c
       ;;         (fat-st->path st))))
       ;;    (mv fat32$c
       ;;        (change-fat-st
       ;;         st :retval retval :errno errno))))
       ;; ((when (eq syscall-sym :truncate))
       ;;  (b*
       ;;      (((mv fat32$c retval errno)
       ;;        (lofat-unlink
       ;;         fat32$c
       ;;         (fat-st->path st))))
       ;;    (mv fat32$c
       ;;        (change-fat-st
       ;;         st :retval retval :errno errno))))
       ((when (eq syscall-sym :mkdir))
        (b*
            (((mv fat32$c retval errno)
              (lofat-mkdir
               fat32$c
               (fat-st->path st))))
          (mv fat32$c
              (change-fat-st
               st :retval retval :errno errno))))
       ((when (eq syscall-sym :opendir))
        (b*
            (((mv dir-stream-table dirp retval)
              (lofat-opendir
               fat32$c
               (fat-st->dir-stream-table st)
               (fat-st->path st))))
          (mv fat32$c
              (change-fat-st
               st :dir-stream-table dir-stream-table :dirp dirp
               :retval retval :errno 0))))
       ((when (eq syscall-sym :close))
        (b*
            (((mv fd-table file-table errno)
              (lofat-close
               (fat-st->fd st)
               (fat-st->fd-table st)
               (fat-st->file-table st))))
          (mv fat32$c
              (change-fat-st
               st :fd-table fd-table :file-table file-table :errno errno))))
       ((when (and (consp syscall-sym) (eq (car syscall-sym) :set-path)))
        (mv fat32$c
            (change-fat-st st :path (cdr syscall-sym))))
       ((when (and (consp syscall-sym) (eq (car syscall-sym) :set-count)))
        (mv fat32$c
            (change-fat-st st :count (cdr syscall-sym)))))
    (mv fat32$c st)))

;; We aren't going to put statfs in this. It'll just make things pointlessly
;; complicated.
(defund absfat-oracle-single-step (frame syscall-sym st)
  (declare (xargs :guard (and (frame-p frame)
                              (fat-st-p st)
                              (consp (assoc-equal 0 frame))
                              (no-duplicatesp-equal (strip-cars frame)))
                  :verify-guards nil))
  (b*
      ((st (mbe :logic (fat-st-fix st) :exec st))
       ((when (eq syscall-sym :pwrite))
        (b*
            (((mv frame retval errno)
              (abs-pwrit1
               (fat-st->fd st)
               (fat-st->buf st)
               (fat-st->offset st)
               frame
               (fat-st->fd-table st)
               (fat-st->file-table st))))
          (mv frame
              (change-fat-st
               st :retval retval :errno errno))))
       ((when (eq syscall-sym :pread))
        (b*
            (((mv buf retval errno)
              (abs-pread
               (fat-st->fd st)
               (fat-st->count st)
               (fat-st->offset st)
               frame
               (fat-st->fd-table st)
               (fat-st->file-table st))))
          (mv frame
              (change-fat-st
               st :buf buf :retval retval :errno errno))))
       ((when (eq syscall-sym :open))
        (b*
            (((mv fd-table file-table fd retval)
              (abs-open
               (fat-st->path st)
               (fat-st->fd-table st)
               (fat-st->file-table st))))
          (mv frame
              (change-fat-st
               st :fd fd :retval retval :errno 0 :file-table file-table
               :fd-table fd-table))))
       ((when (eq syscall-sym :lstat))
        (b*
            (((mv stat retval errno)
              (abs-lstat
               frame
               (fat-st->path st))))
          (mv frame
              (change-fat-st
               st :stat stat :retval retval :errno errno))))
       ;; ((when (eq syscall-sym :unlink))
       ;;  (b*
       ;;      (((mv fat32$c retval errno)
       ;;        (lofat-unlink
       ;;         fat32$c
       ;;         (fat-st->path st))))
       ;;    (mv fat32$c
       ;;        (change-fat-st
       ;;         st :retval retval :errno errno))))
       ;; ((when (eq syscall-sym :truncate))
       ;;  (b*
       ;;      (((mv fat32$c retval errno)
       ;;        (lofat-unlink
       ;;         fat32$c
       ;;         (fat-st->path st))))
       ;;    (mv fat32$c
       ;;        (change-fat-st
       ;;         st :retval retval :errno errno))))
       ((when (eq syscall-sym :mkdir))
        (b*
            (((mv frame retval errno)
              (abs-mkdir
               frame
               (fat-st->path st))))
          (mv frame
              (change-fat-st
               st :retval retval :errno errno))))
       ;; This is an interesting case! Basically, this command does not modify
       ;; the state of the filesystem but does change the frame.
       ((when (eq syscall-sym :opendir))
        (b*
            (((mv dirp dir-stream-table retval frame)
              (abs-opendir
               frame
               (fat-st->path st)
               (fat-st->dir-stream-table st))))
          (mv frame
              (change-fat-st
               st :dir-stream-table dir-stream-table :dirp dirp
               :retval retval :errno 0))))
       ((when (eq syscall-sym :close))
        (b*
            (((mv fd-table file-table errno)
              (abs-close
               (fat-st->fd st)
               (fat-st->fd-table st)
               (fat-st->file-table st))))
          (mv frame
              (change-fat-st
               st :fd-table fd-table :file-table file-table :errno errno))))
       ((when (and (consp syscall-sym) (eq (car syscall-sym) :set-path)))
        (mv frame
            (change-fat-st st :path (cdr syscall-sym))))
       ((when (and (consp syscall-sym) (eq (car syscall-sym) :set-count)))
        (mv frame
            (change-fat-st st :count (cdr syscall-sym)))))
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
   (frame-reps-fs (mv-nth 0 (abs-mkdir frame (fat-st->path st)))
                  (mv-nth 0
                          (hifat-mkdir (mv-nth 0 (lofat-to-hifat fat32$c))
                                       (fat-st->path st)))))
  :hints (("goal" :do-not-induct t
           :in-theory (disable abs-mkdir-correctness-2 hifat-mkdir)
           :use (:instance abs-mkdir-correctness-2
                           (path (fat-st->path st))))))

(defthm
  absfat-oracle-single-step-refinement-lemma-2
  (implies
   (frame-reps-fs frame
                  (mv-nth 0 (lofat-to-hifat fat32$c)))
   (frame-reps-fs (mv-nth 0
                          (abs-pwrite (fat-st->fd st)
                                      (fat-st->buf st)
                                      (fat-st->offset st)
                                      frame
                                      (fat-st->fd-table st)
                                      (fat-st->file-table st)))
                  (mv-nth 0
                          (hifat-pwrite (fat-st->fd st)
                                        (fat-st->buf st)
                                        (fat-st->offset st)
                                        (mv-nth 0 (lofat-to-hifat fat32$c))
                                        (fat-st->fd-table st)
                                        (fat-st->file-table st)))))
  :hints (("goal" :do-not-induct t
           :in-theory (disable abs-pwrite-correctness-1 hifat-pwrite)
           :use (:instance abs-pwrite-correctness-1
                           (fd (fat-st->fd st))
                           (buf (fat-st->buf st))
                           (offset (fat-st->offset st))
                           (fd-table (fat-st->fd-table st))
                           (file-table (fat-st->file-table st))))))

;; I have this single-step property relating two representations of
;; my FAT32 filesystem, AbsFAT and LoFAT. The very next thing I want to do are
;; derive from this a multi-step property for when multiple steps are executed,
;; which is a refinement relation. Towards that end, I will need to define an
;; interpreter which processes a sequence of system calls, and induct on the
;; length of that sequence to apply this single-step property to the induction
;; case.
;;
;; My problem, however, is that this single-step property has too many
;; hypotheses. Currently, there are four hypotheses, and as you can see,
;; hypotheses 1 and 2 are invariants. However, hypotheses 3 and 4 are not,
;; because they ensure that
;; we are not facing certain kinds of running-out-of-space errors in
;; LoFAT. There is not really an equivalent concept of "running out of space"
;; in AbsFAT, because it is a more abstract model and does not get into the
;; byte level as much as LoFAT does. That means there isn't a way to ensure
;; the same kind of running-out-of-space behaviour in AbsFAT, which would allow
;; us to make these hypotheses invariants - there is simply no way in AbsFAT to
;; draw out this information about how much space is available.
;;
;; This seems to present two ways to proceed:
;;
;; - Make a predicate which takes as arguments the current state of LoFAT
;; (i.e. the stobj fat32$c and the auxiliary state st) and the list of
;; instructions, and returns true or false depending on whether hypotheses 3
;; and 4 are preserved as invariants throughout the execution. Use this as a
;; hypothesis for the multi-step relation so that the induction hypothesis
;; becomes strong enough to allow this single-step relation to be used. This
;; seems clunky because I expect to spend a lot of time messing around with
;; this new predicate holds in subgoals when I'm using this multi-step relation
;; for code proofs.
;;
;; - Make some kind of intermediate model between LoFAT and AbsFAT, which does
;; take space issues into account. This, too, seems clunky because AbsFAT is
;; designed to simplify reasoning about sequences of instructions and I will
;; potentially give up some of that if I have to reason about a new model.
;;
;; So, coming to the main questions: is there a third option which is better?
;; Should I just pick one of these two and go with it until I actually start
;; doing a code proof and run into difficulties? Or is one of these two
;; obviously better, despite me not being able to see it yet? It's worth noting
;; that I also want to reason about instructions being executed concurrently,
;; i.e. not necessarily in parallel in the plet sense, but definitely in the
;; sense of single-core concurrency where multiple threads of instructions each
;; get their turn in an arbitrary order to execute one instruction at a
;; time. I expect this to exacerbate any bad decisions I make now, which is why
;; I'm hoping to get this right before I go too far.
;;
;; Having written this question down and received advice from Dr Moore, Dr
;; Swords and an acknowledgement from Dr Ray, I ultimately chose to make the
;; predicate. Let's see how it pans out.
(defthm
  absfat-oracle-single-step-refinement
  (implies
   (and
    ;; Hypothesis 1
    (lofat-fs-p fat32$c)
    ;; Hypothesis 2
    (equal (mv-nth '1 (lofat-to-hifat fat32$c))
           '0)
    ;; Hypothesis 3
    (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
       (max-entry-count fat32$c))
    ;; Hypothesis 4
    (not
     (equal (fat-st->errno
             (mv-nth 1
                     (lofat-oracle-single-step fat32$c syscall-sym st)))
            *enospc*))
    ;; Predicate relating AbsFAT and LoFAT.
    (frame-reps-fs frame
                   (mv-nth 0 (lofat-to-hifat fat32$c))))
   (and
    ;; Hypothesis 1
    (lofat-fs-p (mv-nth 0
                        (lofat-oracle-single-step fat32$c syscall-sym st)))
    ;; Hypothesis 2
    (equal
     (mv-nth '1
             (lofat-to-hifat
              (mv-nth 0
                      (lofat-oracle-single-step fat32$c syscall-sym st))))
     '0)
    ;; Predicate relating AbsFAT and LoFAT.
    (frame-reps-fs
     (mv-nth 0
             (absfat-oracle-single-step frame syscall-sym st))
     (mv-nth
      0
      (lofat-to-hifat
       (mv-nth 0
               (lofat-oracle-single-step fat32$c syscall-sym st)))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (absfat-oracle-single-step lofat-oracle-single-step)
                    (hifat-mkdir hifat-pwrite)))))

(defthmd abs-open-correctness-2
  (equal (lofat-open path fd-table file-table)
         (abs-open path fd-table file-table))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-open abs-open))))

(defthm abs-close-correctness-1
  (and (fd-table-p (mv-nth 0 (abs-close fd fd-table file-table)))
       (file-table-p (mv-nth 1 (abs-close fd fd-table file-table))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable abs-close hifat-close))))

(defthmd abs-close-correctness-2
  (equal (lofat-close fd fd-table file-table)
         (abs-close fd fd-table file-table))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-close abs-close))))

(defthmd
  absfat-oracle-multi-step-refinement-lemma-2
  (implies
   (and
    (lofat-fs-p fat32$c)
    (equal (mv-nth '1 (lofat-to-hifat fat32$c))
           '0)
    (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
       (max-entry-count fat32$c))
    (not
     (equal (fat-st->errno
             (mv-nth 1
                     (lofat-oracle-single-step fat32$c syscall-sym st)))
            *enospc*))
    (frame-reps-fs frame
                   (mv-nth 0 (lofat-to-hifat fat32$c))))
   (equal (mv-nth 1
                  (absfat-oracle-single-step frame syscall-sym st))
          (mv-nth 1
                  (lofat-oracle-single-step fat32$c syscall-sym st))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (absfat-oracle-single-step lofat-oracle-single-step
                                               abs-open-correctness-2
                                               abs-opendir-correctness-2
                                               lofat-opendir-correctness-2
                                               lofat-opendir-correctness-3
                                               abs-close-correctness-2)
                    (hifat-mkdir hifat-pwrite)))))

(defund lofat-oracle-multi-step (fat32$c syscall-sym-list st)
  (declare (xargs :stobjs fat32$c
                  :guard (and (lofat-fs-p fat32$c)
                              (fat-st-p st))
                  :verify-guards nil))
  (b*
      (((when (atom syscall-sym-list)) (mv fat32$c st))
       ((mv fat32$c st) (lofat-oracle-single-step fat32$c (car syscall-sym-list) st)))
    (lofat-oracle-multi-step fat32$c (cdr syscall-sym-list) st)))

(defthmd
  lofat-oracle-multi-step-of-true-list-fix
  (equal (lofat-oracle-multi-step fat32$c (true-list-fix syscall-sym-list)
                                  st)
         (lofat-oracle-multi-step fat32$c syscall-sym-list st))
  :hints (("goal" :in-theory (enable lofat-oracle-multi-step
                                     true-list-fix))))

(defcong
  list-equiv equal
  (lofat-oracle-multi-step fat32$c syscall-sym-list st)
  2
  :hints
  (("goal"
    :use
    (lofat-oracle-multi-step-of-true-list-fix
     (:instance lofat-oracle-multi-step-of-true-list-fix
                (syscall-sym-list syscall-sym-list-equiv))))))

(defund absfat-oracle-multi-step (frame syscall-sym-list st)
  (declare (xargs :guard (and (frame-p frame)
                              (fat-st-p st)
                              (consp (assoc-equal 0 frame))
                              (no-duplicatesp-equal (strip-cars frame)))
                  :guard-debug t
                  :verify-guards nil))
  (b*
      (((when (atom syscall-sym-list)) (mv frame st))
       ((mv frame st) (absfat-oracle-single-step frame (car syscall-sym-list) st)))
    (absfat-oracle-multi-step frame (cdr syscall-sym-list) st)))

(defthmd
  absfat-oracle-multi-step-of-true-list-fix
  (equal (absfat-oracle-multi-step frame (true-list-fix syscall-sym-list)
                                   st)
         (absfat-oracle-multi-step frame syscall-sym-list st))
  :hints (("goal" :in-theory (enable absfat-oracle-multi-step
                                     true-list-fix))))

(defcong
  list-equiv equal
  (absfat-oracle-multi-step frame syscall-sym-list st)
  2
  :hints
  (("goal"
    :use
    (absfat-oracle-multi-step-of-true-list-fix
     (:instance absfat-oracle-multi-step-of-true-list-fix
                (syscall-sym-list syscall-sym-list-equiv))))))

(defund good-lofat-oracle-steps-p-helper (fat32$c syscall-sym-list st)
  (declare (xargs :stobjs fat32$c
                  :guard (and (lofat-fs-p fat32$c)
                              (fat-st-p st))
                  :verify-guards nil
                  :measure (len syscall-sym-list)))
  (b*
      (((when (atom syscall-sym-list)) (mv t fat32$c))
       ((mv fs &) (lofat-to-hifat fat32$c))
       ((unless
            (< (hifat-entry-count fs)
               (max-entry-count fat32$c)))
        (mv nil fat32$c))
       ((mv fat32$c st)
        (lofat-oracle-single-step fat32$c (car syscall-sym-list)
                                  st))
       ((when
            (equal (fat-st->errno
                    st)
                   *enospc*))
        (mv nil fat32$c)))
    (good-lofat-oracle-steps-p-helper fat32$c (cdr syscall-sym-list) st)))

(defthmd
  good-lofat-oracle-steps-p-helper-of-true-list-fix
  (equal
   (good-lofat-oracle-steps-p-helper fat32$c (true-list-fix syscall-sym-list)
                                     st)
   (good-lofat-oracle-steps-p-helper fat32$c syscall-sym-list st))
  :hints (("goal" :in-theory (enable good-lofat-oracle-steps-p-helper
                                     true-list-fix))))

(defcong
  list-equiv equal
  (good-lofat-oracle-steps-p-helper fat32$c syscall-sym-list st)
  2
  :hints
  (("goal"
    :do-not-induct t
    :use
    (good-lofat-oracle-steps-p-helper-of-true-list-fix
     (:instance
      good-lofat-oracle-steps-p-helper-of-true-list-fix
      (syscall-sym-list syscall-sym-list-equiv))))))

(defthm
  lofat-oracle-multi-step-of-append
  (equal
   (lofat-oracle-multi-step fat32$c (append x y)
                            st)
   (lofat-oracle-multi-step (mv-nth 0
                                    (lofat-oracle-multi-step fat32$c x st))
                            y
                            (mv-nth 1
                                    (lofat-oracle-multi-step fat32$c x st))))
  :hints (("goal" :in-theory (enable lofat-oracle-multi-step append))))

(defthm
  good-lofat-oracle-steps-p-helper-of-append
  (equal (mv-nth 0
                 (good-lofat-oracle-steps-p-helper fat32$c (append x y)
                                                   st))
         (and (mv-nth 0
                      (good-lofat-oracle-steps-p-helper fat32$c x st))
              (mv-nth 0
                      (good-lofat-oracle-steps-p-helper
                       (mv-nth 0
                               (lofat-oracle-multi-step fat32$c x st))
                       y
                       (mv-nth 1
                               (lofat-oracle-multi-step fat32$c x st))))))
  :hints (("goal" :in-theory (enable good-lofat-oracle-steps-p-helper
                                     lofat-oracle-multi-step append))))

(defthm
  absfat-oracle-multi-step-of-append
  (equal
   (absfat-oracle-multi-step frame (append x y)
                             st)
   (absfat-oracle-multi-step (mv-nth 0
                                     (absfat-oracle-multi-step frame x st))
                             y
                             (mv-nth 1
                                     (absfat-oracle-multi-step frame x st))))
  :hints (("goal" :in-theory (enable absfat-oracle-multi-step append))))

(encapsulate
  ()

  (local
   (defun-nx
     induction-scheme (fat32$c frame st syscall-sym-list)
     (declare (xargs :stobjs fat32$c
                     :verify-guards nil
                     :measure (len syscall-sym-list)))
     (cond
      ((and
        (not (atom syscall-sym-list))
        (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
           (max-entry-count fat32$c))
        (not
         (equal
          (fat-st->errno
           (mv-nth 1
                   (lofat-oracle-single-step fat32$c (car syscall-sym-list)
                                             st)))
          28)))
       (induction-scheme
        (mv-nth 0
                (lofat-oracle-single-step fat32$c (car syscall-sym-list)
                                          st))
        (mv-nth 0
                (absfat-oracle-single-step frame (car syscall-sym-list)
                                           st))
        (mv-nth 1
                (lofat-oracle-single-step fat32$c (car syscall-sym-list)
                                          st))
        (cdr syscall-sym-list)))
      (t
       (mv fat32$c frame st syscall-sym-list)))))

  (local (include-book "std/basic/inductions" :dir :system))

  ;; This is made local because it is ultimately implied by
  ;; absfat-oracle-multi-step-refinement-1 and
  ;; absfat-oracle-multi-step-refinement-2.
  (local
   (defthmd
     lemma
     (implies
      (and
       (lofat-fs-p fat32$c)
       (equal (mv-nth '1 (lofat-to-hifat fat32$c))
              '0)
       (mv-nth
        0
        (good-lofat-oracle-steps-p-helper fat32$c (take n syscall-sym-list)
                                          st))
       (frame-reps-fs frame
                      (mv-nth 0 (lofat-to-hifat fat32$c))))
      (and
       (lofat-fs-p
        (mv-nth 0
                (lofat-oracle-multi-step fat32$c (take n syscall-sym-list)
                                         st)))
       (equal
        (mv-nth
         '1
         (lofat-to-hifat
          (mv-nth 0
                  (lofat-oracle-multi-step fat32$c (take n syscall-sym-list)
                                           st))))
        '0)
       (frame-reps-fs
        (mv-nth 0
                (absfat-oracle-multi-step frame (take n syscall-sym-list)
                                          st))
        (mv-nth
         0
         (lofat-to-hifat
          (mv-nth 0
                  (lofat-oracle-multi-step fat32$c (take n syscall-sym-list)
                                           st)))))
       (equal (mv-nth 1
                      (absfat-oracle-multi-step frame (take n syscall-sym-list)
                                                st))
              (mv-nth 1
                      (lofat-oracle-multi-step fat32$c (take n syscall-sym-list)
                                               st)))))
     :hints
     (("goal"
       :in-theory
       (e/d
        (absfat-oracle-multi-step lofat-oracle-multi-step
                                  good-lofat-oracle-steps-p-helper
                                  absfat-oracle-multi-step-refinement-lemma-2)
        (hifat-mkdir hifat-pwrite
                     take append-of-take-and-cons))
       :induct (dec-induct n)
       :do-not-induct t
       :expand (:with take-as-append-and-nth
                      (take n syscall-sym-list))))))

  (defthm
    absfat-oracle-multi-step-refinement-1
    (implies
     (and
      (lofat-fs-p fat32$c)
      (equal (mv-nth 1 (lofat-to-hifat fat32$c))
             0)
      (mv-nth 0
              (good-lofat-oracle-steps-p-helper fat32$c syscall-sym-list st))
      (frame-reps-fs frame
                     (mv-nth 0 (lofat-to-hifat fat32$c))))
     (and
      (lofat-fs-p
       (mv-nth 0
               (lofat-oracle-multi-step fat32$c syscall-sym-list st)))
      (equal
       (mv-nth
        1
        (lofat-to-hifat
         (mv-nth 0
                 (lofat-oracle-multi-step fat32$c syscall-sym-list st))))
       0)
      (frame-reps-fs
       (mv-nth 0
               (absfat-oracle-multi-step frame syscall-sym-list st))
       (mv-nth
        0
        (lofat-to-hifat
         (mv-nth 0
                 (lofat-oracle-multi-step fat32$c syscall-sym-list st)))))))
    :hints (("goal" :use (:instance lemma
                                    (n (len syscall-sym-list))))))

  (defthmd
    absfat-oracle-multi-step-refinement-2
    (implies
     (and
      (lofat-fs-p fat32$c)
      (equal (mv-nth 1 (lofat-to-hifat fat32$c))
             0)
      (mv-nth 0
              (good-lofat-oracle-steps-p-helper fat32$c syscall-sym-list st))
      (frame-reps-fs frame
                     (mv-nth 0 (lofat-to-hifat fat32$c))))
     (equal (mv-nth 1
                    (absfat-oracle-multi-step frame syscall-sym-list st))
            (mv-nth 1
                    (lofat-oracle-multi-step fat32$c syscall-sym-list st))))
    :hints (("goal" :use (:instance lemma
                                    (n (len syscall-sym-list)))))))

(defconst *example-prog-1*
  (list (cons :set-path (path-to-fat32-path (coerce "/tmp/ticket1.txt" 'list)))
        :open
        :pwrite
        :close
        (cons :set-path (path-to-fat32-path (coerce "/tmp/ticket2.txt" 'list)))
        :open
        :pwrite
        :close))

#|
(absfat-oracle-multi-step
(frame-with-root (list (cons "TMP        " (make-m1-file :contents nil))) nil)
*example-prog-1*
(make-fat-st))
|#

(defund nonempty-queues (queues)
  (if (atom queues)
      nil
    (append
     (nonempty-queues (butlast queues 1))
     (if (consp (nth (- (len queues) 1) queues))
         (list (- (len queues) 1))
       nil))))

(defthm
  consp-of-nonempty-queues-1
  (implies (consp (flatten queues))
           (consp (nonempty-queues queues)))
  :hints
  (("goal" :in-theory (e/d (nonempty-queues flatten)
                           ((:rewrite flattenp-of-append)))
    :induct (nonempty-queues queues))
   ("subgoal *1/2" :use (:instance (:rewrite flattenp-of-append)
                                   (y (list (nth (+ -1 (len queues)) queues)))
                                   (x (take (+ -1 (len queues)) queues)))
    :expand (len queues)))
  :rule-classes :type-prescription)

;; Move later.
(encapsulate
  ()

  (local
   (defthm lemma
     (equal (len (flatten (update-nth key val nil)))
            (len val))
     :hints (("goal" :in-theory (enable update-nth nth flatten)))))

  (defthm len-of-flatten-of-update-nth
    (equal (len (flatten (update-nth key val l)))
           (- (+ (len (flatten l)) (len val))
              (len (nth key l))))
    :hints (("goal" :in-theory (enable update-nth nth flatten)))))

(assert-event
 (equal (nonempty-queues (list nil (list 3) (list 4 5) nil))
        (list 1 2)))

(defthm
  member-of-nonempty-queues
  (iff (member-equal (nfix x)
                     (nonempty-queues queues))
       (consp (nth x queues)))
  :hints (("goal" :in-theory (enable nonempty-queues nth)
           :induct (nonempty-queues queues)
           :expand ((:free (n) (nth n queues))
                    (len queues)
                    (:with nth-when->=-n-len-l
                           (nth (+ -1 x) (cdr queues))))))
  :rule-classes
  ((:rewrite :corollary (implies (member-equal (nfix x)
                                               (nonempty-queues queues))
                                 (consp (nth x queues))))
   (:rewrite :corollary (implies (not (member-equal (nfix x)
                                                    (nonempty-queues queues)))
                                 (not (consp (nth x queues)))))
   (:type-prescription
    :corollary (implies (not (member-equal (nfix x)
                                           (nonempty-queues queues)))
                        (not (consp (nth x queues)))))))

(defthm nat-listp-of-nonempty-queues
  (nat-listp (nonempty-queues queues))
  :hints (("goal" :in-theory (enable nonempty-queues))))

(defund
  schedule-queues (queues oracle)
  (declare
   (xargs
    :verify-guards nil
    :measure (len (flatten queues))
    :hints
    (("goal"
      :expand
      ((:with
        (:rewrite member-of-nonempty-queues . 1)
        (:free (n)
               (consp (nth (nth n (nonempty-queues queues))
                           queues))))
       (:with
        integerp-of-nth-when-integer-listp
        (:free
         (n)
         (integerp (nth n (nonempty-queues queues))))))))))
  (b*
      (((when (atom (flatten queues)))
        (mv nil oracle))
       (nonempty-queues (nonempty-queues queues))
       (next-queue (nth (min (nfix (car oracle))
                             (- (len nonempty-queues) 1))
                        nonempty-queues))
       (oracle (cdr oracle))
       (next (car (nth next-queue queues)))
       (queues (update-nth next-queue (cdr (nth next-queue queues))
                           queues))
       ((mv tail-queues tail-oracle)
        (schedule-queues queues oracle))
       ((when (and (consp next) (equal (car next) :transaction)))
        (mv (append (cdr next) tail-queues)
            tail-oracle)))
    (mv (cons next tail-queues)
        tail-oracle)))

;; This shows that sensible things happen even if the oracle is shorter in
;; length than expected. However, it also shows a potential ill-effect of
;; heedless scheduling, as the paths get scrambled because of unwanted
;; interleaving. We need to have transactions somehow...
(assert-event
 (mv-let
   (queue oracle)
   (schedule-queues
    (list
     (list
      (cons
       :set-path
       (path-to-fat32-path (coerce "/tmp/ticket1.txt" 'list)))
      :open
      :pwrite :close)
     (list
      (cons
       :set-path
       (path-to-fat32-path (coerce "/tmp/ticket2.txt" 'list)))
      :open
      :pwrite :close))
    (list 0 1 1 1 0 0))
   (and (equal queue
               '((:SET-PATH "TMP        " "TICKET1 TXT")
                 (:SET-PATH "TMP        " "TICKET2 TXT")
                 :open :pwrite
                 :open :pwrite
                 :close :close))
        (equal oracle nil))))

(defconst
  *example-prog-2-queues*
  (list
   (list
    (cons
     :transaction
     (list
      (cons
       :set-path
       (path-to-fat32-path (coerce "/tmp/ticket1.txt" 'list)))
      :open
      :pwrite :close)))
   (list
    (cons
     :transaction
     (list
      (cons
       :set-path
       (path-to-fat32-path (coerce "/tmp/ticket2.txt" 'list)))
      :open
      :pwrite :close)))))

;; This is a little bit better... we get an interleaving, but we leave the
;; important things in place.
(assert-event
 (mv-let
   (queue oracle)
   (schedule-queues
    *example-prog-2-queues*
    (list 1 1 1 0 0 0))
   (and (equal queue
               '((:SET-PATH "TMP        " "TICKET2 TXT")
                 :OPEN :PWRITE :CLOSE
                 (:SET-PATH "TMP        " "TICKET1 TXT")
                 :OPEN
                 :PWRITE :CLOSE))
        (equal oracle (list 1 0 0 0)))))

(defthm oracle-prog-2-correctness-1
  (implies
   (true-equiv o1 o2)
   (collapse-equiv
    (mv-nth
     0
     (absfat-oracle-multi-step
      (frame-with-root (list (cons "TMP        " (make-m1-file :contents nil))) nil)
      (mv-nth 0
              (schedule-queues
               *example-prog-2-queues*
               o1))
      (make-fat-st)))
    (mv-nth
     0
     (absfat-oracle-multi-step
      (frame-with-root (list (cons "TMP        " (make-m1-file :contents nil))) nil)
      (mv-nth 0
              (schedule-queues
               *example-prog-2-queues*
               o2))
      (make-fat-st)))))
  :hints (("Goal" :in-theory (enable schedule-queues absfat-oracle-multi-step)
           :do-not-induct t
           :expand
           (:free (x y o) (schedule-queues (cons x y) o))))
  :rule-classes :congruence)

(defconst
  *example-prog-3-queues*
  (list
   (list
    (cons
     :transaction
     (list
      (cons
       :set-path
       (path-to-fat32-path (coerce "/tmp/ticket1.txt" 'list)))
      :open
      :pwrite :close)))
   (list
    (cons
     :transaction
     (list
      (cons
       :set-path
       (path-to-fat32-path (coerce "/tmp/ticket2.txt" 'list)))
      :open
      :pwrite :close)))
   (list
    (cons
     :transaction
     (list
      (cons
       :set-path
       (path-to-fat32-path (coerce "/tmp/ticket3.txt" 'list)))
      :open
      :pwrite :close)))))

(defthm oracle-prog-3-correctness-1
  (implies
   (true-equiv o1 o2)
   (collapse-equiv
    (mv-nth
     0
     (absfat-oracle-multi-step
      (frame-with-root (list (cons "TMP        " (make-m1-file :contents nil))) nil)
      (mv-nth 0
              (schedule-queues
               *example-prog-2-queues*
               o1))
      (make-fat-st)))
    (mv-nth
     0
     (absfat-oracle-multi-step
      (frame-with-root (list (cons "TMP        " (make-m1-file :contents nil))) nil)
      (mv-nth 0
              (schedule-queues
               *example-prog-2-queues*
               o2))
      (make-fat-st)))))
  :hints (("Goal" :in-theory (enable schedule-queues absfat-oracle-multi-step)
           :do-not-induct t
           :expand
           (:free (x y o) (schedule-queues (cons x y) o))))
  :rule-classes :congruence)

(defund cp-without-subdirs-helper (src dst names)
  (if
      (atom names)
      nil
    (cons
     (list
      (cons
       :transaction
       (list
        (cons :set-path (append src (list (car names))))
        :open
        (cons :set-count (expt 2 32))
        :pread
        :close
        (cons :set-path (append dst (list (car names))))
        :open
        :pwrite
        :close)))
     (cp-without-subdirs-helper src dst (cdr names)))))

(defthm cp-without-subdirs-helper-correctness-1
  (and (true-list-listp (cp-without-subdirs-helper src dst names))
       (equal (len (cp-without-subdirs-helper src dst names))
              (len names)))
  :hints (("Goal" :in-theory (enable cp-without-subdirs-helper))))

(defund plus-list (l n)
  (if (atom l)
      nil
    (cons (+ (car l) n)
          (plus-list (cdr l) n))))

(defthm plus-list-of-append
  (equal (plus-list (append x y) n)
         (append (plus-list x n)
                 (plus-list y n)))
  :hints (("goal" :in-theory (enable plus-list))))

(defthm
  plus-list-correctness-1
  (iff (equal (plus-list l n)
              (acl2-number-list-fix l))
       (or (equal (fix n) 0) (atom l)))
  :hints (("goal" :in-theory (enable acl2-number-list-fix plus-list)))
  :rule-classes
  ((:rewrite :corollary (implies (equal (fix n) 0)
                                 (equal (plus-list l n)
                                        (acl2-number-list-fix l))))
   (:type-prescription :corollary (implies (atom l)
                                           (equal (plus-list l n) nil)))))

(defthm
  nonempty-queues-of-append
  (equal (nonempty-queues (append x y))
         (append (nonempty-queues x)
                 (plus-list (nonempty-queues y)
                            (len x))))
  :hints
  (("goal" :in-theory (e/d (nonempty-queues append plus-list
                                            len painful-debugging-lemma-21)
                           (nth-when->=-n-len-l))
    :induct (nonempty-queues y)
    :expand (nonempty-queues (append x y)))
   ("subgoal *1/2" :cases ((consp (cdr y)))
    :use (:instance (:rewrite nth-when->=-n-len-l)
                    (l x)
                    (n (+ -1 (len x) (len y)))))))

(defthm nonempty-queues-of-cons
  (equal (nonempty-queues (cons x y))
         (if (consp x)
             (cons 0 (plus-list (nonempty-queues y) 1))
             (plus-list (nonempty-queues y) 1)))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (nonempty-queues)
                           (nonempty-queues-of-append))
           :use (:instance nonempty-queues-of-append
                           (x (list x))))))

(defthm member-of-plus-list
  (iff (member-equal x (plus-list l n))
       (and (acl2-numberp x)
            (member-equal (- x n)
                          (acl2-number-list-fix l))))
  :hints (("goal" :in-theory (enable plus-list member-equal))))

(defthm
  cp-without-subdirs-helper-correctness-lemma-1
  (implies
   (member-equal n
                 (nonempty-queues (cp-without-subdirs-helper src dst names)))
   (equal (nth n
               (cp-without-subdirs-helper src dst names))
          (list (list* :transaction
                       (cons :set-path (append src (list (nth n names))))
                       :open '(:set-count . 4294967296)
                       :pread :close
                       (cons :set-path (append dst (list (nth n names))))
                       '(:open :pwrite :close)))))
  :hints (("goal" :in-theory (enable cp-without-subdirs-helper nth))))

(defund cp-spec-1 (frame syscall-sym-list st src fs)
  (declare (xargs :verify-guards nil
                  :measure (len syscall-sym-list)))
  (b*
      (((when (atom syscall-sym-list)) t)
       ((mv new-frame st)
        (absfat-oracle-single-step frame (car syscall-sym-list) st))
       ((unless (and (equal
                      (remove-assoc-equal (abs-find-file-src src new-frame) new-frame)
                      (remove-assoc-equal (abs-find-file-src src frame) frame))
                     (absfat-subsetp
                      (cdr
                       (assoc-equal (abs-find-file-src src new-frame) new-frame))
                      fs)))
        nil))
    (cp-spec-1 new-frame (cdr syscall-sym-list) st src fs)))

(defthm
  cp-without-subdirs-helper-correctness-lemma-2
  (equal (consp (flatten (cp-without-subdirs-helper src dst names)))
         (consp names))
  :hints (("goal"
           :in-theory (enable cp-without-subdirs-helper))))

(defthm
  cp-without-subdirs-helper-correctness-lemma-3
  (implies
   (and (cp-spec-1 frame syscall-sym-list st src fs)
        (absfat-subsetp (cdr (assoc-equal (abs-find-file-src src frame)
                                          frame))
                        fs))
   (b*
       (((mv new-frame &)
         (absfat-oracle-multi-step frame syscall-sym-list st)))
     (and (equal (remove-assoc-equal (abs-find-file-src src new-frame)
                                     new-frame)
                 (remove-assoc-equal (abs-find-file-src src frame)
                                     frame))
          (absfat-subsetp (cdr (assoc-equal (abs-find-file-src src new-frame)
                                            new-frame))
                          fs))))
  :hints (("goal" :in-theory (enable absfat-oracle-multi-step cp-spec-1))))

(skip-proofs
 (defthm
   cp-without-subdirs-helper-correctness-lemma-4
   (implies
    (absfat-subsetp (cdr (assoc-equal (abs-find-file-src src frame)
                                      frame))
                    fs)
    (cp-spec-1 frame
               (mv-nth
                0
                (schedule-queues (cp-without-subdirs-helper src dst names)
                                 o))
               st src fs))
   :hints (("goal" :in-theory (enable cp-without-subdirs-helper schedule-queues
                                      cp-spec-1 absfat-oracle-single-step
                                      abs-pwrite)))))

(defund cp-spec-2 (frame syscall-sym-list st src fs)
  (declare (xargs :verify-guards nil
                  :measure (len syscall-sym-list)))
  (b*
      (((when (atom syscall-sym-list)) t)
       ((mv new-frame st)
        (absfat-oracle-single-step frame (car syscall-sym-list) st))
       ((unless (and (equal
                      (remove-assoc-equal (abs-find-file-src src new-frame) new-frame)
                      (remove-assoc-equal (abs-find-file-src src frame) frame))
                     (absfat-subsetp
                      fs
                      (cdr
                       (assoc-equal (abs-find-file-src src new-frame) new-frame)))))
        nil))
    (cp-spec-2 new-frame (cdr syscall-sym-list) st src fs)))

(defthm
  cp-without-subdirs-helper-correctness-lemma-5
  (implies
   (and (cp-spec-2 frame syscall-sym-list st src fs)
        (absfat-subsetp fs
                        (cdr (assoc-equal (abs-find-file-src src frame)
                                          frame))))
   (b*
       (((mv new-frame &)
         (absfat-oracle-multi-step frame syscall-sym-list st)))
     (and (equal (remove-assoc-equal (abs-find-file-src src new-frame)
                                     new-frame)
                 (remove-assoc-equal (abs-find-file-src src frame)
                                     frame))
          (absfat-subsetp fs
                          (cdr (assoc-equal (abs-find-file-src src new-frame)
                                            new-frame))))))
  :hints (("goal" :in-theory (enable absfat-oracle-multi-step cp-spec-2))))

(defund cp-spec-3 (queues dst)
  (or (atom queues)
      (and
       (or (atom (car queues))
           (and (atom (cdar queues))
                (equal (caaar queues) :transaction)
                (equal (car (nth 0 (cdaar queues))) :set-path)
                (equal (nth 1 (cdaar queues)) :open)
                (equal (car (nth 2 (cdaar queues))) :set-count)
                (equal (nth 3 (cdaar queues)) :pread)
                (equal (nth 4 (cdaar queues)) :close)
                (equal (car (nth 5 (cdaar queues))) :set-path)
                (equal (nth 6 (cdaar queues)) :open)
                (equal (nth 7 (cdaar queues)) :pwrite)
                (equal (nth 8 (cdaar queues)) :close)
                (atom (nthcdr 9 (cdaar queues)))
                (fat32-filename-list-equiv
                 dst
                 (dirname
                  (cdr (nth 5 (cdaar queues)))))))
       (cp-spec-3 (cdr queues) dst))))

(defthm
   cp-without-subdirs-helper-correctness-lemma-6
   (cp-spec-3 (cp-without-subdirs-helper src dst names)
              dst)
   :hints (("goal" :in-theory (enable cp-without-subdirs-helper cp-spec-3)
            :expand
            (dirname (append dst (list (car names)))))))

(defthm cp-without-subdirs-helper-correctness-lemma-7
  (implies (cp-spec-3 queues dst)
           (and (not (consp (cdr (nth n queues))))
                (list-equiv (cdr (nth n queues)) nil)))
  :hints (("goal" :in-theory (enable nth cp-spec-3))))

(defthm cp-without-subdirs-helper-correctness-lemma-8
  (implies (and (cp-spec-3 queues dst) (atom val))
           (cp-spec-3 (update-nth key val queues)
                      dst))
  :hints (("goal" :in-theory (enable update-nth cp-spec-3))))

(defthm
  take-of-true-list-list-fix
  (equal (take n (true-list-list-fix x))
         (true-list-list-fix (take n x)))
  :hints
  (("goal" :in-theory (e/d (true-list-list-fix)
                           (take-of-too-many take-when-atom take-of-cons)))))

(defthmd
  nonempty-queues-of-true-list-list-fix
  (equal (nonempty-queues (true-list-list-fix queues))
         (nonempty-queues queues))
  :hints (("goal" :in-theory (enable nonempty-queues true-list-list-fix)
           :induct (nonempty-queues queues)
           :expand (nonempty-queues (true-list-list-fix queues)))))

(defcong
 true-list-list-equiv equal
 (nonempty-queues queues)
 1
 :hints (("Goal"
          :use
          (nonempty-queues-of-true-list-list-fix
           (:instance
            nonempty-queues-of-true-list-list-fix
            (queues queues-equiv))))))

(defthm true-list-list-fix-of-update-nth
  (equal (true-list-list-fix (update-nth key val l))
         (update-nth key (true-list-fix val)
                     (true-list-list-fix l)))
  :hints (("goal" :in-theory (enable true-list-list-fix))))

(defthm flatten-of-true-list-list-fix
  (equal (flatten (true-list-list-fix queues))
         (flatten queues))
  :hints (("goal" :in-theory (enable true-list-list-fix flatten))))

(defthmd
  schedule-queues-of-true-list-list-fix
  (equal
   (schedule-queues (true-list-list-fix queues) o)
   (schedule-queues queues o))
  :hints (("goal" :in-theory (enable schedule-queues true-list-list-fix)
           :induct (schedule-queues queues o)
           :expand
           (schedule-queues (true-list-list-fix queues)
                            o))))

(defcong
  true-list-list-equiv
  equal (schedule-queues queues o)
  1
  :hints
  (("goal"
    :use (schedule-queues-of-true-list-list-fix
          (:instance schedule-queues-of-true-list-list-fix
                     (queues queues-equiv))))))

(defcong list-equiv true-list-list-equiv
  (update-nth key val l)
  2
  :hints (("goal" :in-theory (enable update-nth))))

(defthm cp-without-subdirs-helper-correctness-lemma-9
  (implies (cp-spec-3 queues dst)
           (not (equal (car (nth n queues)) :close)))
  :hints (("goal" :in-theory (enable nth cp-spec-3))))

(defthm cp-without-subdirs-helper-correctness-lemma-10
  (implies (cp-spec-3 queues dst)
           (equal (consp (car (nth n queues)))
                  (consp (nth n queues))))
  :hints (("goal" :in-theory (enable nth cp-spec-3 nonempty-queues))))

(defthm cp-without-subdirs-helper-correctness-lemma-11
  (implies (cp-spec-3 queues dst)
           (equal (equal (car (car (nth n queues)))
                         :transaction)
                  (consp (nth n queues))))
  :hints (("goal" :in-theory (enable nth cp-spec-3 nonempty-queues))))

(defthm cp-without-subdirs-helper-correctness-lemma-12
  (implies (and
            (not (consp (assoc-equal z frame)))
            (syntaxp (not (quotep z))))
           (iff (equal (abs-find-file-src frame path) z)
                (and (equal (abs-find-file-src frame path) 0)
                     (equal z 0)))))

(encapsulate
  ()

  (local (include-book "std/lists/prefixp" :dir :system))

  (defthm
    cp-without-subdirs-helper-correctness-lemma-13
    (implies
     (and (path-clear path frame)
          (no-duplicatesp-equal (strip-cars frame))
          (atom (assoc-equal 0 frame)))
     (not
      (consp
       (names-at
        (frame-val->dir (cdr (assoc-equal (abs-find-file-src frame path)
                                          frame)))
        (nthcdr
         (len (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                                 frame))))
         path)))))
    :hints (("goal" :in-theory (enable path-clear
                                       abs-find-file-src frame-p strip-cars
                                       no-duplicatesp-equal names-at)))))

;; (assert-event
;;  (b*
;;      (((mv frame st)
;;        (absfat-oracle-multi-step
;;         (frame-with-root
;;          '(("TMP        "
;;             (D-E 0 0 0 0 0 0 0 0 0 0 0 0
;;                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;             (contents
;;              ("TICKET2 TXT"
;;               (d-e 0 0 0 0 0 0 0 0 0 0 0 0
;;                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;               (contents . ""))
;;              ("TICKET3 TXT"
;;               (d-e 0 0 0 0 0 0 0 0 0 0 0 0
;;                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;               (contents . ""))
;;              ("TICKET1 TXT"
;;               (d-e 0 0 0 0 0 0 0 0 0 0 0 0
;;                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;               (contents . ""))))
;;            ("VAR        "
;;             (d-e 0 0 0 0 0 0 0 0 0 0 0 16
;;                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;             (contents
;;              ("TMP        "
;;               (d-e 0 0 0 0 0 0 0 0 0 0 0 16
;;                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;               (contents)))))
;;          nil)
;;         '((:set-path "TMP        " "TICKET2 TXT")
;;           :open (:set-count . 4294967296)
;;           :pread :close
;;           (:set-path "VAR        "
;;                      "TMP        " "TICKET2 TXT")
;;           :open :pwrite :close
;;           (:set-path "TMP        " "TICKET3 TXT")
;;           :open (:set-count . 4294967296)
;;           :pread :close
;;           (:set-path "VAR        "
;;                      "TMP        " "TICKET3 TXT")
;;           :open :pwrite :close
;;           (:set-path "TMP        " "TICKET1 TXT")
;;           :open (:set-count . 4294967296)
;;           :pread :close
;;           (:set-path "VAR        "
;;                      "TMP        " "TICKET1 TXT")
;;           :open
;;           :pwrite :close)
;;         (make-fat-st))))
;;    (and
;;     (equal
;;      frame
;;      '((0
;;         (path)
;;         (dir
;;          ("TMP        "
;;           (d-e 0 0 0 0 0 0 0 0 0 0 0 0
;;                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;           (contents
;;            ("TICKET2 TXT"
;;             (d-e 0 0 0 0 0 0 0 0 0 0 0 0
;;                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;             (contents . ""))
;;            ("TICKET3 TXT"
;;             (d-e 0 0 0 0 0 0 0 0 0 0 0 0
;;                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;             (contents . ""))
;;            ("TICKET1 TXT"
;;             (d-e 0 0 0 0 0 0 0 0 0 0 0 0
;;                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;             (contents . ""))))
;;          ("VAR        "
;;           (d-e 0 0 0 0 0 0 0 0 0 0 0 16
;;                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;           (contents
;;            ("TMP        "
;;             (d-e 0 0 0 0 0 0 0 0 0 0 0 16
;;                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;             (contents 1)))))
;;         (src . 0))
;;        (1
;;         (path "VAR        " "TMP        ")
;;         (dir ("TICKET2 TXT"
;;               (d-e 0 0 0 0 0 0 0 0 0 0 0 0
;;                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;               (contents . ""))
;;              ("TICKET3 TXT"
;;               (d-e 0 0 0 0 0 0 0 0 0 0 0 0
;;                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;               (contents . ""))
;;              ("TICKET1 TXT"
;;               (d-e 0 0 0 0 0 0 0 0 0 0 0 0
;;                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;               (contents . "")))
;;         (src . 0))))
;;     (equal st
;;            '((fd . 0)
;;              (buf . "")
;;              (offset . 0)
;;              (count . 4294967296)
;;              (retval . 0)
;;              (errno . 0)
;;              (PATH "VAR        "
;;                    "TMP        " "TICKET1 TXT")
;;              (stat (st_size . 0))
;;              (statfs (f_type . 0)
;;                      (f_bsize . 0)
;;                      (f_blocks . 0)
;;                      (f_bfree . 0)
;;                      (f_bavail . 0)
;;                      (f_files . 0)
;;                      (f_ffree . 0)
;;                      (f_fsid . 0)
;;                      (f_namelen . 72))
;;              (dirp . 0)
;;              (fd-table)
;;              (file-table)
;;              (dir-stream-table)
;;              (oracle))))))

;; ;; This assertion shows a little bit about the problems with the current
;; ;; definition of 1st-complete-under-path and in turn partial-collapse. There
;; ;; was no need to split the 1 variable and produce the 2 variable, but that's
;; ;; what we ended up doing...
;; (assert-event
;;  (b*
;;      (((mv frame st)
;;        (absfat-oracle-multi-step
;;         '((0
;;            (PATH)
;;            (DIR
;;             ("TMP        "
;;              (D-E 0 0 0 0 0 0 0 0 0 0 0 0
;;                   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;              (CONTENTS ("TICKET2 TXT" (D-E 0 0 0 0 0 0 0 0 0 0 0 0
;;                                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;                         (CONTENTS . ""))
;;                        ("TICKET3 TXT" (D-E 0 0 0 0 0 0 0 0 0 0 0 0
;;                                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;                         (CONTENTS . ""))
;;                        ("TICKET1 TXT" (D-E 0 0 0 0 0 0 0 0 0 0 0 0
;;                                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;                         (CONTENTS . ""))))
;;             ("VAR        " (D-E 0 0 0 0 0 0 0 0 0 0 0 16
;;                                 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;              (CONTENTS 1)))
;;            (SRC . 0))
;;           (1 (PATH "VAR        ")
;;              (DIR ("TMP        " (D-E 0 0 0 0 0 0 0 0 0 0 0 16
;;                                       0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;                    (CONTENTS)))
;;              (SRC . 0)))
;;         '((:set-path "TMP        " "TICKET2 TXT")
;;           :open (:set-count . 4294967296)
;;           :pread :close
;;           (:set-path "VAR        "
;;                      "TMP        " "TICKET2 TXT")
;;           :open :pwrite :close
;;           (:set-path "TMP        " "TICKET3 TXT")
;;           :open (:set-count . 4294967296)
;;           :pread :close
;;           (:set-path "VAR        "
;;                      "TMP        " "TICKET3 TXT")
;;           :open :pwrite :close
;;           (:set-path "TMP        " "TICKET1 TXT")
;;           :open (:set-count . 4294967296)
;;           :pread :close
;;           (:set-path "VAR        "
;;                      "TMP        " "TICKET1 TXT")
;;           :open
;;           :pwrite :close)
;;         (make-fat-st))))
;;    (and
;;     (equal
;;      frame
;;      '((0
;;         (path)
;;         (dir
;;          ("TMP        "
;;           (d-e 0 0 0 0 0 0 0 0 0 0 0 0
;;                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;           (contents ("TICKET2 TXT" (d-e 0 0 0 0 0 0 0 0 0 0 0 0
;;                                         0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;                      (contents . ""))
;;                     ("TICKET3 TXT" (d-e 0 0 0 0 0 0 0 0 0 0 0 0
;;                                         0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;                      (contents . ""))
;;                     ("TICKET1 TXT" (d-e 0 0 0 0 0 0 0 0 0 0 0 0
;;                                         0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;                      (contents . ""))))
;;          ("VAR        " (d-e 0 0 0 0 0 0 0 0 0 0 0 16
;;                              0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;           (contents 1)))
;;         (src . 0))
;;        (2 (path "VAR        " "TMP        ")
;;           (dir ("TICKET2 TXT" (d-e 0 0 0 0 0 0 0 0 0 0 0 0
;;                                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;                 (contents . ""))
;;                ("TICKET3 TXT" (d-e 0 0 0 0 0 0 0 0 0 0 0 0
;;                                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;                 (contents . ""))
;;                ("TICKET1 TXT" (d-e 0 0 0 0 0 0 0 0 0 0 0 0
;;                                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;                 (contents . "")))
;;           (src . 1))
;;        (1 (path "VAR        ")
;;           (dir ("TMP        " (d-e 0 0 0 0 0 0 0 0 0 0 0 16
;;                                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;                 (contents 2)))
;;           (src . 0))))
;;     (equal st
;;            '((fd . 0)
;;              (buf . "")
;;              (offset . 0)
;;              (count . 4294967296)
;;              (retval . 0)
;;              (errno . 0)
;;              (PATH "VAR        "
;;                    "TMP        " "TICKET1 TXT")
;;              (stat (st_size . 0))
;;              (statfs (f_type . 0)
;;                      (f_bsize . 0)
;;                      (f_blocks . 0)
;;                      (f_bfree . 0)
;;                      (f_bavail . 0)
;;                      (f_files . 0)
;;                      (f_ffree . 0)
;;                      (f_fsid . 0)
;;                      (f_namelen . 72))
;;              (dirp . 0)
;;              (fd-table)
;;              (file-table)
;;              (dir-stream-table)
;;              (oracle))))))

(encapsulate
  ()

  (local (include-book "std/lists/prefixp" :dir :system))

  ;; This is important because it is annoying.
  (defthm
    1st-complete-under-path-could-fire-up-at-a-painful-moment
    (implies
     (and
      (frame-p frame)
      (consp (assoc-equal x frame))
      (atom (assoc-equal 0 frame))
      (abs-complete (frame-val->dir (cdr (assoc-equal x frame))))
      (equal (1st-complete-under-path frame path) 0))
     (and
      (not
       (fat32-filename-list-equiv
        path (frame-val->path (cdr (assoc-equal x frame)))))
      (not
       (fat32-filename-list-equiv
        (frame-val->path (cdr (assoc-equal x frame))) path))))
    :hints (("goal" :in-theory (enable 1st-complete-under-path
                                       assoc-equal frame-p)))))

(defthm cp-without-subdirs-helper-correctness-lemma-16
  (implies (good-frame-p frame)
           (< 0 (find-new-index (strip-cars frame))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable good-frame-p)))
  :rule-classes
  (:linear
   :rewrite
   (:rewrite
    :corollary
    (implies (good-frame-p frame)
             (not (equal (find-new-index (strip-cars frame)) 0))))))

(defthm
  cp-without-subdirs-helper-correctness-lemma-17
  (implies
   (and (good-frame-p frame)
        (equal (1st-complete (frame->frame frame))
               0))
   (and
    (not
     (consp (abs-addrs (frame-val->dir$inline (cdr (assoc-equal 0 frame))))))
    (abs-complete (frame->root frame))
    (abs-complete (frame-val->dir$inline (cdr (assoc-equal 0 frame))))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable good-frame-p
                              collapse frame->root abs-complete))))

(defthm cp-without-subdirs-helper-correctness-lemma-20
  (implies (and (integerp n) (abs-complete x))
           (not (equal (list n) x)))
  :hints (("goal" :in-theory (enable abs-complete abs-addrs))))

;; Move later.
(defthm abs-file-alist-p-of-abs-alloc
  (and (abs-file-alist-p (mv-nth 0 (abs-alloc fs path new-index)))
       (abs-file-alist-p (mv-nth 1 (abs-alloc fs path new-index))))
  :hints (("goal" :in-theory (e/d (abs-alloc) nil))))

(defthm hifat-no-dups-p-of-abs-alloc
  (implies (and (hifat-no-dups-p fs)
                (m1-file-alist-p fs))
           (hifat-no-dups-p (mv-nth 0 (abs-alloc fs path new-index))))
  :hints (("goal" :in-theory (enable hifat-no-dups-p abs-alloc
                                     abs-fs-p-when-hifat-no-dups-p))))

(defthm
  cp-without-subdirs-helper-correctness-lemma-18
  (ctx-app-ok (mv-nth '1 (abs-alloc fs 'nil n))
              n 'nil)
  :hints
  (("goal" :do-not-induct t
    :in-theory (enable ctx-app-ok abs-alloc addrs-at))))

(defthm
  abs-find-file-src-of-remove-assoc-1
  (implies
   (and
    (not (null x))
    (no-duplicatesp-equal (strip-cars frame))
    (or
     (not (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                   (fat32-filename-list-fix path)))
     (equal
      (mv-nth 1
              (abs-find-file-helper
               (frame-val->dir (cdr (assoc-equal x frame)))
               (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                       path)))
      *enoent*)))
   (equal (abs-find-file-src (remove-assoc-equal x frame)
                             path)
          (abs-find-file-src frame path)))
  :hints (("goal" :in-theory (enable abs-find-file-src remove-assoc-equal
                                     no-duplicatesp-equal strip-cars)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and
      (not (null x))
      (no-duplicatesp-equal (strip-cars frame))
      (or
       (not (fat32-filename-list-prefixp
             (frame-val->path (cdr (assoc-equal x frame)))
             path))
       (equal
        (mv-nth 1
                (abs-find-file-helper
                 (frame-val->dir (cdr (assoc-equal x frame)))
                 (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                         path)))
        *enoent*)))
     (equal (abs-find-file-src (remove-assoc-equal x frame)
                               path)
            (abs-find-file-src frame path)))
    :hints (("Goal" :do-not-induct t
             :in-theory (enable fat32-filename-list-prefixp-alt))))))

(defthm
  abs-find-file-src-of-frame->frame-1
  (implies
   (and
    (no-duplicatesp-equal (strip-cars frame))
    (or
     (not (fat32-filename-list-prefixp
           (frame-val->path (cdr (assoc-equal 0 frame)))
           path))
     (equal
      (mv-nth 1
              (abs-find-file-helper
               (frame-val->dir (cdr (assoc-equal 0 frame)))
               (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                       path)))
      2)))
   (equal (abs-find-file-src (frame->frame frame)
                             path)
          (abs-find-file-src frame path)))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (frame->frame fat32-filename-list-prefixp-alt)
                           (abs-find-file-src-of-remove-assoc-1))
           :use (:instance abs-find-file-src-of-remove-assoc-1
                           (x 0)))))

(defthm
  cp-without-subdirs-helper-correctness-lemma-19
  (implies (good-frame-p frame)
           (and (no-duplicatesp-equal (strip-cars frame))
                (list-equiv (frame-val->path (cdr (assoc-equal 0 frame)))
                            nil)
                (mv-nth '1 (collapse frame))
                (frame-p frame)
                (abs-separate frame)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable good-frame-p))))

(defthm cp-without-subdirs-helper-correctness-lemma-21
  (implies (atom n)
           (equal (names-at (list n) path) nil))
  :hints (("goal" :in-theory (enable names-at abs-fs-fix))))

(defthm
  cp-without-subdirs-helper-correctness-lemma-22
  (implies (atom n)
           (equal (mv-nth 1 (abs-find-file-helper (list n) src))
                  *enoent*))
  :hints (("goal" :in-theory (enable abs-find-file-helper abs-fs-fix))))

(defthm
  cp-without-subdirs-helper-correctness-lemma-23
  (implies
   (and
    (good-frame-p frame)
    (equal (1st-complete (frame->frame frame))
           0)
    (equal
     (mv-nth
      1
      (hifat-find-file
       (put-assoc-equal name
                        (m1-file '(0 0 0 0 0 0 0 0 0 0 0 0
                                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                                 contents)
                        (frame->root frame))
       src))
     *enoent*)
    (fat32-filename-p name)
    (stringp contents))
   (equal
    (mv-nth
     1
     (hifat-find-file (frame-val->dir$inline (cdr (assoc-equal 0 frame)))
                      src))
    *enoent*))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (abs-pwrit1 abs-pwrite
                                abs-find-file-src-of-frame-with-root
                                abs-find-file-src
                                partial-collapse 1st-complete
                                collapse-this remove-assoc-when-absent-1
                                abs-alloc hifat-find-file)
                    ((:rewrite-quoted-constant true-fix-under-true-equiv)))
    :expand ((:free (fs)
                    (hifat-find-file fs src))))))

(defthm cp-without-subdirs-helper-correctness-lemma-24
  (implies (not (consp (frame->frame frame)))
           (equal (abs-find-file-src frame src) 0))
  :hints (("goal" :in-theory (enable abs-find-file-src frame->frame))))

(defthm
  cp-without-subdirs-helper-correctness-lemma-14
  (equal
   (mv-nth
    1
    (abs-find-file-helper
     (mv-nth 1
             (abs-alloc (frame-val->dir (cdr (assoc-equal 0 frame)))
                        nil
                        (find-new-index (strip-cars frame))))
     src))
   *enoent*)
  :hints (("goal" :in-theory (enable abs-mkdir-correctness-lemma-4 dirname
                                     basename abs-find-file-helper abs-alloc)
           :do-not-induct t)))

(defthm cp-without-subdirs-helper-correctness-lemma-15
  (implies (stringp contents)
           (not (abs-directory-file-p (m1-file d-e contents))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable m1-file abs-directory-file-p
                              abs-file-p abs-file->contents))))

(defthmd cp-without-subdirs-helper-correctness-lemma-25
  (equal (mv-nth 0
                 (abs-alloc fs path (true-fix new-index)))
         (mv-nth 0 (abs-alloc fs path new-index)))
  :hints (("goal" :in-theory (enable abs-alloc))))

(defthm
  cp-without-subdirs-helper-correctness-lemma-26
  (equal (mv-nth 0 (abs-alloc fs path x))
         (mv-nth 0 (abs-alloc fs path y)))
  :hints
  (("goal" :use ((:instance cp-without-subdirs-helper-correctness-lemma-25
                            (new-index x))
                 (:instance cp-without-subdirs-helper-correctness-lemma-25
                            (new-index y)))))
  :rule-classes
  ((:congruence
    :corollary (implies (true-equiv x y)
                        (equal (mv-nth 0 (abs-alloc fs path x))
                               (mv-nth 0 (abs-alloc fs path y)))))))

(defthm abs-no-dups-p-of-abs-alloc
  (implies (and (abs-no-dups-p fs)
                (abs-file-alist-p fs))
           (abs-no-dups-p (mv-nth 0 (abs-alloc fs path new-index))))
  :hints (("goal" :in-theory (enable abs-no-dups-p abs-alloc))))

(defthm
  ctx-app-ok-of-abs-alloc-2
  (implies
   ;; These clauses are a more explicit test for path's existence...
   (and (zp (mv-nth 1 (abs-find-file-helper fs path)))
        (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs path))))
   (ctx-app-ok (mv-nth 1 (abs-alloc fs path new-index))
               new-index path))
  :hints
  (("goal"
    :in-theory (e/d (ctx-app-ok abs-find-file-helper abs-alloc addrs-at)
                    ((:rewrite-quoted-constant true-fix-under-true-equiv)))
    :expand ((abs-file-contents-fix (list new-index))
             (abs-file-contents-p (list new-index))
             (abs-file-alist-p (list new-index))))))

(defthm abs-directory-file-p-when-not-m1-regular-file-p
  (implies (and (abs-file-p x)
                (not (m1-regular-file-p x)))
           (abs-directory-file-p x))
  :hints (("goal" :in-theory (enable abs-file-p-alt))))

(defthm strip-cars-of-frame->frame
  (equal (strip-cars (frame->frame frame))
         (remove-equal 0 (strip-cars frame)))
  :hints (("goal" :in-theory (enable frame->frame))))

;; Modelled after
;; abs-find-file-of-put-assoc.
(defthm
  abs-find-file-src-of-put-assoc
  (implies
   (and
    (frame-p (put-assoc-equal name val frame))
    (no-duplicatesp-equal (strip-cars (put-assoc-equal name val frame)))
    (or
     (not (prefixp (frame-val->path val)
                   (fat32-filename-list-fix path)))
     (equal (mv-nth 1
                    (abs-find-file-helper (frame-val->dir val)
                                          (nthcdr (len (frame-val->path val))
                                                  path)))
            *enoent*)
     (equal (mv-nth 1
                    (abs-find-file (remove-assoc-equal name frame)
                                   path))
            *enoent*)))
   (equal
    (abs-find-file-src (put-assoc-equal name val frame)
                       path)
    (if
     (and
      (prefixp (frame-val->path val)
               (fat32-filename-list-fix path))
      (not
       (equal
        (mv-nth 1
                (abs-find-file-helper (frame-val->dir val)
                                      (nthcdr (len (frame-val->path val))
                                              path)))
        *enoent*)))
     name
     (abs-find-file-src (remove-assoc-equal name frame)
                        path))))
  :hints (("goal" :in-theory (enable abs-find-file-src abs-find-file))))

(defthm
  cp-without-subdirs-helper-correctness-lemma-27
  (implies
   (and (atom (assoc-equal 0 frame))
        (not (zp name))
        (frame-p frame)
        (no-duplicatesp-equal (strip-cars frame)))
   (iff (> (1st-complete-under-path (put-assoc-equal name val frame)
                                    path)
           0)
        (or (> (1st-complete-under-path (remove-assoc-equal name frame)
                                        path)
               0)
            (and (fat32-filename-list-prefixp path (frame-val->path val))
                 (abs-complete (frame-val->dir val))))))
  :hints (("goal" :in-theory (enable 1st-complete-under-path
                                     strip-cars no-duplicatesp-equal))))

(defthm
  1st-complete-under-path-of-remove-assoc-1
  (implies (and (not (zp name))
                (equal (1st-complete-under-path frame path)
                       0))
           (equal (1st-complete-under-path (remove-assoc-equal name frame)
                                           path)
                  0))
  :hints (("goal" :in-theory (enable 1st-complete-under-path
                                     strip-cars no-duplicatesp-equal))))

(defthm fat32-filename-list-prefixp-when-fat32-filename-list-prefixp
  (implies (fat32-filename-list-prefixp x y)
           (equal (fat32-filename-list-prefixp y x)
                  (fat32-filename-list-equiv x y)))
  :hints (("goal" :in-theory (enable fat32-filename-list-equiv))))

(defthm
  cp-without-subdirs-helper-correctness-lemma-28
  (implies
   (and
    (frame-p (frame->frame frame))
    (consp (assoc-equal x (frame->frame frame)))
    (abs-complete (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
    (equal (1st-complete-under-path (frame->frame frame)
                                    path)
           0)
    (equal (assoc-equal x (frame->frame frame))
           (assoc-equal x frame)))
   (and
    (not (fat32-filename-list-equiv
          path
          (frame-val->path (cdr (assoc-equal x frame)))))
    (not
     (fat32-filename-list-equiv (frame-val->path (cdr (assoc-equal x frame)))
                                path))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (disable 1st-complete-under-path-could-fire-up-at-a-painful-moment)
    :use (:instance 1st-complete-under-path-could-fire-up-at-a-painful-moment
                    (frame (frame->frame frame))))))

(defthm cp-without-subdirs-helper-correctness-lemma-29
  (implies (and (abs-fs-p (put-assoc-equal name val fs))
                (abs-fs-p fs)
                (case-split (not (null name))))
           (set-equiv (names-at (put-assoc-equal name val fs)
                                nil)
                      (cons name (names-at fs nil))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (names-at)))))

(defthm
  abs-complete-of-abs-fs-fix
  (implies (and (abs-file-alist-p abs-file-alist)
                (abs-complete abs-file-alist))
           (abs-complete (abs-fs-fix abs-file-alist)))
  :hints
  (("goal"
    :in-theory (e/d (abs-complete subsetp-equal)
                    (no-duplicatesp-of-abs-addrs-of-abs-fs-fix-lemma-1))
    :use no-duplicatesp-of-abs-addrs-of-abs-fs-fix-lemma-1)))

(defthm
  cp-without-subdirs-helper-correctness-lemma-30
  (implies
   (and (mv-nth 1 (collapse frame))
        (abs-separate (frame->frame frame))
        (frame-p (frame->frame frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (not (equal x 0)))
   (subsetp-equal (abs-addrs (frame-val->dir (cdr (assoc-equal x frame))))
                  (strip-cars frame)))
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d (assoc-of-frame->frame)
                    (path-clear-partial-collapse-when-zp-src-lemma-22))
    :use path-clear-partial-collapse-when-zp-src-lemma-22)))

(defthm
  cp-without-subdirs-helper-correctness-lemma-31
  (implies
   (good-frame-p frame)
   (subsetp-equal (abs-addrs (frame-val->dir (cdr (assoc-equal x frame))))
                  (strip-cars frame)))
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d (frame->root good-frame-p)
                    (cp-without-subdirs-helper-correctness-lemma-30))
    :use cp-without-subdirs-helper-correctness-lemma-30)))

(defthm
  cp-without-subdirs-helper-correctness-lemma-32
  (implies
   (good-frame-p frame)
   (no-duplicatesp-equal
    (abs-addrs
     (mv-nth
      1
      (abs-alloc
       (frame-val->dir (cdr (assoc-equal (abs-find-file-src frame path)
                                         frame)))
       (nthcdr
        (len (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                                frame))))
        path)
       (find-new-index (strip-cars frame)))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (abs-pwrit1 abs-pwrite
                                abs-find-file-src-of-frame-with-root
                                partial-collapse 1st-complete
                                collapse-this remove-assoc-when-absent-1
                                abs-alloc 1st-complete-under-path
                                assoc-of-frame->frame
                                frame->frame-of-put-assoc)
                    ((:rewrite-quoted-constant true-fix-under-true-equiv))))))

;; (encapsulate
;;   ()

;;   (local (in-theory
;;           (e/d (nth cp-spec-3 absfat-oracle-multi-step
;;                     absfat-oracle-single-step abs-find-file-src
;;                     abs-complete-when-atom-abs-addrs
;;                     abs-mkdir-correctness-lemma-76
;;                     ;; Enabling the following causes ACL2 to get really slow.
;;                     ;; abs-mkdir-correctness-lemma-238
;;                     abs-find-file-src-correctness-2
;;                     abs-addrs-of-ctx-app-lemma-2)
;;                ((:linear lofat-to-hifat-helper-correctness-1)
;;                 (:rewrite
;;                  lofat-to-hifat-helper-of-place-contents)
;;                 (:rewrite place-contents-expansion-2)
;;                 (:rewrite
;;                  lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-2)
;;                 (:rewrite
;;                  lofat-place-file-correctness-lemma-57)
;;                 (:rewrite
;;                  lofat-to-hifat-helper-of-update-fati)
;;                 (:rewrite consp-of-find-n-free-clusters)
;;                 (:rewrite
;;                  lofat-to-hifat-helper-of-update-dir-contents)
;;                 (:rewrite
;;                  not-intersectp-list-of-lofat-to-hifat-helper)
;;                 (:rewrite
;;                  count-free-clusters-of-set-indices-in-fa-table-1)
;;                 ;; somehow the whole thing gets slowed down when this is
;;                 ;; enabled...
;;                 (:rewrite remove-assoc-when-absent-1)
;;                 (:definition no-duplicatesp-equal)
;;                 (:type-prescription
;;                  abs-addrs-of-remove-assoc-lemma-1)
;;                 (:rewrite member-of-abs-addrs-when-natp . 2)
;;                 (:rewrite names-at-of-put-assoc)
;;                 (:rewrite abs-directory-file-p-correctness-1)
;;                 (:rewrite
;;                  path-clear-partial-collapse-when-zp-src-lemma-15)
;;                 (:rewrite str::consp-of-explode)
;;                 (:rewrite abs-mkdir-correctness-lemma-228)
;;                 (:rewrite consp-of-nthcdr)
;;                 (:type-prescription assoc-when-zp-len)
;;                 (:rewrite hifat-to-lofat-inversion-lemma-2)
;;                 (:linear
;;                  path-clear-partial-collapse-when-zp-src-lemma-9)
;;                 (:rewrite abs-directory-file-p-when-m1-file-p)
;;                 (:rewrite m1-directory-file-p-when-m1-file-p)
;;                 (:rewrite
;;                  no-duplicatesp-of-strip-cars-when-hifat-no-dups-p)
;;                 (:rewrite names-at-of-abs-alloc-2)
;;                 names-at-of-put-assoc
;;                 collapse-hifat-place-file-lemma-6
;;                 (:rewrite car-of-nthcdr)
;;                 (:rewrite nth-when->=-n-len-l)
;;                 (:rewrite nfix-when-zp)
;;                 (:rewrite
;;                  fat32-filename-p-of-nth-when-fat32-filename-list-p)
;;                 (:rewrite
;;                  append-nthcdr-dirname-basename-lemma-1
;;                  . 3)
;;                 (:definition nthcdr)
;;                 (:definition nat-equiv$inline)
;;                 (:rewrite m1-directory-file-p-correctness-1)
;;                 (:rewrite abs-pwrite-correctness-lemma-29)
;;                 (:definition nth)
;;                 (:rewrite frame-p-of-cdr-when-frame-p)
;;                 (:rewrite names-at-of-abs-alloc-1)
;;                 (:rewrite put-assoc-equal-without-change . 2)))))

;;   (local (include-book "std/lists/prefixp" :dir :system))
;;   (local (include-book "std/lists/intersectp" :dir :system))

;;   (local (deflabel theory-label))

;;   (local (in-theory (theory 'minimal-theory)))

;;   (encapsulate
;;     ()

;;     (local (in-theory (current-theory 'theory-label)))

;;     (thm
;;      (implies
;;       (and
;;        (good-frame-p frame)
;;        (not (consp (cdr (car queues))))
;;        (equal (car (car (car queues)))
;;               :transaction)
;;        (equal (car (car syscall-sym-list))
;;               :set-path)
;;        (equal (cadr syscall-sym-list) :open)
;;        (equal (car (caddr syscall-sym-list))
;;               :set-count)
;;        (equal (cadddr syscall-sym-list) :pread)
;;        (equal (car (cddddr syscall-sym-list))
;;               :close)
;;        (equal (car (cadr (cddddr syscall-sym-list)))
;;               :set-path)
;;        (equal (caddr (cddddr syscall-sym-list))
;;               :open)
;;        (equal (cadddr (cddddr syscall-sym-list))
;;               :pwrite)
;;        (equal (car (cddddr (cddddr syscall-sym-list)))
;;               :close)
;;        (not (consp (cdr (cddddr (cddddr syscall-sym-list)))))
;;        (equal
;;         (1st-complete-under-path (frame->frame frame)
;;                                  (dirname (cdr (cadr (cddddr syscall-sym-list)))))
;;         0)
;;        (consp syscall-sym-list)
;;        (consp (cdr syscall-sym-list))
;;        (consp (cddr syscall-sym-list))
;;        (consp (cdddr syscall-sym-list))
;;        (consp (cddddr syscall-sym-list))
;;        (consp (cdr (cddddr syscall-sym-list)))
;;        (consp (cddr (cddddr syscall-sym-list)))
;;        (consp (cdddr (cddddr syscall-sym-list)))
;;        (consp (cddddr (cddddr syscall-sym-list)))
;;        (consp (car syscall-sym-list))
;;        (consp (caddr syscall-sym-list))
;;        (not (integerp (cdr (caddr syscall-sym-list))))
;;        (consp (cadr (cddddr syscall-sym-list)))
;;        (not (m1-regular-file-p
;;              (mv-nth 0
;;                      (abs-find-file frame (cdr (car syscall-sym-list))))))
;;        (abs-complete
;;         (mv-nth
;;          0
;;          (abs-alloc
;;           (frame-val->dir$inline
;;            (cdr
;;             (assoc-equal
;;              (abs-find-file-src frame
;;                                 (dirname (cdr (cadr (cddddr syscall-sym-list)))))
;;              frame)))
;;           (nthcdr
;;            (len
;;             (frame-val->path$inline
;;              (cdr
;;               (assoc-equal
;;                (abs-find-file-src frame
;;                                   (dirname (cdr (cadr (cddddr syscall-sym-list)))))
;;                frame))))
;;            (dirname (cdr (cadr (cddddr syscall-sym-list)))))
;;           (find-new-index (strip-cars frame))))))
;;       (equal
;;        (abs-find-file-src
;;         (mv-nth
;;          0
;;          (abs-pwrit1
;;           (find-new-index (strip-cars (fat-st->fd-table st)))
;;           "" (fat-st->offset st)
;;           frame
;;           (cons
;;            (cons (find-new-index (strip-cars (fat-st->fd-table st)))
;;                  (find-new-index (strip-cars (fat-st->file-table st))))
;;            (remove-assoc-equal (find-new-index (strip-cars (fat-st->fd-table st)))
;;                                (fat-st->fd-table st)))
;;           (cons (cons (find-new-index (strip-cars (fat-st->file-table st)))
;;                       (file-table-element 0
;;                                           (cdr (cadr (cddddr syscall-sym-list)))))
;;                 (remove-assoc-equal
;;                  (find-new-index (strip-cars (fat-st->file-table st)))
;;                  (fat-st->file-table st)))))
;;         src)
;;        (abs-find-file-src frame src)))
;;      :hints (("Goal" :do-not-induct t :in-theory
;;               (e/d
;;                (abs-pwrit1 abs-pwrite
;;                            abs-find-file-src-of-frame-with-root
;;                            partial-collapse
;;                            1st-complete
;;                            collapse-this
;;                            remove-assoc-when-absent-1
;;                            abs-alloc
;;                            1st-complete-under-path
;;                            assoc-of-frame->frame
;;                            frame->frame-of-put-assoc
;;                            cp-without-subdirs-helper-correctness-lemma-34)
;;                ((:rewrite-quoted-constant true-fix-under-true-equiv)))
;;               :expand
;;               ((partial-collapse
;;                 (frame-with-root
;;                  (frame->root frame)
;;                  (cons
;;                   (cons
;;                    (find-new-index (strip-cars frame))
;;                    (frame-val
;;                     (dirname (cdr (cadr (cddddr syscall-sym-list))))
;;                     (put-assoc-equal
;;                      (basename (cdr (cadr (cddddr syscall-sym-list))))
;;                      (m1-file '(0 0 0 0 0 0 0 0 0 0 0 0
;;                                   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;                               (implode (insert-text nil (fat-st->offset st)
;;                                                     "")))
;;                      (mv-nth
;;                       0
;;                       (abs-alloc
;;                        (frame-val->dir
;;                         (cdr (assoc-equal
;;                               (abs-find-file-src
;;                                frame
;;                                (dirname (cdr (cadr (cddddr syscall-sym-list)))))
;;                               frame)))
;;                        (nthcdr
;;                         (len
;;                          (frame-val->path
;;                           (cdr
;;                            (assoc-equal
;;                             (abs-find-file-src
;;                              frame
;;                              (dirname (cdr (cadr (cddddr syscall-sym-list)))))
;;                             frame))))
;;                         (dirname (cdr (cadr (cddddr syscall-sym-list)))))
;;                        (find-new-index (strip-cars frame)))))
;;                     (abs-find-file-src
;;                      frame
;;                      (dirname (cdr (cadr (cddddr syscall-sym-list)))))))
;;                   (put-assoc-equal
;;                    (abs-find-file-src frame
;;                                       (dirname (cdr (cadr (cddddr syscall-sym-list)))))
;;                    (frame-val
;;                     (frame-val->path
;;                      (cdr
;;                       (assoc-equal (abs-find-file-src
;;                                     frame
;;                                     (dirname (cdr (cadr (cddddr syscall-sym-list)))))
;;                                    frame)))
;;                     (mv-nth
;;                      1
;;                      (abs-alloc
;;                       (frame-val->dir
;;                        (cdr (assoc-equal
;;                              (abs-find-file-src
;;                               frame
;;                               (dirname (cdr (cadr (cddddr syscall-sym-list)))))
;;                              frame)))
;;                       (nthcdr
;;                        (len
;;                         (frame-val->path
;;                          (cdr (assoc-equal
;;                                (abs-find-file-src
;;                                 frame
;;                                 (dirname (cdr (cadr (cddddr syscall-sym-list)))))
;;                                frame))))
;;                        (dirname (cdr (cadr (cddddr syscall-sym-list)))))
;;                       (find-new-index (strip-cars frame))))
;;                     (frame-val->src
;;                      (cdr
;;                       (assoc-equal (abs-find-file-src
;;                                     frame
;;                                     (dirname (cdr (cadr (cddddr syscall-sym-list)))))
;;                                    frame))))
;;                    (frame->frame frame))))
;;                 (dirname (cdr (cadr (cddddr syscall-sym-list)))))))))

;;     (thm
;;      (implies
;;       (and
;;        (not (consp (cdr (car queues))))
;;        (equal (car (car (car queues)))
;;               :transaction)
;;        (equal (car (car syscall-sym-list))
;;               :set-path)
;;        (equal (cadr syscall-sym-list) :open)
;;        (equal (car (caddr syscall-sym-list))
;;               :set-count)
;;        (equal (cadddr syscall-sym-list) :pread)
;;        (equal (car (cddddr syscall-sym-list))
;;               :close)
;;        (equal (car (cadr (cddddr syscall-sym-list)))
;;               :set-path)
;;        (equal (caddr (cddddr syscall-sym-list))
;;               :open)
;;        (equal (cadddr (cddddr syscall-sym-list))
;;               :pwrite)
;;        (equal (car (cddddr (cddddr syscall-sym-list)))
;;               :close)
;;        (not (consp (cdr (cddddr (cddddr syscall-sym-list)))))
;;        (equal
;;         (1st-complete-under-path (frame->frame frame)
;;                                  (dirname (cdr (cadr (cddddr syscall-sym-list)))))
;;         0)
;;        (abs-complete
;;         (put-assoc-equal
;;          (basename (cdr (cadr (cddddr syscall-sym-list))))
;;          (m1-file '(0 0 0 0 0 0 0 0 0 0 0 0
;;                       0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;                   (implode$inline (insert-text nil (fat-st->offset$inline st)
;;                                                "")))
;;          (mv-nth
;;           0
;;           (abs-alloc
;;            (frame-val->dir$inline
;;             (cdr
;;              (assoc-equal (abs-find-file-src
;;                            frame
;;                            (dirname (cdr (cadr (cddddr syscall-sym-list)))))
;;                           frame)))
;;            (nthcdr
;;             (len
;;              (frame-val->path$inline
;;               (cdr (assoc-equal
;;                     (abs-find-file-src
;;                      frame
;;                      (dirname (cdr (cadr (cddddr syscall-sym-list)))))
;;                     frame))))
;;             (dirname (cdr (cadr (cddddr syscall-sym-list)))))
;;            t))))
;;        (consp syscall-sym-list)
;;        (consp (cdr syscall-sym-list))
;;        (consp (cddr syscall-sym-list))
;;        (consp (cdddr syscall-sym-list))
;;        (consp (cddddr syscall-sym-list))
;;        (consp (cdr (cddddr syscall-sym-list)))
;;        (consp (cddr (cddddr syscall-sym-list)))
;;        (consp (cdddr (cddddr syscall-sym-list)))
;;        (consp (cddddr (cddddr syscall-sym-list)))
;;        (consp (car syscall-sym-list))
;;        (consp (caddr syscall-sym-list))
;;        (not (integerp (cdr (caddr syscall-sym-list))))
;;        (consp (cadr (cddddr syscall-sym-list))))
;;       (equal
;;        (abs-find-file-src
;;         (mv-nth
;;          0
;;          (abs-pwrit1
;;           (mv-nth
;;            2
;;            (abs-open
;;             (cdr (cadr (cddddr syscall-sym-list)))
;;             (mv-nth 0
;;                     (abs-close (mv-nth 2
;;                                        (abs-open (cdr (car syscall-sym-list))
;;                                                  (fat-st->fd-table st)
;;                                                  (fat-st->file-table st)))
;;                                (mv-nth 0
;;                                        (abs-open (cdr (car syscall-sym-list))
;;                                                  (fat-st->fd-table st)
;;                                                  (fat-st->file-table st)))
;;                                (mv-nth 1
;;                                        (abs-open (cdr (car syscall-sym-list))
;;                                                  (fat-st->fd-table st)
;;                                                  (fat-st->file-table st)))))
;;             (mv-nth 1
;;                     (abs-close (mv-nth 2
;;                                        (abs-open (cdr (car syscall-sym-list))
;;                                                  (fat-st->fd-table st)
;;                                                  (fat-st->file-table st)))
;;                                (mv-nth 0
;;                                        (abs-open (cdr (car syscall-sym-list))
;;                                                  (fat-st->fd-table st)
;;                                                  (fat-st->file-table st)))
;;                                (mv-nth 1
;;                                        (abs-open (cdr (car syscall-sym-list))
;;                                                  (fat-st->fd-table st)
;;                                                  (fat-st->file-table st)))))))
;;           (mv-nth 0
;;                   (abs-pread (mv-nth 2
;;                                      (abs-open (cdr (car syscall-sym-list))
;;                                                (fat-st->fd-table st)
;;                                                (fat-st->file-table st)))
;;                              0 (fat-st->offset st)
;;                              frame
;;                              (mv-nth 0
;;                                      (abs-open (cdr (car syscall-sym-list))
;;                                                (fat-st->fd-table st)
;;                                                (fat-st->file-table st)))
;;                              (mv-nth 1
;;                                      (abs-open (cdr (car syscall-sym-list))
;;                                                (fat-st->fd-table st)
;;                                                (fat-st->file-table st)))))
;;           (fat-st->offset st)
;;           frame
;;           (mv-nth
;;            0
;;            (abs-open
;;             (cdr (cadr (cddddr syscall-sym-list)))
;;             (mv-nth 0
;;                     (abs-close (mv-nth 2
;;                                        (abs-open (cdr (car syscall-sym-list))
;;                                                  (fat-st->fd-table st)
;;                                                  (fat-st->file-table st)))
;;                                (mv-nth 0
;;                                        (abs-open (cdr (car syscall-sym-list))
;;                                                  (fat-st->fd-table st)
;;                                                  (fat-st->file-table st)))
;;                                (mv-nth 1
;;                                        (abs-open (cdr (car syscall-sym-list))
;;                                                  (fat-st->fd-table st)
;;                                                  (fat-st->file-table st)))))
;;             (mv-nth 1
;;                     (abs-close (mv-nth 2
;;                                        (abs-open (cdr (car syscall-sym-list))
;;                                                  (fat-st->fd-table st)
;;                                                  (fat-st->file-table st)))
;;                                (mv-nth 0
;;                                        (abs-open (cdr (car syscall-sym-list))
;;                                                  (fat-st->fd-table st)
;;                                                  (fat-st->file-table st)))
;;                                (mv-nth 1
;;                                        (abs-open (cdr (car syscall-sym-list))
;;                                                  (fat-st->fd-table st)
;;                                                  (fat-st->file-table st)))))))
;;           (mv-nth
;;            1
;;            (abs-open
;;             (cdr (cadr (cddddr syscall-sym-list)))
;;             (mv-nth 0
;;                     (abs-close (mv-nth 2
;;                                        (abs-open (cdr (car syscall-sym-list))
;;                                                  (fat-st->fd-table st)
;;                                                  (fat-st->file-table st)))
;;                                (mv-nth 0
;;                                        (abs-open (cdr (car syscall-sym-list))
;;                                                  (fat-st->fd-table st)
;;                                                  (fat-st->file-table st)))
;;                                (mv-nth 1
;;                                        (abs-open (cdr (car syscall-sym-list))
;;                                                  (fat-st->fd-table st)
;;                                                  (fat-st->file-table st)))))
;;             (mv-nth 1
;;                     (abs-close (mv-nth 2
;;                                        (abs-open (cdr (car syscall-sym-list))
;;                                                  (fat-st->fd-table st)
;;                                                  (fat-st->file-table st)))
;;                                (mv-nth 0
;;                                        (abs-open (cdr (car syscall-sym-list))
;;                                                  (fat-st->fd-table st)
;;                                                  (fat-st->file-table st)))
;;                                (mv-nth 1
;;                                        (abs-open (cdr (car syscall-sym-list))
;;                                                  (fat-st->fd-table st)
;;                                                  (fat-st->file-table st)))))))))
;;         src)
;;        (abs-find-file-src frame src)))
;;      :hints (("Goal" :do-not-induct t
;;               :in-theory (enable abs-open abs-close abs-pread hifat-open
;;                                  hifat-close))))

;;     (thm
;;      (implies
;;       (and (not (consp (cdr (car queues))))
;;            (equal (car (car (car queues)))
;;                   :transaction)
;;            (equal (car (car syscall-sym-list))
;;                   :set-path)
;;            (equal (cadr syscall-sym-list) :open)
;;            (equal (car (caddr syscall-sym-list))
;;                   :set-count)
;;            (equal (cadddr syscall-sym-list) :pread)
;;            (equal (car (cddddr syscall-sym-list))
;;                   :close)
;;            (equal (car (cadr (cddddr syscall-sym-list)))
;;                   :set-path)
;;            (equal (caddr (cddddr syscall-sym-list))
;;                   :open)
;;            (equal (cadddr (cddddr syscall-sym-list))
;;                   :pwrite)
;;            (equal (car (cddddr (cddddr syscall-sym-list)))
;;                   :close)
;;            (not (consp (cdr (cddddr (cddddr syscall-sym-list)))))
;;            (fat32-filename-list-equiv
;;             dst
;;             (dirname (cdr (cadr (cddddr syscall-sym-list)))))
;;            (equal (1st-complete-under-path (frame->frame frame)
;;                                            dst)
;;                   0)
;;            (abs-complete
;;             (mv-nth
;;              0
;;              (abs-alloc
;;               (frame-val->dir$inline
;;                (cdr (assoc-equal (abs-find-file-src frame
;;                                                     dst)
;;                                  frame)))
;;               (nthcdr
;;                (len
;;                 (frame-val->path$inline
;;                  (cdr (assoc-equal (abs-find-file-src frame
;;                                                       dst)
;;                                    frame))))
;;                path)
;;               t)))
;;            (consp syscall-sym-list)
;;            (consp (cdr syscall-sym-list))
;;            (consp (cddr syscall-sym-list))
;;            (consp (cdddr syscall-sym-list))
;;            (consp (cddddr syscall-sym-list))
;;            (consp (cdr (cddddr syscall-sym-list)))
;;            (consp (cddr (cddddr syscall-sym-list)))
;;            (consp (cdddr (cddddr syscall-sym-list)))
;;            (consp (cddddr (cddddr syscall-sym-list))))
;;       (equal
;;        (abs-find-file-src
;;         (mv-nth
;;          0
;;          (absfat-oracle-single-step
;;           (mv-nth
;;            0
;;            (absfat-oracle-single-step
;;             (mv-nth
;;              0
;;              (absfat-oracle-single-step
;;               (mv-nth
;;                0
;;                (absfat-oracle-single-step
;;                 (mv-nth
;;                  0
;;                  (absfat-oracle-single-step
;;                   (mv-nth
;;                    0
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))
;;                   :close
;;                   (mv-nth
;;                    1
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))))
;;                 (cadr (cddddr syscall-sym-list))
;;                 (mv-nth
;;                  1
;;                  (absfat-oracle-single-step
;;                   (mv-nth
;;                    0
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))
;;                   :close
;;                   (mv-nth
;;                    1
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))))))
;;               :open
;;               (mv-nth
;;                1
;;                (absfat-oracle-single-step
;;                 (mv-nth
;;                  0
;;                  (absfat-oracle-single-step
;;                   (mv-nth
;;                    0
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))
;;                   :close
;;                   (mv-nth
;;                    1
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))))
;;                 (cadr (cddddr syscall-sym-list))
;;                 (mv-nth
;;                  1
;;                  (absfat-oracle-single-step
;;                   (mv-nth
;;                    0
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))
;;                   :close
;;                   (mv-nth
;;                    1
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))))))))
;;             :pwrite
;;             (mv-nth
;;              1
;;              (absfat-oracle-single-step
;;               (mv-nth
;;                0
;;                (absfat-oracle-single-step
;;                 (mv-nth
;;                  0
;;                  (absfat-oracle-single-step
;;                   (mv-nth
;;                    0
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))
;;                   :close
;;                   (mv-nth
;;                    1
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))))
;;                 (cadr (cddddr syscall-sym-list))
;;                 (mv-nth
;;                  1
;;                  (absfat-oracle-single-step
;;                   (mv-nth
;;                    0
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))
;;                   :close
;;                   (mv-nth
;;                    1
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))))))
;;               :open
;;               (mv-nth
;;                1
;;                (absfat-oracle-single-step
;;                 (mv-nth
;;                  0
;;                  (absfat-oracle-single-step
;;                   (mv-nth
;;                    0
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))
;;                   :close
;;                   (mv-nth
;;                    1
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))))
;;                 (cadr (cddddr syscall-sym-list))
;;                 (mv-nth
;;                  1
;;                  (absfat-oracle-single-step
;;                   (mv-nth
;;                    0
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))
;;                   :close
;;                   (mv-nth
;;                    1
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))))))))))
;;           :close
;;           (mv-nth
;;            1
;;            (absfat-oracle-single-step
;;             (mv-nth
;;              0
;;              (absfat-oracle-single-step
;;               (mv-nth
;;                0
;;                (absfat-oracle-single-step
;;                 (mv-nth
;;                  0
;;                  (absfat-oracle-single-step
;;                   (mv-nth
;;                    0
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))
;;                   :close
;;                   (mv-nth
;;                    1
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))))
;;                 (cadr (cddddr syscall-sym-list))
;;                 (mv-nth
;;                  1
;;                  (absfat-oracle-single-step
;;                   (mv-nth
;;                    0
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))
;;                   :close
;;                   (mv-nth
;;                    1
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))))))
;;               :open
;;               (mv-nth
;;                1
;;                (absfat-oracle-single-step
;;                 (mv-nth
;;                  0
;;                  (absfat-oracle-single-step
;;                   (mv-nth
;;                    0
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))
;;                   :close
;;                   (mv-nth
;;                    1
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))))
;;                 (cadr (cddddr syscall-sym-list))
;;                 (mv-nth
;;                  1
;;                  (absfat-oracle-single-step
;;                   (mv-nth
;;                    0
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))
;;                   :close
;;                   (mv-nth
;;                    1
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))))))))
;;             :pwrite
;;             (mv-nth
;;              1
;;              (absfat-oracle-single-step
;;               (mv-nth
;;                0
;;                (absfat-oracle-single-step
;;                 (mv-nth
;;                  0
;;                  (absfat-oracle-single-step
;;                   (mv-nth
;;                    0
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))
;;                   :close
;;                   (mv-nth
;;                    1
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))))
;;                 (cadr (cddddr syscall-sym-list))
;;                 (mv-nth
;;                  1
;;                  (absfat-oracle-single-step
;;                   (mv-nth
;;                    0
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))
;;                   :close
;;                   (mv-nth
;;                    1
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))))))
;;               :open
;;               (mv-nth
;;                1
;;                (absfat-oracle-single-step
;;                 (mv-nth
;;                  0
;;                  (absfat-oracle-single-step
;;                   (mv-nth
;;                    0
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))
;;                   :close
;;                   (mv-nth
;;                    1
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))))
;;                 (cadr (cddddr syscall-sym-list))
;;                 (mv-nth
;;                  1
;;                  (absfat-oracle-single-step
;;                   (mv-nth
;;                    0
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))
;;                   :close
;;                   (mv-nth
;;                    1
;;                    (absfat-oracle-single-step
;;                     (mv-nth
;;                      0
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))
;;                     :pread
;;                     (mv-nth
;;                      1
;;                      (absfat-oracle-single-step
;;                       (mv-nth
;;                        0
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))
;;                       (caddr syscall-sym-list)
;;                       (mv-nth
;;                        1
;;                        (absfat-oracle-single-step
;;                         (mv-nth
;;                          0
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))
;;                         :open
;;                         (mv-nth
;;                          1
;;                          (absfat-oracle-single-step frame (car syscall-sym-list)
;;                                                     st))))))))))))))))))
;;         src)
;;        (abs-find-file-src frame src)))
;;      :hints (("Goal" :do-not-induct t))))

;;   (thm
;;    (implies
;;     (and (not (consp (cdr (car queues))))
;;          (equal (car (car (car queues)))
;;                 :transaction)
;;          (equal (car (car syscall-sym-list))
;;                 :set-path)
;;          (equal (cadr syscall-sym-list) :open)
;;          (equal (car (caddr syscall-sym-list))
;;                 :set-count)
;;          (equal (cadddr syscall-sym-list) :pread)
;;          (equal (car (cddddr syscall-sym-list))
;;                 :close)
;;          (equal (car (cadr (cddddr syscall-sym-list)))
;;                 :set-path)
;;          (equal (caddr (cddddr syscall-sym-list))
;;                 :open)
;;          (equal (cadddr (cddddr syscall-sym-list))
;;                 :pwrite)
;;          (equal (car (cddddr (cddddr syscall-sym-list)))
;;                 :close)
;;          (not (consp (cdr (cddddr (cddddr syscall-sym-list)))))
;;          (fat32-filename-list-equiv
;;           dst
;;           (dirname (cdr (cadr (cddddr syscall-sym-list)))))
;;          (equal (1st-complete-under-path (frame->frame frame)
;;                                          dst)
;;                 0)
;;          (abs-complete
;;           (mv-nth
;;            0
;;            (abs-alloc
;;             (frame-val->dir$inline
;;              (cdr (assoc-equal (abs-find-file-src frame
;;                                                   dst)
;;                                frame)))
;;             (nthcdr
;;              (len
;;               (frame-val->path$inline
;;                (cdr (assoc-equal (abs-find-file-src frame dst)
;;                                  frame))))
;;              path)
;;             t))))
;;     (equal (abs-find-file-src
;;             (mv-nth 0
;;                     (absfat-oracle-multi-step frame syscall-sym-list st))
;;             src)
;;            (abs-find-file-src frame src)))
;;    :hints
;;    (("goal"
;;      :expand
;;      ((:free
;;        (frame syscall-sym-list st)
;;        (absfat-oracle-multi-step frame syscall-sym-list st)))))))

;; (thm
;;  (implies
;;   (and
;;    (cp-spec-3 queues dst)
;;    (consp (nth n queues))
;;    (equal
;;     (1st-complete-under-path
;;      (frame->frame frame)
;;      dst)
;;     0)
;;    (abs-complete
;;     (mv-nth
;;      0
;;      (abs-alloc
;;       (frame-val->dir$inline
;;        (cdr (assoc-equal (abs-find-file-src frame
;;                                             dst)
;;                          frame)))
;;       (nthcdr
;;        (len
;;         (frame-val->path$inline
;;          (cdr (assoc-equal (abs-find-file-src frame dst)
;;                            frame))))
;;        path)
;;       t))))
;;   (equal
;;    (abs-find-file-src
;;     (mv-nth
;;      0
;;      (absfat-oracle-multi-step frame
;;                                (cdr (car (nth n queues)))
;;                                st))
;;     src)
;;    (abs-find-file-src frame src)))
;;  :hints (("Goal" :in-theory (enable nth cp-spec-3))))

;; (encapsulate
;;   ()

;;   (local
;;    (defun-nx induction-scheme
;;      (dst frame fs o1 queues src st)
;;      (declare (xargs :verify-guards nil
;;                      :measure (len (flatten queues))))
;;      (cond
;;       ((and
;;         (not (atom (flatten queues)))
;;         (consp (car (nth (nth (min (nfix (car o1))
;;                                    (+ -1 (len (nonempty-queues queues))))
;;                               (nonempty-queues queues))
;;                          queues)))
;;         (equal (car (car (nth (nth (min (nfix (car o1))
;;                                         (+ -1 (len (nonempty-queues queues))))
;;                                    (nonempty-queues queues))
;;                               queues)))
;;                :transaction))
;;        (induction-scheme
;;         dst
;;         (mv-nth 0
;;                 (absfat-oracle-multi-step
;;                      frame
;;                      (cdr (car (nth (nth (min (nfix (car o1))
;;                                               (+ -1 (len (nonempty-queues queues))))
;;                                          (nonempty-queues queues))
;;                                     queues)))
;;                      st))
;;         fs (cdr o1)
;;         (update-nth (nth (min (nfix (car o1))
;;                               (+ -1 (len (nonempty-queues queues))))
;;                          (nonempty-queues queues))
;;                     (cdr (nth (nth (min (nfix (car o1))
;;                                         (+ -1 (len (nonempty-queues queues))))
;;                                    (nonempty-queues queues))
;;                               queues))
;;                     queues)
;;         src
;;         (mv-nth 1
;;                 (absfat-oracle-multi-step
;;                  frame
;;                  (cdr (car (nth
;;                             (nth (min (nfix (car o1))
;;                                         (+ -1 (len (nonempty-queues queues))))
;;                                    (nonempty-queues queues))
;;                                 queues)))
;;                  st))))
;;       (t
;;        (mv dst frame fs o1 queues src st)))))

;;   (thm
;;    (implies
;;     (and
;;      (cp-spec-3 queues dst))
;;     (b*
;;         ((frame1
;;           (mv-nth
;;            0
;;            (absfat-oracle-multi-step
;;             frame
;;             (mv-nth 0
;;                     (schedule-queues
;;                      queues
;;                      o1))
;;             st)))
;;          (frame2
;;           (mv-nth
;;            0
;;            (absfat-oracle-multi-step
;;             frame
;;             (mv-nth 0
;;                     (schedule-queues
;;                      queues
;;                      o2))
;;             st))))
;;       (implies
;;        (absfat-subsetp
;;         (cdr
;;          (assoc-equal
;;           (abs-find-file-src frame2 src)
;;           frame2))
;;         fs)
;;        (and
;;         (equal
;;          (abs-find-file-src frame1 src)
;;          (abs-find-file-src frame src))
;;         (equal
;;          (remove-assoc-equal (abs-find-file-src frame1 src)
;;                              frame1)
;;          (remove-assoc-equal (abs-find-file-src frame src)
;;                              frame))
;;         (absfat-subsetp
;;          (cdr (assoc-equal (abs-find-file-src frame1 src)
;;                            frame1))
;;          fs)))))
;;    :hints (("goal" :induct
;;             (induction-scheme
;;              dst frame fs o1 queues src st)
;;             :in-theory (enable schedule-queues cp-spec-3 absfat-oracle-multi-step
;;                                absfat-oracle-single-step)
;;             :expand
;;             ((:with
;;               (:rewrite member-of-nonempty-queues . 1)
;;               (consp (nth (nth (+ -1 (len (nonempty-queues queues)))
;;                                (nonempty-queues queues))
;;                           queues)))
;;              (cp-spec-1 frame nil st src fs)
;;              (schedule-queues
;;               queues
;;               o1))))))

;; (defthm cp-without-subdirs-helper-correctness-2
;;   (implies
;;    (true-equiv o1 o2)
;;    (collapse-equiv
;;     (mv-nth
;;      0
;;      (absfat-oracle-multi-step
;;       frame
;;       (mv-nth 0
;;               (schedule-queues
;;                (cp-without-subdirs-helper src dst names)
;;                o1))
;;       st))
;;     (mv-nth
;;      0
;;      (absfat-oracle-multi-step
;;       frame
;;       (mv-nth 0
;;               (schedule-queues
;;                (cp-without-subdirs-helper src dst names)
;;                o2))
;;       st))))
;;   :hints (("Goal" :in-theory (enable schedule-queues absfat-oracle-multi-step
;;                                      cp-without-subdirs-helper
;;                                      absfat-oracle-single-step)
;;            :induct
;;            (cp-without-subdirs-helper src dst names)
;;            :expand
;;            ((schedule-queues
;;              (cons (list (list* :transaction
;;                                 (cons :set-path (append src (car names)))
;;                                 :open '(:set-count . 4294967296)
;;                                 :pread :close
;;                                 (cons :set-path (append dst (car names)))
;;                                 '(:open :pwrite :close)))
;;                    (cp-without-subdirs-helper src dst (cdr names)))
;;              o1)
;;             (schedule-queues
;;              (cons (list (list* :transaction
;;                                 (cons :set-path (append src (car names)))
;;                                 :open '(:set-count . 4294967296)
;;                                 :pread :close
;;                                 (cons :set-path (append dst (car names)))
;;                                 '(:open :pwrite :close)))
;;                    (cp-without-subdirs-helper src dst (cdr names)))
;;              o2))))
;;   :rule-classes :congruence)
