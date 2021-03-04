(in-package "ACL2")

;  oracle.lisp                                         Mihir Mehta

(include-book "lofat-syscalls")
(include-book "abs-syscalls")

(local (in-theory (disable nth make-list-ac-removal last
                           make-list-ac)))

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
            (change-fat-st st :path (cdr syscall-sym)))))
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
              (abs-pwrite
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
              (lofat-close
               (fat-st->fd st)
               (fat-st->fd-table st)
               (fat-st->file-table st))))
          (mv frame
              (change-fat-st
               st :fd-table fd-table :file-table file-table :errno errno))))
       ((when (and (consp syscall-sym) (eq (car syscall-sym) :set-path)))
        (mv frame
            (change-fat-st st :path (cdr syscall-sym)))))
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
                                               lofat-opendir-correctness-3)
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
   (:type-prescription
    :corollary (implies (member-equal (nfix x)
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
        (schedule-queues queues oracle)))
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
