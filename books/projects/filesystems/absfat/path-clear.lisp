;  path-clear.lisp                                      Mihir Mehta

(in-package "ACL2")

(include-book "partial-collapse")
(include-book "abs-find-file-src")
(local (include-book "std/lists/prefixp" :dir :system))

(defund
  path-clear (path frame)
  (declare (xargs :guard (and (fat32-filename-list-p path)
                              (frame-p frame))
                  :guard-debug t))
  (b*
      (((when (atom frame)) t)
       ((unless
            (path-clear path (cdr frame)))
        nil)
       (path (mbe :exec path :logic (fat32-filename-list-fix
                                             path))))
    (and
     (or
      (not (prefixp
            path
            (frame-val->path (cdar frame))))
      (equal
       (frame-val->path (cdar frame))
       path))
     (or
      (not (prefixp
            (frame-val->path (cdar frame))
            path))
      (atom
       (names-at (frame-val->dir (cdar frame))
                 (nthcdr
                  (len (frame-val->path (cdar frame)))
                  path)))))))

(defthm
  path-clear-of-frame-with-root
  (iff (path-clear path (frame-with-root root frame))
       (and (path-clear path frame)
            (not (consp (names-at root path)))))
  :hints (("goal" :in-theory (enable path-clear frame-with-root names-at)
           :do-not-induct t))
  :otf-flg t)

(defthm
  dist-names-when-path-clear
  (implies (path-clear path frame)
           (dist-names dir path frame))
  :hints (("goal" :in-theory (enable dist-names
                                     path-clear prefixp)
           :induct (path-clear path frame)
           :expand (dist-names dir path frame))))

(defthm path-clear-of-remove-assoc
  (implies
   (path-clear path frame)
   (path-clear path (remove-assoc-equal x frame)))
  :hints (("goal" :in-theory (enable path-clear))))

(defthm
  1st-complete-under-path-when-path-clear-of-prefix
  (implies (and (path-clear path1 frame)
                (fat32-filename-list-prefixp path1 path2)
                (not (fat32-filename-list-equiv path1 path2)))
           (equal (1st-complete-under-path frame path2)
                  0))
  :hints
  (("goal" :in-theory (e/d (frame-p path-clear
                                    1st-complete-under-path names-at
                                    fat32-filename-list-prefixp-alt list-equiv)
                           (prefixp-when-equal-lengths len-when-prefixp)))))

;; I suspect this might be useful later.
(defthm partial-collapse-when-path-clear-of-prefix
  (implies (and (path-clear path1 (frame->frame frame))
                (fat32-filename-list-prefixp path1 path2)
                (not (fat32-filename-list-equiv path1 path2)))
           (equal (partial-collapse frame path2)
                  frame))
  :hints (("goal" :in-theory (enable partial-collapse))))

(defthmd path-clear-of-fat32-filename-list-fix
  (equal (path-clear (fat32-filename-list-fix path)
                     frame)
         (path-clear path frame))
  :hints (("goal" :in-theory (enable path-clear))))

(defcong fat32-filename-list-equiv equal (path-clear path frame) 1
  :hints (("Goal"
           :use
           (path-clear-of-fat32-filename-list-fix
            (:instance
             path-clear-of-fat32-filename-list-fix
             (path path-equiv))))))

(defthm path-clear-of-frame->frame
  (implies (path-clear path frame)
           (path-clear path (frame->frame frame)))
  :hints (("goal" :in-theory (enable frame->frame))))

(defthmd path-clear-of-true-list-fix
  (equal (path-clear path (true-list-fix frame))
         (path-clear path frame))
  :hints (("Goal" :in-theory (enable path-clear true-list-fix))))

(defcong
  list-equiv equal (path-clear path frame)
  2
  :hints
  (("goal" :use (path-clear-of-true-list-fix
                 (:instance path-clear-of-true-list-fix
                            (frame frame-equiv))))))

(local
 (defund
   path-clear-alt (path frame indices)
   (declare (xargs :guard (and (fat32-filename-list-p path)
                               (frame-p frame))
                   :guard-debug t))
   (b*
       (((when (atom indices)) t)
        ((unless (path-clear-alt path frame (cdr indices)))
         nil)
        (path (mbe :exec path
                   :logic (fat32-filename-list-fix path)))
        (alist-elem (assoc-equal (car indices) frame)))
     (or
      (atom alist-elem)
      (and
       (or (not (prefixp path
                         (frame-val->path (cdr alist-elem))))
           (equal (frame-val->path (cdr alist-elem))
                  path))
       (or
        (not (prefixp (frame-val->path (cdr alist-elem))
                      path))
        (atom
         (names-at
          (frame-val->dir (cdr alist-elem))
          (nthcdr (len (frame-val->path (cdr alist-elem)))
                  path)))))))))

(local
 (defthm path-clear-alt-of-remove-of-strip-cars-lemma-1
   (implies (and (subsetp-equal indices (strip-cars (cdr frame)))
                 (no-duplicatesp-equal (strip-cars frame)))
            (equal (path-clear-alt path (cdr frame)
                                   indices)
                   (path-clear-alt path frame indices)))
   :hints (("goal" :in-theory (enable path-clear-alt)))))

(local
 (defthmd path-clear-alt-of-remove-of-strip-cars
   (implies (and (frame-p frame)
                 (no-duplicatesp-equal (strip-cars frame)))
            (equal (path-clear-alt path frame
                                   (remove-equal x (strip-cars frame)))
                   (path-clear path (remove-assoc-equal x frame))))
   :hints (("goal" :in-theory (enable path-clear path-clear-alt)))))

(local
 (defthmd path-clear-alt-of-strip-cars
   (implies (and (frame-p frame)
                 (no-duplicatesp-equal (strip-cars frame)))
            (equal (path-clear-alt path frame (strip-cars frame))
                   (path-clear path frame)))
   :hints (("goal" :in-theory (enable path-clear path-clear-alt)))))

(defthm
  path-clear-partial-collapse-when-zp-src-lemma-2
  (implies
   (not (consp (assoc-equal x (frame->frame frame))))
   (not
    (consp (assoc-equal x
                        (frame->frame (partial-collapse frame path))))))
  :hints (("goal" :in-theory (enable partial-collapse))))

(defthm
  path-clear-partial-collapse-when-zp-src-lemma-3
  (implies
   (consp (assoc-equal x
                       (frame->frame (partial-collapse frame path))))
   (and
    (equal
     (frame-val->src
      (cdr (assoc-equal x
                        (frame->frame (partial-collapse frame path)))))
     (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
    (equal
     (frame-val->path
      (cdr (assoc-equal x
                        (frame->frame (partial-collapse frame path)))))
     (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
  :hints (("goal" :in-theory (enable partial-collapse))))

(local
 (defthm path-clear-partial-collapse-when-zp-src-lemma-4
   (implies
    (and (fat32-filename-list-prefixp
          path
          (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
         (mv-nth 1 (collapse frame))
         (no-duplicatesp-equal (strip-cars (frame->frame frame)))
         (consp (assoc-equal x (frame->frame frame)))
         (frame-p frame)
         (abs-separate frame)
         (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
         (subsetp-equal (abs-addrs (frame->root frame))
                        (frame-addrs-root (frame->frame frame))))
    (member-equal x (seq-this-under-path frame path)))
   :hints
   (("goal"
     :do-not-induct t
     :in-theory
     (disable 1st-complete-under-path-of-frame->frame-of-partial-collapse)
     :use
     ((:instance
       1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-54
       (seq (seq-this-under-path frame path)))
      collapse-seq-of-seq-this-under-path-is-partial-collapse
      1st-complete-under-path-of-frame->frame-of-partial-collapse)))))

;; In some circumstances, this is more general than
;; valid-seqp-after-collapse-this-lemma-7.
(defthm
  path-clear-partial-collapse-when-zp-src-lemma-5
  (implies (and (frame-p frame)
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (valid-seqp frame seq))
           (iff (consp (assoc-equal x
                                    (frame->frame (collapse-seq frame seq))))
                (and (not (member-equal x seq))
                     (consp (assoc-equal x (frame->frame frame))))))
  :hints
  (("goal"
    :in-theory (enable valid-seqp collapse-seq)
    :expand
    (:with
     (:rewrite
      1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-69)
     (mv-nth 1
             (collapse (collapse-this frame (car seq))))))))

(defthm
  path-clear-partial-collapse-when-zp-src-lemma-17
  (implies
   (and (frame-p frame)
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (valid-seqp frame (seq-this-under-path frame path))
        (abs-separate frame)
        (atom (frame-val->path (cdr (assoc-equal 0 frame)))))
   (iff (consp (assoc-equal x
                            (frame->frame (partial-collapse frame path))))
        (and (not (member-equal x (seq-this-under-path frame path)))
             (consp (assoc-equal x (frame->frame frame))))))
  :hints
  (("goal" :do-not-induct t
    :in-theory (disable path-clear-partial-collapse-when-zp-src-lemma-5)
    :use ((:instance path-clear-partial-collapse-when-zp-src-lemma-5
                     (seq (seq-this-under-path frame path)))
          collapse-seq-of-seq-this-under-path-is-partial-collapse))))

(defthmd path-clear-partial-collapse-when-zp-src-lemma-6
  (implies
   (and
    (not (prefixp (fat32-filename-list-fix path)
                  (frame-val->path (cdr (assoc-equal (car indices)
                                                     (frame->frame frame))))))
    (prefixp (frame-val->path (cdr (assoc-equal (car indices)
                                                (frame->frame frame))))
             (fat32-filename-list-fix path)))
   (<
    (len (frame-val->path$inline (cdr (assoc-equal (car indices)
                                                   (frame->frame frame)))))
    (len path)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable (:rewrite len-when-prefixp)
                        (:rewrite prefixp-when-equal-lengths))
    :use
    ((:instance
      (:rewrite len-when-prefixp)
      (y (fat32-filename-list-fix path))
      (x (frame-val->path (cdr (assoc-equal (car indices)
                                            (frame->frame frame))))))
     (:instance (:rewrite prefixp-when-equal-lengths)
                (y (frame-val->path (cdr (assoc-equal (car indices)
                                                      (frame->frame frame)))))
                (x (fat32-filename-list-fix path)))
     (:instance (:rewrite prefixp-when-equal-lengths)
                (x (frame-val->path (cdr (assoc-equal (car indices)
                                                      (frame->frame frame)))))
                (y (fat32-filename-list-fix path))))))
  :rule-classes :linear)

(defthmd
  path-clear-partial-collapse-when-zp-src-lemma-7
  (implies (and (consp (assoc-equal 0 frame))
                (not (consp (assoc-equal x frame))))
           (not (consp (assoc-equal x (partial-collapse frame path)))))
  :hints (("goal" :in-theory (enable partial-collapse collapse-this
                                     assoc-equal-of-frame-with-root
                                     assoc-of-frame->frame)
           :induct (partial-collapse frame path))))

(defthm
  path-clear-partial-collapse-when-zp-src-lemma-8
  (implies
   (and (equal (frame-val->path (cdr (assoc-equal 0 frame)))
               nil)
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0))
   (and
    (equal
     (frame-val->path (cdr (assoc-equal x (partial-collapse frame path))))
     (if (consp (assoc-equal x (partial-collapse frame path)))
         (frame-val->path (cdr (assoc-equal x frame)))
       nil))
    (equal
     (frame-val->src (cdr (assoc-equal x (partial-collapse frame path))))
     (if (consp (assoc-equal x (partial-collapse frame path)))
         (frame-val->src (cdr (assoc-equal x frame)))
       0))))
  :hints (("goal" :in-theory
           (e/d (partial-collapse collapse-this
                                  assoc-equal-of-frame-with-root
                                  assoc-of-frame->frame
                                  path-clear-partial-collapse-when-zp-src-lemma-7)
                ((:definition remove-assoc-equal)
                 (:rewrite remove-assoc-when-absent-1)
                 (:rewrite remove-assoc-of-put-assoc)
                 (:rewrite abs-fs-fix-when-abs-fs-p)
                 (:rewrite abs-fs-p-when-hifat-no-dups-p)
                 (:definition abs-complete)
                 (:rewrite remove-assoc-of-remove-assoc)
                 (:definition len)))
           :induct (partial-collapse frame path))))

;; Used in other files.
(defthm
  path-clear-partial-collapse-when-zp-src-lemma-9
  (implies
   (and (no-duplicatesp-equal (strip-cars frame))
        (atom (frame-val->path (cdr (assoc-equal 0 frame)))))
   (prefixp (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                               frame)))
            (fat32-filename-list-fix path)))
  :hints (("goal" :in-theory (enable abs-find-file abs-find-file-src
                                     fat32-filename-list-prefixp-alt)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (no-duplicatesp-equal (strip-cars frame))
          (atom (frame-val->path (cdr (assoc-equal 0 frame))))
          (fat32-filename-list-equiv
           (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                              frame)))
           (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                              other-frame))))
          (fat32-filename-list-prefixp path other-path))
     (fat32-filename-list-prefixp
      (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                         other-frame)))
      other-path))
    :hints (("goal" :in-theory (enable fat32-filename-list-prefixp-alt))))
   (:linear
    :corollary
    (implies
     (and (no-duplicatesp-equal (strip-cars frame))
          (atom (frame-val->path (cdr (assoc-equal 0 frame))))
          (fat32-filename-list-equiv
           (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                              frame)))
           (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                              other-frame)))))
     (<=
      (len (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                              other-frame))))
      (len path)))
    :hints (("goal" :in-theory (enable len-of-fat32-filename-list-fix))))))

(defthm
  path-clear-partial-collapse-when-zp-src-lemma-10
  (implies
   (abs-separate frame)
   (no-duplicatesp-equal
    (abs-addrs
     (abs-fs-fix
      (abs-file->contents$inline
       (mv-nth
        0
        (abs-find-file-helper
         (frame-val->dir$inline
          (cdr
           (assoc-equal
            (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
         (nthcdr
          (len
           (frame-val->path$inline
            (cdr (assoc-equal (frame-val->src$inline
                               (cdr (assoc-equal x (frame->frame frame))))
                              (frame->frame frame)))))
          path))))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (collapse abs-fs-fix abs-file-contents-p)
                    ((:rewrite abs-file-contents-p-of-abs-file->contents)))
    :use
    (:instance
     (:rewrite abs-file-contents-p-of-abs-file->contents)
     (x
      (mv-nth
       0
       (abs-find-file-helper
        (frame-val->dir
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
        (nthcdr
         (len
          (frame-val->path
           (cdr
            (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame)))))
         path))))))))

(defthm
  path-clear-partial-collapse-when-zp-src-lemma-11
  (implies
   (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs path)))
   (abs-no-dups-p
    (abs-file->contents (mv-nth 0 (abs-find-file-helper fs path)))))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm
  path-clear-partial-collapse-when-zp-src-lemma-12
  (implies
   (member-equal
    y
    (abs-addrs
     (abs-file->contents (mv-nth 0 (abs-find-file-helper fs path)))))
   (member-equal
    y
    (abs-addrs
     (abs-fs-fix
      (abs-file->contents (mv-nth 0 (abs-find-file-helper fs path)))))))
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d (abs-file-p-alt)
                    ((:rewrite abs-file-p-of-abs-find-file-helper)))
    :use abs-file-p-of-abs-find-file-helper)))

(defthmd
  path-clear-partial-collapse-when-zp-src-lemma-13
  (implies
   (and
    (prefixp (frame-val->path
              (cdr (assoc-equal x (frame->frame frame))))
             (fat32-filename-list-fix path))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-separate frame)
    (mv-nth 1 (collapse frame))
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (member-equal
     y
     (abs-addrs
      (abs-file->contents
       (mv-nth
        0
        (abs-find-file-helper
         (frame-val->dir
          (cdr (assoc-equal x (frame->frame frame))))
         (nthcdr
          (len (frame-val->path
                (cdr (assoc-equal x (frame->frame frame)))))
          path)))))))
   (prefixp (fat32-filename-list-fix path)
            (frame-val->path
             (cdr (assoc-equal y (frame->frame frame))))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (collapse abs-fs-fix)
     ((:definition fat32-filename-list-prefixp)
      (:rewrite
       abs-separate-of-frame->frame-of-collapse-this-lemma-8
       . 2)
      (:rewrite prefixp-when-equal-lengths)
      (:rewrite abs-addrs-of-remove-assoc-lemma-2)
      (:rewrite len-when-prefixp)
      (:rewrite abs-fs-p-when-hifat-no-dups-p)
      (:rewrite abs-file-alist-p-correctness-1)
      (:definition len)
      (:rewrite abs-find-file-correctness-lemma-16)
      (:rewrite abs-find-file-correctness-lemma-40)))
    :induct (collapse frame))
   ("subgoal *1/6"
    :use
    (:instance
     (:rewrite abs-find-file-helper-of-ctx-app-lemma-4)
     (path
      (nthcdr
       (len
        (frame-val->path
         (cdr
          (assoc-equal
           (frame-val->src
            (cdr
             (assoc-equal (1st-complete (frame->frame frame))
                          (frame->frame frame))))
           (frame->frame frame)))))
       path))
     (fs
      (frame-val->dir
       (cdr
        (assoc-equal
         (frame-val->src
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))
         (frame->frame frame)))))))))

(defthm path-clear-partial-collapse-when-zp-src-lemma-18
  (implies (atom path)
           (equal (abs-find-file-src frame path)
                  0))
  :hints (("goal" :in-theory (enable abs-find-file-src
                                     abs-find-file-helper))))

(defthm
  path-clear-partial-collapse-when-zp-src-lemma-19
  (implies (and (not (consp path)))
           (> (mv-nth 1
                      (hifat-find-file (mv-nth 0 (collapse frame))
                                       path))
              0))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable hifat-find-file))))

(local
 (defthm
   path-clear-partial-collapse-when-zp-src-lemma-20
   (implies
    (equal (abs-find-file (partial-collapse frame path)
                          path)
           (list '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                   (contents))
                 (mv-nth 1
                         (abs-find-file (partial-collapse frame path)
                                        path))))
    (not
     (consp
      (abs-addrs
       (abs-file->contents (mv-nth 0
                                   (abs-find-file (partial-collapse frame path)
                                                  path)))))))
   :hints
   (("goal"
     :do-not-induct t
     :in-theory (e/d (abs-complete assoc-of-frame->frame)
                     (path-clear-partial-collapse-when-zp-src-lemma-4
                      (:rewrite path-clear-partial-collapse-when-zp-src-lemma-9 . 1)))
     :expand
     (member-equal
      (car (abs-addrs (abs-file->contents
                       (mv-nth 0
                               (abs-find-file (partial-collapse frame path)
                                              path)))))
      (abs-addrs
       (abs-file->contents
        (mv-nth
         0
         (abs-find-file-helper
          (frame-val->dir
           (cdr (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                                path)
                             frame)))
          (nthcdr
           (len
            (frame-val->path
             (cdr (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                                  path)
                               frame))))
           path))))))))))

(defthm
  path-clear-partial-collapse-when-zp-src-lemma-21
  (implies
   (and (abs-separate (frame->frame frame))
        (frame-p (frame->frame frame))
        (mv-nth 1 (collapse frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (consp (assoc-equal x (frame->frame frame))))
   (subsetp-equal
    (abs-addrs (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
    (strip-cars (frame->frame frame))))
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d ()
                    ((:rewrite 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-3
                               . 1)))
    :use ((:instance (:rewrite 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-3
                               . 1)
                     (y (strip-cars (frame->frame frame)))
                     (n (collapse-1st-index frame x))
                     (x x)
                     (frame frame))
          1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-39)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (abs-separate (frame->frame frame))
          (frame-p (frame->frame frame))
          (mv-nth 1 (collapse frame))
          (no-duplicatesp-equal (strip-cars (frame->frame frame)))
          (consp (assoc-equal x (frame->frame frame)))
          (not (member-equal y
                             (strip-cars (frame->frame frame)))))
     (not
      (member-equal
       y
       (abs-addrs (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))))))

(defthm
  path-clear-partial-collapse-when-zp-src-lemma-22
  (implies
   (and (mv-nth 1 (collapse frame))
        (abs-separate (frame->frame frame))
        (frame-p (frame->frame frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (subsetp-equal
    (abs-addrs (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
    (strip-cars (frame->frame frame))))
  :hints
  (("goal"
    :in-theory (e/d (collapse abs-addrs-of-ctx-app-lemma-2)
                    ((:rewrite remove-assoc-of-put-assoc)
                     (:rewrite remove-assoc-of-remove-assoc)
                     (:rewrite abs-file-alist-p-when-m1-file-alist-p)))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (mv-nth 1 (collapse frame))
          (abs-separate (frame->frame frame))
          (frame-p (frame->frame frame))
          (no-duplicatesp-equal (strip-cars (frame->frame frame)))
          (subsetp-equal z
                         (abs-addrs (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
     (subsetp-equal z
                    (strip-cars (frame->frame frame)))))
   (:rewrite
    :corollary
    (implies
     (and
      (mv-nth 1 (collapse frame))
      (abs-separate (frame->frame frame))
      (frame-p (frame->frame frame))
      (no-duplicatesp-equal (strip-cars (frame->frame frame)))
      (member-equal
       y
       (abs-addrs
        (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
     (consp (assoc-equal y (frame->frame frame))))
    :hints
    (("goal"
      :in-theory (disable subsetp-member)
      :use
      (:instance
       subsetp-member
       (y (strip-cars (frame->frame frame)))
       (x
        (abs-addrs
         (frame-val->dir$inline (cdr (assoc-equal x (frame->frame frame))))))
       (a y)))))))

(defthm
  path-clear-partial-collapse-when-zp-src-lemma-23
  (subsetp-equal
   (abs-addrs (abs-file->contents (mv-nth 0 (abs-find-file-helper fs path))))
   (abs-addrs (abs-fs-fix fs)))
  :hints (("goal" :in-theory (enable abs-find-file-helper)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (abs-fs-p fs)
     (subsetp-equal
      (abs-addrs (abs-file->contents (mv-nth 0 (abs-find-file-helper fs path))))
      (abs-addrs fs))))
   (:rewrite
    :corollary
    (implies
     (atom (abs-addrs (abs-fs-fix fs)))
     (not
      (member-equal
       x
       (abs-addrs (abs-file->contents (mv-nth 0 (abs-find-file-helper fs path))))))))))

(defthmd path-clear-partial-collapse-when-zp-src-lemma-24
  (implies (and (< (nfix n) (len l))
                (subsetp-equal l (strip-cars (frame->frame frame)))
                (frame-p frame))
           (> (nth n l) 0))
  :hints (("goal" :in-theory (enable subsetp-equal)))
  :rule-classes :linear)

(defthm
  path-clear-partial-collapse-when-zp-src-lemma-25
  (implies
   (and
    (equal
     (abs-find-file-helper
      (frame-val->dir
       (cdr (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                            path)
                         (partial-collapse frame path))))
      (nthcdr
       (len
        (frame-val->path
         (cdr (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                              path)
                           frame))))
       path))
     (abs-find-file (partial-collapse frame path)
                    path))
    (consp
     (abs-addrs
      (abs-file->contents (mv-nth 0
                                  (abs-find-file (partial-collapse frame path)
                                                 path)))))
    (case-split
     (not (equal (abs-find-file-src (partial-collapse frame path)
                                    path)
                 0)))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-separate frame)
    (mv-nth 1 (collapse frame))
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (subsetp-equal (abs-addrs (frame->root frame))
                   (frame-addrs-root (frame->frame frame))))
   (>
    (nth
     0
     (abs-addrs
      (abs-file->contents (mv-nth 0
                                  (abs-find-file (partial-collapse frame path)
                                                 path)))))
    0))
  :instructions
  ((:in-theory (enable assoc-of-frame->frame len-when-consp))
   :promote (:dive 2 2 1 1 2)
   := :top (:dive 2)
   (:apply-linear path-clear-partial-collapse-when-zp-src-lemma-24
                  ((frame (partial-collapse frame path))))
   :top :bash :bash
   (:rewrite (:rewrite path-clear-partial-collapse-when-zp-src-lemma-22 . 1)
             ((x (abs-find-file-src (partial-collapse frame path)
                                    path))))
   :bash :bash :bash :bash
   (:= (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                       path)
                    (frame->frame (partial-collapse frame path)))
       (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                       path)
                    (partial-collapse frame path)))
   (:rewrite (:rewrite path-clear-partial-collapse-when-zp-src-lemma-23 . 2))
   :bash :bash)
  :rule-classes :linear)

(defthm
  path-clear-partial-collapse-when-zp-src-lemma-26
  (implies
   (abs-separate frame)
   (no-duplicatesp-equal
    (abs-addrs
     (abs-fs-fix
      (abs-file->contents$inline
       (mv-nth
        0
        (abs-find-file-helper
         (frame-val->dir$inline
          (cdr
           (assoc-equal
            (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
         path2)))))))
  :hints
  (("goal"
    :in-theory (e/d (abs-fs-fix abs-file-contents-p)
                    ((:rewrite no-duplicatesp-of-abs-addrs-of-abs-fs-fix)
                     (:rewrite abs-file-contents-p-of-abs-file->contents)))
    :use
    ((:instance
      (:rewrite no-duplicatesp-of-abs-addrs-of-abs-fs-fix)
      (x
       (abs-file->contents
        (mv-nth
         0
         (abs-find-file-helper
          (frame-val->dir
           (cdr
            (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame))))
          path2)))))
     (:instance
      (:rewrite abs-file-contents-p-of-abs-file->contents)
      (x
       (mv-nth
        0
        (abs-find-file-helper
         (frame-val->dir
          (cdr
           (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
         path2))))))))

(defthm
  path-clear-partial-collapse-when-zp-src-lemma-27
  (subsetp-equal
   (abs-addrs
    (abs-fs-fix
     (abs-file->contents (mv-nth 0 (abs-find-file-helper fs path)))))
   (abs-addrs (abs-file->contents (mv-nth 0 (abs-find-file-helper fs path)))))
  :hints
  (("goal"
    :in-theory
    (e/d (abs-fs-fix abs-file-contents-p)
         ((:rewrite abs-file-contents-p-of-abs-file->contents)
          (:rewrite no-duplicatesp-of-abs-addrs-of-abs-fs-fix-lemma-1
                    . 1)))
    :use
    ((:instance (:rewrite abs-file-contents-p-of-abs-file->contents)
                (x (mv-nth 0 (abs-find-file-helper fs path))))
     (:instance
      (:rewrite no-duplicatesp-of-abs-addrs-of-abs-fs-fix-lemma-1
                . 1)
      (abs-file-alist
       (abs-file->contents (mv-nth 0 (abs-find-file-helper fs path)))))))))

(defthm
  path-clear-partial-collapse-when-zp-src-lemma-28
  (implies
   (and (abs-separate frame)
        (atom (frame-val->path (cdr (assoc-equal 0 frame))))
        (frame-p frame)
        (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (subsetp-equal
    (abs-addrs
     (abs-file->contents
      (mv-nth
       0
       (abs-find-file-helper
        (frame-val->dir
         (cdr (assoc-equal x
                           (frame->frame (partial-collapse frame path1)))))
        path2))))
    (abs-addrs
     (abs-file->contents
      (mv-nth 0
              (abs-find-file-helper
               (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
               path2))))))
  :hints (("goal" :in-theory (enable partial-collapse)
           :induct (partial-collapse frame path1)
           :do-not-induct t)))

(defthm
  path-clear-partial-collapse-when-zp-src-lemma-29
  (implies
   (and
    (equal
     (abs-find-file-helper
      (frame-val->dir
       (cdr (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                            path)
                         (partial-collapse frame path))))
      (nthcdr
       (len
        (frame-val->path
         (cdr (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                              path)
                           frame))))
       path))
     (abs-find-file (partial-collapse frame path)
                    path))
    (not (equal (abs-find-file-src (partial-collapse frame path)
                                   path)
                0))
    (consp
     (abs-addrs
      (abs-file->contents (mv-nth 0
                                  (abs-find-file (partial-collapse frame path)
                                                 path)))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-separate frame)
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame))))))
   (member-equal
    (nth
     0
     (abs-addrs
      (abs-file->contents (mv-nth 0
                                  (abs-find-file (partial-collapse frame path)
                                                 path)))))
    (abs-addrs
     (abs-file->contents
      (mv-nth
       0
       (abs-find-file-helper
        (frame-val->dir
         (cdr (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                              path)
                           frame)))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                                path)
                             frame))))
         path)))))))
  :instructions
  (:promote
   (:dive 1 2 1 1 2)
   := :top
   (:rewrite
    (:rewrite subsetp-member . 1)
    ((x
      (abs-addrs
       (abs-file->contents
        (mv-nth
         0
         (abs-find-file-helper
          (frame-val->dir
           (cdr (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                                path)
                             (partial-collapse frame path))))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                              path)
                           frame))))
           path))))))))
   :bash
   (:in-theory (enable assoc-of-frame->frame))
   (:= (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                       path)
                    (partial-collapse frame path))
       (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                       path)
                    (frame->frame (partial-collapse frame path))))
   (:= (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                       path)
                    frame)
       (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                       path)
                    (frame->frame frame)))
   (:claim (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))))
   (:rewrite path-clear-partial-collapse-when-zp-src-lemma-28)))

(defthm
  path-clear-partial-collapse-when-zp-src-lemma-30
  (implies
   (and
    (equal
     (abs-find-file-helper
      (frame-val->dir (cdr (assoc-equal 0 (partial-collapse frame path))))
      path)
     (abs-find-file (partial-collapse frame path)
                    path))
    (consp
     (abs-addrs
      (abs-file->contents (mv-nth 0
                                  (abs-find-file (partial-collapse frame path)
                                                 path)))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-separate frame)
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (subsetp-equal (abs-addrs (frame->root frame))
                   (frame-addrs-root (frame->frame frame))))
   (>
    (nth
     0
     (abs-addrs
      (abs-file->contents (mv-nth 0
                                  (abs-find-file (partial-collapse frame path)
                                                 path)))))
    0))
  :rule-classes :linear
  :instructions
  (:promote
   (:dive 2)
   (:apply-linear path-clear-partial-collapse-when-zp-src-lemma-24
                  ((frame (partial-collapse frame path))))
   :top :bash :bash (:change-goal nil t)
   :bash (:dive 1 1 1 2)
   :=
   (:= (frame-val->dir (cdr (assoc-equal 0 (partial-collapse frame path))))
       (frame->root (partial-collapse frame path))
       :hints (("goal" :in-theory (enable frame->root))))
   :top
   (:rewrite
    subsetp-trans
    ((y (frame-addrs-root (frame->frame (partial-collapse frame path))))))
   (:change-goal nil t)
   :bash
   (:rewrite subsetp-trans
             ((y (abs-addrs (frame->root (partial-collapse frame path))))))
   :bash :bash))

(defthm path-clear-partial-collapse-when-zp-src-lemma-31
  (subsetp-equal (frame-addrs-root frame)
                 (strip-cars frame))
  :hints (("goal" :in-theory (enable frame-addrs-root))))

(defthm
  path-clear-partial-collapse-when-zp-src-lemma-32
  (subsetp-equal (strip-cars (frame->frame (partial-collapse frame path)))
                 (strip-cars (frame->frame frame)))
  :hints (("goal" :in-theory (enable partial-collapse))))

(defthm
  path-clear-partial-collapse-when-zp-src-lemma-33
  (implies
   (and
    (equal
     (abs-find-file-helper
      (frame-val->dir (cdr (assoc-equal 0 (partial-collapse frame path))))
      path)
     (abs-find-file (partial-collapse frame path)
                    path))
    (consp
     (abs-addrs
      (abs-file->contents (mv-nth 0
                                  (abs-find-file (partial-collapse frame path)
                                                 path)))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-separate frame)
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (subsetp-equal (abs-addrs (frame->root frame))
                   (frame-addrs-root (frame->frame frame))))
   (consp
    (assoc-equal
     (nth 0
          (abs-addrs (abs-file->contents
                      (mv-nth 0
                              (abs-find-file (partial-collapse frame path)
                                             path)))))
     frame)))
  :instructions
  (:promote
   (:=
    (consp
     (assoc-equal
      (nth
       0
       (abs-addrs (abs-file->contents
                   (mv-nth 0
                           (abs-find-file (partial-collapse frame path)
                                          path)))))
      frame))
    (member-equal
     (nth 0
          (abs-addrs (abs-file->contents
                      (mv-nth 0
                              (abs-find-file (partial-collapse frame path)
                                             path)))))
     (strip-cars frame))
    :equiv iff)
   (:rewrite
    (:rewrite subsetp-member . 1)
    ((x (abs-addrs (abs-file->contents
                    (mv-nth 0
                            (abs-find-file (partial-collapse frame path)
                                           path)))))))
   :bash (:dive 1 1 1 2)
   := :top
   (:rewrite subsetp-trans2
             ((y (strip-cars (frame->frame frame)))))
   (:bash ("goal" :in-theory (enable frame->frame)))
   (:= (frame-val->dir (cdr (assoc-equal 0 (partial-collapse frame path))))
       (frame->root (partial-collapse frame path))
       :hints (("goal" :in-theory (enable frame->root))))
   (:rewrite subsetp-trans
             ((y (abs-addrs (frame->root (partial-collapse frame path))))))
   :bash
   (:rewrite
    subsetp-trans
    ((y (frame-addrs-root (frame->frame (partial-collapse frame path))))))
   :bash
   (:rewrite subsetp-trans
             ((y (strip-cars (frame->frame (partial-collapse frame path))))))
   :bash :bash))

(defthmd
  path-clear-partial-collapse-when-zp-src-lemma-34
  (implies (m1-regular-file-p file)
           (abs-no-dups-p (abs-file->contents file)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable m1-file->contents m1-regular-file-p
                              m1-file-contents-fix abs-no-dups-p)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies (m1-regular-file-p file)
             (abs-no-dups-p (m1-file->contents file))))))

(encapsulate
  ()

  (local
   (defthm
     lemma-1
     (implies
      (prefixp
       (fat32-filename-list-fix path)
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))
      (abs-no-dups-p (abs-file->contents$inline
                      (mv-nth '0
                              (abs-find-file-helper (frame->root frame)
                                                    path)))))
     :hints
     (("goal"
       :do-not-induct t
       :in-theory
       (e/d (collapse abs-fs-fix abs-file-p-alt)
            ((:definition fat32-filename-list-prefixp)
             (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8
                       . 2)
             (:rewrite prefixp-when-equal-lengths)
             (:rewrite path-clear-partial-collapse-when-zp-src-lemma-11)
             (:rewrite len-when-prefixp)
             (:rewrite abs-fs-p-when-hifat-no-dups-p)
             (:rewrite abs-file-alist-p-correctness-1)
             (:definition len)
             (:rewrite abs-find-file-correctness-lemma-16)
             (:rewrite path-clear-partial-collapse-when-zp-src-lemma-11)
             (:rewrite abs-file-p-of-abs-find-file-helper)))
       :use ((:instance (:rewrite path-clear-partial-collapse-when-zp-src-lemma-11)
                        (path path)
                        (fs (frame->root frame)))
             (:instance path-clear-partial-collapse-when-zp-src-lemma-34
                        (file (mv-nth 0
                                      (abs-find-file-helper (frame->root frame)
                                                            path))))
             (:instance (:rewrite abs-file-p-of-abs-find-file-helper)
                        (path path)
                        (fs (frame->root frame))))))))

  (local
   (defthm lemma-2
     (implies
      (and
       (prefixp
        (fat32-filename-list-fix path)
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame)))))
       (ctx-app-ok
        (frame->root frame)
        (1st-complete (frame->frame frame))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))))
      (abs-directory-file-p (mv-nth '0
                                    (abs-find-file-helper (frame->root frame)
                                                          path))))
     :hints
     (("goal"
       :do-not-induct t
       :in-theory
       (e/d (collapse abs-fs-fix abs-file-p-alt)
            ((:definition fat32-filename-list-prefixp)
             (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8
                       . 2)
             (:rewrite prefixp-when-equal-lengths)
             (:rewrite path-clear-partial-collapse-when-zp-src-lemma-11)
             (:rewrite len-when-prefixp)
             (:rewrite abs-fs-p-when-hifat-no-dups-p)
             (:rewrite abs-file-alist-p-correctness-1)
             (:definition len)
             (:rewrite abs-find-file-correctness-lemma-16)
             (:rewrite abs-file-p-of-abs-find-file-helper)))
       :use (:instance (:rewrite abs-file-p-of-abs-find-file-helper)
                       (path path)
                       (fs (frame->root frame)))))))

  ;; This is inductive, so it's kept but left disabled.
  (defthmd
    path-clear-partial-collapse-when-zp-src-lemma-37
    (implies
     (and
      (frame-p frame)
      (no-duplicatesp-equal (strip-cars frame))
      (abs-separate frame)
      (mv-nth 1 (collapse frame))
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (member-equal
       y
       (abs-addrs
        (abs-file->contents (mv-nth 0
                                    (abs-find-file-helper (frame->root frame)
                                                          path)))))
      (subsetp-equal (abs-addrs (frame->root frame))
                     (frame-addrs-root (frame->frame frame))))
     (fat32-filename-list-prefixp
      path
      (frame-val->path (cdr (assoc-equal y (frame->frame frame))))))
    :hints
    (("goal"
      :in-theory
      (e/d (collapse abs-fs-fix)
           ((:definition fat32-filename-list-prefixp)
            (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8
                      . 2)
            (:rewrite prefixp-when-equal-lengths)
            (:rewrite path-clear-partial-collapse-when-zp-src-lemma-11)
            (:rewrite len-when-prefixp)
            (:rewrite abs-fs-p-when-hifat-no-dups-p)
            (:rewrite abs-file-alist-p-correctness-1)
            (:definition len)
            (:rewrite abs-find-file-correctness-lemma-16)))
      :induct (collapse frame)))))

(defthm
  path-clear-partial-collapse-when-zp-src-lemma-38
  (implies
   (abs-separate frame)
   (no-duplicatesp-equal
    (abs-addrs
     (abs-fs-fix (abs-file->contents$inline
                  (mv-nth 0
                          (abs-find-file-helper (frame->root frame)
                                                path)))))))
  :hints
  (("goal"
    :in-theory (e/d (abs-fs-fix abs-file-contents-p)
                    ((:rewrite no-duplicatesp-of-abs-addrs-of-abs-fs-fix)
                     (:rewrite abs-file-contents-p-of-abs-file->contents)))
    :use
    ((:instance
      (:rewrite no-duplicatesp-of-abs-addrs-of-abs-fs-fix)
      (x (abs-file->contents (mv-nth 0
                                     (abs-find-file-helper (frame->root frame)
                                                           path)))))
     (:instance (:rewrite abs-file-contents-p-of-abs-file->contents)
                (x (mv-nth 0
                           (abs-find-file-helper (frame->root frame)
                                                 path))))))))

(defthm
  path-clear-partial-collapse-when-zp-src-lemma-39
  (implies
   (and (abs-separate frame)
        (atom (frame-val->path (cdr (assoc-equal 0 frame))))
        (frame-p frame)
        (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (subsetp-equal
    (abs-addrs
     (abs-file->contents
      (mv-nth
       0
       (abs-find-file-helper (frame->root (partial-collapse frame path1))
                             path2))))
    (abs-addrs
     (abs-file->contents (mv-nth 0
                                 (abs-find-file-helper (frame->root frame)
                                                       path2))))))
  :hints (("goal" :in-theory (enable partial-collapse)
           :induct (partial-collapse frame path1))))

(defthm
  path-clear-partial-collapse-when-zp-src-lemma-40
  (implies
   (and
    (equal
     (abs-find-file-helper
      (frame-val->dir (cdr (assoc-equal 0 (partial-collapse frame path))))
      path)
     (abs-find-file (partial-collapse frame path)
                    path))
    (consp
     (abs-addrs
      (abs-file->contents (mv-nth 0
                                  (abs-find-file (partial-collapse frame path)
                                                 path)))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-separate frame)
    (mv-nth 1 (collapse frame))
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (subsetp-equal (abs-addrs (frame->root frame))
                   (frame-addrs-root (frame->frame frame))))
   (fat32-filename-list-prefixp
    path
    (frame-val->path
     (cdr
      (assoc-equal
       (nth
        0
        (abs-addrs (abs-file->contents
                    (mv-nth 0
                            (abs-find-file (partial-collapse frame path)
                                           path)))))
       frame)))))
  :instructions
  (:promote
   (:=
    (assoc-equal
     (nth 0
          (abs-addrs (abs-file->contents
                      (mv-nth 0
                              (abs-find-file (partial-collapse frame path)
                                             path)))))
     frame)
    (assoc-equal
     (nth 0
          (abs-addrs (abs-file->contents
                      (mv-nth 0
                              (abs-find-file (partial-collapse frame path)
                                             path)))))
     (frame->frame frame))
    :hints (("goal" :in-theory (e/d (assoc-of-frame->frame)
                                    (nth)))))
   (:rewrite path-clear-partial-collapse-when-zp-src-lemma-37)
   (:dive 1 2 1 1 2)
   := :top
   (:rewrite
    (:rewrite subsetp-member . 2)
    ((x
      (abs-addrs
       (abs-file->contents
        (mv-nth
         0
         (abs-find-file-helper
          (frame-val->dir (cdr (assoc-equal 0 (partial-collapse frame path))))
          path)))))))
   (:change-goal nil t)
   :bash
   (:= (frame-val->dir (cdr (assoc-equal 0 (partial-collapse frame path))))
       (frame->root (partial-collapse frame path))
       :hints (("goal" :in-theory (enable frame->root))))
   :bash))

(defthm
  path-clear-partial-collapse-when-zp-src-lemma-41
  (implies
   (and
    (equal (mv-nth 1
                   (abs-find-file (partial-collapse frame path)
                                  path))
           0)
    (equal
     (abs-find-file-helper
      (frame-val->dir
       (cdr (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                            path)
                         (partial-collapse frame path))))
      (nthcdr
       (len
        (frame-val->path
         (cdr (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                              path)
                           frame))))
       path))
     (abs-find-file (partial-collapse frame path)
                    path))
    (fat32-filename-list-prefixp
     path
     (frame-val->path
      (cdr
       (assoc-equal
        (nth
         0
         (abs-addrs (abs-file->contents
                     (mv-nth 0
                             (abs-find-file (partial-collapse frame path)
                                            path)))))
        frame))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-separate frame)
    (mv-nth 1 (collapse frame))
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (subsetp-equal (abs-addrs (frame->root frame))
                   (frame-addrs-root (frame->frame frame))))
   (consp
    (assoc-equal
     (nth 0
          (abs-addrs (abs-file->contents
                      (mv-nth 0
                              (abs-find-file (partial-collapse frame path)
                                             path)))))
     (partial-collapse frame path))))
  :instructions
  (:promote
   (:dive 1 1 2 1 1 2)
   := :top
   (:=
    (consp
     (assoc-equal
      (nth
       0
       (abs-addrs
        (abs-file->contents
         (mv-nth
          0
          (abs-find-file-helper
           (frame-val->dir
            (cdr (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                                 path)
                              (partial-collapse frame path))))
           (nthcdr
            (len
             (frame-val->path
              (cdr
               (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                               path)
                            frame))))
            path))))))
      (partial-collapse frame path)))
    (member-equal
     (nth
      0
      (abs-addrs
       (abs-file->contents
        (mv-nth
         0
         (abs-find-file-helper
          (frame-val->dir
           (cdr (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                                path)
                             (partial-collapse frame path))))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                              path)
                           frame))))
           path))))))
     (strip-cars (partial-collapse frame path)))
    :equiv iff)
   (:rewrite
    (:rewrite subsetp-member . 1)
    ((x
      (abs-addrs
       (abs-file->contents
        (mv-nth
         0
         (abs-find-file-helper
          (frame-val->dir
           (cdr (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                                path)
                             (partial-collapse frame path))))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                              path)
                           frame))))
           path))))))))
   :bash
   (:rewrite
    subsetp-trans
    ((y
      (abs-addrs
       (frame-val->dir
        (cdr (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                             path)
                          (partial-collapse frame path))))))))
   (:rewrite (:rewrite path-clear-partial-collapse-when-zp-src-lemma-23 . 2))
   :bash
   (:bash
    ("goal"
     :use (:instance (:rewrite assoc-of-frame->frame)
                     (frame (partial-collapse frame path))
                     (x (abs-find-file-src (partial-collapse frame path)
                                           path)))))
   (:= (frame-val->dir (cdr (assoc-equal 0 (partial-collapse frame path))))
       (frame->root (partial-collapse frame path))
       :hints (("goal" :in-theory (enable frame->root))))
   (:rewrite
    subsetp-trans
    ((y (frame-addrs-root (frame->frame (partial-collapse frame path))))))
   :bash
   (:rewrite subsetp-trans
             ((y (strip-cars (frame->frame (partial-collapse frame path))))))
   :bash
   (:bash ("goal" :in-theory (enable frame->frame)))
   (:rewrite subsetp-trans
             ((y (strip-cars (frame->frame (partial-collapse frame path))))))
   (:bash
    ("goal" :restrict (((:rewrite path-clear-partial-collapse-when-zp-src-lemma-22 . 1)
                        ((x (abs-find-file-src (partial-collapse frame path)
                                               path)))))))
   (:bash ("goal" :in-theory (enable frame->frame)))))

(defthm
  path-clear-partial-collapse-when-zp-src-lemma-42
  (implies
   (and
    (equal (mv-nth 1
                   (abs-find-file (partial-collapse frame path)
                                  path))
           0)
    (equal
     (abs-find-file-helper
      (frame-val->dir
       (cdr (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                            path)
                         (partial-collapse frame path))))
      (nthcdr
       (len
        (frame-val->path
         (cdr (assoc-equal (abs-find-file-src (partial-collapse frame path)
                                              path)
                           frame))))
       path))
     (abs-find-file (partial-collapse frame path)
                    path))
    (not
     (equal
      (nth
       0
       (abs-addrs (abs-file->contents
                   (mv-nth 0
                           (abs-find-file (partial-collapse frame path)
                                          path)))))
      0))
    (fat32-filename-list-prefixp
     path
     (frame-val->path
      (cdr
       (assoc-equal
        (nth
         0
         (abs-addrs (abs-file->contents
                     (mv-nth 0
                             (abs-find-file (partial-collapse frame path)
                                            path)))))
        frame))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-separate frame)
    (mv-nth 1 (collapse frame))
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (subsetp-equal (abs-addrs (frame->root frame))
                   (frame-addrs-root (frame->frame frame))))
   (not
    (member-equal
     (nth 0
          (abs-addrs (abs-file->contents
                      (mv-nth 0
                              (abs-find-file (partial-collapse frame path)
                                             path)))))
     (seq-this-under-path frame path))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (assoc-of-frame->frame)
                    (nth path-clear-partial-collapse-when-zp-src-lemma-17))
    :use
    (:instance
     path-clear-partial-collapse-when-zp-src-lemma-17
     (x
      (nth
       0
       (abs-addrs (abs-file->contents
                   (mv-nth 0
                           (abs-find-file (partial-collapse frame path)
                                          path))))))))))

;; This is important too - it establishes that after partially-collapsing on
;; path, the contents of the directory at path are complete, or there's a
;; regular file at path.
(defthm
  path-clear-partial-collapse-when-zp-src-lemma-43
  (implies
   (and (frame-p frame)
        (no-duplicatesp-equal (strip-cars frame))
        (abs-separate frame)
        (mv-nth 1 (collapse frame))
        (atom (frame-val->path (cdr (assoc-equal 0 frame))))
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame)))
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0))
   (abs-complete
    (abs-file->contents (mv-nth 0
                                (abs-find-file (partial-collapse frame path)
                                               path)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (abs-complete assoc-of-frame->frame)
                    (nth path-clear-partial-collapse-when-zp-src-lemma-4
                         (:rewrite path-clear-partial-collapse-when-zp-src-lemma-9 . 1)))
    :use
    ((:instance abs-find-file-src-correctness-2
                (frame (partial-collapse frame path)))
     (:instance
      path-clear-partial-collapse-when-zp-src-lemma-4
      (x
       (nth
        0
        (abs-addrs (abs-file->contents
                    (mv-nth 0
                            (abs-find-file (partial-collapse frame path)
                                           path))))))
      (path (fat32-filename-list-fix path)))
     (:instance (:rewrite abs-find-file-of-remove-assoc-lemma-3)
                (frame (partial-collapse frame path)))
     (:instance
      path-clear-partial-collapse-when-zp-src-lemma-13
      (frame frame)
      (y
       (nth
        0
        (abs-addrs (abs-file->contents
                    (mv-nth 0
                            (abs-find-file (partial-collapse frame path)
                                           path))))))
      (path path)
      (x (abs-find-file-src (partial-collapse frame path)
                            path)))
     (:instance (:rewrite path-clear-partial-collapse-when-zp-src-lemma-9 . 1)
                (path path)
                (frame (partial-collapse frame path)))))))

(encapsulate
  ()

  (local
   (defthmd lemma
     (implies
      (and
       (equal (frame-val->src$inline (cdr (assoc-equal 0 frame)))
              0)
       (not (equal (mv-nth 1
                           (abs-find-file (partial-collapse frame path)
                                          path))
                   2))
       (not (member-equal (car indices)
                          (seq-this-under-path frame path)))
       (consp (assoc-equal (car indices)
                           (frame->frame frame)))
       (prefixp (frame-val->path (cdr (assoc-equal (car indices)
                                                   (frame->frame frame))))
                (fat32-filename-list-fix path))
       (frame-p frame)
       (no-duplicatesp-equal (strip-cars frame))
       (abs-separate frame)
       (mv-nth 1 (collapse frame))
       (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
       (subsetp-equal (abs-addrs (frame->root frame))
                      (frame-addrs-root (frame->frame frame)))
       (equal (abs-find-file-src (partial-collapse frame path)
                                 path)
              0))
      (equal
       (mv-nth
        1
        (abs-find-file-helper
         (frame-val->dir$inline
          (cdr (assoc-equal (car indices)
                            (frame->frame (partial-collapse frame path)))))
         (nthcdr
          (len
           (frame-val->path$inline (cdr (assoc-equal (car indices)
                                                     (frame->frame frame)))))
          path)))
       *enoent*))
     :hints
     (("goal"
       :do-not-induct t
       :in-theory
       (e/d
        nil
        ((:rewrite abs-find-file-correctness-2)))
       :use ((:instance abs-find-file-src-correctness-2
                        (frame (partial-collapse frame path)))
             (:instance abs-find-file-correctness-1-lemma-36
                        (x (car indices))
                        (frame (partial-collapse frame path)))
             (:instance (:rewrite abs-find-file-correctness-2)
                        (frame (partial-collapse frame path)))))
      ("goal'''" :expand (frame->root (partial-collapse frame path))))))

  (defthm
    path-clear-partial-collapse-when-zp-src-lemma-14
    (implies
     (and (equal (frame-val->src$inline (cdr (assoc-equal 0 frame)))
                 0)
          (not (member-equal (car indices)
                             (seq-this-under-path frame path)))
          (consp (assoc-equal (car indices)
                              (frame->frame frame)))
          (prefixp (frame-val->path (cdr (assoc-equal (car indices)
                                                      (frame->frame frame))))
                   (fat32-filename-list-fix path))
          (frame-p frame)
          (no-duplicatesp-equal (strip-cars frame))
          (abs-separate frame)
          (mv-nth 1 (collapse frame))
          (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
          (subsetp-equal (abs-addrs (frame->root frame))
                         (frame-addrs-root (frame->frame frame)))
          (equal (abs-find-file-src (partial-collapse frame path)
                                    path)
                 0))
     (equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir$inline
         (cdr (assoc-equal (car indices)
                           (frame->frame (partial-collapse frame path)))))
        (nthcdr
         (len (frame-val->path$inline (cdr (assoc-equal (car indices)
                                                        (frame->frame frame)))))
         path)))
      *enoent*))
    :instructions
    ((:in-theory (disable lemma))
     (:use lemma)
     :split (:dive 1 2)
     (:= (frame-val->path (cdr (assoc-equal (car indices)
                                            (frame->frame frame))))
         (frame-val->path
          (cdr (assoc-equal (car indices)
                            (frame->frame (partial-collapse frame path))))))
     (:claim
      (and
       (consp (assoc-equal (car indices)
                           (frame->frame (partial-collapse frame path))))
       (equal
        (mv-nth 1
                (abs-find-file (frame->frame (partial-collapse frame path))
                               path))
        2)
       (prefixp
        (frame-val->path
         (cdr (assoc-equal (car indices)
                           (frame->frame (partial-collapse frame path)))))
        (fat32-filename-list-fix path)))
      :hints :none)
     (:rewrite abs-find-file-correctness-lemma-14)
     :top
     :bash :bash)))

(defthm path-clear-partial-collapse-when-zp-src-lemma-15
  (implies (and (consp path)
                (not (zp (mv-nth 1 (abs-find-file-helper fs path)))))
           (equal (names-at fs path) nil))
  :hints (("goal" :in-theory (enable abs-find-file-helper names-at))))

(defthm
  path-clear-partial-collapse-when-zp-src-lemma-16
  (implies
   (and
    (equal (frame-val->src$inline (cdr (assoc-equal 0 frame)))
           0)
    (not (member-equal (car indices)
                       (seq-this-under-path frame path)))
    (consp (assoc-equal (car indices)
                        (frame->frame frame)))
    (not (prefixp (fat32-filename-list-fix path)
                  (frame-val->path (cdr (assoc-equal (car indices)
                                                     (frame->frame frame))))))
    (prefixp (frame-val->path (cdr (assoc-equal (car indices)
                                                (frame->frame frame))))
             (fat32-filename-list-fix path))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-separate frame)
    (mv-nth 1 (collapse frame))
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (subsetp-equal (abs-addrs (frame->root frame))
                   (frame-addrs-root (frame->frame frame)))
    (equal (abs-find-file-src (partial-collapse frame path)
                              path)
           0))
   (equal
    (names-at
     (frame-val->dir
      (cdr (assoc-equal (car indices)
                        (frame->frame (partial-collapse frame path)))))
     (nthcdr (len (frame-val->path (cdr (assoc-equal (car indices)
                                                     (frame->frame frame)))))
             path))
    nil))
  :hints (("goal" :do-not-induct t
           :use (:instance abs-find-file-correctness-1-lemma-36
                           (x (car indices)))
           :in-theory (e/d
                       ((:linear
                         path-clear-partial-collapse-when-zp-src-lemma-6))
                       (prefixp-when-prefixp len-when-prefixp)))))

(local
 (defthmd
   path-clear-partial-collapse-when-zp-src-lemma-1
   (implies (and (equal (frame-val->src$inline (cdr (assoc-equal 0 frame)))
                        0)
                 (frame-p frame)
                 (no-duplicatesp-equal (strip-cars frame))
                 (abs-separate frame)
                 (mv-nth 1 (collapse frame))
                 (atom (frame-val->path (cdr (assoc-equal 0 frame))))
                 (subsetp-equal (abs-addrs (frame->root frame))
                                (frame-addrs-root (frame->frame frame)))
                 (equal (abs-find-file-src (partial-collapse frame path)
                                           path)
                        0))
            (path-clear-alt path
                            (frame->frame (partial-collapse frame path))
                            indices))
   :hints
   (("goal"
     :induct (path-clear-alt path
                             (frame->frame (partial-collapse frame path))
                             indices)
     :in-theory (e/d (subsetp-equal path-clear-alt)
                     ())))))

(defthm
  path-clear-partial-collapse-when-zp-src
  (implies (and (frame-p frame)
                (no-duplicatesp-equal (strip-cars frame))
                (abs-separate frame)
                (mv-nth 1 (collapse frame))
                (atom (frame-val->path (cdr (assoc-equal 0 frame))))
                (subsetp-equal (abs-addrs (frame->root frame))
                               (frame-addrs-root (frame->frame frame)))
                (equal (abs-find-file-src (partial-collapse frame path)
                                          path)
                       0)
                (equal (frame-val->src (cdr (assoc-equal 0 frame)))
                       0))
           (path-clear path
                       (frame->frame (partial-collapse frame path))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (enable path-clear-alt-of-strip-cars)
    :use
    (:instance
     path-clear-partial-collapse-when-zp-src-lemma-1
     (indices (strip-cars (frame->frame (partial-collapse frame path))))))))

(defthm
  path-clear-partial-collapse-when-not-zp-src-lemma-2
  (implies
   (and (no-duplicatesp-equal (strip-cars frame))
        (not (zp (abs-find-file-src frame path))))
   (prefixp
    (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                       frame)))
    (fat32-filename-list-fix path)))
  :hints (("goal" :in-theory (enable abs-find-file-src))))

(defthm
  path-clear-partial-collapse-when-not-zp-src-lemma-3
  (implies
   (and (no-duplicatesp-equal (strip-cars frame))
        (< 0 (abs-find-file-src frame path)))
   (not
    (equal
     (mv-nth
      1
      (abs-find-file-helper
       (frame-val->dir (cdr (assoc-equal (abs-find-file-src frame path)
                                         frame)))
       (nthcdr
        (len (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                                frame))))
        path)))
     *enoent*)))
  :hints (("goal" :in-theory (enable abs-find-file-src))))

;; This is actually not a great lemma to disable, since it eliminates a free
;; variable from an existing lemma and removes one of its hypotheses.
(defthm
  path-clear-partial-collapse-when-not-zp-src-lemma-4
  (implies
   (and (no-duplicatesp-equal (strip-cars frame))
        (mv-nth 1 (collapse frame))
        (frame-p (frame->frame frame))
        (consp (assoc-equal (abs-find-file-src frame path)
                            (frame->frame frame)))
        (consp (assoc-equal y (frame->frame frame)))
        (not (equal (abs-find-file-src frame path)
                    y))
        (prefixp (frame-val->path (cdr (assoc-equal y (frame->frame frame))))
                 (fat32-filename-list-fix path))
        (dist-names (frame->root frame)
                    nil (frame->frame frame))
        (abs-separate (frame->frame frame)))
   (equal
    (abs-find-file-helper
     (frame-val->dir (cdr (assoc-equal y (frame->frame frame))))
     (nthcdr
      (len (frame-val->path (cdr (assoc-equal y (frame->frame frame)))))
      path))
    (cons (abs-file-fix nil) '(2))))
  :hints (("goal" :in-theory (e/d (assoc-of-frame->frame))
           :use (:instance abs-find-file-correctness-1-lemma-75
                           (x (abs-find-file-src frame path))))))

(defthm
  path-clear-partial-collapse-when-not-zp-src-lemma-5
  (implies
   (and (not (member-equal (car indices)
                           (seq-this-under-path frame path)))
        (consp (assoc-equal (car indices)
                            (frame->frame frame)))
        (prefixp (frame-val->path (cdr (assoc-equal (car indices)
                                                    (frame->frame frame))))
                 (fat32-filename-list-fix path))
        (frame-p frame)
        (no-duplicatesp-equal (strip-cars frame))
        (abs-separate frame)
        (mv-nth 1 (collapse frame))
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame)))
        (not (equal (abs-find-file-src (partial-collapse frame path)
                                       path)
                    0))
        (not (member-equal (abs-find-file-src (partial-collapse frame path)
                                              path)
                           indices)))
   (equal
    (mv-nth
     1
     (abs-find-file-helper
      (frame-val->dir$inline
       (cdr (assoc-equal (car indices)
                         (frame->frame (partial-collapse frame path)))))
      (nthcdr
       (len (frame-val->path$inline (cdr (assoc-equal (car indices)
                                                      (frame->frame frame)))))
       path)))
    *enoent*))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable path-clear-partial-collapse-when-not-zp-src-lemma-4
                        (:r abs-find-file-src-correctness-1))
    :use ((:instance (:rewrite abs-find-file-src-correctness-1)
                     (frame (partial-collapse frame path)))
          (:instance path-clear-partial-collapse-when-not-zp-src-lemma-4
                     (path path)
                     (frame (partial-collapse frame path))
                     (y (car indices)))
          (:instance (:rewrite assoc-of-frame->frame)
                     (frame (partial-collapse frame path))
                     (x (abs-find-file-src (partial-collapse frame path)
                                           path)))))))

(local
 (defthm
   path-clear-partial-collapse-when-not-zp-src-lemma-1
   (implies
    (and (frame-p frame)
         (no-duplicatesp-equal (strip-cars frame))
         (abs-separate frame)
         (mv-nth 1 (collapse frame))
         (atom (frame-val->path (cdr (assoc-equal 0 frame))))
         (subsetp-equal (abs-addrs (frame->root frame))
                        (frame-addrs-root (frame->frame frame)))
         (not (equal (abs-find-file-src (partial-collapse frame path)
                                        path)
                     0))
         (subsetp-equal
          indices
          (remove-equal
           (abs-find-file-src (partial-collapse frame path)
                              path)
           (strip-cars (frame->frame (partial-collapse frame path))))))
    (path-clear-alt path
                    (frame->frame (partial-collapse frame path))
                    indices))
   :hints
   (("goal"
     :in-theory (enable path-clear-alt
                        subsetp-equal member-equal
                        (:linear path-clear-partial-collapse-when-zp-src-lemma-6))
     :do-not-induct t
     :induct (path-clear-alt path
                             (frame->frame (partial-collapse frame path))
                             indices)))))

(defthm
  path-clear-partial-collapse-when-not-zp-src
  (implies
   (and (frame-p frame)
        (no-duplicatesp-equal (strip-cars frame))
        (abs-separate frame)
        (mv-nth 1 (collapse frame))
        (atom (frame-val->path (cdr (assoc-equal 0 frame))))
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame)))
        (not (equal (abs-find-file-src (partial-collapse frame path)
                                       path)
                    0)))
   (path-clear
    path
    (remove-assoc-equal (abs-find-file-src (partial-collapse frame path)
                                           path)
                        (frame->frame (partial-collapse frame path)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (path-clear-alt-of-remove-of-strip-cars)
                    (path-clear-partial-collapse-when-not-zp-src-lemma-1))
    :use
    (:instance
     path-clear-partial-collapse-when-not-zp-src-lemma-1
     (indices
      (remove-equal
       (abs-find-file-src (partial-collapse frame path)
                          path)
       (strip-cars (frame->frame (partial-collapse frame path)))))))))

(defthm
  path-clear-when-prefixp-lemma-1
  (implies
   (and
    (prefixp (frame-val->path (cdr (car frame)))
             (fat32-filename-list-fix y))
    (prefixp (fat32-filename-list-fix x)
             (fat32-filename-list-fix y))
    (not (prefixp (fat32-filename-list-fix x)
                  (frame-val->path (cdr (car frame)))))
    (not (consp (names-at (frame-val->dir (cdr (car frame)))
                          (nthcdr (len (frame-val->path (cdr (car frame))))
                                  x)))))
   (not (consp (names-at (frame-val->dir (cdr (car frame)))
                         (nthcdr (len (frame-val->path (cdr (car frame))))
                                 y)))))
  :hints
  (("goal"
    :in-theory (e/d ()
                    ((:rewrite prefixp-nthcdr-nthcdr)
                     (:rewrite names-at-when-prefixp)
                     len-when-prefixp))
    :use ((:instance (:rewrite names-at-when-prefixp)
                     (y (nthcdr (len (frame-val->path (cdr (car frame))))
                                y))
                     (fs (frame-val->dir (cdr (car frame))))
                     (x (nthcdr (len (frame-val->path (cdr (car frame))))
                                x)))
          (:instance (:rewrite prefixp-nthcdr-nthcdr)
                     (l2 (fat32-filename-list-fix y))
                     (l1 (fat32-filename-list-fix x))
                     (n (len (frame-val->path (cdr (car frame))))))
          (:instance len-when-prefixp
                     (x (frame-val->path (cdr (car frame))))
                     (y (fat32-filename-list-fix y)))))))

(defthm
  path-clear-when-prefixp-lemma-2
  (implies (not (consp (names-at (frame-val->dir (cdr (car frame)))
                                 nil)))
           (not (consp (names-at (frame-val->dir (cdr (car frame)))
                                 (nthcdr (len x) y)))))
  :hints
  (("goal" :in-theory (e/d (names-at)
                           ((:rewrite member-of-remove)))
    :do-not-induct t
    :expand (names-at (frame-val->dir (cdr (car frame)))
                      (nthcdr (len x) y))
    :use (:instance (:rewrite member-of-remove)
                    (x (strip-cars (frame-val->dir (cdr (car frame)))))
                    (b nil)
                    (a (fat32-filename-fix (nth (len x) y)))))))

(defthm
  path-clear-when-prefixp
  (implies (and (prefixp (fat32-filename-list-fix x)
                         (fat32-filename-list-fix y))
                (path-clear x frame))
           (path-clear y frame))
  :hints
  (("goal"
    :in-theory (e/d (path-clear list-equiv)
                    (len-when-prefixp (:rewrite prefixp-when-equal-lengths))))))

(defthm
  path-clear-partial-collapse-lemma-1
  (implies
   (and (frame-p frame)
        (no-duplicatesp-equal (strip-cars frame))
        (abs-separate frame)
        (mv-nth 1 (collapse frame))
        (atom (frame-val->path (cdr (assoc-equal 0 frame))))
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame)))
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0))
   (path-clear
    path
    (remove-assoc-equal (abs-find-file-src (partial-collapse frame path)
                                           path)
                        (frame->frame (partial-collapse frame path)))))
  :hints
  (("goal" :do-not-induct t
    :in-theory (disable path-clear-partial-collapse-when-not-zp-src)
    :use path-clear-partial-collapse-when-not-zp-src)))

(encapsulate
  ()

  (local
   (defthmd
     lemma-1
     (implies
      (and
       (not (equal (abs-find-file-src frame path)
                   0))
       (equal
        (abs-find-file-helper
         (frame-val->dir (cdr (assoc-equal (abs-find-file-src frame path)
                                           (frame->frame frame))))
         (nthcdr
          (len (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                                  (frame->frame frame)))))
          path))
        (abs-find-file (frame->frame frame)
                       path))
       (no-duplicatesp-equal (strip-cars frame))
       (mv-nth 1 (collapse frame))
       (frame-p frame)
       (dist-names (frame->root frame)
                   nil (frame->frame frame))
       (abs-separate (frame->frame frame)))
      (equal (mv-nth 1
                     (abs-find-file-helper (frame->root frame)
                                           path))
             *enoent*))
     :hints
     (("goal"
       :cases
       ((not
         (equal
          (abs-find-file-helper
           (frame-val->dir (cdr (assoc-equal (abs-find-file-src frame path)
                                             (frame->frame frame))))
           (nthcdr
            (len
             (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                                (frame->frame frame)))))
            path))
          (abs-find-file (frame->frame frame)
                         path))))
       :do-not-induct t
       :in-theory
       (e/d (assoc-of-frame->frame)
            ((:rewrite path-clear-partial-collapse-when-not-zp-src-lemma-3)))
       :use (:rewrite path-clear-partial-collapse-when-not-zp-src-lemma-3)))))

  (local
   (defthmd
     lemma-2
     (implies
      (and
       (prefixp (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                                   (frame->frame frame))))
                (fat32-filename-list-fix path))
       (no-duplicatesp-equal (strip-cars frame))
       (mv-nth 1 (collapse frame))
       (frame-p frame)
       (dist-names (frame->root frame)
                   nil (frame->frame frame))
       (abs-separate (frame->frame frame))
       (not (equal (mv-nth 1
                           (abs-find-file-helper (frame->root frame)
                                                 path))
                   2)))
      (equal (abs-find-file-src frame path)
             0))
     :hints
     (("goal"
       :use
       lemma-1))))

  (defthm
    path-clear-partial-collapse-lemma-2
    (implies (and (no-duplicatesp-equal (strip-cars frame))
                  (mv-nth 1 (collapse frame))
                  (frame-p frame)
                  (dist-names (frame->root frame)
                              nil (frame->frame frame))
                  (abs-separate (frame->frame frame))
                  (not (equal (mv-nth 1
                                      (abs-find-file-helper (frame->root frame)
                                                            path))
                              2)))
             (equal (abs-find-file-src frame path)
                    0))
    :hints (("goal" :do-not-induct t
             :in-theory (enable assoc-of-frame->frame)
             :use (:instance lemma-2)))))

(defthm
  path-clear-partial-collapse-lemma-3
  (implies (and (frame-p frame)
                (no-duplicatesp-equal (strip-cars frame))
                (abs-separate frame)
                (mv-nth 1 (collapse frame))
                (atom (frame-val->path (cdr (assoc-equal 0 frame))))
                (subsetp-equal (abs-addrs (frame->root frame))
                               (frame-addrs-root (frame->frame frame)))
                (not (equal (abs-find-file-src (partial-collapse frame path)
                                               path)
                            0)))
           (equal (names-at (frame->root (partial-collapse frame path))
                            path)
                  nil))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (assoc-of-frame->frame)
                    ((:rewrite path-clear-partial-collapse-when-zp-src-lemma-15)
                     (:rewrite abs-find-file-src-correctness-1)
                     (:rewrite path-clear-partial-collapse-when-zp-src-lemma-17)))
    :use ((:instance (:rewrite path-clear-partial-collapse-when-zp-src-lemma-15)
                     (path path)
                     (fs (frame->root (partial-collapse frame path))))
          (:instance abs-find-file-correctness-1-lemma-36
                     (x (abs-find-file-src (partial-collapse frame path)
                                           path)))
          (:instance (:rewrite abs-find-file-src-correctness-1)
                     (path path)
                     (frame (partial-collapse frame path)))
          (:instance (:rewrite path-clear-partial-collapse-when-zp-src-lemma-17)
                     (path path)
                     (frame frame)
                     (x (abs-find-file-src (partial-collapse frame path)
                                           path)))
          (:instance abs-find-file-src-correctness-2
                     (frame (partial-collapse frame path)))))))

(defthm
  path-clear-partial-collapse-lemma-4
  (implies (and (no-duplicatesp-equal (strip-cars frame))
                (atom (frame-val->path (cdr (assoc-equal 0 frame))))
                (path-clear path
                            (remove-assoc-equal x (frame->frame frame)))
                (atom (names-at (frame->root frame) path)))
           (path-clear path (remove-assoc-equal x frame)))
  :hints (("goal" :in-theory (enable remove-assoc-equal path-clear prefixp
                                     frame->root frame->frame abs-separate)
           :induct (remove-assoc-equal x frame))))

(defthm
  path-clear-partial-collapse
  (implies
   (and (frame-p frame)
        (no-duplicatesp-equal (strip-cars frame))
        (abs-separate frame)
        (mv-nth 1 (collapse frame))
        (atom (frame-val->path (cdr (assoc-equal 0 frame))))
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame)))
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (equal
         x
         (abs-find-file-src (partial-collapse frame path)
                            path)))
   (path-clear
    path
    (remove-assoc-equal x
                        (partial-collapse frame path))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (e/d (frame->frame)
         (path-clear-partial-collapse-lemma-1
          (:rewrite path-clear-partial-collapse-lemma-4)
          (:rewrite path-clear-partial-collapse-lemma-3)))
    :use
    (path-clear-partial-collapse-lemma-1
     (:instance (:rewrite path-clear-partial-collapse-lemma-4)
                (frame (partial-collapse frame path))
                (x (abs-find-file-src (partial-collapse frame path)
                                      path))
                (path path))
     (:rewrite path-clear-partial-collapse-lemma-3)))))
