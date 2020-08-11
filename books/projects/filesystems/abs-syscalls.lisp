;  abs-syscalls.lisp                                    Mihir Mehta

; This is a model of the FAT32 filesystem, related to HiFAT but with abstract
; variables.

(in-package "ACL2")

(include-book "partial-collapse")
(include-book "abs-find-file")
(include-book "abs-alloc")
(include-book "hifat-syscalls")
(local (include-book "std/lists/prefixp" :dir :system))
(local (include-book "std/lists/intersectp" :dir :system))

(local (in-theory (e/d (abs-file-p-when-m1-regular-file-p
                        len-when-consp)
                       ((:definition member-equal)
                        (:definition intersection-equal)
                        (:definition integer-listp)
                        (:rewrite true-listp-when-string-list)
                        (:linear position-equal-ac-when-member)
                        (:linear position-when-member)
                        (:rewrite nth-when->=-n-len-l)
                        (:linear len-of-remove-assoc-1)
                        (:definition position-equal-ac)
                        (:definition remove1-assoc-equal)
                        (:rewrite
                         abs-addrs-when-m1-file-alist-p-lemma-2)
                        (:rewrite m1-directory-file-p-correctness-1)
                        (:rewrite assoc-of-car-when-member)
                        (:rewrite integerp-of-car-when-integer-listp)
                        (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
                        (:linear
                         len-when-hifat-bounded-file-alist-p . 1)
                        (:rewrite
                         m1-file-p-of-cdar-when-m1-file-alist-p)
                        (:rewrite natp-of-car-when-nat-listp)
                        (:rewrite abs-find-file-correctness-1-lemma-3)
                        (:rewrite
                         partial-collapse-correctness-lemma-24)
                        (:rewrite abs-find-file-correctness-lemma-29)
                        (:rewrite collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-2)
                        (:rewrite when-zp-src-of-1st-collapse-1)
                        (:rewrite ctx-app-ok-of-abs-fs-fix-1)
                        (:rewrite
                         hifat-find-file-correctness-3-lemma-3)
                        (:rewrite abs-addrs-of-ctx-app-1-lemma-2)
                        (:rewrite
                         abs-fs-fix-of-put-assoc-equal-lemma-2)
                        (:rewrite hifat-file-alist-fix-guard-lemma-1)
                        (:rewrite
                         abs-file-alist-p-of-abs-file->contents)
                        (:rewrite member-of-abs-fs-fix-when-natp)
                        (:rewrite hifat-find-file-correctness-lemma-2)
                        (:rewrite
                         no-duplicatesp-equal-of-abs-addrs-of-abs-fs-fix)
                        (:rewrite
                         abs-find-file-helper-of-collapse-lemma-2)
                        (:rewrite
                         m1-file-alist-p-of-intersection-equal-2)
                        (:rewrite absfat-subsetp-transitivity-lemma-5)
                        (:rewrite
                         abs-separate-of-frame->frame-of-collapse-this-lemma-7)
                        (:linear 1st-complete-correctness-2)
                        different-from-own-src-1
                        (:rewrite m1-file-alist-p-when-subsetp-equal)
                        (:rewrite stringp-when-nonempty-stringp)
                        m1-file-alist-p-of-nthcdr
                        take-of-len-free
                        nth-when-prefixp
                        take-of-too-many
                        len-of-remove-assoc-2
                        nth-of-take))))

(defund abs-no-dups-file-p (file)
  (declare (xargs :guard t))
  (or (m1-regular-file-p file)
      (and (abs-directory-file-p file)
           (abs-no-dups-p (abs-file->contents file)))))

(defthm
  abs-file-p-when-abs-no-dups-file-p
  (implies (abs-no-dups-file-p file)
           (abs-file-p file))
  :hints (("goal" :in-theory (enable abs-file-p-alt abs-no-dups-file-p))))

(defund
  abs-no-dups-file-fix (file)
  (if (not (abs-file-alist-p (abs-file->contents file)))
      (abs-file-fix file)
      (change-abs-file
       file
       :contents (abs-fs-fix (abs-file->contents file)))))

(defthm abs-no-dups-file-fix-of-abs-no-dups-file-fix
  (equal (abs-no-dups-file-fix (abs-no-dups-file-fix x))
         (abs-no-dups-file-fix x))
  :hints (("goal" :in-theory (enable abs-no-dups-file-fix))))

(defthm abs-no-dups-file-fix-when-abs-no-dups-file-p
  (implies (abs-no-dups-file-p x)
           (equal (abs-no-dups-file-fix x) x))
  :hints (("goal" :in-theory (enable abs-no-dups-file-fix abs-no-dups-file-p))))

(defthm
  abs-no-dups-file-p-of-abs-no-dups-file-fix
  (abs-no-dups-file-p (abs-no-dups-file-fix x))
  :hints
  (("goal"
    :in-theory (e/d (abs-no-dups-file-fix abs-no-dups-file-p abs-file-p-alt)
                    (abs-file-p-of-abs-file-fix))
    :use abs-file-p-of-abs-file-fix)))

(defund
  abs-no-dups-file-equiv (file1 file2)
  (cond ((and (abs-file-alist-p (abs-file->contents file1))
              (abs-file-alist-p (abs-file->contents file2)))
         (absfat-equiv (abs-file->contents file1)
                       (abs-file->contents file2)))
        ((and (stringp (abs-file->contents file1))
              (stringp (abs-file->contents file2)))
         (equal (abs-file->contents file1)
                (abs-file->contents file2)))
        (t nil)))

(defund abs-place-file-helper (fs path file)
  (declare (xargs :guard (and (abs-fs-p fs) (abs-no-dups-file-p file)
                              (fat32-filename-list-p path))
                  :measure (len path)))
  (b* ((fs (mbe :exec fs :logic (abs-fs-fix fs)))
       (file (mbe :exec file :logic (abs-no-dups-file-fix file)))
       ((unless (consp path)) (mv fs *enoent*))
       (name (fat32-filename-fix (car path)))
       (alist-elem (abs-assoc name fs))
       ((unless (consp alist-elem)) (if (consp (cdr path)) (mv fs *enotdir*)
                                      (mv (abs-put-assoc name file fs) 0)))
       ((when (and (not (abs-directory-file-p (cdr alist-elem)))
                   (or (consp (cdr path)) (abs-directory-file-p file))))
        (mv fs *enotdir*))
       ((when (not (or (abs-directory-file-p (cdr alist-elem))
                       (consp (cdr path)) (abs-directory-file-p file)
                       (and (atom alist-elem) (>= (len fs) *ms-max-dir-ent-count*)))))
        (mv (abs-put-assoc name file fs) 0))
       ((when (not (or (m1-regular-file-p (cdr alist-elem))
                       (consp (cdr path)) (m1-regular-file-p file)
                       (and (atom alist-elem) (>= (len fs) *ms-max-dir-ent-count*)))))
        (mv (abs-put-assoc name file fs) 0))
       ((when (and (atom alist-elem) (>= (len fs) *ms-max-dir-ent-count*))) (mv fs *enospc*))
       ((mv new-contents error-code) (abs-place-file-helper (abs-file->contents (cdr alist-elem))
                                                            (cdr path) file)))
    (mv (abs-put-assoc name (make-abs-file :dir-ent (abs-file->dir-ent (cdr alist-elem))
                                           :contents new-contents)
                       fs)
        error-code)))

(defthm abs-file-alist-p-of-abs-place-file-helper
  (abs-file-alist-p (mv-nth 0 (abs-place-file-helper fs path file)))
  :hints (("goal" :in-theory (enable abs-place-file-helper))))

(defthm
  abs-no-dups-p-of-abs-file->contents-of-abs-no-dups-file-fix
  (abs-no-dups-p (abs-file->contents (abs-no-dups-file-fix file)))
  :hints (("goal" :in-theory (enable abs-no-dups-file-fix
                                     abs-file->contents abs-file-contents-fix
                                     abs-no-dups-p abs-file-contents-p
                                     abs-file abs-file-fix))))

(defthm
  abs-no-dups-p-of-abs-place-file-helper
  (abs-no-dups-p (mv-nth 0 (abs-place-file-helper fs path file)))
  :hints (("goal" :in-theory (enable abs-place-file-helper abs-no-dups-p)
           :induct (abs-place-file-helper fs path file))))

(defthm
  abs-fs-p-of-abs-place-file-helper-lemma-1
  (implies (m1-regular-file-p file)
           (abs-no-dups-p (abs-file->contents file)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable m1-file->contents m1-regular-file-p
                              m1-file-contents-fix abs-no-dups-p)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (m1-regular-file-p file)
             (abs-no-dups-p (m1-file->contents file))))))

(defthm abs-fs-p-of-abs-place-file-helper
  (abs-fs-p (mv-nth 0 (abs-place-file-helper fs path file)))
  :hints (("goal" :in-theory (enable abs-fs-p))))

(defthmd abs-place-file-helper-of-fat32-filename-list-fix
  (equal
   (abs-place-file-helper fs (fat32-filename-list-fix path) file)
   (abs-place-file-helper fs path file))
  :hints (("goal" :in-theory (enable abs-place-file-helper))))

(defcong
  fat32-filename-list-equiv
  equal
  (abs-place-file-helper fs path file)
  2
  :hints (("Goal" :use
           (abs-place-file-helper-of-fat32-filename-list-fix
            (:instance
             abs-place-file-helper-of-fat32-filename-list-fix
             (path path-equiv))))))

(defund
  abs-place-file (frame path file)
  (declare
   (xargs :guard (and (frame-p frame)
                      (abs-no-dups-file-p file)
                      (fat32-filename-list-p path))
          :guard-hints (("Goal" :do-not-induct t) )))
  (b*
      (((when (atom frame))
        (mv frame *enoent*))
       (path (mbe :exec path
                      :logic (fat32-filename-list-fix path)))
       ((mv tail tail-error-code)
        (abs-place-file (cdr frame) path file))
       ((unless (and (equal tail-error-code *ENOENT*)
                     (prefixp (frame-val->path (cdar frame))
                              path)))
        (mv (list* (car frame) tail) tail-error-code))
       ;; Look up the parent directory - it has to be in one of the variables,
       ;; or else we must return ENOENT.
       ((mv & error-code)
        (abs-find-file-helper
         (frame-val->dir (cdar frame))
         (nthcdr (len (frame-val->path (cdar frame)))
                 (butlast path 1))))
       ((when (or (equal error-code *enoent*)
                  (not (abs-complete (frame-val->dir (cdar frame))))))
        (mv (list* (car frame) tail) tail-error-code))
       ((mv head head-error-code)
        (abs-place-file-helper (frame-val->dir (cdar frame)) path file)))
    (mv
     (list* (cons (caar frame) (change-frame-val (cdar frame)
                                                 :dir (abs-fs-fix head)))
            (cdr frame))
     head-error-code)))

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
                                     path-clear prefixp intersectp-equal)
           :induct (path-clear path frame)
           :expand (dist-names dir path frame))))

(defthm path-clear-of-remove-assoc
  (implies
   (path-clear path frame)
   (path-clear path (remove-assoc-equal x frame)))
  :hints (("goal" :in-theory (enable path-clear))))

(defthm
  1st-complete-under-path-when-path-clear-of-prefix
  (implies (and (fat32-filename-list-p path2)
                (path-clear path1 frame)
                (prefixp (fat32-filename-list-fix path1)
                         (fat32-filename-list-fix path2))
                (not (fat32-filename-list-equiv path1 path2)))
           (equal (1st-complete-under-path frame path2)
                  0))
  :hints
  (("goal" :in-theory (e/d (frame-p path-clear
                                    1st-complete-under-path names-at)
                           (prefixp-when-equal-lengths len-when-prefixp)))
   ("subgoal *1/2" :use ((:instance prefixp-when-equal-lengths (x path2)
                                    (y (fat32-filename-list-fix path1)))
                         (:instance len-when-prefixp
                                    (x (fat32-filename-list-fix path1))
                                    (y path2))
                         (:instance len-when-prefixp
                                    (y (fat32-filename-list-fix path1))
                                    (x path2))))))

(defthm partial-collapse-when-path-clear-of-prefix
  (implies (and (fat32-filename-list-p path2)
                (path-clear path1 (frame->frame frame))
                (prefixp (fat32-filename-list-fix path1)
                         (fat32-filename-list-fix path2))
                (not (fat32-filename-list-equiv path1 path2)))
           (equal (partial-collapse frame path2)
                  frame))
  :hints (("Goal" :in-theory (enable partial-collapse))))

(defthm
  hifat-subsetp-of-put-assoc-1
  (implies
   (and (m1-file-alist-p x)
        (hifat-no-dups-p x)
        (stringp name))
   (equal
    (hifat-subsetp (put-assoc-equal name val x)
                   y)
    (and
     (hifat-subsetp (remove-assoc-equal name x)
                    y)
     (consp (assoc-equal name y))
     (or
      (and (not (m1-directory-file-p (cdr (assoc-equal name y))))
           (not (m1-directory-file-p val))
           (equal (m1-file->contents val)
                  (m1-file->contents (cdr (assoc-equal name y)))))
      (and (m1-directory-file-p (cdr (assoc-equal name y)))
           (m1-directory-file-p val)
           (hifat-subsetp (m1-file->contents val)
                          (m1-file->contents (cdr (assoc-equal name y)))))))))
  :hints (("goal" :in-theory (enable hifat-subsetp)
           :induct (mv (put-assoc-equal name val x)
                       (remove-assoc-equal name x)))))

(defthm hifat-subsetp-of-put-assoc-2
  (implies (and (m1-file-alist-p x)
                (hifat-subsetp x (remove-assoc-equal name y)))
           (hifat-subsetp x (put-assoc-equal name val y)))
  :hints (("goal" :in-theory (enable hifat-subsetp))))

(defthm hifat-subsetp-of-remove-assoc-1
  (implies (and (m1-file-alist-p x)
                (atom (assoc-equal name x))
                (hifat-subsetp x y))
           (hifat-subsetp x (remove-assoc-equal name y)))
  :hints (("goal" :in-theory (enable hifat-subsetp))))

(defthm hifat-subsetp-of-remove-assoc-2
  (implies (hifat-subsetp x y)
           (hifat-subsetp (remove-assoc-equal name x)
                          y))
  :hints (("goal" :in-theory (enable hifat-subsetp))))

(defthm
  hifat-place-file-correctness-lemma-3
  (implies
   (and
    (not
     (m1-regular-file-p (cdr (assoc-equal (fat32-filename-fix (car path))
                                          x))))
    (m1-file-alist-p x)
    (hifat-subsetp y x))
   (not
    (m1-regular-file-p (cdr (assoc-equal (fat32-filename-fix (car path))
                                         y)))))
  :hints (("goal" :in-theory (enable hifat-subsetp))))

(defthmd
  hifat-place-file-correctness-lemma-1
  (implies (and (m1-file-alist-p x)
                (m1-file-alist-p y)
                (hifat-no-dups-p x)
                (hifat-no-dups-p y)
                (hifat-subsetp x y)
                (hifat-subsetp y x)
                (hifat-no-dups-p (m1-file->contents file)))
           (and (hifat-subsetp (mv-nth 0 (hifat-place-file y path file))
                               (mv-nth 0 (hifat-place-file x path file)))
                (equal (mv-nth 1 (hifat-place-file y path file))
                       (mv-nth 1 (hifat-place-file x path file)))))
  :hints (("goal" :in-theory (enable hifat-place-file hifat-subsetp))))

;; This isn't a congruence rule, so it may have to be left disabled...
(defthm
  hifat-place-file-correctness-4
  (implies
   (and (hifat-equiv m1-file-alist2 m1-file-alist1)
        (syntaxp (not (term-order m1-file-alist1 m1-file-alist2)))
        (hifat-no-dups-p (m1-file->contents file)))
   (and
    (equal (mv-nth 1
                   (hifat-place-file m1-file-alist2 path file))
           (mv-nth 1
                   (hifat-place-file m1-file-alist1 path file)))
    (hifat-equiv (mv-nth 0
                         (hifat-place-file m1-file-alist2 path file))
                 (mv-nth 0
                         (hifat-place-file m1-file-alist1 path file)))))
  :hints
  (("goal" :in-theory (enable hifat-place-file hifat-equiv)
    :use ((:instance (:rewrite hifat-place-file-correctness-lemma-1)
                     (x (hifat-file-alist-fix m1-file-alist2))
                     (file file)
                     (path path)
                     (y (hifat-file-alist-fix m1-file-alist1)))
          (:instance (:rewrite hifat-place-file-correctness-lemma-1)
                     (x (hifat-file-alist-fix m1-file-alist1))
                     (file file)
                     (path path)
                     (y (hifat-file-alist-fix m1-file-alist2))))
    :do-not-induct t)))

(defthm
  absfat-place-file-correctness-lemma-4
  (implies
   (subsetp-equal
    (abs-addrs root)
    (frame-addrs-root
     (cons (cons x
                 (frame-val nil
                            (put-assoc-equal (car (last path))
                                             file dir)
                            src))
           frame)))
   (subsetp-equal (abs-addrs root)
                  (frame-addrs-root (cons (cons x (frame-val 'nil dir src))
                                          frame))))
  :hints
  (("goal" :do-not-induct t
    :in-theory
    (e/d (hifat-equiv-when-absfat-equiv dist-names
                                        abs-separate frame-addrs-root)
         nil)))
  :otf-flg t)

(defthm
  absfat-place-file-correctness-lemma-5
  (implies
   (and
    (hifat-equiv
     (mv-nth
      0
      (collapse
       (frame-with-root
        root
        (cons (cons x
                    (frame-val nil
                               (put-assoc-equal (car (last path))
                                                file dir)
                               src))
              frame))))
     (mv-nth
      0
      (hifat-place-file
       fs nil
       (m1-file
        (m1-file->dir-ent
         (mv-nth
          0
          (hifat-find-file
           (mv-nth
            0
            (collapse (frame-with-root root
                                       (cons (cons x (frame-val nil dir src))
                                             frame))))
           nil)))
        (put-assoc-equal (car (last path))
                         file dir)))))
    (equal (mv-nth 1
                   (hifat-place-file fs nil
                                     (put-assoc-equal (car (last path))
                                                      file dir)))
           0))
   (hifat-equiv
    (mv-nth
     0
     (collapse
      (frame-with-root
       root
       (cons (cons x
                   (frame-val nil
                              (put-assoc-equal (car (last path))
                                               file dir)
                              src))
             frame))))
    (mv-nth 0 (hifat-place-file fs path file))))
  :instructions
  (:promote
   (:=
    (mv-nth
     0
     (collapse
      (frame-with-root
       root
       (cons (cons x
                   (frame-val nil
                              (put-assoc-equal (car (last path))
                                               file dir)
                              src))
             frame))))
    (mv-nth
     0
     (hifat-place-file
      fs nil
      (m1-file
       (m1-file->dir-ent
        (mv-nth
         0
         (hifat-find-file
          (mv-nth
           0
           (collapse (frame-with-root root
                                      (cons (cons x (frame-val nil dir src))
                                            frame))))
          nil)))
       (put-assoc-equal (car (last path))
                        file dir))))
    :equiv hifat-equiv)
   (:bash ("goal" :in-theory (enable hifat-place-file)))))

(defthm absfat-place-file-correctness-lemma-6
  (implies (and (abs-fs-p dir)
                (not (member-equal (car (last path))
                                   (names-at dir nil))))
           (not (consp (assoc-equal (car (last path))
                                    dir))))
  :hints (("goal" :in-theory (enable names-at))))

(defthm abs-file-p-when-m1-file-p
  (implies (m1-file-p file)
           (abs-file-p file))
  :hints (("goal" :cases ((abs-directory-file-p file)))))

(defthm
  m1-file-p-of-abs-file
  (equal (m1-file-p (abs-file dir-ent contents))
         (or (stringp (abs-file-contents-fix contents))
             (m1-file-alist-p contents)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable m1-file-p abs-file abs-file-contents-fix
                              abs-file-contents-p
                              m1-file-contents-p))))

(defthm
  m1-file-alist-p-of-abs-place-file-helper
  (implies
   (and (abs-complete (abs-fs-fix fs))
        (m1-file-p (abs-no-dups-file-fix file)))
   (m1-file-alist-p (mv-nth 0
                            (abs-place-file-helper fs path file))))
  :hints (("goal" :in-theory (enable abs-place-file-helper))))

(defthm abs-place-file-helper-of-abs-fs-fix
  (equal (abs-place-file-helper (abs-fs-fix fs) path file)
         (abs-place-file-helper fs path file))
  :hints (("goal" :in-theory (enable abs-place-file-helper))))

(defthm abs-place-file-helper-of-abs-no-dups-file-fix
  (equal (abs-place-file-helper fs path (abs-no-dups-file-fix file))
         (abs-place-file-helper fs path file))
  :hints (("goal" :in-theory (enable abs-place-file-helper))))

(encapsulate
  ()

  (local
   (defthm
     lemma
     (implies (and (m1-file-alist-p fs)
                   (hifat-no-dups-p fs)
                   ;; This hypothesis is suboptimal... I know.
                   (m1-file-p file)
                   (abs-no-dups-file-p file))
              (equal (abs-place-file-helper fs path file)
                     (hifat-place-file fs path file)))
     :hints
     (("goal"
       :in-theory (enable abs-place-file-helper hifat-place-file
                          abs-file m1-file abs-file->dir-ent
                          m1-file->dir-ent abs-fs-p)
       :induct (abs-place-file-helper fs path file)))))

  (defthm
    abs-place-file-helper-correctness-1
    (implies (and (abs-complete (abs-fs-fix fs))
                  (m1-file-p (abs-no-dups-file-fix file)))
             (equal (abs-place-file-helper fs path file)
                    (hifat-place-file (abs-fs-fix fs)
                                      path (abs-no-dups-file-fix file))))
    :hints (("goal" :in-theory (disable lemma)
             :use (:instance lemma
                             (fs (abs-fs-fix fs))
                             (file (abs-no-dups-file-fix file)))))))

(defthm
  abs-top-addrs-of-abs-place-file-helper
  (equal (abs-top-addrs (mv-nth 0
                                (abs-place-file-helper fs path file)))
         (abs-top-addrs fs))
  :hints (("goal" :in-theory (enable abs-top-addrs abs-place-file-helper))))

(defthm
  addrs-at-of-abs-place-file-helper-lemma-1
  (implies (and (m1-file-p file)
                (or (m1-regular-file-p file)
                    (hifat-no-dups-p (m1-file->contents file))))
           (not (addrs-at (m1-file->contents file)
                          (cdr relpath))))
  :hints
  (("goal" :in-theory
    (e/d (m1-file-contents-p addrs-at m1-regular-file-p
                             m1-file-p m1-file->contents abs-fs-fix)
         (m1-file-contents-p-of-m1-file->contents))
    :use (:instance m1-file-contents-p-of-m1-file->contents
                    (x file))
    :do-not-induct t))
  :otf-flg t)

(defthm
  addrs-at-of-abs-place-file-helper-1
  (implies (and (abs-file-p file)
                (abs-no-dups-p (abs-file->contents file)))
           (equal (addrs-at (mv-nth 0
                                    (abs-place-file-helper fs path file))
                            relpath)
                  (if (and
                       (zp (mv-nth 1
                                   (abs-place-file-helper fs path file)))
                       (prefixp (fat32-filename-list-fix path)
                                (fat32-filename-list-fix relpath)))
                      (addrs-at (abs-file->contents (abs-no-dups-file-fix file))
                                (nthcdr (len path) relpath))
                    (addrs-at fs relpath))))
  :hints
  (("goal"
    :in-theory (enable abs-place-file-helper addrs-at)
    :induct (mv (fat32-filename-list-prefixp relpath path)
                (addrs-at fs relpath))
    :expand
    ((abs-place-file-helper fs path file)
     (addrs-at
      (put-assoc-equal
       (fat32-filename-fix (car path))
       (abs-file
        (abs-file->dir-ent
         (cdr (assoc-equal (fat32-filename-fix (car path))
                           fs)))
        (mv-nth
         0
         (abs-place-file-helper
          (abs-file->contents
           (cdr (assoc-equal (fat32-filename-fix (car path))
                             fs)))
          (cdr path)
          file)))
       fs)
      relpath)))))

(defthm natp-of-abs-place-file-helper
  (natp (mv-nth 1
                (abs-place-file-helper fs path file)))
  :hints (("goal" :in-theory (enable abs-place-file-helper)))
  :rule-classes :type-prescription)

(defthm abs-place-file-helper-correctness-2
  (implies (not (zp (mv-nth 1
                            (abs-place-file-helper fs path file))))
           (equal (mv-nth 0
                          (abs-place-file-helper fs path file))
                  (abs-fs-fix fs)))
  :hints (("goal" :in-theory (enable abs-place-file-helper))))

(encapsulate
  ()

  (local
   (defthmd lemma
     (implies
      (and (abs-file-p file)
           (abs-no-dups-p (abs-file->contents file)))
      (equal (ctx-app-ok (mv-nth 0
                                 (abs-place-file-helper fs path file))
                         x x-path)
             (if (and (zp (mv-nth 1
                                  (abs-place-file-helper fs path file)))
                      (prefixp (fat32-filename-list-fix path)
                               (fat32-filename-list-fix x-path)))
                 (ctx-app-ok (abs-file->contents (abs-no-dups-file-fix file))
                             x (nthcdr (len path) x-path))
               (ctx-app-ok fs x x-path))))
     :hints (("goal" :in-theory (enable ctx-app-ok)
              :do-not-induct t))
     :otf-flg t))

  (defthm
    ctx-app-ok-of-abs-place-file-helper-1
    (equal (ctx-app-ok (mv-nth 0 (abs-place-file-helper fs path file))
                       x x-path)
           (if (and (zp (mv-nth 1 (abs-place-file-helper fs path file)))
                    (prefixp (fat32-filename-list-fix path)
                             (fat32-filename-list-fix x-path)))
               (ctx-app-ok (abs-file->contents (abs-no-dups-file-fix file))
                           x (nthcdr (len path) x-path))
             (ctx-app-ok fs x x-path)))
    :hints (("goal" :use (:instance lemma
                                    (file (abs-no-dups-file-fix file)))))))

(defthm natp-of-abs-place-file-helper
  (natp (mv-nth 1
                (abs-place-file-helper fs path file)))
  :hints (("goal" :in-theory (enable abs-place-file-helper)))
  :rule-classes :type-prescription)

(defthm names-at-of-abs-place-file-helper-lemma-1
  (implies (and (abs-file-p file)
                (not (abs-directory-file-p file)))
           (not (names-at (abs-file->contents file)
                          (nthcdr 1 relpath))))
  :hints (("goal" :in-theory (enable names-at abs-directory-file-p
                                     abs-file-p abs-file->contents
                                     abs-file-contents-p abs-fs-fix)
           :do-not-induct t)))

(defthm
  names-at-of-abs-place-file-helper-lemma-2
  (implies (m1-regular-file-p file)
           (not (names-at (m1-file->contents file)
                          (nthcdr 1 relpath))))
  :hints (("goal" :in-theory (enable names-at
                                     abs-directory-file-p m1-regular-file-p
                                     abs-file-p abs-file->contents
                                     abs-file-contents-p abs-fs-fix)
           :do-not-induct t)))

(defthm names-at-of-abs-place-file-helper-lemma-5
  (implies (m1-regular-file-p file)
           (equal (strip-cars (abs-fs-fix (m1-file->contents file)))
                  nil))
  :hints (("goal" :do-not-induct t
           :in-theory (enable m1-regular-file-p
                              abs-file-p abs-file->contents
                              abs-fs-fix abs-file-contents-p))))

(defthmd names-at-of-abs-place-file-helper-lemma-6
  (implies (not (m1-regular-file-p (abs-no-dups-file-fix file)))
           (abs-directory-file-p (abs-no-dups-file-fix file)))
  :hints
  (("goal" :in-theory (e/d (abs-file-p-alt)
                           ((:rewrite abs-file-p-when-abs-no-dups-file-p)))
    :use (:instance (:rewrite abs-file-p-when-abs-no-dups-file-p)
                    (file (abs-no-dups-file-fix file))))))

(defthm
  names-at-of-abs-place-file-helper-1
  (equal (names-at (mv-nth 0 (abs-place-file-helper fs path file))
                   relpath)
         (cond ((not (zp (mv-nth 1
                                 (abs-place-file-helper fs path file))))
                (names-at fs relpath))
               ((fat32-filename-list-prefixp path relpath)
                (names-at (abs-file->contents (abs-no-dups-file-fix file))
                          (nthcdr (len path) relpath)))
               ((and (fat32-filename-list-equiv relpath (butlast path 1))
                     (not (member-equal (fat32-filename-fix (car (last path)))
                                        (names-at fs relpath))))
                (append (names-at fs relpath)
                        (list (fat32-filename-fix (car (last path))))))
               (t (names-at fs relpath))))
  :hints
  (("goal"
    :in-theory
    (e/d (abs-place-file-helper names-at fat32-filename-list-fix
                                fat32-filename-list-equiv
                                fat32-filename-equiv
                                names-at-of-abs-place-file-helper-lemma-6)
         ((:definition put-assoc-equal)
          (:rewrite ctx-app-ok-when-absfat-equiv-lemma-3)
          (:definition abs-complete)
          (:rewrite hifat-find-file-correctness-1-lemma-1)
          (:type-prescription assoc-equal-when-frame-p)
          (:definition assoc-equal)
          (:definition no-duplicatesp-equal)
          (:rewrite m1-file-alist-p-when-subsetp-equal)
          (:rewrite subsetp-when-prefixp)))
    :induct (mv (fat32-filename-list-prefixp relpath path)
                (names-at fs relpath))
    :expand (abs-place-file-helper fs path file))))

;; This is based on collapse-hifat-place-file-2, which relies on the lemma
;; collapse-hifat-place-file-lemma-6. That lemma would probably have to be tweaked to
;; deal with all the path appending stuff, which I'm skipping over for now.
(skip-proofs
 (defthm
   collapse-hifat-place-file-2
   (implies
    (and
     (m1-file-p file)
     (or (m1-regular-file-p file)
         (hifat-no-dups-p (m1-file->contents file)))
     (dist-names (frame->root (frame-with-root root frame))
                 nil
                 (frame->frame (frame-with-root root frame)))
     (abs-separate (frame->frame (frame-with-root root frame)))
     (frame-p (frame->frame (frame-with-root root frame)))
     (no-duplicatesp-equal
      (strip-cars (frame->frame (frame-with-root root frame))))
     (consp (assoc-equal x frame)))
    (and
     (equal
      (mv-nth
       0
       (collapse
        (frame-with-root
         root
         (put-assoc-equal
          x
          (frame-val
           (frame-val->path (cdr (assoc-equal x frame)))
           (mv-nth
            0
            (abs-place-file-helper
             (frame-val->dir (cdr (assoc-equal x frame)))
             path file))
           (frame-val->src (cdr (assoc-equal x frame))))
          frame))))
      (mv-nth
       0
       (abs-place-file-helper
        (mv-nth 0
                (collapse (frame-with-root root frame)))
        (append (frame-val->path (cdr (assoc-equal x frame)))
                path)
        file)))
     (equal
      (mv-nth
       1
       (collapse
        (frame-with-root
         root
         (put-assoc-equal
          x
          (frame-val
           (frame-val->path (cdr (assoc-equal x frame)))
           (mv-nth
            0
            (abs-place-file-helper
             (frame-val->dir (cdr (assoc-equal x frame)))
             path file))
           (frame-val->src (cdr (assoc-equal x frame))))
          frame))))
      (mv-nth 1
              (collapse (frame-with-root root frame))))))))

;; I guess I should say that this function can only really do so much, and if
;; we try to use this in our proofs we'll kinda be back to representing
;; filesystem trees as... filesystem trees. When I say it can only do so much,
;; I mean that it can only help us do some refinement proofs, which will tie
;; lofat to hifat and hifat to absfat. Ultimately, I guess we'll want theorems
;; that use the collapse-equiv relation defined previously...
(defund frame-reps-fs
    (frame fs)
  (b*
      (((mv fs-equiv result) (collapse frame)))
    (and result
         (absfat-equiv fs-equiv fs)
         (frame-p frame)
         (abs-separate frame)
         (subsetp-equal
          (abs-addrs (frame->root frame))
          (frame-addrs-root (frame->frame frame)))
         (no-duplicatesp-equal (strip-cars frame))
         (atom (frame-val->path (cdr (assoc-equal 0 frame)))))))

(defcong absfat-equiv equal (frame-reps-fs frame fs) 2
  :hints (("Goal" :in-theory (enable frame-reps-fs))))

(defund abs-lstat (frame path)
  (declare
   (xargs
    :guard (and (fat32-filename-list-p path)
                (frame-p frame))
    :guard-debug t
    :guard-hints
    (("goal"
      :in-theory (e/d (abs-file-p-alt)
                      ((:rewrite abs-file-p-of-abs-find-file)))
      :use (:rewrite abs-file-p-of-abs-find-file)))))
  (b* (((mv file errno)
        (abs-find-file frame path))
       ((when (not (equal errno 0)))
        (mv (make-struct-stat) -1 errno))
       (st_size (if (abs-directory-file-p file)
                    *ms-max-dir-size*
                  (length (abs-file->contents file)))))
    (mv (make-struct-stat :st_size st_size)
        0 0)))

(defthm
  abs-lstat-refinement-lemma-1
  (implies (stringp (m1-file->contents (mv-nth 0 (hifat-find-file fs path))))
           (m1-regular-file-p (mv-nth '0 (hifat-find-file fs path)))))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies
      (and
       (frame-reps-fs frame fs)
       (abs-fs-p fs)
       (m1-file-alist-p fs)
       (consp (assoc-equal 0 frame))
       (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
       (frame-p frame)
       (no-duplicatesp-equal (strip-cars frame))
       (subsetp-equal (abs-addrs (frame->root frame))
                      (frame-addrs-root (frame->frame frame)))
       (abs-separate frame)
       (abs-complete (abs-file->contents (mv-nth 0 (abs-find-file frame path)))))
      (equal (abs-lstat frame path)
             (hifat-lstat fs path)))
     :hints (("goal" :do-not-induct t
              :in-theory (enable abs-lstat frame-reps-fs hifat-lstat)))))

  (defthm
    abs-lstat-refinement
    (implies
     (and
      (consp (assoc-equal 0 frame))
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (frame-p frame)
      (no-duplicatesp-equal (strip-cars frame))
      (abs-complete (abs-file->contents (mv-nth 0 (abs-find-file frame path))))
      (frame-reps-fs frame fs)
      (abs-fs-p fs))
     (equal (abs-lstat frame path)
            (hifat-lstat fs path)))
    :hints (("goal" :do-not-induct t
             :in-theory (enable frame-reps-fs)
             :use lemma))))

(defthm absfat-place-file-correctness-lemma-1
  (implies (m1-regular-file-p file)
           (abs-no-dups-file-p file))
  :hints (("goal" :in-theory (enable abs-no-dups-file-p))))

;; I'm not even sure what the definition of abs-place-file above should be. But
;; I'm pretty sure it should support a theorem like the following.
;;
;; In the hypotheses here, there has to be a stipulation that not only is dir
;; complete, but also that it's the only one which has any names at that
;; particular relpath, i.e. (butlast path 1). It's codified under
;; path-clear.
;;
;; Also, the use hints in this theorem are awkward but necessary - restrict
;; hints do not work because there's never a real chance for them to be
;; applied, or so :brr tells us.
;;
;; OK, so how do we develop a specification for abs-mkdir which we can actually
;; USE? Like, we would want to say that (abs-mkdir frame) is going to return a
;; new frame and an error code, and that error code will tell us whether to
;; expect an unchanged frame (modulo absfat-equiv) or a new frame with an
;; element right at the front representing the parent directory of the new
;; directory with the new directory inside it.
(defthm
  absfat-place-file-correctness-lemma-2
  (implies
   (and
    (m1-file-alist-p fs)
    (hifat-no-dups-p fs)
    (fat32-filename-list-p path)
    (m1-regular-file-p file)
    (abs-fs-p dir)
    (abs-complete dir)
    (path-clear (butlast path 1) frame)
    (atom (names-at root (butlast path 1)))
    (frame-reps-fs
     (frame-with-root root
                      (cons (cons x (frame-val (butlast path 1) dir src))
                            frame))
     fs)
    (not (member-equal (car (last path))
                       (names-at dir nil)))
    (consp path))
   (b*
       ((dir (put-assoc-equal (car (last path))
                              file dir))
        (frame
         (frame-with-root root
                          (cons (cons x (frame-val (butlast path 1) dir src))
                                frame)))
        ((mv fs &)
         (hifat-place-file fs path file)))
     (frame-reps-fs frame fs)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (e/d (hifat-place-file dist-names abs-separate
                           frame-addrs-root frame-reps-fs)
         (collapse-hifat-place-file-2
          (:rewrite m1-file-alist-p-when-subsetp-equal)
          (:rewrite len-of-remove-assoc-when-no-duplicatesp-strip-cars)
          (:linear len-of-remove-assoc-1)
          (:definition remove-assoc-equal)
          (:rewrite subsetp-trans)
          (:rewrite abs-addrs-of-put-assoc-lemma-2)
          member-of-abs-addrs-when-natp
          (:linear position-equal-ac-when-member)
          (:rewrite 1st-complete-of-put-assoc-lemma-1)
          (:definition hifat-file-alist-fix)
          (:rewrite hifat-find-file-correctness-1-lemma-1)
          (:type-prescription ctx-app-list-when-set-equiv-lemma-4)
          (:rewrite m1-directory-file-p-when-m1-file-p)
          (:rewrite abs-no-dups-p-of-put-assoc-equal)
          (:rewrite nthcdr-when->=-n-len-l)
          (:rewrite ctx-app-ok-when-absfat-equiv-lemma-3)
          (:type-prescription assoc-when-zp-len)
          (:definition take)
          (:rewrite take-of-len-free)
          (:rewrite take-of-too-many)
          (:definition true-listp)
          (:rewrite true-listp-when-string-list)
          (:definition string-listp)))
    :use
    ((:instance collapse-hifat-place-file-2
                (frame (cons (cons x (frame-val (butlast path 1) dir src))
                             frame))
                (path (last path)))))))

(defthm
  frame-p-of-abs-place-file
  (implies (frame-p frame)
           (frame-p (mv-nth 0 (abs-place-file
                               frame
                               path
                               file))))
  :hints (("Goal" :in-theory (enable abs-place-file))))

(defund
  abs-remove-file (frame path)
  (declare
   (xargs :guard (and (frame-p frame)
                      (fat32-filename-list-p path))
          :guard-hints (("Goal" :do-not-induct t) )))
  (b*
      (((when (atom frame))
        (mv frame *enoent*))
       (path (mbe :exec path
                      :logic (fat32-filename-list-fix path)))
       ((mv tail tail-error-code)
        (abs-remove-file (cdr frame) path))
       ((unless (and (equal tail-error-code *ENOENT*)
                     (prefixp (frame-val->path (cdar frame))
                              path)))
        (mv (list* (car frame) tail) tail-error-code))
       ;; Look up the parent directory - it has to be in one of the variables,
       ;; or else we must return ENOENT.
       ((mv & error-code)
        (abs-find-file-helper
         (frame-val->dir (cdar frame))
         (nthcdr (len (frame-val->path (cdar frame)))
                 (butlast path 1))))
       ((when (or (equal error-code *enoent*)
                  (not (abs-complete (frame-val->dir (cdar frame))))))
        (mv (list* (car frame) tail) tail-error-code))
       ((mv head head-error-code)
        (hifat-remove-file (frame-val->dir (cdar frame)) path)))
    (mv
     (list* (cons (caar frame) (change-frame-val (cdar frame) :dir head))
            (cdr frame))
     head-error-code)))

(defthm abs-mkdir-guard-lemma-1
  (implies (consp (assoc-equal 0 frame))
           (consp (assoc-equal 0 (partial-collapse frame path))))
  :hints (("goal" :in-theory (enable partial-collapse))))

;; This deliberately follows an almost-identical induction scheme to
;; abs-find-file. It was going to be a part of that function, but that just led
;; to too many failures.
(defund
  abs-find-file-src (frame path)
  (declare
   (xargs :guard (and (frame-p frame)
                      (fat32-filename-list-p path))))
  (b*
      (((when (atom frame)) 0)
       (path (mbe :exec path
                      :logic (fat32-filename-list-fix path)))
       ((unless (prefixp (frame-val->path (cdar frame))
                         path))
        (abs-find-file-src (cdr frame) path))
       ((mv & error-code)
        (abs-find-file-helper
         (frame-val->dir (cdar frame))
         (nthcdr (len (frame-val->path (cdar frame)))
                 path)))
       ((when (not (equal error-code *enoent*)))
        (mbe :exec (caar frame) :logic (nfix (caar frame)))))
    (abs-find-file-src (cdr frame) path)))

(defthm
  abs-find-file-src-correctness-2
  (implies
   (and (frame-p frame)
        (no-duplicatesp-equal (strip-cars frame))
        (not (equal (mv-nth 1 (abs-find-file frame path))
                    *enoent*)))
   (and
    (consp (assoc-equal (abs-find-file-src frame path)
                        frame))
    (prefixp
     (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                        frame)))
     (fat32-filename-list-fix path))
    (equal
     (abs-find-file-helper
      (frame-val->dir (cdr (assoc-equal (abs-find-file-src frame path)
                                        frame)))
      (nthcdr (len (frame-val->path
                    (cdr (assoc-equal (abs-find-file-src frame path)
                                      frame))))
              path))
     (abs-find-file frame path))))
  :hints (("goal" :in-theory (enable abs-find-file abs-find-file-src)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (frame-p frame)
          (no-duplicatesp-equal (strip-cars frame))
          (not (equal (mv-nth 1 (abs-find-file frame path))
                      *enoent*)))
     (and
      (prefixp
       (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                          frame)))
       (fat32-filename-list-fix path))
      (equal
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal (abs-find-file-src frame path)
                                          frame)))
        (nthcdr
         (len (frame-val->path
               (cdr (assoc-equal (abs-find-file-src frame path)
                                 frame))))
         path))
       (abs-find-file frame path)))))))

(encapsulate ()

  (local
   (defthm
     lemma
     (implies (not (zp (abs-find-file-src frame path)))
              (consp (assoc-equal (abs-find-file-src frame path)
                                  frame)))
     :hints (("goal" :in-theory (enable abs-find-file abs-find-file-src)))))

  (defthm
    abs-find-file-src-correctness-1
    (implies (consp (assoc-equal 0 frame))
             (consp (assoc-equal (abs-find-file-src frame path)
                                 frame)))
    :hints (("goal" :in-theory (enable abs-find-file abs-find-file-src)))
    :rule-classes
    ((:rewrite
      :corollary
      (implies (or (not (zp (abs-find-file-src frame path)))
                   (consp (assoc-equal 0 frame))
                   (and (frame-p frame)
                        (no-duplicatesp-equal (strip-cars frame))
                        (not (equal (mv-nth 1 (abs-find-file frame path))
                                    *enoent*))))
               (consp (assoc-equal (abs-find-file-src frame path)
                                   frame)))
      :hints
      (("goal" :in-theory (disable
                           abs-find-file-src-correctness-2)
        :use
        abs-find-file-src-correctness-2))))))

(defthmd
  abs-find-file-src-of-fat32-filename-list-fix
  (equal
   (abs-find-file-src frame (fat32-filename-list-fix path))
   (abs-find-file-src frame path))
  :hints (("Goal" :in-theory (enable abs-find-file-src))))

(defcong
  fat32-filename-list-equiv
  equal (abs-find-file-src frame path)
  2
  :hints
  (("goal"
    :use
    ((:instance abs-find-file-src-of-fat32-filename-list-fix
                (path path-equiv))
     abs-find-file-src-of-fat32-filename-list-fix))))

(defthm
  abs-find-file-src-of-frame-with-root
  (equal (abs-find-file-src (frame-with-root root frame)
                            path)
         (if (equal (mv-nth 1 (abs-find-file-helper root path))
                    2)
             (abs-find-file-src frame path)
             0))
  :hints (("goal" :do-not-induct t
           :in-theory (enable abs-find-file-src frame-with-root))))

(defthm abs-mkdir-guard-lemma-5
  (implies (abs-no-dups-p fs)
           (no-duplicatesp-equal (remove-equal nil (strip-cars fs))))
  :hints (("goal" :in-theory (enable abs-no-dups-p))))

(defthm
  abs-mkdir-guard-lemma-7
  (implies
   (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs path)))
   (abs-no-dups-p
    (abs-file->contents (mv-nth 0 (abs-find-file-helper fs path)))))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm
  abs-mkdir-guard-lemma-8
  (implies
   (abs-directory-file-p (mv-nth 0 (abs-find-file frame path)))
   (abs-no-dups-p
    (abs-file->contents (mv-nth 0 (abs-find-file frame path)))))
  :hints (("goal" :in-theory (enable abs-find-file))))

;; OK, here's the plan for defining abs-mkdir. We can proooobably get rid of
;; abs-place-file and abs-remove-file, since those tasks are going to be
;; accomplished by first bringing the parent directory to the front and then
;; doing a put-assoc or a remove-assoc respectively.
(defund abs-mkdir (frame path)
  (declare (xargs :guard (and (frame-p frame)
                              (consp (assoc-equal 0 frame))
                              (fat32-filename-list-p path)
                              (no-duplicatesp-equal (strip-cars frame)))
                  :guard-debug t
                  :guard-hints
                  (("goal"
                    :in-theory (enable abs-find-file-helper abs-fs-p)))))
  (b*
      ((path (mbe :exec path :logic (fat32-filename-list-fix path)))
       (dirname (dirname path)) (frame (partial-collapse frame dirname))
       ;; After partial-collapse, either the parent directory is there in one
       ;; variable, or it isn't there at all.
       ((mv parent-dir error-code) (abs-find-file frame dirname))
       ((unless (or (atom dirname) (and (zp error-code) (abs-directory-file-p parent-dir))))
        (mv frame -1 *enoent*))
       (src (abs-find-file-src frame dirname))
       (new-index (find-new-index
                   ;; Using this, not (strip-cars (frame->frame frame)), to make
                   ;; sure we don't get a zero.
                   (strip-cars frame)))
       ;; It's not even a matter of removing that thing - we need to leave a
       ;; body address in its place...
       ((mv var new-src-dir)
        (abs-alloc (frame-val->dir (cdr (assoc-equal src frame)))
                   (nthcdr (len (frame-val->path (cdr (assoc-equal src frame)))) dirname)
                   new-index))
       ;; Check somewhere that (basename path) is not already present...
       ((unless (consp path)) (mv frame -1 *enoent*))
       ((when (consp (abs-assoc (basename path) var))) (mv frame -1 *eexist*))
       (frame (put-assoc-equal src (change-frame-val (cdr (assoc-equal src frame))
                                                     :dir new-src-dir)
                               frame))
       (new-var (abs-put-assoc (basename path)
                               (make-abs-file :contents nil
                                              :dir-ent (dir-ent-install-directory-bit
                                                        (dir-ent-fix nil) t))
                               var))
       (frame
        (frame-with-root (frame->root frame)
                         (cons (cons new-index
                                     (frame-val dirname
                                                new-var src))
                               (frame->frame frame)))))
    (mv frame 0 0)))

;; An example demonstrating that both ways of doing mkdir work out the same:
(assert-event
 (equal
  (b*
      ((fs (list (cons (implode (name-to-fat32-name (explode "tmp")))
                       (make-m1-file :contents nil))))
       (frame (frame-with-root fs nil))
       (result1 (frame-reps-fs frame fs))
       ((mv frame & &) (abs-mkdir frame (path-to-fat32-path (explode "/tmp/docs"))))
       ((mv frame error-code result3)
        (abs-mkdir frame
                   (path-to-fat32-path (explode "/tmp/docs/pdf-docs"))))
       ((mv frame result4) (collapse frame)))
    (list (m1-file-alist-p fs) result1 error-code result3 frame
          result4))
  '(T
    T 0 0
    (("TMP        "
      (DIR-ENT 0 0 0 0 0 0 0 0 0 0 0 0
               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
      (CONTENTS
       ("DOCS       "
        (DIR-ENT 0 0 0 0 0 0 0 0 0 0 0 16
                 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
        (CONTENTS
         ("PDF-DOCS   " (DIR-ENT 0 0 0 0 0 0 0 0 0 0 0 16
                                 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
          (CONTENTS)))))))
    T)))

(assert-event
 (equal
  (b*
      ((fs (list (cons (implode (name-to-fat32-name (explode "tmp")))
                       (make-m1-file :contents nil))))
       ((mv fs & &) (hifat-mkdir fs (path-to-fat32-path (explode "/tmp/docs"))))
       ((mv fs & &)
        (hifat-mkdir fs
                     (path-to-fat32-path (explode "/tmp/docs/pdf-docs")))))
    (list fs))
  '((("TMP        "
      (DIR-ENT 0 0 0 0 0 0 0 0 0 0 0 0
               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
      (CONTENTS
       ("DOCS       "
        (DIR-ENT 0 0 0 0 0 0 0 0 0 0 0 16
                 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
        (CONTENTS
         ("PDF-DOCS   " (DIR-ENT 0 0 0 0 0 0 0 0 0 0 0 16
                                 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
          (CONTENTS))))))))))

(defthm
  abs-mkdir-correctness-lemma-8
  (not (consp (assoc-equal (find-new-index (strip-cars alist))
                           alist)))
  :hints (("goal" :in-theory (disable member-of-strip-cars)
           :use (:instance member-of-strip-cars
                           (x (find-new-index (strip-cars alist))))))
  :rule-classes (:rewrite :type-prescription))

(defthm
  abs-mkdir-correctness-lemma-9
  (implies
   (consp (assoc-equal 0 alist))
   (not (equal (find-new-index (strip-cars alist)) 0)))
  :hints (("Goal" :in-theory
           (disable
            abs-mkdir-correctness-lemma-8)
           :use
           abs-mkdir-correctness-lemma-8))
  :rule-classes
  (:rewrite
   (:linear
    :corollary
    (implies
     (consp (assoc-equal 0 alist))
     (< 0 (find-new-index (strip-cars alist)))))
   (:type-prescription
    :corollary
    (implies
     (consp (assoc-equal 0 alist))
     (< 0 (find-new-index (strip-cars alist)))))))

(defthm abs-mkdir-correctness-lemma-11
  (equal (frame->root (put-assoc-equal 0 val frame))
         (frame-val->dir val))
  :hints (("goal" :do-not-induct t
           :in-theory (enable frame->root))))

(defthm abs-mkdir-correctness-lemma-12
  (equal (frame->frame (put-assoc-equal 0 val frame))
         (frame->frame frame))
  :hints (("goal" :do-not-induct t
           :in-theory (enable frame->frame))))

(defthm
  abs-mkdir-correctness-lemma-14
  (implies (and (consp (assoc-equal 0 frame))
                (not (consp (assoc-equal x frame))))
           (not (consp (assoc-equal x (partial-collapse frame path)))))
  :hints (("goal" :in-theory (enable partial-collapse collapse-this
                                     assoc-equal-of-frame-with-root
                                     assoc-equal-of-frame->frame)
           :induct (partial-collapse frame path))))

(defthm
  abs-mkdir-correctness-lemma-15
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
                                  assoc-equal-of-frame->frame)
                ((:definition remove-assoc-equal)
                 (:rewrite remove-assoc-when-absent-1)
                 (:rewrite remove-assoc-of-put-assoc)
                 (:rewrite subsetp-when-prefixp)
                 (:rewrite abs-fs-fix-when-abs-fs-p)
                 (:rewrite abs-fs-p-when-hifat-no-dups-p)
                 (:definition abs-complete)
                 (:rewrite remove-assoc-of-remove-assoc)
                 (:definition len)))
           :induct (partial-collapse frame path))))

(defthmd
  abs-mkdir-correctness-lemma-16
  (implies (not (consp (dirname path)))
           (equal (dirname path) nil))
  :hints (("goal" :in-theory (enable dirname)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (zp (len (dirname path)))
             (equal (dirname path) nil))
    :hints (("goal" :in-theory (disable len-of-dirname))))))

(defthm abs-mkdir-correctness-lemma-17
  (implies (atom path)
           (equal (abs-find-file-src frame path)
                  0))
  :hints (("goal" :in-theory (enable abs-find-file-src
                                     abs-find-file-helper))))

(defthm
  abs-mkdir-correctness-lemma-18
  (implies
   (and (no-duplicatesp-equal (strip-cars frame))
        (frame-p frame)
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (mv-nth 1 (collapse frame))
        (abs-separate frame)
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame))))
   (hifat-equiv
    (mv-nth 0
            (collapse (partial-collapse frame (dirname path))))
    (mv-nth 0 (collapse frame))))
  :hints
  (("goal" :in-theory (disable (:rewrite partial-collapse-correctness-1 . 1))
    :use (:instance (:rewrite partial-collapse-correctness-1 . 1)
                    (path (dirname path))
                    (frame frame)))))

(defthm
  abs-mkdir-correctness-lemma-20
  (ctx-app-ok
   (list (find-new-index
          (strip-cars (partial-collapse frame (dirname path)))))
   (find-new-index
    (strip-cars (partial-collapse frame (dirname path))))
   nil)
  :hints (("goal" :in-theory (enable ctx-app-ok addrs-at abs-fs-fix)
           :do-not-induct t)))

(defthm
  abs-mkdir-correctness-lemma-84
  (implies
   (and
    (fat32-filename-list-prefixp x y)
    (zp (mv-nth 1 (abs-find-file-helper fs x)))
    (not
     (consp
      (abs-addrs
       (abs-file->contents (mv-nth 0 (abs-find-file-helper fs x)))))))
   (not (consp (addrs-at fs y))))
  :hints
  (("goal" :in-theory
    (e/d (abs-find-file-helper addrs-at fat32-filename-list-prefixp)
         (ctx-app-ok-when-abs-complete-lemma-4))
    :induct (mv (fat32-filename-list-prefixp x y)
                (mv-nth 0 (abs-find-file-helper fs x))))
   ("subgoal *1/1'''"
    :use
    (:instance
     ctx-app-ok-when-abs-complete-lemma-4
     (fs (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car x))
                                               (abs-fs-fix fs)))))
     (relpath (cdr y))))))

(defthm
  abs-mkdir-correctness-lemma-25
  (implies
   (and
    (equal (mv-nth 1
                   (abs-find-file-helper (frame->root frame)
                                         path))
           2)
    (prefixp
     (fat32-filename-list-fix path)
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame)))))
    (equal
     (mv-nth
      1
      (abs-find-file
       (remove-assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))
       path))
     2)
    (ctx-app-ok
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (1st-complete (frame->frame frame))
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (m1-regular-file-p (mv-nth 0 (abs-find-file frame path))))
   (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (fat32-filename-list-prefixp-alt ctx-app-ok)
                    (abs-mkdir-correctness-lemma-84
                     abs-find-file-of-put-assoc-lemma-7
                     (:rewrite abs-addrs-when-m1-file-alist-p)
                     (:rewrite partial-collapse-correctness-lemma-24)
                     (:definition assoc-equal)
                     (:rewrite remove-when-absent)
                     (:definition remove-equal)
                     (:rewrite abs-file-alist-p-correctness-1)
                     (:rewrite abs-fs-p-when-hifat-no-dups-p)
                     (:rewrite prefixp-when-equal-lengths)
                     (:rewrite subsetp-when-prefixp)
                     (:definition no-duplicatesp-equal)))
    :use
    ((:instance
      abs-mkdir-correctness-lemma-84
      (x
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame)))))
        path))
      (y
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))))
      (fs
       (frame-val->dir
        (cdr (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (frame->frame frame))))))
     (:instance
      (:rewrite abs-find-file-of-put-assoc-lemma-6)
      (path path)
      (frame (frame->frame frame))
      (x (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame)))))))))
  :otf-flg t)

;; For whatever reason, it is not tempting to replace this. It has an inductive proof...
(defthmd
  abs-mkdir-correctness-lemma-26
  (implies
   (and (consp (assoc-equal 0 frame))
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (mv-nth 1 (collapse frame))
        (frame-p frame)
        (no-duplicatesp-equal (strip-cars frame))
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame)))
        (abs-separate frame))
   (equal
    (m1-regular-file-p (mv-nth 0 (abs-find-file frame path)))
    (m1-regular-file-p (mv-nth 0
                               (hifat-find-file (mv-nth 0 (collapse frame))
                                                path)))))
  :hints
  (("goal"
    :in-theory (e/d ((:definition abs-find-file)
                     collapse (:definition collapse-this)
                     len-of-fat32-filename-list-fix
                     abs-separate-of-frame->frame-of-collapse-this-lemma-10
                     different-from-own-src-1)
                    ((:rewrite partial-collapse-correctness-lemma-24)
                     (:definition remove-equal)
                     (:definition assoc-equal)
                     (:definition remove-assoc-equal)
                     (:rewrite abs-file-alist-p-correctness-1)
                     (:rewrite nthcdr-when->=-n-len-l)
                     (:rewrite abs-find-file-of-put-assoc-lemma-6)
                     (:rewrite subsetp-when-prefixp)
                     (:definition strip-cars)
                     abs-find-file-helper-of-collapse-3
                     abs-find-file-correctness-1-lemma-3
                     (:rewrite consp-of-nthcdr)
                     (:rewrite abs-find-file-helper-of-collapse-lemma-2)
                     (:rewrite partial-collapse-correctness-lemma-2)
                     (:rewrite put-assoc-equal-without-change . 2)
                     (:rewrite abs-find-file-correctness-lemma-14)
                     (:rewrite prefixp-when-equal-lengths)
                     (:definition put-assoc-equal)
                     (:rewrite abs-fs-p-when-hifat-no-dups-p)))
    :induct (collapse frame)
    :expand
    ((:with abs-find-file-of-put-assoc
            (:free (name val frame path)
                   (abs-find-file (put-assoc-equal name val frame)
                                  path)))
     (:with
      abs-find-file-of-remove-assoc-1
      (abs-find-file (remove-assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))
                     path))))
   ("subgoal *1/6.4'" :expand ((:free (x) (hide x))))))

(defthm
  abs-mkdir-correctness-lemma-27
 (implies
  (and (consp (assoc-equal 0 frame))
       (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
       (mv-nth 1 (collapse frame))
       (frame-p frame)
       (no-duplicatesp-equal (strip-cars frame))
       (subsetp-equal (abs-addrs (frame->root frame))
                      (frame-addrs-root (frame->frame frame)))
       (abs-separate frame))
  (equal
   (abs-directory-file-p (mv-nth 0 (abs-find-file frame path)))
   (m1-directory-file-p (mv-nth 0
                                (hifat-find-file (mv-nth 0 (collapse frame))
                                                 path)))))
 :hints
 (("goal"
   :do-not-induct t
   :in-theory
   (e/d
    (abs-file-p-alt)
    (abs-file-p-of-abs-find-file (:rewrite m1-regular-file-p-correctness-1)
                                 m1-directory-file-p-when-m1-file-p))
   :use
   (abs-file-p-of-abs-find-file
    abs-mkdir-correctness-lemma-26
    (:instance (:rewrite m1-regular-file-p-correctness-1)
               (file (mv-nth 0
                             (hifat-find-file (mv-nth 0 (collapse frame))
                                              path))))))
  ("subgoal 1"
   :expand
   (m1-regular-file-p (mv-nth 0
                              (hifat-find-file (mv-nth 0 (collapse frame))
                                               path))))))

(defthm
  abs-mkdir-correctness-lemma-28
  (not
   (intersectp-equal
    (names-at
     (frame-val->dir
      (cdr (assoc-equal 0
                        (partial-collapse frame (dirname path)))))
     nil)
    (names-at
     (list
      (find-new-index
       (strip-cars (partial-collapse frame (dirname path)))))
     nil)))
  :hints (("goal" :in-theory (enable names-at abs-fs-fix)
           :do-not-induct t)))

(defthm abs-mkdir-correctness-lemma-29
  (implies (atom n)
           (dist-names (list n) relpath frame))
  :hints (("goal" :in-theory (enable names-at abs-fs-fix dist-names))))

(defthm abs-mkdir-correctness-lemma-77
  (implies (atom n)
           (equal (names-at (list n) relpath) nil))
  :hints (("goal" :in-theory (enable names-at abs-fs-fix))))

(defthm
  abs-mkdir-correctness-lemma-78
  (implies (natp n)
           (ctx-app-ok (list n) n nil))
  :hints (("goal" :in-theory (enable ctx-app-ok addrs-at abs-fs-fix)
           :do-not-induct t)))

(defthm abs-mkdir-correctness-lemma-79
  (implies (not (consp (frame->frame frame)))
           (dist-names (frame->root frame)
                       nil (remove-assoc-equal 0 frame)))
  :hints (("goal" :in-theory (enable frame->frame))))

(defthm
  abs-mkdir-correctness-lemma-40
  (implies
   (and (no-duplicatesp-equal (strip-cars frame))
        (frame-p frame)
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (abs-separate frame)
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame))))
   (subsetp-equal
    (abs-addrs
     (frame-val->dir$inline
      (cdr (assoc-equal 0
                        (partial-collapse frame (dirname path))))))
    (frame-addrs-root
     (frame->frame (partial-collapse frame (dirname path))))))
  :hints
  (("goal"
    :do-not-induct t
    :cases
    ((not
      (equal
       (frame-val->dir
        (cdr (assoc-equal 0
                          (partial-collapse frame (dirname path)))))
       (frame->root (partial-collapse frame (dirname path)))))))
   ("subgoal 1" :in-theory (enable frame->root))))

(defthm
  abs-mkdir-correctness-lemma-41
  (implies (not (zp (abs-find-file-src frame path)))
           (consp (assoc-equal (abs-find-file-src frame path)
                               (frame->frame frame))))
  :hints
  (("goal" :in-theory (e/d (frame->frame)
                           ((:rewrite abs-find-file-src-correctness-1)))
    :use (:rewrite abs-find-file-src-correctness-1))))

(defthm
  abs-mkdir-correctness-lemma-42
  (implies
   (not (consp (assoc-equal x (frame->frame frame))))
   (not
    (consp (assoc-equal x
                        (frame->frame (partial-collapse frame path))))))
  :hints (("goal" :in-theory (enable partial-collapse))))

(defthm
  abs-mkdir-correctness-lemma-43
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

(defthm
  abs-mkdir-correctness-lemma-44
  (implies
   (and
    (no-duplicatesp-equal (strip-cars frame))
    (frame-p frame)
    (equal (frame-val->src (cdr (assoc-equal 0 frame)))
           0)
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (abs-separate frame)
    (subsetp-equal (abs-addrs (frame->root frame))
                   (frame-addrs-root (frame->frame frame)))
    (not
     (equal 0
            (abs-find-file-src
             (partial-collapse frame (dirname path))
             (dirname path)))))
   (subsetp-equal
    (abs-addrs
     (frame->root (partial-collapse frame (dirname path))))
    (frame-addrs-root
     (put-assoc-equal
      (abs-find-file-src
       (partial-collapse frame (dirname path))
       (dirname path))
      (frame-val
       (frame-val->path
        (cdr
         (assoc-equal
          (abs-find-file-src
           (partial-collapse frame (dirname path))
           (dirname path))
          frame)))
       (mv-nth
        1
        (abs-alloc
         (frame-val->dir
          (cdr
           (assoc-equal
            (abs-find-file-src
             (partial-collapse frame (dirname path))
             (dirname path))
            (partial-collapse frame (dirname path)))))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (abs-find-file-src
               (partial-collapse frame (dirname path))
               (dirname path))
              frame))))
          (dirname path))
         (find-new-index
          (strip-cars
           (partial-collapse frame (dirname path))))))
       (frame-val->src
        (cdr
         (assoc-equal
          (abs-find-file-src
           (partial-collapse frame (dirname path))
           (dirname path))
          frame))))
      (frame->frame
       (partial-collapse frame (dirname path)))))))
  :hints
  (("goal"
    :cases
    ((not
      (and
       (consp
        (assoc-equal
         (abs-find-file-src
          (partial-collapse frame (dirname path))
          (dirname path))
         (frame->frame
          (partial-collapse frame (dirname path)))))
       (equal
        (frame-val->src
         (frame-val
          (frame-val->path
           (cdr
            (assoc-equal
             (abs-find-file-src
              (partial-collapse frame (dirname path))
              (dirname path))
             frame)))
          (mv-nth
           1
           (abs-alloc
            (frame-val->dir
             (cdr
              (assoc-equal
               (abs-find-file-src
                (partial-collapse frame (dirname path))
                (dirname path))
               (partial-collapse frame (dirname path)))))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (abs-find-file-src
                  (partial-collapse frame (dirname path))
                  (dirname path))
                 frame))))
             (dirname path))
            (find-new-index
             (strip-cars
              (partial-collapse frame (dirname path))))))
          (frame-val->src
           (cdr
            (assoc-equal
             (abs-find-file-src
              (partial-collapse frame (dirname path))
              (dirname path))
             frame)))))
        (frame-val->src
         (cdr
          (assoc-equal
           (abs-find-file-src
            (partial-collapse frame (dirname path))
            (dirname path))
           (frame->frame
            (partial-collapse frame (dirname path))))))))))
    :do-not-induct t)
   ("subgoal 1" :in-theory (enable frame->frame))))

(defthm
  abs-mkdir-correctness-lemma-45
  (implies
   (and (no-duplicatesp-equal (strip-cars frame))
        (frame-p frame)
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (abs-separate frame))
   (dist-names
    (frame-val->dir$inline
     (cdr (assoc-equal 0
                       (partial-collapse frame (dirname path)))))
    nil
    (frame->frame (partial-collapse frame (dirname path)))))
  :hints
  (("goal"
    :cases
    ((not
      (equal
       (frame-val->dir
        (cdr (assoc-equal 0
                          (partial-collapse frame (dirname path)))))
       (frame->root (partial-collapse frame (dirname path)))))))
   ("subgoal 1" :in-theory (enable frame->root))))

(defthm
  abs-mkdir-correctness-lemma-46
  (implies
   (and
    (no-duplicatesp-equal (strip-cars frame))
    (frame-p frame)
    (equal (frame-val->src (cdr (assoc-equal 0 frame)))
           0)
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (abs-separate frame)
    (not
     (equal
      0
      (abs-find-file-src (partial-collapse frame (dirname path))
                         (dirname path)))))
   (dist-names
    (frame-val->dir$inline
     (cdr
      (assoc-equal
       (abs-find-file-src (partial-collapse frame (dirname path))
                          (dirname path))
       (partial-collapse frame (dirname path)))))
    (frame-val->path$inline
     (cdr
      (assoc-equal
       (abs-find-file-src (partial-collapse frame (dirname path))
                          (dirname path))
       frame)))
    (remove-assoc-equal
     (abs-find-file-src (partial-collapse frame (dirname path))
                        (dirname path))
     (frame->frame (partial-collapse frame (dirname path))))))
  :hints
  (("goal"
    :in-theory (e/d (frame->frame)
                    (abs-separate-of-frame->frame-of-collapse-this-lemma-2))
    :use
    (:instance
     abs-separate-of-frame->frame-of-collapse-this-lemma-2
     (x (abs-find-file-src (partial-collapse frame (dirname path))
                           (dirname path)))
     (frame
      (frame->frame (partial-collapse frame (dirname path))))))))

;; It's not hard to imagine a scenario where the first corollary might be
;; needed, even though accumulated-persistence says it is useless.
(defthm
  abs-mkdir-correctness-lemma-47
  (implies
   (and (zp (mv-nth 1 (abs-find-file-helper fs path)))
        (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs path)))
        (not (member-equal (nfix new-index)
                           (abs-addrs (abs-fs-fix fs)))))
   (not (equal (mv-nth 1 (abs-alloc fs path new-index))
               (abs-fs-fix fs))))
  :hints
  (("goal"
    :in-theory
    (e/d (abs-find-file-helper abs-alloc fat32-filename-list-fix)
         (ctx-app-ok-when-abs-complete-lemma-2 nfix))
    :expand
    ((:with
      put-assoc-equal-without-change
      (equal
       (put-assoc-equal
        (car path)
        (abs-file (abs-file->dir-ent (cdr (assoc-equal (car path) fs)))
                  (list (nfix new-index)))
        fs)
       fs))
     (abs-alloc fs path new-index)
     (abs-file-contents-fix (list (nfix new-index))))
    :induct (abs-find-file-helper fs path))
   ("subgoal *1/1"
    :use (:instance ctx-app-ok-when-abs-complete-lemma-2
                    (name (fat32-filename-fix (car path))))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (zp (mv-nth 1 (abs-find-file-helper fs path)))
          (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs path)))
          (not (member-equal (nfix new-index)
                             (abs-addrs (abs-fs-fix fs))))
          (abs-fs-p fs))
     (not (equal (mv-nth 1 (abs-alloc fs path new-index))
                 fs))))))

(defthm
  abs-mkdir-correctness-lemma-48
  (implies
   (consp
    (nthcdr
     (len
      (frame-val->path
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         frame))))
     (dirname path)))
   (not
    (intersectp-equal
     (names-at
      (frame-val->dir
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         (partial-collapse frame (dirname path)))))
      nil)
     (names-at
      nil
      (cdr
       (nthcdr
        (+ -1 (len path))
        (frame-val->path
         (cdr
          (assoc-equal (abs-find-file-src
                        (partial-collapse frame (dirname path))
                        (dirname path))
                       frame)))))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite nthcdr-of-nthcdr))
    :use
    (:instance
     (:rewrite nthcdr-of-nthcdr)
     (x
      (frame-val->path
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         frame))))
     (b (+ -1 (len path)))
     (a 1)))))

(defthm
  abs-mkdir-correctness-lemma-49
  (implies
   (and
    (no-duplicatesp-equal (strip-cars frame))
    (frame-p frame)
    (equal (frame-val->src (cdr (assoc-equal 0 frame)))
           0)
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (abs-separate frame)
    (not
     (equal
      0
      (abs-find-file-src (partial-collapse frame (dirname path))
                         (dirname path)))))
   (not
    (intersectp-equal
     (names-at
      (frame-val->dir
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         (partial-collapse frame (dirname path)))))
      nil)
     (names-at
      (frame->root (partial-collapse frame (dirname path)))
      (frame-val->path
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         frame)))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d nil
                    ((:rewrite abs-separate-of-collapse-this-lemma-1
                               . 1)))
    :use
    (:instance
     (:rewrite abs-separate-of-collapse-this-lemma-1 . 1)
     (relpath
      (frame-val->path
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         frame))))
     (root (frame->root (partial-collapse frame (dirname path))))
     (frame (frame->frame (partial-collapse frame (dirname path))))
     (x (abs-find-file-src (partial-collapse frame (dirname path))
                           (dirname path)))))
   ("subgoal 2" :in-theory (enable frame->frame))
   ("subgoal 1" :in-theory (enable frame->frame))))

(defthm
  abs-place-file-helper-of-ctx-app-1
  (implies
   (and (ctx-app-ok abs-file-alist1 x x-path)
        (not (member-equal (fat32-filename-fix (car path))
                           (names-at abs-file-alist1 x-path)))
        (abs-fs-p (ctx-app abs-file-alist1 fs x x-path)))
   (equal
    (ctx-app abs-file-alist1
             (mv-nth 0 (abs-place-file-helper fs path file))
             x x-path)
    (if (consp path)
        (mv-nth 0
                (abs-place-file-helper (ctx-app abs-file-alist1 fs x x-path)
                                       (append x-path path)
                                       file))
        (ctx-app abs-file-alist1 fs x x-path))))
  :hints
  (("goal" :in-theory
    (e/d (abs-place-file-helper ctx-app ctx-app-ok addrs-at names-at)
         ((:rewrite abs-file-alist-p-correctness-1)
          (:rewrite hifat-equiv-when-absfat-equiv)
          (:definition no-duplicatesp-equal)
          (:rewrite abs-fs-fix-of-put-assoc-equal-lemma-1)
          (:rewrite subsetp-when-prefixp)
          (:rewrite abs-addrs-when-m1-file-alist-p)
          (:rewrite abs-addrs-of-ctx-app-2)))
    :induct (mv (append x-path path)
                (ctx-app abs-file-alist1 fs x x-path))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (ctx-app-ok abs-file-alist1 x x-path)
          (not (member-equal (fat32-filename-fix (car path))
                             (names-at abs-file-alist1 x-path)))
          (abs-fs-p (ctx-app abs-file-alist1 fs x x-path))
          (abs-fs-p fs)
          (abs-complete fs)
          (abs-no-dups-file-p file)
          (m1-file-p file))
     (equal
      (ctx-app abs-file-alist1
               (mv-nth 0 (hifat-place-file fs path file))
               x x-path)
      (if (consp path)
          (mv-nth 0
                  (abs-place-file-helper (ctx-app abs-file-alist1 fs x x-path)
                                         (append x-path path)
                                         file))
          (ctx-app abs-file-alist1 fs x x-path)))))))

(defthm abs-mkdir-correctness-lemma-50
  (implies (consp path)
           (fat32-filename-list-equiv
            (append (dirname path)
                    (list (basename path)))
            path))
  :hints (("goal" :in-theory (enable dirname basename
                                     basename-dirname-helper
                                     fat32-filename-list-fix
                                     fat32-filename-list-equiv)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (iff (fat32-filename-list-equiv (dirname path)
                                    path)
         (atom path))
    :instructions
    ((:bash ("goal" :in-theory (enable dirname basename
                                       basename-dirname-helper
                                       fat32-filename-list-fix
                                       fat32-filename-list-equiv)))
     (:claim
      (equal
       (len (append (fat32-filename-list-fix path)
                    (list (mv-nth 0
                                  (basename-dirname-helper path)))))
       (len path))
      :hints :none)
     (:change-goal nil t)
     (:dive 1 1)
     := :up
     (:rewrite len-of-fat32-filename-list-fix)
     :top
     :s :bash))
   (:rewrite
    :corollary
    (implies (and (consp path) (nat-equiv n (len (dirname path))))
             (fat32-filename-list-equiv
              (nthcdr n path)
              (list (basename path))))
    :instructions (:split (:dive 1 2)
                          (:= path
                              (append (dirname path)
                                      (list (basename path)))
                              :equiv fat32-filename-list-equiv$inline)
                          :top (:dive 1)
                          (:= (append (nthcdr n (dirname path))
                                      (list (basename path))))
                          (:dive 1)
                          (:= nil)
                          :top :bash))))

(defthm
  abs-mkdir-correctness-lemma-53
  (implies
   (and
    (not
     (equal
      0
      (abs-find-file-src (partial-collapse frame (dirname path))
                         (dirname path))))
    (consp (assoc-equal 0 frame)))
   (consp (frame->frame frame)))
  :hints
  (("goal"
    :in-theory (e/d (collapse frame->frame)
                    ((:rewrite abs-find-file-src-correctness-1)
                     (:rewrite consp-of-remove-assoc-1)))
    :do-not-induct t
    :use
    ((:instance (:rewrite abs-find-file-src-correctness-1)
                (path (dirname path))
                (frame (partial-collapse frame (dirname path))))
     (:instance
      (:rewrite consp-of-remove-assoc-1)
      (alist frame)
      (x2 0)
      (x1 (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path)))))))
  :rule-classes
  ((:forward-chaining
    :trigger-terms
    ((abs-find-file-src (partial-collapse frame (dirname path))
                        (dirname path))))))

(defthm
  abs-mkdir-correctness-lemma-54
  (implies
   (and
    (not
     (equal
      0
      (abs-find-file-src (partial-collapse frame (dirname path))
                         (dirname path))))
    (mv-nth 1 (collapse frame))
    (consp (assoc-equal 0 frame)))
   (< '0
      (1st-complete (frame->frame frame))))
  :hints (("goal" :in-theory (enable collapse)
           :do-not-induct t))
  :rule-classes
  ((:forward-chaining
    :trigger-terms
    ((abs-find-file-src (partial-collapse frame (dirname path))
                        (dirname path))))
   :linear))

(defthm
  abs-mkdir-correctness-lemma-55
  (implies
   (not
    (equal
     0
     (abs-find-file-src (partial-collapse frame (dirname path))
                        (dirname path))))
   (not
    (equal
     (abs-find-file-src (partial-collapse frame (dirname path))
                        (dirname path))
     (find-new-index
      (strip-cars (partial-collapse frame (dirname path)))))))
  :instructions
  ((:use
    (:instance
     (:rewrite find-new-index-correctness-1)
     (fd-list
      (strip-cars (partial-collapse frame (dirname path))))))
   :split (:contrapose 1)
   (:dive 1)
   := :up (:rewrite member-of-strip-cars)
   (:rewrite abs-find-file-src-correctness-1)))

(defthm
  abs-mkdir-correctness-lemma-56
  (equal (consp (assoc-equal x
                             (mv-nth 0
                                     (abs-alloc fs path new-index))))
         (if (member-equal x (names-at fs path))
             t nil))
  :hints (("goal" :in-theory (enable abs-alloc names-at)
           :induct (abs-alloc fs path new-index)))
  :rule-classes
  ((:rewrite
    :corollary
    (iff (consp (assoc-equal x
                               (mv-nth 0
                                       (abs-alloc fs path new-index))))
         (member-equal x (names-at fs path))))))

(defthm
  abs-mkdir-correctness-lemma-58
  (implies
   (and (absfat-subsetp abs-file-alist1 abs-file-alist2)
        (abs-file-alist-p abs-file-alist1)
        (consp (assoc-equal x abs-file-alist1))
        (not (abs-directory-file-p (cdr (assoc-equal x abs-file-alist1)))))
   (not (abs-directory-file-p (cdr (assoc-equal x abs-file-alist2)))))
  :hints (("goal" :in-theory (enable absfat-subsetp))))

(defthm
  abs-mkdir-correctness-lemma-59
  (implies
   (and
    (not (abs-fs-p (abs-file->contents
                    (cdr (assoc-equal (fat32-filename-fix (car path))
                                      fs1)))))
    (abs-fs-p fs1)
    (absfat-subsetp fs1 fs2))
   (not (abs-directory-file-p
         (cdr (assoc-equal (fat32-filename-fix (car path))
                           fs2)))))
  :hints (("goal" :in-theory (disable (:rewrite abs-mkdir-correctness-lemma-58))
           :use (:instance (:rewrite abs-mkdir-correctness-lemma-58)
                           (abs-file-alist2 fs2)
                           (x (fat32-filename-fix (car path)))
                           (abs-file-alist1 fs1)))))

(defthm
  abs-mkdir-correctness-lemma-62
  (implies
   (and
    (absfat-subsetp
     (mv-nth 0
             (abs-place-file-helper
              (abs-file->contents
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs1)))
              (cdr path)
              file))
     (mv-nth 0
             (abs-place-file-helper
              (abs-file->contents
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs2)))
              (cdr path)
              file)))
    (m1-regular-file-p file))
   (absfat-subsetp
    (mv-nth '0
            (abs-place-file-helper
             (abs-file->contents$inline
              (cdr (assoc-equal (fat32-filename-fix (car path))
                                fs1)))
             (cdr path)
             file))
    (abs-file-contents-fix
     (mv-nth '0
             (abs-place-file-helper
              (abs-file->contents$inline
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs2)))
              (cdr path)
              file))))))

(defthm
  abs-mkdir-correctness-lemma-63
  (implies
   (and
    (absfat-subsetp
     (mv-nth 0
             (abs-place-file-helper
              (abs-file->contents
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs1)))
              (cdr path)
              file))
     (mv-nth 0
             (abs-place-file-helper
              (abs-file->contents
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs2)))
              (cdr path)
              file)))
    (abs-directory-file-p file))
   (absfat-subsetp
    (mv-nth '0
            (abs-place-file-helper
             (abs-file->contents$inline
              (cdr (assoc-equal (fat32-filename-fix (car path))
                                fs1)))
             (cdr path)
             file))
    (abs-file-contents-fix
     (mv-nth '0
             (abs-place-file-helper
              (abs-file->contents$inline
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs2)))
              (cdr path)
              file))))))

(defthm
  abs-mkdir-correctness-lemma-64
  (implies
   (not
    (absfat-subsetp
     (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                           fs1)))
     (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                           fs2)))))
   (consp (assoc-equal (fat32-filename-fix (car path))
                       fs1)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (abs-place-file-helper absfat-subsetp abs-file-p-alt)
                    nil))))

(defthm
  abs-mkdir-correctness-lemma-65
  (implies
   (and
    (abs-directory-file-p
     (cdr (assoc-equal (fat32-filename-fix (car path))
                       fs2)))
    (abs-fs-p fs1)
    (absfat-subsetp fs1 fs2)
    (not (abs-directory-file-p
          (cdr (assoc-equal (fat32-filename-fix (car path))
                            fs1)))))
   (absfat-subsetp
    fs1
    (put-assoc-equal
     (fat32-filename-fix (car path))
     (abs-file
      (abs-file->dir-ent
       (cdr (assoc-equal (fat32-filename-fix (car path))
                         fs2)))
      (mv-nth
       0
       (abs-place-file-helper
        (abs-file->contents
         (cdr (assoc-equal (fat32-filename-fix (car path))
                           fs2)))
        (cdr path)
        file)))
     fs2)))
  :hints
  (("goal"
    :in-theory (e/d (abs-place-file-helper absfat-subsetp abs-file-p-alt)
                    ((:rewrite abs-mkdir-correctness-lemma-58)))
    :use (:instance (:rewrite abs-mkdir-correctness-lemma-58)
                    (abs-file-alist2 fs2)
                    (x (fat32-filename-fix (car path)))
                    (abs-file-alist1 fs1)))))

(defthm
  abs-mkdir-correctness-lemma-66
  (implies
   (and
    (absfat-subsetp
     (mv-nth 0
             (abs-place-file-helper
              (abs-file->contents
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs1)))
              (cdr path)
              file))
     (mv-nth 0
             (abs-place-file-helper
              (abs-file->contents
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs2)))
              (cdr path)
              file)))
    (m1-regular-file-p file))
   (absfat-subsetp
    (abs-file-contents-fix
     (mv-nth '0
             (abs-place-file-helper
              (abs-file->contents$inline
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs1)))
              (cdr path)
              file)))
    (abs-file-contents-fix
     (mv-nth '0
             (abs-place-file-helper
              (abs-file->contents$inline
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs2)))
              (cdr path)
              file)))))
  :hints
  (("goal"
    :in-theory (e/d (abs-place-file-helper absfat-subsetp abs-file-p-alt)))))

(defthm
  abs-mkdir-correctness-lemma-67
  (implies
   (and
    (absfat-subsetp
     (mv-nth 0
             (abs-place-file-helper
              (abs-file->contents
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs1)))
              (cdr path)
              file))
     (mv-nth 0
             (abs-place-file-helper
              (abs-file->contents
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs2)))
              (cdr path)
              file)))
    (abs-directory-file-p file))
   (absfat-subsetp
    (abs-file-contents-fix
     (mv-nth '0
             (abs-place-file-helper
              (abs-file->contents$inline
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs1)))
              (cdr path)
              file)))
    (abs-file-contents-fix
     (mv-nth '0
             (abs-place-file-helper
              (abs-file->contents$inline
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs2)))
              (cdr path)
              file)))))
  :hints
  (("goal"
    :in-theory (e/d (abs-place-file-helper absfat-subsetp abs-file-p-alt))
    :do-not-induct t)))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies (and (absfat-subsetp fs1 fs2)
                   (abs-fs-p fs1)
                   (abs-fs-p fs2)
                   (abs-no-dups-file-p file)
                   (zp (mv-nth 1
                               (abs-place-file-helper fs2 path file))))
              (absfat-subsetp (mv-nth 0 (abs-place-file-helper fs1 path file))
                              (mv-nth 0
                                      (abs-place-file-helper fs2 path file))))
     :hints (("goal" :in-theory (enable abs-place-file-helper absfat-subsetp
                                        abs-file-p-alt abs-no-dups-file-p)
              :induct (mv (abs-place-file-helper fs1 path file)
                          (abs-place-file-helper fs2 path file))))))

  ;; Non-trivial proof, might cause trouble if disabled.
  (defthm
    abs-mkdir-correctness-lemma-57
    (implies
     (and (absfat-subsetp (abs-fs-fix fs1) (abs-fs-fix fs2))
          (zp (mv-nth 1
                      (abs-place-file-helper fs2 path file))))
     (absfat-subsetp (mv-nth 0
                             (abs-place-file-helper fs1 path file))
                     (mv-nth 0
                             (abs-place-file-helper fs2 path file))))
    :hints (("goal" :use
             (:instance
              lemma
              (fs1 (abs-fs-fix fs1))
              (fs2 (abs-fs-fix fs2))
              (file (abs-no-dups-file-fix file)))
             :do-not-induct t))))

(defthmd
  abs-mkdir-correctness-lemma-61
  (implies (not (or (equal (mv-nth 1
                                   (abs-place-file-helper fs path file))
                           *enospc*)
                    (equal (mv-nth 1
                                   (abs-place-file-helper fs path file))
                           *enotdir*)
                    (equal (mv-nth 1
                                   (abs-place-file-helper fs path file))
                           *enoent*)))
           (equal (mv-nth 1
                          (abs-place-file-helper fs path file))
                  0))
  :hints (("goal" :in-theory (enable abs-place-file-helper))))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies
      (and
       (equal (mv-nth 1
                      (abs-place-file-helper fs2 path file))
              28)
       (abs-fs-p fs1)
       (abs-fs-p fs2))
      (> (mv-nth 1
                 (abs-place-file-helper fs1 path file))
         2))
     :hints
     (("goal"
       :in-theory (enable abs-place-file-helper
                          absfat-subsetp abs-file-p-alt)
       :do-not-induct t
       :induct (mv (abs-place-file-helper fs1 path file)
                   (abs-place-file-helper fs2 path file))))
     :rule-classes :linear))

  (defthm
    abs-mkdir-correctness-lemma-68
    (implies
     (and
      (equal (mv-nth 1
                     (abs-place-file-helper fs2 path file))
             28))
     (> (mv-nth 1
                (abs-place-file-helper fs1 path file))
        2))
    :hints (("goal" :use (:instance lemma (fs1 (abs-fs-fix fs1))
                                    (fs2 (abs-fs-fix fs2)))))
    :rule-classes :linear))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies
      (and
       (equal (mv-nth 1
                      (abs-place-file-helper fs2 path file))
              *enoent*)
       (abs-fs-p fs1)
       (abs-fs-p fs2)
       (absfat-subsetp fs2 fs1))
      (> (mv-nth 1
                 (abs-place-file-helper fs1 path file))
         0))
     :hints
     (("goal"
       :in-theory (enable abs-place-file-helper
                          absfat-subsetp abs-file-p-alt)
       :induct (mv (abs-place-file-helper fs1 path file)
                   (abs-place-file-helper fs2 path file))))
     :rule-classes :linear))

  (defthm
    abs-mkdir-correctness-lemma-69
    (implies
     (and
      (equal (mv-nth 1
                     (abs-place-file-helper fs2 path file))
             *enoent*)
      (absfat-subsetp (abs-fs-fix fs2)
                      (abs-fs-fix fs1)))
     (> (mv-nth 1
                (abs-place-file-helper fs1 path file))
        0))
    :hints (("goal" :use (:instance lemma (fs1 (abs-fs-fix fs1))
                                    (fs2 (abs-fs-fix fs2)))))
    :rule-classes :linear))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies (and (equal (mv-nth 1
                                  (abs-place-file-helper fs2 path file))
                          *enotdir*)
                   (abs-fs-p fs1)
                   (absfat-subsetp (abs-fs-fix fs1)
                                   (abs-fs-fix fs2))
                   (not (abs-directory-file-p (abs-no-dups-file-fix file))))
              (equal (mv-nth 1
                             (abs-place-file-helper fs1 path file))
                     *enotdir*))
     :hints (("goal" :in-theory (enable abs-place-file-helper
                                        absfat-subsetp abs-file-p-alt)
              :induct (mv (abs-place-file-helper fs1 path file)
                          (abs-place-file-helper fs2 path file))))))

  (defthm
    abs-mkdir-correctness-lemma-70
    (implies (and (equal (mv-nth 1
                                 (abs-place-file-helper fs2 path file))
                         *enotdir*)
                  (absfat-subsetp (abs-fs-fix fs1)
                                  (abs-fs-fix fs2))
                  (case-split (not (abs-directory-file-p (abs-no-dups-file-fix file)))))
             (equal (mv-nth 1
                            (abs-place-file-helper fs1 path file))
                    *enotdir*))
    :hints (("goal" :use (:instance lemma (fs1 (abs-fs-fix fs1)))))))

(defthm
  abs-mkdir-correctness-lemma-71
  (implies
   (and (absfat-equiv fs1 fs2)
        (syntaxp (not (term-order fs1 fs2)))
        (abs-fs-p fs1)
        (abs-fs-p fs2))
   (absfat-equiv
    (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                          fs1)))
    (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                          fs2)))))
  :hints
  (("goal"
    :in-theory (e/d (absfat-equiv absfat-subsetp abs-fs-fix
                                  abs-file-p-alt m1-regular-file-p)
                    ((:rewrite absfat-subsetp-guard-lemma-1)))
    :do-not-induct t
    :cases
    ((or
      (abs-directory-file-p (cdr (assoc-equal (fat32-filename-fix (car path))
                                              fs1)))
      (abs-directory-file-p (cdr (assoc-equal (fat32-filename-fix (car path))
                                              fs2))))))
   ("subgoal 2" :use ((:instance (:rewrite absfat-subsetp-guard-lemma-1)
                                 (abs-file-alist fs1)
                                 (name (fat32-filename-fix (car path))))
                      (:instance (:rewrite absfat-subsetp-guard-lemma-1)
                                 (abs-file-alist fs2)
                                 (name (fat32-filename-fix (car path)))))))
  :otf-flg t)

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies (and (equal (mv-nth 1
                                  (abs-place-file-helper fs2 path file))
                          *enotdir*)
                   (abs-fs-p fs1)
                   (abs-fs-p fs2)
                   (absfat-equiv fs1 fs2)
                   (abs-directory-file-p (abs-no-dups-file-fix file)))
              (equal (mv-nth 1
                             (abs-place-file-helper fs1 path file))
                     *enotdir*))
     :hints
     (("goal"
       :in-theory
       (e/d (abs-place-file-helper abs-file-p-alt)
            ((:rewrite absfat-equiv-implies-set-equiv-names-at-1-lemma-4)
             (:rewrite
              absfat-equiv-implies-set-equiv-addrs-at-1-lemma-2)
             (:definition put-assoc-equal)
             (:rewrite abs-file-alist-p-correctness-1)
             (:rewrite
              hifat-find-file-correctness-1-lemma-1)
             (:definition abs-complete)
             (:rewrite
              abs-fs-fix-of-put-assoc-equal-lemma-1)
             (:rewrite subsetp-when-prefixp)
             abs-mkdir-correctness-lemma-71))
       :induct (mv (abs-place-file-helper fs1 path file)
                   (abs-place-file-helper fs2 path file)))
      ("subgoal *1/3"
       :use
       (abs-mkdir-correctness-lemma-71
        (:instance (:rewrite absfat-equiv-implies-set-equiv-names-at-1-lemma-3)
                   (abs-file-alist2 fs1)
                   (abs-file-alist1 fs2)
                   (x (fat32-filename-fix (car path))))))
      ("subgoal *1/1"
       :use
       (abs-mkdir-correctness-lemma-71
        (:instance (:rewrite absfat-equiv-implies-set-equiv-names-at-1-lemma-3)
                   (abs-file-alist2 fs1)
                   (abs-file-alist1 fs2)
                   (x (fat32-filename-fix (car path)))))))))

  (defthm
    abs-mkdir-correctness-lemma-72
    (implies (and (equal (mv-nth 1
                                 (abs-place-file-helper fs2 path file))
                         *enotdir*)
                  (absfat-equiv fs1 fs2)
                  (abs-directory-file-p (abs-no-dups-file-fix file)))
             (equal (mv-nth 1
                            (abs-place-file-helper fs1 path file))
                    *enotdir*))
    :hints (("goal" :use (:instance lemma (fs1 (abs-fs-fix fs1))
                                    (fs2 (abs-fs-fix fs2)))))))

(defthm
  abs-mkdir-correctness-lemma-60
  (implies (absfat-equiv fs1 fs2)
           (and (absfat-equiv (mv-nth 0 (abs-place-file-helper fs1 path file))
                              (mv-nth 0
                                      (abs-place-file-helper fs2 path file)))
                (equal (mv-nth 1 (abs-place-file-helper fs1 path file))
                       (mv-nth 1
                               (abs-place-file-helper fs2 path file)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (absfat-equiv)
                    (abs-mkdir-correctness-lemma-57
                     (:rewrite abs-place-file-helper-correctness-2)))
    :use ((:instance abs-mkdir-correctness-lemma-57
                     (fs1 (abs-fs-fix fs1))
                     (fs2 (abs-fs-fix fs2)))
          (:instance abs-mkdir-correctness-lemma-57
                     (fs1 (abs-fs-fix fs2))
                     (fs2 (abs-fs-fix fs1)))
          (:instance (:rewrite abs-place-file-helper-correctness-2)
                     (file file)
                     (path path)
                     (fs fs1))
          (:instance (:rewrite abs-place-file-helper-correctness-2)
                     (file file)
                     (path path)
                     (fs fs2))
          (:instance (:rewrite abs-mkdir-correctness-lemma-61)
                     (file file)
                     (path path)
                     (fs fs1))
          (:instance (:rewrite abs-mkdir-correctness-lemma-61)
                     (file file)
                     (path path)
                     (fs fs2)))))
  :rule-classes
  ((:congruence
    :corollary
    (implies (absfat-equiv fs1 fs2)
             (absfat-equiv (mv-nth 0 (abs-place-file-helper fs1 path file))
                           (mv-nth 0
                                   (abs-place-file-helper fs2 path file)))))
   (:congruence
    :corollary
    (implies (absfat-equiv fs1 fs2)
             (equal (mv-nth 1 (abs-place-file-helper fs1 path file))
                    (mv-nth 1
                            (abs-place-file-helper fs2 path file)))))
   (:rewrite
    :corollary
    (implies
     (and (absfat-equiv fs1 fs2)
          (syntaxp (not (term-order fs1 fs2)))
          (abs-fs-p fs1)
          (abs-complete fs1)
          (abs-no-dups-file-p file)
          (m1-file-p file))
     (and (absfat-equiv (mv-nth 0 (hifat-place-file fs1 path file))
                        (mv-nth 0
                                (abs-place-file-helper fs2 path file)))
          (equal (mv-nth 1 (hifat-place-file fs1 path file))
                 (mv-nth 1
                         (abs-place-file-helper fs2 path file))))))))

(defthmd
  collapse-hifat-place-file-lemma-4
  (implies
   (and
    (zp
     (mv-nth
      1
      (abs-find-file-helper fs
                            (mv-nth 1
                                    (basename-dirname-helper path)))))
    (abs-directory-file-p
     (mv-nth
      0
      (abs-find-file-helper fs
                            (mv-nth 1
                                    (basename-dirname-helper path)))))
    (not (equal (mv-nth 1 (abs-find-file-helper fs path))
                0)))
   (equal (mv-nth 1 (abs-find-file-helper fs path))
          *enoent*))
  :hints
  (("goal" :in-theory (enable abs-find-file-helper
                              basename-dirname-helper))
   ("subgoal *1/2'''" :expand (basename-dirname-helper (cdr path)))))

(defthm
  collapse-hifat-place-file-lemma-5
  (implies (and (consp x)
                (fat32-filename-list-prefixp x y)
                (equal (mv-nth 1 (abs-find-file-helper fs x))
                       *enoent*))
           (equal (addrs-at fs y) nil))
  :hints
  (("goal" :in-theory
    (e/d (abs-find-file-helper addrs-at fat32-filename-list-prefixp)
         (ctx-app-ok-when-abs-complete-lemma-4))
    :induct (mv (fat32-filename-list-prefixp x y)
                (mv-nth 0 (abs-find-file-helper fs x))))))

(defthm
  collapse-hifat-place-file-lemma-6
  (implies (and (consp x)
                (fat32-filename-list-prefixp x y)
                (equal (mv-nth 1 (abs-find-file-helper fs x))
                       *enoent*))
           (not (ctx-app-ok fs var y)))
  :hints
  (("goal" :in-theory (enable ctx-app-ok))))

(defthm
  collapse-hifat-place-file-lemma-9
  (implies
   (and
    (equal (mv-nth 1
                   (abs-find-file-helper (frame->root frame2)
                                         (dirname path)))
           0)
    (equal (mv-nth 1
                   (abs-find-file-helper (frame->root frame2)
                                         path))
           2)
    (prefixp
     (fat32-filename-list-fix path)
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                        (frame->frame frame1))))))
   (not
    (ctx-app-ok
     (frame->root frame2)
     (1st-complete (frame->frame frame1))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                        (frame->frame frame1)))))))
  :hints
  (("goal"
    :in-theory (e/d (abs-find-file-helper dirname
                                          basename-dirname-helper
                                          fat32-filename-list-prefixp-alt)
                    ((:rewrite collapse-hifat-place-file-lemma-6)))
    :use
    (:instance
     (:rewrite collapse-hifat-place-file-lemma-6)
     (y
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                         (frame->frame frame1)))))
     (var (1st-complete (frame->frame frame1)))
     (fs (frame->root frame2))
     (x path)))))

(defthm
  collapse-hifat-place-file-lemma-10
  (implies (and (m1-file-p file)
                (hifat-no-dups-p (m1-file->contents file)))
           (abs-no-dups-p (m1-file->contents file)))
  :hints
  (("goal" :in-theory (e/d (m1-file-p m1-file->contents
                                      m1-file-contents-p abs-no-dups-p)
                           ((:rewrite abs-no-dups-p-when-m1-file-alist-p)))
    :use (:instance (:rewrite abs-no-dups-p-when-m1-file-alist-p)
                    (fs (abs-file->contents file))))))

(defthm
  collapse-hifat-place-file-lemma-12
  (implies
   (and (m1-file-p file)
        (hifat-no-dups-p (m1-file->contents file)))
   (not
    (ctx-app-ok
     (m1-file->contents file)
     (1st-complete (frame->frame frame1))
     (nthcdr
      (len path)
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                         (frame->frame frame1))))))))
  :hints
  (("goal" :in-theory (disable (:rewrite m1-directory-file-p-when-m1-file-p))
    :use (:instance (:rewrite m1-directory-file-p-when-m1-file-p)
                    (x file)))))

(defthm
 collapse-hifat-place-file-lemma-11
 (implies
  (and
   (equal (frame->root frame1)
          (mv-nth 0
                  (abs-place-file-helper (frame->root frame2)
                                         path file)))
   (m1-file-p file)
   (hifat-no-dups-p (m1-file->contents file))
   (not
    (ctx-app-ok
      (frame->root frame2)
      (1st-complete (frame->frame frame1))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                         (frame->frame frame1)))))))
  (not
   (ctx-app-ok
      (frame->root frame1)
      (1st-complete (frame->frame frame1))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                         (frame->frame frame1)))))))
 :hints
 (("goal"
   :in-theory (e/d (abs-no-dups-file-fix)
                   ((:rewrite ctx-app-ok-of-abs-place-file-helper-1)))
   :use
   (:instance
    (:rewrite ctx-app-ok-of-abs-place-file-helper-1)
    (x-path
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                         (frame->frame frame1)))))
    (x (1st-complete (frame->frame frame1)))
    (file file)
    (path path)
    (fs (frame->root frame2))))))

(defthm
  collapse-hifat-place-file-lemma-14
  (implies
   (and
    (equal (mv-nth 1
                   (abs-find-file-helper (frame->root frame2)
                                         path))
           2)
    (ctx-app-ok
     (frame->root frame2)
     (1st-complete (frame->frame frame1))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                        (frame->frame frame1)))))
    (prefixp
     (fat32-filename-list-fix path)
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                        (frame->frame frame1))))))
   (not (equal (mv-nth 1
                       (abs-place-file-helper (frame->root frame2)
                                              path file))
               0)))
  :hints
  (("goal"
    :in-theory (e/d (abs-find-file-helper dirname
                                          basename-dirname-helper
                                          fat32-filename-list-prefixp-alt))
    :expand ((abs-place-file-helper (frame->root frame1)
                                    path file)
             (abs-place-file-helper (frame->root frame2)
                                    path file)))))

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
    :in-theory (e/d nil
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
    :in-theory (e/d (path-clear)
                    (len-when-prefixp (:rewrite prefixp-when-equal-lengths))))
   ("subgoal *1/4'''" :use ((:instance (:rewrite prefixp-when-equal-lengths)
                                       (y (fat32-filename-list-fix y))
                                       (x (fat32-filename-list-fix x)))
                            (:instance len-when-prefixp
                                       (x (fat32-filename-list-fix x))
                                       (y (fat32-filename-list-fix y)))
                            (:instance len-when-prefixp
                                       (x (fat32-filename-list-fix y))
                                       (y (fat32-filename-list-fix x)))))))

(defthm
  abs-place-file-helper-of-ctx-app-2
  (implies
   (not (fat32-filename-list-prefixp x-path path))
   (equal
    (mv-nth 1 (abs-place-file-helper
               (ctx-app fs1 fs2 x x-path)
               path file))
    (mv-nth 1 (abs-place-file-helper
               fs1
               path file))))
  :hints (("Goal" :in-theory (enable abs-place-file-helper ctx-app)
           :induct (mv (fat32-filename-list-prefixp x-path path)
                       (ctx-app fs1 fs2 x x-path)))))

;; Here's the problem with this theorem: it doesn't work for the arbitrary
;; place-file because it can literally dump a number of names in different
;; directories while wiping out a bunch of others, making an utter mess of
;; dist-names and therefor abs-separate. In actual system calls, we create one
;; new name at a time, which is what makes it possible to ensure that we can
;; use path-clear and basically account for everything. But... how do we
;; pass on that kind of stipulation here? It would be nice to hang on to a
;; model where we just do put-assoc and we can tell what the names in each
;; directory are, but when in the middle of collapsing that assumption
;; disappears because wherever you did the put-assoc, that's going somewhere,
;; and then somewhere else, and at various points it sinks deeper and deeper
;; down into the directory tree. So how do we say that we are only introducing
;; this one name? Maybe the answer is simply to maintain path-clear...
(encapsulate
  ()

  (local
   (defun
       induction-scheme (frame1 frame2)
     (declare (xargs :verify-guards nil
                     :measure (len (frame->frame frame1))))
     (cond
      ((and
        (not (atom (frame->frame frame1)))
        (not (zp (1st-complete (frame->frame frame1))))
        (not
         (zp
          (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame1))
                             (frame->frame frame1))))))
        (not
         (or
          (equal
           (frame-val->src
            (cdr
             (assoc-equal (1st-complete (frame->frame frame1))
                          (frame->frame frame1))))
           (1st-complete (frame->frame frame1)))
          (atom
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame1))
                           (frame->frame frame1))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame1))
             (frame->frame frame1))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame1))
                           (frame->frame frame1))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame1))
             (frame->frame frame1)))))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame1))
                            (frame->frame frame1)))))
        (ctx-app-ok
         (frame-val->dir
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame1))
                           (frame->frame frame1))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame1))
             (frame->frame frame1)))))
         (1st-complete (frame->frame frame1))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src
               (cdr
                (assoc-equal (1st-complete (frame->frame frame1))
                             (frame->frame frame1))))
              (remove-assoc-equal
               (1st-complete (frame->frame frame1))
               (frame->frame frame1))))))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame1))
                             (frame->frame frame1)))))))
       (induction-scheme
        (collapse-this frame1
                       (1st-complete (frame->frame frame1)))
        (collapse-this frame2
                       (1st-complete (frame->frame frame2)))))
      ((and
        (not (atom (frame->frame frame1)))
        (not (zp (1st-complete (frame->frame frame1))))
        (zp
         (frame-val->src
          (cdr (assoc-equal (1st-complete (frame->frame frame1))
                            (frame->frame frame1)))))
        (ctx-app-ok
         (frame->root frame1)
         (1st-complete (frame->frame frame1))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame1))
                            (frame->frame frame1))))))
       (induction-scheme
        (collapse-this frame1
                       (1st-complete (frame->frame frame1)))
        (collapse-this frame2
                       (1st-complete (frame->frame frame2)))))
      (t (mv frame1 frame2)))))

  (skip-proofs
   (defthmd
     collapse-hifat-place-file-lemma-8
     (implies
      (and
       (equal (frame->frame frame1)
              (frame->frame frame2))
       (equal (frame->root frame1)
              (mv-nth 0
                      (abs-place-file-helper (frame->root frame2)
                                             path file)))
       ;; We're going to need to make some assumptions about
       ;; abs-place-file-helper and where it is called, because currently it has
       ;; the ability to come in and smoosh the directory structure by placing a file
       ;; at an arbitrary place. While it's all very well to think about
       ;; basenames and dirnames and what should and should not exist, perhaps
       ;; we can go for a property I suspect is provided by partial-collapse -
       ;; path-clear...
       (or
        (atom (dirname path))
        (path-clear (dirname path) (frame->frame frame2)))
       (m1-file-p file)
       (hifat-no-dups-p (m1-file->contents file))
       (dist-names (frame->root frame2)
                   nil (frame->frame frame2))
       (abs-separate (frame->frame frame2))
       (frame-p (frame->frame frame2))
       (no-duplicatesp-equal (strip-cars (frame->frame frame2))))
      (and
       (equal
        (mv-nth 0 (collapse frame1))
        (mv-nth
         0
         (abs-place-file-helper (mv-nth 0 (collapse frame2))
                                path file)))
       (equal (mv-nth 1 (collapse frame1))
              (mv-nth 1 (collapse frame2)))))
     :hints
     (("goal"
       :in-theory
       (e/d
        (collapse)
        ((:definition no-duplicatesp-equal)
         (:rewrite partial-collapse-correctness-lemma-24)
         (:definition assoc-equal)
         (:rewrite subsetp-when-prefixp)
         (:rewrite
          abs-separate-of-frame->frame-of-collapse-this-lemma-8
          . 2)
         (:rewrite nthcdr-when->=-n-len-l)
         (:rewrite strip-cars-of-frame->frame-of-collapse-this)
         (:definition len)
         (:definition remove-equal)
         (:rewrite remove-when-absent)))
       :induct (induction-scheme frame1 frame2)
       :expand (collapse frame2))))))

;; This theorem asserts some things about applying abs-place-file-helper to
;; filesystem instances with holes...
(defthm
  collapse-hifat-place-file-1
  (implies
   (and (or (not (consp (dirname path)))
            (path-clear (dirname path) frame))
        (m1-file-p file)
        (hifat-no-dups-p (m1-file->contents file))
        (dist-names (frame->root (frame-with-root root frame))
                    nil
                    (frame->frame (frame-with-root root frame)))
        (abs-separate (frame->frame (frame-with-root root frame)))
        (frame-p (frame->frame (frame-with-root root frame)))
        (no-duplicatesp-equal
         (strip-cars (frame->frame (frame-with-root root frame)))))
   (and
    (equal
     (mv-nth
      1
      (collapse
       (frame-with-root (mv-nth 0
                                (abs-place-file-helper root path file))
                        frame)))
     (mv-nth 1
             (collapse (frame-with-root root frame))))
    (equal
     (mv-nth
      0
      (collapse
       (frame-with-root (mv-nth 0
                                (abs-place-file-helper root path file))
                        frame)))
     (mv-nth
      0
      (abs-place-file-helper (mv-nth 0
                                     (collapse (frame-with-root root frame)))
                             path file)))))
  :otf-flg t
  :hints
  (("goal"
    :do-not-induct t
    :use
    (:instance
     (:rewrite collapse-hifat-place-file-lemma-8)
     (frame1
      (frame-with-root (mv-nth 0
                               (abs-place-file-helper root path file))
                       frame))
     (frame2 (frame-with-root root frame))))))

(defthmd abs-find-file-after-abs-mkdir-lemma-1
  (implies (case-split (consp path))
           (fat32-filename-list-equiv (nthcdr (- (len path) 1) path)
                                      (list (basename path))))
  :hints (("goal" :in-theory (enable basename-dirname-helper
                                     fat32-filename-list-equiv basename))))

(defthm fat32-filename-list-fix-when-zp-len
  (implies (zp (len x))
           (equal (fat32-filename-list-fix x) nil))
  :rule-classes :type-prescription)

(defthm prefixp-of-dirname
  (prefixp (dirname path)
           (fat32-filename-list-fix path))
  :hints (("goal" :in-theory (enable dirname
                                     basename-dirname-helper)))
  :rule-classes
  ((:rewrite
    :corollary
    (fat32-filename-list-prefixp (dirname path) path)
    :hints (("Goal" :in-theory (enable fat32-filename-list-prefixp-alt))))
   :rewrite))

(defthmd
  abs-find-file-after-abs-mkdir-lemma-4
  (implies (fat32-filename-list-equiv (list (basename path))
                                      path)
           (fat32-filename-equiv$inline (basename path)
                                        (car path)))
  :hints
  (("goal" :in-theory (e/d (abs-mkdir abs-find-file abs-find-file-helper
                                      abs-find-file-after-abs-mkdir-lemma-1
                                      len-when-consp
                                      fat32-filename-list-fix
                                      fat32-filename-list-equiv
                                      fat32-filename-equiv)
                           (abs-mkdir-correctness-lemma-50
                            (:definition nth)
                            (:definition true-listp)
                            (:definition string-listp)
                            (:rewrite true-listp-when-string-list)
                            (:rewrite fat32-filename-p-correctness-1)))
    :do-not-induct t)))

(defthm
  abs-find-file-after-abs-mkdir-lemma-2
  (implies (equal (list (basename path))
                  (fat32-filename-list-fix path))
           (consp path))
  :hints
  (("goal" :in-theory (e/d (abs-mkdir abs-find-file abs-find-file-helper
                                      abs-find-file-after-abs-mkdir-lemma-1
                                      abs-find-file-after-abs-mkdir-lemma-4
                                      len-when-consp
                                      fat32-filename-list-fix abs-alloc)
                           (abs-mkdir-correctness-lemma-50
                            (:definition nth)
                            (:definition true-listp)
                            (:definition string-listp)
                            (:rewrite true-listp-when-string-list)
                            (:rewrite fat32-filename-p-correctness-1)))
    :do-not-induct t))
  :rule-classes :forward-chaining)

;; Again, since this has an inductive proof it doesn't seem like a great idea
;; to remove or disable it.
(defthm abs-find-file-after-abs-mkdir-lemma-3
  (implies (and (consp x)
                (fat32-filename-list-prefixp x y)
                (not (equal (mv-nth 1 (abs-find-file-helper fs y))
                            *enoent*)))
           (not (equal (mv-nth 1 (abs-find-file-helper fs x))
                       *enoent*)))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm
  abs-find-file-after-abs-mkdir-lemma-7
  (implies
   (and
    (prefixp
     (frame-val->path
      (cdr
       (assoc-equal
        (abs-find-file-src (partial-collapse frame (dirname path))
                           (dirname path))
        frame)))
     (dirname path))
    (equal
     (abs-find-file
      (frame->frame (partial-collapse frame (dirname path)))
      (dirname path))
     '(((dir-ent 0 0 0 0 0 0 0 0 0 0 0 0
                 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
        (contents))
       2))
    (not (frame-val->path (cdr (assoc-equal 0 frame))))
    (equal (frame-val->src (cdr (assoc-equal 0 frame)))
           0)
    (not
     (equal
      0
      (abs-find-file-src (partial-collapse frame (dirname path))
                         (dirname path)))))
   (equal
    (abs-find-file-helper
     (frame-val->dir
      (cdr
       (assoc-equal
        (abs-find-file-src (partial-collapse frame (dirname path))
                           (dirname path))
        (partial-collapse frame (dirname path)))))
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          frame))))
      (dirname path)))
    (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal"
    :in-theory (e/d (frame->frame)
                    (abs-find-file-correctness-lemma-14))
    :use
    ((:instance
      (:rewrite abs-find-file-helper-of-ctx-app-lemma-4)
      (path
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (abs-find-file-src
                         (partial-collapse frame (dirname path))
                         (dirname path))
                        frame))))
        (dirname path)))
      (fs
       (frame-val->dir
        (cdr
         (assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          (partial-collapse frame (dirname path)))))))
     (:instance
      abs-find-file-correctness-lemma-14
      (x (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path)))
      (frame (frame->frame (partial-collapse frame (dirname path))))
      (path (dirname path)))))))

(defthm
  abs-find-file-after-abs-mkdir-lemma-8
  (implies
   (and (not (frame-val->path (cdr (assoc-equal 0 frame))))
        (consp (assoc-equal 0
                            (partial-collapse frame (dirname path))))
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (frame-p frame)
        (no-duplicatesp-equal (strip-cars frame))
        (mv-nth '1 (collapse frame))
        (not (equal 0
                    (abs-find-file-src (partial-collapse frame (dirname path))
                                       (dirname path))))
        (abs-separate frame)
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame))))
   (equal (abs-find-file-helper
           (frame->root (partial-collapse frame (dirname path)))
           path)
          (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal"
    :in-theory (e/d (abs-mkdir abs-find-file abs-find-file-helper
                               abs-find-file-after-abs-mkdir-lemma-1
                               abs-find-file-after-abs-mkdir-lemma-4
                               len-when-consp fat32-filename-list-fix
                               abs-alloc abs-fs-fix)
                    (abs-find-file-after-abs-mkdir-lemma-3
                     abs-find-file-src-correctness-2
                     (:definition nth)
                     (:definition true-listp)
                     (:definition string-listp)
                     (:rewrite true-listp-when-string-list)
                     (:rewrite fat32-filename-p-correctness-1)))
    :use
    ((:instance abs-find-file-after-abs-mkdir-lemma-3
                (fs (frame->root (partial-collapse frame (dirname path))))
                (x (dirname path))
                (y (fat32-filename-list-fix path)))
     (:instance abs-find-file-src-correctness-2
                (frame (partial-collapse frame (dirname path)))
                (path (dirname path)))
     (:instance (:rewrite abs-find-file-helper-of-ctx-app-lemma-4)
                (path path)
                (fs (frame->root (partial-collapse frame (dirname path))))))
    :do-not-induct t)))

;; Inductive, so probably not worth disabling.
(defthm
  abs-find-file-after-abs-mkdir-lemma-9
  (implies
   (and (fat32-filename-list-prefixp x y)
        (not (fat32-filename-list-equiv x y))
        (not (equal (mv-nth 1 (abs-alloc fs x new-index))
                    (abs-fs-fix fs))))
   (equal (abs-find-file-helper (mv-nth 1 (abs-alloc fs x new-index))
                                y)
          (mv (abs-file-fix nil) *enoent*)))
  :hints (("goal" :in-theory (enable abs-find-file-helper
                                     abs-alloc fat32-filename-list-fix
                                     fat32-filename-list-equiv
                                     fat32-filename-list-prefixp abs-fs-fix)
           :induct (mv (abs-alloc fs x new-index)
                       (fat32-filename-list-prefixp x y)))))

(defthm
  abs-find-file-after-abs-mkdir-lemma-11
  (implies
   (and
    (equal
     (mv-nth 1
             (abs-find-file (partial-collapse frame (dirname path))
                            (dirname path)))
     0)
    (not (frame-val->path (cdr (assoc-equal 0 frame))))
    (equal (frame-val->src (cdr (assoc-equal 0 frame)))
           0)
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-directory-file-p
     (mv-nth 0
             (abs-find-file (partial-collapse frame (dirname path))
                            (dirname path))))
    (equal
     0
     (abs-find-file-src (partial-collapse frame (dirname path))
                        (dirname path)))
    (not
     (member-equal
      (find-new-index
       (strip-cars (partial-collapse frame (dirname path))))
      (abs-addrs
       (frame-val->dir
        (cdr
         (assoc-equal 0
                      (partial-collapse frame (dirname path)))))))))
   (not
    (equal
     (mv-nth
      1
      (abs-alloc
       (frame-val->dir
        (cdr (assoc-equal 0
                          (partial-collapse frame (dirname path)))))
       (dirname path)
       (find-new-index
        (strip-cars (partial-collapse frame (dirname path))))))
     (frame-val->dir
      (cdr
       (assoc-equal 0
                    (partial-collapse frame (dirname path))))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite abs-find-file-src-correctness-2))
    :use
    ((:instance (:rewrite abs-find-file-src-correctness-2)
                (path (dirname path))
                (frame (partial-collapse frame (dirname path))))))))

(defthm
  abs-find-file-after-abs-mkdir-lemma-10
  (implies
   (and
    (equal
     (mv-nth 1
             (abs-find-file (partial-collapse frame (dirname path))
                            (dirname path)))
     0)
    (not (frame-val->path (cdr (assoc-equal 0 frame))))
    (equal (frame-val->src (cdr (assoc-equal 0 frame)))
           0)
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-directory-file-p
     (mv-nth 0
             (abs-find-file (partial-collapse frame (dirname path))
                            (dirname path))))
    (equal
     0
     (abs-find-file-src (partial-collapse frame (dirname path))
                        (dirname path)))
    (not
     (member-equal
      (find-new-index
       (strip-cars (partial-collapse frame (dirname path))))
      (abs-addrs
       (frame-val->dir
        (cdr
         (assoc-equal 0
                      (partial-collapse frame (dirname path)))))))))
   (equal
    (abs-find-file-helper
     (mv-nth
      1
      (abs-alloc
       (frame-val->dir
        (cdr
         (assoc-equal 0
                      (partial-collapse frame (dirname path)))))
       (dirname path)
       (find-new-index
        (strip-cars (partial-collapse frame (dirname path))))))
     path)
    (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal"
    :in-theory (disable (:rewrite abs-find-file-after-abs-mkdir-lemma-9))
    :use
    ((:instance
      (:rewrite abs-find-file-after-abs-mkdir-lemma-9)
      (y path)
      (new-index
       (find-new-index
        (strip-cars (partial-collapse frame (dirname path)))))
      (x (dirname path))
      (fs
       (frame-val->dir
        (cdr
         (assoc-equal 0
                      (partial-collapse frame (dirname path)))))))
     (:instance
      (:rewrite abs-find-file-helper-of-ctx-app-lemma-4)
      (path path)
      (fs
       (mv-nth
        1
        (abs-alloc
         (frame-val->dir
          (cdr
           (assoc-equal
            0
            (partial-collapse frame (dirname path)))))
         (dirname path)
         (find-new-index
          (strip-cars
           (partial-collapse frame (dirname path))))))))))))

(defthm abs-find-file-after-abs-mkdir-lemma-12
  (subsetp-equal (frame-addrs-root frame)
                 (strip-cars frame))
  :hints (("goal" :in-theory (enable frame-addrs-root))))

(defthm
  abs-find-file-after-abs-mkdir-lemma-13
  (implies
   (and
    (mv-nth 1 (collapse frame))
    (not (frame-val->path (cdr (assoc-equal 0 frame))))
    (consp (assoc-equal 0
                        (partial-collapse frame (dirname path))))
    (equal (frame-val->src (cdr (assoc-equal 0 frame)))
           0)
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-separate frame)
    (abs-directory-file-p
     (mv-nth 0
             (abs-find-file (partial-collapse frame (dirname path))
                            (dirname path))))
    (subsetp-equal (abs-addrs (frame->root frame))
                   (frame-addrs-root (frame->frame frame))))
   (not
    (member-equal
     (find-new-index
      (strip-cars (partial-collapse frame (dirname path))))
     (abs-addrs
      (frame-val->dir$inline
       (cdr
        (assoc-equal '0
                     (partial-collapse frame (dirname path)))))))))
  :instructions
  (:promote
   (:dive 1)
   (:rewrite
    (:rewrite subsetp-member . 4)
    ((y (strip-cars (partial-collapse frame (dirname path))))))
   (:change-goal nil t)
   :bash
   (:=
    (frame-val->dir
     (cdr (assoc-equal 0
                       (partial-collapse frame (dirname path)))))
    (frame->root (partial-collapse frame (dirname path)))
    :hints (("goal" :in-theory (enable frame->root))))
   (:rewrite
    subsetp-trans2
    ((y
      (frame-addrs-root
       (frame->frame (partial-collapse frame (dirname path)))))))
   (:change-goal nil t)
   :bash
   :bash
   (:rewrite
    subsetp-trans
    ((y
      (strip-cars
       (frame->frame (partial-collapse frame (dirname path)))))))
   :bash (:bash ("goal" :in-theory (enable frame->frame)))))

(defthm abs-find-file-after-abs-mkdir-lemma-14
  (implies (fat32-filename-list-equiv (list (basename path))
                                      path)
           (equal (fat32-filename-fix (car path))
                  (basename path)))
  :instructions (:promote (:dive 1)
                          (:= path
                              (list (basename path))
                              :equiv fat32-filename-list-equiv$inline)
                          :top :bash))

(defthm
  abs-find-file-after-abs-mkdir-1
  (implies
   (and
    (mv-nth '1 (collapse frame))
    (equal (frame-val->path (cdr (assoc-equal 0 frame)))
           nil)
    (consp (assoc-equal 0
                        (partial-collapse frame (dirname path))))
    (equal (frame-val->src (cdr (assoc-equal 0 frame)))
           0)
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-separate frame)
    (subsetp-equal (abs-addrs (frame->root frame))
                   (frame-addrs-root (frame->frame frame))))
   (b*
       (((mv frame & mkdir-error-code)
         (abs-mkdir frame path)))
     (implies
      (equal mkdir-error-code 0)
      (b*
          (((mv file error-code)
            (abs-find-file frame path)))
        (and (equal error-code 0)
             (m1-file-equiv
              file
              (make-m1-file
               :dir-ent (dir-ent-install-directory-bit (dir-ent-fix nil)
                                                       t))))))))
  :hints
  (("goal" :in-theory (e/d (abs-mkdir abs-find-file abs-find-file-helper
                                      abs-find-file-after-abs-mkdir-lemma-1
                                      abs-find-file-after-abs-mkdir-lemma-4
                                      len-when-consp fat32-filename-list-fix
                                      abs-alloc abs-fs-fix)
                           (abs-mkdir-correctness-lemma-50
                            (:definition nth)
                            (:definition true-listp)
                            (:definition string-listp)
                            (:rewrite true-listp-when-string-list)
                            (:rewrite fat32-filename-p-correctness-1)
                            (:rewrite abs-find-file-correctness-lemma-2)
                            (:rewrite
                             abs-find-file-helper-when-m1-file-alist-p)
                            (:rewrite abs-alloc-correctness-1)
                            (:rewrite abs-fs-p-when-hifat-no-dups-p)
                            (:rewrite abs-file-alist-p-correctness-1)
                            (:rewrite consp-of-nthcdr)
                            (:rewrite
                             abs-find-file-correctness-1-lemma-18)
                            (:rewrite abs-find-file-correctness-1-lemma-3)
                            (:definition no-duplicatesp-equal)
                            (:rewrite abs-fs-p-correctness-1)
                            (:definition len)))
    :use abs-mkdir-correctness-lemma-50
    :do-not-induct t))
  :otf-flg t)

;; Taking this together with abs-mkdir-correctness-lemma-47, it can be
;; determined how the abs-alloc is going to turn out...
(defthm
  abs-mkdir-correctness-lemma-73
  (implies
   (and
    (not (atom path))
    (not
     (and
      (zp (mv-nth 1 (abs-find-file-helper fs path)))
      (abs-directory-file-p (mv-nth 0
                                    (abs-find-file-helper fs path))))))
   (equal (mv-nth 1 (abs-alloc fs path new-index))
          (abs-fs-fix fs)))
  :hints
  (("goal"
    :in-theory
    (e/d (abs-find-file-helper abs-alloc fat32-filename-list-fix)
         (ctx-app-ok-when-abs-complete-lemma-2 nfix))
    :expand
    ((:with
      put-assoc-equal-without-change
      (equal
       (put-assoc-equal
        (car path)
        (abs-file (abs-file->dir-ent (cdr (assoc-equal (car path) fs)))
                  (list (nfix new-index)))
        fs)
       fs))
     (abs-alloc fs path new-index)
     (abs-file-contents-fix (list (nfix new-index))))
    :induct (abs-find-file-helper fs path))))

(defthm
  abs-mkdir-correctness-lemma-74
  (implies
   (prefixp
    (dirname path)
    (frame-val->path
     (cdr
      (assoc-equal
       (abs-find-file-src (partial-collapse frame (dirname path))
                          (dirname path))
       frame))))
   (>=
    (len
     (frame-val->path
      (cdr
       (assoc-equal
        (abs-find-file-src (partial-collapse frame (dirname path))
                           (dirname path))
        frame))))
    (+ -1 (len path))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite abs-mkdir-correctness-lemma-73))
    :use
    (:instance
     (:rewrite abs-mkdir-correctness-lemma-73)
     (new-index
      (find-new-index
       (strip-cars (partial-collapse frame (dirname path)))))
     (path (dirname path))
     (fs
      (frame-val->dir
       (cdr
        (assoc-equal 0
                     (partial-collapse frame (dirname path)))))))))
  :rule-classes :linear)

(defthm
  abs-mkdir-correctness-lemma-75
  (implies
   (and
    (not
     (member-equal
      (basename path)
      (names-at
       (frame-val->dir
        (cdr
         (assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          (partial-collapse frame (dirname path)))))
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (abs-find-file-src
                         (partial-collapse frame (dirname path))
                         (dirname path))
                        frame))))
        (dirname path)))))
    (prefixp
     (dirname path)
     (frame-val->path
      (cdr
       (assoc-equal
        (abs-find-file-src (partial-collapse frame (dirname path))
                           (dirname path))
        frame))))
    (member-equal
     (basename path)
     (names-at
      (frame-val->dir
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         (partial-collapse frame (dirname path)))))
      nil))
    (<=
     (len
      (frame-val->path
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         frame))))
     (+ -1 (len path))))
   (not
    (equal
     (mv-nth
      1
      (abs-alloc
       (frame-val->dir
        (cdr
         (assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          (partial-collapse frame (dirname path)))))
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (abs-find-file-src
                         (partial-collapse frame (dirname path))
                         (dirname path))
                        frame))))
        (dirname path))
       (find-new-index
        (strip-cars (partial-collapse frame (dirname path))))))
     (frame-val->dir
      (cdr
       (assoc-equal
        (abs-find-file-src (partial-collapse frame (dirname path))
                           (dirname path))
        (partial-collapse frame (dirname path))))))))
  :hints
  (("goal"
    :in-theory (e/d (names-at)
                    ((:rewrite abs-mkdir-correctness-lemma-47 . 2)))
    :use
    (:instance
     (:rewrite abs-mkdir-correctness-lemma-47 . 2)
     (new-index
      (find-new-index
       (strip-cars (partial-collapse frame (dirname path)))))
     (path
      (nthcdr
       (len
        (frame-val->path
         (cdr
          (assoc-equal (abs-find-file-src
                        (partial-collapse frame (dirname path))
                        (dirname path))
                       frame))))
       (dirname path)))
     (fs
      (frame-val->dir
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         (partial-collapse frame (dirname path))))))))))

(defthm
  abs-mkdir-correctness-lemma-76
  (implies
   (and
    (equal (list (basename path))
           (fat32-filename-list-fix path))
    (abs-complete (frame-val->dir (cdr (assoc-equal 0 frame))))
    (not (consp (assoc-equal (basename path)
                             (frame-val->dir (cdr (assoc-equal 0 frame)))))))
   (equal
    (mv-nth
     1
     (hifat-place-file (frame->root frame)
                       path
                       '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                         (contents))))
    0))
  :instructions
  (:promote
   (:= path
       (list (basename path))
       :equiv fat32-filename-list-equiv$inline)
   (:dive 1 2)
   :x
   :top
   (:bash ("goal" :in-theory (enable fat32-filename-list-fix frame->root)))))

(defthm
  abs-mkdir-correctness-lemma-82
  (implies
   (and
    (equal (list (basename path))
           (fat32-filename-list-fix path))
    (abs-complete (frame-val->dir (cdr (assoc-equal 0 frame))))
    (not (consp (assoc-equal (basename path)
                             (frame-val->dir (cdr (assoc-equal 0 frame)))))))
   (hifat-equiv
    (mv-nth
     0
     (hifat-place-file (frame->root frame)
                       path
                       '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                         (contents))))
    (put-assoc-equal (basename path)
                     '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                       (contents))
                     (frame-val->dir (cdr (assoc-equal 0 frame))))))
  :instructions
  (:promote
   (:dive 1)
   (:= path
       (list (basename path))
       :equiv fat32-filename-list-equiv$inline)
   (:dive 2)
   :x
   :top
   (:bash ("goal" :in-theory (enable hifat-place-file
                                     fat32-filename-list-fix frame->root)))))

(defthm abs-mkdir-correctness-lemma-83
  (implies (fat32-filename-list-equiv (list (basename path))
                                      path)
           (consp path))
  :hints (("goal" :in-theory (enable fat32-filename-list-equiv)
           :do-not-induct t))
  :rule-classes :forward-chaining)

;; How come this was not already proven?
(defthm
 abs-mkdir-correctness-lemma-85
 (implies
      (and (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                    (fat32-filename-list-fix path))
           (equal (mv-nth 1 (abs-find-file frame path))
                  *enoent*))
      (equal (abs-find-file-helper
                  (frame-val->dir (cdr (assoc-equal x frame)))
                  (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                          path))
             (abs-find-file frame path)))
 :hints (("goal" :in-theory (enable abs-find-file hifat-find-file))))

;; This is nice and general.
(defthm
  abs-mkdir-correctness-lemma-86
  (implies
   (and
    (fat32-filename-list-equiv
     x-path
     (nthcdr
      (len (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                              frame))))
      path))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (prefixp (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                                frame)))
             (fat32-filename-list-fix path)))
   (equal (abs-find-file-helper (frame-val->dir (cdr (assoc-equal
                                                      (abs-find-file-src frame path) frame)))
                                x-path)
          (abs-find-file frame path)))
  :hints
  (("goal" :in-theory (e/d nil
                           (abs-find-file-src-correctness-2 nfix nat-equiv))
    :use abs-find-file-src-correctness-2
    :do-not-induct t)))

(defthm
  abs-mkdir-correctness-lemma-87
  (implies
   (and (no-duplicatesp-equal (strip-cars frame))
        (not (zp (abs-find-file-src frame path))))
   (prefixp
    (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                       frame)))
    (fat32-filename-list-fix path)))
  :hints (("goal" :in-theory (enable abs-find-file-src))))

(defthmd
  abs-mkdir-correctness-lemma-88
  (implies
   (fat32-filename-p x)
   (iff (member-equal x (names-at fs relpath))
        (zp (mv-nth 1
                    (abs-find-file-helper fs (append relpath (list x)))))))
  :hints (("goal" :in-theory (enable names-at abs-find-file-helper))))

(defthm abs-mkdir-correctness-lemma-90
  (implies (fat32-filename-list-equiv (list (basename path))
                                      path)
           (not (consp (cdr path))))
  :hints (("goal" :in-theory (enable fat32-filename-list-equiv)))
  :rule-classes :forward-chaining)

(defthm
  abs-mkdir-correctness-lemma-91
  (implies
   (and
    (fat32-filename-list-equiv (list (basename path))
                               path)
    (abs-complete (frame-val->dir (cdr (assoc-equal 0 frame))))
    (not (consp (assoc-equal (basename path)
                             (frame-val->dir (cdr (assoc-equal 0 frame)))))))
   (equal
    (mv-nth
     1
     (hifat-place-file (frame->root frame)
                       path
                       '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                         (contents))))
    0))
  :hints (("goal" :in-theory (enable hifat-place-file frame->root))))

(defthm
  abs-mkdir-correctness-lemma-92
  (implies (consp (assoc-equal (basename path)
                               (frame-val->dir (cdr (assoc-equal 0 frame)))))
           (consp (assoc-equal (basename path)
                               (frame->root frame))))
  :hints (("goal" :in-theory (enable frame->root))))

(defthm
  abs-mkdir-correctness-lemma-93
  (implies
   (and
    (not
     (equal
      (mv-nth
       1
       (abs-alloc
        (frame-val->dir
         (cdr
          (assoc-equal 0
                       (partial-collapse frame (dirname path)))))
        (dirname path)
        (find-new-index
         (strip-cars (partial-collapse frame (dirname path))))))
      (frame-val->dir
       (cdr
        (assoc-equal 0
                     (partial-collapse frame (dirname path)))))))
    (consp (dirname path)))
   (and
    (zp
     (mv-nth
      1
      (abs-find-file-helper
       (frame-val->dir
        (cdr (assoc-equal 0
                          (partial-collapse frame (dirname path)))))
       (dirname path))))
    (abs-directory-file-p
     (mv-nth
      0
      (abs-find-file-helper
       (frame-val->dir
        (cdr (assoc-equal 0
                          (partial-collapse frame (dirname path)))))
       (dirname path))))))
  :instructions (:promote (:contrapose 1)
                          (:dive 1)
                          (:rewrite abs-mkdir-correctness-lemma-73)
                          :top :bash)
  :rule-classes :forward-chaining)

(defthm
  abs-mkdir-correctness-lemma-94
  (implies
   (and
    (prefixp
     (frame-val->path
      (cdr
       (assoc-equal
        (abs-find-file-src (partial-collapse frame (dirname path))
                           (dirname path))
        frame)))
     (dirname path))
    (<= 0 (+ -1 (len path)))
    (<=
     (+ -1 (len path))
     (len
      (frame-val->path
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         frame))))))
   (ctx-app-ok
    (list
     (find-new-index
      (strip-cars (partial-collapse frame (dirname path)))))
    (find-new-index
     (strip-cars (partial-collapse frame (dirname path))))
    (nthcdr
     (len
      (frame-val->path
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         frame))))
     (dirname path))))
  :hints (("goal" :in-theory (disable (:rewrite nthcdr-when->=-n-len-l))
           :use (:instance (:rewrite nthcdr-when->=-n-len-l)
                           (l (dirname path))
                           (n (+ -1 (len path)))))))

(defthm abs-mkdir-correctness-lemma-97
  (implies (not (consp path))
           (equal (dirname path) nil))
  :hints (("goal" :in-theory (enable dirname
                                     basename-dirname-helper)))
  :rule-classes :type-prescription)

(defthm
  abs-mkdir-correctness-lemma-98
  (implies
   (and (hifat-equiv (mv-nth 0 (collapse frame))
                     fs)
        (no-duplicatesp-equal (strip-cars frame))
        (frame-p frame)
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (mv-nth 1 (collapse frame))
        (abs-separate frame)
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame)))
        (m1-directory-file-p
         (mv-nth 0
                 (hifat-find-file fs (dirname path)))))
   (m1-directory-file-p
    (mv-nth
     '0
     (hifat-find-file
      (mv-nth '0
              (collapse (partial-collapse frame (dirname path))))
      (dirname path))))))

;; Again, most likely an inductive proof, doesn't seem worth disabling...
(defthm abs-mkdir-correctness-lemma-99
  (implies (and (hifat-equiv fs1 fs2)
                (syntaxp (not (term-order fs1 fs2)))
                (fat32-filename-p name)
                (m1-file-alist-p fs1)
                (m1-file-alist-p fs2)
                (hifat-no-dups-p fs1)
                (hifat-no-dups-p fs2))
           (iff (consp (assoc-equal name fs1))
                (consp (assoc-equal name fs2))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-equiv))))

(defthm
  abs-mkdir-correctness-lemma-102
  (implies
   (and (hifat-equiv (mv-nth 0 (collapse frame))
                     fs)
        (m1-directory-file-p
         (mv-nth 0
                 (hifat-find-file fs (dirname path)))))
   (m1-directory-file-p (mv-nth 0
                                (hifat-find-file (mv-nth 0 (collapse frame))
                                                 (dirname path))))))

(defthm
  abs-mkdir-correctness-lemma-103
  (implies
   (and (hifat-equiv (mv-nth 0 (collapse frame))
                     fs)
        (no-duplicatesp-equal (strip-cars frame))
        (frame-p frame)
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (mv-nth 1 (collapse frame))
        (abs-separate frame)
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame)))
        (m1-directory-file-p
         (mv-nth 0
                 (hifat-find-file fs (dirname path))))
        (equal (mv-nth 1
                       (hifat-find-file fs (dirname path)))
               0))
   (iff
    (consp
     (assoc-equal
      (basename path)
      (m1-file->contents
       (mv-nth
        0
        (hifat-find-file
         (mv-nth 0
                 (collapse (partial-collapse frame (dirname path))))
         (dirname path))))))
    (consp (assoc-equal
            (basename path)
            (m1-file->contents
             (mv-nth 0
                     (hifat-find-file (mv-nth 0 (collapse frame))
                                      (dirname path))))))))
  :hints
  (("goal"
    :do-not-induct t
    :use
    ((:instance
      abs-mkdir-correctness-lemma-99
      (name (basename path))
      (fs1
       (m1-file->contents
        (mv-nth
         0
         (hifat-find-file
          (mv-nth
           0
           (collapse (partial-collapse frame (dirname path))))
          (dirname path)))))
      (fs2 (m1-file->contents
            (mv-nth 0
                    (hifat-find-file (mv-nth 0 (collapse frame))
                                     (dirname path))))))))))

(defthm
  abs-mkdir-correctness-lemma-104
  (implies
   (and
    (no-duplicatesp-equal (strip-cars frame))
    (frame-p frame)
    (equal (frame-val->src (cdr (assoc-equal 0 frame)))
           0)
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (mv-nth 1 (collapse frame))
    (abs-separate frame)
    (subsetp-equal (abs-addrs (frame->root frame))
                   (frame-addrs-root (frame->frame frame)))
    (m1-directory-file-p (mv-nth 0
                                 (hifat-find-file (mv-nth 0 (collapse frame))
                                                  (dirname path)))))
   (abs-directory-file-p
    (mv-nth
     0
     (hifat-find-file
      (mv-nth 0
              (collapse (partial-collapse frame (dirname path))))
      (dirname path)))))
  :hints
  (("goal"
    :in-theory (e/d (hifat-place-file)
                    ((:rewrite partial-collapse-correctness-1 . 1)))
    :use ((:instance (:rewrite partial-collapse-correctness-1 . 1)
                     (path (dirname path))
                     (frame frame)))
    :expand
    (:with
     (:rewrite hifat-equiv-when-absfat-equiv)
     (absfat-equiv
      (mv-nth 0
              (collapse (partial-collapse frame (dirname path))))
      fs))
    :do-not-induct t)))

(defthm
  abs-mkdir-correctness-lemma-105
  (implies
   (and
    (m1-directory-file-p (mv-nth 0
                                 (hifat-find-file (mv-nth 0 (collapse frame))
                                                  (dirname path))))
    (consp path)
    (equal (mv-nth 1
                   (hifat-find-file (mv-nth 0 (collapse frame))
                                    (dirname path)))
           0))
   (equal
    (hifat-place-file (mv-nth 0 (collapse frame))
                      path
                      '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                                 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                        (contents)))
    (mv
     (mv-nth
      0
      (hifat-place-file
       (mv-nth 0 (collapse frame))
       (dirname path)
       (m1-file
        (m1-file->dir-ent (mv-nth 0
                                  (hifat-find-file (mv-nth 0 (collapse frame))
                                                   (dirname path))))
        (mv-nth 0
                (hifat-place-file
                 (m1-file->contents
                  (mv-nth 0
                          (hifat-find-file (mv-nth 0 (collapse frame))
                                           (dirname path))))
                 (list (basename path))
                 '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                   (contents)))))))
     (mv-nth
      1
      (hifat-place-file
       (m1-file->contents (mv-nth 0
                                  (hifat-find-file (mv-nth 0 (collapse frame))
                                                   (dirname path))))
       (list (basename path))
       '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
         (contents)))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite hifat-place-file-of-append-1))
    :use (:instance (:rewrite hifat-place-file-of-append-1)
                    (file '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                            (contents)))
                    (y (list (basename path)))
                    (x (dirname path))
                    (fs (mv-nth 0 (collapse frame)))))))

(defthm
  abs-mkdir-correctness-lemma-106
  (implies
   (and
    (no-duplicatesp-equal (strip-cars frame))
    (frame-p frame)
    (equal (frame-val->src (cdr (assoc-equal 0 frame)))
           0)
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (mv-nth 1 (collapse frame))
    (abs-separate frame)
    (subsetp-equal (abs-addrs (frame->root frame))
                   (frame-addrs-root (frame->frame frame)))
    (m1-directory-file-p (mv-nth 0
                                 (hifat-find-file (mv-nth 0 (collapse frame))
                                                  (dirname path))))
    (equal (mv-nth 1
                   (hifat-find-file (mv-nth 0 (collapse frame))
                                    (dirname path)))
           0))
   (iff
    (consp
     (assoc-equal
      (basename path)
      (abs-file->contents
       (mv-nth
        0
        (hifat-find-file
         (mv-nth
          0
          (collapse (partial-collapse frame (dirname path))))
         (dirname path))))))
    (consp
     (assoc-equal (basename path)
                  (m1-file->contents
                   (mv-nth 0
                           (hifat-find-file (mv-nth 0 (collapse frame))
                                            (dirname path))))))))
  :hints
  (("goal"
    :in-theory (e/d (hifat-place-file)
                    ((:rewrite partial-collapse-correctness-1 . 1)))
    :use ((:instance (:rewrite partial-collapse-correctness-1 . 1)
                     (path (dirname path))
                     (frame frame)))
    :expand
    (:with
     (:rewrite hifat-equiv-when-absfat-equiv)
     (absfat-equiv
      (mv-nth 0
              (collapse (partial-collapse frame (dirname path))))
      fs))
    :do-not-induct t)))

(defthm abs-mkdir-correctness-lemma-108
  (equal (nthcdr (+ -1 (len path))
                 (dirname path))
         nil)
  :hints (("goal" :in-theory (e/d nil (len-of-dirname))
           :use len-of-dirname)))

(defthm
  abs-mkdir-correctness-lemma-122
  (implies
   (and (m1-directory-file-p
         (mv-nth 0
                 (hifat-find-file fs (dirname path))))
        (consp path)
        (equal (mv-nth 1
                       (hifat-find-file fs (dirname path)))
               0))
   (equal (hifat-find-file fs path)
          (hifat-find-file
           (m1-file->contents
            (mv-nth 0
                    (hifat-find-file fs (dirname path))))
           (list (basename path)))))
  :hints
  (("goal" :in-theory (disable (:rewrite hifat-find-file-of-append-1))
    :use (:instance (:rewrite hifat-find-file-of-append-1)
                    (y (list (basename path)))
                    (x (dirname path))
                    (fs fs)))))

(defthm
  abs-mkdir-correctness-lemma-123
  (implies
   (and (no-duplicatesp-equal (strip-cars frame))
        (frame-p frame)
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (m1-file-alist-p fs)
        (mv-nth 1 (collapse frame))
        (hifat-equiv (mv-nth 0 (collapse frame))
                     fs)
        (abs-separate frame)
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame)))
        (equal (mv-nth 1
                       (hifat-find-file fs (dirname path)))
               0)
        (m1-directory-file-p
         (mv-nth 0
                 (hifat-find-file fs (dirname path)))))
   (iff
    (consp
     (assoc-equal (basename path)
                  (m1-file->contents
                   (mv-nth 0
                           (hifat-find-file (mv-nth 0 (collapse frame))
                                            (dirname path))))))
    (consp
     (assoc-equal
      (basename path)
      (m1-file->contents
       (mv-nth 0
               (hifat-find-file fs (dirname path))))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite abs-mkdir-correctness-lemma-99))
    :use
    (:instance
     (:rewrite abs-mkdir-correctness-lemma-99)
     (fs1
      (m1-file->contents (mv-nth 0
                                 (hifat-find-file (mv-nth 0 (collapse frame))
                                                  (dirname path)))))
     (name (basename path))
     (fs2 (m1-file->contents
           (mv-nth 0
                   (hifat-find-file fs (dirname path)))))))))

(defthm
  abs-mkdir-correctness-lemma-36
  (implies (and (not (consp path))
                (frame-reps-fs frame fs))
           (frame-reps-fs (mv-nth 0 (abs-mkdir frame path))
                          (mv-nth 0 (collapse frame))))
  :hints
  (("goal"
    :in-theory
    (e/d (abs-mkdir collapse frame-reps-fs)
         ((:definition assoc-equal)
          (:rewrite abs-find-file-correctness-2)
          (:rewrite consp-of-assoc-of-frame->frame)
          (:rewrite default-cdr)
          (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8
                    . 2)
          (:rewrite prefixp-when-equal-lengths)
          (:rewrite subsetp-when-prefixp)
          (:rewrite partial-collapse-correctness-lemma-24)))
    :do-not-induct t
    :use (:instance
          (:rewrite hifat-equiv-when-absfat-equiv)
          (abs-file-alist2 fs)
          (abs-file-alist1 (mv-nth 0 (collapse frame)))))))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies
      (and (absfat-equiv fs1 fs2)
           (abs-fs-p fs1)
           (abs-fs-p fs2))
      (and (absfat-equiv
            (abs-file->contents (mv-nth 0 (abs-find-file-helper fs1 path)))
            (abs-file->contents (mv-nth 0 (abs-find-file-helper fs2 path))))
           (equal
            (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs1 path)))
            (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs2 path))))
           (equal (mv-nth 1 (abs-find-file-helper fs1 path))
                  (mv-nth 1 (abs-find-file-helper fs2 path)))))
     :hints (("goal" :in-theory (enable abs-find-file-helper)))))

  (defthm
    abs-mkdir-correctness-lemma-128
    (implies
     (absfat-equiv fs1 fs2)
     (and (absfat-equiv
           (abs-file->contents (mv-nth 0 (abs-find-file-helper fs1 path)))
           (abs-file->contents (mv-nth 0 (abs-find-file-helper fs2 path))))
          (equal
           (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs1 path)))
           (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs2 path))))
          (equal (mv-nth 1 (abs-find-file-helper fs1 path))
                 (mv-nth 1 (abs-find-file-helper fs2 path)))))
    :hints
    (("goal"
      :in-theory (e/d (abs-file-p-alt abs-fs-fix m1-regular-file-p)
                      ((:rewrite abs-file-p-of-abs-find-file-helper)))
      :do-not-induct t
      :use ((:instance lemma (fs1 (abs-fs-fix fs1))
                       (fs2 (abs-fs-fix fs2)))
            (:instance lemma (fs1 (abs-fs-fix fs2))
                       (fs2 (abs-fs-fix fs1)))
            (:instance (:rewrite abs-file-p-of-abs-find-file-helper)
                       (path path)
                       (fs fs2))
            (:instance (:rewrite abs-file-p-of-abs-find-file-helper)
                       (path path)
                       (fs fs1)))))
    :rule-classes
    ((:congruence
      :corollary
      (implies
       (absfat-equiv fs1 fs2)
       (absfat-equiv
        (abs-file->contents (mv-nth 0 (abs-find-file-helper fs1 path)))
        (abs-file->contents (mv-nth 0 (abs-find-file-helper fs2 path))))))
     (:congruence
      :corollary
      (implies
       (absfat-equiv fs1 fs2)
       (equal
        (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs1 path)))
        (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs2 path))))))
     (:congruence
      :corollary
      (implies
       (absfat-equiv fs1 fs2)
       (equal
        (mv-nth 1 (abs-find-file-helper fs1 path))
        (mv-nth 1 (abs-find-file-helper fs2 path)))))
     (:rewrite
      :corollary
      (implies
       (and
        (absfat-equiv fs1 fs2)
        (syntaxp (not (term-order fs1 fs2)))
        (abs-fs-p fs1)
        (abs-complete fs1))
       (and (absfat-equiv
             (abs-file->contents (mv-nth 0 (hifat-find-file fs1 path)))
             (abs-file->contents (mv-nth 0 (abs-find-file-helper fs2 path))))
            (equal
             (m1-directory-file-p (mv-nth 0 (hifat-find-file fs1 path)))
             (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs2 path))))
            (equal (mv-nth 1 (hifat-find-file fs1 path))
                   (mv-nth 1 (abs-find-file-helper fs2 path)))))))))

(defthmd
  abs-mkdir-correctness-lemma-129
  (implies
   (and
    (zp (abs-find-file-src frame path))
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (mv-nth 1 (collapse frame))
    (subsetp-equal (abs-addrs (frame->root frame))
                   (frame-addrs-root (frame->frame frame)))
    (abs-separate frame)
    (abs-complete (abs-file->contents (mv-nth 0 (abs-find-file frame path))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (consp (assoc-equal '0 frame)))
   (and
    (equal (abs-find-file-helper (frame-val->dir (cdr (assoc-equal 0 frame)))
                                 path)
           (hifat-find-file (mv-nth 0 (collapse frame))
                            path))
    (equal (abs-find-file-helper (frame->root frame)
                                 path)
           (hifat-find-file (mv-nth 0 (collapse frame))
                            path))))
  :hints (("goal" :in-theory (e/d (frame->root)
                                  (abs-mkdir-correctness-lemma-86))
           :do-not-induct t
           :use (:instance abs-mkdir-correctness-lemma-86
                           (x-path path)))))

(defthm
  abs-mkdir-correctness-lemma-139
  (implies
   (and
    (prefixp
     (frame-val->path
      (cdr
       (assoc-equal
        (abs-find-file-src (partial-collapse frame (dirname path))
                           (dirname path))
        frame)))
     (dirname path))
    (< 1 (len path)))
   (equal
    (mv-nth
     0
     (abs-place-file-helper
      (frame-val->dir
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         (partial-collapse frame (dirname path)))))
      (append
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (abs-find-file-src
                         (partial-collapse frame (dirname path))
                         (dirname path))
                        frame))))
        (dirname path))
       (list (basename path)))
      '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
        (contents))))
    (mv-nth
     0
     (abs-place-file-helper
      (frame-val->dir
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         (partial-collapse frame (dirname path)))))
      (nthcdr
       (len
        (frame-val->path
         (cdr
          (assoc-equal (abs-find-file-src
                        (partial-collapse frame (dirname path))
                        (dirname path))
                       frame))))
       path)
      '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
        (contents))))))
  :instructions
  (promote
   (:dive 1 2 2 1 2)
   (:rewrite dirname-alt)
   :top (:dive 1 2 2 2 1)
   (:rewrite basename-alt)
   (:dive 1 1)
   (:rewrite last-alt)
   :top
   (:bash
    ("goal"
     :in-theory (e/d nil)
     :use
     (:instance
      take-of-nthcdr
      (n1
       (-
        (+ -1 (len path))
        (len
         (frame-val->path
          (cdr
           (assoc-equal (abs-find-file-src
                         (partial-collapse frame (dirname path))
                         (dirname path))
                        frame))))))
      (n2
       (len
        (frame-val->path
         (cdr
          (assoc-equal (abs-find-file-src
                        (partial-collapse frame (dirname path))
                        (dirname path))
                       frame)))))
      (l path))))
   (:dive 1 2 2 1)
   := :top
   (:=
    (list (nth (+ -1 (len path)) path))
    (nthcdr
     (+
      -1 (len path)
      (-
       (len
        (frame-val->path
         (cdr
          (assoc-equal (abs-find-file-src
                        (partial-collapse frame (dirname path))
                        (dirname path))
                       frame))))))
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          frame))))
      path))
    :hints :none
    :equiv list-equiv)
   (:dive 1 2 2)
   (:claim
    (<=
     (+
      -1 (len path)
      (-
       (len
        (frame-val->path
         (cdr
          (assoc-equal (abs-find-file-src
                        (partial-collapse frame (dirname path))
                        (dirname path))
                       frame))))))
     (len
      (nthcdr
       (len
        (frame-val->path
         (cdr
          (assoc-equal (abs-find-file-src
                        (partial-collapse frame (dirname path))
                        (dirname path))
                       frame))))
       path))))
   (:rewrite binary-append-take-nthcdr)
   :top :bash (:dive 2)
   (:rewrite nthcdr-of-nthcdr)
   :top :bash
   (:= (nthcdr (+ -1 (len path)) path)
       (cons (car (nthcdr (+ -1 (len path)) path))
             (cdr (nthcdr (+ -1 (len path))
                          path)))
       :hints :none)
   (:bash ("goal" :in-theory (disable (:rewrite nthcdr-of-nthcdr))
           :use (:instance (:rewrite nthcdr-of-nthcdr)
                           (x path)
                           (b (+ -1 (len path)))
                           (a 1))))
   (:dive 2)
   (:rewrite cons-car-cdr)
   :top :bash))

(defthmd
  abs-mkdir-correctness-lemma-157
  (implies
   (and
    (prefixp
     (frame-val->path
      (cdr
       (assoc-equal
        (abs-find-file-src (partial-collapse frame (dirname path))
                           (dirname path))
        frame)))
     (dirname path))
    (consp path))
   (fat32-filename-list-equiv
    (binary-append
     (nthcdr
      (len
       (frame-val->path$inline
        (cdr
         (assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          frame))))
      (dirname path))
     (cons (basename path) 'nil))
    (if
     (< 1 (len path))
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          frame))))
      path)
     (list (car path)))))
  :instructions
  (:promote
   (:dive 1 1 2)
   (:rewrite dirname-alt)
   :top (:dive 1 2 1)
   (:rewrite basename-alt)
   (:dive 1 1)
   (:rewrite last-alt)
   :top :bash
   (:bash
    ("goal"
     :in-theory (e/d nil)
     :use
     (:instance
      take-of-nthcdr
      (n1
       (-
        (+ -1 (len path))
        (len
         (frame-val->path
          (cdr
           (assoc-equal (abs-find-file-src
                         (partial-collapse frame (dirname path))
                         (dirname path))
                        frame))))))
      (n2
       (len
        (frame-val->path
         (cdr
          (assoc-equal (abs-find-file-src
                        (partial-collapse frame (dirname path))
                        (dirname path))
                       frame)))))
      (l path))))
   (:dive 1 1)
   := :top
   (:=
    (list (nth (+ -1 (len path)) path))
    (nthcdr
     (+
      -1 (len path)
      (-
       (len
        (frame-val->path
         (cdr
          (assoc-equal (abs-find-file-src
                        (partial-collapse frame (dirname path))
                        (dirname path))
                       frame))))))
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          frame))))
      path))
    :hints :none
    :equiv list-equiv)
   (:dive 1)
   (:claim
    (and
     (<=
      (+
       -1 (len path)
       (-
        (len
         (frame-val->path
          (cdr
           (assoc-equal (abs-find-file-src
                         (partial-collapse frame (dirname path))
                         (dirname path))
                        frame))))))
      (len
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (abs-find-file-src
                         (partial-collapse frame (dirname path))
                         (dirname path))
                        frame))))
        path)))))
   (:rewrite binary-append-take-nthcdr)
   :top (:change-goal nil t)
   (:dive 2)
   (:rewrite nthcdr-of-nthcdr)
   :top :bash
   (:= (nthcdr (+ -1 (len path)) path)
       (cons (car (nthcdr (+ -1 (len path)) path))
             (cdr (nthcdr (+ -1 (len path))
                          path)))
       :hints :none)
   (:bash ("goal" :in-theory (disable (:rewrite nthcdr-of-nthcdr))
           :use (:instance (:rewrite nthcdr-of-nthcdr)
                           (x path)
                           (b (+ -1 (len path)))
                           (a 1))))
   (:dive 2)
   (:rewrite cons-car-cdr)
   :top
   :bash :bash))

(defthm
  hifat-equiv-of-put-assoc-equal-1
  (implies (and (hifat-equiv (m1-file->contents file1)
                             (m1-file->contents file2))
                (syntaxp (not (term-order file1 file2)))
                (m1-directory-file-p (m1-file-fix file1))
                (m1-directory-file-p (m1-file-fix file2)))
           (hifat-equiv (put-assoc-equal name file1 fs)
                        (put-assoc-equal name file2 fs)))
  :hints
  (("goal"
    :induct (mv (put-assoc-equal name file1 fs)
                (put-assoc-equal name file2 fs))
    :in-theory
    (e/d (hifat-no-dups-p hifat-equiv)
         (hifat-subsetp-reflexive-lemma-4
          (:rewrite hifat-file-alist-fix-when-hifat-no-dups-p)
          (:rewrite abs-find-file-helper-when-m1-file-alist-p-lemma-1)
          (:rewrite abs-fs-fix-of-put-assoc-equal-lemma-1)
          (:rewrite abs-file-fix-when-abs-file-p)
          (:rewrite abs-fs-fix-of-put-assoc-equal-lemma-2)
          (:rewrite collapse-hifat-place-file-lemma-10))))
   ("subgoal *1/2"
    :use
    (:instance
     hifat-subsetp-reflexive-lemma-4
     (x
      (list
       (cons (fat32-filename-fix (car (car fs)))
             (m1-file (m1-file->dir-ent file1)
                      (hifat-file-alist-fix (m1-file->contents file1))))))
     (y (hifat-file-alist-fix (cdr fs)))))))

(defthm
  hifat-place-file-when-hifat-equiv-lemma-1
  (implies
   (and
    (hifat-equiv
     (mv-nth
      0
      (hifat-place-file
       (m1-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                            (hifat-file-alist-fix fs))))
       (cdr path)
       file1))
     (mv-nth
      0
      (hifat-place-file
       (m1-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                            (hifat-file-alist-fix fs))))
       (cdr path)
       file2)))
    (syntaxp (not (term-order file1 file2))))
   (hifat-equiv
    (put-assoc-equal
     (fat32-filename-fix (car path))
     (m1-file
      (m1-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car path))
                                          (hifat-file-alist-fix fs))))
      (mv-nth
       0
       (hifat-place-file
        (m1-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                             (hifat-file-alist-fix fs))))
        (cdr path)
        file1)))
     (hifat-file-alist-fix fs))
    (put-assoc-equal
     (fat32-filename-fix (car path))
     (m1-file
      (m1-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car path))
                                          (hifat-file-alist-fix fs))))
      (mv-nth
       0
       (hifat-place-file
        (m1-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                             (hifat-file-alist-fix fs))))
        (cdr path)
        file2)))
     (hifat-file-alist-fix fs))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite hifat-equiv-of-put-assoc-equal-1))
    :use
    (:instance
     (:rewrite hifat-equiv-of-put-assoc-equal-1)
     (fs (hifat-file-alist-fix fs))
     (file1
      (m1-file
       (m1-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car path))
                                           (hifat-file-alist-fix fs))))
       (mv-nth
        0
        (hifat-place-file
         (m1-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                              (hifat-file-alist-fix fs))))
         (cdr path)
         file1))))
     (file2
      (m1-file
       (m1-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car path))
                                           (hifat-file-alist-fix fs))))
       (mv-nth
        0
        (hifat-place-file
         (m1-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                              (hifat-file-alist-fix fs))))
         (cdr path)
         file2))))
     (name (fat32-filename-fix (car path)))))))

(defthm
  hifat-place-file-when-hifat-equiv-lemma-3
  (implies (and (hifat-equiv (m1-file->contents file1)
                             (m1-file->contents file2))
                (syntaxp (not (term-order file1 file2)))
                (m1-directory-file-p (m1-file-fix file1))
                (m1-directory-file-p (m1-file-fix file2)))
           (hifat-equiv (put-assoc-equal (fat32-filename-fix (car path))
                                         (m1-file-fix file1)
                                         (hifat-file-alist-fix fs))
                        (put-assoc-equal (fat32-filename-fix (car path))
                                         (m1-file-fix file2)
                                         (hifat-file-alist-fix fs))))
  :instructions (:promote (:dive 1)
                          (:rewrite hifat-equiv-of-put-assoc-equal-1
                                    ((file2 (m1-file-fix file2))))
                          :top
                          :bash :bash
                          :bash :bash))

(defthm hifat-place-file-when-hifat-equiv-1
  (implies (and (hifat-equiv (m1-file->contents file1)
                             (m1-file->contents file2))
                (syntaxp (not (term-order file1 file2)))
                (m1-directory-file-p (m1-file-fix file1))
                (m1-directory-file-p (m1-file-fix file2)))
           (hifat-equiv (mv-nth 0 (hifat-place-file fs path file1))
                        (mv-nth 0 (hifat-place-file fs path file2))))
  :hints (("goal" :in-theory (enable hifat-place-file))))

(defthm
  hifat-equiv-of-put-assoc-lemma-1
  (implies (and (m1-file-alist-p fs1)
                (hifat-no-dups-p fs1)
                (hifat-subsetp fs1 fs2)
                (hifat-no-dups-p (m1-file->contents val)))
           (hifat-subsetp (put-assoc-equal key val fs1)
                          (put-assoc-equal key val fs2)))
  :hints (("goal" :in-theory (enable hifat-subsetp)
           :induct (mv (hifat-subsetp fs1 fs2)
                       (put-assoc-equal key val fs1)))))

(defthm hifat-equiv-of-put-assoc-2
  (implies (and (hifat-equiv fs1 fs2)
                (syntaxp (not (term-order fs1 fs2)))
                (m1-file-alist-p fs1)
                (hifat-no-dups-p fs1)
                (m1-file-alist-p fs2)
                (hifat-no-dups-p fs2)
                (m1-file-p val)
                (fat32-filename-p key)
                (hifat-no-dups-p (m1-file->contents val)))
           (hifat-equiv (put-assoc-equal key val fs1)
                        (put-assoc-equal key val fs2)))
  :hints (("goal" :in-theory (enable hifat-equiv)
           :do-not-induct t)))

(defthm
  abs-mkdir-correctness-lemma-126
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
                    ((:rewrite chain-ends-in-abs-complete-lemma-5
                               . 1)))
    :use ((:instance (:rewrite chain-ends-in-abs-complete-lemma-5
                               . 1)
                     (y (strip-cars (frame->frame frame)))
                     (n (collapse-1st-index frame x))
                     (x x)
                     (frame frame))
          chain-ends-in-abs-complete-lemma-9)))
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

;; Kinda general.
(defthmd
  abs-mkdir-correctness-lemma-30
  (implies
   (and (zp (mv-nth 1 (abs-find-file-helper fs path)))
        (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs path))))
   (equal (mv-nth 0 (abs-alloc fs path new-index))
          (abs-file->contents (mv-nth 0 (abs-find-file-helper fs path)))))
  :hints (("goal" :in-theory (enable abs-alloc abs-find-file-helper))))

(defthm
  abs-mkdir-correctness-lemma-197
  (subsetp-equal (abs-addrs (mv-nth 0 (abs-alloc fs path new-index)))
                 (abs-addrs (abs-fs-fix fs)))
  :hints (("goal" :in-theory (enable abs-alloc abs-fs-fix abs-addrs))))

(encapsulate
  ()

  (local
   (in-theory
    (e/d (collapse ctx-app 1st-complete
                   collapse-this hifat-place-file
                   hifat-find-file
                   abs-alloc
                   abs-mkdir-correctness-lemma-16
                   assoc-equal-of-frame-with-root
                   abs-separate dist-names abs-fs-fix
                   abs-addrs frame-addrs-root
                   frame->root-of-put-assoc
                   frame->frame-of-put-assoc
                   abs-mkdir-correctness-lemma-88
                   abs-find-file-helper
                   abs-place-file-helper)
         ((:rewrite put-assoc-equal-without-change . 2)
          (:rewrite
           abs-separate-of-frame->frame-of-collapse-this-lemma-8
           . 2)
          (:rewrite abs-addrs-of-ctx-app-2)
          (:rewrite remove-when-absent)
          (:rewrite
           abs-fs-fix-of-put-assoc-equal-lemma-1)
          (:linear count-free-clusters-correctness-1)
          (:rewrite
           partial-collapse-correctness-lemma-24)
          (:rewrite m1-file-p-when-m1-regular-file-p)
          (:definition len)
          (:rewrite
           abs-addrs-when-m1-file-alist-p-lemma-2)
          (:rewrite nthcdr-when->=-n-len-l)
          (:rewrite abs-file-fix-when-abs-file-p)
          (:rewrite
           ctx-app-ok-when-absfat-equiv-lemma-4)
          (:rewrite abs-find-file-correctness-lemma-2)
          (:rewrite assoc-after-remove-assoc)
          (:rewrite abs-mkdir-correctness-lemma-14)
          (:definition acl2-number-listp)
          (:rewrite 1st-complete-correctness-1)
          (:rewrite abs-addrs-when-m1-file-contents-p)
          (:rewrite
           abs-separate-of-frame->frame-of-collapse-this-lemma-11)
          (:rewrite abs-find-file-correctness-1-lemma-3)
          (:rewrite
           absfat-equiv-implies-set-equiv-addrs-at-1-lemma-1)
          (:rewrite
           abs-fs-fix-of-put-assoc-equal-lemma-2)
          (:rewrite abs-fs-p-of-ctx-app)
          (:type-prescription
           abs-fs-fix-of-put-assoc-equal-lemma-3)
          (:definition binary-append)
          (:definition true-listp)
          (:rewrite
           partial-collapse-correctness-lemma-2)
          (:definition rational-listp)
          (:rewrite list-equiv-when-true-listp)
          (:rewrite ctx-app-when-not-ctx-app-ok)
          (:rewrite ctx-app-ok-when-abs-complete)
          (:rewrite nth-when->=-n-len-l)
          (:rewrite
           no-duplicatesp-of-abs-addrs-of-remove-assoc-lemma-3)
          (:rewrite
           partial-collapse-correctness-lemma-1)
          (:rewrite
           abs-separate-of-frame->frame-of-collapse-this-lemma-15)
          (:rewrite m1-file-alist-p-when-subsetp-equal)
          (:type-prescription
           abs-find-file-correctness-1-lemma-17)
          abs-mkdir-correctness-lemma-50
          (:rewrite collapse-hifat-place-file-lemma-6)
          (:definition nth)
          (:rewrite
           abs-find-file-after-abs-mkdir-lemma-11)
          (:rewrite
           hifat-find-file-correctness-1-lemma-1)
          abs-separate-of-frame->frame-of-collapse-this-lemma-8
          (:rewrite
           abs-find-file-after-abs-mkdir-lemma-13)
          (:rewrite
           abs-file-alist-p-of-abs-file->contents)
          (:rewrite member-of-abs-addrs-when-natp . 2)
          (:definition hifat-file-alist-fix)
          (:type-prescription assoc-when-zp-len)
          (:rewrite abs-addrs-of-ctx-app-2)
          (:definition put-assoc-equal)
          (:rewrite abs-mkdir-correctness-lemma-42)
          (:rewrite
           abs-file-contents-fix-when-abs-file-contents-p)
          (:rewrite
           abs-file-contents-p-when-m1-file-contents-p)
          (:rewrite
           hifat-find-file-correctness-1-lemma-1)
          (:rewrite abs-fs-p-of-ctx-app)
          (:definition binary-append)
          (:rewrite absfat-subsetp-transitivity-lemma-7)
          (:rewrite assoc-after-remove-assoc)
          (:rewrite abs-find-file-correctness-lemma-2)
          (:rewrite abs-mkdir-correctness-lemma-85)
          (:rewrite abs-mkdir-correctness-lemma-75)
          (:rewrite len-when-prefixp)
          (:rewrite m1-directory-file-p-when-m1-file-p)
          (:rewrite consp-of-assoc-of-abs-fs-fix)
          (:rewrite
           abs-find-file-correctness-1-lemma-18)
          (:rewrite
           abs-find-file-correctness-1-lemma-40)
          (:rewrite
           abs-separate-of-frame->frame-of-collapse-this-lemma-7)
          (:rewrite nth-when-prefixp)
          (:rewrite abs-addrs-of-ctx-app-1-lemma-2)
          (:rewrite member-of-abs-top-addrs)
          (:rewrite abs-find-file-correctness-lemma-12)
          (:linear position-when-member)
          (:linear position-equal-ac-when-member)
          (:rewrite prefixp-one-way-or-another . 1)
          (:rewrite member-of-abs-addrs-when-natp . 1)
          (:rewrite hifat-subsetp-transitive-lemma-1)
          abs-separate-of-frame->frame-of-collapse-this-lemma-13
          (:rewrite append-atom-under-list-equiv)
          (:rewrite abs-mkdir-correctness-lemma-99)
          (:rewrite hifat-subsetp-preserves-assoc-equal)
          (:rewrite
           absfat-equiv-implies-set-equiv-names-at-1-lemma-1)
          (:linear abs-mkdir-correctness-lemma-74)
          (:definition hifat-subsetp)
          (:rewrite member-of-abs-fs-fix-when-natp)
          (:type-prescription
           abs-separate-of-frame->frame-of-collapse-this-lemma-7)
          (:rewrite
           m1-file-alist-p-of-cdr-when-m1-file-alist-p)
          (:rewrite
           fat32-filename-p-of-nth-when-fat32-filename-list-p)
          (:rewrite m1-file-alist-p-when-not-consp)
          (:rewrite
           abs-fs-fix-of-put-assoc-equal-lemma-3)
          (:rewrite
           abs-no-dups-p-of-abs-file->contents-of-cdr-of-assoc)
          (:rewrite subsetp-member . 2)
          (:rewrite subsetp-member . 1)
          (:rewrite
           fat32-filename-p-when-member-equal-of-fat32-filename-list-p)
          (:rewrite path-clear-when-prefixp-lemma-1)
          (:rewrite
           absfat-equiv-implies-set-equiv-names-at-1-lemma-2)
          (:rewrite abs-mkdir-correctness-lemma-58)
          (:rewrite subsetp-member . 4)
          (:rewrite ctx-app-ok-when-not-natp)
          (:rewrite ctx-app-when-not-natp)
          (:rewrite
           ctx-app-ok-when-absfat-equiv-lemma-3)
          (:rewrite
           abs-separate-of-frame->frame-of-collapse-this-lemma-14)
          (:rewrite collapse-hifat-place-file-lemma-9)
          (:rewrite collapse-hifat-place-file-lemma-11)
          (:rewrite
           absfat-equiv-implies-set-equiv-names-at-1-lemma-4)
          (:rewrite
           abs-find-file-after-abs-mkdir-lemma-7)
          (:rewrite consp-of-remove-assoc-1)
          (:rewrite abs-find-file-correctness-lemma-6)
          (:rewrite
           abs-find-file-of-put-assoc-lemma-7 . 1)
          (:rewrite
           abs-find-file-helper-of-collapse-lemma-2)
          (:rewrite abs-find-file-correctness-lemma-3)
          (:rewrite
           fat32-filename-p-of-caar-when-m1-file-alist-p)
          (:rewrite subsetp-car-member)
          (:rewrite abs-mkdir-correctness-lemma-59)
          (:rewrite m1-file-alist-p-of-cons)
          (:rewrite abs-mkdir-correctness-lemma-102)
          (:linear
           abs-separate-of-frame->frame-of-collapse-this-lemma-11)
          (:rewrite abs-find-file-correctness-lemma-14)
          (:rewrite subsetp-trans)
          hifat-place-file-correctness-3
          prefixp-when-not-consp-right
          1st-complete-of-put-assoc-2
          cdr-of-append-when-consp
          abs-no-dups-p-when-m1-file-alist-p
          hifat-find-file-correctness-lemma-2
          hifat-find-file-correctness-lemma-4
          fat32-filename-list-fix-when-zp-len
          (:rewrite m1-regular-file-p-correctness-1)
          abs-file-alist-p-when-m1-file-alist-p
          abs-alloc-when-not-natp
          (:rewrite prefixp-transitive . 1)
          abs-addrs-of-ctx-app-1-lemma-6
          absfat-equiv-implies-set-equiv-addrs-at-1-lemma-2
          (:rewrite
           m1-file-alist-p-of-abs-place-file-helper)
          path-clear-when-prefixp-lemma-2
          car-of-append
          names-at-when-prefixp
          list-fix-when-true-listp
          ctx-app-ok-of-abs-place-file-helper-1
          true-listp-when-string-list
          m1-regular-file-p-of-m1-file
          dir-ent-p-when-member-equal-of-dir-ent-list-p
          abs-mkdir-correctness-lemma-64
          (:rewrite hifat-place-file-of-append-1)
          (:type-prescription
           1st-complete-correctness-1)
          (:rewrite
           abs-find-file-helper-of-collapse-2 . 2)
          (:rewrite
           names-at-of-abs-place-file-helper-1)
          (:rewrite abs-place-file-helper-correctness-2)
          (:rewrite
           hifat-file-alist-fix-when-hifat-no-dups-p)
          (:rewrite fat32-filename-list-p-of-append)
          (:rewrite
           abs-find-file-helper-of-collapse-3 . 2)
          (:rewrite
           absfat-place-file-correctness-lemma-6)
          (:rewrite 1st-complete-of-put-assoc-lemma-1)
          (:rewrite list-fix-when-len-zero)
          (:rewrite len-of-nthcdr)
          (:rewrite list-fix-when-not-consp)
          (:rewrite collapse-congruence-lemma-5)
          (:rewrite len-of-append)
          (:rewrite
           fat32-filename-list-p-when-subsetp-equal)
          (:rewrite abs-addrs-of-put-assoc-lemma-1)
          (:rewrite
           member-equal-of-strip-cars-when-m1-file-alist-p)
          (:rewrite hifat-file-alist-fix-guard-lemma-1)
          (:rewrite abs-addrs-of-put-assoc-lemma-2)
          (:rewrite true-listp-when-dir-ent-p)))))

  (defthm
    abs-mkdir-correctness-lemma-134
    (implies
     (and
      (mv-nth
       1
       (collapse
        (frame-with-root
         (frame->root (partial-collapse frame (dirname path)))
         (put-assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          (frame-val
           (frame-val->path
            (cdr (assoc-equal
                  (abs-find-file-src
                   (partial-collapse frame (dirname path))
                   (dirname path))
                  (frame->frame
                   (partial-collapse frame (dirname path))))))
           (mv-nth
            0
            (abs-place-file-helper
             (frame-val->dir
              (cdr
               (assoc-equal
                (abs-find-file-src
                 (partial-collapse frame (dirname path))
                 (dirname path))
                (frame->frame
                 (partial-collapse frame (dirname path))))))
             (append
              (nthcdr
               (len
                (frame-val->path
                 (cdr
                  (assoc-equal
                   (abs-find-file-src
                    (partial-collapse frame (dirname path))
                    (dirname path))
                   frame))))
               (dirname path))
              (list (basename path)))
             '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
               (contents))))
           (frame-val->src
            (cdr
             (assoc-equal
              (abs-find-file-src
               (partial-collapse frame (dirname path))
               (dirname path))
              (frame->frame
               (partial-collapse frame (dirname path)))))))
          (frame->frame (partial-collapse frame (dirname path)))))))
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (not
       (equal
        0
        (abs-find-file-src (partial-collapse frame (dirname path))
                           (dirname path)))))
     (mv-nth
      1
      (collapse
       (frame-with-root
        (frame->root (partial-collapse frame (dirname path)))
        (put-assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         (frame-val
          (frame-val->path
           (cdr (assoc-equal
                 (abs-find-file-src
                  (partial-collapse frame (dirname path))
                  (dirname path))
                 frame)))
          (mv-nth
           0
           (abs-place-file-helper
            (frame-val->dir
             (cdr (assoc-equal
                   (abs-find-file-src
                    (partial-collapse frame (dirname path))
                    (dirname path))
                   (partial-collapse frame (dirname path)))))
            (append
             (nthcdr
              (len
               (frame-val->path
                (cdr
                 (assoc-equal
                  (abs-find-file-src
                   (partial-collapse frame (dirname path))
                   (dirname path))
                  frame))))
              (dirname path))
             (list (basename path)))
            '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                       0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
              (contents))))
          (frame-val->src
           (cdr (assoc-equal
                 (abs-find-file-src
                  (partial-collapse frame (dirname path))
                  (dirname path))
                 frame))))
         (frame->frame
          (partial-collapse frame (dirname path))))))))
    :hints
    (("goal" :in-theory (e/d (frame->root assoc-equal-of-frame->frame)
                             ((:rewrite partial-collapse-correctness-lemma-76)))
      :use (:instance (:rewrite partial-collapse-correctness-lemma-76)
                      (path (dirname path))
                      (frame frame)))))

  (defthm
    abs-mkdir-correctness-lemma-162
    (implies
     (and
      (mv-nth
       1
       (collapse
        (frame-with-root
         (frame->root (partial-collapse frame (dirname path)))
         (put-assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          (frame-val
           (frame-val->path
            (cdr (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  (frame->frame frame))))
           (mv-nth
            0
            (abs-place-file-helper
             (frame-val->dir
              (cdr
               (assoc-equal
                (abs-find-file-src (partial-collapse frame (dirname path))
                                   (dirname path))
                (frame->frame (partial-collapse frame (dirname path))))))
             (append
              (nthcdr
               (len
                (frame-val->path
                 (cdr
                  (assoc-equal
                   (abs-find-file-src (partial-collapse frame (dirname path))
                                      (dirname path))
                   frame))))
               (dirname path))
              (list (basename path)))
             '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
               (contents))))
           (frame-val->src
            (cdr (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  (frame->frame frame)))))
          (frame->frame (partial-collapse frame (dirname path)))))))
      (not (equal 0
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path)))))
     (mv-nth
      1
      (collapse
       (frame-with-root
        (frame->root (partial-collapse frame (dirname path)))
        (put-assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         (frame-val
          (frame-val->path
           (cdr
            (assoc-equal
             (abs-find-file-src (partial-collapse frame (dirname path))
                                (dirname path))
             frame)))
          (mv-nth
           0
           (abs-place-file-helper
            (frame-val->dir
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               (partial-collapse frame (dirname path)))))
            (append
             (nthcdr
              (len
               (frame-val->path
                (cdr
                 (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  frame))))
              (dirname path))
             (list (basename path)))
            '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                       0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
              (contents))))
          (frame-val->src
           (cdr
            (assoc-equal
             (abs-find-file-src (partial-collapse frame (dirname path))
                                (dirname path))
             frame))))
         (remove-assoc-equal
          (find-new-index
           (strip-cars (partial-collapse frame (dirname path))))
          (frame->frame (partial-collapse frame (dirname path)))))))))
    :hints (("goal" :do-not-induct t
             :in-theory (enable assoc-equal-of-frame->frame))))

  (defthm
    abs-mkdir-correctness-lemma-166
    (equal
     (remove-assoc-equal
      (find-new-index (strip-cars (partial-collapse frame (dirname path))))
      (frame->frame (partial-collapse frame (dirname path))))
     (frame->frame (partial-collapse frame (dirname path))))
    :hints (("goal" :in-theory (enable assoc-equal-of-frame->frame)
             :do-not-induct t)))

  (defthm
    abs-mkdir-correctness-lemma-167
    (implies
     (and (no-duplicatesp-equal (strip-cars frame))
          (frame-p frame)
          (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
          (mv-nth 1 (collapse frame))
          (abs-separate frame)
          (subsetp-equal (abs-addrs (frame->root frame))
                         (frame-addrs-root (frame->frame frame))))
     (mv-nth
      1
      (collapse
       (frame-with-root
        (frame-val->dir
         (cdr (assoc-equal 0
                           (partial-collapse frame (dirname path)))))
        (frame->frame (partial-collapse frame (dirname path)))))))
    :instructions
    (:promote
     (:= (frame-val->dir
          (cdr (assoc-equal 0
                            (partial-collapse frame (dirname path)))))
         (frame->root (partial-collapse frame (dirname path)))
         :hints (("goal" :in-theory (enable frame->root))))
     :bash))

  (defthm
    abs-mkdir-correctness-lemma-169
    (implies
     (and (hifat-equiv (mv-nth 0 (collapse frame))
                       fs)
          (m1-directory-file-p (mv-nth 0 (hifat-find-file fs (dirname path)))))
     (m1-directory-file-p (mv-nth '0
                                  (hifat-find-file (mv-nth '0 (collapse frame))
                                                   (dirname path)))))
    :hints (("goal" :do-not-induct t)))

  (defthm
    abs-mkdir-correctness-lemma-170
    (abs-no-dups-p
     (remove1-assoc-equal
      (basename path)
      (mv-nth
       0
       (abs-alloc
        (frame-val->dir$inline
         (cdr (assoc-equal 0
                           (partial-collapse frame (dirname path)))))
        (dirname path)
        (find-new-index
         (strip-cars (partial-collapse frame (dirname path)))))))))

  (defthm
    abs-mkdir-correctness-lemma-171
    (implies
     (and (no-duplicatesp-equal (strip-cars frame))
          (frame-p frame)
          (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
          (mv-nth 1 (collapse frame))
          (abs-separate frame)
          (subsetp-equal (abs-addrs (frame->root frame))
                         (frame-addrs-root (frame->frame frame))))
     (absfat-equiv
      (mv-nth
       0
       (collapse
        (frame-with-root
         (frame-val->dir
          (cdr (assoc-equal 0
                            (partial-collapse frame (dirname path)))))
         (frame->frame (partial-collapse frame (dirname path))))))
      (mv-nth 0 (collapse frame))))
    :instructions
    (:promote
     (:= (frame-val->dir
          (cdr (assoc-equal 0
                            (partial-collapse frame (dirname path)))))
         (frame->root (partial-collapse frame (dirname path)))
         :hints (("goal" :in-theory (enable frame->root))))
     :bash))

  (defthm
    abs-mkdir-correctness-lemma-19
    (implies
     (and
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (mv-nth 1 (collapse frame))
      (hifat-equiv (mv-nth 0 (collapse frame))
                   fs)
      (abs-separate frame)
      (subsetp-equal (abs-addrs (frame->root frame))
                     (frame-addrs-root (frame->frame frame)))
      (m1-file-alist-p fs)
      (equal (mv-nth 1 (hifat-find-file fs (dirname path)))
             0)
      (m1-directory-file-p (mv-nth 0 (hifat-find-file fs (dirname path))))
      (not
       (consp
        (assoc-equal
         (basename path)
         (m1-file->contents (mv-nth 0
                                    (hifat-find-file fs (dirname path)))))))
      (consp path))
     (hifat-equiv
      (mv-nth
       0
       (hifat-place-file
        (mv-nth
         0
         (collapse
          (frame-with-root
           (frame-val->dir
            (cdr (assoc-equal 0
                              (partial-collapse frame (dirname path)))))
           (frame->frame (partial-collapse frame (dirname path))))))
        path
        '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
          (contents))))
      (mv-nth
       0
       (hifat-place-file
        (mv-nth 0 (collapse frame))
        (dirname path)
        (m1-file
         (m1-file->dir-ent (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path))))
         (put-assoc-equal
          (basename path)
          '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
            (contents))
          (m1-file->contents
           (mv-nth 0
                   (hifat-find-file (mv-nth 0 (collapse frame))
                                    (dirname path))))))))))
    :instructions
    (:promote
     (:= (frame-val->dir
          (cdr (assoc-equal 0
                            (partial-collapse frame (dirname path)))))
         (frame->root (partial-collapse frame (dirname path)))
         :hints (("goal" :in-theory (enable frame->root))))
     :bash
     (:claim
      (hifat-equiv (mv-nth 0
                           (collapse (partial-collapse frame (dirname path))))
                   (mv-nth 0 (collapse frame))))
     (:dive 1)
     (:rewrite hifat-place-file-correctness-4
               ((m1-file-alist1 (mv-nth 0 (collapse frame)))))
     (:change-goal nil t)
     :bash :top (:dive 1)
     (:rewrite
      hifat-place-file-when-hifat-equiv-1
      ((file2
        (m1-file
         (m1-file->dir-ent (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path))))
         (put-assoc-equal
          (basename path)
          '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
            (contents))
          (m1-file->contents
           (mv-nth 0
                   (hifat-find-file (mv-nth 0 (collapse frame))
                                    (dirname path)))))))))
     :top :bash :bash (:change-goal nil t)
     :bash :bash (:dive 1)
     (:rewrite
      hifat-equiv-of-put-assoc-2
      ((fs2
        (m1-file->contents (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path)))))))
     :top :bash
     :bash :bash
     :bash :bash
     :bash :bash
     :bash :bash))

  (defthm
    abs-mkdir-correctness-lemma-51
    (implies
     (and (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
          (abs-separate frame)
          (frame-p frame)
          (no-duplicatesp-equal (strip-cars frame))
          (subsetp-equal (abs-addrs (frame->root frame))
                         (frame-addrs-root (frame->frame frame)))
          (mv-nth 1 (collapse frame))
          (hifat-no-dups-p (m1-file->contents file)))
     (hifat-equiv
      (mv-nth
       0
       (hifat-place-file (mv-nth 0
                                 (collapse (partial-collapse frame path1)))
                         path2 file))
      (mv-nth 0
              (hifat-place-file (mv-nth 0 (collapse frame))
                                path2 file))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (disable partial-collapse-correctness-1)
      :use
      ((:instance
        hifat-place-file-correctness-4 (path path2)
        (m1-file-alist1 (mv-nth 0
                                (collapse (partial-collapse frame path1))))
        (m1-file-alist2 (mv-nth 0 (collapse frame))))
       (:instance partial-collapse-correctness-1 (path path1))))))

  (defthm
    abs-mkdir-correctness-lemma-174
    (implies
     (and
      (mv-nth
       1
       (collapse
        (frame-with-root
         (frame->root (partial-collapse frame (dirname path)))
         (put-assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          (frame-val
           (frame-val->path
            (cdr (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  (frame->frame frame))))
           (mv-nth
            0
            (abs-place-file-helper
             (frame-val->dir
              (cdr
               (assoc-equal
                (abs-find-file-src (partial-collapse frame (dirname path))
                                   (dirname path))
                (frame->frame (partial-collapse frame (dirname path))))))
             (nthcdr
              (len
               (frame-val->path
                (cdr
                 (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  frame))))
              path)
             '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
               (contents))))
           (frame-val->src
            (cdr (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  (frame->frame frame)))))
          (frame->frame (partial-collapse frame (dirname path)))))))
      (not (equal 0
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path)))))
     (mv-nth
      1
      (collapse
       (frame-with-root
        (frame->root (partial-collapse frame (dirname path)))
        (put-assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         (frame-val
          (frame-val->path
           (cdr (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame)))
          (mv-nth
           0
           (abs-place-file-helper
            (frame-val->dir
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               (partial-collapse frame (dirname path)))))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
             path)
            '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                       0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
              (contents))))
          (frame-val->src
           (cdr (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
         (frame->frame (partial-collapse frame (dirname path))))))))
    :hints (("goal" :in-theory (enable assoc-equal-of-frame->frame))))

  (defthm
    abs-mkdir-correctness-lemma-175
    (implies (and (not (consp (cdr path))))
             (not (consp (dirname path))))
    :hints (("goal" :in-theory (enable dirname-alt len hifat-find-file)))
    :rule-classes :type-prescription)

  (defthm
    abs-mkdir-correctness-lemma-182
    (implies
     (not (equal (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 0))
     (equal
      (mv-nth
       0
       (collapse
        (frame-with-root
         (frame->root (partial-collapse frame (dirname path)))
         (put-assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          (frame-val
           (frame-val->path
            (cdr (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  (frame->frame frame))))
           (mv-nth
            0
            (abs-place-file-helper
             (frame-val->dir
              (cdr
               (assoc-equal
                (abs-find-file-src (partial-collapse frame (dirname path))
                                   (dirname path))
                (frame->frame (partial-collapse frame (dirname path))))))
             (append
              (nthcdr
               (len
                (frame-val->path
                 (cdr
                  (assoc-equal
                   (abs-find-file-src (partial-collapse frame (dirname path))
                                      (dirname path))
                   frame))))
               (dirname path))
              (list (basename path)))
             '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
               (contents))))
           (frame-val->src
            (cdr (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  (frame->frame frame)))))
          (frame->frame (partial-collapse frame (dirname path)))))))
      (mv-nth
       0
       (collapse
        (frame-with-root
         (frame->root (partial-collapse frame (dirname path)))
         (put-assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          (frame-val
           (frame-val->path
            (cdr (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  frame)))
           (mv-nth
            0
            (abs-place-file-helper
             (frame-val->dir
              (cdr
               (assoc-equal
                (abs-find-file-src (partial-collapse frame (dirname path))
                                   (dirname path))
                (partial-collapse frame (dirname path)))))
             (append
              (nthcdr
               (len
                (frame-val->path
                 (cdr
                  (assoc-equal
                   (abs-find-file-src (partial-collapse frame (dirname path))
                                      (dirname path))
                   frame))))
               (dirname path))
              (list (basename path)))
             '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
               (contents))))
           (frame-val->src
            (cdr (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  frame))))
          (frame->frame (partial-collapse frame (dirname path)))))))))
    :hints (("goal" :in-theory (enable assoc-equal-of-frame->frame))))

  (defthm
    abs-mkdir-correctness-lemma-183
    (implies
     (and (hifat-no-dups-p (m1-file->contents file))
          (no-duplicatesp-equal (strip-cars frame))
          (frame-p frame)
          (equal (frame-val->src (cdr (assoc-equal 0 frame)))
                 0)
          (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
          (mv-nth 1 (collapse frame))
          (abs-separate frame)
          (subsetp-equal (abs-addrs (frame->root frame))
                         (frame-addrs-root (frame->frame frame))))
     (absfat-equiv
      (mv-nth 0
              (hifat-place-file
               (mv-nth 0
                       (collapse (partial-collapse frame (dirname path))))
               path2 file))
      (mv-nth 0
              (hifat-place-file (mv-nth 0 (collapse frame))
                                path2 file))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (disable (:rewrite hifat-place-file-correctness-4))
      :use
      (:instance
       (:rewrite hifat-place-file-correctness-4)
       (file file)
       (path path2)
       (m1-file-alist2
        (mv-nth 0
                (collapse (partial-collapse frame (dirname path)))))
       (m1-file-alist1 (mv-nth 0 (collapse frame)))))))

  (defthm
    abs-mkdir-correctness-lemma-186
    (implies
     (and
      (hifat-equiv (mv-nth 0 (collapse frame))
                   fs)
      (equal
       (mv-nth
        1
        (abs-find-file-helper
         (frame-val->dir
          (cdr (assoc-equal 0
                            (partial-collapse frame (dirname path)))))
         path))
       0)
      (equal
       (abs-find-file-helper
        (frame-val->dir
         (cdr (assoc-equal 0
                           (partial-collapse frame (dirname path)))))
        (dirname path))
       (hifat-find-file
        (mv-nth 0
                (collapse (partial-collapse frame (dirname path))))
        (dirname path)))
      (fat32-filename-list-equiv (append (dirname path)
                                         (list (basename path)))
                                 path)
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (m1-file-alist-p fs)
      (mv-nth 1 (collapse frame))
      (abs-separate frame)
      (subsetp-equal (abs-addrs (frame->root frame))
                     (frame-addrs-root (frame->frame frame)))
      (m1-directory-file-p (mv-nth 0 (hifat-find-file fs (dirname path))))
      (consp (dirname path)))
     (consp
      (assoc-equal
       (basename path)
       (m1-file->contents (mv-nth 0
                                  (hifat-find-file fs (dirname path)))))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (disable (:rewrite abs-find-file-helper-of-append-1))
      :use
      (:instance
       (:rewrite abs-find-file-helper-of-append-1)
       (y (list (basename path)))
       (x (dirname path))
       (fs
        (frame-val->dir
         (cdr (assoc-equal 0
                           (partial-collapse frame (dirname path))))))))))

  ;; (defthm
  ;;   abs-mkdir-correctness-lemma-187
  ;;   (implies
  ;;    (and
  ;;     (equal
  ;;      (mv-nth
  ;;       0
  ;;       (collapse
  ;;        (frame-with-root
  ;;         (frame->root (partial-collapse frame (dirname path)))
  ;;         (put-assoc-equal
  ;;          0 '((path) (dir) (src . 0))
  ;;          (frame->frame (partial-collapse frame (dirname path)))))))
  ;;      (mv-nth
  ;;       0
  ;;       (hifat-place-file
  ;;        (mv-nth 0
  ;;                (collapse (partial-collapse frame (dirname path))))
  ;;        (dirname path)
  ;;        (m1-file
  ;;         (m1-file->dir-ent
  ;;          (mv-nth
  ;;           0
  ;;           (hifat-find-file
  ;;            (mv-nth 0
  ;;                    (collapse (partial-collapse frame (dirname path))))
  ;;            (dirname path))))
  ;;         (put-assoc-equal
  ;;          (basename path)
  ;;          '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
  ;;                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
  ;;            (contents))
  ;;          (m1-file->contents
  ;;           (mv-nth
  ;;            0
  ;;            (hifat-find-file
  ;;             (mv-nth 0
  ;;                     (collapse (partial-collapse frame (dirname path))))
  ;;             (dirname path)))))))))
  ;;     (mv-nth
  ;;      1
  ;;      (collapse
  ;;       (frame-with-root
  ;;        (frame->root (partial-collapse frame (dirname path)))
  ;;        (put-assoc-equal
  ;;         0 '((path) (dir) (src . 0))
  ;;         (frame->frame (partial-collapse frame (dirname path)))))))
  ;;     (no-duplicatesp-equal (strip-cars frame))
  ;;     (frame-p frame)
  ;;     (equal (frame-val->src (cdr (assoc-equal 0 frame)))
  ;;            0)
  ;;     (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
  ;;     (hifat-equiv (mv-nth 0 (collapse frame))
  ;;                  fs)
  ;;     (m1-file-alist-p fs)
  ;;     (mv-nth 1 (collapse frame))
  ;;     (abs-separate frame)
  ;;     (subsetp-equal (abs-addrs (frame->root frame))
  ;;                    (frame-addrs-root (frame->frame frame)))
  ;;     (equal (mv-nth 1 (hifat-find-file fs (dirname path)))
  ;;            0)
  ;;     (m1-directory-file-p (mv-nth 0 (hifat-find-file fs (dirname path))))
  ;;     (not
  ;;      (consp
  ;;       (assoc-equal
  ;;        (basename path)
  ;;        (m1-file->contents (mv-nth 0
  ;;                                   (hifat-find-file fs (dirname path)))))))
  ;;     (consp path))
  ;;    (absfat-equiv
  ;;     (mv-nth
  ;;      0
  ;;      (hifat-place-file
  ;;       (mv-nth
  ;;        0
  ;;        (collapse
  ;;         (frame-with-root
  ;;          (frame-val->dir
  ;;           (cdr (assoc-equal 0
  ;;                             (partial-collapse frame (dirname path)))))
  ;;          (frame->frame (partial-collapse frame (dirname path))))))
  ;;       path
  ;;       '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
  ;;                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
  ;;         (contents))))
  ;;     (mv-nth
  ;;      0
  ;;      (hifat-place-file
  ;;       (mv-nth 0 (collapse frame))
  ;;       (dirname path)
  ;;       (m1-file
  ;;        (m1-file->dir-ent (mv-nth 0
  ;;                                  (hifat-find-file (mv-nth 0 (collapse frame))
  ;;                                                   (dirname path))))
  ;;        (put-assoc-equal
  ;;         (basename path)
  ;;         '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
  ;;                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
  ;;           (contents))
  ;;         (m1-file->contents
  ;;          (mv-nth 0
  ;;                  (hifat-find-file (mv-nth 0 (collapse frame))
  ;;                                   (dirname path))))))))))
  ;;   :instructions
  ;;   ((:in-theory (e/d (m1-file-contents-p-correctness-1)
  ;;                     nil))
  ;;    :promote
  ;;    (:= (frame-val->dir
  ;;         (cdr (assoc-equal 0
  ;;                           (partial-collapse frame (dirname path)))))
  ;;        (frame->root (partial-collapse frame (dirname path)))
  ;;        :hints (("goal" :in-theory (enable frame->root))))
  ;;    :bash (:dive 1)
  ;;    :=
  ;;    (:claim
  ;;     (and
  ;;      (hifat-equiv (mv-nth 0
  ;;                           (collapse (partial-collapse frame (dirname path))))
  ;;                   (mv-nth 0 (collapse frame)))
  ;;      (hifat-no-dups-p
  ;;       (m1-file->contents$inline
  ;;        (m1-file
  ;;         (m1-file->dir-ent$inline
  ;;          (mv-nth
  ;;           0
  ;;           (hifat-find-file
  ;;            (mv-nth 0
  ;;                    (collapse (partial-collapse frame (dirname path))))
  ;;            (dirname path))))
  ;;         (put-assoc-equal
  ;;          (basename path)
  ;;          '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
  ;;                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
  ;;            (contents))
  ;;          (m1-file->contents$inline
  ;;           (mv-nth
  ;;            0
  ;;            (hifat-find-file
  ;;             (mv-nth 0
  ;;                     (collapse (partial-collapse frame (dirname path))))
  ;;             (dirname path)))))))))
  ;;     :hints :none)
  ;;    (:rewrite hifat-place-file-correctness-4
  ;;              ((m1-file-alist1 (mv-nth 0 (collapse frame)))))
  ;;    (:claim
  ;;     (and
  ;;      (hifat-equiv
  ;;       (m1-file->contents$inline
  ;;        (m1-file
  ;;         (m1-file->dir-ent$inline
  ;;          (mv-nth
  ;;           0
  ;;           (hifat-find-file
  ;;            (mv-nth 0
  ;;                    (collapse (partial-collapse frame (dirname path))))
  ;;            (dirname path))))
  ;;         (put-assoc-equal
  ;;          (basename path)
  ;;          '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
  ;;                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
  ;;            (contents))
  ;;          (m1-file->contents$inline
  ;;           (mv-nth
  ;;            0
  ;;            (hifat-find-file
  ;;             (mv-nth 0
  ;;                     (collapse (partial-collapse frame (dirname path))))
  ;;             (dirname path)))))))
  ;;       (m1-file->contents$inline
  ;;        (m1-file (m1-file->dir-ent$inline
  ;;                  (mv-nth 0
  ;;                          (hifat-find-file (mv-nth 0 (collapse frame))
  ;;                                           (dirname path))))
  ;;                 (put-assoc-equal
  ;;                  (basename path)
  ;;                  '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
  ;;                             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
  ;;                    (contents))
  ;;                  (m1-file->contents$inline
  ;;                   (mv-nth 0
  ;;                           (hifat-find-file (mv-nth 0 (collapse frame))
  ;;                                            (dirname path))))))))
  ;;      (m1-directory-file-p
  ;;       (m1-file-fix$inline
  ;;        (m1-file
  ;;         (m1-file->dir-ent$inline
  ;;          (mv-nth
  ;;           0
  ;;           (hifat-find-file
  ;;            (mv-nth 0
  ;;                    (collapse (partial-collapse frame (dirname path))))
  ;;            (dirname path))))
  ;;         (put-assoc-equal
  ;;          (basename path)
  ;;          '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
  ;;                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
  ;;            (contents))
  ;;          (m1-file->contents$inline
  ;;           (mv-nth
  ;;            0
  ;;            (hifat-find-file
  ;;             (mv-nth 0
  ;;                     (collapse (partial-collapse frame (dirname path))))
  ;;             (dirname path))))))))
  ;;      (m1-directory-file-p
  ;;       (m1-file-fix$inline
  ;;        (m1-file (m1-file->dir-ent$inline
  ;;                  (mv-nth 0
  ;;                          (hifat-find-file (mv-nth 0 (collapse frame))
  ;;                                           (dirname path))))
  ;;                 (put-assoc-equal
  ;;                  (basename path)
  ;;                  '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
  ;;                             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
  ;;                    (contents))
  ;;                  (m1-file->contents$inline
  ;;                   (mv-nth 0
  ;;                           (hifat-find-file (mv-nth 0 (collapse frame))
  ;;                                            (dirname path)))))))))
  ;;     :hints :none)
  ;;    (:rewrite
  ;;     hifat-place-file-when-hifat-equiv-1
  ;;     ((file2
  ;;       (m1-file
  ;;        (m1-file->dir-ent (mv-nth 0
  ;;                                  (hifat-find-file (mv-nth 0 (collapse frame))
  ;;                                                   (dirname path))))
  ;;        (put-assoc-equal
  ;;         (basename path)
  ;;         '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
  ;;                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
  ;;           (contents))
  ;;         (m1-file->contents
  ;;          (mv-nth 0
  ;;                  (hifat-find-file (mv-nth 0 (collapse frame))
  ;;                                   (dirname path)))))))))
  ;;    :top :s
  ;;    (:bash ("goal" :in-theory (enable m1-file-contents-p-correctness-1)))
  ;;    (:change-goal nil t)
  ;;    (:bash ("goal" :in-theory (enable m1-file-contents-p-correctness-1)))
  ;;    (:dive 1)
  ;;    (:rewrite
  ;;     hifat-equiv-of-put-assoc-2
  ;;     ((fs2
  ;;       (m1-file->contents (mv-nth 0
  ;;                                  (hifat-find-file (mv-nth 0 (collapse frame))
  ;;                                                   (dirname path)))))))
  ;;    :top :s
  ;;    :bash :bash
  ;;    :bash :bash
  ;;    :bash :bash
  ;;    :bash :bash))

  (defthm
    abs-mkdir-correctness-lemma-188
    (implies
     (and
      (hifat-equiv (mv-nth 0 (collapse frame))
                   fs)
      (not (equal (mv-nth 1 (hifat-find-file fs path))
                  0))
      (equal
       (abs-find-file-helper
        (frame-val->dir
         (cdr (assoc-equal 0
                           (partial-collapse frame (dirname path)))))
        (dirname path))
       (hifat-find-file
        (mv-nth 0
                (collapse (partial-collapse frame (dirname path))))
        (dirname path)))
      (fat32-filename-list-equiv (append (dirname path)
                                         (list (basename path)))
                                 path)
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (m1-file-alist-p fs)
      (mv-nth 1 (collapse frame))
      (abs-separate frame)
      (subsetp-equal (abs-addrs (frame->root frame))
                     (frame-addrs-root (frame->frame frame)))
      (equal (mv-nth 1 (hifat-find-file fs (dirname path)))
             0)
      (m1-directory-file-p (mv-nth 0 (hifat-find-file fs (dirname path)))))
     (>
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir
         (cdr (assoc-equal 0
                           (partial-collapse frame (dirname path)))))
        path))
      0))
    :rule-classes :linear
    :instructions (:promote (:dive 2 2 2)
                            (:= path
                                (append (dirname path)
                                        (list (basename path)))
                                :equiv fat32-filename-list-equiv$inline)
                            :up
                            (:rewrite abs-find-file-helper-of-append-1)
                            :top :bash (:contrapose 2)
                            (:dive 1 2 2)
                            (:= path
                                (append (dirname path)
                                        (list (basename path)))
                                :equiv fat32-filename-list-equiv$inline)
                            :up (:rewrite hifat-find-file-of-append-1)
                            :top :bash))

  (defthm
    abs-mkdir-correctness-lemma-127
    (implies
     (and (no-duplicatesp-equal (strip-cars frame))
          (frame-p frame)
          (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
          (abs-separate frame)
          (subsetp-equal (abs-addrs (frame->root frame))
                         (frame-addrs-root (frame->frame frame))))
     (not
      (member-equal
       (find-new-index (strip-cars (partial-collapse frame (dirname path))))
       (abs-addrs
        (frame-val->dir
         (cdr (assoc-equal 0
                           (partial-collapse frame (dirname path)))))))))
    :hints
    (("goal"
      :in-theory (e/d (frame->root)
                      ((:rewrite subsetp-member . 3)))
      :use
      (:instance
       (:rewrite subsetp-member . 3)
       (y (frame-addrs-root
           (frame->frame (partial-collapse frame (dirname path)))))
       (x
        (abs-addrs
         (frame-val->dir
          (cdr (assoc-equal 0
                            (partial-collapse frame (dirname path)))))))
       (a (find-new-index
           (strip-cars (partial-collapse frame (dirname path)))))))))

  (defthm
    abs-mkdir-correctness-lemma-130
    (implies
     (and (no-duplicatesp-equal (strip-cars frame))
          (frame-p frame)
          (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
          (mv-nth 1 (collapse frame))
          (abs-separate frame)
          (subsetp-equal (abs-addrs (frame->root frame))
                         (frame-addrs-root (frame->frame frame)))
          (not (equal (abs-find-file-src (partial-collapse frame (dirname path))
                                         (dirname path))
                      0)))
     (not
      (member-equal
       (find-new-index (strip-cars (partial-collapse frame (dirname path))))
       (abs-addrs
        (frame-val->dir
         (cdr (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               (partial-collapse frame (dirname path)))))))))
    :instructions
    (:promote
     (:dive 1)
     (:= (assoc-equal (abs-find-file-src (partial-collapse frame (dirname path))
                                         (dirname path))
                      (partial-collapse frame (dirname path)))
         (assoc-equal (abs-find-file-src (partial-collapse frame (dirname path))
                                         (dirname path))
                      (frame->frame (partial-collapse frame (dirname path))))
         :hints :none)
     (:change-goal nil t)
     (:dive 2)
     (:rewrite assoc-equal-of-frame->frame)
     :top :bash
     :top :bash))

  (defthm
    abs-mkdir-correctness-lemma-132
    (implies
     (and (no-duplicatesp-equal (strip-cars frame))
          (frame-p frame)
          (equal (frame-val->src (cdr (assoc-equal 0 frame)))
                 0)
          (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
          (mv-nth 1 (collapse frame))
          (hifat-equiv (mv-nth 0 (collapse frame))
                       fs)
          (abs-separate frame)
          (subsetp-equal (abs-addrs (frame->root frame))
                         (frame-addrs-root (frame->frame frame)))
          (equal (mv-nth 1 (hifat-find-file fs (dirname path)))
                 0))
     (equal
      (mv-nth 1
              (hifat-find-file
               (mv-nth 0
                       (collapse (partial-collapse frame (dirname path))))
               (dirname path)))
      0))
    :hints (("goal" :do-not-induct t
             :in-theory (e/d (abs-mkdir frame-reps-fs) nil))))

  (defthm
    abs-mkdir-correctness-lemma-144
    (implies
     (and
      (equal
       (abs-find-file-helper
        (frame-val->dir
         (cdr (assoc-equal 0
                           (partial-collapse frame (dirname path)))))
        (dirname path))
       (hifat-find-file
        (mv-nth 0
                (collapse (partial-collapse frame (dirname path))))
        (dirname path)))
      (fat32-filename-list-equiv (append (dirname path)
                                         (list (basename path)))
                                 path)
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (mv-nth 1 (collapse frame))
      (hifat-equiv (mv-nth 0 (collapse frame))
                   fs)
      (abs-separate frame)
      (subsetp-equal (abs-addrs (frame->root frame))
                     (frame-addrs-root (frame->frame frame)))
      (equal (mv-nth 1 (hifat-find-file fs (dirname path)))
             0)
      (m1-directory-file-p (mv-nth 0 (hifat-find-file fs (dirname path)))))
     (equal
      (abs-find-file-helper
       (frame-val->dir$inline
        (cdr (assoc-equal '0
                          (partial-collapse frame (dirname path)))))
       path)
      (abs-find-file-helper
       (abs-file->contents
        (mv-nth
         0
         (abs-find-file-helper
          (frame-val->dir
           (cdr (assoc-equal 0
                             (partial-collapse frame (dirname path)))))
          (dirname path))))
       (list (basename path)))))
    :hints
    (("goal"
      :in-theory (disable (:rewrite abs-find-file-helper-of-append-1))
      :use
      (:instance
       (:rewrite abs-find-file-helper-of-append-1)
       (y (list (basename path)))
       (x (dirname path))
       (fs
        (frame-val->dir
         (cdr (assoc-equal 0
                           (partial-collapse frame (dirname path))))))))))

  (defthm
    abs-mkdir-correctness-lemma-149
    (implies
     (and
      (hifat-equiv
       (mv-nth
        0
        (collapse
         (frame-with-root
          (frame-val->dir
           (cdr (assoc-equal 0
                             (partial-collapse frame (dirname path)))))
          (frame->frame (partial-collapse frame (dirname path))))))
       (mv-nth 0 (collapse frame)))
      (hifat-no-dups-p (m1-file->contents file)))
     (and
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (collapse
           (frame-with-root
            (frame-val->dir
             (cdr (assoc-equal 0
                               (partial-collapse frame (dirname path)))))
            (frame->frame (partial-collapse frame (dirname path))))))
         path2 file))
       (mv-nth 1
               (hifat-place-file (mv-nth 0 (collapse frame))
                                 path2 file)))
      (hifat-equiv
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (collapse
           (frame-with-root
            (frame-val->dir
             (cdr (assoc-equal 0
                               (partial-collapse frame (dirname path)))))
            (frame->frame (partial-collapse frame (dirname path))))))
         path2 file))
       (mv-nth 0
               (hifat-place-file (mv-nth 0 (collapse frame))
                                 path2 file)))))
    :hints
    (("goal"
      :in-theory (disable hifat-place-file-correctness-4)
      :use
      (:instance
       hifat-place-file-correctness-4
       (m1-file-alist1 (mv-nth 0 (collapse frame)))
       (m1-file-alist2
        (mv-nth
         0
         (collapse
          (frame-with-root
           (frame-val->dir
            (cdr (assoc-equal 0
                              (partial-collapse frame (dirname path)))))
           (frame->frame (partial-collapse frame (dirname path)))))))
       (path path2)))))

  (defthm
    abs-mkdir-correctness-lemma-160
    (implies
     (and (no-duplicatesp-equal (strip-cars frame))
          (frame-p frame)
          (equal (frame-val->src (cdr (assoc-equal 0 frame)))
                 0)
          (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
          (mv-nth 1 (collapse frame))
          (abs-separate frame)
          (subsetp-equal (abs-addrs (frame->root frame))
                         (frame-addrs-root (frame->frame frame))))
     (hifat-equiv
      (mv-nth
       0
       (collapse
        (frame-with-root
         (frame-val->dir$inline
          (cdr (assoc-equal 0
                            (partial-collapse frame (dirname path)))))
         (frame->frame (partial-collapse frame (dirname path))))))
      (mv-nth 0 (collapse frame))))
    :instructions
    (:promote
     (:= (frame-val->dir$inline
          (cdr (assoc-equal '0
                            (partial-collapse frame (dirname path)))))
         (frame->root (partial-collapse frame (dirname path)))
         :hints (("goal" :in-theory (enable frame->root))))
     :bash))

  (defthm
    abs-mkdir-correctness-lemma-168
    (implies
     (and (no-duplicatesp-equal (strip-cars frame))
          (frame-p frame)
          (equal (frame-val->src (cdr (assoc-equal 0 frame)))
                 0)
          (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
          (mv-nth 1 (collapse frame))
          (hifat-equiv (mv-nth 0 (collapse frame))
                       fs)
          (abs-separate frame)
          (subsetp-equal (abs-addrs (frame->root frame))
                         (frame-addrs-root (frame->frame frame)))
          (m1-directory-file-p (mv-nth 0 (hifat-find-file fs (dirname path)))))
     (hifat-equiv
      (put-assoc-equal
       (basename path)
       '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
         (contents))
       (m1-file->contents
        (mv-nth 0
                (hifat-find-file
                 (mv-nth 0
                         (collapse (partial-collapse frame (dirname path))))
                 (dirname path)))))
      (put-assoc-equal
       (basename path)
       '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
         (contents))
       (m1-file->contents (mv-nth 0
                                  (hifat-find-file (mv-nth 0 (collapse frame))
                                                   (dirname path)))))))
    :hints
    (("goal"
      :in-theory (disable (:rewrite hifat-equiv-of-put-assoc-2))
      :use
      (:instance
       (:rewrite hifat-equiv-of-put-assoc-2)
       (fs1
        (m1-file->contents
         (mv-nth
          0
          (hifat-find-file
           (mv-nth 0
                   (collapse (partial-collapse frame (dirname path))))
           (dirname path)))))
       (val '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                       0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
              (contents)))
       (key (basename path))
       (fs2 (m1-file->contents$inline
             (mv-nth '0
                     (hifat-find-file (mv-nth '0 (collapse frame))
                                      (dirname path)))))))))

  (defthm
    abs-mkdir-correctness-lemma-165
    (implies
     (and (no-duplicatesp-equal (strip-cars frame))
          (frame-p frame)
          (equal (frame-val->src (cdr (assoc-equal 0 frame)))
                 0)
          (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
          (mv-nth 1 (collapse frame))
          (hifat-equiv (mv-nth 0 (collapse frame))
                       fs)
          (abs-separate frame)
          (subsetp-equal (abs-addrs (frame->root frame))
                         (frame-addrs-root (frame->frame frame)))
          (m1-directory-file-p (mv-nth 0 (hifat-find-file fs (dirname path)))))
     (hifat-equiv
      (mv-nth
       0
       (hifat-place-file
        (mv-nth 0 (collapse frame))
        (dirname path)
        (m1-file
         (m1-file->dir-ent
          (mv-nth
           0
           (hifat-find-file
            (mv-nth 0
                    (collapse (partial-collapse frame (dirname path))))
            (dirname path))))
         (put-assoc-equal
          (basename path)
          '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
            (contents))
          (m1-file->contents
           (mv-nth
            0
            (hifat-find-file
             (mv-nth 0
                     (collapse (partial-collapse frame (dirname path))))
             (dirname path))))))))
      (mv-nth
       0
       (hifat-place-file
        (mv-nth 0 (collapse frame))
        (dirname path)
        (m1-file
         (m1-file->dir-ent (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path))))
         (put-assoc-equal
          (basename path)
          '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
            (contents))
          (m1-file->contents
           (mv-nth 0
                   (hifat-find-file (mv-nth 0 (collapse frame))
                                    (dirname path))))))))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (disable (:rewrite hifat-place-file-when-hifat-equiv-1))
      :use
      (:instance
       (:rewrite hifat-place-file-when-hifat-equiv-1)
       (file1
        (m1-file
         (m1-file->dir-ent
          (mv-nth
           0
           (hifat-find-file
            (mv-nth 0
                    (collapse (partial-collapse frame (dirname path))))
            (dirname path))))
         (put-assoc-equal
          (basename path)
          '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
            (contents))
          (m1-file->contents
           (mv-nth
            0
            (hifat-find-file
             (mv-nth 0
                     (collapse (partial-collapse frame (dirname path))))
             (dirname path)))))))
       (path (dirname path))
       (fs (mv-nth 0 (collapse frame)))
       (file2
        (m1-file (m1-file->dir-ent$inline
                  (mv-nth '0
                          (hifat-find-file (mv-nth '0 (collapse frame))
                                           (dirname path))))
                 (put-assoc-equal
                  (basename path)
                  '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                    (contents))
                  (m1-file->contents$inline
                   (mv-nth '0
                           (hifat-find-file (mv-nth '0 (collapse frame))
                                            (dirname path)))))))))))

  (defthm
    abs-mkdir-correctness-lemma-37
    (implies
     (and
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (frame-reps-fs frame fs)
      (consp (assoc-equal 0 frame))
      (abs-complete
       (abs-file->contents
        (mv-nth 0
                (abs-find-file (partial-collapse frame (dirname path))
                               (dirname path)))))
      (equal (mv-nth 1
                     (hifat-find-file (mv-nth 0 (collapse frame))
                                      (dirname path)))
             0))
     (equal (mv-nth 1
                    (abs-find-file (partial-collapse frame (dirname path))
                                   (dirname path)))
            0))
    :hints
    (("goal" :do-not-induct t
      :in-theory (e/d (frame-reps-fs)
                      ((:rewrite abs-find-file-correctness-2)))
      :use (:instance (:rewrite abs-find-file-correctness-2)
                      (path (dirname path))
                      (frame (partial-collapse frame (dirname path)))))))

  (defthm
    abs-mkdir-correctness-lemma-176
    (implies
     (and
      (mv-nth 1 (collapse frame))
      (frame-p frame)
      (abs-separate frame)
      (subsetp-equal (abs-addrs (frame->root frame))
                     (frame-addrs-root (frame->frame frame)))
      (no-duplicatesp-equal (strip-cars frame))
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (m1-directory-file-p (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path)))))
     (m1-directory-file-p
      (mv-nth '0
              (hifat-find-file
               (mv-nth '0
                       (collapse (partial-collapse frame (dirname path))))
               (dirname path)))))
    :instructions
    (:promote (:dive 1 2 1)
              (:rewrite (:rewrite partial-collapse-correctness-1 . 2))
              :top :bash))

  (defthm
    abs-mkdir-correctness-lemma-177
    (implies
     (and
      (mv-nth 1 (collapse frame))
      (frame-p frame)
      (abs-separate frame)
      (subsetp-equal (abs-addrs (frame->root frame))
                     (frame-addrs-root (frame->frame frame)))
      (no-duplicatesp-equal (strip-cars frame))
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (m1-directory-file-p (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path))))
      (consp
       (assoc-equal
        (basename path)
        (m1-file->contents (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path)))))))
     (consp
      (assoc-equal
       (basename path)
       (m1-file->contents
        (mv-nth 0
                (hifat-find-file
                 (mv-nth 0
                         (collapse (partial-collapse frame (dirname path))))
                 (dirname path)))))))
    :instructions
    (:promote
     (:rewrite
      abs-mkdir-correctness-lemma-99
      ((fs2
        (m1-file->contents (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path)))))))
     :bash
     :bash :bash
     :bash :bash
     :bash :bash))

  (defthm
    abs-mkdir-correctness-lemma-38
    (implies
     (and
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (frame-reps-fs frame fs)
      (abs-fs-p fs)
      (m1-file-alist-p fs)
      (consp (assoc-equal 0 frame))
      (abs-complete
       (abs-file->contents
        (mv-nth 0
                (abs-find-file (partial-collapse frame (dirname path))
                               (dirname path)))))
      (prefixp
       (frame-val->path
        (cdr
         (assoc-equal (abs-find-file-src (partial-collapse frame (dirname path))
                                         (dirname path))
                      frame)))
       (dirname path))
      (equal (mv-nth 1
                     (hifat-find-file (mv-nth 0 (collapse frame))
                                      (dirname path)))
             0)
      (m1-directory-file-p (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path))))
      (equal (mv-nth 1
                     (hifat-find-file (mv-nth 0 (collapse frame))
                                      path))
             0))
     (equal (mv-nth 2 (abs-mkdir frame path))
            *eexist*))
    :hints (("goal" :in-theory (e/d (abs-mkdir frame-reps-fs)
                                    ((:rewrite abs-mkdir-correctness-lemma-128)))
             :do-not-induct t)))

  (defthm
    abs-mkdir-correctness-lemma-178
    (implies
     (and
      (consp
       (assoc-equal
        (basename path)
        (m1-file->contents
         (mv-nth
          0
          (hifat-find-file
           (mv-nth 0
                   (collapse (partial-collapse frame (dirname path))))
           (dirname path))))))
      (fat32-filename-list-equiv (append (dirname path)
                                         (list (basename path)))
                                 path)
      (mv-nth 1 (collapse frame))
      (frame-p frame)
      (abs-separate frame)
      (subsetp-equal (abs-addrs (frame->root frame))
                     (frame-addrs-root (frame->frame frame)))
      (no-duplicatesp-equal (strip-cars frame))
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (equal (mv-nth 1
                     (hifat-find-file (mv-nth 0 (collapse frame))
                                      (dirname path)))
             0)
      (m1-directory-file-p (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path)))))
     (equal (mv-nth 1
                    (hifat-find-file (mv-nth 0 (collapse frame))
                                     path))
            0))
    :instructions
    (:promote
     (:= path
         (append (dirname path)
                 (list (basename path)))
         :equiv fat32-filename-list-equiv$inline)
     (:dive 1 2)
     (:rewrite hifat-find-file-of-append-1)
     :top :bash (:contrapose 1)
     (:dive 1)
     (:rewrite
      abs-mkdir-correctness-lemma-99
      ((fs2
        (m1-file->contents (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path)))))))
     :top :bash
     :bash :bash
     :bash :bash
     :bash :bash))

  (defthm
    abs-mkdir-correctness-lemma-39
    (implies
     (and
      (not (equal (mv-nth 2 (abs-mkdir frame path))
                  0))
      (fat32-filename-list-equiv (append (dirname path)
                                         (list (basename path)))
                                 path)
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (frame-reps-fs frame fs)
      (abs-fs-p fs)
      (m1-file-alist-p fs)
      (consp (assoc-equal 0 frame))
      (abs-complete
       (abs-file->contents
        (mv-nth 0
                (abs-find-file (partial-collapse frame (dirname path))
                               (dirname path)))))
      (prefixp
       (frame-val->path
        (cdr
         (assoc-equal (abs-find-file-src (partial-collapse frame (dirname path))
                                         (dirname path))
                      frame)))
       (dirname path))
      (equal (mv-nth 1
                     (hifat-find-file (mv-nth 0 (collapse frame))
                                      (dirname path)))
             0)
      (m1-directory-file-p (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path)))))
     (equal (mv-nth 1
                    (hifat-find-file (mv-nth 0 (collapse frame))
                                     path))
            0))
    :hints (("goal" :do-not-induct t
             :in-theory (e/d (frame-reps-fs abs-mkdir)
                             ((:rewrite abs-mkdir-correctness-lemma-128))))))

  (defthm
    abs-mkdir-correctness-lemma-52
    (implies
     (and
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (frame-reps-fs frame fs)
      (consp (assoc-equal 0 frame))
      (abs-complete
       (abs-file->contents
        (mv-nth 0
                (abs-find-file (partial-collapse frame (dirname path))
                               (dirname path)))))
      (not
       (member-equal
        (find-new-index (strip-cars (partial-collapse frame (dirname path))))
        (abs-addrs
         (frame-val->dir
          (cdr (assoc-equal
                (abs-find-file-src (partial-collapse frame (dirname path))
                                   (dirname path))
                (partial-collapse frame (dirname path))))))))
      (prefixp
       (frame-val->path
        (cdr
         (assoc-equal (abs-find-file-src (partial-collapse frame (dirname path))
                                         (dirname path))
                      frame)))
       (dirname path))
      (equal (mv-nth 1
                     (hifat-find-file (mv-nth 0 (collapse frame))
                                      (dirname path)))
             0)
      (m1-directory-file-p (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path)))))
     (ctx-app-ok
      (mv-nth
       1
       (abs-alloc
        (frame-val->dir
         (cdr (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               (partial-collapse frame (dirname path)))))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
         (dirname path))
        (find-new-index (strip-cars (partial-collapse frame (dirname path))))))
      (find-new-index (strip-cars (partial-collapse frame (dirname path))))
      (nthcdr
       (len
        (frame-val->path
         (cdr (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               frame))))
       (dirname path))))
    :hints (("goal" :do-not-induct t
             :in-theory (e/d (frame-reps-fs abs-mkdir)))))

  (defthm
    abs-mkdir-correctness-lemma-163
    (implies
     (and (fat32-filename-list-equiv (list (basename path))
                                     path)
          (absfat-equiv (mv-nth 0 (collapse frame))
                        fs)
          (not (consp (assoc-equal (basename path)
                                   (mv-nth 0 (collapse frame))))))
     (absfat-equiv
      (put-assoc-equal (basename path)
                       '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                         (contents))
                       (mv-nth 0 (collapse frame)))
      (mv-nth 0
              (abs-place-file-helper
               fs path
               '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                          0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                 (contents))))))
    :instructions (:promote (:dive 2 2 1)
                            (:= fs (mv-nth 0 (collapse frame))
                                :equiv absfat-equiv)
                            :top :bash))

  (local (deflabel abs-mkdir-correctness-label))

  (local
   (in-theory
    (union-theories '(length hifat-mkdir fat32-filename-p-of-basename
                             fat32-filename-p-correctness-1
                             str::coerce-to-list-removal
                             (:e m1-file-p)
                             (:e m1-regular-file-p)
                             (:e hifat-no-dups-p)
                             (:e m1-file->contents))
                    (theory 'minimal-theory))))

  (encapsulate
    ()

    (local (in-theory (current-theory 'abs-mkdir-correctness-label)))

    (defthm
      abs-mkdir-correctness-lemma-32
      (implies
       (and
        (fat32-filename-list-equiv (append (dirname path)
                                           (list (basename path)))
                                   path)
        (frame-reps-fs frame fs)
        (abs-fs-p fs)
        (m1-file-alist-p fs)
        (not (consp (dirname path)))
        (not (equal (mv-nth 1
                            (hifat-find-file (mv-nth 0 (collapse frame))
                                             path))
                    0)))
       (not
        (consp
         (abs-addrs
          (remove-assoc-equal
           (basename path)
           (mv-nth
            '0
            (abs-alloc
             (frame-val->dir$inline
              (cdr (assoc-equal '0
                                (partial-collapse frame (dirname path)))))
             (nthcdr '0 (dirname path))
             (find-new-index
              (strip-cars (partial-collapse frame (dirname path)))))))))))
      :hints (("goal" :do-not-induct t
               :in-theory (e/d (abs-mkdir-correctness-lemma-30
                                frame-reps-fs abs-mkdir frame->root)
                               ((:rewrite abs-mkdir-correctness-lemma-128))))))

    (defthm
      abs-mkdir-correctness-lemma-33
      (implies
       (and
        (equal
         (abs-find-file-helper
          (frame-val->dir
           (cdr (assoc-equal 0
                             (partial-collapse frame (dirname path)))))
          (nthcdr 0 (dirname path)))
         (abs-find-file (partial-collapse frame (dirname path))
                        (dirname path)))
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (frame-reps-fs frame fs)
        (abs-fs-p fs)
        (m1-file-alist-p fs)
        (consp (assoc-equal 0 frame))
        (abs-complete
         (abs-file->contents
          (mv-nth 0
                  (abs-find-file (partial-collapse frame (dirname path))
                                 (dirname path)))))
        (equal (mv-nth 1
                       (hifat-find-file (mv-nth 0 (collapse frame))
                                        (dirname path)))
               0)
        (m1-directory-file-p (mv-nth 0
                                     (hifat-find-file (mv-nth 0 (collapse frame))
                                                      (dirname path)))))
       (not
        (consp
         (abs-addrs
          (remove-assoc-equal
           (basename path)
           (mv-nth
            '0
            (abs-alloc
             (frame-val->dir$inline
              (cdr (assoc-equal '0
                                (partial-collapse frame (dirname path)))))
             (nthcdr '0 (dirname path))
             (find-new-index
              (strip-cars (partial-collapse frame (dirname path)))))))))))
      :hints
      (("goal"
        :do-not-induct t
        :in-theory (e/d (abs-mkdir-correctness-lemma-30 frame-reps-fs abs-mkdir)
                        ((:rewrite abs-mkdir-correctness-lemma-128)
                         collapse-congruence-lemma-4)))))

    (defthm
      abs-mkdir-correctness-lemma-34
      (implies
       (not (consp (dirname path)))
       (equal (abs-find-file-src (partial-collapse frame (dirname path))
                                 (dirname path))
              0))
      :hints (("goal" :do-not-induct t)))

    (defthm
      abs-mkdir-correctness-lemma-35
      (implies
       (and
        (equal
         (abs-find-file-helper
          (frame-val->dir
           (cdr (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 (partial-collapse frame (dirname path)))))
          (nthcdr
           (len
            (frame-val->path
             (cdr (assoc-equal
                   (abs-find-file-src (partial-collapse frame (dirname path))
                                      (dirname path))
                   (partial-collapse frame (dirname path))))))
           (dirname path)))
         (abs-find-file (partial-collapse frame (dirname path))
                        (dirname path)))
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (frame-reps-fs frame fs)
        (abs-fs-p fs)
        (m1-file-alist-p fs)
        (consp (assoc-equal 0 frame))
        (abs-complete
         (abs-file->contents
          (mv-nth 0
                  (abs-find-file (partial-collapse frame (dirname path))
                                 (dirname path)))))
        (equal (mv-nth 1
                       (hifat-find-file (mv-nth 0 (collapse frame))
                                        (dirname path)))
               0)
        (m1-directory-file-p (mv-nth 0
                                     (hifat-find-file (mv-nth 0 (collapse frame))
                                                      (dirname path)))))
       (not
        (consp
         (abs-addrs
          (remove-assoc-equal
           (basename path)
           (mv-nth
            0
            (abs-alloc
             (frame-val->dir
              (cdr (assoc-equal
                    (abs-find-file-src (partial-collapse frame (dirname path))
                                       (dirname path))
                    (partial-collapse frame (dirname path)))))
             (nthcdr
              (len
               (frame-val->path
                (cdr
                 (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  (partial-collapse frame (dirname path))))))
              (dirname path))
             (find-new-index
              (strip-cars (partial-collapse frame (dirname path)))))))))))
      :hints (("goal" :do-not-induct t
               :in-theory (e/d (abs-mkdir-correctness-lemma-30
                                frame-reps-fs abs-mkdir
                                consp-of-set-difference$
                                subsetp-equal)
                               ((:rewrite abs-mkdir-correctness-lemma-128)
                                (:rewrite abs-addrs-of-remove-assoc)
                                (:rewrite abs-fs-p-of-abs-alloc-2)
                                (:rewrite abs-fs-p-of-frame-val->dir)
                                (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-4)
                                (:rewrite collapse-congruence-lemma-4 . 2)
                                (:rewrite fat32-filename-p-of-basename)
                                (:rewrite no-duplicatesp-of-abs-addrs-of-abs-alloc-1)
                                (:rewrite consp-of-set-difference$)
                                (:type-prescription abs-complete))))))

    (defthm
      abs-mkdir-correctness-lemma-80
      (implies
       (and
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (frame-reps-fs frame fs)
        (consp (assoc-equal 0 frame))
        (not
         (m1-directory-file-p (mv-nth 0
                                      (hifat-find-file (mv-nth 0 (collapse frame))
                                                       (dirname path))))))
       (frame-reps-fs (mv-nth 0 (abs-mkdir frame path))
                      (mv-nth 0 (collapse frame))))
      :hints
      (("goal"
        :in-theory
        (e/d (abs-mkdir collapse frame-reps-fs)
             (abs-file-alist-p-correctness-1 abs-fs-p-correctness-1
                                             abs-fs-p-when-hifat-no-dups-p
                                             partial-collapse-when-atom
                                             frame->frame-of-frame-with-root
                                             frame->root-of-frame-with-root))
        :do-not-induct t)))

    (defthm
      abs-mkdir-correctness-lemma-109
      (implies (and (not (consp path)))
               (> (mv-nth 1
                          (hifat-find-file (mv-nth 0 (collapse frame))
                                           path))
                  0))
      :rule-classes :type-prescription)

    (defthm abs-mkdir-correctness-lemma-110
      (implies (not (consp path))
               (equal (mv-nth 1
                              (hifat-place-file (mv-nth 0 (collapse frame))
                                                path file))
                      *enoent*)))

    (defthm abs-mkdir-correctness-lemma-111
      (implies (and (not (consp path))
                    (frame-reps-fs frame fs)
                    (abs-fs-p fs)
                    (m1-file-alist-p fs))
               (equal (mv-nth 0
                              (hifat-place-file (mv-nth 0 (collapse frame))
                                                path file))
                      (mv-nth 0 (collapse frame))))
      :hints (("goal" :in-theory (e/d (abs-mkdir frame-reps-fs)))))

    (defthm abs-mkdir-correctness-lemma-113
      (implies (not (consp path))
               (equal (mv-nth 2 (abs-mkdir frame path))
                      *enoent*))
      :hints (("goal" :in-theory (e/d (abs-mkdir)))))

    (defthm
      abs-mkdir-correctness-lemma-81
      (implies
       (and
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (frame-reps-fs frame fs)
        (consp (assoc-equal 0 frame))
        (not
         (m1-directory-file-p (mv-nth 0
                                      (hifat-find-file (mv-nth 0 (collapse frame))
                                                       (dirname path))))))
       (equal (mv-nth 2 (abs-mkdir frame path))
              *enoent*))
      :hints (("goal" :in-theory (e/d (abs-mkdir frame-reps-fs)))))

    (defthm
      abs-mkdir-correctness-lemma-118
      (implies
       (and
        (fat32-filename-list-equiv (append (dirname path)
                                           (list (basename path)))
                                   path)
        (frame-reps-fs frame fs)
        (consp (assoc-equal 0 frame))
        (abs-complete
         (remove-assoc-equal
          (basename path)
          (mv-nth
           0
           (abs-alloc
            (frame-val->dir
             (cdr (assoc-equal
                   (abs-find-file-src (partial-collapse frame (dirname path))
                                      (dirname path))
                   (partial-collapse frame (dirname path)))))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 (partial-collapse frame (dirname path))))))
             (dirname path))
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))))
        (not (consp (dirname path)))
        (not (equal (mv-nth 1
                            (hifat-find-file (mv-nth 0 (collapse frame))
                                             path))
                    0)))
       (frame-reps-fs
        (mv-nth 0 (abs-mkdir frame path))
        (mv-nth 0
                (hifat-place-file
                 (mv-nth 0 (collapse frame))
                 path
                 (m1-file (dir-ent-install-directory-bit (dir-ent-fix nil)
                                                         t)
                          nil)))))
      :hints
      (("goal"
        :in-theory
        (e/d (frame->root frame-reps-fs abs-mkdir abs-complete
                          abs-separate-of-frame->frame-of-collapse-this-lemma-10)
             ((:rewrite abs-addrs-of-remove-assoc)
              (:rewrite abs-directory-file-p-correctness-1)
              (:rewrite abs-directory-file-p-when-m1-file-p)
              (:rewrite abs-file-alist-p-of-abs-fs-fix)
              (:rewrite abs-find-file-helper-when-m1-file-alist-p)
              (:rewrite abs-fs-p-of-abs-fs-fix)
              (:rewrite abs-mkdir-correctness-lemma-128)
              (:rewrite abs-no-dups-p-of-abs-fs-fix)
              (:rewrite abs-place-file-helper-correctness-1)
              (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-10)
              (:rewrite collapse-congruence-lemma-4 . 1)
              (:rewrite collapse-congruence-lemma-4 . 2)
              (:rewrite hifat-find-file-correctness-1)
              (:rewrite intersectp-equal-of-atom-left)
              (:rewrite set-difference$-when-not-intersectp)))
        :do-not-induct t)))

    (defthm
      abs-mkdir-correctness-lemma-119
      (implies
       (and (fat32-filename-list-equiv (append (dirname path)
                                               (list (basename path)))
                                       path)
            (frame-reps-fs frame fs)
            (abs-fs-p fs)
            (m1-file-alist-p fs)
            (not (consp (dirname path)))
            (equal (mv-nth 1
                           (hifat-find-file (mv-nth 0 (collapse frame))
                                            path))
                   0))
       (equal (mv-nth 2 (abs-mkdir frame path))
              *eexist*))
      :hints (("goal" :in-theory
               (e/d (frame->root abs-mkdir frame-reps-fs)
                    ((:rewrite abs-mkdir-correctness-lemma-128)))
               :do-not-induct t)))

    (defthm
      abs-mkdir-correctness-lemma-120
      (implies
       (and
        (fat32-filename-list-equiv (append (dirname path)
                                           (list (basename path)))
                                   path)
        (not (consp (dirname path)))
        (not (equal (mv-nth 1
                            (hifat-find-file (mv-nth 0 (collapse frame))
                                             path))
                    0)))
       (equal
        (mv-nth 1
                (hifat-place-file
                 (mv-nth 0 (collapse frame))
                 path
                 (m1-file (dir-ent-install-directory-bit (dir-ent-fix nil)
                                                         t)
                          nil)))
        0)))

    (defthm
      abs-mkdir-correctness-lemma-121
      (implies
       (and (fat32-filename-list-equiv (append (dirname path)
                                               (list (basename path)))
                                       path)
            (frame-reps-fs frame fs)
            (not (consp (dirname path)))
            (not (equal (mv-nth 1
                                (hifat-find-file (mv-nth 0 (collapse frame))
                                                 path))
                        0)))
       (equal (mv-nth 2 (abs-mkdir frame path))
              0))
      :hints (("goal" :in-theory (e/d (abs-mkdir frame-reps-fs)
                                      ((:rewrite abs-mkdir-correctness-lemma-128)))
               :do-not-induct t)))

    (defthm
      abs-mkdir-correctness-lemma-136
      (implies
       (frame-p frame)
       (frame-p (partial-collapse frame (dirname path))))
      :hints (("goal" :do-not-induct t)))

    (defthm
      abs-mkdir-correctness-lemma-140
      (abs-fs-p
       (ctx-app
        (mv-nth
         1
         (abs-alloc
          (frame-val->dir
           (cdr
            (assoc-equal (abs-find-file-src
                          (partial-collapse frame (dirname path))
                          (dirname path))
                         (partial-collapse frame (dirname path)))))
          (nthcdr
           (len
            (frame-val->path
             (cdr (assoc-equal
                   (abs-find-file-src
                    (partial-collapse frame (dirname path))
                    (dirname path))
                   frame))))
           (dirname path))
          (find-new-index
           (strip-cars (partial-collapse frame (dirname path))))))
        (mv-nth
         0
         (abs-alloc
          (frame-val->dir
           (cdr
            (assoc-equal (abs-find-file-src
                          (partial-collapse frame (dirname path))
                          (dirname path))
                         (partial-collapse frame (dirname path)))))
          (nthcdr
           (len
            (frame-val->path
             (cdr (assoc-equal
                   (abs-find-file-src
                    (partial-collapse frame (dirname path))
                    (dirname path))
                   frame))))
           (dirname path))
          (find-new-index
           (strip-cars (partial-collapse frame (dirname path))))))
        (find-new-index
         (strip-cars (partial-collapse frame (dirname path))))
        (nthcdr
         (len
          (frame-val->path
           (cdr
            (assoc-equal (abs-find-file-src
                          (partial-collapse frame (dirname path))
                          (dirname path))
                         frame))))
         (dirname path)))))

    (defthm
      abs-mkdir-correctness-lemma-141
      (implies
       (and
        (frame-p frame))
       (frame-p
        (frame->frame
         (frame-with-root
          (frame->root (partial-collapse frame (dirname path)))
          (frame->frame (partial-collapse frame (dirname path))))))))

    (defthm
      abs-mkdir-correctness-lemma-142
      (abs-fs-p
       (mv-nth
        0
        (abs-place-file-helper
         (mv-nth
          0
          (abs-alloc
           (frame-val->dir
            (cdr
             (assoc-equal (abs-find-file-src
                           (partial-collapse frame (dirname path))
                           (dirname path))
                          (partial-collapse frame (dirname path)))))
           (nthcdr
            (len
             (frame-val->path
              (cdr (assoc-equal
                    (abs-find-file-src
                     (partial-collapse frame (dirname path))
                     (dirname path))
                    frame))))
            (dirname path))
           (find-new-index
            (strip-cars (partial-collapse frame (dirname path))))))
         (list (basename path)) file))) :hints (("Goal" :do-not-induct t)))

    (defthm
      abs-mkdir-correctness-lemma-107
      (implies
       (and
        (equal (mv-nth 1
                       (abs-find-file (partial-collapse frame (dirname path))
                                      (dirname path)))
               2)
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (frame-reps-fs frame fs)
        (consp (assoc-equal 0 frame))
        (abs-complete
         (abs-file->contents
          (mv-nth 0
                  (abs-find-file (partial-collapse frame (dirname path))
                                 (dirname path))))))
       (> (mv-nth 1
                  (hifat-find-file (mv-nth 0 (collapse frame))
                                   (dirname path)))
          0))
      :hints (("goal" :do-not-induct t))
      :rule-classes :linear)

    (defthm
      abs-mkdir-correctness-lemma-145
      (implies
       (and
        (consp (assoc-equal 0 frame)))
       (consp
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         (partial-collapse frame (dirname path)))))
      :hints (("goal" :do-not-induct t)))

    (defthm
      abs-mkdir-correctness-lemma-146
      (implies
       (and
        (no-duplicatesp-equal (strip-cars frame)))
       (no-duplicatesp-equal
        (strip-cars
         (frame->frame
          (frame-with-root
           (frame->root (partial-collapse frame (dirname path)))
           (frame->frame (partial-collapse frame (dirname path))))))))
      :hints (("goal" :do-not-induct t)))

    (defthm
      abs-mkdir-correctness-lemma-147
      (implies
       (and
        (no-duplicatesp-equal (strip-cars frame)))
       (no-duplicatesp-equal
        (strip-cars (partial-collapse frame (dirname path)))))
      :hints (("goal" :do-not-induct t)))

    (defthm
      abs-mkdir-correctness-lemma-112
      (implies
       (frame-reps-fs frame fs)
       (dist-names
        (frame->root
         (frame-with-root (frame->root (partial-collapse frame (dirname path)))
                          (frame->frame (partial-collapse frame (dirname path)))))
        nil
        (frame->frame
         (frame-with-root
          (frame->root (partial-collapse frame (dirname path)))
          (frame->frame (partial-collapse frame (dirname path)))))))
      :hints (("goal" :do-not-induct t
               :in-theory (e/d (frame-reps-fs abs-mkdir)))))

    (defthm
      abs-mkdir-correctness-lemma-152
      (implies
       (and
        (fat32-filename-list-equiv (append (dirname path)
                                           (list (basename path)))
                                   path)
        (equal (mv-nth 1
                       (hifat-find-file (mv-nth 0 (collapse frame))
                                        (dirname path)))
               0)
        (m1-directory-file-p (mv-nth 0
                                     (hifat-find-file (mv-nth 0 (collapse frame))
                                                      (dirname path))))
        (not (equal (mv-nth 1
                            (hifat-find-file (mv-nth 0 (collapse frame))
                                             path))
                    0)))
       (equal
        (mv-nth 1
                (hifat-place-file
                 (mv-nth 0 (collapse frame))
                 path
                 (m1-file (dir-ent-install-directory-bit (dir-ent-fix nil)
                                                         t)
                          nil)))
        0))
      :hints (("goal" :do-not-induct t)))

    (defthm
      abs-mkdir-correctness-lemma-153
      (implies
       (and
        (not
         (member-equal
          (find-new-index
           (strip-cars (partial-collapse frame (dirname path))))
          (abs-addrs
           (frame-val->dir
            (cdr
             (assoc-equal
              (abs-find-file-src (partial-collapse frame (dirname path))
                                 (dirname path))
              (partial-collapse frame (dirname path)))))))))
       (not
        (member-equal
         (fat32-filename-fix (car (list (basename path))))
         (names-at
          (mv-nth
           1
           (abs-alloc
            (frame-val->dir
             (cdr
              (assoc-equal (abs-find-file-src
                            (partial-collapse frame (dirname path))
                            (dirname path))
                           (partial-collapse frame (dirname path)))))
            (nthcdr
             (len
              (frame-val->path
               (cdr (assoc-equal
                     (abs-find-file-src
                      (partial-collapse frame (dirname path))
                      (dirname path))
                     frame))))
             (dirname path))
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal (abs-find-file-src
                            (partial-collapse frame (dirname path))
                            (dirname path))
                           frame))))
           (dirname path))))))
      :hints (("goal" :do-not-induct t)))

    (defthm
      abs-mkdir-correctness-lemma-154
      (implies
       (and
        (fat32-filename-list-equiv (append (dirname path)
                                           (list (basename path)))
                                   path)
        (frame-reps-fs frame fs)
        (abs-fs-p fs)
        (m1-file-alist-p fs)
        (not (consp (dirname path)))
        (equal (mv-nth 1
                       (hifat-find-file (mv-nth 0 (collapse frame))
                                        path))
               0))
       (frame-reps-fs (mv-nth 0 (abs-mkdir frame path))
                      (mv-nth 0 (collapse frame))))
      :hints (("goal" :do-not-induct t
               :in-theory (e/d (frame->root abs-mkdir frame-reps-fs)
                               ((:rewrite abs-mkdir-correctness-lemma-128))))))

    (defthm
      abs-mkdir-correctness-lemma-114
      (implies
       (frame-reps-fs frame fs)
       (abs-separate
        (frame->frame
         (frame-with-root
          (frame->root (partial-collapse frame (dirname path)))
          (frame->frame (partial-collapse frame (dirname path)))))))
      :hints (("goal" :do-not-induct t
               :in-theory (enable abs-mkdir frame-reps-fs))))

    (defthm
      abs-mkdir-correctness-lemma-159
      (implies
       (not (equal (abs-find-file-src (partial-collapse frame (dirname path))
                                      (dirname path))
                   0))
       (consp
        (assoc-equal (abs-find-file-src (partial-collapse frame (dirname path))
                                        (dirname path))
                     (frame->frame (partial-collapse frame (dirname path))))))
      :hints (("goal" :do-not-induct t))
      :rule-classes :type-prescription)

    (defthm
      abs-mkdir-correctness-lemma-181
      (implies
       (not
        (member-equal
         (find-new-index (strip-cars (partial-collapse frame (dirname path))))
         (abs-addrs
          (frame-val->dir
           (cdr (assoc-equal 0
                             (partial-collapse frame (dirname path))))))))
       (not
        (member-equal
         (fat32-filename-fix (car (list (basename path))))
         (names-at
          (mv-nth
           1
           (abs-alloc
            (frame-val->dir
             (cdr (assoc-equal 0
                               (partial-collapse frame (dirname path)))))
            (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                    (dirname path))
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))
          (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                  (dirname path))))))
      :hints (("goal" :do-not-induct t)))

    (defthm
      abs-mkdir-correctness-lemma-184
      (implies
       (and
        (fat32-filename-list-equiv (append (dirname path)
                                           (list (basename path)))
                                   path)
        (no-duplicatesp-equal (strip-cars frame))
        (frame-p frame)
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (hifat-equiv (mv-nth 0 (collapse frame))
                     fs)
        (m1-file-alist-p fs)
        (mv-nth 1 (collapse frame))
        (abs-separate frame)
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame)))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal (abs-find-file-src (partial-collapse frame (dirname path))
                                           (dirname path))
                        frame)))
         (dirname path))
        (equal (mv-nth 1 (hifat-find-file fs (dirname path)))
               0)
        (m1-directory-file-p (mv-nth 0 (hifat-find-file fs (dirname path))))
        (not
         (consp
          (assoc-equal
           (basename path)
           (m1-file->contents (mv-nth 0
                                      (hifat-find-file fs (dirname path)))))))
        (consp path))
       (absfat-equiv
        (mv-nth
         0
         (hifat-place-file
          (mv-nth 0 (collapse frame))
          (append
           (frame-val->path
            (cdr (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  (frame->frame frame))))
           (nthcdr
            (len
             (frame-val->path
              (cdr (assoc-equal
                    (abs-find-file-src (partial-collapse frame (dirname path))
                                       (dirname path))
                    frame))))
            (dirname path))
           (list (basename path)))
          '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
            (contents))))
        (mv-nth
         0
         (hifat-place-file
          (mv-nth 0 (collapse frame))
          (dirname path)
          (m1-file
           (m1-file->dir-ent (mv-nth 0
                                     (hifat-find-file (mv-nth 0 (collapse frame))
                                                      (dirname path))))
           (put-assoc-equal
            (basename path)
            '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                       0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
              (contents))
            (m1-file->contents
             (mv-nth 0
                     (hifat-find-file (mv-nth 0 (collapse frame))
                                      (dirname path))))))))))
      :instructions
      (:promote
       (:dive 1 2 2 1)
       (:=
        (frame-val->path
         (cdr
          (assoc-equal (abs-find-file-src (partial-collapse frame (dirname path))
                                          (dirname path))
                       (frame->frame frame))))
        (take
         (len
          (frame-val->path$inline
           (cdr (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
         (dirname path))
        :hints :none)
       (:change-goal nil t)
       (:dive 2)
       (:rewrite take-when-prefixp)
       :top
       (:bash ("goal" :in-theory (enable assoc-equal-of-frame->frame)))
       :up
       (:=
        (append
         (append
          (take
           (len
            (frame-val->path
             (cdr (assoc-equal
                   (abs-find-file-src (partial-collapse frame (dirname path))
                                      (dirname path))
                   frame))))
           (dirname path))
          (nthcdr
           (len
            (frame-val->path
             (cdr (assoc-equal
                   (abs-find-file-src (partial-collapse frame (dirname path))
                                      (dirname path))
                   frame))))
           (dirname path)))
         (list (basename path))))
       (:dive 1)
       (:claim
        (and
         (<=
          (len
           (frame-val->path
            (cdr (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  frame))))
          (len (dirname path)))))
       (:rewrite binary-append-take-nthcdr)
       :top :bash)
      :rule-classes
      (:rewrite
       (:rewrite
        :corollary
        (implies
         (and
          (fat32-filename-list-equiv (append (dirname path)
                                             (list (basename path)))
                                     path)
          (no-duplicatesp-equal (strip-cars frame))
          (frame-p frame)
          (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
          (hifat-equiv (mv-nth 0 (collapse frame))
                       fs)
          (m1-file-alist-p fs)
          (mv-nth 1 (collapse frame))
          (abs-separate frame)
          (subsetp-equal (abs-addrs (frame->root frame))
                         (frame-addrs-root (frame->frame frame)))
          (prefixp
           (frame-val->path
            (cdr
             (assoc-equal (abs-find-file-src (partial-collapse frame (dirname path))
                                             (dirname path))
                          frame)))
           (dirname path))
          (equal (mv-nth 1 (hifat-find-file fs (dirname path)))
                 0)
          (m1-directory-file-p (mv-nth 0 (hifat-find-file fs (dirname path))))
          (not
           (consp
            (assoc-equal
             (basename path)
             (m1-file->contents (mv-nth 0
                                        (hifat-find-file fs (dirname path)))))))
          (consp path))
         (hifat-equiv
          (mv-nth
           0
           (hifat-place-file
            (mv-nth 0 (collapse frame))
            (append
             (frame-val->path
              (cdr (assoc-equal
                    (abs-find-file-src (partial-collapse frame (dirname path))
                                       (dirname path))
                    (frame->frame frame))))
             (nthcdr
              (len
               (frame-val->path
                (cdr (assoc-equal
                      (abs-find-file-src (partial-collapse frame (dirname path))
                                         (dirname path))
                      frame))))
              (dirname path))
             (list (basename path)))
            '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                       0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
              (contents))))
          (mv-nth
           0
           (hifat-place-file
            (mv-nth 0 (collapse frame))
            (dirname path)
            (m1-file
             (m1-file->dir-ent (mv-nth 0
                                       (hifat-find-file (mv-nth 0 (collapse frame))
                                                        (dirname path))))
             (put-assoc-equal
              (basename path)
              '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                         0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                (contents))
              (m1-file->contents
               (mv-nth 0
                       (hifat-find-file (mv-nth 0 (collapse frame))
                                        (dirname path)))))))))))))

    (defthm
      abs-mkdir-correctness-lemma-10
      (implies
       (and (equal (frame-val->src$inline (cdr (assoc-equal 0 frame)))
                   '0)
            (not (consp (frame-val->path$inline (cdr (assoc-equal 0 frame))))))
       (equal
        (len (frame-val->path
              (cdr (assoc-equal 0
                                (partial-collapse frame (dirname path))))))
        0))
      :hints (("goal" :do-not-induct t)))

    (defthm
      abs-mkdir-correctness-lemma-115
      (implies
       (frame-reps-fs frame fs)
       (not
        (member-equal
         (find-new-index (strip-cars (partial-collapse frame (dirname path))))
         (abs-addrs
          (frame-val->dir$inline
           (cdr (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 (partial-collapse frame (dirname path)))))))))
      :hints
      (("goal"
        :do-not-induct t
        :in-theory (enable frame-reps-fs)
        :cases ((equal (abs-find-file-src (partial-collapse frame (dirname path))
                                          (dirname path))
                       0)))))

    (defthm
      abs-mkdir-correctness-lemma-137
      (implies
       (and
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (not
         (equal
          (mv-nth
           1
           (abs-alloc
            (frame-val->dir
             (cdr (assoc-equal 0
                               (partial-collapse frame (dirname path)))))
            (dirname path)
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))
          (frame-val->dir
           (cdr (assoc-equal 0
                             (partial-collapse frame (dirname path))))))))
       (not
        (member-equal
         (fat32-filename-fix (car (list (basename path))))
         (names-at
          (mv-nth
           1
           (abs-alloc
            (frame-val->dir
             (cdr (assoc-equal 0
                               (partial-collapse frame (dirname path)))))
            (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                    (dirname path))
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))
          (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                  (dirname path))))))
      :hints (("goal" :do-not-induct t)))

    (defthm
      abs-mkdir-correctness-lemma-138
      (implies
       (consp (assoc-equal 0 frame))
       (consp (assoc-equal 0
                           (partial-collapse frame (dirname path)))))
      :hints (("goal" :do-not-induct t)))

    (defthm abs-mkdir-correctness-lemma-116
      (implies (and (not (consp path))
                    (frame-reps-fs frame fs))
               (frame-reps-fs (mv-nth 0 (abs-mkdir frame path))
                              (mv-nth 0 (collapse frame))))
      :hints (("goal" :do-not-induct t)))

    (defthm
      abs-mkdir-correctness-lemma-117
      (implies
       (and
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal (abs-find-file-src (partial-collapse frame (dirname path))
                                           (dirname path))
                        (partial-collapse frame (dirname path)))))
         (fat32-filename-list-fix (dirname path)))
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (frame-reps-fs frame fs)
        (consp (assoc-equal 0 frame))
        (abs-complete
         (abs-file->contents
          (mv-nth 0
                  (abs-find-file (partial-collapse frame (dirname path))
                                 (dirname path)))))
        (equal (mv-nth 1
                       (hifat-find-file (mv-nth 0 (collapse frame))
                                        (dirname path)))
               0)
        (m1-directory-file-p (mv-nth 0
                                     (hifat-find-file (mv-nth 0 (collapse frame))
                                                      (dirname path)))))
       (ctx-app-ok
        (mv-nth
         1
         (abs-alloc
          (frame-val->dir
           (cdr (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 (partial-collapse frame (dirname path)))))
          (nthcdr
           (len
            (frame-val->path
             (cdr (assoc-equal
                   (abs-find-file-src (partial-collapse frame (dirname path))
                                      (dirname path))
                   frame))))
           (dirname path))
          (find-new-index (strip-cars (partial-collapse frame (dirname path))))))
        (find-new-index (strip-cars (partial-collapse frame (dirname path))))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
         (dirname path))))
      :hints (("goal" :do-not-induct t)))

    (defthm abs-mkdir-correctness-lemma-180
     (implies
      (and
       (mv-nth 1 (collapse frame))
       (absfat-equiv (mv-nth 0 (collapse frame))
                     fs)
       (frame-p frame)
       (abs-separate frame)
       (subsetp-equal (abs-addrs (frame->root frame))
                      (frame-addrs-root (frame->frame frame)))
       (no-duplicatesp-equal (strip-cars frame))
       (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
       (abs-fs-p fs)
       (equal (mv-nth 1
                      (hifat-find-file (mv-nth 0 (collapse frame))
                                       path))
              0)
       (consp (dirname path))
       (m1-directory-file-p (mv-nth 0
                                    (hifat-find-file (mv-nth 0 (collapse frame))
                                                     (dirname path))))
       (consp path))
      (consp
       (assoc-equal
        (basename path)
        (m1-file->contents
         (mv-nth
          0
          (hifat-find-file
           (mv-nth 0
                   (collapse (partial-collapse frame (dirname path))))
           (dirname path)))))))
     :hints (("goal" :do-not-induct t
              :in-theory (disable (:rewrite hifat-find-file-of-append-1))
              :use ((:instance (:rewrite hifat-find-file-of-append-1)
                               (y (list (basename path)))
                               (x (dirname path))
                               (fs fs))
                    abs-mkdir-correctness-lemma-50))))

    (defthm
      abs-mkdir-correctness-lemma-190
      (implies (and (mv-nth 1 (collapse frame))
                    (absfat-equiv (mv-nth 0 (collapse frame))
                                  fs)
                    (frame-p frame)
                    (abs-separate frame)
                    (subsetp-equal (abs-addrs (frame->root frame))
                                   (frame-addrs-root (frame->frame frame)))
                    (no-duplicatesp-equal (strip-cars frame))
                    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
                    (abs-fs-p fs))
               (hifat-equiv (mv-nth 0 (collapse frame))
                            fs))
      :hints
      (("goal"
        :do-not-induct t
        :in-theory (e/d (frame-reps-fs abs-mkdir)
                        (collapse collapse-this
                                  (:rewrite abs-mkdir-correctness-lemma-128)
                                  (:rewrite hifat-equiv-when-absfat-equiv)))
        :use (:instance (:rewrite hifat-equiv-when-absfat-equiv)
                        (abs-file-alist2 fs)
                        (abs-file-alist1 (mv-nth 0 (collapse frame))))))
      :rule-classes (:rewrite :forward-chaining))

    (defthm
      abs-mkdir-correctness-lemma-192
      (implies
       (and
        (equal (mv-nth 1 (hifat-find-file fs (dirname path)))
               0)
        (mv-nth 1 (collapse frame))
        (absfat-equiv (mv-nth 0 (collapse frame))
                      fs)
        (frame-p frame)
        (abs-separate frame)
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame)))
        (no-duplicatesp-equal (strip-cars frame))
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (abs-fs-p fs)
        (consp
         (assoc-equal
          (basename path)
          (m1-file->contents (mv-nth 0
                                     (hifat-find-file fs (dirname path))))))
        (m1-directory-file-p (mv-nth 0 (hifat-find-file fs (dirname path)))))
       (consp
        (assoc-equal
         (basename path)
         (m1-file->contents (mv-nth 0
                                    (hifat-find-file (mv-nth 0 (collapse frame))
                                                     (dirname path)))))))
      :instructions (:promote (:rewrite abs-mkdir-correctness-lemma-123
                                        ((fs fs)))
                              :bash :bash))

    (defthm
      abs-mkdir-correctness-lemma-124
      (implies
       (and
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal (abs-find-file-src (partial-collapse frame (dirname path))
                                           (dirname path))
                        (partial-collapse frame (dirname path)))))
         (fat32-filename-list-fix (dirname path)))
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (frame-reps-fs frame fs)
        (abs-fs-p fs)
        (m1-file-alist-p fs)
        (consp (assoc-equal 0 frame))
        (abs-complete
         (abs-file->contents
          (mv-nth 0
                  (abs-find-file (partial-collapse frame (dirname path))
                                 (dirname path)))))
        (not (equal (abs-find-file-src (partial-collapse frame (dirname path))
                                       (dirname path))
                    0))
        (equal (mv-nth 1
                       (hifat-find-file (mv-nth 0 (collapse frame))
                                        path))
               0))
       (frame-reps-fs (mv-nth 0 (abs-mkdir frame path))
                      (mv-nth 0 (collapse frame))))
      :hints (("goal" :do-not-induct t
               :in-theory (e/d (frame-reps-fs abs-mkdir)
                               (collapse collapse-this
                                         (:rewrite abs-mkdir-correctness-lemma-128))))))

    (defthm
      abs-mkdir-correctness-lemma-125
      (implies
       (and
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal (abs-find-file-src (partial-collapse frame (dirname path))
                                           (dirname path))
                        (partial-collapse frame (dirname path)))))
         (fat32-filename-list-fix (dirname path)))
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (frame-reps-fs frame fs)
        (abs-fs-p fs)
        (m1-file-alist-p fs)
        (consp (assoc-equal 0 frame))
        (abs-complete
         (abs-file->contents
          (mv-nth 0
                  (abs-find-file (partial-collapse frame (dirname path))
                                 (dirname path)))))
        (equal (mv-nth 1
                       (hifat-find-file (mv-nth 0 (collapse frame))
                                        (dirname path)))
               0)
        (m1-directory-file-p (mv-nth 0
                                     (hifat-find-file (mv-nth 0 (collapse frame))
                                                      (dirname path))))
        (equal (mv-nth 1
                       (hifat-find-file (mv-nth 0 (collapse frame))
                                        path))
               0))
       (equal (mv-nth 2 (abs-mkdir frame path))
              *eexist*))
      :hints (("goal" :do-not-induct t)))

    (defthm
      abs-mkdir-correctness-lemma-131
      (implies
       (and
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal (abs-find-file-src (partial-collapse frame (dirname path))
                                           (dirname path))
                        (partial-collapse frame (dirname path)))))
         (fat32-filename-list-fix (dirname path)))
        (fat32-filename-list-equiv (append (dirname path)
                                           (list (basename path)))
                                   path)
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (frame-reps-fs frame fs)
        (abs-fs-p fs)
        (m1-file-alist-p fs)
        (consp (assoc-equal 0 frame))
        (abs-complete
         (abs-file->contents
          (mv-nth 0
                  (abs-find-file (partial-collapse frame (dirname path))
                                 (dirname path)))))
        (equal (mv-nth 1
                       (hifat-find-file (mv-nth 0 (collapse frame))
                                        (dirname path)))
               0)
        (m1-directory-file-p (mv-nth 0
                                     (hifat-find-file (mv-nth 0 (collapse frame))
                                                      (dirname path))))
        (not (equal (mv-nth 1
                            (hifat-find-file (mv-nth 0 (collapse frame))
                                             path))
                    0)))
       (equal (mv-nth 2 (abs-mkdir frame path))
              0))
      :hints (("goal" :do-not-induct t)))

    (defthm
      abs-mkdir-correctness-lemma-135
      (implies
       (and
        (equal
         (abs-find-file-helper
          (frame-val->dir
           (cdr (assoc-equal 0
                             (partial-collapse frame (dirname path)))))
          (nthcdr 0 (dirname path)))
         (abs-find-file (partial-collapse frame (dirname path))
                        (dirname path)))
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (frame-reps-fs frame fs)
        (abs-fs-p fs)
        (m1-file-alist-p fs)
        (consp (assoc-equal 0 frame))
        (abs-complete
         (abs-file->contents
          (mv-nth 0
                  (abs-find-file (partial-collapse frame (dirname path))
                                 (dirname path)))))
        (equal (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               0)
        (equal (mv-nth 1
                       (hifat-find-file (mv-nth 0 (collapse frame))
                                        (dirname path)))
               0)
        (equal (mv-nth 1
                       (hifat-find-file (mv-nth 0 (collapse frame))
                                        path))
               0))
       (frame-reps-fs (mv-nth 0 (abs-mkdir frame path))
                      (mv-nth 0 (collapse frame))))
      :hints (("goal" :do-not-induct t
               :in-theory (e/d (abs-mkdir frame-reps-fs)
                               ((:rewrite abs-mkdir-correctness-lemma-128))))))

    (defthm
      abs-mkdir-correctness-lemma-191
      (implies
       (and (mv-nth 1 (collapse frame))
            (absfat-equiv (mv-nth 0 (collapse frame))
                          fs)
            (frame-p frame)
            (abs-separate frame)
            (subsetp-equal (abs-addrs (frame->root frame))
                           (frame-addrs-root (frame->frame frame)))
            (no-duplicatesp-equal (strip-cars frame))
            (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
            (abs-fs-p fs)
            (equal (mv-nth 1 (hifat-find-file fs (dirname path)))
                   0))
       (equal
        (mv-nth 1
                (hifat-find-file
                 (mv-nth 0
                         (collapse (partial-collapse frame (dirname path))))
                 (dirname path)))
        0))
      :hints
      (("goal" :do-not-induct t
        :in-theory (e/d (abs-mkdir frame-reps-fs)
                        ((:rewrite abs-mkdir-correctness-lemma-128))))))

    (defthm
      abs-mkdir-correctness-lemma-133
      (implies
       (and
        (equal
         (abs-find-file-helper
          (frame-val->dir
           (cdr (assoc-equal 0
                             (partial-collapse frame (dirname path)))))
          (nthcdr 0 (dirname path)))
         (abs-find-file (partial-collapse frame (dirname path))
                        (dirname path)))
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (frame-reps-fs frame fs)
        (abs-fs-p fs)
        (m1-file-alist-p fs)
        (consp (assoc-equal 0 frame))
        (abs-complete
         (abs-file->contents
          (mv-nth 0
                  (abs-find-file (partial-collapse frame (dirname path))
                                 (dirname path)))))
        (equal (mv-nth 1
                       (hifat-find-file (mv-nth 0 (collapse frame))
                                        (dirname path)))
               0)
        (m1-directory-file-p (mv-nth 0
                                     (hifat-find-file (mv-nth 0 (collapse frame))
                                                      (dirname path)))))
       (ctx-app-ok
        (mv-nth
         1
         (abs-alloc
          (frame-val->dir
           (cdr (assoc-equal 0
                             (partial-collapse frame (dirname path)))))
          (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                  (dirname path))
          (find-new-index (strip-cars (partial-collapse frame (dirname path))))))
        (find-new-index (strip-cars (partial-collapse frame (dirname path))))
        (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                (dirname path))))
      :hints (("goal" :do-not-induct t
               :in-theory (e/d (abs-mkdir frame-reps-fs)
                               ((:rewrite abs-mkdir-correctness-lemma-128))))))

    (defthm
      abs-mkdir-correctness-lemma-172
      (implies
       (and
        (equal
         (abs-find-file-helper
          (frame-val->dir
           (cdr (assoc-equal 0
                             (partial-collapse frame (dirname path)))))
          (nthcdr 0 (dirname path)))
         (abs-find-file (partial-collapse frame (dirname path))
                        (dirname path)))
        (equal
         (ctx-app
          (mv-nth
           1
           (abs-alloc
            (frame-val->dir
             (cdr (assoc-equal 0
                               (partial-collapse frame (dirname path)))))
            (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                    (dirname path))
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))
          (mv-nth
           0
           (abs-place-file-helper
            (mv-nth
             0
             (abs-alloc
              (frame-val->dir
               (cdr (assoc-equal 0
                                 (partial-collapse frame (dirname path)))))
              (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                      (dirname path))
              (find-new-index
               (strip-cars (partial-collapse frame (dirname path))))))
            (list (basename path))
            '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                       0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
              (contents))))
          (find-new-index (strip-cars (partial-collapse frame (dirname path))))
          (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                  (dirname path)))
         (mv-nth
          0
          (abs-place-file-helper
           (ctx-app
            (mv-nth
             1
             (abs-alloc
              (frame-val->dir
               (cdr (assoc-equal 0
                                 (partial-collapse frame (dirname path)))))
              (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                      (dirname path))
              (find-new-index
               (strip-cars (partial-collapse frame (dirname path))))))
            (mv-nth
             0
             (abs-alloc
              (frame-val->dir
               (cdr (assoc-equal 0
                                 (partial-collapse frame (dirname path)))))
              (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                      (dirname path))
              (find-new-index
               (strip-cars (partial-collapse frame (dirname path))))))
            (find-new-index (strip-cars (partial-collapse frame (dirname path))))
            (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                    (dirname path)))
           (append (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                           (dirname path))
                   (list (basename path)))
           '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
             (contents)))))
        (fat32-filename-list-equiv (append (dirname path)
                                           (list (basename path)))
                                   path)
        (no-duplicatesp-equal (strip-cars frame))
        (frame-p frame)
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (frame-reps-fs frame fs)
        (abs-fs-p fs)
        (m1-file-alist-p fs)
        (consp (assoc-equal 0 frame))
        (not
         (consp
          (abs-addrs
           (remove-assoc-equal
            (basename path)
            (mv-nth
             0
             (abs-alloc
              (frame-val->dir
               (cdr (assoc-equal 0
                                 (partial-collapse frame (dirname path)))))
              (nthcdr 0 (dirname path))
              (find-new-index
               (strip-cars (partial-collapse frame (dirname path))))))))))
        (abs-complete
         (abs-file->contents
          (mv-nth 0
                  (abs-find-file (partial-collapse frame (dirname path))
                                 (dirname path)))))
        (equal (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               0)
        (path-clear (dirname path)
                    (frame->frame (partial-collapse frame (dirname path))))
        (equal (mv-nth 1
                       (hifat-find-file (mv-nth 0 (collapse frame))
                                        (dirname path)))
               0)
        (m1-directory-file-p (mv-nth 0
                                     (hifat-find-file (mv-nth 0 (collapse frame))
                                                      (dirname path))))
        (not (equal (mv-nth 1
                            (hifat-find-file (mv-nth 0 (collapse frame))
                                             path))
                    0)))
       (frame-reps-fs
        (mv-nth 0 (abs-mkdir frame path))
        (mv-nth 0
                (hifat-place-file
                 (mv-nth 0 (collapse frame))
                 path
                 (m1-file (dir-ent-install-directory-bit (dir-ent-fix nil)
                                                         t)
                          nil)))))
      :hints (("goal" :do-not-induct t
               :in-theory (e/d (frame-reps-fs
                                abs-mkdir abs-complete
                                abs-separate-of-frame->frame-of-collapse-this-lemma-10)
                               ((:rewrite abs-mkdir-correctness-lemma-128))))))

    (defthm
      abs-mkdir-correctness-lemma-185
      (implies
       (frame-reps-fs frame fs)
       (not
        (member-equal
         (fat32-filename-fix (car (list (basename path))))
         (names-at
          (mv-nth
           1
           (abs-alloc
            (frame-val->dir
             (cdr (assoc-equal 0
                               (partial-collapse frame (dirname path)))))
            (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                    (dirname path))
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))
          (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                  (dirname path))))))
      :hints (("goal" :do-not-induct t
               :in-theory (enable abs-mkdir frame-reps-fs))))

    (defthm
      abs-mkdir-correctness-lemma-193
      (implies
       (and
        (consp
         (assoc-equal
          (basename path)
          (m1-file->contents (mv-nth 0
                                     (hifat-find-file (mv-nth 0 (collapse frame))
                                                      (dirname path))))))
        (fat32-filename-list-equiv (append (dirname path)
                                           (list (basename path)))
                                   path)
        (mv-nth 1 (collapse frame))
        (absfat-equiv (mv-nth 0 (collapse frame))
                      fs)
        (frame-p frame)
        (abs-separate frame)
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame)))
        (no-duplicatesp-equal (strip-cars frame))
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (abs-fs-p fs)
        (equal (mv-nth 1 (hifat-find-file fs (dirname path)))
               0)
        (m1-directory-file-p (mv-nth 0 (hifat-find-file fs (dirname path)))))
       (equal (mv-nth 1 (hifat-find-file fs path))
              0))
      :instructions
      (:promote
       (:dive 1 2 2)
       (:= path
           (append (dirname path)
                   (list (basename path)))
           :equiv fat32-filename-list-equiv$inline)
       :up
       (:rewrite hifat-find-file-of-append-1)
       :top
       :bash
       (:rewrite
        ctx-app-ok-when-absfat-equiv-lemma-1
        ((abs-file-alist2
          (m1-file->contents (mv-nth 0
                                     (hifat-find-file (mv-nth 0 (collapse frame))
                                                      (dirname path)))))))
       :bash :bash
       :bash :bash))

    ;; Hypotheses minimised.
    (defthm
      abs-mkdir-correctness-lemma-143
      (implies
       (and
        (equal
         (mv-nth
          0
          (collapse
           (frame-with-root
            (frame->root (partial-collapse frame (dirname path)))
            (put-assoc-equal
             (abs-find-file-src (partial-collapse frame (dirname path))
                                (dirname path))
             (frame-val
              (frame-val->path
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 (frame->frame (partial-collapse frame (dirname path))))))
              (mv-nth
               0
               (abs-place-file-helper
                (frame-val->dir
                 (cdr
                  (assoc-equal
                   (abs-find-file-src (partial-collapse frame (dirname path))
                                      (dirname path))
                   (frame->frame (partial-collapse frame (dirname path))))))
                (append
                 (nthcdr
                  (len
                   (frame-val->path
                    (cdr
                     (assoc-equal
                      (abs-find-file-src (partial-collapse frame (dirname path))
                                         (dirname path))
                      frame))))
                  (dirname path))
                 (list (basename path)))
                '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                  (contents))))
              (frame-val->src
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 (frame->frame (partial-collapse frame (dirname path)))))))
             (frame->frame (partial-collapse frame (dirname path)))))))
         (mv-nth
          0
          (abs-place-file-helper
           (mv-nth
            0
            (collapse
             (frame-with-root
              (frame->root (partial-collapse frame (dirname path)))
              (frame->frame (partial-collapse frame (dirname path))))))
           (append
            (frame-val->path
             (cdr (assoc-equal
                   (abs-find-file-src (partial-collapse frame (dirname path))
                                      (dirname path))
                   (frame->frame (partial-collapse frame (dirname path))))))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
             (dirname path))
            (list (basename path)))
           '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
             (contents)))))
        (equal
         (mv-nth
          1
          (collapse
           (frame-with-root
            (frame->root (partial-collapse frame (dirname path)))
            (put-assoc-equal
             (abs-find-file-src (partial-collapse frame (dirname path))
                                (dirname path))
             (frame-val
              (frame-val->path
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 (frame->frame (partial-collapse frame (dirname path))))))
              (mv-nth
               0
               (abs-place-file-helper
                (frame-val->dir
                 (cdr
                  (assoc-equal
                   (abs-find-file-src (partial-collapse frame (dirname path))
                                      (dirname path))
                   (frame->frame (partial-collapse frame (dirname path))))))
                (append
                 (nthcdr
                  (len
                   (frame-val->path
                    (cdr
                     (assoc-equal
                      (abs-find-file-src (partial-collapse frame (dirname path))
                                         (dirname path))
                      frame))))
                  (dirname path))
                 (list (basename path)))
                '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                  (contents))))
              (frame-val->src
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 (frame->frame (partial-collapse frame (dirname path)))))))
             (frame->frame (partial-collapse frame (dirname path)))))))
         (mv-nth
          1
          (collapse
           (frame-with-root
            (frame->root (partial-collapse frame (dirname path)))
            (frame->frame (partial-collapse frame (dirname path)))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal (abs-find-file-src (partial-collapse frame (dirname path))
                                           (dirname path))
                        (partial-collapse frame (dirname path)))))
         (fat32-filename-list-fix (dirname path)))
        (equal
         (ctx-app
          (mv-nth
           1
           (abs-alloc
            (frame-val->dir
             (cdr (assoc-equal
                   (abs-find-file-src (partial-collapse frame (dirname path))
                                      (dirname path))
                   (partial-collapse frame (dirname path)))))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
             (dirname path))
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))
          (mv-nth
           0
           (abs-place-file-helper
            (mv-nth
             0
             (abs-alloc
              (frame-val->dir
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 (partial-collapse frame (dirname path)))))
              (nthcdr
               (len
                (frame-val->path
                 (cdr
                  (assoc-equal
                   (abs-find-file-src (partial-collapse frame (dirname path))
                                      (dirname path))
                   frame))))
               (dirname path))
              (find-new-index
               (strip-cars (partial-collapse frame (dirname path))))))
            (list (basename path))
            '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                       0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
              (contents))))
          (find-new-index (strip-cars (partial-collapse frame (dirname path))))
          (nthcdr
           (len
            (frame-val->path
             (cdr (assoc-equal
                   (abs-find-file-src (partial-collapse frame (dirname path))
                                      (dirname path))
                   frame))))
           (dirname path)))
         (mv-nth
          0
          (abs-place-file-helper
           (ctx-app
            (mv-nth
             1
             (abs-alloc
              (frame-val->dir
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 (partial-collapse frame (dirname path)))))
              (nthcdr
               (len
                (frame-val->path
                 (cdr
                  (assoc-equal
                   (abs-find-file-src (partial-collapse frame (dirname path))
                                      (dirname path))
                   frame))))
               (dirname path))
              (find-new-index
               (strip-cars (partial-collapse frame (dirname path))))))
            (mv-nth
             0
             (abs-alloc
              (frame-val->dir
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 (partial-collapse frame (dirname path)))))
              (nthcdr
               (len
                (frame-val->path
                 (cdr
                  (assoc-equal
                   (abs-find-file-src (partial-collapse frame (dirname path))
                                      (dirname path))
                   frame))))
               (dirname path))
              (find-new-index
               (strip-cars (partial-collapse frame (dirname path))))))
            (find-new-index (strip-cars (partial-collapse frame (dirname path))))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
             (dirname path)))
           (append
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
             (dirname path))
            (list (basename path)))
           '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
             (contents)))))
        (fat32-filename-list-equiv (append (dirname path)
                                           (list (basename path)))
                                   path)
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (frame-reps-fs frame fs)
        (abs-fs-p fs)
        (consp (assoc-equal 0 frame))
        (atom
         (abs-addrs
          (remove-assoc-equal
           (basename path)
           (mv-nth
            0
            (abs-alloc
             (frame-val->dir
              (cdr (assoc-equal
                    (abs-find-file-src (partial-collapse frame (dirname path))
                                       (dirname path))
                    (partial-collapse frame (dirname path)))))
             (nthcdr
              (len
               (frame-val->path
                (cdr
                 (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  (partial-collapse frame (dirname path))))))
              (dirname path))
             (find-new-index
              (strip-cars (partial-collapse frame (dirname path)))))))))
        (abs-complete
         (abs-file->contents
          (mv-nth 0
                  (abs-find-file (partial-collapse frame (dirname path))
                                 (dirname path)))))
        (not (equal (abs-find-file-src (partial-collapse frame (dirname path))
                                       (dirname path))
                    0))
        (not
         (consp (names-at (frame->root (partial-collapse frame (dirname path)))
                          (dirname path))))
        (path-clear
         (dirname path)
         (remove-assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          (frame->frame (partial-collapse frame (dirname path)))))
        (equal (mv-nth 1
                       (hifat-find-file (mv-nth 0 (collapse frame))
                                        (dirname path)))
               0)
        (m1-directory-file-p (mv-nth 0
                                     (hifat-find-file (mv-nth 0 (collapse frame))
                                                      (dirname path))))
        (not (equal (mv-nth 1
                            (hifat-find-file (mv-nth 0 (collapse frame))
                                             path))
                    0)))
       (frame-reps-fs
        (mv-nth 0 (abs-mkdir frame path))
        (mv-nth 0
                (hifat-place-file
                 (mv-nth 0 (collapse frame))
                 path
                 (m1-file (dir-ent-install-directory-bit (dir-ent-fix nil)
                                                         t)
                          nil)))))
      :hints
      (("goal"
        :do-not-induct t
        :in-theory
        (e/d (abs-mkdir frame-reps-fs abs-complete
                        abs-separate-of-frame->frame-of-collapse-this-lemma-10)
             ((:rewrite abs-mkdir-correctness-lemma-128)
              (:rewrite abs-mkdir-correctness-lemma-177)
              (:rewrite abs-no-dups-p-of-remove1-assoc)
              (:rewrite frame-addrs-root-of-frame->frame-of-collapse-this-lemma-1)
              (:rewrite different-from-own-src-1)
              (:rewrite abs-mkdir-correctness-lemma-192)
              (:rewrite hifat-equiv-when-absfat-equiv-lemma-1))))))

    (defthm abs-mkdir-correctness-lemma-3
      (abs-fs-p
       (ctx-app
        (mv-nth
         1
         (abs-alloc
          (frame-val->dir
           (cdr (assoc-equal 0
                             (partial-collapse frame (dirname path)))))
          (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                  (dirname path))
          (find-new-index
           (strip-cars (partial-collapse frame (dirname path))))))
        (mv-nth
         0
         (abs-alloc
          (frame-val->dir
           (cdr (assoc-equal 0
                             (partial-collapse frame (dirname path)))))
          (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                  (dirname path))
          (find-new-index
           (strip-cars (partial-collapse frame (dirname path))))))
        (find-new-index (strip-cars (partial-collapse frame (dirname path))))
        (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                (dirname path)))))

    (defthm
      abs-mkdir-correctness-lemma-31
      (implies
       (not (consp (dirname path)))
       (ctx-app-ok
        (mv-nth
         1
         (abs-alloc
          (frame-val->dir
           (cdr (assoc-equal 0
                             (partial-collapse frame (dirname path)))))
          (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                  (dirname path))
          (find-new-index
           (strip-cars (partial-collapse frame (dirname path))))))
        (find-new-index (strip-cars (partial-collapse frame (dirname path))))
        (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                (dirname path)))))

    (defthm abs-mkdir-correctness-lemma-148
      (implies
       (and
        (no-duplicatesp-equal
         (strip-cars (partial-collapse frame (dirname path)))))
       (no-duplicatesp-equal
        (strip-cars
         (frame->frame
          (frame-with-root
           (frame->root (partial-collapse frame (dirname path)))
           (frame->frame (partial-collapse frame (dirname path)))))))))

    (defthm
      abs-mkdir-correctness-lemma-150
      (implies
       (and
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame))))))
       (prefixp
        (frame-val->path
         (cdr (assoc-equal 0
                           (partial-collapse frame (dirname path)))))
        (fat32-filename-list-fix (dirname path))))
      :hints (("goal" :do-not-induct t)))

    (defthm
      abs-mkdir-correctness-lemma-151
      (implies
       (frame-reps-fs frame fs)
       (no-duplicatesp-equal
        (strip-cars (partial-collapse frame (dirname path)))))
      :hints (("goal" :do-not-induct t
               :in-theory (enable frame-reps-fs))))

    (defthm
      abs-mkdir-correctness-lemma-195
      (implies
       (and
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (frame-reps-fs frame fs)
        (consp (assoc-equal 0 frame))
        (abs-complete
         (abs-file->contents
          (mv-nth 0
                  (abs-find-file (partial-collapse frame (dirname path))
                                 (dirname path)))))
        (consp (dirname path))
        (not (equal (mv-nth 1
                            (hifat-find-file (mv-nth 0 (collapse frame))
                                             (dirname path)))
                    0)))
       (frame-reps-fs (mv-nth 0 (abs-mkdir frame path))
                      (mv-nth 0 (collapse frame))))
      :hints (("goal" :do-not-induct t
               :in-theory (e/d
                           (frame-reps-fs abs-mkdir)
                           ((:REWRITE ABS-DIRECTORY-FILE-P-WHEN-M1-FILE-P)
                            (:REWRITE ABS-FILE-ALIST-P-CORRECTNESS-1)
                            (:REWRITE ABS-FILE-ALIST-P-OF-ABS-FS-FIX)
                            (:REWRITE ABS-FIND-FILE-HELPER-WHEN-M1-FILE-ALIST-P)
                            (:REWRITE ABS-MKDIR-CORRECTNESS-LEMMA-128)
                            (:REWRITE ABS-SEPARATE-CORRECTNESS-2)
                            (:REWRITE COLLAPSE-CONGRUENCE-LEMMA-4 . 1)
                            (:REWRITE COLLAPSE-CONGRUENCE-LEMMA-4 . 2)
                            (:REWRITE HIFAT-FIND-FILE-CORRECTNESS-1))))))

    (defthm
      abs-mkdir-correctness-lemma-196
      (implies
       (and
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (frame-reps-fs frame fs)
        (consp (assoc-equal 0 frame))
        (abs-complete
         (abs-file->contents
          (mv-nth 0
                  (abs-find-file (partial-collapse frame (dirname path))
                                 (dirname path)))))
        (consp (dirname path))
        (not (equal (mv-nth 1
                            (hifat-find-file (mv-nth 0 (collapse frame))
                                             (dirname path)))
                    0)))
       (equal (mv-nth 2 (abs-mkdir frame path))
              *enoent*))
      :hints (("goal" :do-not-induct t
               :in-theory (enable frame-reps-fs abs-mkdir))))

    (defthm
      abs-mkdir-correctness-lemma-21
      (implies
       (and
        (mv-nth 1 (collapse frame))
        (absfat-equiv (mv-nth 0 (collapse frame))
                      fs)
        (frame-p frame)
        (abs-separate frame)
        (subsetp-equal (abs-addrs (frame-val->dir (cdr (assoc-equal 0 frame))))
                       (frame-addrs-root (frame->frame frame)))
        (no-duplicatesp-equal (strip-cars frame))
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (abs-fs-p fs))
       (hifat-equiv
        (put-assoc-equal (basename path)
                         '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (contents))
                         (mv-nth 0 (collapse frame)))
        (put-assoc-equal (basename path)
                         '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (contents))
                         fs)))
      :hints
      (("goal" :in-theory (e/d (frame->root)
                               ((:rewrite hifat-equiv-when-absfat-equiv)))
        :use (:instance (:rewrite hifat-equiv-when-absfat-equiv)
                        (abs-file-alist2 fs)
                        (abs-file-alist1 (mv-nth 0 (collapse frame)))))))

    (defthm
      abs-mkdir-correctness-lemma-22
      (implies (and (absfat-equiv (mv-nth 0 (collapse frame))
                                  fs)
                    (abs-fs-p fs)
                    (not (consp (assoc-equal (basename path) fs))))
               (not (consp (assoc-equal (basename path)
                                        (mv-nth 0 (collapse frame))))))
      :instructions (:promote (:dive 1)
                              (:rewrite ctx-app-ok-when-absfat-equiv-lemma-1
                                        ((abs-file-alist2 fs)))
                              :top
                              :s (:rewrite abs-fs-p-of-collapse)))

    (defthm
      abs-mkdir-correctness-lemma-23
      (implies
       (and (fat32-filename-list-equiv (append (dirname path)
                                               (list (basename path)))
                                       path)
            (frame-reps-fs frame fs)
            (abs-fs-p fs)
            (consp (assoc-equal 0 frame))
            (path-clear (dirname path)
                        (frame->frame (partial-collapse frame (dirname path))))
            (not (consp (dirname path)))
            (not (equal (mv-nth 1
                                (hifat-find-file (mv-nth 0 (collapse frame))
                                                 path))
                        0)))
       (frame-reps-fs
        (mv-nth 0 (abs-mkdir frame path))
        (mv-nth 0
                (hifat-place-file
                 (mv-nth 0 (collapse frame))
                 path
                 (m1-file (dir-ent-install-directory-bit (dir-ent-fix nil)
                                                         t)
                          nil)))))
      :hints
      (("goal" :do-not-induct t
        :in-theory
        (enable frame-reps-fs abs-mkdir frame->root
                hifat-file-alist-fix-when-hifat-no-dups-p
                hifat-no-dups-p-when-abs-complete
                abs-fs-p-correctness-1
                abs-fs-p-of-frame-val->dir abs-complete
                abs-separate-of-frame->frame-of-collapse-this-lemma-10)))))

  ;; This has some unnecessary hypotheses which are awkward to remove.
  (defthm abs-mkdir-correctness-1
    (implies
     (and
      (frame-p frame)
      (no-duplicatesp-equal (strip-cars frame))
      (equal (frame-val->src$inline (cdr (assoc-equal 0 frame)))
             '0)
      (not (consp (frame-val->path$inline (cdr (assoc-equal 0 frame)))))
      (frame-reps-fs frame fs)
      (abs-fs-p fs)
      (m1-file-alist-p fs)
      (consp (assoc-equal 0 frame))
      (abs-complete
       (abs-file->contents$inline
        (mv-nth 0
                (abs-find-file (partial-collapse frame (dirname path))
                               (dirname path)))))
      (if
          (equal (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 0)
          (path-clear (dirname path)
                      (frame->frame (partial-collapse frame (dirname path))))
        (and
         (atom (names-at (frame->root (partial-collapse frame (dirname path)))
                         (dirname path)))
         (path-clear
          (dirname path)
          (remove-assoc-equal
           (abs-find-file-src (partial-collapse frame (dirname path))
                              (dirname path))
           (frame->frame (partial-collapse frame (dirname path))))))))
     (and (frame-reps-fs (mv-nth 0 (abs-mkdir frame path))
                         (mv-nth 0
                                 (hifat-mkdir (mv-nth 0 (collapse frame))
                                              path)))
          (equal (mv-nth 2 (abs-mkdir frame path))
                 (mv-nth 2
                         (hifat-mkdir (mv-nth 0 (collapse frame))
                                      path)))))
    :hints
    (("goal"
      :do-not-induct t
      :use
      ((:instance
        collapse-hifat-place-file-2
        (x (abs-find-file-src (partial-collapse frame (dirname path))
                              (dirname path)))
        (frame (frame->frame (partial-collapse frame (dirname path))))
        (path
         (append
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               frame))))
           (dirname path))
          (list (basename path))))
        (file '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                         0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                (contents)))
        (root (frame->root (partial-collapse frame (dirname path)))))
       (:instance abs-find-file-src-correctness-2
                  (frame (partial-collapse frame (dirname path)))
                  (path (dirname path)))
       (:instance
        (:rewrite abs-place-file-helper-of-ctx-app-1 . 1)
        (x-path
         (nthcdr
          (len
           (frame-val->path
            (cdr (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  frame))))
          (dirname path)))
        (x
         (find-new-index (strip-cars (partial-collapse frame (dirname path)))))
        (file '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                         0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                (contents)))
        (path (list (basename path)))
        (fs
         (mv-nth
          0
          (abs-alloc
           (frame-val->dir
            (cdr (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  (partial-collapse frame (dirname path)))))
           (nthcdr
            (len
             (frame-val->path
              (cdr
               (assoc-equal
                (abs-find-file-src (partial-collapse frame (dirname path))
                                   (dirname path))
                frame))))
            (dirname path))
           (find-new-index
            (strip-cars (partial-collapse frame (dirname path)))))))
        (abs-file-alist1
         (mv-nth
          1
          (abs-alloc
           (frame-val->dir
            (cdr (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  (partial-collapse frame (dirname path)))))
           (nthcdr
            (len
             (frame-val->path
              (cdr
               (assoc-equal
                (abs-find-file-src (partial-collapse frame (dirname path))
                                   (dirname path))
                frame))))
            (dirname path))
           (find-new-index
            (strip-cars (partial-collapse frame (dirname path))))))))
       abs-mkdir-correctness-lemma-50)))
    :otf-flg t))

(defthm
  abs-mkdir-correctness-lemma-155
  (implies
   (and (absfat-equiv (mv-nth 0 (collapse frame))
                      fs)
        (abs-fs-p fs)
        (m1-file-alist-p fs))
   (equal
    (frame-reps-fs
     (mv-nth 0 (abs-mkdir frame path))
     (mv-nth
      0
      (hifat-place-file (mv-nth 0 (collapse frame))
                        path
                        '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                                   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                          (contents)))))
    (frame-reps-fs
     (mv-nth 0 (abs-mkdir frame path))
     (mv-nth
      0
      (hifat-place-file fs path
                        '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                                   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                          (contents)))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d nil
                    ((:rewrite abs-place-file-helper-correctness-1)))
    :use ((:instance (:rewrite abs-place-file-helper-correctness-1)
                     (file '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                             (contents)))
                     (path path)
                     (fs (mv-nth 0 (collapse frame))))
          (:instance (:rewrite abs-place-file-helper-correctness-1)
                     (file '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                             (contents)))
                     (path path)
                     (fs fs))))))

(defthmd
  abs-mkdir-correctness-lemma-156
  (implies (and (frame-reps-fs frame fs)
                (abs-fs-p fs)
                (m1-file-alist-p fs))
           (and (absfat-equiv (mv-nth 0 (collapse frame))
                              fs)
                (hifat-equiv (mv-nth 0 (collapse frame))
                             fs)))
  :instructions
  (:promote
   (:demote 1)
   (:dive 1)
   :x :top :split (:demote 4)
   (:dive 1)
   (:claim (and (m1-file-alist-p (abs-fs-fix (mv-nth 0 (collapse frame))))
                (m1-file-alist-p (abs-fs-fix fs))))
   (:rewrite hifat-equiv-when-absfat-equiv)
   :top :bash))

(skip-proofs
 (defthm
   abs-mkdir-correctness-lemma-158
   (implies
    (and (frame-p frame)
         (no-duplicatesp-equal (strip-cars (frame->frame frame)))
         (abs-separate frame)
         (mv-nth 1 (collapse frame))
         (atom (frame-val->path (cdr (assoc-equal 0 frame))))
         (subsetp-equal (abs-addrs (frame->root frame))
                        (frame-addrs-root (frame->frame frame))))
    (abs-complete
     (abs-file->contents$inline
      (mv-nth 0
              (abs-find-file (partial-collapse frame path)
                             path)))))))

(skip-proofs
 (defthm
   abs-mkdir-correctness-lemma-161
   (implies
    (and (frame-p frame)
         (no-duplicatesp-equal (strip-cars (frame->frame frame)))
         (abs-separate frame)
         (mv-nth 1 (collapse frame))
         (atom (frame-val->path (cdr (assoc-equal 0 frame))))
         (subsetp-equal (abs-addrs (frame->root frame))
                        (frame-addrs-root (frame->frame frame))))
    (and
     (implies
      (equal (abs-find-file-src (partial-collapse frame path)
                                path)
             0)
      (path-clear path
                  (frame->frame (partial-collapse frame path))))
     (implies
      (not
       (equal (abs-find-file-src (partial-collapse frame path)
                                 path)
              0))
      (and
       (not
        (consp (names-at (frame->root (partial-collapse frame path))
                         path)))
       (path-clear
        path
        (remove-assoc-equal
         (abs-find-file-src (partial-collapse frame path)
                            path)
         (frame->frame (partial-collapse frame path))))))))))

(defthm
  abs-mkdir-correctness-2
  (implies (and (zp (frame-val->src (cdr (assoc-equal 0 frame))))
                (frame-reps-fs frame fs)
                (abs-fs-p fs)
                (consp (assoc-equal 0 frame)))
           (and (frame-reps-fs (mv-nth 0 (abs-mkdir frame path))
                               (mv-nth 0 (hifat-mkdir fs path)))
                (equal (mv-nth 2 (abs-mkdir frame path))
                       (mv-nth 2 (hifat-mkdir fs path)))))
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d (frame-reps-fs)
                    (abs-mkdir-correctness-1
                     (:rewrite
                      abs-mkdir-correctness-lemma-60)))
    :use (abs-mkdir-correctness-1 abs-mkdir-correctness-lemma-156))))

(defthm
  abs-find-file-after-abs-mkdir-lemma-15
  (implies
   (and (fat32-filename-p name)
        (abs-fs-p fs))
   (equal
    (abs-find-file-helper (put-assoc-equal name file fs)
                          (cons name nil))
    (if
        (abs-directory-file-p (abs-file-fix file))
        (mv (abs-file (abs-file->dir-ent file)
                      (abs-fs-fix (abs-file->contents file)))
            0)
      (mv (abs-file-fix file) 0))))
  :hints (("goal" :in-theory (enable abs-mkdir partial-collapse
                                     1st-complete-under-path abs-find-file
                                     abs-find-file-src abs-find-file-helper
                                     assoc-equal-of-frame-with-root)
           :do-not-induct t)))

(defthm
  abs-find-file-after-abs-mkdir-lemma-17
  (implies
   (and (fat32-filename-p name) (natp n2))
   (equal
    (abs-find-file-helper
     (mv-nth
      1
      (abs-alloc (put-assoc-equal name file
                                     (mv-nth 0 (abs-alloc fs nil n1)))
                    (cons name nil)
                    n2))
     (cons name nil))
    (if (not (abs-directory-file-p (abs-file-fix file)))
        (mv (abs-file-fix file) 0)
      (mv (abs-file (abs-file->dir-ent file)
                    (list n2))
          0))))
  :hints (("goal" :in-theory (enable abs-mkdir partial-collapse
                                     abs-alloc abs-find-file-helper
                                     1st-complete-under-path
                                     abs-find-file abs-find-file-src
                                     assoc-equal-of-frame-with-root
                                     put-assoc-equal-of-frame-with-root
                                     abs-directory-file-p abs-file-alist-p
                                     abs-fs-fix)
           :do-not-induct t)))

(defthm
  abs-find-file-after-abs-mkdir-lemma-18
  (implies
   (and (abs-fs-p fs)
        (natp n)
        (fat32-filename-p name))
   (equal
    (abs-find-file-helper (mv-nth 1
                                  (abs-alloc (put-assoc-equal name file fs)
                                                (cons name nil)
                                                n))
                          (cons name nil))
    (if (not (abs-directory-file-p (abs-file-fix file)))
        (mv (abs-file-fix file) 0)
        (mv (abs-file (abs-file->dir-ent file)
                      (list n))
            0))))
  :hints (("goal" :in-theory (enable abs-fs-fix
                                     abs-mkdir abs-file-contents-fix
                                     abs-alloc abs-find-file-helper
                                     assoc-equal-of-frame-with-root
                                     put-assoc-equal-of-frame-with-root)
           :do-not-induct t))
  :otf-flg t)

(defthm
  abs-find-file-after-abs-mkdir-lemma-21
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

(encapsulate
  ()

  (local
   (defthm
     lemma
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
     :instructions
     ((:casesplit
       (not
        (equal
         (abs-find-file-helper
          (frame-val->dir (cdr (assoc-equal (abs-find-file-src frame path)
                                            (frame->frame frame))))
          (nthcdr
           (len (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                                   (frame->frame frame)))))
           path))
         (abs-find-file (frame->frame frame)
                        path))))
      :bash :promote (:contrapose 1)
      (:claim
       (not
        (equal
         (mv-nth
          1
          (abs-find-file-helper
           (frame-val->dir (cdr (assoc-equal (abs-find-file-src frame path)
                                             frame)))
           (nthcdr
            (len
             (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                                frame))))
            path)))
         *enoent*))
       :hints :none)
      (:change-goal nil t)
      (:dive 1)
      (:rewrite abs-find-file-after-abs-mkdir-lemma-21)
      (:bash
       ("goal" :in-theory (enable (:rewrite assoc-equal-of-frame->frame)))))))

  (defthm
    abs-find-file-after-abs-mkdir-lemma-22
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
    :instructions
    (:promote
     (:dive 1)
     (:claim
      (prefixp (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                                  (frame->frame frame))))
               (fat32-filename-list-fix path))
      :hints :none)
     (:rewrite lemma)
     (:dive 1 1 1)
     (:rewrite assoc-equal-of-frame->frame)
     :top :bash)))

(defthm
  abs-find-file-after-abs-mkdir-lemma-23
  (implies
   (not
    (equal (mv-nth 1
                   (abs-find-file-helper
                    (frame->root (partial-collapse frame (cons name nil)))
                    (cons name path)))
           *enoent*))
   (not
    (equal (mv-nth '1
                   (abs-find-file-helper
                    (frame->root (partial-collapse frame (cons name nil)))
                    (cons name nil)))
           *enoent*)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable abs-find-file-helper)))
  :rule-classes :forward-chaining)

(skip-proofs
 (defthm abs-find-file-after-abs-mkdir-lemma-5
   (implies
    (and
     (frame-p frame)
     (abs-separate frame)
     (subsetp-equal (abs-addrs (frame->root frame))
                    (frame-addrs-root (frame->frame frame)))
     (no-duplicatesp-equal (strip-cars frame))
     (mv-nth 1 (collapse frame))
     (fat32-filename-list-prefixp path1 path2))
    (equal
     (1st-complete-under-path
      (frame->frame (partial-collapse frame path1))
      path2)
     0))))

(defthm
  1st-complete-under-path-of-put-assoc-1
  (implies
   (and
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (not (and (equal (1st-complete-under-path (put-assoc-equal name val frame)
                                              path)
                     name)
              (atom (abs-addrs (frame-val->dir val)))
              (prefixp path (frame-val->path val)))))
   (equal (1st-complete-under-path (put-assoc-equal name val frame)
                                   path)
          (1st-complete-under-path (remove-assoc-equal name frame)
                                   path)))
  :hints (("goal" :in-theory (enable 1st-complete-under-path))))

;; (thm
;;  (IMPLIES
;;   (AND
;;    (FRAME-P FRAME)
;;    (NO-DUPLICATESP-EQUAL (STRIP-CARS FRAME))
;;    (abs-separate frame)
;;    (MV-NTH '1 (COLLAPSE FRAME))
;;    (subsetp-equal (abs-addrs (frame->root frame))
;;                   (frame-addrs-root (frame->frame frame)))
;;    (CONSP (ASSOC-EQUAL 0 FRAME))
;;    (EQUAL (FRAME-VAL->PATH$INLINE (CDR (ASSOC-EQUAL 0 FRAME)))
;;           NIL)
;;    (EQUAL (FRAME-VAL->SRC$INLINE (CDR (ASSOC-EQUAL 0 FRAME)))
;;           0))
;;    (EQUAL
;;     (1ST-COMPLETE-UNDER-PATH
;;      (FRAME->FRAME
;;       (PUT-ASSOC-EQUAL
;;        (ABS-FIND-FILE-SRC (PARTIAL-COLLAPSE FRAME '("TMP        "))
;;                           '("TMP        "))
;;        (FRAME-VAL
;;         (FRAME-VAL->PATH$INLINE
;;          (CDR
;;             (ASSOC-EQUAL
;;                  (ABS-FIND-FILE-SRC (PARTIAL-COLLAPSE FRAME '("TMP        "))
;;                                     '("TMP        "))
;;                  FRAME)))
;;         (MV-NTH
;;          1
;;          (ABS-ALLOC
;;           (FRAME-VAL->DIR$INLINE
;;            (CDR
;;             (ASSOC-EQUAL
;;                  (ABS-FIND-FILE-SRC (PARTIAL-COLLAPSE FRAME '("TMP        "))
;;                                     '("TMP        "))
;;                  (PARTIAL-COLLAPSE FRAME '("TMP        ")))))
;;           (NTHCDR
;;            (LEN
;;             (FRAME-VAL->PATH$INLINE
;;              (CDR
;;               (ASSOC-EQUAL
;;                  (ABS-FIND-FILE-SRC (PARTIAL-COLLAPSE FRAME '("TMP        "))
;;                                     '("TMP        "))
;;                  FRAME))))
;;            '("TMP        "))
;;           (FIND-NEW-INDEX
;;                (STRIP-CARS (PARTIAL-COLLAPSE FRAME '("TMP        "))))))
;;         (FRAME-VAL->SRC$INLINE
;;          (CDR
;;             (ASSOC-EQUAL
;;                  (ABS-FIND-FILE-SRC (PARTIAL-COLLAPSE FRAME '("TMP        "))
;;                                     '("TMP        "))
;;                  FRAME))))
;;        (PARTIAL-COLLAPSE FRAME '("TMP        "))))
;;      '("TMP        " "DOCS       "))
;;     0))
;;  :HINTS (("goal" :IN-THEORY
;;           (e/d (ABS-MKDIR
;;                 PARTIAL-COLLAPSE 1ST-COMPLETE-UNDER-PATH
;;                 ABS-FIND-FILE ABS-FIND-FILE-SRC
;;                 ASSOC-EQUAL-OF-FRAME-WITH-ROOT
;;                 PUT-ASSOC-EQUAL-OF-FRAME-WITH-ROOT
;;                 frame->frame-of-put-assoc abs-addrs abs-alloc
;;                 abs-fs-fix)
;;                ((:REWRITE FRAME-P-OF-CDR-WHEN-FRAME-P)
;;                 (:REWRITE COLLAPSE-HIFAT-PLACE-FILE-LEMMA-6)
;;                 (:DEFINITION FAT32-FILENAME-LIST-PREFIXP)
;;                 (:REWRITE LEN-WHEN-PREFIXP)
;;                 (:REWRITE CAR-OF-NTHCDR)
;;                 ABS-SEPARATE-OF-FRAME->FRAME-OF-COLLAPSE-THIS-LEMMA-8))
;;           :DO-NOT-INDUCT T
;;           :restrict ((1ST-COMPLETE-UNDER-PATH-WHEN-PATH-CLEAR-OF-PREFIX
;;                       ((PATH1 '("TMP        ")))))))
;;  :otf-flg t)
(defthm
  abs-find-file-after-abs-mkdir-lemma-6
  (implies (and (zp (abs-find-file-src frame (list basename)))
                (fat32-filename-p basename)
                (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
                (frame-p frame)
                (no-duplicatesp-equal (strip-cars frame))
                (zp
                 (mv-nth 1
                         (abs-find-file frame (list basename)))))
           (and
            (consp (assoc-equal basename (frame->root frame)))
            (equal (cdr (assoc-equal basename (frame->root frame)))
                   (mv-nth 0
                           (abs-find-file frame (list basename))))
            (consp (assoc-equal basename (frame-val->dir (cdr (assoc-equal 0 frame)))))
            (equal (cdr (assoc-equal basename (frame-val->dir (cdr (assoc-equal 0 frame)))))
                   (mv-nth 0
                           (abs-find-file frame (list basename))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (basename-alt abs-find-file-helper frame->root)
                    (abs-mkdir-correctness-lemma-86))
    :use
    (:instance
     abs-mkdir-correctness-lemma-86
     (path (list basename))
     (x-path
      (nthcdr
       (len (frame-val->path
             (cdr (assoc-equal (abs-find-file-src frame (list basename))
                               frame))))
       (list basename))))))
  :otf-flg t)

;; This theorem shows that abs-find-file, without the benefit of
;; partial-collapse, can't really get the contents of a directory.
(DEFTHM
 ABS-FIND-FILE-AFTER-ABS-MKDIR-2
 (IMPLIES
  (AND
   (FRAME-P FRAME)
   (NO-DUPLICATESP-EQUAL (STRIP-CARS FRAME))
   (abs-separate frame)
   (MV-NTH '1 (COLLAPSE FRAME))
   (subsetp-equal (abs-addrs (frame->root frame))
                  (frame-addrs-root (frame->frame frame)))
   (CONSP (ASSOC-EQUAL 0 FRAME))
   (EQUAL (FRAME-VAL->PATH$INLINE (CDR (ASSOC-EQUAL 0 FRAME)))
          NIL)
   (EQUAL (FRAME-VAL->SRC$INLINE (CDR (ASSOC-EQUAL 0 FRAME)))
          0)
   (EQUAL
    (1ST-COMPLETE-UNDER-PATH
     (FRAME->FRAME
      (PUT-ASSOC-EQUAL
       (ABS-FIND-FILE-SRC (PARTIAL-COLLAPSE FRAME '("TMP        "))
                          '("TMP        "))
       (FRAME-VAL
        (FRAME-VAL->PATH$INLINE
         (CDR
            (ASSOC-EQUAL
                 (ABS-FIND-FILE-SRC (PARTIAL-COLLAPSE FRAME '("TMP        "))
                                    '("TMP        "))
                 FRAME)))
        (MV-NTH
         1
         (ABS-ALLOC
          (FRAME-VAL->DIR$INLINE
           (CDR
            (ASSOC-EQUAL
                 (ABS-FIND-FILE-SRC (PARTIAL-COLLAPSE FRAME '("TMP        "))
                                    '("TMP        "))
                 (PARTIAL-COLLAPSE FRAME '("TMP        ")))))
          (NTHCDR
           (LEN
            (FRAME-VAL->PATH$INLINE
             (CDR
              (ASSOC-EQUAL
                 (ABS-FIND-FILE-SRC (PARTIAL-COLLAPSE FRAME '("TMP        "))
                                    '("TMP        "))
                 FRAME))))
           '("TMP        "))
          (FIND-NEW-INDEX
               (STRIP-CARS (PARTIAL-COLLAPSE FRAME '("TMP        "))))))
        (FRAME-VAL->SRC$INLINE
         (CDR
            (ASSOC-EQUAL
                 (ABS-FIND-FILE-SRC (PARTIAL-COLLAPSE FRAME '("TMP        "))
                                    '("TMP        "))
                 FRAME))))
       (PARTIAL-COLLAPSE FRAME '("TMP        "))))
     '("TMP        " "DOCS       "))
    0))
  (B*
   (((MV FRAME & MKDIR-ERROR-CODE)
     (ABS-MKDIR FRAME
                (PATH-TO-FAT32-PATH (EXPLODE "/tmp/docs")))))
   (IMPLIES
       (EQUAL MKDIR-ERROR-CODE 0)
       (B* (((MV FRAME & &)
             (ABS-MKDIR FRAME
                        (PATH-TO-FAT32-PATH (EXPLODE "/tmp/docs/pdf-docs"))))
            ((MV & ERROR-CODE)
             (ABS-FIND-FILE FRAME
                            (PATH-TO-FAT32-PATH (EXPLODE "/tmp/docs")))))
           (AND (EQUAL ERROR-CODE 0))))))
 :HINTS (("goal" :IN-THEORY
          (e/d (ABS-MKDIR
                PARTIAL-COLLAPSE 1ST-COMPLETE-UNDER-PATH
                ABS-FIND-FILE ABS-FIND-FILE-SRC
                ASSOC-EQUAL-OF-FRAME-WITH-ROOT
                PUT-ASSOC-EQUAL-OF-FRAME-WITH-ROOT)
               ((:REWRITE FRAME-P-OF-CDR-WHEN-FRAME-P)
                (:REWRITE COLLAPSE-HIFAT-PLACE-FILE-LEMMA-6)
                (:DEFINITION FAT32-FILENAME-LIST-PREFIXP)
                (:REWRITE LEN-WHEN-PREFIXP)
                (:REWRITE CAR-OF-NTHCDR)
                ABS-SEPARATE-OF-FRAME->FRAME-OF-COLLAPSE-THIS-LEMMA-8))
          :DO-NOT-INDUCT T
          :expand
          (ABS-DIRECTORY-FILE-P
           (ABS-FILE
            (ABS-FILE->DIR-ENT
             (CDR
              (ASSOC-EQUAL
               "TMP        "
               (FRAME-VAL->DIR
                (CDR (ASSOC-EQUAL 0
                                  (PARTIAL-COLLAPSE FRAME '("TMP        "))))))))
            (LIST (FIND-NEW-INDEX
                   (STRIP-CARS (PARTIAL-COLLAPSE FRAME '("TMP        "))))))))
         ("Subgoal 2.1"
          :in-theory (enable abs-find-file-helper abs-alloc abs-file-alist-p)))
 :otf-flg t)

(defund good-frame-p (frame)
  (b*
      (((mv & result) (collapse frame)))
    (and result
         (equal (frame-val->path (cdr (assoc-equal 0 frame)))
                nil)
         (consp (assoc-equal 0 frame))
         (equal (frame-val->src (cdr (assoc-equal 0 frame)))
                0)
         (frame-p frame)
         (no-duplicatesp-equal (strip-cars frame))
         (abs-separate frame)
         (subsetp-equal (abs-addrs (frame->root frame))
                        (frame-addrs-root (frame->frame frame))))))

(thm (implies (good-frame-p frame)
              (frame-reps-fs frame (mv-nth 0 (collapse frame))))
     :hints (("GOal" :do-not-induct t
              :in-theory (enable good-frame-p frame-reps-fs))))

(defthm
  abs-lstat-after-abs-mkdir-1
  (implies (good-frame-p frame)
           (b* (((mv frame & mkdir-error-code)
                 (abs-mkdir frame path)))
             (implies (equal mkdir-error-code 0)
                      (b* (((mv & lstat-error-code &)
                            (abs-lstat frame path)))
                        (equal lstat-error-code 0)))))
  :hints
  (("goal"
    :in-theory (enable abs-mkdir abs-lstat abs-alloc abs-fs-fix
                       abs-find-file-helper abs-find-file good-frame-p))))

(defthm
  abs-lstat-after-abs-mkdir-2
  (implies (good-frame-p init-frame)
           (b* (((mv final-frame & mkdir-error-code)
                 (abs-mkdir init-frame path)))
             (implies (not (equal mkdir-error-code 0))
                      (collapse-equiv final-frame init-frame))))
  :hints
  (("goal"
    :in-theory (enable collapse-equiv abs-mkdir abs-lstat abs-alloc abs-fs-fix
                       abs-find-file-helper abs-find-file good-frame-p) :expand
                       (:free (root) (collapse (frame-with-root root nil))))))

(defund abs-mknod (frame path)
  (declare (xargs :guard (and (frame-p frame)
                              (consp (assoc-equal 0 frame))
                              (fat32-filename-list-p path)
                              (no-duplicatesp-equal (strip-cars frame)))
                  :guard-debug t
                  :guard-hints
                  (("goal"
                    :in-theory (enable abs-find-file-helper abs-fs-p)))))
  (b*
      ((path (mbe :exec path :logic (fat32-filename-list-fix path)))
       (dirname (dirname path)) (frame (partial-collapse frame dirname))
       ;; After partial-collapse, either the parent directory is there in one
       ;; variable, or it isn't there at all.
       ((mv parent-dir error-code) (abs-find-file frame dirname))
       ((unless (or (atom dirname) (and (zp error-code) (abs-directory-file-p parent-dir))))
        (mv frame -1 *enoent*))
       (src (abs-find-file-src frame dirname))
       (new-index (find-new-index
                   ;; Using this, not (strip-cars (frame->frame frame)), to make
                   ;; sure we don't get a zero.
                   (strip-cars frame)))
       ;; It's not even a matter of removing that thing - we need to leave a
       ;; body address in its place...
       ((mv var new-src-dir)
        (abs-alloc (frame-val->dir (cdr (assoc-equal src frame)))
                   (nthcdr (len (frame-val->path (cdr (assoc-equal src frame)))) dirname)
                   new-index))
       ;; Check somewhere that (basename path) is not already present...
       ((unless (consp path)) (mv frame -1 *enoent*))
       ((when (consp (abs-assoc (basename path) var))) (mv frame -1 *eexist*))
       (frame (put-assoc-equal src (change-frame-val (cdr (assoc-equal src frame))
                                                     :dir new-src-dir)
                               frame))
       (new-var (abs-put-assoc (basename path)
                               (make-abs-file :contents ""
                                              :dir-ent (dir-ent-set-filename (dir-ent-fix nil)
                                                                             (basename path)))
                               var))
       (frame
        (frame-with-root (frame->root frame)
                         (cons (cons new-index
                                     (frame-val dirname
                                                new-var src))
                               (frame->frame frame)))))
    (mv frame 0 0)))

(defund
  abs-pwrite
  (fd buf offset frame fd-table file-table)
  (declare
   (xargs
    :guard (and (natp fd)
                (stringp buf)
                (natp offset)
                (fd-table-p fd-table)
                (file-table-p file-table)
                (frame-p frame)
                (consp (assoc-equal 0 frame)))
    :guard-debug t
    :guard-hints
    (("goal"
      :do-not-induct t
      :in-theory (e/d (len-of-insert-text abs-no-dups-file-p abs-no-dups-p)
                      (unsigned-byte-p))
      :expand
      (:with m1-file-contents-fix-when-m1-file-contents-p
             (:free (oldtext)
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
       (path (file-table-element->fid (cdr file-table-entry)))
       (dirname (dirname path)) (frame (partial-collapse frame dirname))
       ;; After partial-collapse, either the parent directory is there in one
       ;; variable, or it isn't there at all.
       ((mv parent-dir error-code) (abs-find-file frame dirname))
       ((unless (or (atom dirname) (and (zp error-code) (abs-directory-file-p parent-dir))))
        (mv frame -1 *enoent*))
       (src (abs-find-file-src frame dirname))
       (new-index (find-new-index
                   ;; Using this, not (strip-cars (frame->frame frame)), to make
                   ;; sure we don't get a zero.
                   (strip-cars frame)))
       ((mv var new-src-dir)
        (abs-alloc (frame-val->dir (cdr (assoc-equal src frame)))
                   (nthcdr (len (frame-val->path (cdr (assoc-equal src frame)))) dirname)
                   new-index))
       ((when (consp (abs-assoc (basename path) var))) (mv frame -1 *eexist*))
       ((mv file error-code)
        (if (consp (abs-assoc (basename path) var))
            (mv (cdr (abs-assoc (basename path) var)) 0)
          (mv (make-abs-file) *enoent*)))
       ((mv oldtext dir-ent)
        (if (and (equal error-code 0)
                 (m1-regular-file-p file))
            (mv (coerce (m1-file->contents file) 'list)
                (m1-file->dir-ent file))
            (mv nil (dir-ent-fix nil))))
       ((unless (unsigned-byte-p 32 (+ offset (length buf))))
        (mv frame -1 *enospc*))
       (frame (put-assoc-equal src (change-frame-val (cdr (assoc-equal src frame))
                                                     :dir new-src-dir)
                               frame))
       (file (make-m1-file :dir-ent dir-ent
                           :contents (coerce (insert-text oldtext offset buf)
                                             'string)))
       (new-var (abs-put-assoc (basename path)
                               file
                               var))
       (frame
        (frame-with-root (frame->root frame)
                         (cons (cons new-index
                                     (frame-val dirname
                                                new-var src))
                               (frame->frame frame)))))
    (mv frame (if (equal error-code 0) 0 -1)
        error-code)))

(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse
  (implies
   (and (mv-nth 1 (collapse frame))
        (abs-separate frame)
        (frame-p frame)
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (atom (frame-val->path (cdr (assoc-equal 0 frame))))
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame))))
   (equal
    (1st-complete-under-path (frame->frame (partial-collapse frame path))
                             path)
    0))
  :hints
  (("goal"
    :in-theory (enable partial-collapse
                       1st-complete-under-path)
    :induct (partial-collapse frame path)
    :do-not-induct t
    :expand
    (:with
     (:rewrite partial-collapse-correctness-lemma-122)
     (mv-nth
      1
      (collapse (collapse-this frame
                               (1st-complete-under-path (frame->frame frame)
                                                        path))))))))

(defthm
  abs-mkdir-correctness-lemma-24
  (implies (and (frame-p frame)
                (atom (assoc-equal 0 frame))
                (consp (assoc-equal y frame))
                (abs-complete (frame-val->dir (cdr (assoc-equal y frame))))
                (prefixp path
                         (frame-val->path (cdr (assoc-equal y frame)))))
           (< 0 (1st-complete-under-path frame path)))
  :hints (("goal" :in-theory (enable 1st-complete-under-path)))
  :rule-classes :linear)

(defthm
  collapse-hifat-place-file-lemma-2
  (implies
   (and
    (prefixp
     (frame-val->path
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame)))))
    (dist-names root nil (frame->frame frame))
    (abs-separate (frame->frame frame))
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (dist-names
    root nil
    (frame->frame (collapse-this frame
                                 (1st-complete (frame->frame frame))))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable collapse-this))))

(defund
  partial-seq-this (frame pathname)
  (declare (xargs :guard (and (frame-p frame)
                              (consp (assoc-equal 0 frame)))
                  :measure (len (frame->frame frame))))
  (b*
      (((when (atom (frame->frame frame)))
        nil)
       (head-index
        (1st-complete-under-path (frame->frame frame)
                                 pathname))
       ((when (zp head-index)) nil)
       (head-frame-val
        (cdr (assoc-equal head-index (frame->frame frame))))
       (src
        (frame-val->src
         (cdr
          (assoc-equal
           (1st-complete-under-path (frame->frame frame)
                                    pathname)
           (frame->frame frame))))))
    (if
        (zp src)
        (b*
            (((unless (ctx-app-ok (frame->root frame)
                                  head-index
                                  (frame-val->path head-frame-val)))
              nil))
          (cons
           head-index
           (partial-seq-this (collapse-this frame head-index)
                             pathname)))
      (b*
          ((path (frame-val->path head-frame-val))
           ((when (or (equal src head-index)
                      (atom (assoc-equal src (frame->frame frame)))))
            nil)
           (src-path
            (frame-val->path
             (cdr (assoc-equal src (frame->frame frame)))))
           (src-dir
            (frame-val->dir
             (cdr (assoc-equal src (frame->frame frame)))))
           ((unless (and (prefixp src-path path)
                         (ctx-app-ok src-dir head-index
                                     (nthcdr (len src-path) path))))
            nil))
        (cons
         head-index
         (partial-seq-this (collapse-this frame head-index)
                           pathname))))))

(defthmd
  collapse-seq-of-partial-seq-this-is-partial-collapse
  (implies (no-duplicatesp-equal (strip-cars (frame->frame frame)))
           (equal (partial-collapse frame path)
                  (collapse-seq frame
                                (partial-seq-this frame path))))
  :hints
  (("goal"
    :in-theory
    (e/d (partial-collapse collapse-seq
                           partial-seq-this collapse-iter)
         ((:definition assoc-equal)
          (:rewrite nthcdr-when->=-n-len-l)
          (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8
                    . 3)
          (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8
                    . 2)
          (:definition remove-equal)
          (:rewrite remove-when-absent)))
    :induct (partial-seq-this frame path))))

(defthm
  abs-mkdir-correctness-lemma-89
  (implies
   (and
    (subsetp-equal (abs-addrs (frame->root frame))
                   (frame-addrs-root (frame->frame frame)))
    (atom (frame-val->path (cdr (assoc-equal 0 frame))))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (frame-p frame)
    (abs-separate frame)
    (mv-nth 1 (collapse frame))
    (abs-complete
     (frame-val->dir
      (cdr (assoc-equal y
                        (frame->frame (partial-collapse frame path))))))
    (prefixp
     path
     (frame-val->path
      (cdr (assoc-equal y
                        (frame->frame (partial-collapse frame path)))))))
   (not (consp (assoc-equal y
                            (frame->frame (partial-collapse frame path))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (disable abs-mkdir-correctness-lemma-24
             1st-complete-under-path-of-frame->frame-of-partial-collapse)
    :use ((:instance abs-mkdir-correctness-lemma-24
                     (frame (frame->frame (partial-collapse frame path))))
          1st-complete-under-path-of-frame->frame-of-partial-collapse))))

;; (encapsulate
;;   ()

;;   (local (include-book "tricks/chain-leading-to-complete"))

;;   (thm
;;    (implies
;;     (and (frame-p frame)
;;          (no-duplicatesp-equal (strip-cars frame))
;;          (abs-separate frame)
;;          (mv-nth 1 (collapse frame))
;;          (atom (frame-val->path (cdr (assoc-equal 0 frame))))
;;          (subsetp-equal (abs-addrs (frame->root frame))
;;                         (frame-addrs-root (frame->frame frame))))
;;     (abs-complete
;;      (abs-file->contents$inline
;;       (mv-nth 0
;;               (abs-find-file (partial-collapse frame path)
;;                              path)))))
;;    :hints
;;    (("Goal"
;;      :do-not-induct t
;;      :in-theory
;;      (disable
;;       abs-mkdir-correctness-lemma-158
;;       abs-find-file-src-correctness-2
;;       abs-mkdir-correctness-lemma-86)
;;      :use
;;      (:instance
;;       abs-find-file-src-correctness-2
;;       (frame (partial-collapse frame path))))
;;     ("subgoal 2"
;;      :use
;;      (:instance
;;       (:rewrite abs-find-file-of-put-assoc-lemma-4)
;;       (path path)
;;       (frame (partial-collapse frame path))))
;;     ("Subgoal 1" :use
;;      collapse-seq-of-partial-seq-this-is-partial-collapse))))

(defthm strip-cars-of-hifat-file-alist-fix-lemma-1
  (implies (and (not (null x))
                (set-equiv (strip-cars alist)
                           (remove-duplicates-equal l)))
           (iff (member-equal x l)
                (consp (assoc-equal x alist))))
  :hints (("goal" :do-not-induct t
           :in-theory (disable member-of-strip-cars)
           :use member-of-strip-cars))
  :rule-classes
  ((:rewrite
    :corollary
    (implies (and (case-split (not (null x)))
                  (equal (strip-cars alist)
                         (remove-duplicates-equal l)))
             (iff (member-equal x l)
                  (consp (assoc-equal x alist)))))))

(defthm
  strip-cars-of-hifat-file-alist-fix
  (equal (strip-cars (hifat-file-alist-fix fs))
         (remove-duplicates-equal (fat32-filename-list-fix (strip-cars fs))))
  :hints (("goal" :in-theory (enable hifat-file-alist-fix))))

(defthm hifat-equiv-implies-set-equiv-strip-cars-1-lemma-1
  (implies (and (member-equal a x) (null (car a)))
           (member-equal nil (strip-cars x))))

(defthm hifat-equiv-implies-set-equiv-strip-cars-1-lemma-2
  (implies (hifat-subsetp fs1 fs2)
           (subsetp-equal (strip-cars fs1)
                          (strip-cars fs2)))
  :hints (("goal" :in-theory (enable hifat-subsetp))))

(defthm
  hifat-equiv-implies-set-equiv-strip-cars-1
  (implies (hifat-equiv fs1 fs2)
           (set-equiv (fat32-filename-list-fix (strip-cars fs1))
                      (fat32-filename-list-fix (strip-cars fs2))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (hifat-equiv set-equiv)
                    (hifat-equiv-implies-set-equiv-strip-cars-1-lemma-2))
    :use ((:instance hifat-equiv-implies-set-equiv-strip-cars-1-lemma-2
                     (fs1 (hifat-file-alist-fix fs1))
                     (fs2 (hifat-file-alist-fix fs2)))
          (:instance hifat-equiv-implies-set-equiv-strip-cars-1-lemma-2
                     (fs2 (hifat-file-alist-fix fs1))
                     (fs1 (hifat-file-alist-fix fs2))))))
  :rule-classes :congruence)

(defund abs-opendir (frame path dir-stream-table)
  (declare
   (xargs
    :guard (and (fat32-filename-list-p path)
                (frame-p frame)
                (consp (assoc-equal 0 frame))
                (dir-stream-table-p dir-stream-table))
    :guard-debug t
    :guard-hints
    (("Goal"
      :use
      (:theorem
       (implies
        (m1-directory-file-p (mv-nth 0
                                     (abs-find-file (partial-collapse frame path)
                                                    path)))
        (m1-file-alist-p
         (m1-file->contents (mv-nth 0
                                    (abs-find-file (partial-collapse frame path)
                                                   path))))))))))
  (b* ((dir-stream-table
        (mbe :exec dir-stream-table :logic (dir-stream-table-fix dir-stream-table)))
       (frame (partial-collapse frame path))
       ((mv file errno)
        (abs-find-file frame path))
       ((unless (equal errno 0))
        (mv 0 dir-stream-table *enoent* frame))
       ((unless (m1-directory-file-p file))
        (mv 0 dir-stream-table *enotdir* frame))
       (dir-stream-table-index
        (find-new-index (strip-cars dir-stream-table))))
    (mv
     dir-stream-table-index
     (cons
      (cons dir-stream-table-index
            (make-dir-stream
             :file-list
             (<<-sort
              (strip-cars (m1-file->contents file)))))
      dir-stream-table)
     0
     frame)))

(defthm
  abs-opendir-correctness-1
  (implies (good-frame-p frame)
           (collapse-equiv (mv-nth 3
                                   (abs-opendir frame path dir-stream-table))
                           frame))
  :hints (("goal" :do-not-induct t
           :in-theory (enable good-frame-p
                              abs-opendir collapse-equiv))))

(defthm
  abs-opendir-correctness-lemma-1
  (implies
   (and
    (mv-nth 1 (collapse frame))
    (not (frame-val->path (cdr (assoc-equal 0 frame))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-separate frame)
    (subsetp-equal (abs-addrs (frame->root frame))
                   (frame-addrs-root (frame->frame frame)))
    (m1-directory-file-p (mv-nth 0
                                 (hifat-find-file (mv-nth 0 (collapse frame))
                                                  path))))
   (m1-directory-file-p
    (mv-nth '0
            (hifat-find-file (mv-nth '0
                                     (collapse (partial-collapse frame path)))
                             path))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable abs-opendir
                              hifat-opendir good-frame-p))))

(defthm
  abs-opendir-correctness-lemma-2
  (implies
   (and
    (mv-nth 1 (collapse frame))
    (not (frame-val->path (cdr (assoc-equal 0 frame))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-separate frame)
    (subsetp-equal (abs-addrs (frame->root frame))
                   (frame-addrs-root (frame->frame frame)))
    (m1-directory-file-p (mv-nth 0
                                 (hifat-find-file (mv-nth 0 (collapse frame))
                                                  path))))
   (set-equiv
    (strip-cars
     (m1-file->contents
      (mv-nth
       0
       (hifat-find-file (mv-nth 0
                                (collapse (partial-collapse frame path)))
                        path))))
    (strip-cars
     (m1-file->contents (mv-nth 0
                                (hifat-find-file (mv-nth 0 (collapse frame))
                                                 path))))))
  :hints
  (("goal"
    :in-theory (disable hifat-equiv-implies-set-equiv-strip-cars-1)
    :do-not-induct t
    :use
    (:instance
     hifat-equiv-implies-set-equiv-strip-cars-1
     (fs1
      (m1-file->contents
       (mv-nth
        0
        (hifat-find-file (mv-nth 0
                                 (collapse (partial-collapse frame path)))
                         path))))
     (fs2
      (m1-file->contents (mv-nth 0
                                 (hifat-find-file (mv-nth 0 (collapse frame))
                                                  path))))))))

(defthm
  abs-opendir-correctness-lemma-3
  (implies
   (and
    (mv-nth 1 (collapse frame))
    (not (frame-val->path (cdr (assoc-equal 0 frame))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-separate frame)
    (subsetp-equal (abs-addrs (frame->root frame))
                   (frame-addrs-root (frame->frame frame)))
    (m1-directory-file-p (mv-nth 0
                                 (hifat-find-file (mv-nth 0 (collapse frame))
                                                  path))))
   (equal
    (<<-sort
     (strip-cars
      (m1-file->contents
       (mv-nth
        0
        (hifat-find-file (mv-nth 0
                                 (collapse (partial-collapse frame path)))
                         path)))))
    (<<-sort
     (strip-cars
      (m1-file->contents (mv-nth 0
                                 (hifat-find-file (mv-nth 0 (collapse frame))
                                                  path)))))))
  :hints
  (("goal"
    :in-theory (disable common-<<-sort-for-perms)
    :do-not-induct t
    :use
    (:instance
     common-<<-sort-for-perms
     (x
      (strip-cars
       (m1-file->contents
        (mv-nth
         0
         (hifat-find-file (mv-nth 0
                                  (collapse (partial-collapse frame path)))
                          path)))))
     (y
      (strip-cars
       (m1-file->contents (mv-nth 0
                                  (hifat-find-file (mv-nth 0 (collapse frame))
                                                   path)))))))))

(defthmd
  abs-opendir-correctness-2
  (implies
   (good-frame-p frame)
   (b*
       (((mv fs &) (collapse frame)))
     (and
      (equal (mv-nth 0 (abs-opendir frame path dir-stream-table))
             (mv-nth 0 (hifat-opendir fs path dir-stream-table)))
      (equal (mv-nth 1 (abs-opendir frame path dir-stream-table))
             (mv-nth 1 (hifat-opendir fs path dir-stream-table)))
      (equal (mv-nth 2 (abs-opendir frame path dir-stream-table))
             (mv-nth 2 (hifat-opendir fs path dir-stream-table))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (enable abs-opendir hifat-opendir good-frame-p))))

(defund abs-readdir (dirp dir-stream-table)
  (hifat-readdir dirp dir-stream-table))

(defund abs-closedir (dirp dir-stream-table)
  (hifat-closedir dirp dir-stream-table))

(encapsulate
  ()

  (local (include-book "arithmetic-3/top" :dir :system))

  (defund
    tar-len-encode-helper (len n)
    (declare (xargs :guard (and (natp len) (natp n))))
    (if
        (zp n)
        nil
      (cons (code-char (+ (mod len 8) (char-code #\0)))
            (tar-len-encode-helper (floor len 8) (- n 1))))))

(defthm
  character-listp-of-tar-len-encode-helper
  (character-listp (tar-len-encode-helper len n))
  :hints (("goal" :in-theory (enable tar-len-encode-helper))))

(defund tar-len-encode (len)
  ;; It would be folly to stipulate that the length has to be less than 8^11,
  ;; and then keep struggling with every new guard proof.
  (declare (xargs :guard (natp len)
                  :guard-hints (("goal" :in-theory (e/d(
                                                        tar-len-encode-helper)
                                                       ((:rewrite revappend-removal)))) )))
  (coerce (revappend (tar-len-encode-helper len 11) (list (code-char 0)))
          'string))

;; Redundant with the definition in test/tar-writer.lisp - please update both
;; if necessary.
(defund
  tar-header-block (path len typeflag)
  (declare
   (xargs :guard (and (characterp typeflag)
                      (stringp path)
                      (>= 100 (length path))
                      (natp len))
          :guard-hints
          (("goal" :in-theory (e/d
                               (string-listp)
                               (make-list-ac-removal))))))
  (let ((path (mbe :exec path
                       :logic (str-fix path))))
       (concatenate
        'string
        path
        (coerce (make-list (- 124 (length path))
                           :initial-element (code-char 0))
                'string)
        (tar-len-encode len)
        (coerce (make-list (- 155 136)
                           :initial-element (code-char 0))
                'string)
        (string (mbe :exec typeflag
                     :logic (char-fix typeflag)))
        (coerce (make-list (- 512 156)
                           :initial-element (code-char 0))
                'string))))

;; This is defined in tar-stuff.lisp.
(defconst *tar-regtype* #\0)
(defconst *tar-dirtype* #\5)

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defund hifat-tar-reg-file-string (fs path)
    (declare (xargs :guard (and (stringp path) (m1-file-alist-p fs)
                                (hifat-no-dups-p fs) (<= (length path) 100))
                    :guard-debug t
                    :guard-hints (("Goal" :in-theory (e/d
                                                      (string-listp)
                                                      (MAKE-LIST-AC-REMOVAL))))))
    (b*
        ((fat32-path (path-to-fat32-path (coerce path 'list)))
         ((unless (fat32-filename-list-p fat32-path)) "")
         ((mv val & &) (hifat-lstat fs fat32-path))
         (file-length (struct-stat->st_size val))
         ((mv fd-table file-table fd &)
          (hifat-open fat32-path nil nil))
         ((unless (>= fd 0)) "")
         ((mv contents & &)
          (hifat-pread
           fd file-length 0 fs fd-table file-table))
         (len (length contents))
         (first-block
          (tar-header-block path len *tar-regtype*)))
      (concatenate
       'string
       first-block
       contents
       (coerce
        (make-list
         (- (* 512 (ceiling len 512)) len) :initial-element
         (code-char 0))
        'string)))))

;; Path is not needed as an argument! This is the recursive part only.
(defund
  hifat-get-names-from-dirp
  (dirp dir-stream-table)
  (declare
   (xargs
    :measure
    (len
     (dir-stream->file-list
      (cdr
       (assoc-equal (nfix dirp)
                    (dir-stream-table-fix dir-stream-table)))))
    :hints (("goal" :in-theory (enable hifat-readdir)))
    :guard (and (natp dirp) (dir-stream-table-p dir-stream-table))))
  (b*
      (((mv name errno dir-stream-table)
        (hifat-readdir dirp dir-stream-table))
       ((when (or (equal errno *ebadf*)
                  (equal name *empty-fat32-name*)))
        (mv nil dir-stream-table))
       ((mv tail dir-stream-table)
        (hifat-get-names-from-dirp dirp dir-stream-table)))
    (mv (list* name tail) dir-stream-table)))

(defthm fat32-filename-list-p-of-hifat-get-names-from-dirp
  (fat32-filename-list-p
   (mv-nth 0
           (hifat-get-names-from-dirp dirp dir-stream-table)))
  :hints (("goal" :in-theory (enable hifat-get-names-from-dirp
                                     hifat-readdir))))

(defthm dir-stream-table-p-of-hifat-get-names-from-dirp
  (dir-stream-table-p
   (mv-nth 1
           (hifat-get-names-from-dirp dirp dir-stream-table)))
  :hints (("goal" :in-theory (enable hifat-get-names-from-dirp
                                     hifat-readdir))))

(include-book "hifat-entry-count")

;; Move later.
(defthm character-listp-of-fat32-name-to-name
  (character-listp (fat32-name-to-name character-list)))
(defthm natp-of-hifat-opendir
  (natp (mv-nth 0
                (hifat-opendir fs path dir-stream-table)))
  :hints (("goal" :in-theory (enable hifat-opendir)))
  :rule-classes :type-prescription)

;; Making a recursive function to do tar can get really annoying because in
;; theory we could hit directory cycles and just keep traversing deeper and
;; deeper into the tree. It's important for proof purposes that we induct on
;; the pathnames, keeping the fs the same and accessing its inside parts only
;; through system calls.
;;
;; The way this proof is going to look is, we'll have to do one real
;; partial collapse, and possibly a few more later which won't have any
;; effect. But the one partial collapse will bring the whole directory into one
;; variable, and then effectively all lookups will just be lookups inside that
;; thing.
;;
;; Always gotta remember, though, that indiscriminate use of hifat-find-file will
;; be incorrect for looking up the contents of a directory because that
;; function will not work for looking up a root directory!
;; Anyway, to return to the induction scheme, it will be needed to make
;; something like a max path length and stop when we get there...
(encapsulate
  ()

  (local (in-theory (disable
                     hifat-close hifat-open hifat-pread)))

  (defthm
    natp-of-hifat-pread
    (natp
     (mv-nth 2
             (hifat-pread fd count offset fs fd-table file-table)))
    :hints (("goal" :in-theory (enable hifat-pread)))
    :rule-classes :type-prescription)

  (defund
    hifat-tar-name-list-string
    (fs path name-list fd-table file-table dir-stream-table entry-count)
    (declare
     (xargs
      :guard (and
              (m1-file-alist-p fs)
              (hifat-no-dups-p fs)
              (fat32-filename-list-p path)
              (natp entry-count)
              (fat32-filename-list-p name-list)
              (file-table-p file-table)
              (fd-table-p fd-table)
              (dir-stream-table-p dir-stream-table))
      :measure (nfix entry-count)
      :verify-guards nil))
    (b*
        ((fd-table (mbe :exec fd-table :logic (fd-table-fix fd-table)))
         (file-table (mbe :exec file-table :logic (file-table-fix file-table)))
         (dir-stream-table (mbe :exec dir-stream-table
                                :logic (dir-stream-table-fix dir-stream-table)))
         ((unless (and (consp name-list)
                       (not (zp entry-count))))
          (mv "" fd-table file-table))
         (head (car name-list))
         (head-path
          (append path (list head)))
         ((mv st & &) (hifat-lstat fs head-path))
         (len (struct-stat->st_size st))
         ((mv fd-table file-table fd &)
          (hifat-open head-path
                      fd-table file-table))
         ((unless (>= fd 0)) (mv "" fd-table file-table))
         ((mv & & pread-error-code)
          (hifat-pread
           fd len 0 fs fd-table file-table))
         ((mv fd-table file-table &) (hifat-close fd fd-table file-table))
         ((unless (and (<= (len (fat32-path-to-path head-path)) 100)))
          (mv "" fd-table file-table))
         (head-string
          (hifat-tar-reg-file-string fs (implode (fat32-path-to-path head-path))))
         ((when (zp pread-error-code))
          (b*
              (((mv tail-string fd-table file-table)
                (hifat-tar-name-list-string fs
                                            head-path
                                            (cdr name-list)
                                            fd-table file-table
                                            dir-stream-table
                                            (- entry-count 1))))
            (mv
             (concatenate
              'string
              head-string
              tail-string)
             fd-table file-table)))
         ((mv dirp dir-stream-table &)
          (hifat-opendir fs head-path dir-stream-table))
         ((mv names dir-stream-table)
          (hifat-get-names-from-dirp dirp dir-stream-table))
         ((mv & dir-stream-table) (hifat-closedir dirp dir-stream-table))
         ((mv head-string fd-table file-table)
          (hifat-tar-name-list-string fs
                                      (append path (list))
                                      names
                                      fd-table file-table
                                      dir-stream-table
                                      (- entry-count 1)))
         ((mv tail-string fd-table file-table)
          (hifat-tar-name-list-string fs
                                      path
                                      (cdr name-list)
                                      fd-table file-table
                                      dir-stream-table
                                      (- entry-count 1))))
      (mv
       (concatenate
        'string
        (tar-header-block
         (implode (fat32-path-to-path head-path))
         0 *tar-dirtype*)
        head-string tail-string)
       fd-table file-table)))

  (defthm
    fd-table-p-of-hifat-tar-name-list-string
    (fd-table-p
     (mv-nth 1
             (hifat-tar-name-list-string fs path name-list fd-table file-table
                                         dir-stream-table entry-count)))
    :hints
    (("goal" :in-theory (e/d (hifat-tar-name-list-string)
                             (append append-of-cons)))))

  (defthm
    stringp-of-hifat-tar-name-list-string
    (stringp
     (mv-nth 0
             (hifat-tar-name-list-string fs path name-list fd-table file-table
                                         dir-stream-table entry-count)))
    :hints
    (("goal" :in-theory (e/d (hifat-tar-name-list-string)
                             (append append-of-cons))))
    :rule-classes :type-prescription)

  (defthm
    file-table-p-of-hifat-tar-name-list-string
    (file-table-p
     (mv-nth 2
             (hifat-tar-name-list-string fs path name-list fd-table file-table
                                         dir-stream-table entry-count)))
    :hints
    (("goal" :in-theory (e/d (hifat-tar-name-list-string)
                             (append append-of-cons)))))

  (verify-guards
    hifat-tar-name-list-string
    :guard-debug t :otf-flg t
    :hints (("GOal" :in-theory (e/d (hifat-tar-name-list-string)
                                    (append append-of-cons))
                   :do-not-induct t))))
