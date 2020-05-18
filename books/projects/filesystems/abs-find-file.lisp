;  abs-find-file.lisp                                   Mihir Mehta

(in-package "ACL2")

(include-book "abstract-separate")
(local (include-book "std/lists/prefixp" :dir :system))

(local
 (in-theory (disable (:definition true-listp)
                     (:definition string-listp)
                     (:definition integer-listp)
                     (:definition acl2-number-listp)
                     (:rewrite nat-listp-of-remove)
                     (:definition rational-listp)
                     (:rewrite take-fewer-of-take-more)
                     (:rewrite take-when-atom)
                     (:rewrite take-of-take-split)
                     (:rewrite take-more-of-take-fewer)
                     (:rewrite remove-assoc-of-put-assoc))))

(local
 (in-theory
  (disable
   (:rewrite partial-collapse-correctness-lemma-29)
   (:rewrite partial-collapse-correctness-lemma-21)
   (:type-prescription abs-fs-fix-of-put-assoc-equal-lemma-3)
   (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
   (:rewrite collapse-congruence-lemma-4)
   (:rewrite abs-addrs-of-ctx-app-1-lemma-2)
   (:rewrite partial-collapse-correctness-lemma-23)
   (:rewrite absfat-subsetp-transitivity-lemma-8)
   (:rewrite collapse-congruence-lemma-2)
   (:rewrite absfat-equiv-of-ctx-app-lemma-8)
   (:rewrite abs-addrs-of-ctx-app-2-lemma-8)
   (:rewrite abs-separate-correctness-1-lemma-19)
   (:rewrite abs-separate-correctness-1-lemma-38)
   (:rewrite final-val-of-collapse-this-lemma-7)
   (:rewrite
    partial-collapse-correctness-lemma-20)
   (:rewrite
    final-val-of-collapse-this-lemma-6 . 1)
   (:rewrite m1-file-alist-p-when-subsetp-equal)
   (:rewrite
    m1-file-alist-p-of-final-val-seq-lemma-3)
   (:rewrite final-val-of-collapse-this-lemma-2)
   (:rewrite collapse-congruence-lemma-5)
   (:rewrite
    abs-file-alist-p-correctness-1-lemma-1)
   (:rewrite
    abs-find-file-helper-of-collapse-lemma-3)
   (:rewrite
    partial-collapse-correctness-lemma-106)
   (:rewrite
    abs-fs-fix-of-put-assoc-equal-lemma-2))))

(defund abs-find-file-helper (fs pathname)
  (declare (xargs :guard (and (abs-file-alist-p fs)
                              (fat32-filename-list-p pathname))
                  :measure (acl2-count pathname)))
  (b*
      ((fs (abs-fs-fix fs))
       ((unless (consp pathname))
        (mv (make-abs-file) *enoent*))
       (name (mbe :logic (fat32-filename-fix (car pathname))
                  :exec (car pathname)))
       (alist-elem (abs-assoc name fs))
       ((unless (consp alist-elem))
        (mv (make-abs-file) *enoent*))
       ((when (abs-directory-file-p (cdr alist-elem)))
        (if (atom (cdr pathname))
            (mv (cdr alist-elem) 0)
          (abs-find-file-helper (abs-file->contents (cdr alist-elem))
                                (cdr pathname))))
       ((unless (atom (cdr pathname)))
        (mv (make-abs-file) *enotdir*)))
    (mv (cdr alist-elem) 0)))

(defthm
  natp-of-abs-find-file-helper
  (natp (mv-nth 1 (abs-find-file-helper fs pathname)))
  :hints (("goal" :in-theory (enable abs-find-file-helper)))
  :rule-classes :type-prescription)

(defthm abs-find-file-helper-of-fat32-filename-list-fix
  (equal (abs-find-file-helper fs (fat32-filename-list-fix pathname))
         (abs-find-file-helper fs pathname))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defcong
  fat32-filename-list-equiv
  equal (abs-find-file-helper fs pathname)
  2
  :hints
  (("goal"
    :in-theory
    (disable abs-find-file-helper-of-fat32-filename-list-fix)
    :use
    ((:instance abs-find-file-helper-of-fat32-filename-list-fix
                (pathname pathname-equiv))
     abs-find-file-helper-of-fat32-filename-list-fix))))

(defthm abs-find-file-helper-of-abs-fs-fix
  (equal (abs-find-file-helper (abs-fs-fix fs)
                               pathname)
         (abs-find-file-helper fs pathname))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defund
  abs-find-file (frame pathname)
  (declare
   (xargs :guard (and (frame-p frame)
                      (fat32-filename-list-p pathname))))
  (b*
      (((when (atom frame))
        (mv (make-abs-file) *enoent*))
       (pathname (mbe :exec pathname
                      :logic (fat32-filename-list-fix pathname)))
       ((unless (prefixp (frame-val->path (cdar frame))
                         pathname))
        (abs-find-file (cdr frame) pathname))
       ((mv file error-code)
        (abs-find-file-helper
         (frame-val->dir (cdar frame))
         (nthcdr (len (frame-val->path (cdar frame)))
                 pathname)))
       ((when (not (equal error-code *enoent*)))
        (mv file error-code)))
    (abs-find-file (cdr frame) pathname)))

(defthm natp-of-abs-find-file
  (natp (mv-nth 1 (abs-find-file frame pathname)))
  :hints (("goal" :in-theory (enable abs-find-file)))
  :rule-classes :type-prescription)

(encapsulate
  ()

  (local
   (defthmd abs-find-file-of-fat32-filename-list-fix
     (equal (abs-find-file frame
                           (fat32-filename-list-fix pathname))
            (abs-find-file frame pathname))
     :hints (("goal" :in-theory (enable abs-find-file)))))

  (defcong
    fat32-filename-list-equiv
    equal (abs-find-file frame pathname)
    2
    :hints
    (("goal"
      :use ((:instance abs-find-file-of-fat32-filename-list-fix
                       (pathname pathname-equiv))
            abs-find-file-of-fat32-filename-list-fix)))))

(defthmd abs-find-file-of-true-list-fix
  (equal (abs-find-file (true-list-fix frame)
                        pathname)
         (abs-find-file frame pathname))
  :hints (("goal" :in-theory (enable abs-find-file))))

(defcong
  list-equiv
  equal (abs-find-file frame pathname)
  1
  :hints
  (("goal" :use ((:instance abs-find-file-of-true-list-fix
                            (frame frame-equiv))
                 abs-find-file-of-true-list-fix))))

(defthm
  abs-find-file-helper-when-m1-file-alist-p-lemma-1
  (implies (and (abs-fs-p fs) (abs-complete fs))
           (equal (hifat-file-alist-fix fs) fs))
  :hints
  (("goal" :in-theory (disable (:rewrite abs-no-dups-p-when-m1-file-alist-p))
    :use ((:rewrite abs-no-dups-p-when-m1-file-alist-p)))))

(defthm
  abs-find-file-helper-when-m1-file-alist-p-lemma-2
  (implies
   (and
    (m1-directory-file-p (cdr (assoc-equal (fat32-filename-fix (car pathname))
                                           fs)))
    (abs-fs-p fs))
   (abs-fs-p
    (m1-file->contents (cdr (assoc-equal (fat32-filename-fix (car pathname))
                                         fs)))))
  :hints
  (("goal"
    :in-theory
    (disable (:rewrite abs-fs-p-of-abs-file->contents-of-cdr-of-assoc))
    :use (:instance (:rewrite abs-fs-p-of-abs-file->contents-of-cdr-of-assoc)
                    (name (fat32-filename-fix (car pathname)))))))

(defthm
  abs-find-file-helper-when-m1-file-alist-p
  (implies (abs-complete (abs-fs-fix fs))
           (equal (abs-find-file-helper fs pathname)
                  (hifat-find-file (abs-fs-fix fs)
                                   pathname)))
  :hints (("goal" :in-theory (enable abs-find-file-helper
                                     hifat-find-file m1-file-alist-p))))

(defthm
  abs-find-file-helper-of-ctx-app-lemma-1
  (implies
   (and (abs-fs-p abs-file-alist1)
        (abs-fs-p (append (remove-equal x abs-file-alist1)
                          abs-file-alist2))
        (integerp x)
        (not (equal (mv-nth 1
                            (abs-find-file-helper abs-file-alist1 pathname))
                    *enoent*)))
   (equal (abs-find-file-helper (append (remove-equal x abs-file-alist1)
                                        abs-file-alist2)
                                pathname)
          (abs-find-file-helper abs-file-alist1 pathname)))
  :hints
  (("goal" :do-not-induct t
    :expand (:free (abs-file-alist)
                   (abs-find-file-helper abs-file-alist pathname))
    :cases ((null (car pathname))))))

(defthmd abs-find-file-helper-of-ctx-app-lemma-4
  (implies (not (zp (mv-nth 1 (abs-find-file-helper fs pathname))))
           (equal (abs-find-file-helper fs pathname)
                  (mv (abs-file-fix nil)
                      (mv-nth 1 (abs-find-file-helper fs pathname)))))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm
  abs-find-file-helper-of-ctx-app-lemma-6
  (implies
   (and
    (abs-fs-p abs-file-alist2)
    (abs-fs-p abs-file-alist1)
    (integerp x)
    (not (intersectp-equal (remove-equal nil (strip-cars abs-file-alist1))
                           (remove-equal nil (strip-cars abs-file-alist2))))
    (equal (mv-nth 1
                   (abs-find-file-helper abs-file-alist1 pathname))
           2))
   (equal (abs-find-file-helper (append (remove-equal x abs-file-alist1)
                                        abs-file-alist2)
                                pathname)
          (abs-find-file-helper abs-file-alist2 pathname)))
  :hints
  (("goal"
    :do-not-induct t
    :use
    (:instance (:rewrite abs-find-file-helper-of-ctx-app-lemma-4)
               (pathname (cdr pathname))
               (fs (abs-file->contents
                    (cdr (assoc-equal (fat32-filename-fix (car pathname))
                                      abs-file-alist1)))))
    :expand ((:free (abs-file-alist)
                    (abs-find-file-helper abs-file-alist pathname))))))

(defthm
  abs-find-file-helper-of-ctx-app
  (implies
   (and (ctx-app-ok abs-file-alist1 x x-path)
        (abs-fs-p (ctx-app abs-file-alist1
                           abs-file-alist2 x x-path)))
   (equal
    (abs-find-file-helper (ctx-app abs-file-alist1
                                   abs-file-alist2 x x-path)
                          pathname)
    (cond
     ((and (equal (mv-nth 1
                          (abs-find-file-helper abs-file-alist1 pathname))
                  0)
           (prefixp (fat32-filename-list-fix pathname)
                    (fat32-filename-list-fix x-path)))
      (mv
       (abs-file
        (abs-file->dir-ent
         (mv-nth 0
                 (abs-find-file-helper abs-file-alist1 pathname)))
        (ctx-app
         (abs-file->contents
          (mv-nth 0
                  (abs-find-file-helper abs-file-alist1 pathname)))
         abs-file-alist2
         x (nthcdr (len pathname) x-path)))
       0))
     ((and (equal (mv-nth 1
                          (abs-find-file-helper abs-file-alist1 pathname))
                  *enoent*)
           (prefixp (fat32-filename-list-fix x-path)
                    (fat32-filename-list-fix pathname)))
      (abs-find-file-helper abs-file-alist2
                            (nthcdr (len x-path) pathname)))
     (t (abs-find-file-helper abs-file-alist1 pathname)))))
  :hints
  (("goal"
    :in-theory
    (e/d (prefixp abs-find-file-helper
                  ctx-app ctx-app-ok names-at addrs-at)
         (nfix (:rewrite abs-addrs-of-ctx-app-1-lemma-4)
               (:rewrite remove-when-absent)
               (:rewrite abs-find-file-helper-when-m1-file-alist-p)
               (:rewrite m1-file-contents-p-correctness-1)
               (:rewrite abs-file-contents-p-when-m1-file-contents-p)
               (:rewrite abs-addrs-of-ctx-app)
               (:rewrite abs-file-alist-p-correctness-1)
               (:definition no-duplicatesp-equal)))
    :induct
    (mv (mv-nth 0
                (abs-find-file-helper (ctx-app abs-file-alist1
                                               abs-file-alist2 x x-path)
                                      pathname))
        (fat32-filename-list-prefixp x-path pathname)
        (ctx-app abs-file-alist1
                 abs-file-alist2 x x-path)))))

(defthm
  abs-find-file-of-remove-assoc-1
  (implies
   (and
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (or
     (not (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                   (fat32-filename-list-fix pathname)))
     (equal
      (mv-nth 1
              (abs-find-file-helper
               (frame-val->dir (cdr (assoc-equal x frame)))
               (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                       pathname)))
      *enoent*)))
   (equal (abs-find-file (remove-assoc-equal x frame)
                         pathname)
          (abs-find-file frame pathname)))
  :hints (("goal" :in-theory (enable abs-find-file))))

(defthm
  abs-find-file-of-remove-assoc-2
  (implies
   (and
    (frame-p (remove-assoc-equal x frame))
    (no-duplicatesp-equal (strip-cars (remove-assoc-equal x frame)))
    (or
     (not
      (prefixp
       (frame-val->path (cdr (assoc-equal y (remove-assoc-equal x frame))))
       (fat32-filename-list-fix pathname)))
     (equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal y (remove-assoc-equal x frame))))
        (nthcdr (len (frame-val->path
                      (cdr (assoc-equal y (remove-assoc-equal x frame)))))
                pathname)))
      *enoent*)))
   (equal (abs-find-file (remove-assoc-equal x (remove-assoc-equal y frame))
                         pathname)
          (abs-find-file (remove-assoc-equal x frame)
                         pathname)))
  :hints (("goal" :in-theory (disable abs-find-file-of-remove-assoc-1)
           :use (:instance abs-find-file-of-remove-assoc-1 (x y)
                           (frame (remove-assoc-equal x frame))))))

(defthmd abs-find-file-of-put-assoc-lemma-1
  (equal (abs-find-file-helper fs pathname)
         (mv (mv-nth 0 (abs-find-file-helper fs pathname))
             (mv-nth 1 (abs-find-file-helper fs pathname))))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm
  abs-find-file-of-put-assoc-lemma-2
  (equal
   (list (mv-nth 0
                 (abs-find-file-helper (frame-val->dir val)
                                       (nthcdr (len (frame-val->path val))
                                               pathname)))
         (mv-nth 1
                 (abs-find-file-helper (frame-val->dir val)
                                       (nthcdr (len (frame-val->path val))
                                               pathname))))
   (abs-find-file-helper (frame-val->dir val)
                         (nthcdr (len (frame-val->path val))
                                 pathname)))
  :hints
  (("goal" :use (:instance (:rewrite abs-find-file-of-put-assoc-lemma-1)
                           (pathname (nthcdr (len (frame-val->path val))
                                             pathname))
                           (fs (frame-val->dir val))))))

(defthm
  abs-find-file-of-put-assoc-lemma-3
  (implies
   (and
    (equal
     (mv-nth
      1
      (abs-find-file-helper (frame-val->dir val)
                            (nthcdr (len (frame-val->path val))
                                    pathname)))
     2)
    (equal const (mv (abs-file-fix nil) *enoent*)))
   (iff
    (equal
     const
     (abs-find-file-helper (frame-val->dir val)
                           (nthcdr (len (frame-val->path val))
                                   pathname)))
    t))
  :hints
  (("goal"
    :use
    (:instance (:rewrite abs-find-file-helper-of-ctx-app-lemma-4)
               (pathname (nthcdr (len (frame-val->path val))
                                 pathname))
               (fs (frame-val->dir val))))))

(defthmd
  abs-find-file-of-put-assoc-lemma-4
  (implies (not (zp (mv-nth 1 (abs-find-file frame pathname))))
           (equal (abs-find-file frame pathname)
                  (mv (abs-file-fix nil)
                      (mv-nth 1 (abs-find-file frame pathname)))))
  :hints
  (("goal" :in-theory (enable abs-find-file))
   ("subgoal *1/2"
    :use
    (:instance (:rewrite abs-find-file-helper-of-ctx-app-lemma-4)
               (pathname (nthcdr (len (frame-val->path (cdr (car frame))))
                                 pathname))
               (fs (frame-val->dir (cdr (car frame))))))))

(defthm
  abs-find-file-of-put-assoc-lemma-5
  (implies (and (equal (mv-nth 1 (abs-find-file (cdr frame) pathname))
                       2)
                (equal const (mv (abs-file-fix nil) *enoent*)))
           (iff (equal (abs-find-file (cdr frame) pathname)
                       const)
                t))
  :hints
  (("goal" :use (:instance (:rewrite abs-find-file-of-put-assoc-lemma-4)
                           (frame (cdr frame))))))

;; Could be important...
(defthm
  abs-find-file-of-put-assoc-lemma-6
  (implies
   (and (frame-p frame)
        (no-duplicatesp-equal (strip-cars frame))
        (consp (assoc-equal x frame))
        (equal (mv-nth 1
                       (abs-find-file (remove-assoc-equal x frame)
                                      pathname))
               *enoent*))
   (equal (abs-find-file frame pathname)
          (if (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                       (fat32-filename-list-fix pathname))
              (abs-find-file-helper
               (frame-val->dir (cdr (assoc-equal x frame)))
               (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                       pathname))
            (mv (abs-file-fix nil) *enoent*))))
  :hints (("goal" :in-theory (enable abs-find-file))))

;; What do you know, this theorem is useless except in one place where it has
;; to be manually invoked anyway...
(defthmd
  abs-find-file-of-put-assoc
  (implies
   (and
    (frame-p (put-assoc-equal name val frame))
    (no-duplicatesp-equal (strip-cars (put-assoc-equal name val frame)))
    (or
     (not (prefixp (frame-val->path val)
                   (fat32-filename-list-fix pathname)))
     (equal (mv-nth 1
                    (abs-find-file-helper (frame-val->dir val)
                                          (nthcdr (len (frame-val->path val))
                                                  pathname)))
            *enoent*)
     (equal (mv-nth 1
                    (abs-find-file (remove-assoc-equal name frame)
                                   pathname))
            *enoent*)))
   (equal
    (abs-find-file (put-assoc-equal name val frame)
                   pathname)
    (if
     (and
      (prefixp (frame-val->path val)
               (fat32-filename-list-fix pathname))
      (not
       (equal
        (mv-nth 1
                (abs-find-file-helper (frame-val->dir val)
                                      (nthcdr (len (frame-val->path val))
                                              pathname)))
        *enoent*)))
     (abs-find-file-helper (frame-val->dir val)
                           (nthcdr (len (frame-val->path val))
                                   pathname))
     (abs-find-file (remove-assoc-equal name frame)
                    pathname))))
  :hints (("goal" :in-theory (enable abs-find-file))))

(defthm
  abs-find-file-of-frame-with-root
  (equal (abs-find-file (frame-with-root root frame)
                        pathname)
         (if (equal (mv-nth 1
                            (abs-find-file-helper (abs-fs-fix root)
                                                  pathname))
                    *enoent*)
             (abs-find-file frame pathname)
           (abs-find-file-helper (abs-fs-fix root)
                                 pathname)))
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d (abs-find-file frame-with-root)
                    ((:rewrite abs-find-file-of-put-assoc-lemma-1)))
    :use (:instance (:rewrite abs-find-file-of-put-assoc-lemma-1)
                    (fs (abs-fs-fix root))))))

(local
 (defund abs-find-file-alt
   (frame indices pathname)
   (b* (((when (atom indices))
         (mv (make-abs-file) *enoent*))
        (pathname (fat32-filename-list-fix pathname))
        ((unless (prefixp (frame-val->path (cdr (assoc-equal (car indices) frame)))
                          pathname))
         (abs-find-file-alt frame (cdr indices) pathname))
        ((mv file error-code)
         (abs-find-file-helper
          (frame-val->dir (cdr (assoc-equal (car indices) frame)))
          (nthcdr (len (frame-val->path (cdr (assoc-equal (car indices) frame))))
                  pathname)))
        ((when (not (equal error-code *enoent*)))
         (mv file error-code)))
     (abs-find-file-alt frame (cdr indices) pathname))))

(local
 (defthm abs-find-file-alt-of-fat32-filename-list-fix
   (equal (abs-find-file-alt frame indices
                             (fat32-filename-list-fix pathname))
          (abs-find-file-alt frame indices pathname))
   :hints (("goal" :in-theory (enable abs-find-file-alt)))))

(local
 (defcong
   fat32-filename-list-equiv equal
   (abs-find-file-alt frame indices pathname)
   3
   :hints
   (("goal"
     :in-theory
     (disable abs-find-file-alt-of-fat32-filename-list-fix)
     :use
     ((:instance abs-find-file-alt-of-fat32-filename-list-fix
                 (pathname pathname-equiv))
      abs-find-file-alt-of-fat32-filename-list-fix)))))

(local
 (defthm abs-find-file-alt-correctness-1-lemma-1
   (implies (not (member-equal (caar frame) indices))
            (equal (abs-find-file-alt (cdr frame)
                                      indices pathname)
                   (abs-find-file-alt frame indices pathname)))
   :hints (("goal" :in-theory (enable abs-find-file-alt)))))

(local
 (defthm
   abs-find-file-alt-correctness-1
   (implies (no-duplicatesp-equal (strip-cars frame))
            (equal (abs-find-file-alt frame (strip-cars frame)
                                      pathname)
                   (abs-find-file frame pathname)))
   :hints (("goal" :in-theory (enable abs-find-file-alt abs-find-file)))))

(local
 (defthm
   abs-find-file-alt-correctness-2
   (implies (no-duplicatesp-equal (strip-cars frame))
            (equal (abs-find-file-alt frame
                                      (remove-equal x (strip-cars frame))
                                      pathname)
                   (abs-find-file (remove-assoc-equal x frame)
                                  pathname)))
   :hints (("goal" :in-theory (enable abs-find-file-alt abs-find-file)))))

(defund abs-enotdir-witness (fs pathname)
  (declare (xargs :measure (len pathname)))
  (b* (((when (atom pathname)) pathname)
       ((mv file errno)
        (abs-find-file-helper fs pathname))
       ((when (and (zp errno) (m1-regular-file-p file))) pathname))
    (abs-enotdir-witness fs (butlast pathname 1))))

(defthm true-listp-of-abs-enotdir-witness
  (implies (true-listp pathname)
           (true-listp (abs-enotdir-witness fs pathname)))
  :hints (("Goal" :in-theory (enable abs-enotdir-witness)))
  :rule-classes :type-prescription)

(defthm prefixp-of-abs-enotdir-witness
  (prefixp (abs-enotdir-witness fs pathname)
           pathname)
  :hints (("goal" :in-theory (enable abs-enotdir-witness))))

(defthm len-of-abs-enotdir-witness
  (<= (len (abs-enotdir-witness fs pathname))
      (len pathname))
  :hints (("goal" :in-theory (enable abs-enotdir-witness)))
  :rule-classes :linear)

(defthm
  abs-enotdir-witness-correctness-1-lemma-1
  (implies
   (< 1 (len pathname))
   (not (equal (abs-enotdir-witness fs
                                    (take (+ -1 (len pathname)) pathname))
               pathname)))
  :hints (("goal" :use (:instance len-of-abs-enotdir-witness
                                  (pathname (take (+ -1 (len pathname))
                                                  pathname))))))

(defthm
  abs-enotdir-witness-correctness-1
  (implies (equal (mv-nth 1 (abs-find-file-helper fs pathname))
                  *enotdir*)
           (not (equal (abs-enotdir-witness fs pathname)
                       pathname)))
  :hints (("goal" :in-theory (enable abs-enotdir-witness
                                     abs-find-file-helper))))

(defthm
  abs-enotdir-witness-correctness-2-lemma-1
  (implies
   (and
    (not
     (equal
      (mv-nth 1
              (abs-find-file-helper fs
                                    (take (+ -1 (len pathname)) pathname)))
      *enotdir*))
    (equal (mv-nth 1 (abs-find-file-helper fs pathname))
           *enotdir*))
   (and
    (m1-regular-file-p
     (mv-nth 0
             (abs-find-file-helper fs
                                   (take (+ -1 (len pathname)) pathname))))
    (equal
     (mv-nth 1
             (abs-find-file-helper fs
                                   (take (+ -1 (len pathname)) pathname)))
     0)))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm
  abs-enotdir-witness-correctness-2
  (implies
   (equal (mv-nth 1 (abs-find-file-helper fs pathname))
          *enotdir*)
   (and
    (m1-regular-file-p
     (mv-nth 0
             (abs-find-file-helper fs (abs-enotdir-witness fs pathname))))
    (equal
     (mv-nth 1
             (abs-find-file-helper fs (abs-enotdir-witness fs pathname)))
     0)
    (consp (abs-enotdir-witness fs pathname))))
  :hints (("goal" :in-theory (enable abs-enotdir-witness
                                     abs-find-file-helper))))

(defthm fat32-filename-list-p-of-abs-enotdir-witness
  (implies
   (fat32-filename-list-p pathname)
   (fat32-filename-list-p (abs-enotdir-witness fs pathname)))
  :hints (("goal" :in-theory (enable abs-enotdir-witness))))

(defthm
  abs-find-file-helper-of-collapse-lemma-1
  (implies (m1-regular-file-p (mv-nth 0 (abs-find-file-helper root pathname)))
           (not (equal (mv-nth 1 (abs-find-file-helper root pathname))
                       2)))
  :hints
  (("goal"
    :use (:instance (:rewrite abs-find-file-helper-of-ctx-app-lemma-4)
                    (fs root)))))

;; Important!
;; It's a pain in the neck that we have to stipulate x-path has at least one
;; element in it... but it's unavoidable. This is really a fundamental
;; difference between abs-find-file-helper and ctx-app.
(defthm
  abs-find-file-helper-of-collapse-lemma-2
  (implies (and (consp x-path)
                (ctx-app-ok abs-file-alist1 x x-path))
           (and (equal (mv-nth 1
                               (abs-find-file-helper abs-file-alist1 x-path))
                       0)
                (abs-directory-file-p
                 (mv-nth 0
                         (abs-find-file-helper abs-file-alist1 x-path)))))
  :hints
  (("goal" :in-theory (e/d (abs-find-file-helper ctx-app ctx-app-ok addrs-at)
                           (nfix))
    :induct (abs-find-file-helper abs-file-alist1 x-path)
    :expand (ctx-app abs-file-alist1
                     abs-file-alist2 x x-path))))

(defthmd
  abs-find-file-helper-of-collapse-lemma-4
  (implies
   (and (consp pathname)
        (prefixp (fat32-filename-list-fix pathname)
                 (fat32-filename-list-fix x-path))
        (zp (mv-nth 1 (abs-find-file-helper fs x-path))))
   (and
    (equal
     (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs pathname)))
     (or (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs x-path)))
         (not (fat32-filename-list-equiv pathname x-path))))
    (equal (mv-nth 1 (abs-find-file-helper fs pathname))
           0)))
  :hints (("goal" :in-theory (enable abs-find-file-helper prefixp)
           :induct (mv (mv-nth 1 (abs-find-file-helper fs pathname))
                       (fat32-filename-list-prefixp pathname x-path))
           :expand (abs-find-file-helper fs x-path))))

(defthm
  abs-find-file-helper-of-collapse-lemma-5
  (implies
   (and (ctx-app-ok root x
                    (frame-val->path (cdr (assoc-equal x frame))))
        (prefixp (fat32-filename-list-fix pathname)
                 (frame-val->path (cdr (assoc-equal x frame)))))
   (not (m1-regular-file-p (mv-nth 0
                                   (abs-find-file-helper root pathname)))))
  :hints
  (("goal"
    :in-theory (e/d (abs-find-file-helper)
                    ((:rewrite abs-find-file-helper-of-collapse-lemma-2)))
    :use ((:instance (:rewrite abs-find-file-helper-of-collapse-lemma-2)
                     (x x)
                     (x-path (frame-val->path (cdr (assoc-equal x frame))))
                     (abs-file-alist1 root))
          (:instance (:rewrite abs-find-file-helper-of-collapse-lemma-4)
                     (x-path (frame-val->path (cdr (assoc-equal x frame))))
                     (fs root))))))

(defthm
  abs-find-file-helper-of-collapse-1
  (implies
   (and (frame-p (frame->frame frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (abs-separate (frame->frame frame))
        (dist-names (frame->root frame)
                    nil (frame->frame frame))
        (m1-regular-file-p (mv-nth 0
                                   (abs-find-file-helper (frame->root frame)
                                                         pathname))))
   (equal (abs-find-file-helper (mv-nth 0 (collapse frame))
                                pathname)
          (abs-find-file-helper (frame->root frame)
                                pathname)))
  :hints (("goal" :in-theory (enable collapse dist-names collapse-this)
           :induct (collapse frame)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (frame-p (frame->frame frame))
          (no-duplicatesp-equal (strip-cars (frame->frame frame)))
          (abs-separate (frame->frame frame))
          (dist-names (frame->root frame)
                      nil (frame->frame frame))
          (m1-regular-file-p (mv-nth 0
                                     (abs-find-file-helper (frame->root frame)
                                                           pathname)))
          (m1-file-alist-p (mv-nth 0 (collapse frame)))
          (hifat-no-dups-p (mv-nth 0 (collapse frame))))
     (equal (hifat-find-file (mv-nth 0 (collapse frame))
                             pathname)
            (abs-find-file-helper (frame->root frame)
                                  pathname))))))

;; This seems useless according to accumulated-persistence.
(defthmd
  abs-find-file-helper-of-collapse-2
  (implies (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (frame-p (frame->frame frame))
                (abs-separate (frame->frame frame))
                (dist-names (frame->root frame)
                            nil (frame->frame frame))
                (not (equal (mv-nth 1
                                    (abs-find-file-helper (frame->root frame)
                                                          pathname))
                            0))
                (not (equal (mv-nth 1
                                    (abs-find-file-helper (frame->root frame)
                                                          pathname))
                            *enoent*)))
           (equal (abs-find-file-helper (mv-nth 0 (collapse frame))
                                        pathname)
                  (abs-find-file-helper (frame->root frame)
                                        pathname)))
  :hints (("goal" :in-theory (enable collapse dist-names collapse-this)
           :induct (collapse frame))))

;; The somewhat weaker conclusion, in terms of (mv-nth 1 (abs-find-file ...))
;; rather than (abs-find-file ...), is because of the possibility that the file
;; returned is a directory with holes, which gets filled in during collapse.
(defthm
  abs-find-file-helper-of-collapse-3
  (implies (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (frame-p (frame->frame frame))
                (abs-separate (frame->frame frame))
                (dist-names (frame->root frame)
                            nil (frame->frame frame))
                (not (equal (mv-nth 1
                                    (abs-find-file-helper (frame->root frame)
                                                          pathname))
                            *enoent*)))
           (equal (mv-nth 1
                          (abs-find-file-helper (mv-nth 0 (collapse frame))
                                                pathname))
                  (mv-nth 1
                          (abs-find-file-helper (frame->root frame)
                                                pathname))))
  :hints (("goal" :in-theory (enable collapse dist-names collapse-this)
           :induct (collapse frame)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
          (frame-p (frame->frame frame))
          (abs-separate (frame->frame frame))
          (dist-names (frame->root frame)
                      nil (frame->frame frame))
          (not (equal (mv-nth 1
                              (abs-find-file-helper (frame->root frame)
                                                    pathname))
                      *enoent*))
          (m1-file-alist-p (mv-nth 0 (collapse frame)))
          (hifat-no-dups-p (mv-nth 0 (collapse frame))))
     (equal (mv-nth 1
                    (hifat-find-file (mv-nth 0 (collapse frame))
                                     pathname))
            (mv-nth 1
                    (abs-find-file-helper (frame->root frame)
                                          pathname)))))))

(defthm
  abs-find-file-correctness-1-lemma-1
  (implies
   (and (not (consp (abs-addrs (abs-fs-fix root))))
        (m1-regular-file-p (mv-nth 0
                                   (abs-find-file (frame-with-root root nil)
                                                  pathname))))
   (equal (mv-nth 0
                  (abs-find-file (frame-with-root root nil)
                                 pathname))
          (mv-nth 0
                  (hifat-find-file (abs-fs-fix root)
                                   pathname))))
  :hints (("goal" :in-theory (enable frame-with-root
                                     abs-find-file abs-separate))))

(defthmd
  abs-find-file-correctness-1-lemma-2
  (implies
   (and
    (not (intersectp-equal
          (abs-addrs (cdr abs-file-alist))
          (abs-addrs (abs-file->contents (cdr (car abs-file-alist))))))
    (member-equal x (abs-addrs (cdr abs-file-alist))))
   (not (member-equal
         x
         (abs-addrs (abs-file->contents (cdr (car abs-file-alist)))))))
  :hints (("goal" :in-theory (enable intersectp-member))))

;; It seems this is useless...
(defthmd
  abs-find-file-correctness-1-lemma-4
  (implies
   (and (abs-directory-file-p val)
        (abs-directory-file-p (cdr (assoc-equal name abs-file-alist)))
        (no-duplicatesp-equal (abs-addrs abs-file-alist)))
   (iff
    (member-equal x
                  (abs-addrs (put-assoc-equal name val abs-file-alist)))
    (or
     (member-equal x (abs-addrs (abs-file->contents val)))
     (and
      (member-equal x (abs-addrs abs-file-alist))
      (not
       (member-equal
        x
        (abs-addrs
         (abs-file->contents (cdr (assoc-equal name abs-file-alist))))))))))
  :hints (("goal" :induct (put-assoc-equal name val abs-file-alist)
           :in-theory (enable abs-addrs))))

(defthm
  abs-find-file-correctness-1-lemma-28
  (implies
   (and
    (equal (mv-nth 1
                   (abs-find-file-helper (ctx-app abs-file-alist1
                                                  abs-file-alist2 x x-path)
                                         pathname))
           *enoent*)
    (prefixp (fat32-filename-list-fix x-path)
             (fat32-filename-list-fix pathname))
    (ctx-app-ok abs-file-alist1 x x-path)
    (not (intersectp-equal (names-at abs-file-alist2 nil)
                           (names-at abs-file-alist1 x-path))))
   (and (equal (mv-nth 1
                       (abs-find-file-helper abs-file-alist1 pathname))
               *enoent*)
        (equal (mv-nth 1
                       (abs-find-file-helper abs-file-alist2
                                             (nthcdr (len x-path) pathname)))
               *enoent*))))

;; Should the corollary be a type-prescription?
(defthm
  abs-find-file-correctness-1-lemma-13
  (implies
   (and
    (not (consp (assoc-equal (fat32-filename-fix (car pathname))
                             abs-file-alist1)))
    (abs-fs-p (append (remove-equal x abs-file-alist1)
                      abs-file-alist2))
    (abs-fs-p abs-file-alist2)
    (equal
     (mv-nth 1
             (abs-find-file-helper (append (remove-equal x abs-file-alist1)
                                           abs-file-alist2)
                                   pathname))
     0))
   (equal (mv-nth 1
                  (abs-find-file-helper abs-file-alist2 pathname))
          0))
  :hints
  (("goal"
    :do-not-induct t
    :expand ((abs-find-file-helper abs-file-alist2 pathname)
             (abs-find-file-helper (append (remove-equal x abs-file-alist1)
                                           abs-file-alist2)
                                   pathname))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (not (consp (assoc-equal (fat32-filename-fix (car pathname))
                                   abs-file-alist1)))
          (abs-fs-p (append (remove-equal x abs-file-alist1)
                            abs-file-alist2))
          (abs-fs-p abs-file-alist2)
          (not (equal (mv-nth 1
                              (abs-find-file-helper abs-file-alist2 pathname))
                      0)))
     (not
      (equal
       (mv-nth 1
               (abs-find-file-helper (append (remove-equal x abs-file-alist1)
                                             abs-file-alist2)
                                     pathname))
       0))))))

(defthm
  abs-find-file-correctness-1-lemma-8
  (implies
   (and
    (abs-directory-file-p
     (cdr (assoc-equal (fat32-filename-fix (car pathname))
                       (abs-fs-fix abs-file-alist1))))
    (abs-fs-p (append (remove-equal x abs-file-alist1)
                      abs-file-alist2))
    (abs-fs-p abs-file-alist1)
    (integerp x)
    (equal
     (mv-nth 1
             (abs-find-file-helper abs-file-alist1 pathname))
     *enoent*))
   (equal (mv-nth 1
                  (abs-find-file-helper
                   (append (remove-equal x abs-file-alist1)
                           abs-file-alist2)
                   pathname))
          *enoent*))
  :hints
  (("goal"
    :do-not-induct t
    :expand
    ((abs-find-file-helper abs-file-alist1 pathname)
     (abs-find-file-helper
      (append (remove-equal x abs-file-alist1)
              abs-file-alist2)
      pathname)))))

(defthm abs-find-file-correctness-1-lemma-6
  (implies (and (fat32-filename-list-p pathname)
                (< n (len pathname))
                (zp (mv-nth 1
                            (abs-find-file-helper (abs-fs-fix fs)
                                                  pathname))))
           (member-equal (nth n pathname)
                         (names-at fs (take n pathname))))
  :hints (("goal" :in-theory (enable names-at
                                     abs-find-file-helper))))

(defthm
  abs-find-file-correctness-1-lemma-9
  (implies
   (and
    (not (prefixp (fat32-filename-list-fix relpath)
                  (frame-val->path (cdr (assoc-equal x frame)))))
    (prefixp (fat32-filename-list-fix relpath)
             (fat32-filename-list-fix pathname))
    (equal (mv-nth 1
                   (abs-find-file-helper (abs-fs-fix dir)
                                         (nthcdr (len relpath) pathname)))
           0)
    (equal
     (mv-nth 1
             (abs-find-file-helper
              (frame-val->dir (cdr (assoc-equal x frame)))
              (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                      pathname)))
     0)
    (prefixp (frame-val->path (cdr (assoc-equal x frame)))
             (fat32-filename-list-fix pathname)))
   (intersectp-equal
    (names-at dir nil)
    (names-at (frame-val->dir (cdr (assoc-equal x frame)))
              (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                      relpath))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (e/d (names-at abs-find-file-helper take-of-nthcdr)
         (abs-find-file-correctness-1-lemma-6 nth-of-fat32-filename-list-fix
                                              len-when-prefixp
                                              (:rewrite member-of-remove)
                                              (:rewrite car-of-nthcdr)
                                              (:rewrite nth-of-nthcdr)
                                              (:rewrite take-when-prefixp)))
    :use
    ((:instance
      (:rewrite intersectp-member)
      (y (names-at (frame-val->dir (cdr (assoc-equal x frame)))
                   (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                           relpath)))
      (x (names-at dir nil))
      (a (nth (len relpath)
              (fat32-filename-list-fix pathname))))
     (:instance abs-find-file-correctness-1-lemma-6
                (fs (abs-fs-fix dir))
                (pathname (nthcdr (len relpath)
                                  (fat32-filename-list-fix pathname)))
                (n 0))
     (:instance
      abs-find-file-correctness-1-lemma-6
      (fs (frame-val->dir (cdr (assoc-equal x frame))))
      (pathname (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                        (fat32-filename-list-fix pathname)))
      (n (+ (len relpath)
            (- (len (frame-val->path (cdr (assoc-equal x frame))))))))
     (:instance len-when-prefixp
                (x (frame-val->path (cdr (assoc-equal x frame))))
                (y (fat32-filename-list-fix relpath)))
     (:instance (:rewrite car-of-nthcdr)
                (x (fat32-filename-list-fix pathname))
                (i (len relpath)))
     (:instance
      (:rewrite nth-of-nthcdr)
      (x (fat32-filename-list-fix pathname))
      (m (len (frame-val->path (cdr (assoc-equal x frame)))))
      (n (+ (len relpath)
            (- (len (frame-val->path (cdr (assoc-equal x frame))))))))
     (:instance (:rewrite take-when-prefixp)
                (y (fat32-filename-list-fix pathname))
                (x (fat32-filename-list-fix relpath)))))))

(defthm
  abs-find-file-correctness-1-lemma-33
  (implies (and (abs-fs-p fs)
                (fat32-filename-list-p pathname)
                (not (equal (mv-nth 1 (abs-find-file-helper fs pathname))
                            *enoent*)))
           (member-equal (car pathname)
                         (remove-equal nil (strip-cars fs))))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm
  abs-find-file-correctness-1-lemma-37
  (implies
   (and (abs-fs-p fs)
        (fat32-filename-list-p pathname)
        (not (equal (mv-nth 1
                            (abs-find-file-helper fs (nthcdr n pathname)))
                    *enoent*)))
   (member-equal (nth n pathname)
                 (remove-equal nil (strip-cars fs))))
  :hints (("goal" :do-not-induct t
           :in-theory (disable abs-find-file-correctness-1-lemma-33
                               nth-of-nthcdr)
           :use ((:instance abs-find-file-correctness-1-lemma-33
                            (pathname (nthcdr n pathname)))
                 (:instance nth-of-nthcdr (n 0)
                            (m n)
                            (x pathname))))))

(defthmd
  abs-find-file-correctness-1-lemma-20
  (implies (and (< (+ (- (len relpath))
                      (len (frame-val->path (cdr (assoc-equal x frame)))))
                   0)
                (prefixp relpath pathname)
                (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                         pathname))
           (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                    relpath))
  :hints
  (("goal"
    :in-theory
    (e/d (names-at take-of-nthcdr abs-find-file-helper)
         (abs-find-file-correctness-1-lemma-6 member-of-remove))
    :cases ((prefixp relpath
                     (frame-val->path (cdr (assoc-equal x frame))))))))

(defthm
  abs-find-file-correctness-1-lemma-21
  (implies
   (and
    (not (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                  (fat32-filename-list-fix relpath)))
    (prefixp (fat32-filename-list-fix relpath)
             (fat32-filename-list-fix pathname))
    (equal (mv-nth 1
                   (abs-find-file-helper dir (nthcdr (len relpath) pathname)))
           0)
    (equal
     (mv-nth 1
             (abs-find-file-helper
              (frame-val->dir (cdr (assoc-equal x frame)))
              (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                      pathname)))
     0)
    (prefixp (frame-val->path (cdr (assoc-equal x frame)))
             (fat32-filename-list-fix pathname)))
   (intersectp-equal
    (names-at (frame-val->dir (cdr (assoc-equal x frame)))
              nil)
    (names-at
     dir
     (nthcdr (len relpath)
             (frame-val->path (cdr (assoc-equal x frame)))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (names-at take-of-nthcdr abs-find-file-helper
                              abs-find-file-correctness-1-lemma-20)
                    (abs-find-file-correctness-1-lemma-6
                     member-of-remove
                     (:rewrite nth-of-fat32-filename-list-fix)
                     (:rewrite take-when-prefixp)
                     (:rewrite nth-of-nthcdr)))
    :use
    ((:instance
      abs-find-file-correctness-1-lemma-6
      (fs (frame-val->dir (cdr (assoc-equal x frame))))
      (pathname (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                        (fat32-filename-list-fix pathname)))
      (n 0))
     (:instance abs-find-file-correctness-1-lemma-6
                (fs (abs-fs-fix dir))
                (pathname (nthcdr (len relpath)
                                  (fat32-filename-list-fix pathname)))
                (n (+ (len (frame-val->path (cdr (assoc-equal x frame))))
                      (- (len relpath)))))
     (:theorem (equal (+ (len relpath)
                         (- (len relpath))
                         (len (frame-val->path (cdr (assoc-equal x frame)))))
                      (len (frame-val->path (cdr (assoc-equal x frame))))))
     (:instance
      intersectp-member
      (a (nth (len (frame-val->path (cdr (assoc-equal x frame))))
              (fat32-filename-list-fix pathname)))
      (y (names-at
          dir
          (nthcdr (len relpath)
                  (frame-val->path (cdr (assoc-equal x frame))))))
      (x (remove-equal
          nil
          (strip-cars (frame-val->dir (cdr (assoc-equal x frame)))))))
     (:instance (:rewrite nth-of-nthcdr)
                (x (fat32-filename-list-fix pathname))
                (m (len relpath))
                (n (+ (- (len relpath))
                      (len (frame-val->path (cdr (assoc-equal x frame)))))))
     (:instance (:rewrite take-when-prefixp)
                (y (fat32-filename-list-fix pathname))
                (x (frame-val->path (cdr (assoc-equal x frame)))))))))

(defthmd
  abs-find-file-correctness-1-lemma-29
  (implies
   (and
    (not (intersectp-equal
          (names-at (frame-val->dir (cdr (assoc-equal x frame)))
                    nil)
          (names-at
           dir
           (nthcdr (len relpath)
                   (frame-val->path (cdr (assoc-equal x frame)))))))
    (prefixp (fat32-filename-list-fix relpath)
             (fat32-filename-list-fix pathname))
    (equal (mv-nth 1
                   (abs-find-file-helper (abs-fs-fix dir)
                                         (nthcdr (len relpath) pathname)))
           0)
    (equal
     (mv-nth 1
             (abs-find-file-helper
              (frame-val->dir (cdr (assoc-equal x frame)))
              (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                      pathname)))
     0)
    (prefixp (frame-val->path (cdr (assoc-equal x frame)))
             (fat32-filename-list-fix pathname)))
   (intersectp-equal
    (names-at dir nil)
    (names-at
     (frame-val->dir (cdr (assoc-equal x frame)))
     (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
             relpath))))
  :hints
  (("goal"
    :do-not-induct t
    :cases ((and (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                          (fat32-filename-list-fix relpath))
                 (prefixp (fat32-filename-list-fix relpath)
                          (frame-val->path (cdr (assoc-equal x frame))))))
    :in-theory
    (e/d (list-equiv nthcdr-when->=-n-len-l)
         (nth-of-fat32-filename-list-fix (:rewrite prefixp-when-equal-lengths)
                                         member-of-remove))
    :use
    ((:instance (:rewrite prefixp-when-equal-lengths)
                (y (frame-val->path (cdr (assoc-equal x frame))))
                (x (fat32-filename-list-fix relpath)))
     (:instance
      (:rewrite intersectp-member)
      (a (nth (len (frame-val->path (cdr (assoc-equal x frame))))
              (fat32-filename-list-fix pathname)))
      (y (names-at
          dir
          (nthcdr (len relpath)
                  (frame-val->path (cdr (assoc-equal x frame))))))
      (x (names-at (frame-val->dir (cdr (assoc-equal x frame)))
                   nil)))))
   ("subgoal 1.2"
    :expand (names-at (frame-val->dir (cdr (assoc-equal x frame)))
                      nil))
   ("subgoal 1.1" :expand (names-at dir nil))))

;; This theorem is kinda inadequate. It would be better to prove that the
;; subterm of the LHS, which is proved to be non-zero, is actually
;; *enoent*. But that's not possible, because proving that it cannot be
;; *ENOTDIR* (necessary) can't be done without the additional knowledge of
;; collapsibility...
(defthm
  abs-find-file-correctness-1-lemma-22
  (implies
   (and
    (equal (mv-nth 1
                   (abs-find-file-helper dir (nthcdr (len relpath) pathname)))
           0)
    (dist-names dir
                relpath frame)
    (consp (assoc-equal x frame))
    (prefixp (fat32-filename-list-fix relpath)
             (fat32-filename-list-fix pathname))
    (prefixp (frame-val->path (cdr (assoc-equal x frame)))
             (fat32-filename-list-fix pathname)))
   (not
    (equal
     (mv-nth 1
             (abs-find-file-helper
              (frame-val->dir (cdr (assoc-equal x frame)))
              (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                      pathname)))
     0)))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d
                       (abs-find-file-correctness-1-lemma-29)
                       (abs-separate-correctness-1-lemma-19
                        abs-separate-of-put-assoc-lemma-1))
           :use ((:instance abs-separate-correctness-1-lemma-19
                            (dir (abs-fs-fix dir)))
                 (:instance abs-separate-of-put-assoc-lemma-1
                            (dir (abs-fs-fix dir))))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and
      (equal (mv-nth 1
                     (abs-find-file-helper dir (nthcdr (len relpath) pathname)))
             0)
      (dist-names dir
                  relpath frame)
      (consp (assoc-equal x frame))
      (prefixp (fat32-filename-list-fix relpath)
               (fat32-filename-list-fix pathname))
      (prefixp (frame-val->path (cdr (assoc-equal x frame)))
               (fat32-filename-list-fix pathname))
      (equal (mv-nth 1 mv) 0))
     (not
      (equal
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal x frame)))
        (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                pathname))
       mv))))))

(defthm
  abs-find-file-correctness-1-lemma-24
  (implies
   (equal
    (mv-nth
     1
     (abs-find-file-helper (frame-val->dir (cdr (car frame)))
                           (nthcdr (len (frame-val->path (cdr (car frame))))
                                   pathname)))
    0)
   (equal
    (cons
     (mv-nth
      0
      (abs-find-file-helper (frame-val->dir (cdr (car frame)))
                            (nthcdr (len (frame-val->path (cdr (car frame))))
                                    pathname)))
     '(0))
    (abs-find-file-helper (frame-val->dir (cdr (car frame)))
                          (nthcdr (len (frame-val->path (cdr (car frame))))
                                  pathname))))
  :instructions (:promote (:dive 2)
                          (:rewrite abs-find-file-of-put-assoc-lemma-1)
                          :top (:dive 2 2 1)
                          :=
                          :top :s))

(defthmd
  abs-find-file-correctness-1-lemma-59
  (implies
   (and
    (consp (assoc-equal x frame))
    (equal (mv-nth 1 (abs-find-file frame pathname))
           0)
    (equal
     (mv-nth 1
             (abs-find-file-helper
              (frame-val->dir (cdr (assoc-equal x frame)))
              (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                      pathname)))
     0)
    (abs-separate frame)
    (prefixp (frame-val->path (cdr (assoc-equal x frame)))
             (fat32-filename-list-fix pathname)))
   (equal (abs-find-file-helper
           (frame-val->dir (cdr (assoc-equal x frame)))
           (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                   pathname))
          (abs-find-file frame pathname)))
  :hints (("goal" :in-theory (enable abs-find-file abs-separate)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and
      (consp (assoc-equal x frame))
      (equal (mv-nth 1 (abs-find-file frame pathname))
             0)
      (equal
       (mv-nth
        1
        (hifat-find-file
         (frame-val->dir (cdr (assoc-equal x frame)))
         (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                 pathname)))
       0)
      (abs-separate frame)
      (prefixp (frame-val->path (cdr (assoc-equal x frame)))
               (fat32-filename-list-fix pathname))
      (m1-file-alist-p (frame-val->dir (cdr (assoc-equal x frame))))
      (hifat-no-dups-p (frame-val->dir (cdr (assoc-equal x frame)))))
     (equal (hifat-find-file
             (frame-val->dir (cdr (assoc-equal x frame)))
             (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                     pathname))
            (abs-find-file frame pathname))))))

(defthm
  abs-find-file-correctness-1-lemma-5
  (implies
   (and
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))
             (fat32-filename-list-fix pathname))
    (< 0 (1st-complete frame))
    (ctx-app-ok root (1st-complete frame)
                (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                   frame))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (dist-names root nil frame)
    (equal
     (mv-nth
      1
      (abs-find-file-helper
       (ctx-app root
                (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                  frame)))
                (1st-complete frame)
                (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                   frame))))
       pathname))
     2))
   (equal
    (mv-nth
     1
     (hifat-find-file
      (frame-val->dir$inline (cdr (assoc-equal (1st-complete frame)
                                               frame)))
      (nthcdr
       (len (frame-val->path$inline (cdr (assoc-equal (1st-complete frame)
                                                      frame))))
       pathname)))
    *enoent*))
  :hints (("goal" :do-not-induct t)))

(defthm
  abs-find-file-correctness-1-lemma-14
  (implies
   (and
    (equal (mv-nth 1
                   (abs-find-file (frame-with-root root frame)
                                  pathname))
           0)
    (< 0 (1st-complete frame))
    (ctx-app-ok root (1st-complete frame)
                (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                   frame))))
    (equal
     (mv-nth
      1
      (abs-find-file
       (frame-with-root
        (ctx-app root
                 (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                 (1st-complete frame)
                 (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                    frame))))
        (remove-assoc-equal (1st-complete frame)
                            frame))
       pathname))
     0)
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-separate (frame-with-root root frame))
    (m1-regular-file-p (mv-nth 0
                               (abs-find-file (frame-with-root root frame)
                                              pathname))))
   (equal
    (mv-nth
     0
     (abs-find-file
      (frame-with-root
       (ctx-app root
                (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                  frame)))
                (1st-complete frame)
                (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                   frame))))
       (remove-assoc-equal (1st-complete frame)
                           frame))
      pathname))
    (mv-nth 0
            (abs-find-file (frame-with-root root frame)
                           pathname))))
  :hints
  (("goal" :in-theory (enable abs-find-file
                              (:rewrite abs-find-file-correctness-1-lemma-59
                                        . 2)
                              frame-with-root abs-separate)
    :do-not-induct t)))

;; Kinda general
(defthm
  abs-find-file-correctness-1-lemma-40
  (implies
   (and (not (equal (mv-nth 1 (hifat-find-file fs pathname))
                    0))
        (not (equal (mv-nth 1 (hifat-find-file fs pathname))
                    *enoent*)))
   (equal (mv-nth 1 (hifat-find-file fs pathname))
          *enotdir*))
  :hints (("goal" :in-theory (enable hifat-find-file)))
  :rule-classes
  (:rewrite
   (:type-prescription
    :corollary
    (natp (mv-nth 1 (hifat-find-file fs pathname))))))

;; Kinda general
(defthm
  abs-find-file-correctness-1-lemma-18
  (implies
   (and (not (equal (mv-nth 1 (abs-find-file-helper fs pathname))
                    0))
        (not (equal (mv-nth 1 (abs-find-file-helper fs pathname))
                    *enoent*)))
   (equal (mv-nth 1 (abs-find-file-helper fs pathname))
          *enotdir*))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm
  abs-find-file-correctness-1-lemma-23
  (implies
   (and (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                    frame)))
                 (fat32-filename-list-fix pathname))
        (equal (mv-nth 1 (abs-find-file-helper root pathname))
               0)
        (dist-names root nil frame))
   (equal
    (mv-nth
     1
     (abs-find-file-helper
      (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                        frame)))
      (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                      frame))))
              pathname)))
    *enoent*))
  :hints
  (("goal"
    :in-theory (e/d (abs-find-file-helper)
                    (abs-find-file-correctness-1-lemma-6
                     (:rewrite abs-find-file-correctness-1-lemma-18)))
    :do-not-induct t
    :cases
    ((equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                        frame))))
                pathname)))
      0)
     (equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                        frame))))
                pathname)))
      *enotdir*))
    :use
    ((:instance
      (:rewrite intersectp-member)
      (a
       (fat32-filename-fix
        (car
         (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                         frame))))
                 pathname))))
      (y (names-at
          (abs-fs-fix root)
          (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                             frame)))))
      (x (names-at
          (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame)))
          nil)))
     (:instance
      abs-find-file-correctness-1-lemma-6
      (fs (abs-fs-fix root))
      (n (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                 frame)))))
      (pathname (fat32-filename-list-fix pathname)))
     (:instance
      (:rewrite abs-find-file-correctness-1-lemma-18)
      (pathname
       (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                       frame))))
               pathname))
      (fs (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame))))))
    :expand
    (abs-find-file-helper
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                     frame))))
             pathname)))
   ("subgoal 2.2"
    :expand
    (names-at (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                frame)))
              nil))
   ("subgoal 2.1"
    :expand
    (names-at (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                frame)))
              nil))
   ("subgoal 1.2"
    :expand
    (names-at (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                frame)))
              nil))
   ("subgoal 1.1"
    :expand
    (names-at (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                frame)))
              nil))))

(defthm
  abs-find-file-correctness-1-lemma-30
  (implies
   (and (fat32-filename-list-p pathname2)
        (zp (mv-nth 1 (abs-find-file-helper fs pathname1)))
        (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs pathname1)))
        (equal (mv-nth 1 (abs-find-file-helper fs pathname2))
               *enotdir*)
        (prefixp pathname1 pathname2))
   (member-equal (nth (len pathname1) pathname2)
                 (names-at fs pathname1)))
  :hints (("goal" :in-theory (enable abs-find-file-helper
                                     names-at prefixp)
           :induct t
           :expand (names-at fs pathname1))))

(defthm
  abs-find-file-correctness-1-lemma-25
  (implies (and (fat32-filename-list-p pathname)
                (not (equal (mv-nth 1
                                    (abs-find-file-helper (abs-fs-fix fs)
                                                          pathname))
                            *enoent*)))
           (member-equal (car pathname)
                         (names-at fs nil)))
  :hints (("goal" :in-theory (e/d (names-at)
                                  (abs-find-file-correctness-1-lemma-33))
           :use (:instance abs-find-file-correctness-1-lemma-33
                           (fs (abs-fs-fix fs))))))

(defthmd
  abs-find-file-correctness-1-lemma-26
  (implies
   (and (fat32-filename-list-p pathname)
        (not (equal (mv-nth 1
                            (abs-find-file-helper (abs-fs-fix fs)
                                                  (nthcdr n pathname)))
                    *enoent*)))
   (member-equal (nth n pathname)
                 (names-at fs nil)))
  :hints (("goal" :in-theory (e/d (names-at)
                                  (abs-find-file-correctness-1-lemma-37))
           :use (:instance abs-find-file-correctness-1-lemma-37
                           (fs (abs-fs-fix fs))))))

(encapsulate
  ()

  (local
   (defthm
     lemma
     (implies
      (and
       (member-equal (car (fat32-filename-list-fix pathname))
                     (names-at root nil))
       (not (equal (mv-nth 1 (abs-find-file-helper root pathname))
                   0))
       (ctx-app-ok root (1st-complete frame)
                   (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                      frame))))
       (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                (fat32-filename-list-fix pathname))
       (not (equal (mv-nth 1 (abs-find-file-helper root pathname))
                   2)))
      (member-equal
       (nth (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                    frame))))
            (fat32-filename-list-fix pathname))
       (names-at root
                 (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                    frame))))))
     :hints
     (("goal"
       :do-not-induct t
       :in-theory (e/d (names-at abs-find-file-helper)
                       (nthcdr-of-fat32-filename-list-fix
                        nth-of-fat32-filename-list-fix
                        (:rewrite abs-find-file-correctness-1-lemma-33)))
       :cases ((consp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                         frame)))))))))

  (defthmd
    abs-find-file-correctness-1-lemma-7
    (implies
     (and
      (ctx-app-ok root (1st-complete frame)
                  (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                     frame))))
      (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                  frame)))
               (fat32-filename-list-fix pathname))
      (not (equal (mv-nth 1 (abs-find-file-helper (abs-fs-fix root) pathname))
                  2))
      (dist-names root nil frame))
     (equal
      (abs-find-file-helper
       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                         frame)))
       (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                       frame))))
               pathname))
      (mv (abs-file-fix nil) *enoent*)))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (e/d (abs-find-file-helper)
                      (nthcdr-of-fat32-filename-list-fix
                       nth-of-fat32-filename-list-fix
                       (:rewrite abs-find-file-correctness-1-lemma-25)))
      :use
      ((:instance
        (:rewrite abs-find-file-correctness-1-lemma-25)
        (fs (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                              frame))))
        (pathname
         (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                         frame))))
                 (fat32-filename-list-fix pathname))))
       (:instance (:rewrite abs-find-file-correctness-1-lemma-25)
                  (fs (abs-fs-fix root))
                  (pathname (fat32-filename-list-fix pathname)))
       (:instance
        (:rewrite intersectp-member)
        (a
         (car
          (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                          frame))))
                  (fat32-filename-list-fix pathname))))
        (y (names-at
            root
            (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                               frame)))))
        (x
         (names-at (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                     frame)))
                   nil))))
      :cases
      ((and
        (not
         (equal
          (mv-nth
           1
           (abs-find-file-helper
            (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                              frame)))
            (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                            frame))))
                    pathname)))
          2))
        (abs-file-alist-p (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                            frame))))
        (equal (mv-nth 1 (abs-find-file-helper root pathname))
               0))
       (and
        (not
         (equal
          (mv-nth
           1
           (abs-find-file-helper
            (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                              frame)))
            (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                            frame))))
                    pathname)))
          2))
        (abs-file-alist-p (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                            frame))))
        (not (equal (mv-nth 1 (abs-find-file-helper root pathname))
                    0))))))))

(defthm
  abs-find-file-correctness-1-lemma-11
  (implies
   (and (ctx-app-ok root (1st-complete frame)
                    (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                       frame))))
        (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                 (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                    frame)))))
   (abs-directory-file-p
    (mv-nth
     0
     (abs-find-file-helper root
                           (frame-val->path (cdr (assoc-equal x frame)))))))
  :hints
  (("goal"
    :in-theory (e/d (abs-find-file-helper)
                    ((:rewrite abs-find-file-helper-of-collapse-lemma-2)
                     (:rewrite abs-find-file-helper-of-collapse-lemma-4)))
    :use ((:instance
           (:rewrite abs-find-file-helper-of-collapse-lemma-4)
           (pathname (frame-val->path (cdr (assoc-equal x frame))))
           (fs root)
           (x-path (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                      frame)))))
          (:instance
           (:rewrite abs-find-file-helper-of-collapse-lemma-2)
           (x (1st-complete frame))
           (x-path (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                      frame))))
           (abs-file-alist1 root))))))

(defthm
  abs-find-file-correctness-1-lemma-16
  (implies
   (ctx-app-ok root (1st-complete frame)
               (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                  frame))))
   (abs-directory-file-p
    (mv-nth 0
            (abs-find-file-helper
             root
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))))))
  :hints
  (("goal"
    :in-theory (e/d (abs-find-file-helper)
                    ((:rewrite abs-find-file-helper-of-collapse-lemma-2)))
    :use ((:instance
           (:rewrite abs-find-file-helper-of-collapse-lemma-2)
           (x-path (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                      frame))))
           (abs-file-alist1 root)
           (x (1st-complete frame)))))))

(defthmd
  abs-find-file-correctness-1-lemma-49
  (implies
   (and (prefixp (fat32-filename-list-fix pathname)
                 (fat32-filename-list-fix x-path))
        (m1-regular-file-p (mv-nth 0 (abs-find-file-helper fs pathname)))
        (not (fat32-filename-list-equiv pathname x-path)))
   (equal (abs-find-file-helper fs x-path)
          (mv (abs-file-fix nil) *enotdir*)))
  :hints
  (("goal" :in-theory (enable fat32-filename-list-equiv
                              abs-find-file-helper
                              prefixp fat32-filename-list-fix)
    :induct (mv (mv-nth 0 (abs-find-file-helper fs pathname))
                (fat32-filename-list-prefixp pathname x-path)))))

(defthm
  abs-find-file-correctness-1-lemma-12
  (implies
   (and (equal (mv-nth 1 (abs-find-file frame pathname))
               *enoent*)
        (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                 (fat32-filename-list-fix pathname)))
   (equal (abs-find-file-helper
           (frame-val->dir (cdr (assoc-equal x frame)))
           (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                   pathname))
          (mv (abs-file-fix nil) *enoent*)))
  :hints (("goal" :in-theory (enable abs-find-file hifat-find-file))))

(defthm
  abs-find-file-correctness-1-lemma-3
  (implies
   (and
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (consp (assoc-equal (1st-complete frame)
                        frame))
    (equal
     (mv-nth
      1
      (abs-find-file
       (remove-assoc-equal (1st-complete frame)
                           frame)
       pathname))
     2))
   (equal
    (abs-find-file frame pathname)
    (if
        (prefixp
         (frame-val->path
          (cdr (assoc-equal (1st-complete frame)
                            frame)))
         (fat32-filename-list-fix pathname))
        (abs-find-file-helper
         (frame-val->dir
          (cdr (assoc-equal (1st-complete frame)
                            frame)))
         (nthcdr
          (len
           (frame-val->path
            (cdr (assoc-equal (1st-complete frame)
                              frame))))
          pathname))
      (mv (abs-file-fix nil) *enoent*))))
  :hints
  (("goal"
    :in-theory (disable abs-find-file-of-put-assoc-lemma-6)
    :use (:instance abs-find-file-of-put-assoc-lemma-6
                    (x (1st-complete frame))))))

(defthm
  abs-find-file-correctness-1-lemma-19
  (implies
   (and
    (fat32-filename-list-p pathname)
    (equal
     (mv-nth
      1
      (abs-find-file-helper
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame)))
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame))))))
     0)
    (abs-directory-file-p
     (mv-nth
      0
      (abs-find-file-helper
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame)))
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame)))))))
    (equal
     (mv-nth
      1
      (abs-find-file-helper
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame)))
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        pathname)))
     20))
   (not
    (prefixp
     (abs-enotdir-witness
      (frame-val->dir
       (cdr
        (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                       frame)))
                     frame)))
      (nthcdr
       (len
        (frame-val->path
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       frame))))
       pathname))
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                         frame)))))))
  :hints
  (("goal"
    :do-not-induct t
    :use
    (:instance
     abs-find-file-helper-of-collapse-lemma-4
     (pathname
      (abs-enotdir-witness
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame)))
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        pathname)))
     (fs
      (frame-val->dir
       (cdr
        (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                       frame)))
                     frame))))
     (x-path
      (nthcdr
       (len
        (frame-val->path
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       frame))))
       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                          frame)))))))))

(defthm
  abs-find-file-correctness-1-lemma-57
  (implies
   (and
    (fat32-filename-list-p pathname)
    (equal
     (mv-nth
      1
      (abs-find-file-helper
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame)))
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        pathname)))
     *enotdir*)
    (ctx-app-ok
     (frame-val->dir
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (1st-complete frame)
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                         frame))))))
   (not
    (prefixp
     (abs-enotdir-witness
      (frame-val->dir
       (cdr
        (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                       frame)))
                     frame)))
      (nthcdr
       (len
        (frame-val->path
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       frame))))
       pathname))
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                         frame)))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable abs-find-file-helper-of-collapse-lemma-2)
    :use
    (:instance
     abs-find-file-helper-of-collapse-lemma-2
     (x-path
      (nthcdr
       (len
        (frame-val->path
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       frame))))
       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                          frame)))))
     (x (1st-complete frame))
     (abs-file-alist1
      (frame-val->dir
       (cdr
        (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                       frame)))
                     frame))))))))

(defthmd
  abs-separate-correctness-1-lemma-41
  (implies
   (and
    (fat32-filename-list-p pathname)
    (equal
     (mv-nth
      1
      (abs-find-file-helper
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame)))
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        pathname)))
     *enotdir*)
    (prefixp
     (frame-val->path
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                        frame))))
    (prefixp
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                         frame))))
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (fat32-filename-list-fix pathname)))
    (not
     (prefixp
      (abs-enotdir-witness
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame)))
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        (fat32-filename-list-fix pathname)))
      (nthcdr
       (len
        (frame-val->path
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       frame))))
       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                          frame)))))))
   (member-equal
    (fat32-filename-fix
     (nth (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                  frame))))
          pathname))
    (names-at
     (frame-val->dir
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                         frame)))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (disable nth-when-prefixp
             (:rewrite abs-find-file-correctness-1-lemma-6)
             (:rewrite take-when-prefixp)
             prefixp-one-way-or-another
             (:rewrite abs-find-file-correctness-1-lemma-57))
    :use
    ((:instance
      nth-when-prefixp
      (y
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        (fat32-filename-list-fix pathname)))
      (n
       (+
        (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame))))
        (-
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                 frame)))))))
      (x
       (abs-enotdir-witness
        (frame-val->dir
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       frame)))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                 frame))))
         pathname))))
     (:instance
      (:rewrite abs-find-file-correctness-1-lemma-6)
      (fs
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (pathname
       (abs-enotdir-witness
        (frame-val->dir
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       frame)))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                 frame))))
         pathname)))
      (n
       (+
        (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame))))
        (-
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                 frame))))))))
     (:instance
      (:rewrite take-when-prefixp)
      (y
       (abs-enotdir-witness
        (frame-val->dir
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       frame)))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                 frame))))
         (fat32-filename-list-fix pathname))))
      (x
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame))))))
     (:instance
      prefixp-one-way-or-another
      (z
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        (fat32-filename-list-fix pathname)))
      (x
       (abs-enotdir-witness
        (frame-val->dir
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       frame)))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                 frame))))
         (fat32-filename-list-fix pathname))))
      (y
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame))))))))))

(defthmd
  abs-find-file-correctness-1-lemma-55
  (implies
   (and
    (not
     (member-equal
      (fat32-filename-fix
       (nth (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                    frame))))
            pathname))
      (names-at
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame)))
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame)))))))
    (<
     0
     (mv-nth
      1
      (abs-find-file-helper
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame)))
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        pathname))))
    (prefixp
     (frame-val->path
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                        frame))))
    (ctx-app-ok
     (frame-val->dir
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (1st-complete frame)
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                         frame)))))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))
             (fat32-filename-list-fix pathname)))
   (equal
    (abs-find-file-helper
     (frame-val->dir
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      pathname))
    (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (take-of-nthcdr abs-find-file-helper)
                    (nthcdr-of-fat32-filename-list-fix
                     abs-separate-correctness-1-lemma-14
                     (:rewrite abs-find-file-correctness-1-lemma-18)
                     (:rewrite abs-find-file-correctness-1-lemma-57)))
    :use
    ((:instance
      (:rewrite abs-find-file-correctness-1-lemma-18)
      (pathname
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        pathname))
      (fs
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame)))))
     (:instance (:rewrite abs-separate-correctness-1-lemma-41)
                (pathname (fat32-filename-list-fix pathname)))
     (:instance (:rewrite abs-find-file-correctness-1-lemma-57)
                (pathname (fat32-filename-list-fix pathname)))))))

(defthm
  abs-find-file-correctness-1-lemma-27
  (implies
   (and
    (not (equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                  frame)))
                (1st-complete frame)))
    (prefixp
     (frame-val->path
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                        frame))))
    (ctx-app-ok
     (frame-val->dir
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (1st-complete frame)
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                         frame)))))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))
             (fat32-filename-list-fix pathname))
    (abs-separate frame)
    (not
     (equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                        frame))))
                pathname)))
      *enoent*)))
   (equal
    (abs-find-file-helper
     (frame-val->dir
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      pathname))
    (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (take-of-nthcdr abs-find-file-helper
                                    abs-addrs-of-ctx-app-1-lemma-7)
                    (nthcdr-of-fat32-filename-list-fix
                     abs-separate-correctness-1-lemma-14
                     (:rewrite abs-find-file-correctness-1-lemma-6)))
    :use
    ((:instance abs-separate-correctness-1-lemma-14
                (x (1st-complete frame))
                (y (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                     frame)))))
     (:instance
      (:rewrite intersectp-member)
      (a
       (car
        (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                        frame))))
                (fat32-filename-list-fix pathname))))
      (y
       (names-at
        (frame-val->dir
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       frame)))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                 frame))))
         (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                            frame))))))
      (x (names-at (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                     frame)))
                   nil)))
     (:instance
      (:rewrite abs-find-file-correctness-1-lemma-6)
      (fs
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (pathname
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        (fat32-filename-list-fix pathname)))
      (n
       (+
        (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame))))
        (-
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                 frame))))))))
     (:instance
      (:rewrite abs-find-file-correctness-1-lemma-26)
      (fs (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame))))
      (pathname (fat32-filename-list-fix pathname))
      (n (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                 frame))))))
     (:instance (:rewrite abs-find-file-correctness-1-lemma-55)
                (pathname (fat32-filename-list-fix pathname)))))))

(defthm
  abs-find-file-correctness-1-lemma-46
  (implies
   (and
    (not (equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                  frame)))
                (1st-complete frame)))
    (prefixp
     (frame-val->path
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                        frame))))
    (ctx-app-ok
     (frame-val->dir
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (1st-complete frame)
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                         frame)))))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))
             (fat32-filename-list-fix pathname))
    (abs-separate frame)
    (not
     (equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       frame)))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                 frame))))
         pathname)))
      *enoent*)))
   (equal
    (abs-find-file-helper
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                     frame))))
             pathname))
    (mv (abs-file-fix nil) *enoent*)))
  :hints (("goal" :in-theory (disable abs-find-file-correctness-1-lemma-27)
           :use abs-find-file-correctness-1-lemma-27)))

(defthmd abs-find-file-correctness-1-lemma-31
  (equal (hifat-find-file fs pathname)
         (mv (mv-nth 0 (hifat-find-file fs pathname))
             (mv-nth 1 (hifat-find-file fs pathname))))
  :hints (("goal" :in-theory (enable hifat-find-file))))

(defthm
  abs-find-file-correctness-1-lemma-34
  (implies
   (and
    (not (equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                  frame)))
                (1st-complete frame)))
    (prefixp
     (frame-val->path
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                        frame))))
    (ctx-app-ok
     (frame-val->dir
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (1st-complete frame)
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                         frame)))))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))
             (fat32-filename-list-fix pathname))
    (abs-separate frame)
    (not
     (equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       frame)))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                 frame))))
         pathname)))
      *enoent*)))
   (equal
    (abs-find-file-helper
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                     frame))))
             pathname))
    (mv (abs-file-fix nil) *enoent*)))
  :hints (("goal" :do-not-induct t)))

(defthm
  abs-find-file-correctness-1-lemma-17
  (implies (and (mv-nth 1 (collapse frame))
                (consp (assoc-equal y (frame->frame frame))))
           (consp (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame))))
  :hints
  (("goal"
    :in-theory (disable (:type-prescription 1st-complete-correctness-1))
    :use (:instance (:type-prescription 1st-complete-correctness-1)
                    (frame (frame->frame frame)))))
  :rule-classes :type-prescription)

(defthm
  abs-find-file-correctness-1-lemma-39
  (implies
   (and
    (ctx-app-ok
     (frame-val->dir
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (1st-complete frame)
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                         frame)))))
    (prefixp
     (frame-val->path
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (fat32-filename-list-fix pathname))
    (prefixp (fat32-filename-list-fix pathname)
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))))
   (not
    (m1-regular-file-p
     (mv-nth
      0
      (abs-find-file-helper
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame)))
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        pathname))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (abs-find-file-helper abs-addrs-of-ctx-app-1-lemma-7)
                    (abs-find-file-helper-of-collapse-lemma-2
                     (:rewrite abs-find-file-of-put-assoc-lemma-6)))
    :use
    ((:instance
      abs-find-file-helper-of-collapse-lemma-2
      (abs-file-alist1
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (x (1st-complete frame))
      (x-path
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame))))))
     (:instance
      abs-find-file-correctness-1-lemma-49
      (fs
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (pathname
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        pathname))
      (x-path
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame))))))
     (:instance (:rewrite abs-find-file-of-put-assoc-lemma-6)
                (x (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                     frame)))))
     (:instance
      (:rewrite abs-find-file-of-put-assoc-lemma-6)
      (x (1st-complete frame))
      (frame (remove-assoc-equal
              (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                frame)))
              frame)))))))

(defthm
  abs-find-file-correctness-1-lemma-44
  (implies (equal (mv-nth 1
                          (hifat-find-file (frame->root frame)
                                           pathname))
                  0)
           (equal (cons (mv-nth 0
                                (hifat-find-file (frame->root frame)
                                                 pathname))
                        '(0))
                  (hifat-find-file (frame->root frame)
                                   pathname)))
  :instructions (:promote (:dive 2)
                          (:rewrite abs-find-file-correctness-1-lemma-31)
                          :top :s))

(defthm
  abs-find-file-correctness-1-lemma-56
  (implies (equal (mv-nth 1
                          (abs-find-file-helper (frame->root frame)
                                                pathname))
                  0)
           (equal (cons (mv-nth 0
                                (abs-find-file-helper (frame->root frame)
                                                      pathname))
                        '(0))
                  (abs-find-file-helper (frame->root frame)
                                        pathname)))
  :instructions (:promote (:dive 2)
                          (:rewrite abs-find-file-of-put-assoc-lemma-1)
                          :top :bash))

(defthm
  abs-find-file-correctness-1-lemma-42
  (implies
   (and
    (ctx-app-ok (frame->root frame)
                x
                (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
    (not (equal (mv-nth 1
                        (abs-find-file-helper (frame->root frame)
                                              pathname))
                *enoent*))
    (dist-names (frame->root frame)
                nil (frame->frame frame)))
   (not
    (equal (mv-nth 1
                   (abs-find-file-helper (frame->root (collapse-this frame x))
                                         pathname))
           *enoent*)))
  :hints (("goal" :in-theory (enable collapse-this))))

(defthm
  abs-find-file-correctness-1-lemma-41
  (implies
   (and
    (prefixp
     (frame-val->path
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
     (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
    (prefixp (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
             (fat32-filename-list-fix pathname)))
   (prefixp
    (frame-val->path
     (cdr
      (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                   (frame->frame (collapse-this frame x)))))
    (fat32-filename-list-fix pathname)))
  :hints (("goal" :in-theory (enable collapse-this))))

(defthm
  abs-find-file-correctness-1-lemma-68
  (implies
   (and (< 0
           (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
        (not (equal (mv-nth 1
                            (abs-find-file-helper (frame->root frame)
                                                  pathname))
                    2)))
   (not
    (equal (mv-nth 1
                   (abs-find-file-helper (frame->root (collapse-this frame x))
                                         pathname))
           2)))
  :hints (("goal" :in-theory (enable collapse-this))))

;; Maybe revisit this if a more explicit theorem turns out to be necessary.
(defthm
  abs-find-file-correctness-1-lemma-69
  (implies
   (not (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               0))
   (consp
    (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame (collapse-this frame x)))))
  :hints (("goal" :in-theory (enable collapse-this)))
  :rule-classes :type-prescription)

(defthm
  abs-find-file-correctness-1-lemma-67
  (implies
   (and
    (not (equal x (1st-complete (frame->frame frame))))
    (prefixp
     (frame-val->path
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame)))))
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
    (equal
     (abs-find-file-helper
      (frame-val->dir
       (cdr
        (assoc-equal
         x
         (frame->frame (collapse-this frame
                                      (1st-complete (frame->frame frame)))))))
      (nthcdr
       (len
        (frame-val->path
         (cdr
          (assoc-equal
           x
           (frame->frame
            (collapse-this frame
                           (1st-complete (frame->frame frame))))))))
       pathname))
     (mv (abs-file-fix nil) *enoent*))
    (consp (assoc-equal x (frame->frame frame)))
    (abs-separate (frame->frame frame)))
   (equal
    (abs-find-file-helper
     (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
     (nthcdr
      (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
      pathname))
    (mv (abs-file-fix nil) *enoent*)))
  :hints (("goal" :in-theory (enable collapse-this))))

(defthm
  abs-find-file-correctness-1-lemma-50
  (implies
   (and
    (equal
     (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     0)
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (frame-p (frame->frame frame))
    (mv-nth 1 (collapse frame))
    (consp (assoc-equal (1st-complete (frame->frame frame))
                        (frame->frame frame)))
    (prefixp
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))
     (fat32-filename-list-fix pathname))
    (not (equal (mv-nth 1
                        (abs-find-file-helper (frame->root frame)
                                              pathname))
                2))
    (dist-names (frame->root frame)
                nil (frame->frame frame)))
   (equal
    (hifat-find-file
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     (nthcdr
      (len
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))
      pathname))
    (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal"
    :in-theory (e/d (collapse-this)
                    ((:rewrite abs-find-file-helper-when-m1-file-alist-p)))
    :use
    ((:instance
      (:rewrite abs-find-file-helper-when-m1-file-alist-p)
      (pathname
       (nthcdr (len (frame-val->path
                     (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame)))))
               pathname))
      (fs
       (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))
     (:instance (:rewrite abs-find-file-correctness-1-lemma-7)
                (root (frame->root frame))
                (pathname pathname)
                (frame (frame->frame frame)))))))

(encapsulate
  ()

  (local
   (defun
       induction-scheme (frame pathname x)
     (declare (xargs :measure (len (frame->frame frame))))
     (cond
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (not (zp (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (not
         (or
          (equal (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
                 (1st-complete (frame->frame frame)))
          (atom
           (assoc-equal (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
                        (remove-assoc-equal
                         (1st-complete (frame->frame frame))
                         (frame->frame frame))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
                        (remove-assoc-equal
                         (1st-complete (frame->frame frame))
                         (frame->frame frame)))))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))
        (ctx-app-ok
         (frame-val->dir
          (cdr
           (assoc-equal (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
                        (remove-assoc-equal
                         (1st-complete (frame->frame frame))
                         (frame->frame frame)))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr (assoc-equal
                  (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
                  (remove-assoc-equal
                   (1st-complete (frame->frame frame))
                   (frame->frame frame))))))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (equal x (1st-complete (frame->frame frame))))
       (induction-scheme
        (collapse-this frame (1st-complete (frame->frame frame)))
        pathname
        (frame-val->src
         (cdr (assoc-equal x (frame->frame frame))))))
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (not (zp (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (not
         (or
          (equal (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
                 (1st-complete (frame->frame frame)))
          (atom
           (assoc-equal (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
                        (remove-assoc-equal
                         (1st-complete (frame->frame frame))
                         (frame->frame frame))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
                        (remove-assoc-equal
                         (1st-complete (frame->frame frame))
                         (frame->frame frame)))))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))
        (ctx-app-ok
         (frame-val->dir
          (cdr
           (assoc-equal (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
                        (remove-assoc-equal
                         (1st-complete (frame->frame frame))
                         (frame->frame frame)))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr (assoc-equal
                  (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
                  (remove-assoc-equal
                   (1st-complete (frame->frame frame))
                   (frame->frame frame))))))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))))))
       (induction-scheme
        (collapse-this frame (1st-complete (frame->frame frame)))
        pathname x))
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (zp (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))))
        (ctx-app-ok
         (frame->root frame)
         (1st-complete (frame->frame frame))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))))
       (induction-scheme
        (collapse-this frame (1st-complete (frame->frame frame)))
        pathname x))
      (t (mv frame pathname x)))))

  ;; Rather general!
  (defthmd
    abs-find-file-correctness-1-lemma-36
    (implies
     (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
          (frame-p (frame->frame frame))
          (mv-nth 1 (collapse frame))
          (consp (assoc-equal x (frame->frame frame)))
          (prefixp (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
                   (fat32-filename-list-fix pathname))
          (not (equal (mv-nth 1
                              (abs-find-file-helper (frame->root frame)
                                                    pathname))
                      *enoent*))
          (dist-names (frame->root frame)
                      nil (frame->frame frame))
          (abs-separate (frame->frame frame)))
     (equal
      (abs-find-file-helper
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
       (nthcdr
        (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
        pathname))
      (mv (abs-file-fix nil) *enoent*)))
    :hints (("goal" :induct (induction-scheme frame pathname x)
             :in-theory
             (e/d (collapse)
                  ((:rewrite partial-collapse-correctness-lemma-1)
                   (:rewrite partial-collapse-correctness-lemma-24)
                   (:rewrite partial-collapse-correctness-lemma-33)
                   (:rewrite partial-collapse-correctness-lemma-77)))))))

(defthmd
  abs-find-file-correctness-1-lemma-15
  (implies
   (and
    (no-duplicatesp-equal (strip-cars frame))
    (frame-p frame)
    (ctx-app-ok root (1st-complete frame)
                (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                   frame))))
    (mv-nth
     1
     (collapse
      (frame-with-root
       (ctx-app root
                (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                  frame)))
                (1st-complete frame)
                (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                   frame))))
       (remove-assoc-equal (1st-complete frame)
                           frame))))
    (consp (assoc-equal y frame))
    (not (equal (1st-complete frame) y))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))
             (fat32-filename-list-fix pathname))
    (prefixp (frame-val->path (cdr (assoc-equal y frame)))
             (fat32-filename-list-fix pathname))
    (dist-names root nil frame)
    (abs-separate frame)
    (not
     (equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                        frame))))
                pathname)))
      *enoent*))
    (atom (assoc-equal 0 frame)))
   (equal (abs-find-file-helper
           (frame-val->dir (cdr (assoc-equal y frame)))
           (nthcdr (len (frame-val->path (cdr (assoc-equal y frame))))
                   pathname))
          (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal"
    :do-not-induct t
    :use
    ((:instance
      (:rewrite abs-find-file-correctness-1-lemma-36)
      (frame
       (frame-with-root
        (ctx-app root
                 (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                 (1st-complete frame)
                 (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                    frame))))
        (remove-assoc-equal (1st-complete frame)
                            frame)))
      (x y))))))

(defthm
  abs-find-file-correctness-1-lemma-35
  (implies
   (and
    (abs-complete (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
    (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
           0)
    (equal (mv-nth 1
                   (abs-find-file-helper (frame->root (collapse-this frame x))
                                         pathname))
           2)
    (ctx-app-ok (frame->root frame)
                x
                (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
    (prefixp (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
             (fat32-filename-list-fix pathname))
    (dist-names (frame->root frame)
                nil (frame->frame frame)))
   (equal
    (hifat-find-file
     (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
     (nthcdr
      (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
      pathname))
    (mv (abs-file-fix nil) 2)))
  :hints
  (("goal"
    :in-theory (e/d (collapse-this)
                    (abs-find-file-helper-when-m1-file-alist-p))
    :use
    ((:instance
      (:rewrite abs-find-file-helper-when-m1-file-alist-p)
      (pathname
       (nthcdr
        (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
        pathname))
      (fs (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))))
     (:instance
      (:rewrite abs-find-file-helper-of-ctx-app-lemma-4)
      (pathname
       (nthcdr
        (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
        pathname))
      (fs (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))))))))

(defthm
  abs-find-file-correctness-1-lemma-45
  (implies
   (and
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (mv-nth 1 (collapse frame))
    (equal
     (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
           0)
    (frame-p (frame->frame frame))
    (consp (assoc-equal y (frame->frame frame)))
    (not (equal (1st-complete (frame->frame frame))
                y))
    (prefixp
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))
     (fat32-filename-list-fix pathname))
    (prefixp (frame-val->path (cdr (assoc-equal y (frame->frame frame))))
             (fat32-filename-list-fix pathname))
    (dist-names (frame->root frame)
                nil (frame->frame frame))
    (abs-separate (frame->frame frame))
    (not
     (equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (nthcdr
         (len (frame-val->path
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame)))))
         pathname)))
      2)))
   (equal
    (abs-find-file-helper
     (frame-val->dir (cdr (assoc-equal y (frame->frame frame))))
     (nthcdr
      (len (frame-val->path (cdr (assoc-equal y (frame->frame frame)))))
      pathname))
    (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (collapse)
                    ((:type-prescription 1st-complete-correctness-1)))
    :use
    ((:instance
      (:rewrite abs-find-file-correctness-1-lemma-36)
      (frame
       (collapse-this frame (1st-complete (frame->frame frame))))
      (x y))
     (:instance (:rewrite abs-find-file-correctness-1-lemma-15)
                (frame (frame->frame frame))
                (root (frame->root frame))
                (y (1st-complete (frame->frame frame))))
     (:instance (:type-prescription 1st-complete-correctness-1)
                (frame (frame->frame frame)))))))

(defthm
  abs-find-file-correctness-1-lemma-38
  (implies
   (and
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (mv-nth 1 (collapse frame))
    (equal
     (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     0)
    (frame-p (frame->frame frame))
    (consp (assoc-equal x (frame->frame frame)))
    (not (equal x (1st-complete (frame->frame frame))))
    (prefixp (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
             (fat32-filename-list-fix pathname))
    (prefixp
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))
     (fat32-filename-list-fix pathname))
    (dist-names (frame->root frame)
                nil (frame->frame frame))
    (abs-separate (frame->frame frame))
    (not
     (equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
        (nthcdr
         (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
         pathname)))
      2)))
   (equal
    (abs-find-file-helper
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     (nthcdr
      (len
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))
      pathname))
    (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal"
    :in-theory (enable collapse)
    :use
    ((:instance
      (:rewrite abs-find-file-correctness-1-lemma-36)
      (frame
       (frame-with-root
        (ctx-app
         (frame->root frame)
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (1st-complete (frame->frame frame))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))
        (remove-assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))
     (:instance
      (:rewrite abs-find-file-helper-of-ctx-app-lemma-4)
      (pathname
       (nthcdr (len (frame-val->path
                     (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame)))))
               pathname))
      (fs
       (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))))))

(defthmd
  abs-find-file-correctness-1-lemma-74
  (implies
   (not (zp (mv-nth 1 (hifat-find-file fs pathname))))
   (equal (hifat-find-file fs pathname)
          (mv (make-m1-file)
              (mv-nth 1 (hifat-find-file fs pathname)))))
  :hints (("goal" :in-theory (enable hifat-find-file))))

(defthm
  abs-find-file-correctness-1-lemma-73
  (implies
   (and
    (abs-complete (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
    (< 0
       (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
    (consp
     (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))
    (prefixp
     (frame-val->path
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
     (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
    (ctx-app-ok
     (frame-val->dir
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
     x
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
    (equal
     (mv-nth
      1
      (abs-find-file-helper
       (frame-val->dir
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame (collapse-this frame x)))))
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame)))))
        pathname)))
     2)
    (prefixp (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
             (fat32-filename-list-fix pathname))
    (abs-separate (frame->frame frame)))
   (equal
    (hifat-find-file
     (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
     (nthcdr
      (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
      pathname))
    (mv (make-m1-file) *enoent*)))
  :hints
  (("goal"
    :in-theory (enable collapse-this
                       abs-addrs-of-ctx-app-1-lemma-7)
    :use
    (:instance
     (:rewrite abs-find-file-correctness-1-lemma-74)
     (pathname
      (nthcdr
       (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
       pathname))
     (fs (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))))

(encapsulate
  ()

  (local
   (defun induction-scheme (frame x y)
     (declare (xargs :measure (len (frame->frame frame))))
     (cond
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (not (zp (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (not
         (or
          (equal (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
                 (1st-complete (frame->frame frame)))
          (atom
           (assoc-equal (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
        (ctx-app-ok
         (frame-val->dir
          (cdr
           (assoc-equal (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
                          (remove-assoc-equal (1st-complete (frame->frame frame))
                                              (frame->frame frame))))))
          (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                             (frame->frame frame))))))
        (equal x (1st-complete (frame->frame frame))))
       (induction-scheme
        (collapse-this frame (1st-complete (frame->frame frame)))
        (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))) y))
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (not (zp (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (not
         (or
          (equal (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
                 (1st-complete (frame->frame frame)))
          (atom
           (assoc-equal (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
        (ctx-app-ok
         (frame-val->dir
          (cdr
           (assoc-equal (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
                          (remove-assoc-equal (1st-complete (frame->frame frame))
                                              (frame->frame frame))))))
          (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                             (frame->frame frame))))))
        (equal y (1st-complete (frame->frame frame))))
       (induction-scheme
        (collapse-this frame (1st-complete (frame->frame frame)))
        x (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (not (zp (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (not
         (or
          (equal (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
                 (1st-complete (frame->frame frame)))
          (atom
           (assoc-equal (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
        (ctx-app-ok
         (frame-val->dir
          (cdr
           (assoc-equal (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
                          (remove-assoc-equal (1st-complete (frame->frame frame))
                                              (frame->frame frame))))))
          (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                             (frame->frame frame)))))))
       (induction-scheme
        (collapse-this frame (1st-complete (frame->frame frame)))
        x y))
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (zp (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))))
        (ctx-app-ok
         (frame->root frame)
         (1st-complete (frame->frame frame))
         (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))))
       (induction-scheme
        (collapse-this frame (1st-complete (frame->frame frame)))
        x y))
      (t (mv frame x y)))))

  ;; This is important, but the induction scheme and subgoals were a drag.
  (defthmd
    abs-find-file-correctness-1-lemma-75
    (implies
     (and
      (no-duplicatesp-equal (strip-cars (frame->frame frame)))
      (mv-nth 1 (collapse frame))
      (frame-p (frame->frame frame))
      (consp (assoc-equal x (frame->frame frame)))
      (consp (assoc-equal y (frame->frame frame)))
      (not (equal x y))
      (prefixp (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
               (fat32-filename-list-fix pathname))
      (prefixp (frame-val->path (cdr (assoc-equal y (frame->frame frame))))
               (fat32-filename-list-fix pathname))
      (dist-names (frame->root frame)
                  nil (frame->frame frame))
      (abs-separate (frame->frame frame))
      (not
       (equal
        (mv-nth
         1
         (abs-find-file-helper
          (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
          (nthcdr
           (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
           pathname)))
        2)))
     (equal
      (abs-find-file-helper
       (frame-val->dir (cdr (assoc-equal y (frame->frame frame))))
       (nthcdr
        (len (frame-val->path (cdr (assoc-equal y (frame->frame frame)))))
        pathname))
      (mv (abs-file-fix nil) *enoent*)))
    :hints (("goal" :induct (induction-scheme frame x y)
             :in-theory (e/d (collapse)
                             ())))))

(local
 (defthm
   abs-find-file-correctness-1-lemma-47
   (implies
    (and
     (atom (assoc-equal 0 frame))
     (no-duplicatesp-equal (strip-cars frame))
     (mv-nth 1
             (collapse (frame-with-root root frame)))
     (frame-p frame)
     (consp (assoc-equal x frame))
     (subsetp-equal indices (strip-cars frame))
     (not (member-equal x indices))
     (prefixp (frame-val->path (cdr (assoc-equal x frame)))
              (fat32-filename-list-fix pathname))
     (dist-names root nil frame)
     (abs-separate frame)
     (not
      (equal
       (mv-nth 1
               (abs-find-file-helper
                (frame-val->dir (cdr (assoc-equal x frame)))
                (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                        pathname)))
       *enoent*)))
    (equal (abs-find-file-alt frame indices pathname)
           (mv (abs-file-fix nil) *enoent*)))
   :hints
   (("goal" :induct (abs-find-file-alt frame indices pathname)
     :in-theory (e/d (abs-find-file-alt)
                     (member-of-a-nat-list)))
    ("subgoal *1/2"
     :expand (subsetp-equal indices (strip-cars frame))
     :use ((:instance member-of-a-nat-list (x nil)
                      (lst (strip-cars frame)))
           (:instance (:rewrite abs-find-file-correctness-1-lemma-75)
                      (frame (frame-with-root root frame))
                      (y (car indices))))))))

(defthmd
  abs-find-file-correctness-1-lemma-48
  (implies
   (and
    (atom (assoc-equal 0 frame))
    (dist-names root
                nil frame)
    (frame-p frame)
    (mv-nth 1
            (collapse (frame-with-root root frame)))
    (consp (assoc-equal x frame))
    (prefixp (frame-val->path (cdr (assoc-equal x frame)))
             (fat32-filename-list-fix pathname))
    (abs-separate frame)
    (not
     (equal
      (mv-nth 1
              (abs-find-file-helper
               (frame-val->dir (cdr (assoc-equal x frame)))
               (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                       pathname)))
      *enoent*))
    (no-duplicatesp-equal (strip-cars frame)))
   (equal (abs-find-file (remove-assoc-equal x frame)
                         pathname)
          (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal" :in-theory (disable abs-find-file-correctness-1-lemma-47)
    :use (:instance abs-find-file-correctness-1-lemma-47
                    (indices (remove-equal x (strip-cars frame))))
    :do-not-induct t)))

(defthm
  abs-find-file-correctness-1-lemma-10
  (implies
   (and
    (< 0
       (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                         frame))))
    (prefixp
     (frame-val->path
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                        frame))))
    (ctx-app-ok
     (frame-val->dir
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (1st-complete frame)
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                         frame)))))
    (equal (abs-find-file (remove-assoc-equal (1st-complete frame)
                                              frame)
                          pathname)
           (mv (abs-file-fix nil) *enoent*))
    (< 0 (1st-complete frame))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-separate frame)
    (mv-nth 1
            (collapse (collapse-this (frame-with-root root frame)
                                     (1st-complete frame))))
    (not
     (equal
      (mv-nth
       1
       (hifat-find-file
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                        frame))))
                pathname)))
      2))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))
             (fat32-filename-list-fix pathname)))
   (equal
    (mv-nth
     1
     (abs-find-file
      (remove-assoc-equal
       (1st-complete frame)
       (remove-assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        frame))
      pathname))
    2))
  :hints (("goal" :in-theory (enable collapse-this))))

(defthm
  abs-find-file-correctness-1-lemma-32
  (implies
   (and
    (atom (assoc-equal 0 frame))
    (< 0 (1st-complete frame))
    (prefixp
     (frame-val->path
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                        frame))))
    (ctx-app-ok
     (frame-val->dir
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (1st-complete frame)
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                         frame)))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (dist-names root nil frame)
    (abs-separate frame)
    (mv-nth 1
            (collapse (collapse-this (frame-with-root root frame)
                                     (1st-complete frame))))
    (not
     (equal
      (mv-nth
       1
       (abs-find-file
        (remove-assoc-equal
         (1st-complete frame)
         (remove-assoc-equal
          (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                            frame)))
          frame))
        pathname))
      *enoent*))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))
             (fat32-filename-list-fix pathname)))
   (equal
    (hifat-find-file
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                     frame))))
             pathname))
    (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (collapse abs-addrs-of-ctx-app-1-lemma-7)
                    ((:rewrite remove-assoc-of-put-assoc)
                     (:rewrite abs-find-file-helper-of-ctx-app)))
    :use
    ((:instance (:rewrite abs-find-file-correctness-1-lemma-48)
                (x (1st-complete frame)))
     (:instance
      abs-find-file-correctness-1-lemma-74
      (fs (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame))))
      (pathname
       (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                       frame))))
               pathname))))
    :expand (collapse (frame-with-root root frame)))))

(defthm
  abs-find-file-correctness-1-lemma-43
  (implies
   (and
    (ctx-app-ok
     (frame-val->dir
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (1st-complete frame)
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                         frame)))))
    (prefixp
     (frame-val->path
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (fat32-filename-list-fix pathname))
    (prefixp (fat32-filename-list-fix pathname)
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))))
   (not
    (m1-regular-file-p
     (mv-nth
      0
      (abs-find-file-helper
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame)))
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        pathname))))))
  :hints (("goal" :in-theory (e/d ()
                                  (abs-find-file-correctness-1-lemma-39))
           :use abs-find-file-correctness-1-lemma-39)))

(defthm
  abs-find-file-correctness-1-lemma-62
  (implies
   (and
    (atom (assoc-equal 0 frame))
    (prefixp
     (frame-val->path
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (fat32-filename-list-fix pathname))
    (not
     (equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       frame)))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                 frame))))
         pathname)))
      2))
    (prefixp
     (frame-val->path
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                        frame))))
    (ctx-app-ok
     (frame-val->dir
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (1st-complete frame)
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                         frame)))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (dist-names root nil frame)
    (abs-separate frame)
    (mv-nth 1
            (collapse (collapse-this (frame-with-root root frame)
                                     (1st-complete frame)))))
   (equal
    (abs-find-file (remove-assoc-equal
                    (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                      frame)))
                    frame)
                   pathname)
    (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (enable collapse abs-addrs-of-ctx-app-1-lemma-7)
    :use
    ((:instance (:rewrite abs-find-file-correctness-1-lemma-48)
                (x (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                     frame)))))
     (:instance (:rewrite abs-find-file-correctness-1-lemma-48)
                (x (1st-complete frame)))
     (:instance
      (:rewrite abs-find-file-of-put-assoc-lemma-4)
      (pathname pathname)
      (frame (remove-assoc-equal
              (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                frame)))
              frame)))))))

(defthm
  abs-find-file-correctness-1-lemma-51
  (implies
   (and
    (atom (assoc-equal 0 frame))
    (< 0 (1st-complete frame))
    (< 0
       (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                         frame))))
    (not (equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                  frame)))
                (1st-complete frame)))
    (consp (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))
    (prefixp
     (frame-val->path
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                        frame))))
    (ctx-app-ok
     (frame-val->dir
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (1st-complete frame)
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                         frame)))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-separate frame)
    (mv-nth
     1
     (collapse
      (frame-with-root
       root
       (put-assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (frame-val
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
         (ctx-app
          (frame-val->dir
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                 frame)))
          (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame)))
          (1st-complete frame)
          (nthcdr
           (len
            (frame-val->path
             (cdr (assoc-equal
                   (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                     frame)))
                   frame))))
           (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                              frame)))))
         (frame-val->src
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        (remove-assoc-equal (1st-complete frame)
                            frame)))))
    (dist-names root nil frame)
    (m1-regular-file-p (mv-nth 0 (abs-find-file frame pathname))))
   (equal
    (abs-find-file
     (put-assoc-equal
      (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                        frame)))
      (frame-val
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame)))
       (ctx-app
        (frame-val->dir
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       frame)))
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (1st-complete frame)
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                 frame))))
         (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                            frame)))))
       (frame-val->src
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (remove-assoc-equal (1st-complete frame)
                          frame))
     pathname)
    (abs-find-file frame pathname)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (collapse-this))
    :expand
    ((:with abs-find-file-of-remove-assoc-1
            (abs-find-file (remove-assoc-equal (1st-complete frame)
                                               frame)
                           pathname))
     (:with
      abs-find-file-of-put-assoc
      (abs-find-file
       (put-assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (frame-val
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
         (ctx-app
          (frame-val->dir
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                 frame)))
          (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame)))
          (1st-complete frame)
          (nthcdr
           (len
            (frame-val->path
             (cdr (assoc-equal
                   (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                     frame)))
                   frame))))
           (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                              frame)))))
         (frame-val->src
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        (remove-assoc-equal (1st-complete frame)
                            frame))
       pathname))))))

(defthm
  abs-find-file-correctness-1-lemma-52
  (implies
   (and
    (equal
     (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     0)
    (< 0 (1st-complete (frame->frame frame)))
    (ctx-app-ok
     (frame->root frame)
     (1st-complete (frame->frame frame))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame)))))
    (prefixp
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))
     (fat32-filename-list-fix pathname))
    (not
     (equal
      (mv-nth
       1
       (hifat-find-file
        (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (nthcdr
         (len (frame-val->path
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame)))))
         pathname)))
      2))
    (mv-nth
     1
     (collapse
      (frame-with-root
       (ctx-app
        (frame->root frame)
        (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (1st-complete (frame->frame frame))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame)))))
       (remove-assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame)))))
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (dist-names (frame->root frame)
                nil (frame->frame frame))
    (abs-separate (frame->frame frame)))
   (equal
    (abs-find-file (remove-assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))
                   pathname)
    (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal" :in-theory (enable collapse collapse-this)
    :use (:instance (:rewrite abs-find-file-correctness-1-lemma-48)
                    (frame (frame->frame frame))
                    (x (1st-complete (frame->frame frame)))
                    (root (frame->root frame))))))

(defthm
  abs-find-file-correctness-1-lemma-53
  (implies
   (equal
    (hifat-find-file
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     (nthcdr
      (len
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))
      pathname))
    (cons
     (mv-nth
      0
      (hifat-find-file
       (mv-nth
        0
        (collapse
         (frame-with-root
          (ctx-app
           (frame->root frame)
           (frame-val->dir
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
           (1st-complete (frame->frame frame))
           (frame-val->path
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame)))))
          (remove-assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame)))))
       pathname))
     '(0)))
   (not
    (equal
     (mv-nth
      1
      (hifat-find-file
       (frame-val->dir$inline
        (cdr (assoc-equal (1st-complete (frame->frame frame))
                          (frame->frame frame))))
       (nthcdr (len (frame-val->path$inline
                     (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame)))))
               pathname)))
     2)))
  :hints
  (("goal"
    :in-theory (e/d (abs-find-file collapse abs-separate intersectp-equal collapse-this)
                    ((:rewrite nthcdr-when->=-n-len-l)
                     (:rewrite len-when-prefixp)
                     (:definition remove-assoc-equal)
                     (:rewrite remove-assoc-of-remove-assoc)
                     (:rewrite remove-assoc-when-absent-1)
                     (:rewrite abs-file-alist-p-when-m1-file-alist-p)
                     (:rewrite remove-assoc-of-put-assoc)
                     (:rewrite prefixp-one-way-or-another . 1)
                     (:rewrite abs-find-file-correctness-1-lemma-21)
                     (:definition member-equal)
                     (:rewrite abs-find-file-correctness-1-lemma-45)
                     (:rewrite abs-find-file-helper-of-collapse-lemma-2)
                     (:definition remove-equal))))))

(defthm
  abs-find-file-correctness-1
  (implies
   (and (mv-nth 1 (collapse frame))
        (frame-p (frame->frame frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame)))
        (abs-separate (frame-with-root (frame->root frame)
                                       (frame->frame frame)))
        (zp (mv-nth 1
                    (abs-find-file (frame-with-root (frame->root frame)
                                                    (frame->frame frame))
                                   pathname)))
        (m1-regular-file-p
         (mv-nth 0
                 (abs-find-file (frame-with-root (frame->root frame)
                                                 (frame->frame frame))
                                pathname))))
   (equal (abs-find-file (frame-with-root (frame->root frame)
                                          (frame->frame frame))
                         pathname)
          (mv (mv-nth 0
                      (hifat-find-file (mv-nth 0 (collapse frame))
                                       pathname))
              0)))
  :hints
  (("goal"
    :in-theory (e/d (abs-find-file collapse abs-separate intersectp-equal collapse-this)
                    ((:rewrite nthcdr-when->=-n-len-l)
                     (:rewrite len-when-prefixp)
                     (:rewrite abs-file-alist-p-when-m1-file-alist-p)
                     (:rewrite prefixp-one-way-or-another . 1)
                     (:rewrite
                      abs-find-file-correctness-1-lemma-21)
                     (:definition member-equal)
                     (:rewrite
                      abs-find-file-correctness-1-lemma-45)
                     (:rewrite
                      abs-find-file-helper-of-collapse-lemma-2)
                     (:definition remove-equal)))
    :induct (collapse frame))))
