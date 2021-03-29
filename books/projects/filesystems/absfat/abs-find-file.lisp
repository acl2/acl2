;  abs-find-file.lisp                                   Mihir Mehta

(in-package "ACL2")

(include-book "../abs-separate")
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
                     (:rewrite remove-assoc-of-put-assoc)
                     (:linear position-when-member)
                     (:rewrite true-listp-when-abs-file-alist-p)
                     (:linear position-equal-ac-when-member)
                     (:rewrite m1-directory-file-p-correctness-1)
                     (:linear 1st-complete-of-put-assoc-1)
                     (:rewrite abs-complete-when-stringp)
                     (:definition position-equal-ac)
                     nfix)))

(local
 (in-theory
  (disable
   (:rewrite m1-file-alist-p-when-subsetp-equal)
   (:rewrite
    abs-fs-fix-of-put-assoc-equal-lemma-2)
   abs-addrs-of-remove-assoc-lemma-1
   (:type-prescription
    abs-directory-file-p-when-m1-file-p-lemma-1)
   (:rewrite abs-addrs-when-m1-file-alist-p)
   (:rewrite
    m1-file-alist-p-of-cdr-when-m1-file-alist-p)
   (:rewrite hifat-file-alist-fix-guard-lemma-1)
   (:rewrite 1st-complete-of-put-assoc-2)
   (:rewrite m1-file-contents-p-correctness-1)
   (:rewrite true-listp-when-d-e-p)
   (:rewrite
    abs-separate-of-frame->frame-of-collapse-this-lemma-7)
   (:rewrite dist-names-of-put-assoc-equal)
   (:linear
    len-when-hifat-bounded-file-alist-p . 3)
   (:rewrite absfat-subsetp-of-put-assoc-3)
   (:rewrite
    member-equal-of-strip-cars-when-m1-file-alist-p)
   (:rewrite hifat-subsetp-transitive-lemma-1)
   (:rewrite absfat-subsetp-of-put-assoc-1)
   (:rewrite
    abs-find-file-correctness-1-lemma-40)
   (:rewrite
    absfat-equiv-implies-set-equiv-addrs-at-1-lemma-2)
   (:rewrite
    absfat-equiv-implies-set-equiv-names-at-1-lemma-2)
   (:rewrite
    abs-separate-of-frame->frame-of-collapse-this-lemma-13)
   (:rewrite
    abs-separate-of-frame->frame-of-collapse-this-lemma-5)
   (:rewrite
    hifat-equiv-implies-set-equiv-strip-cars-1-lemma-2)
   (:rewrite
    hifat-equiv-implies-set-equiv-strip-cars-1-lemma-1)
   (:rewrite abs-separate-correctness-1-lemma-38)
   (:rewrite
    abs-separate-of-frame->frame-of-collapse-this-lemma-14)
   (:rewrite
    hifat-place-file-correctness-lemma-3))))

(defund abs-find-file-helper (fs path)
  (declare (xargs :guard (and (abs-file-alist-p fs)
                              (fat32-filename-list-p path))
                  :measure (acl2-count path)))
  (b*
      ((fs (abs-fs-fix fs))
       ((unless (consp path))
        (mv (make-abs-file) *enoent*))
       (name (mbe :logic (fat32-filename-fix (car path))
                  :exec (car path)))
       (alist-elem (abs-assoc name fs))
       ((unless (consp alist-elem))
        (mv (make-abs-file) *enoent*))
       ((when (abs-directory-file-p (cdr alist-elem)))
        (if (atom (cdr path))
            (mv (cdr alist-elem) 0)
          (abs-find-file-helper (abs-file->contents (cdr alist-elem))
                                (cdr path))))
       ((unless (atom (cdr path)))
        (mv (make-abs-file) *enotdir*)))
    (mv (cdr alist-elem) 0)))

(defthm
  natp-of-abs-find-file-helper
  (natp (mv-nth 1 (abs-find-file-helper fs path)))
  :hints (("goal" :in-theory (enable abs-find-file-helper)))
  :rule-classes :type-prescription)

(defthm abs-find-file-helper-of-fat32-filename-list-fix
  (equal (abs-find-file-helper fs (fat32-filename-list-fix path))
         (abs-find-file-helper fs path))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defcong
  fat32-filename-list-equiv
  equal (abs-find-file-helper fs path)
  2
  :hints
  (("goal"
    :in-theory
    (disable abs-find-file-helper-of-fat32-filename-list-fix)
    :use
    ((:instance abs-find-file-helper-of-fat32-filename-list-fix
                (path path-equiv))
     abs-find-file-helper-of-fat32-filename-list-fix))))

(defthm abs-find-file-helper-of-abs-fs-fix
  (equal (abs-find-file-helper (abs-fs-fix fs)
                               path)
         (abs-find-file-helper fs path))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm
  abs-find-file-helper-of-append-1
  (equal
   (abs-find-file-helper fs (append x y))
   (cond ((atom y) (abs-find-file-helper fs x))
         ((and (zp (mv-nth 1 (abs-find-file-helper fs x)))
               (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs x))))
          (abs-find-file-helper
           (abs-file->contents (mv-nth 0 (abs-find-file-helper fs x)))
           y))
         ((zp (mv-nth 1 (abs-find-file-helper fs x)))
          (mv (abs-file-fix nil) *enotdir*))
         ((atom x) (abs-find-file-helper fs y))
         (t (abs-find-file-helper fs x))))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm abs-find-file-helper-when-atom
  (implies (atom path)
           (equal (abs-find-file-helper fs path)
                  (mv (abs-file-fix nil) *enoent*)))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm
  no-duplicatesp-equal-of-abs-addrs-of-abs-file->contents-of-abs-find-file-helper
  (implies
   (no-duplicatesp-equal (abs-addrs (abs-fs-fix fs)))
   (no-duplicatesp-equal
    (abs-addrs
     (abs-file->contents (mv-nth 0 (abs-find-file-helper fs path))))))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm
  member-of-names-at-lemma-1
  (implies (and (abs-file-alist-p fs)
                (consp (assoc-equal name fs))
                (not (abs-directory-file-p (cdr (assoc-equal name fs)))))
           (not (consp (m1-file->contents (cdr (assoc-equal name fs))))))
  :hints (("goal" :in-theory (enable abs-file-alist-p
                                     m1-file->contents m1-file-contents-fix
                                     m1-file-contents-p abs-directory-file-p
                                     abs-file->contents abs-file-p))))

(defthmd
  member-of-names-at
  (iff
   (member-equal x (names-at fs relpath))
   (if
    (consp relpath)
    (consp
     (assoc-equal
      x
      (abs-file->contents (mv-nth 0 (abs-find-file-helper fs relpath)))))
    (consp (assoc-equal x (abs-fs-fix fs)))))
  :hints (("goal" :in-theory (e/d (abs-find-file-helper names-at)
                                  (list-equiv-when-atom))
           :induct (abs-find-file-helper fs relpath))))

(defund
  abs-find-file (frame path)
  (declare
   (xargs :guard (and (frame-p frame)
                      (fat32-filename-list-p path))))
  (b*
      (((when (atom frame))
        (mv (make-abs-file) *enoent*))
       (path (mbe :exec path
                      :logic (fat32-filename-list-fix path)))
       ((unless (prefixp (frame-val->path (cdar frame))
                         path))
        (abs-find-file (cdr frame) path))
       ((mv file error-code)
        (abs-find-file-helper
         (frame-val->dir (cdar frame))
         (nthcdr (len (frame-val->path (cdar frame)))
                 path)))
       ((when (not (equal error-code *enoent*)))
        (mv file error-code)))
    (abs-find-file (cdr frame) path)))

(defthm natp-of-abs-find-file
  (natp (mv-nth 1 (abs-find-file frame path)))
  :hints (("goal" :in-theory (enable abs-find-file)))
  :rule-classes :type-prescription)

(encapsulate
  ()

  (local
   (defthmd abs-find-file-of-fat32-filename-list-fix
     (equal (abs-find-file frame
                           (fat32-filename-list-fix path))
            (abs-find-file frame path))
     :hints (("goal" :in-theory (enable abs-find-file)))))

  (defcong
    fat32-filename-list-equiv
    equal (abs-find-file frame path)
    2
    :hints
    (("goal"
      :use ((:instance abs-find-file-of-fat32-filename-list-fix
                       (path path-equiv))
            abs-find-file-of-fat32-filename-list-fix)))))

(defthmd abs-find-file-of-true-list-fix
  (equal (abs-find-file (true-list-fix frame)
                        path)
         (abs-find-file frame path))
  :hints (("goal" :in-theory (enable abs-find-file))))

(defcong
  list-equiv
  equal (abs-find-file frame path)
  1
  :hints
  (("goal" :use ((:instance abs-find-file-of-true-list-fix
                            (frame frame-equiv))
                 abs-find-file-of-true-list-fix))))

(defthm abs-find-file-when-atom
  (implies (atom path)
           (equal (abs-find-file frame path)
                  (mv (abs-file-fix nil) *enoent*)))
  :hints (("goal" :in-theory (enable abs-find-file))))

(defthm
  abs-file-p-of-abs-find-file-helper
  (abs-file-p (mv-nth 0 (abs-find-file-helper fs path)))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm abs-file-p-of-abs-find-file
  (abs-file-p (mv-nth 0 (abs-find-file frame path)))
  :hints (("goal" :in-theory (enable abs-find-file))))

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
    (m1-directory-file-p (cdr (assoc-equal (fat32-filename-fix (car path))
                                           fs)))
    (abs-fs-p fs))
   (abs-fs-p
    (m1-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                         fs)))))
  :hints
  (("goal"
    :in-theory
    (disable (:rewrite abs-fs-p-of-abs-file->contents-of-cdr-of-assoc))
    :use (:instance (:rewrite abs-fs-p-of-abs-file->contents-of-cdr-of-assoc)
                    (name (fat32-filename-fix (car path)))))))

(defthm
  abs-find-file-helper-when-m1-file-alist-p
  (implies (abs-complete (abs-fs-fix fs))
           (equal (abs-find-file-helper fs path)
                  (hifat-find-file (abs-fs-fix fs)
                                   path)))
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
                            (abs-find-file-helper abs-file-alist1 path))
                    *enoent*)))
   (equal (abs-find-file-helper (append (remove-equal x abs-file-alist1)
                                        abs-file-alist2)
                                path)
          (abs-find-file-helper abs-file-alist1 path)))
  :hints
  (("goal" :do-not-induct t
    :expand (:free (abs-file-alist)
                   (abs-find-file-helper abs-file-alist path))
    :cases ((null (car path))))))

(defthmd abs-find-file-helper-of-ctx-app-lemma-4
  (implies (not (zp (mv-nth 1 (abs-find-file-helper fs path))))
           (equal (abs-find-file-helper fs path)
                  (mv (abs-file-fix nil)
                      (mv-nth 1 (abs-find-file-helper fs path)))))
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
                   (abs-find-file-helper abs-file-alist1 path))
           2))
   (equal (abs-find-file-helper (append (remove-equal x abs-file-alist1)
                                        abs-file-alist2)
                                path)
          (abs-find-file-helper abs-file-alist2 path)))
  :hints
  (("goal"
    :do-not-induct t
    :use
    (:instance (:rewrite abs-find-file-helper-of-ctx-app-lemma-4)
               (path (cdr path))
               (fs (abs-file->contents
                    (cdr (assoc-equal (fat32-filename-fix (car path))
                                      abs-file-alist1)))))
    :expand ((:free (abs-file-alist)
                    (abs-find-file-helper abs-file-alist path))))))

(defthm
  abs-find-file-helper-of-ctx-app
  (implies
   (abs-fs-p (ctx-app abs-file-alist1
                      abs-file-alist2 x x-path))
   (equal
    (abs-find-file-helper (ctx-app abs-file-alist1
                                   abs-file-alist2 x x-path)
                          path)
    (cond
     ((not (ctx-app-ok abs-file-alist1 x x-path))
      (abs-find-file-helper abs-file-alist1 path))
     ((and (equal (mv-nth 1
                          (abs-find-file-helper abs-file-alist1 path))
                  0)
           (prefixp (fat32-filename-list-fix path)
                    (fat32-filename-list-fix x-path)))
      (mv
       (abs-file
        (abs-file->d-e
         (mv-nth 0
                 (abs-find-file-helper abs-file-alist1 path)))
        (ctx-app
         (abs-file->contents
          (mv-nth 0
                  (abs-find-file-helper abs-file-alist1 path)))
         abs-file-alist2
         x (nthcdr (len path) x-path)))
       0))
     ((and (equal (mv-nth 1
                          (abs-find-file-helper abs-file-alist1 path))
                  *enoent*)
           (prefixp (fat32-filename-list-fix x-path)
                    (fat32-filename-list-fix path)))
      (abs-find-file-helper abs-file-alist2
                            (nthcdr (len x-path) path)))
     (t (abs-find-file-helper abs-file-alist1 path)))))
  :hints
  (("goal"
    :in-theory
    (e/d (prefixp abs-find-file-helper
                  ctx-app ctx-app-ok names-at addrs-at)
         (nfix (:rewrite remove-when-absent)
               (:rewrite abs-find-file-helper-when-m1-file-alist-p)
               (:rewrite abs-file-contents-p-when-m1-file-contents-p)
               (:rewrite abs-addrs-of-ctx-app)
               (:rewrite abs-file-alist-p-correctness-1)
               (:definition no-duplicatesp-equal)))
    :induct
    (mv (mv-nth 0
                (abs-find-file-helper (ctx-app abs-file-alist1
                                               abs-file-alist2 x x-path)
                                      path))
        (fat32-filename-list-prefixp x-path path)
        (ctx-app abs-file-alist1
                 abs-file-alist2 x x-path)))))

;; There doesn't seem to be an easy way of getting out of the expand hints that
;; we need to use this theorem. I've tried surrounding the third hypothesis with a
;; case-split, but that is ineffective because the real problem is the size of
;; the terms in that hypothesis which causes brr to report the hypothesis as
;; more complicated than its ancestors. It also doesn't help to split the
;; theorem into two rewrite corollaries for the same reason - the term is too
;; big! I'm not sure how this could be worked around.
(defthm
 abs-find-file-of-remove-assoc-1
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
  (equal (abs-find-file (remove-assoc-equal x frame)
                        path)
         (abs-find-file frame path)))
 :hints (("goal" :in-theory (enable abs-find-file))))

(defthm
  abs-find-file-of-remove-assoc-2
  (implies
   (and
    (not (null y))
    (no-duplicatesp-equal (strip-cars (remove-assoc-equal x frame)))
    (or
     (not
      (prefixp
       (frame-val->path (cdr (assoc-equal y (remove-assoc-equal x frame))))
       (fat32-filename-list-fix path)))
     (equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal y (remove-assoc-equal x frame))))
        (nthcdr (len (frame-val->path
                      (cdr (assoc-equal y (remove-assoc-equal x frame)))))
                path)))
      *enoent*)))
   (equal (abs-find-file (remove-assoc-equal x (remove-assoc-equal y frame))
                         path)
          (abs-find-file (remove-assoc-equal x frame)
                         path)))
  :hints (("goal" :in-theory (disable abs-find-file-of-remove-assoc-1)
           :use (:instance abs-find-file-of-remove-assoc-1 (x y)
                           (frame (remove-assoc-equal x frame))))))

(defthmd abs-find-file-of-remove-assoc-lemma-1
  (equal (abs-find-file-helper fs path)
         (mv (mv-nth 0 (abs-find-file-helper fs path))
             (mv-nth 1 (abs-find-file-helper fs path))))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm
  abs-find-file-of-remove-assoc-lemma-2
  (equal
   (list (mv-nth 0
                 (abs-find-file-helper (frame-val->dir val)
                                       (nthcdr (len (frame-val->path val))
                                               path)))
         (mv-nth 1
                 (abs-find-file-helper (frame-val->dir val)
                                       (nthcdr (len (frame-val->path val))
                                               path))))
   (abs-find-file-helper (frame-val->dir val)
                         (nthcdr (len (frame-val->path val))
                                 path)))
  :hints
  (("goal" :use (:instance (:rewrite abs-find-file-of-remove-assoc-lemma-1)
                           (path (nthcdr (len (frame-val->path val))
                                             path))
                           (fs (frame-val->dir val))))))

(defthmd
  abs-find-file-of-remove-assoc-lemma-3
  (implies (not (zp (mv-nth 1 (abs-find-file frame path))))
           (equal (abs-find-file frame path)
                  (mv (abs-file-fix nil)
                      (mv-nth 1 (abs-find-file frame path)))))
  :hints
  (("goal" :in-theory (enable abs-find-file))
   ("subgoal *1/2"
    :use
    (:instance (:rewrite abs-find-file-helper-of-ctx-app-lemma-4)
               (path (nthcdr (len (frame-val->path (cdr (car frame))))
                                 path))
               (fs (frame-val->dir (cdr (car frame))))))))

(defthm
  abs-find-file-of-remove-assoc-3
  (implies (equal (mv-nth 1 (abs-find-file frame path))
                  *enoent*)
           (equal (mv-nth 1
                          (abs-find-file (remove-assoc-equal x frame)
                                         path))
                  *enoent*))
  :hints (("goal" :in-theory (enable abs-find-file frame->frame)))
  :rule-classes
  ((:rewrite
    :corollary (implies (equal (mv-nth 1 (abs-find-file frame path))
                               *enoent*)
                        (equal (abs-find-file (remove-assoc-equal x frame)
                                              path)
                               (mv (abs-file-fix nil) *enoent*)))
    :hints
    (("goal" :use (:instance (:rewrite abs-find-file-of-remove-assoc-lemma-3)
                             (path path)
                             (frame (remove-assoc-equal x frame))))))))

(defthm abs-find-file-of-frame->frame-1
  (implies (equal (mv-nth 1 (abs-find-file frame path))
                  *enoent*)
           (equal (abs-find-file (frame->frame frame)
                                 path)
                  (mv (abs-file-fix nil) *enoent*)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable frame->frame))))

(defthm
  abs-find-file-of-put-assoc-lemma-1
  (implies
   (and
    (equal
     (mv-nth
      1
      (abs-find-file-helper (frame-val->dir val)
                            (nthcdr (len (frame-val->path val))
                                    path)))
     2)
    (equal const (mv (abs-file-fix nil) *enoent*)))
   (iff
    (equal
     const
     (abs-find-file-helper (frame-val->dir val)
                           (nthcdr (len (frame-val->path val))
                                   path)))
    t))
  :hints
  (("goal"
    :use
    (:instance (:rewrite abs-find-file-helper-of-ctx-app-lemma-4)
               (path (nthcdr (len (frame-val->path val))
                                 path))
               (fs (frame-val->dir val))))))

(defthm
  abs-find-file-of-put-assoc-lemma-2
  (implies (and (equal (mv-nth 1 (abs-find-file (cdr frame) path))
                       2)
                (equal const (mv (abs-file-fix nil) *enoent*)))
           (iff (equal (abs-find-file (cdr frame) path)
                       const)
                t))
  :hints
  (("goal" :use (:instance (:rewrite abs-find-file-of-remove-assoc-lemma-3)
                           (frame (cdr frame))))))

;; Could be important...
(defthmd
  abs-find-file-of-put-assoc-lemma-6
  (implies
   (and (frame-p frame)
        (no-duplicatesp-equal (strip-cars frame))
        (consp (assoc-equal x frame))
        (equal (mv-nth 1
                       (abs-find-file (remove-assoc-equal x frame)
                                      path))
               *enoent*))
   (equal (abs-find-file frame path)
          (if (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                       (fat32-filename-list-fix path))
              (abs-find-file-helper
               (frame-val->dir (cdr (assoc-equal x frame)))
               (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                       path))
            (mv (abs-file-fix nil) *enoent*))))
  :hints (("goal" :in-theory (enable abs-find-file))))

(defthm
  abs-find-file-of-put-assoc-lemma-7
  (implies
   (and (frame-p frame)
        (no-duplicatesp-equal (strip-cars frame))
        (consp (assoc-equal x frame))
        (equal (mv-nth 1
                       (abs-find-file (remove-assoc-equal x frame)
                                      path))
               *enoent*)
        (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                 (fat32-filename-list-fix path)))
   (equal
    (abs-find-file-helper
     (frame-val->dir (cdr (assoc-equal x frame)))
     (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
             path))
    (abs-find-file frame path)))
  :hints (("goal"
           :use
           abs-find-file-of-put-assoc-lemma-6))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (frame-p frame)
          (no-duplicatesp-equal (strip-cars frame))
          (consp (assoc-equal x frame))
          (equal (mv-nth 1
                         (abs-find-file (remove-assoc-equal x frame)
                                        path))
                 *enoent*)
          (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                   (fat32-filename-list-fix path))
          (abs-complete (frame-val->dir (cdr (assoc-equal x frame)))))
     (equal
      (hifat-find-file
       (frame-val->dir (cdr (assoc-equal x frame)))
       (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
               path))
      (abs-find-file frame path))))))

(defthm
  abs-find-file-of-put-assoc
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
    (abs-find-file (put-assoc-equal name val frame)
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
     (abs-find-file-helper (frame-val->dir val)
                           (nthcdr (len (frame-val->path val))
                                   path))
     (abs-find-file (remove-assoc-equal name frame)
                    path))))
  :hints (("goal" :in-theory (enable abs-find-file))))

(defthm
  abs-find-file-of-frame-with-root
  (equal (abs-find-file (frame-with-root root frame)
                        path)
         (if (equal (mv-nth 1
                            (abs-find-file-helper root path))
                    *enoent*)
             (abs-find-file frame path)
           (abs-find-file-helper root path)))
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d (abs-find-file frame-with-root)
                    ((:rewrite abs-find-file-of-remove-assoc-lemma-1)))
    :use (:instance (:rewrite abs-find-file-of-remove-assoc-lemma-1)
                    (fs (abs-fs-fix root))))))

(local
 (defund abs-find-file-alt
   (frame indices path)
   (b* (((when (atom indices))
         (mv (make-abs-file) *enoent*))
        (path (fat32-filename-list-fix path))
        ((unless (prefixp (frame-val->path (cdr (assoc-equal (car indices) frame)))
                          path))
         (abs-find-file-alt frame (cdr indices) path))
        ((mv file error-code)
         (abs-find-file-helper
          (frame-val->dir (cdr (assoc-equal (car indices) frame)))
          (nthcdr (len (frame-val->path (cdr (assoc-equal (car indices) frame))))
                  path)))
        ((when (not (equal error-code *enoent*)))
         (mv file error-code)))
     (abs-find-file-alt frame (cdr indices) path))))

(local
 (defthm abs-find-file-alt-of-fat32-filename-list-fix
   (equal (abs-find-file-alt frame indices
                             (fat32-filename-list-fix path))
          (abs-find-file-alt frame indices path))
   :hints (("goal" :in-theory (enable abs-find-file-alt)))))

(local
 (defcong
   fat32-filename-list-equiv equal
   (abs-find-file-alt frame indices path)
   3
   :hints
   (("goal"
     :in-theory
     (disable abs-find-file-alt-of-fat32-filename-list-fix)
     :use
     ((:instance abs-find-file-alt-of-fat32-filename-list-fix
                 (path path-equiv))
      abs-find-file-alt-of-fat32-filename-list-fix)))))

(local
 (defthm abs-find-file-alt-correctness-1-lemma-1
   (implies (not (member-equal (caar frame) indices))
            (equal (abs-find-file-alt (cdr frame)
                                      indices path)
                   (abs-find-file-alt frame indices path)))
   :hints (("goal" :in-theory (enable abs-find-file-alt)))))

(local
 (defthm
   abs-find-file-alt-correctness-1
   (implies (no-duplicatesp-equal (strip-cars frame))
            (equal (abs-find-file-alt frame (strip-cars frame)
                                      path)
                   (abs-find-file frame path)))
   :hints (("goal" :in-theory (enable abs-find-file-alt abs-find-file)))))

(local
 (defthm
   abs-find-file-alt-correctness-2
   (implies (no-duplicatesp-equal (strip-cars frame))
            (equal (abs-find-file-alt frame
                                      (remove-equal x (strip-cars frame))
                                      path)
                   (abs-find-file (remove-assoc-equal x frame)
                                  path)))
   :hints (("goal" :in-theory (enable abs-find-file-alt abs-find-file)))))

(defund abs-enotdir-witness (fs path)
  (declare (xargs :measure (len path)))
  (b* (((when (atom path)) path)
       ((mv file errno)
        (abs-find-file-helper fs path))
       ((when (and (zp errno) (m1-regular-file-p file))) path))
    (abs-enotdir-witness fs (butlast path 1))))

(defthm true-listp-of-abs-enotdir-witness
  (implies (true-listp path)
           (true-listp (abs-enotdir-witness fs path)))
  :hints (("Goal" :in-theory (enable abs-enotdir-witness)))
  :rule-classes :type-prescription)

(defthm prefixp-of-abs-enotdir-witness
  (prefixp (abs-enotdir-witness fs path)
           path)
  :hints (("goal" :in-theory (enable abs-enotdir-witness))))

(defthm len-of-abs-enotdir-witness
  (<= (len (abs-enotdir-witness fs path))
      (len path))
  :hints (("goal" :in-theory (enable abs-enotdir-witness)))
  :rule-classes :linear)

(defthm
  abs-enotdir-witness-correctness-1-lemma-1
  (implies
   (< 1 (len path))
   (not (equal (abs-enotdir-witness fs
                                    (take (+ -1 (len path)) path))
               path)))
  :hints (("goal" :use (:instance len-of-abs-enotdir-witness
                                  (path (take (+ -1 (len path))
                                                  path))))))

(defthm
  abs-enotdir-witness-correctness-1
  (implies (equal (mv-nth 1 (abs-find-file-helper fs path))
                  *enotdir*)
           (not (equal (abs-enotdir-witness fs path)
                       path)))
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
                                    (take (+ -1 (len path)) path)))
      *enotdir*))
    (equal (mv-nth 1 (abs-find-file-helper fs path))
           *enotdir*))
   (and
    (m1-regular-file-p
     (mv-nth 0
             (abs-find-file-helper fs
                                   (take (+ -1 (len path)) path))))
    (equal
     (mv-nth 1
             (abs-find-file-helper fs
                                   (take (+ -1 (len path)) path)))
     0)))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm
  abs-enotdir-witness-correctness-2
  (implies
   (equal (mv-nth 1 (abs-find-file-helper fs path))
          *enotdir*)
   (and
    (m1-regular-file-p
     (mv-nth 0
             (abs-find-file-helper fs (abs-enotdir-witness fs path))))
    (equal
     (mv-nth 1
             (abs-find-file-helper fs (abs-enotdir-witness fs path)))
     0)
    (consp (abs-enotdir-witness fs path))))
  :hints (("goal" :in-theory (enable abs-enotdir-witness
                                     abs-find-file-helper))))

(defthm fat32-filename-list-p-of-abs-enotdir-witness
  (implies
   (fat32-filename-list-p path)
   (fat32-filename-list-p (abs-enotdir-witness fs path)))
  :hints (("goal" :in-theory (enable abs-enotdir-witness))))

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
   (and (consp path)
        (fat32-filename-list-prefixp path x-path)
        (zp (mv-nth 1 (abs-find-file-helper fs x-path))))
   (and
    (equal
     (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs path)))
     (or (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs x-path)))
         (not (fat32-filename-list-equiv path x-path))))
    (equal (mv-nth 1 (abs-find-file-helper fs path))
           0)))
  :hints (("goal" :in-theory (e/d (abs-find-file-helper prefixp
                                                        len-of-fat32-filename-list-fix)
                                  (fat32-filename-list-equiv-implies-equal-len-1))
           :induct (mv (mv-nth 1 (abs-find-file-helper fs path))
                       (fat32-filename-list-prefixp path x-path))
           :expand (abs-find-file-helper fs x-path))))

(defthm
  abs-find-file-helper-of-collapse-lemma-5
  (implies
   (and (ctx-app-ok root x
                    (frame-val->path (cdr (assoc-equal x frame))))
        (fat32-filename-list-prefixp path
                                     (frame-val->path (cdr (assoc-equal x frame)))))
   (not (m1-regular-file-p (mv-nth 0
                                   (abs-find-file-helper root path)))))
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

(local
 (defthm
   abs-find-file-helper-of-collapse-lemma-6
   (implies
    (not (m1-regular-file-p (mv-nth 0 (abs-find-file-helper fs path))))
    (abs-fs-p
     (abs-file->contents (mv-nth 0 (abs-find-file-helper fs path)))))
   :hints (("goal" :in-theory (enable abs-find-file-helper)))))

(defthm
  abs-find-file-helper-of-collapse-lemma-8
  (implies (equal (mv-nth 1
                          (abs-find-file-helper fs
                                                path))
                  0)
           (equal (cons (mv-nth 0
                                (abs-find-file-helper fs
                                                      path))
                        '(0))
                  (abs-find-file-helper fs
                                        path)))
  :hints
  (("goal" :use (:rewrite abs-find-file-of-remove-assoc-lemma-1))))

(defthm
  abs-find-file-helper-of-collapse-1
  (implies
   (and
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (abs-separate (frame->frame frame))
    (dist-names (frame->root frame)
                nil (frame->frame frame))
    (zp (mv-nth 1
                (abs-find-file-helper (frame->root frame)
                                      path)))
    (or
     (m1-regular-file-p (mv-nth 0
                                (abs-find-file-helper (frame->root frame)
                                                      path)))
     (and
      (abs-fs-p
       (abs-file->contents (mv-nth 0
                                   (abs-find-file-helper (frame->root frame)
                                                         path))))
      (abs-complete
       (abs-file->contents (mv-nth 0
                                   (abs-find-file-helper (frame->root frame)
                                                         path)))))))
   (equal (abs-find-file-helper (mv-nth 0 (collapse frame))
                                path)
          (abs-find-file-helper (frame->root frame)
                                path)))
  :hints (("goal" :in-theory (e/d (collapse dist-names collapse-this
                                            fat32-filename-list-prefixp-alt)
                                  (abs-find-file-helper-of-collapse-lemma-6))
           :induct (collapse frame)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and
      (frame-p (frame->frame frame))
      (no-duplicatesp-equal (strip-cars (frame->frame frame)))
      (abs-separate (frame->frame frame))
      (dist-names (frame->root frame)
                  nil (frame->frame frame))
      (zp (mv-nth 1
                  (abs-find-file-helper (frame->root frame)
                                        path)))
      (or
       (m1-regular-file-p (mv-nth 0
                                  (abs-find-file-helper (frame->root frame)
                                                        path)))
       (and
        (abs-fs-p
         (abs-file->contents (mv-nth 0
                                     (abs-find-file-helper (frame->root frame)
                                                           path))))
        (abs-complete
         (abs-file->contents (mv-nth 0
                                     (abs-find-file-helper (frame->root frame)
                                                           path))))))
      (m1-file-alist-p (mv-nth 0 (collapse frame))))
     (equal (hifat-find-file (mv-nth 0 (collapse frame))
                             path)
            (abs-find-file-helper (frame->root frame)
                                  path))))))

;; The somewhat weaker conclusion, in terms of (mv-nth 1 (abs-find-file ...))
;; rather than (abs-find-file ...), is because of the possibility that the file
;; returned is a directory with holes, which gets filled in during collapse.
(defthm
  abs-find-file-helper-of-collapse-2
  (implies (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (frame-p (frame->frame frame))
                (abs-separate (frame->frame frame))
                (dist-names (frame->root frame)
                            nil (frame->frame frame))
                (not (equal (mv-nth 1
                                    (abs-find-file-helper (frame->root frame)
                                                          path))
                            *enoent*)))
           (equal (mv-nth 1
                          (abs-find-file-helper (mv-nth 0 (collapse frame))
                                                path))
                  (mv-nth 1
                          (abs-find-file-helper (frame->root frame)
                                                path))))
  :hints (("goal" :in-theory (enable collapse dist-names collapse-this)
           :induct (collapse frame)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                  (frame-p (frame->frame frame))
                  (abs-separate (frame->frame frame))
                  (dist-names (frame->root frame)
                              nil (frame->frame frame))
                  (not (equal (mv-nth 1
                                      (abs-find-file-helper (frame->root frame)
                                                            path))
                              *enoent*))
                  (m1-file-alist-p (mv-nth 0 (collapse frame))))
             (equal (mv-nth 1
                            (hifat-find-file (mv-nth 0 (collapse frame))
                                             path))
                    (mv-nth 1
                            (abs-find-file-helper (frame->root frame)
                                                  path)))))))

(defthmd abs-find-file-correctness-lemma-1
  (equal (abs-find-file frame path)
         (mv (mv-nth 0 (abs-find-file frame path))
             (mv-nth 1 (abs-find-file frame path))))
  :hints (("goal" :in-theory (enable abs-find-file))))

(defthmd
  abs-find-file-correctness-lemma-4
  (implies
   (and (prefixp (fat32-filename-list-fix path)
                 (fat32-filename-list-fix x-path))
        (m1-regular-file-p (mv-nth 0 (abs-find-file-helper fs path)))
        (not (fat32-filename-list-equiv path x-path)))
   (equal (abs-find-file-helper fs x-path)
          (mv (abs-file-fix nil) *enotdir*)))
  :hints
  (("goal" :in-theory (enable fat32-filename-list-equiv
                              abs-find-file-helper
                              prefixp fat32-filename-list-fix)
    :induct (mv (mv-nth 0 (abs-find-file-helper fs path))
                (fat32-filename-list-prefixp path x-path)))))

;; Note this carefully as a useful lemma for reasoning about m1-regular-file-p
;; and abs-find-file.
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
     (fat32-filename-list-fix path))
    (prefixp (fat32-filename-list-fix path)
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
        path))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (abs-find-file-helper abs-addrs-of-ctx-app-lemma-2
                                          len-of-fat32-filename-list-fix)
                    (abs-find-file-helper-of-collapse-lemma-2))
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
      abs-find-file-correctness-lemma-4
      (fs
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (path
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        path))
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
  abs-find-file-correctness-lemma-3
  (implies (and (equal (mv-nth 1
                               (abs-find-file-helper (frame->root frame)
                                                     path))
                       2)
                (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
                (frame-p (frame->frame frame))
                (no-duplicatesp-equal (strip-cars frame)))
           (equal (abs-find-file (frame->frame frame)
                                 path)
                  (abs-find-file frame path)))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (abs-find-file frame->root frame->frame)
                           nil))))

(defthm
  abs-find-file-correctness-1-lemma-30
  (implies
   (and (fat32-filename-list-p path2)
        (zp (mv-nth 1 (abs-find-file-helper fs path1)))
        (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs path1)))
        (equal (mv-nth 1 (abs-find-file-helper fs path2))
               *enotdir*)
        (prefixp path1 path2))
   (member-equal (nth (len path1) path2)
                 (names-at fs path1)))
  :hints (("goal" :in-theory (enable abs-find-file-helper
                                     names-at prefixp)
           :induct t
           :expand (names-at fs path1))))

;; Kinda general
(defthm
  abs-find-file-correctness-1-lemma-18
  (implies
   (and (not (equal (mv-nth 1 (abs-find-file-helper fs path))
                    0))
        (not (equal (mv-nth 1 (abs-find-file-helper fs path))
                    *enoent*)))
   (equal (mv-nth 1 (abs-find-file-helper fs path))
          *enotdir*))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm abs-find-file-correctness-1-lemma-6
  (implies (and (fat32-filename-list-p path)
                (< n (len path))
                (zp (mv-nth 1
                            (abs-find-file-helper (abs-fs-fix fs)
                                                  path))))
           (member-equal (nth n path)
                         (names-at fs (take n path))))
  :hints (("goal" :in-theory (enable names-at
                                     abs-find-file-helper))))

(defthm
  abs-find-file-correctness-1-lemma-23
  (implies
   (and (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                    frame)))
                 (fat32-filename-list-fix path))
        (equal (mv-nth 1 (abs-find-file-helper root path))
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
              path)))
    *enoent*))
  :hints
  (("goal"
    :in-theory
    (e/d
     (abs-find-file-helper)
     (abs-find-file-correctness-1-lemma-6
      (:rewrite abs-find-file-correctness-1-lemma-18)
      (:congruence
       fat32-filename-list-equiv-implies-fat32-filename-list-equiv-take-2)
      intersectp-member))
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
                path)))
      0)
     (equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                        frame))))
                path)))
      *enotdir*))
    :use
    ((:instance
      intersectp-member
      (a
       (fat32-filename-fix
        (car
         (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                         frame))))
                 path))))
      (y (names-at (abs-fs-fix root)
                   (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                      frame)))))
      (x (names-at (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                     frame)))
                   nil)))
     (:instance
      abs-find-file-correctness-1-lemma-6
      (fs (abs-fs-fix root))
      (n (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                 frame)))))
      (path (fat32-filename-list-fix path)))
     (:instance
      (:rewrite abs-find-file-correctness-1-lemma-18)
      (path
       (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                       frame))))
               path))
      (fs (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame))))))
    :expand
    (abs-find-file-helper
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                     frame))))
             path)))
   (if
       (not stable-under-simplificationp)
       nil
     '(:expand (names-at (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                           frame)))
                         nil)))))

(local
 (defthm
   abs-find-file-correctness-lemma-10
   (implies (and (abs-fs-p fs)
                 (fat32-filename-list-p path)
                 (not (equal (mv-nth 1 (abs-find-file-helper fs path))
                             *enoent*)))
            (member-equal (car path)
                          (remove-equal nil (strip-cars fs))))
   :hints (("goal" :in-theory (enable abs-find-file-helper)))))

(local
 (defthm
   abs-find-file-correctness-lemma-18
   (implies (and (fat32-filename-list-p path)
                 (not (equal (mv-nth 1
                                     (abs-find-file-helper (abs-fs-fix fs)
                                                           path))
                             *enoent*)))
            (member-equal (car path)
                          (names-at fs nil)))
   :hints (("goal" :in-theory (e/d (names-at)
                                   (abs-find-file-correctness-lemma-10))
            :use (:instance abs-find-file-correctness-lemma-10
                            (fs (abs-fs-fix fs)))))))

(encapsulate
  ()

  (local
   (defthm
     lemma
     (implies
      (and
       (member-equal (car (fat32-filename-list-fix path))
                     (names-at root nil))
       (not (equal (mv-nth 1 (abs-find-file-helper root path))
                   0))
       (ctx-app-ok root (1st-complete frame)
                   (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                      frame))))
       (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                (fat32-filename-list-fix path))
       (not (equal (mv-nth 1 (abs-find-file-helper root path))
                   2)))
      (member-equal
       (nth (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                    frame))))
            (fat32-filename-list-fix path))
       (names-at root
                 (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                    frame))))))
     :hints
     (("goal"
       :do-not-induct t
       :in-theory (e/d (names-at abs-find-file-helper)
                       (nthcdr-of-fat32-filename-list-fix
                        nth-of-fat32-filename-list-fix
                        (:rewrite abs-find-file-correctness-lemma-10)))
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
               (fat32-filename-list-fix path))
      (not (equal (mv-nth 1 (abs-find-file-helper (abs-fs-fix root) path))
                  2))
      (dist-names root nil frame))
     (equal
      (abs-find-file-helper
       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                         frame)))
       (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                       frame))))
               path))
      (mv (abs-file-fix nil) *enoent*)))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (e/d (abs-find-file-helper)
                      (nthcdr-of-fat32-filename-list-fix
                       nth-of-fat32-filename-list-fix
                       (:rewrite abs-find-file-correctness-lemma-18)
                       intersectp-member))
      :use
      ((:instance
        (:rewrite abs-find-file-correctness-lemma-18)
        (fs (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                              frame))))
        (path
         (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                         frame))))
                 (fat32-filename-list-fix path))))
       (:instance (:rewrite abs-find-file-correctness-lemma-18)
                  (fs (abs-fs-fix root))
                  (path (fat32-filename-list-fix path)))
       (:instance
        intersectp-member
        (a
         (car
          (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                          frame))))
                  (fat32-filename-list-fix path))))
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
                    path)))
          2))
        (abs-file-alist-p (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                            frame))))
        (equal (mv-nth 1 (abs-find-file-helper root path))
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
                    path)))
          2))
        (abs-file-alist-p (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                            frame))))
        (not (equal (mv-nth 1 (abs-find-file-helper root path))
                    0))))))))

(local
 (defthm
   abs-find-file-correctness-lemma-11
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
      (fat32-filename-list-fix path))
     (not (equal (mv-nth 1
                         (abs-find-file-helper (frame->root frame)
                                               path))
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
       path))
     (mv (abs-file-fix nil) *enoent*)))
   :hints
   (("goal"
     :in-theory (e/d (collapse-this)
                     ((:rewrite abs-find-file-helper-when-m1-file-alist-p)))
     :use
     ((:instance
       (:rewrite abs-find-file-helper-when-m1-file-alist-p)
       (path
        (nthcdr (len (frame-val->path
                      (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame)))))
                path))
       (fs
        (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))))
      (:instance (:rewrite abs-find-file-correctness-1-lemma-7)
                 (root (frame->root frame))
                 (path path)
                 (frame (frame->frame frame))))))))

(defthm
  abs-find-file-correctness-1-lemma-37
  (implies
   (and (abs-fs-p fs)
        (fat32-filename-list-p path)
        (not (equal (mv-nth 1
                            (abs-find-file-helper fs (nthcdr n path)))
                    *enoent*)))
   (member-equal (nth n path)
                 (remove-equal nil (strip-cars fs))))
  :hints (("goal" :do-not-induct t
           :in-theory (disable abs-find-file-correctness-lemma-10
                               nth-of-nthcdr)
           :use ((:instance abs-find-file-correctness-lemma-10
                            (path (nthcdr n path)))
                 (:instance nth-of-nthcdr (n 0)
                            (m n)
                            (x path))))))

(defthmd
  abs-find-file-correctness-1-lemma-26
  (implies
   (and (fat32-filename-list-p path)
        (not (equal (mv-nth 1
                            (abs-find-file-helper (abs-fs-fix fs)
                                                  (nthcdr n path)))
                    *enoent*)))
   (member-equal (nth n path)
                 (names-at fs nil)))
  :hints (("goal" :in-theory (e/d (names-at)
                                  (abs-find-file-correctness-1-lemma-37))
           :use (:instance abs-find-file-correctness-1-lemma-37
                           (fs (abs-fs-fix fs))))))

(defthm
  abs-find-file-correctness-1-lemma-19
  (implies
   (and
    (fat32-filename-list-p path)
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
        path)))
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
       path))
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
     (path
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
        path)))
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
                                          frame))))))
    :in-theory (enable fat32-filename-list-prefixp-alt))))

(defthm
  abs-find-file-correctness-1-lemma-57
  (implies
   (and
    (fat32-filename-list-p path)
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
        path)))
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
       path))
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
    (fat32-filename-list-p path)
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
        path)))
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
      (fat32-filename-list-fix path)))
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
        (fat32-filename-list-fix path)))
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
          path))
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
        (fat32-filename-list-fix path)))
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
         path))))
     (:instance
      (:rewrite abs-find-file-correctness-1-lemma-6)
      (fs
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (path
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
         path)))
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
         (fat32-filename-list-fix path))))
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
        (fat32-filename-list-fix path)))
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
         (fat32-filename-list-fix path))))
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
            path))
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
        path))))
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
             (fat32-filename-list-fix path)))
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
      path))
    (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (take-of-nthcdr abs-find-file-helper len-of-fat32-filename-list-fix)
                    (nthcdr-of-fat32-filename-list-fix
                     (:rewrite abs-find-file-correctness-1-lemma-18)
                     (:rewrite abs-find-file-correctness-1-lemma-57)))
    :use
    ((:instance
      (:rewrite abs-find-file-correctness-1-lemma-18)
      (path
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        path))
      (fs
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame)))))
     (:instance (:rewrite abs-separate-correctness-1-lemma-41)
                (path (fat32-filename-list-fix path)))
     (:instance (:rewrite abs-find-file-correctness-1-lemma-57)
                (path (fat32-filename-list-fix path)))))))

;; Can't be made local.
(defthm
  abs-find-file-correctness-lemma-16
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
             (fat32-filename-list-fix path))
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
                path)))
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
      path))
    (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (e/d
     (take-of-nthcdr abs-find-file-helper
                     abs-addrs-of-ctx-app-lemma-2)
     (nthcdr-of-fat32-filename-list-fix
      abs-separate-of-frame->frame-of-collapse-this-lemma-3
      (:rewrite abs-find-file-correctness-1-lemma-6)
      (:congruence
       fat32-filename-list-equiv-implies-fat32-filename-list-equiv-take-2)
      intersectp-member))
    :use
    ((:instance abs-separate-of-frame->frame-of-collapse-this-lemma-3
                (x (1st-complete frame))
                (y (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                     frame)))))
     (:instance
      intersectp-member
      (a
       (car
        (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                        frame))))
                (fat32-filename-list-fix path))))
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
      (path
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        (fat32-filename-list-fix path)))
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
      (path (fat32-filename-list-fix path))
      (n (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                 frame))))))
     (:instance (:rewrite abs-find-file-correctness-1-lemma-55)
                (path (fat32-filename-list-fix path)))))))

(local
 (defthm
   abs-find-file-correctness-lemma-20
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
              (fat32-filename-list-fix path))
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
          path)))
       *enoent*)))
    (equal
     (abs-find-file-helper
      (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                        frame)))
      (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                      frame))))
              path))
     (mv (abs-file-fix nil) *enoent*)))
   :hints (("goal" :in-theory (disable abs-find-file-correctness-lemma-16)
            :use abs-find-file-correctness-lemma-16))))

(defthm
  abs-find-file-correctness-lemma-33
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
             (fat32-filename-list-fix path))
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
         path)))
      *enoent*)))
   (equal
    (abs-find-file-helper
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                     frame))))
             path))
    (mv (abs-file-fix nil) *enoent*)))
  :hints (("goal" :do-not-induct t)))

(encapsulate
  ()

  (local
   (defun
       induction-scheme (frame path x)
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
        path
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
        path x))
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
        path x))
      (t (mv frame path x)))))

  ;; Important - states that when we have the collapse property, we can't have
  ;; any frame other than the root with stuff in it if the root has stuff in it.
  (defthmd
    abs-find-file-correctness-1-lemma-36
    (implies
     (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
          (frame-p (frame->frame frame))
          (mv-nth 1 (collapse frame))
          (consp (assoc-equal x (frame->frame frame)))
          (prefixp (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
                   (fat32-filename-list-fix path))
          (not (equal (mv-nth 1
                              (abs-find-file-helper (frame->root frame)
                                                    path))
                      *enoent*))
          (dist-names (frame->root frame)
                      nil (frame->frame frame))
          (abs-separate (frame->frame frame)))
     (equal
      (abs-find-file-helper
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
       (nthcdr
        (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
        path))
      (mv (abs-file-fix nil) *enoent*)))
    :hints (("goal" :induct (induction-scheme frame path x)
             :in-theory
             (enable collapse len-of-fat32-filename-list-fix)))))

(local
 (defthm
   abs-find-file-correctness-lemma-8
   (implies
    (and
     (abs-complete (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
     (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            0)
     (equal (mv-nth 1
                    (abs-find-file-helper (frame->root (collapse-this frame x))
                                          path))
            2)
     (ctx-app-ok (frame->root frame)
                 x
                 (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
     (prefixp (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
              (fat32-filename-list-fix path))
     (dist-names (frame->root frame)
                 nil (frame->frame frame)))
    (equal
     (hifat-find-file
      (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
      (nthcdr
       (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
       path))
     (mv (abs-file-fix nil) 2)))
   :hints
   (("goal"
     :in-theory (e/d (collapse-this)
                     (abs-find-file-helper-when-m1-file-alist-p))
     :use
     ((:instance
       (:rewrite abs-find-file-helper-when-m1-file-alist-p)
       (path
        (nthcdr
         (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
         path))
       (fs (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))))
      (:instance
       (:rewrite abs-find-file-helper-of-ctx-app-lemma-4)
       (path
        (nthcdr
         (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
         path))
       (fs (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))))))

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
             (fat32-filename-list-fix path))
    (prefixp (frame-val->path (cdr (assoc-equal y frame)))
             (fat32-filename-list-fix path))
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
                path)))
      *enoent*))
    (atom (assoc-equal 0 frame)))
   (equal (abs-find-file-helper
           (frame-val->dir (cdr (assoc-equal y frame)))
           (nthcdr (len (frame-val->path (cdr (assoc-equal y frame))))
                   path))
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

(local
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
      (fat32-filename-list-fix path))
     (prefixp (frame-val->path (cdr (assoc-equal y (frame->frame frame))))
              (fat32-filename-list-fix path))
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
          path)))
       2)))
    (equal
     (abs-find-file-helper
      (frame-val->dir (cdr (assoc-equal y (frame->frame frame))))
      (nthcdr
       (len (frame-val->path (cdr (assoc-equal y (frame->frame frame)))))
       path))
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
                 (frame (frame->frame frame))))))))

(local
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
              (fat32-filename-list-fix path))
     (prefixp
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
      (fat32-filename-list-fix path))
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
          path)))
       2)))
    (equal
     (abs-find-file-helper
      (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))
      (nthcdr
       (len
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame)))))
       path))
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
       (path
        (nthcdr (len (frame-val->path
                      (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame)))))
                path))
       (fs
        (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))))))))

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

  ;; The induction scheme and subgoals were a drag, but this is important
  ;; because it helps reason about two different variables in a frame.
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
               (fat32-filename-list-fix path))
      (prefixp (frame-val->path (cdr (assoc-equal y (frame->frame frame))))
               (fat32-filename-list-fix path))
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
           path)))
        2)))
     (equal
      (abs-find-file-helper
       (frame-val->dir (cdr (assoc-equal y (frame->frame frame))))
       (nthcdr
        (len (frame-val->path (cdr (assoc-equal y (frame->frame frame)))))
        path))
      (mv (abs-file-fix nil) *enoent*)))
    :hints (("goal" :induct (induction-scheme frame x y)
             :in-theory (e/d (collapse len-of-fat32-filename-list-fix)
                             ((:rewrite abs-addrs-when-m1-file-alist-p)
                              (:rewrite
                               abs-find-file-of-put-assoc-lemma-7 . 1)
                              (:rewrite prefixp-when-equal-lengths)
                              (:rewrite abs-find-file-of-remove-assoc-1)
                              (:rewrite nthcdr-when->=-n-len-l)
                              (:rewrite prefixp-one-way-or-another . 1)
                              (:definition remove-equal)
                              (:rewrite abs-file-alist-p-correctness-1)
                              (:rewrite remove-when-absent)
                              (:definition member-equal)))))))

(local
 (defthmd
   abs-find-file-correctness-lemma-13
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
              (fat32-filename-list-fix path))
     (dist-names root nil frame)
     (abs-separate frame)
     (not
      (equal
       (mv-nth 1
               (abs-find-file-helper
                (frame-val->dir (cdr (assoc-equal x frame)))
                (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                        path)))
       *enoent*)))
    (equal (abs-find-file-alt frame indices path)
           (mv (abs-file-fix nil) *enoent*)))
   :hints
   (("goal" :induct (abs-find-file-alt frame indices path)
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
             (fat32-filename-list-fix path))
    (abs-separate frame)
    (not
     (equal
      (mv-nth 1
              (abs-find-file-helper
               (frame-val->dir (cdr (assoc-equal x frame)))
               (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                       path)))
      *enoent*))
    (no-duplicatesp-equal (strip-cars frame)))
   (equal (abs-find-file (remove-assoc-equal x frame)
                         path)
          (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal"
    :use (:instance abs-find-file-correctness-lemma-13
                    (indices (remove-equal x (strip-cars frame))))
    :do-not-induct t)))

(local
 (defthm
   abs-find-file-correctness-lemma-27
   (implies
    (and
     (prefixp
      (frame-val->path
       (cdr
        (assoc-equal
         (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (frame->frame frame))))
      (fat32-filename-list-fix path))
     (not
      (equal
       (mv-nth
        1
        (abs-find-file-helper
         (frame-val->dir
          (cdr (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame))))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (frame->frame frame)))))
          path)))
       2))
     (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
     (consp
      (assoc-equal
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (frame->frame frame)))
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
     (mv-nth
      1
      (collapse
       (frame-with-root
        (frame->root frame)
        (put-assoc-equal
         (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (frame-val
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src
                  (cdr (assoc-equal (1st-complete (frame->frame frame))
                                    (frame->frame frame))))
                 (frame->frame frame))))
          (ctx-app
           (frame-val->dir
            (cdr
             (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (frame->frame frame))))
           (frame-val->dir
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
           (1st-complete (frame->frame frame))
           (nthcdr
            (len
             (frame-val->path
              (cdr
               (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame)))))
            (frame-val->path
             (cdr (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame))))))
          (frame-val->src
           (cdr (assoc-equal
                 (frame-val->src
                  (cdr (assoc-equal (1st-complete (frame->frame frame))
                                    (frame->frame frame))))
                 (frame->frame frame)))))
         (remove-assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
     (frame-p frame)
     (no-duplicatesp-equal (strip-cars frame))
     (abs-separate frame))
    (equal
     (abs-find-file
      (remove-assoc-equal
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (frame->frame frame))
      path)
     (mv (abs-file-fix nil) *enoent*)))
   :hints
   (("goal"
     :in-theory (e/d (collapse collapse-this)
                     ((:rewrite abs-find-file-correctness-1-lemma-48)
                      (:definition remove-assoc-equal)
                      (:rewrite abs-addrs-when-m1-file-alist-p)
                      (:definition member-equal)
                      (:rewrite assoc-after-put-assoc)
                      (:definition assoc-equal)
                      (:rewrite strip-cars-of-put-assoc)
                      (:rewrite strip-cars-of-remove-assoc)
                      (:rewrite remove-when-absent)
                      (:definition remove-equal)))
     :use
     ((:instance (:rewrite abs-find-file-of-remove-assoc-lemma-3)
                 (path path)
                 (frame (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))
      (:instance
       (:rewrite abs-find-file-correctness-1-lemma-48)
       (path path)
       (frame (frame->frame frame))
       (x (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
       (root (frame->root frame))))))))

(defthm
  abs-find-file-correctness-lemma-17
  (implies
   (and
    (equal (mv-nth 1
                   (abs-find-file-helper (frame->root frame)
                                         path))
           2)
    (prefixp
     (frame-val->path
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (fat32-filename-list-fix path))
    (equal
     (mv-nth
      1
      (abs-find-file-helper
       (frame-val->dir
        (cdr (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (frame->frame frame))))
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame)))))
        path)))
     0)
    (prefixp
     (fat32-filename-list-fix path)
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame)))))
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
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
    (mv-nth
     1
     (collapse
      (frame-with-root
       (frame->root frame)
       (put-assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame-val
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame))))
         (ctx-app
          (frame-val->dir
           (cdr
            (assoc-equal
             (frame-val->src
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))
             (frame->frame frame))))
          (frame-val->dir
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
          (1st-complete (frame->frame frame))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src
                (cdr (assoc-equal (1st-complete (frame->frame frame))
                                  (frame->frame frame))))
               (frame->frame frame)))))
           (frame-val->path
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))
         (frame-val->src
          (cdr (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame)))))
        (remove-assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-separate frame)
    (abs-complete
     (abs-file->contents (mv-nth 0 (abs-find-file frame path)))))
   (equal
    (cons
     (abs-file
      (abs-file->d-e (mv-nth 0 (abs-find-file frame path)))
      (ctx-app
       (abs-file->contents (mv-nth 0 (abs-find-file frame path)))
       (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (1st-complete (frame->frame frame))
       (nthcdr
        (len path)
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame)))))))
     '(0))
    (abs-find-file frame path)))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d nil
                           (abs-find-file-of-put-assoc-lemma-7))
           :use
           (:instance
            (:rewrite abs-find-file-of-put-assoc-lemma-6)
            (path path)
            (frame (frame->frame frame))
            (x (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                                 (frame->frame frame)))))))))

(defthm
  abs-find-file-correctness-lemma-14
  (implies
   (and (consp (assoc-equal x frame))
        (equal (mv-nth 1 (abs-find-file frame path))
               *enoent*)
        (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                 (fat32-filename-list-fix path)))
   (equal (abs-find-file-helper
           (frame-val->dir (cdr (assoc-equal x frame)))
           (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                   path))
          (mv (abs-file-fix nil) *enoent*)))
  :hints (("goal" :in-theory (enable abs-find-file))))

(local
 (defthm
   abs-find-file-correctness-lemma-31
   (implies
    (and
     (equal (mv-nth 1
                    (abs-find-file-helper (frame->root frame)
                                          path))
            2)
     (prefixp
      (frame-val->path
       (cdr
        (assoc-equal
         (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (frame->frame frame))))
      (fat32-filename-list-fix path))
     (equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir
         (cdr (assoc-equal
               (frame-val->src
                (cdr (assoc-equal (1st-complete (frame->frame frame))
                                  (frame->frame frame))))
               (frame->frame frame))))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src
                  (cdr (assoc-equal (1st-complete (frame->frame frame))
                                    (frame->frame frame))))
                 (frame->frame frame)))))
         path)))
      0)
     (prefixp
      (fat32-filename-list-fix path)
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
     (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
     (< 0 (1st-complete (frame->frame frame)))
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
     (abs-separate frame)
     (equal (mv-nth 1 (abs-find-file frame path))
            2))
    (equal (abs-find-file frame path)
           (mv (abs-file-fix nil) *enoent*)))
   :hints
   (("goal" :do-not-induct t
     :use (:instance (:rewrite abs-find-file-of-put-assoc-lemma-6)
                     (x (1st-complete (frame->frame frame)))
                     (path path)
                     (frame (frame->frame frame)))))))

;; This can't be made local.
(defthm
  abs-find-file-correctness-lemma-24
  (implies
   (and
    (prefixp
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))
     (fat32-filename-list-fix path))
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
         path)))
      2))
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (< 0 (1st-complete (frame->frame frame)))
    (consp
     (assoc-equal
      (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))
      (frame->frame frame)))
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
    (mv-nth
     1
     (collapse
      (frame-with-root
       (frame->root frame)
       (put-assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame-val
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame))))
         (ctx-app
          (frame-val->dir
           (cdr
            (assoc-equal
             (frame-val->src
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))
             (frame->frame frame))))
          (frame-val->dir
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
          (1st-complete (frame->frame frame))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src
                (cdr (assoc-equal (1st-complete (frame->frame frame))
                                  (frame->frame frame))))
               (frame->frame frame)))))
           (frame-val->path
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))
         (frame-val->src
          (cdr (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame)))))
        (remove-assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-separate frame))
   (equal
    (abs-find-file (remove-assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))
                   path)
    (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal" :in-theory (e/d (collapse collapse-this)
                           ((:definition remove-equal)
                            (:rewrite remove-when-absent)
                            (:rewrite strip-cars-of-remove-assoc)
                            (:rewrite strip-cars-of-put-assoc)
                            (:definition assoc-equal)
                            (:rewrite assoc-after-put-assoc)
                            (:definition member-equal)
                            (:rewrite abs-find-file-correctness-lemma-16)))
    :use ((:instance
           (:rewrite abs-find-file-of-remove-assoc-lemma-3)
           (path path)
           (frame
            (remove-assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))
          (:instance (:rewrite abs-find-file-correctness-1-lemma-48)
                     (path path)
                     (frame (frame->frame frame))
                     (x (1st-complete (frame->frame frame)))
                     (root (frame->root frame)))))))

(defthm
  abs-find-file-correctness-lemma-12
  (implies (equal (mv-nth 1
                          (abs-find-file-helper (frame->root frame)
                                                path))
                  *enoent*)
           (equal (abs-find-file-helper (frame->root frame)
                                        path)
                  (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal"
    :in-theory (disable (:rewrite abs-find-file-helper-of-ctx-app-lemma-4))
    :use ((:instance (:rewrite abs-find-file-helper-of-ctx-app-lemma-4)
                     (path path)
                     (fs (frame->root frame)))))))

(defthm
  abs-find-file-correctness-lemma-2
  (implies
   (and (frame-p frame)
        (no-duplicatesp-equal (strip-cars frame))
        (consp (assoc-equal 0 frame))
        (equal (mv-nth 1
                       (abs-find-file (frame->frame frame)
                                      path))
               *enoent*))
   (equal (abs-find-file frame path)
          (if (prefixp (frame-val->path (cdr (assoc-equal 0 frame)))
                       (fat32-filename-list-fix path))
              (abs-find-file-helper
               (frame->root frame)
               (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                       path))
              (mv (abs-file-fix nil) *enoent*))))
  :hints
  (("goal" :in-theory (e/d (frame->root frame->frame))
    :use (:instance (:rewrite abs-find-file-of-put-assoc-lemma-6)
                    (x 0)))))

(local
 (defthm
   abs-find-file-correctness-lemma-5
   (implies (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                 (mv-nth 1 (collapse frame))
                 (frame-p (frame->frame frame))
                 (subsetp-equal indices
                                (strip-cars (frame->frame frame)))
                 (dist-names (frame->root frame)
                             nil (frame->frame frame))
                 (abs-separate (frame->frame frame))
                 (not (equal (mv-nth 1
                                     (abs-find-file-helper (frame->root frame)
                                                           path))
                             *enoent*)))
            (equal (abs-find-file-alt (frame->frame frame)
                                      indices path)
                   (mv (abs-file-fix nil) *enoent*)))
   :hints
   (("goal" :induct (abs-find-file-alt (frame->frame frame)
                                       indices path)
     :in-theory (enable abs-find-file-alt))
    ("subgoal *1/2''" :use (:instance abs-find-file-correctness-1-lemma-36
                                      (x (car indices)))))))

(defthm
  abs-find-file-correctness-lemma-6
  (implies (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (mv-nth 1 (collapse frame))
                (frame-p (frame->frame frame))
                (dist-names (frame->root frame)
                            nil (frame->frame frame))
                (abs-separate (frame->frame frame))
                (not (equal (mv-nth 1
                                    (abs-find-file-helper (frame->root frame)
                                                          path))
                            2)))
           (equal (abs-find-file (frame->frame frame)
                                 path)
                  (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal" :in-theory (disable abs-find-file-correctness-lemma-5)
    :use (:instance abs-find-file-correctness-lemma-5
                    (indices (strip-cars (frame->frame frame)))))))

(defthm
  abs-find-file-correctness-lemma-22
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
     (fat32-filename-list-fix path))
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
         path)))
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
                   path)
    (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal" :in-theory (enable collapse collapse-this)
    :use (:instance (:rewrite abs-find-file-correctness-1-lemma-48)
                    (frame (frame->frame frame))
                    (x (1st-complete (frame->frame frame)))
                    (root (frame->root frame))))))

(defthm abs-find-file-correctness-lemma-9
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

(defthm abs-find-file-correctness-lemma-26
  (implies
   (and
    (m1-regular-file-p (mv-nth 0 (abs-find-file frame path)))
    (prefixp
     (frame-val->path
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (fat32-filename-list-fix path))
    (equal
     (abs-find-file-helper
      (frame-val->dir
       (cdr
        (assoc-equal
         (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (frame->frame frame))))
      (nthcdr
       (len
        (frame-val->path
         (cdr (assoc-equal
               (frame-val->src
                (cdr (assoc-equal (1st-complete (frame->frame frame))
                                  (frame->frame frame))))
               (frame->frame frame)))))
       path))
     (abs-find-file frame path))
    (prefixp
     (fat32-filename-list-fix path)
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))))
   (not
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
                                         (frame->frame frame))))))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (abs-find-file collapse
                    abs-complete-when-atom-abs-addrs
                    len-of-fat32-filename-list-fix)
     ((:definition remove-equal)
      (:definition assoc-equal)
      (:definition member-equal)
      (:definition remove-assoc-equal)
      (:rewrite abs-file-alist-p-correctness-1)
      (:rewrite nthcdr-when->=-n-len-l)
      (:definition strip-cars)
      abs-find-file-helper-of-collapse-2
      (:rewrite abs-find-file-of-put-assoc)
      (:rewrite consp-of-nthcdr)
      (:rewrite abs-find-file-helper-when-atom)
      (:rewrite prefixp-one-way-or-another . 1)
      (:rewrite abs-find-file-correctness-lemma-14)
      (:rewrite len-when-prefixp)
      (:rewrite put-assoc-equal-without-change . 2)
      (:rewrite no-duplicatesp-of-strip-cars-when-hifat-no-dups-p)
      (:type-prescription assoc-when-zp-len)
      (:rewrite
       collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-2)
      (:definition len)
      (:rewrite abs-no-dups-p-of-put-assoc-equal)
      (:definition put-assoc-equal)
      (:rewrite abs-no-dups-p-of-cdr)
      (:rewrite abs-find-file-correctness-1-lemma-43)))
    :use (:instance (:rewrite abs-find-file-correctness-1-lemma-43)
                    (path path)
                    (frame (frame->frame frame))))))

(defthm
  abs-find-file-correctness-lemma-40
  (implies
   (and (frame-p (frame->frame frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (consp (assoc-equal x (frame->frame frame)))
        (not (equal z *enoent*))
        (prefixp (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
                 (fat32-filename-list-fix path))
        (mv-nth 1 (collapse frame))
        (dist-names (frame->root frame)
                    nil (frame->frame frame))
        (abs-separate (frame->frame frame)))
   (iff
    (equal
     (mv-nth
      1
      (abs-find-file-helper
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
       (nthcdr
        (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
        path)))
     z)
    (and
     (equal
      (abs-find-file-helper
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
       (nthcdr
        (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
        path))
      (abs-find-file (frame->frame frame)
                     path))
     (equal (mv-nth 1
                    (abs-find-file (frame->frame frame)
                                   path))
            z))))
  :hints (("goal" :do-not-induct t
           :use (:instance abs-find-file-correctness-1-lemma-48
                           (frame (frame->frame frame))
                           (root (frame->root frame))))))

(defthm
  abs-find-file-correctness-lemma-37
  (implies
   (and
    (frame-p (put-assoc-equal name val frame))
    (no-duplicatesp-equal (strip-cars (put-assoc-equal name val frame)))
    (mv-nth
     1
     (collapse (frame-with-root root (put-assoc-equal name val frame))))
    (dist-names root
                nil (put-assoc-equal name val frame))
    (abs-separate (put-assoc-equal name val frame))
    (not (zp name))
    (atom (assoc-equal 0 frame)))
   (equal
    (abs-find-file (put-assoc-equal name val frame)
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
        2)))
     (abs-find-file-helper (frame-val->dir val)
                           (nthcdr (len (frame-val->path val))
                                   path))
     (abs-find-file (remove-assoc-equal name frame)
                    path))))
  :hints
  (("goal" :do-not-induct t
    :in-theory
    (e/d (fat32-filename-list-prefixp-alt remove-assoc-of-put-assoc)
         (abs-find-file-of-put-assoc))
    :use ((:instance abs-find-file-correctness-1-lemma-48
                     (x name)
                     (frame (put-assoc-equal name val frame))
                     (root root))
          abs-find-file-of-put-assoc))))

;; Seriously, let's not mess around with the structure of this proof - it's
;; actually a good thing for redundant computation to be avoided.
(encapsulate
  ()

  (local
   (in-theory
    (e/d
     (abs-find-file collapse
                    abs-complete-when-atom-abs-addrs
                    len-of-fat32-filename-list-fix)
     ((:definition remove-equal)
      (:definition assoc-equal)
      (:definition member-equal)
      (:definition remove-assoc-equal)
      (:rewrite abs-file-alist-p-correctness-1)
      (:rewrite nthcdr-when->=-n-len-l)
      (:definition strip-cars)
      abs-find-file-helper-of-collapse-2
      (:rewrite abs-find-file-of-put-assoc)
      (:rewrite consp-of-nthcdr)
      (:rewrite abs-find-file-helper-when-atom)
      (:rewrite prefixp-one-way-or-another . 1)
      (:rewrite abs-find-file-correctness-lemma-14)
      (:rewrite len-when-prefixp)
      (:rewrite put-assoc-equal-without-change . 2)
      (:rewrite no-duplicatesp-of-strip-cars-when-hifat-no-dups-p)
      (:type-prescription assoc-when-zp-len)
      (:rewrite
       collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-2)
      (:definition len)
      (:rewrite abs-no-dups-p-of-put-assoc-equal)
      (:definition put-assoc-equal)
      (:rewrite abs-no-dups-p-of-cdr)))))

  (defthm
    abs-find-file-correctness-2
    (implies
     (and (consp (assoc-equal 0 frame))
          (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
          (mv-nth 1 (collapse frame))
          (frame-p frame)
          (no-duplicatesp-equal (strip-cars frame))
          (subsetp-equal (abs-addrs (frame->root frame))
                         (frame-addrs-root (frame->frame frame)))
          (abs-separate frame))
     (and
      (implies
       (abs-complete (abs-file->contents (mv-nth 0 (abs-find-file frame path))))
       (equal (abs-find-file frame path)
              (hifat-find-file (mv-nth 0 (collapse frame))
                               path)))
      (equal (mv-nth 1 (abs-find-file frame path))
             (mv-nth 1
                     (hifat-find-file (mv-nth 0 (collapse frame))
                                      path)))
      (equal
       (m1-regular-file-p (mv-nth 0 (abs-find-file frame path)))
       (m1-regular-file-p (mv-nth 0
                                  (hifat-find-file (mv-nth 0 (collapse frame))
                                                   path))))))
    :hints
    (("goal" :induct (collapse frame) :do-not-induct t
      :in-theory (enable fat32-filename-list-prefixp-alt))
     (if (not stable-under-simplificationp)
         nil
       '(:in-theory (enable collapse-this fat32-filename-list-prefixp-alt)
                    :do-not-induct t
                    :expand
                    ((:with abs-find-file-of-remove-assoc-1
                            (abs-find-file
                             (remove-assoc-equal (1st-complete (frame->frame frame))
                                                 (frame->frame frame))
                             path))))))))
