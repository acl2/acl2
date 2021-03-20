;  partial-collapse.lisp                                Mihir Mehta

; Here we define some things for proof purposes which we make local to prevent
; them from taking up time and space in other files.

(in-package "ACL2")

(include-book "../abs-separate")
(local (include-book "std/lists/prefixp" :dir :system))
(local (include-book "std/lists/intersection" :dir :system))

(local
 (in-theory (disable (:definition true-listp)
                     (:definition string-listp)
                     (:definition integer-listp)
                     (:definition acl2-number-listp)
                     (:rewrite nat-listp-of-remove)
                     (:definition rational-listp)
                     (:rewrite take-when-atom)
                     (:rewrite take-of-take-split)
                     ;; Disabling this because it's defined in terms of helper
                     ;; functions and stuff.
                     position)))

(local
 (in-theory
  (disable
   nat-listp-if-fat32-masked-entry-list-p
   (:rewrite m1-directory-file-p-when-m1-file-p)
   (:rewrite absfat-equiv-implies-set-equiv-addrs-at-1-lemma-2)
   (:rewrite abs-file->contents-when-m1-file-p)
   (:rewrite hifat-find-file-correctness-1-lemma-1)
   (:rewrite abs-addrs-when-m1-file-contents-p)
   (:rewrite
    fat32-filename-list-p-of-cdr-when-fat32-filename-list-p)
   (:rewrite assoc-of-car-when-member)
   (:rewrite no-duplicatesp-of-strip-cars-when-hifat-no-dups-p)
   (:rewrite m1-file-alist-p-when-subsetp-equal)
   (:rewrite abs-no-dups-p-when-m1-file-alist-p)
   (:rewrite m1-file-alist-p-when-not-consp)
   (:rewrite m1-file-contents-p-correctness-1)
   (:rewrite abs-directory-file-p-correctness-1)
   (:rewrite m1-directory-file-p-correctness-1)
   (:rewrite m1-directory-file-p-correctness-1))))

(defund 1st-complete-under-path (frame path)
  (declare (xargs :guard (and (frame-p frame)
                              (fat32-filename-list-p path))))
  (b* ((path (mbe :exec path :logic (fat32-filename-list-fix path)))
       ((when (atom frame)) 0)
       (head-index (caar frame))
       (head-frame-val (cdar frame)))
    (if (and (abs-complete (frame-val->dir head-frame-val))
             (prefixp path (frame-val->path head-frame-val)))
        (mbe :exec head-index :logic (nfix head-index))
      (1st-complete-under-path (cdr frame) path))))

(defthm
  1st-complete-under-path-correctness-1
  (implies (not (zp (1st-complete-under-path frame path)))
           (consp (assoc-equal (1st-complete-under-path frame path)
                               frame)))
  :hints (("goal" :in-theory (enable 1st-complete-under-path)))
  :rule-classes :type-prescription)

(defthmd
  1st-complete-under-path-of-fat32-filename-list-fix
  (equal (1st-complete-under-path frame (fat32-filename-list-fix path))
         (1st-complete-under-path frame path))
  :hints (("goal" :in-theory (enable 1st-complete-under-path))))

(defcong
  fat32-filename-list-equiv equal
  (1st-complete-under-path frame path)
  2
  :hints
  (("goal"
    :in-theory (enable fat32-filename-list-equiv)
    :use
    ((:instance
      1st-complete-under-path-of-fat32-filename-list-fix
      (path path-equiv))
     1st-complete-under-path-of-fat32-filename-list-fix))))

(defthm 1st-complete-under-path-when-atom-1
  (implies (atom path)
           (equal (1st-complete-under-path frame path)
                  (1st-complete frame)))
  :hints (("goal" :in-theory (enable 1st-complete-under-path
                                     1st-complete prefixp))))

(defthm 1st-complete-under-path-of-put-assoc-lemma-1
  (implies (fat32-filename-list-p y)
   (and
    (implies (prefixp (fat32-filename-list-fix x) y)
             (fat32-filename-list-prefixp x y))
    (implies (not (prefixp (fat32-filename-list-fix x) y))
             (not (fat32-filename-list-prefixp x y)))))
  :hints (("goal" :induct (fat32-filename-list-prefixp x y))))

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
              (fat32-filename-list-prefixp path (frame-val->path val)))))
   (equal (1st-complete-under-path (put-assoc-equal name val frame)
                                   path)
          (1st-complete-under-path (remove-assoc-equal name frame)
                                   path)))
  :hints (("goal" :in-theory (enable 1st-complete-under-path))))

;; Trying to refactor this around "path" instead of "pathname" messes things up
;; because path and pathname are both variables.
(defund
  partial-collapse (frame pathname)
  (declare (xargs :guard (and (frame-p frame)
                              (consp (assoc-equal 0 frame))
                              (fat32-filename-list-p pathname))
                  :measure (len (frame->frame frame))))
  (b*
      (((when (atom (frame->frame frame)))
        frame)
       (head-index
        (1st-complete-under-path (frame->frame frame)
                                 pathname))
       ((when (zp head-index)) frame)
       (head-frame-val
        (cdr (assoc-equal head-index (frame->frame frame))))
       (src
        (frame-val->src
         (cdr
          (assoc-equal
           head-index
           (frame->frame frame))))))
    (if
        (zp src)
        (b*
            (((unless (ctx-app-ok (frame->root frame)
                                  head-index
                                  (frame-val->path head-frame-val)))
              frame))
          (partial-collapse (collapse-this frame head-index)
                            pathname))
      (b*
          ((path (frame-val->path head-frame-val))
           ((when (or (equal src head-index)
                      (atom (assoc-equal src (frame->frame frame)))))
            frame)
           (src-path
            (frame-val->path
             (cdr (assoc-equal src (frame->frame frame)))))
           (src-dir
            (frame-val->dir
             (cdr (assoc-equal src (frame->frame frame)))))
           ((unless (and (prefixp src-path path)
                         (ctx-app-ok src-dir head-index
                                     (nthcdr (len src-path) path))))
            frame))
        (partial-collapse (collapse-this frame head-index)
                          pathname)))))

(defthm frame-p-of-partial-collapse
  (implies (frame-p frame)
           (frame-p (partial-collapse frame path)))
  :hints (("goal" :in-theory (enable partial-collapse))))

(defthm
  partial-collapse-when-atom
  (implies (and (mv-nth 1 (collapse frame))
                (atom path))
           (equal (partial-collapse frame path)
                  (if (atom (frame->frame frame))
                      frame
                      (frame-with-root (mv-nth 0 (collapse frame))
                                       nil))))
  :hints
  (("goal"
    :in-theory (e/d (partial-collapse collapse)
                    ((:definition no-duplicatesp-equal)
                     (:definition assoc-equal)
                     (:rewrite put-assoc-equal-without-change . 2)
                     abs-separate-of-frame->frame-of-collapse-this-lemma-8
                     (:rewrite true-list-fix-when-true-listp)
                     (:rewrite true-listp-when-string-list)
                     (:definition put-assoc-equal)
                     (:rewrite remove-assoc-of-put-assoc)
                     (:definition remove-assoc-equal)
                     (:definition remove-equal)
                     (:rewrite fat32-filename-p-correctness-1)))
    :induct (collapse frame)
    :expand ((partial-collapse frame path)
             (collapse-this frame
                            (1st-complete (frame->frame frame)))))))

(defthm
  abs-separate-of-partial-collapse-lemma-1
  (implies
   (and (not (zp (1st-complete-under-path frame path)))
        (no-duplicatesp-equal (strip-cars frame)))
   (equal
    (abs-addrs
     (frame-val->dir
      (cdr (assoc-equal (1st-complete-under-path frame path)
                        frame))))
    nil))
  :hints (("goal" :in-theory (enable 1st-complete-under-path))))

(defthm
  abs-separate-of-partial-collapse-lemma-2
  (equal (frame-val->path (cdr (assoc-equal 0 (frame-with-root root frame))))
         nil)
  :hints (("goal" :do-not-induct t
           :in-theory (enable frame-with-root))))

(defthm abs-separate-of-partial-collapse-lemma-3
  (not
   (consp (frame-val->path (cdr (assoc-equal 0 (collapse-this frame x))))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable collapse-this)))
  :rule-classes :type-prescription)

(defthm abs-separate-of-partial-collapse-lemma-5
  (implies
   (and
    (< 0
       (1st-complete-under-path (frame->frame frame)
                                path))
    (not
     (equal
      (frame-val->src
       (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                  path)
                         (frame->frame frame))))
      (1st-complete-under-path (frame->frame frame)
                               path)))
    (prefixp
     (frame-val->path
      (cdr
       (assoc-equal
        (frame-val->src
         (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                    path)
                           (frame->frame frame))))
        (frame->frame frame))))
     (frame-val->path
      (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                 path)
                        (frame->frame frame)))))
    (ctx-app-ok
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src
         (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                    path)
                           (frame->frame frame))))
        (frame->frame frame))))
     (1st-complete-under-path (frame->frame frame)
                              path)
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal
          (frame-val->src
           (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                      path)
                             (frame->frame frame))))
          (frame->frame frame)))))
      (frame-val->path
       (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                  path)
                         (frame->frame frame))))))
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (abs-separate frame))
   (abs-separate
    (put-assoc-equal
     (frame-val->src
      (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                 path)
                        (frame->frame frame))))
     (frame-val
      (frame-val->path
       (cdr
        (assoc-equal
         (frame-val->src
          (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                     path)
                            (frame->frame frame))))
         (frame->frame frame))))
      (ctx-app
       (frame-val->dir
        (cdr
         (assoc-equal
          (frame-val->src
           (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                      path)
                             (frame->frame frame))))
          (frame->frame frame))))
       (frame-val->dir
        (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                   path)
                          (frame->frame frame))))
       (1st-complete-under-path (frame->frame frame)
                                path)
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                        path)
                               (frame->frame frame))))
            (frame->frame frame)))))
        (frame-val->path
         (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                    path)
                           (frame->frame frame))))))
      (frame-val->src
       (cdr
        (assoc-equal
         (frame-val->src
          (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                     path)
                            (frame->frame frame))))
         (frame->frame frame)))))
     (remove-assoc-equal (1st-complete-under-path (frame->frame frame)
                                                  path)
                         (frame->frame frame)))))
  :hints (("goal" :in-theory (enable collapse-this abs-complete)
           :do-not-induct t)))

(defthm
  abs-separate-of-partial-collapse-lemma-4
  (implies
   (and
    (< 0
       (1st-complete-under-path (frame->frame frame)
                                    path))
    (not
     (equal
      (frame-val->src
       (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                      path)
                         (frame->frame frame))))
      (1st-complete-under-path (frame->frame frame)
                                   path)))
    (consp
     (assoc-equal
      (frame-val->src
       (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                      path)
                         (frame->frame frame))))
      (frame->frame frame)))
    (prefixp
     (frame-val->path
      (cdr
       (assoc-equal
        (frame-val->src
         (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                        path)
                           (frame->frame frame))))
        (frame->frame frame))))
     (frame-val->path
      (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                     path)
                        (frame->frame frame)))))
    (ctx-app-ok
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src
         (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                        path)
                           (frame->frame frame))))
        (frame->frame frame))))
     (1st-complete-under-path (frame->frame frame)
                                  path)
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal
          (frame-val->src
           (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                          path)
                             (frame->frame frame))))
          (frame->frame frame)))))
      (frame-val->path
       (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                      path)
                         (frame->frame frame))))))
    (no-duplicatesp-equal (abs-addrs (frame->root frame)))
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (abs-separate frame))
   (abs-separate
    (collapse-this frame
                   (1st-complete-under-path (frame->frame frame)
                                                path))))
  :hints (("goal" :in-theory (enable collapse-this)
           :do-not-induct t)))

(defthm abs-separate-of-partial-collapse-lemma-6
 (implies
  (and (< 0
          (1st-complete-under-path frame path))
       (no-duplicatesp-equal (strip-cars frame)))
  (and
   (m1-file-alist-p
    (frame-val->dir$inline
     (cdr (assoc-equal (1st-complete-under-path frame path)
                       frame))))))
 :hints (("goal" :in-theory (enable collapse-this abs-complete)
          :do-not-induct t)))

(defthm
  abs-separate-of-partial-collapse
  (implies (and (no-duplicatesp-equal (abs-addrs (frame->root frame)))
                (atom (frame-val->path (cdr (assoc-equal 0 frame))))
                (frame-p (frame->frame frame))
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (abs-separate frame))
           (abs-separate (partial-collapse frame path)))
  :hints (("goal" :in-theory (enable partial-collapse))))

(defthm
  abs-separate-of-frame->frame-of-partial-collapse
  (implies (and (abs-separate (frame->frame frame))
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (frame-p (frame->frame frame)))
           (abs-separate (frame->frame (partial-collapse frame path))))
  :hints (("goal" :in-theory (enable partial-collapse))))

(defthm
  no-duplicatesp-of-strip-cars-of-partial-collapse
  (implies
   (no-duplicatesp-equal (strip-cars frame))
   (no-duplicatesp-equal (strip-cars (partial-collapse frame path))))
  :hints (("goal" :in-theory (enable partial-collapse collapse-this))))

(defthmd
  partial-collapse-of-fat32-filename-list-fix
  (equal (partial-collapse frame
                           (fat32-filename-list-fix pathname))
         (partial-collapse frame pathname))
  :hints
  (("goal" :in-theory (enable partial-collapse)
    :induct (partial-collapse frame pathname)
    :expand (partial-collapse frame
                              (fat32-filename-list-fix pathname)))))

(defcong
  fat32-filename-list-equiv
  equal (partial-collapse frame pathname)
  2
  :hints
  (("goal"
    :in-theory (enable fat32-filename-list-equiv)
    :use ((:instance partial-collapse-of-fat32-filename-list-fix
                     (pathname pathname-equiv))
          partial-collapse-of-fat32-filename-list-fix))))

(defthm
  no-duplicatesp-of-strip-cars-of-frame->frame-of-partial-collapse
  (implies (no-duplicatesp-equal (strip-cars (frame->frame frame)))
           (no-duplicatesp-equal
            (strip-cars (frame->frame (partial-collapse frame path)))))
  :hints (("goal" :in-theory (enable partial-collapse))))

(defthmd
  ctx-app-ok-when-absfat-equiv-lemma-1
  (implies (and (abs-fs-p abs-file-alist1)
                (abs-fs-p abs-file-alist2)
                (absfat-equiv abs-file-alist1 abs-file-alist2))
           (equal (consp (assoc-equal x abs-file-alist1))
                  (consp (assoc-equal x abs-file-alist2))))
  :hints
  (("goal" :in-theory (e/d (absfat-equiv)
                           (absfat-equiv-implies-set-equiv-names-at-1-lemma-1))
    :do-not-induct t
    :use ((:instance absfat-equiv-implies-set-equiv-names-at-1-lemma-1
                     (abs-file-alist2 abs-file-alist1)
                     (abs-file-alist1 abs-file-alist2))
          absfat-equiv-implies-set-equiv-names-at-1-lemma-1))))

(defthm
  ctx-app-ok-when-absfat-equiv-lemma-3
  (implies (and (abs-fs-p abs-file-alist1)
                (abs-fs-p abs-file-alist2)
                (absfat-equiv abs-file-alist1 abs-file-alist2)
                (consp (assoc-equal (fat32-filename-fix (car x-path))
                                    abs-file-alist1)))
           (consp (assoc-equal (fat32-filename-fix (car x-path))
                               abs-file-alist2)))
  :hints
  (("goal"
    :use (:instance (:rewrite ctx-app-ok-when-absfat-equiv-lemma-1)
                    (abs-file-alist2 abs-file-alist1)
                    (abs-file-alist1 abs-file-alist2)
                    (x (fat32-filename-fix (car x-path)))))))

(local
 (defthm ctx-app-ok-when-absfat-equiv-lemma-4
   (implies (and (natp x)
                 (absfat-subsetp abs-file-alist1 abs-file-alist2)
                 (member-equal x abs-file-alist1))
            (member-equal x abs-file-alist2))
   :hints (("goal" :in-theory (enable absfat-subsetp)))))

(defthm
  ctx-app-ok-when-absfat-equiv-1
  (implies (absfat-equiv abs-file-alist1 abs-file-alist2)
           (equal (ctx-app-ok abs-file-alist1 x x-path)
                  (ctx-app-ok abs-file-alist2 x x-path)))
  :hints
  (("goal"
    :in-theory (e/d (ctx-app-ok)
                    (abs-file->contents-when-m1-file-p nfix))))
  :rule-classes :congruence)

;; This is kinda general.
(defthmd ctx-app-ok-when-absfat-equiv-lemma-6
  (implies (and (natp x)
                (absfat-equiv abs-file-alist1 abs-file-alist2)
                (abs-fs-p abs-file-alist1)
                (abs-fs-p abs-file-alist2))
           (iff (member-equal x abs-file-alist1)
                (member-equal x abs-file-alist2)))
  :hints (("goal" :in-theory (enable absfat-equiv)
           :do-not-induct t)))

(defthm
  absfat-equiv-of-ctx-app-lemma-1
  (implies
   (and
    (subsetp-equal
     (abs-addrs (abs-file->contents y))
     (abs-addrs (abs-file->contents (cdr (assoc-equal x abs-file-alist2)))))
    (abs-directory-file-p (cdr (assoc-equal x abs-file-alist2))))
   (subsetp-equal (abs-addrs (abs-file->contents y))
                  (abs-addrs abs-file-alist2)))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm
  absfat-equiv-of-ctx-app-lemma-2
  (implies
   (and (abs-file-alist-p x)
        (consp (car x)))
   (abs-file-alist-p
    (list (cons (car (car x))
                (abs-file (abs-file->d-e (cdr (car x)))
                          (abs-fs-fix (abs-file->contents (cdr (car x)))))))))
  :hints (("goal" :in-theory (enable abs-file-alist-p abs-file))))

(defthm
  absfat-equiv-of-ctx-app-lemma-10
  (implies
   (and (absfat-subsetp (abs-fs-fix (append (cdr x) y))
                        (abs-fs-fix (append (cdr x) z)))
        (abs-file-alist-p x)
        (abs-fs-p z)
        (consp (car x))
        (not (consp (assoc-equal (car (car x)) (cdr x))))
        (not (consp (assoc-equal (car (car x)) z))))
   (absfat-subsetp
    (abs-fs-fix (append (cdr x) y))
    (cons (cons (car (car x))
                (abs-file (abs-file->d-e (cdr (car x)))
                          (abs-fs-fix (abs-file->contents (cdr (car x))))))
          (abs-fs-fix (append (cdr x) z)))))
  :hints
  (("goal"
    :in-theory (e/d (abs-no-dups-p)
                    ((:rewrite absfat-subsetp-of-append-2)))
    :use
    (:instance
     (:rewrite absfat-subsetp-of-append-2)
     (z (abs-fs-fix (append (cdr x) z)))
     (y
      (list
       (cons (car (car x))
             (abs-file (abs-file->d-e (cdr (car x)))
                       (abs-fs-fix (abs-file->contents (cdr (car x))))))))
     (x (abs-fs-fix (append (cdr x) y)))))))

(defthm
  absfat-equiv-of-ctx-app-lemma-11
  (implies (and (abs-file-alist-p x)
                (not (abs-directory-file-p (abs-file-fix (cdr (car x))))))
           (abs-file-alist-p (list (cons (car (car x))
                                         (abs-file-fix (cdr (car x)))))))
  :hints (("goal" :in-theory (enable abs-file-alist-p abs-file-fix))))

(defthm
  absfat-equiv-of-ctx-app-lemma-12
  (implies (and (absfat-subsetp (abs-fs-fix (append (cdr x) y))
                                (abs-fs-fix (append (cdr x) z)))
                (abs-file-alist-p x)
                (abs-fs-p z)
                (consp (car x))
                (not (consp (assoc-equal (car (car x)) (cdr x))))
                (not (abs-directory-file-p (abs-file-fix (cdr (car x)))))
                (not (consp (assoc-equal (car (car x)) z))))
           (absfat-subsetp (abs-fs-fix (append (cdr x) y))
                           (cons (cons (car (car x))
                                       (abs-file-fix (cdr (car x))))
                                 (abs-fs-fix (append (cdr x) z)))))
  :hints
  (("goal" :in-theory (e/d (abs-no-dups-p)
                           ((:rewrite absfat-subsetp-of-append-2)
                            (:rewrite abs-fs-fix-of-put-assoc-equal-lemma-2)))
    :use (:instance (:rewrite absfat-subsetp-of-append-2)
                    (z (abs-fs-fix (append (cdr x) z)))
                    (y (list (cons (car (car x))
                                   (abs-file-fix (cdr (car x))))))
                    (x (abs-fs-fix (append (cdr x) y)))))))

;; Too much trouble at least for now to eliminate this subinduction...
(defthm
  absfat-equiv-of-ctx-app-lemma-7
  (implies (and (abs-file-alist-p x)
                (abs-fs-p y)
                (abs-fs-p z)
                (absfat-subsetp y z)
                (absfat-subsetp z y))
           (absfat-subsetp (abs-fs-fix (append x y))
                           (abs-fs-fix (append x z))))
  :hints
  (("goal"
    :in-theory (e/d (absfat-subsetp abs-fs-fix)
                    ((:rewrite abs-file-alist-p-when-m1-file-alist-p)
                     (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
                     (:rewrite abs-file-alist-p-correctness-1)
                     (:rewrite abs-file->contents-when-m1-file-p)
                     (:rewrite absfat-subsetp-transitivity-lemma-3)
                     nfix
                     (:rewrite abs-fs-fix-of-put-assoc-equal-lemma-2)))
    :induct t)))

(defthm
  absfat-equiv-of-ctx-app-lemma-8
  (implies (and (abs-file-alist-p x)
                (abs-file-alist-p z)
                (abs-no-dups-p z)
                (fat32-filename-p name)
                (not (consp (assoc-equal name x))))
           (equal (assoc-equal name (abs-fs-fix (append z x)))
                  (assoc-equal name z)))
  :hints
  (("goal" :in-theory
    (e/d (abs-fs-fix abs-no-dups-p abs-fs-p)
         ((:rewrite remove-when-absent)
          (:rewrite abs-fs-p-of-append)
          (:definition remove-equal)
          (:definition member-equal)
          (:rewrite abs-file-alist-p-correctness-1)
          (:rewrite abs-file-alist-p-when-m1-file-alist-p)
          (:rewrite abs-file->contents-when-m1-file-p)
          (:rewrite abs-directory-file-p-when-m1-file-p)
          (:rewrite abs-addrs-when-m1-file-alist-p)
          (:rewrite member-of-abs-addrs-when-natp . 2)
          (:rewrite abs-no-dups-p-when-m1-file-alist-p)
          (:rewrite hifat-file-alist-fix-guard-lemma-1)
          (:rewrite hifat-no-dups-p-when-abs-complete)
          (:definition abs-complete)
          (:rewrite abs-file-p-when-abs-directory-file-p)
          (:rewrite m1-file-alist-p-when-subsetp-equal)
          strip-cars)))))

;; Head off a subinduction.
(defthm
  absfat-equiv-of-ctx-app-lemma-3
  (implies (and (abs-file-alist-p x)
                (abs-no-dups-p x))
           (absfat-subsetp x (abs-fs-fix (append z x))))
  :hints
  (("goal"
    :in-theory (e/d (absfat-subsetp abs-fs-fix abs-fs-p)
                    ((:rewrite abs-file-alist-p-when-m1-file-alist-p)
                     (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
                     (:rewrite abs-file-alist-p-correctness-1)
                     (:rewrite abs-file->contents-when-m1-file-p)
                     (:rewrite absfat-subsetp-transitivity-lemma-3))))))

(defthm
  absfat-equiv-of-ctx-app-lemma-17
  (implies (and (abs-file-alist-p x)
                (abs-no-dups-p x)
                (abs-fs-p y)
                (abs-fs-p z)
                (absfat-subsetp y z))
           (absfat-subsetp (abs-fs-fix (append y x))
                           (abs-fs-fix (append z x))))
  :hints
  (("goal"
    :in-theory (e/d (absfat-subsetp abs-fs-fix abs-fs-p
                                    no-duplicatesp-of-abs-addrs-of-put-assoc-lemma-1)
                    ((:rewrite abs-file-alist-p-when-m1-file-alist-p)
                     (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
                     (:rewrite abs-file-alist-p-correctness-1)
                     (:rewrite abs-file->contents-when-m1-file-p)
                     (:rewrite absfat-subsetp-transitivity-lemma-3)))
    :induct t)))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies (and (natp x)
                   (absfat-equiv abs-file-alist1 abs-file-alist2)
                   (abs-fs-p abs-file-alist1)
                   (abs-fs-p abs-file-alist2))
              (absfat-equiv (ctx-app abs-file-alist3
                                     abs-file-alist1 x x-path)
                            (ctx-app abs-file-alist3
                                     abs-file-alist2 x x-path)))
     :hints (("goal" :in-theory (e/d (ctx-app absfat-equiv))
              :induct (mv (ctx-app abs-file-alist3
                                   abs-file-alist1 x x-path)
                          (ctx-app abs-file-alist3
                                   abs-file-alist2 x x-path))))))

  ;; Pretty general.
  (defthm
    absfat-equiv-of-ctx-app-1
    (implies (absfat-equiv abs-file-alist1 abs-file-alist2)
             (absfat-equiv (ctx-app abs-file-alist3
                                    abs-file-alist1 x x-path)
                           (ctx-app abs-file-alist3
                                    abs-file-alist2 x x-path)))
    :hints (("goal"
             :use (:instance lemma
                             (x (nfix x))
                             (abs-file-alist1 (abs-fs-fix abs-file-alist1))
                             (abs-file-alist2 (abs-fs-fix abs-file-alist2)))))
    :rule-classes :congruence))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies (and (natp x)
                   (absfat-equiv abs-file-alist1 abs-file-alist2)
                   (abs-fs-p abs-file-alist1)
                   (abs-fs-p abs-file-alist2))
              (absfat-equiv (ctx-app abs-file-alist1
                                     abs-file-alist3 x x-path)
                            (ctx-app abs-file-alist2
                                     abs-file-alist3 x x-path)))
     :hints
     (("goal" :in-theory (e/d (ctx-app-ok ctx-app absfat-equiv)
                              (abs-file->contents-when-m1-file-p
                               (:rewrite abs-no-dups-p-when-m1-file-alist-p)
                               (:rewrite put-assoc-equal-without-change . 2)
                               (:definition put-assoc-equal)
                               (:rewrite abs-file-alist-p-correctness-1)))
       :induct (mv (ctx-app abs-file-alist1
                            abs-file-alist3 x x-path)
                   (ctx-app abs-file-alist2
                            abs-file-alist3 x x-path))
       :expand (:free (abs-file-alist2)
                      (absfat-subsetp nil abs-file-alist2))))))

  ;; Quite general.
  (defthm
    absfat-equiv-of-ctx-app-2
    (implies (absfat-equiv abs-file-alist1 abs-file-alist2)
             (absfat-equiv (ctx-app abs-file-alist1
                                    abs-file-alist3 x x-path)
                           (ctx-app abs-file-alist2
                                    abs-file-alist3 x x-path)))
    :hints
    (("goal"
      :use (:instance lemma
                      (x (nfix x))
                      (abs-file-alist1 (abs-fs-fix abs-file-alist1))
                      (abs-file-alist2 (abs-fs-fix abs-file-alist2)))))
    :rule-classes :congruence))

(defthm ctx-app-of-ctx-app-lemma-1
  (implies (and (abs-complete (abs-fs-fix y))
                (abs-complete (abs-fs-fix z))
                (not (equal (nfix y-var) (nfix z-var)))
                (not (intersectp-equal (names-at y nil)
                                       (names-at z nil)))
                (not (intersectp-equal (names-at y nil)
                                       (names-at x y-path)))
                (not (intersectp-equal (names-at z nil)
                                       (names-at x y-path))))
           (absfat-subsetp (ctx-app (ctx-app x y y-var y-path)
                                    z z-var y-path)
                           (ctx-app (ctx-app x z z-var y-path)
                                    y y-var y-path)))
  :hints (("goal" :in-theory (e/d (ctx-app ctx-app-ok names-at)
                                  (nfix)))))

(defthm
  ctx-app-of-ctx-app-lemma-2
  (implies (and (ctx-app-ok x z-var z-path)
                (not (intersectp-equal (names-at z nil)
                                       (names-at x z-path)))
                (not (prefixp (fat32-filename-list-fix z-path)
                              (fat32-filename-list-fix y-path)))
                (not (intersectp-equal (names-at y nil)
                                       (names-at x y-path)))
                (natp y-var)
                (natp z-var))
           (absfat-subsetp (ctx-app (ctx-app x z z-var z-path)
                                    y y-var y-path)
                           (ctx-app (ctx-app x y y-var y-path)
                                    z z-var z-path)))
  :hints
  (("goal"
    :in-theory
    (e/d (ctx-app ctx-app-ok
                  names-at put-assoc-of-remove addrs-at)
         ((:definition no-duplicatesp-equal)
          (:rewrite abs-addrs-of-ctx-app)
          (:rewrite abs-file-contents-p-when-m1-file-contents-p)
          (:rewrite m1-file-contents-p-correctness-1)
          (:definition member-equal)
          (:definition assoc-equal)
          (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
          (:type-prescription abs-directory-file-p-when-m1-file-p-lemma-1)))
    :induct (mv (fat32-filename-list-prefixp z-path y-path)
                (ctx-app x z z-var z-path)
                (ctx-app x y y-var y-path)))
   ("subgoal *1/3" :expand ((:free (x y y-var)
                                   (ctx-app x y y-var y-path))
                            (:free (x z z-var)
                                   (ctx-app x z z-var z-path)))
    :cases ((null (fat32-filename-fix (car z-path)))))))

(defthm
  ctx-app-of-ctx-app-lemma-3
  (implies (and (ctx-app-ok x z-var z-path)
                (not (intersectp-equal (names-at z nil)
                                       (names-at x
                                                 z-path)))
                (not (prefixp (fat32-filename-list-fix z-path)
                              (fat32-filename-list-fix y-path)))
                (not (intersectp-equal (names-at y nil)
                                       (names-at x
                                                 y-path))))
           (absfat-subsetp (ctx-app (ctx-app x y y-var y-path)
                                    z z-var z-path)
                           (ctx-app (ctx-app x z z-var z-path)
                                    y y-var y-path)))
  :hints
  (("goal" :in-theory
    (e/d (ctx-app ctx-app-ok addrs-at
                  names-at put-assoc-of-remove)
         (nfix (:definition no-duplicatesp-equal)
               (:rewrite abs-addrs-of-ctx-app)
               (:rewrite abs-file-contents-p-when-m1-file-contents-p)
               (:rewrite m1-file-contents-p-correctness-1)
               (:definition member-equal)
               (:definition assoc-equal)
               (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
               (:rewrite abs-file-alist-p-correctness-1)))
    :induct (mv (fat32-filename-list-prefixp z-path y-path)
                (ctx-app x z z-var z-path)
                (ctx-app x y y-var y-path)))
   ("subgoal *1/3" :expand ((:free (x y y-var)
                                   (ctx-app x y y-var y-path))
                            (:free (x z z-var)
                                   (ctx-app x z z-var z-path)))
    :cases ((null (fat32-filename-fix (car z-path)))))))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies (and (abs-complete (abs-fs-fix y))
                   (abs-complete (abs-fs-fix z))
                   (ctx-app-ok x y-var y-path)
                   (ctx-app-ok x z-var z-path)
                   (not (equal (nfix y-var) (nfix z-var)))
                   (abs-no-dups-p (ctx-app (ctx-app x z z-var z-path)
                                           y y-var y-path))
                   (natp y-var)
                   (natp z-var)
                   (not (intersectp-equal (names-at y nil)
                                          (names-at x y-path)))
                   (not (intersectp-equal (names-at z nil)
                                          (names-at x z-path)))
                   (abs-no-dups-p (ctx-app (ctx-app x y y-var y-path)
                                           z z-var z-path)))
              (absfat-equiv (ctx-app (ctx-app x z z-var z-path)
                                     y y-var y-path)
                            (ctx-app (ctx-app x y y-var y-path)
                                     z z-var z-path)))
     :hints
     (("goal" :in-theory (e/d (list-equiv absfat-equiv)
                              ((:rewrite prefixp-when-equal-lengths)
                               len-when-prefixp))
       :use ((:instance (:rewrite prefixp-when-equal-lengths)
                        (y (fat32-filename-list-fix z-path))
                        (x (fat32-filename-list-fix y-path)))
             (:instance len-when-prefixp
                        (x (fat32-filename-list-fix y-path))
                        (y (fat32-filename-list-fix z-path)))
             (:instance len-when-prefixp
                        (x (fat32-filename-list-fix z-path))
                        (y (fat32-filename-list-fix y-path))))
       :do-not-induct t
       :expand ((:with abs-fs-fix-when-abs-fs-p
                       (abs-fs-fix (ctx-app (ctx-app x y y-var y-path)
                                            z z-var z-path)))
                (:with abs-fs-fix-when-abs-fs-p
                       (abs-fs-fix (ctx-app (ctx-app x z z-var z-path)
                                            y y-var y-path))))))))

  ;; This theorem is interesting because it would really be awesome if it could
  ;; be made hypothesis free, but it's fairly obvious why it can't - there's no
  ;; way to ensure that abs-file-alist2 and abs-file-alist3 won't have names in
  ;; common. A weirdly restricted version of it could exist if it was accessing
  ;; elements from a frame fixed (by an appropriate fixing function) to have
  ;; separate elements.
  (defthm
    ctx-app-of-ctx-app-1
    (implies
     (and
      (abs-complete (abs-fs-fix y))
      (abs-complete (abs-fs-fix z))
      (case-split
       (and (not (equal (nfix y-var) (nfix z-var)))
            (abs-no-dups-p (ctx-app (ctx-app x z z-var z-path)
                                    y y-var y-path))
            (abs-no-dups-p (ctx-app (ctx-app x y y-var y-path)
                                    z z-var z-path))))
      (not (intersectp-equal (names-at y nil)
                             (names-at x y-path)))
      (not (intersectp-equal (names-at z nil)
                             (names-at x z-path))))
     (absfat-equiv (ctx-app (ctx-app x z z-var z-path)
                            y y-var y-path)
                   (ctx-app (ctx-app x y y-var y-path)
                            z z-var z-path)))
    :hints (("goal" :use ((:instance lemma (x (abs-fs-fix x))
                                     (y (abs-fs-fix y))
                                     (z (abs-fs-fix z))
                                     (y-var (nfix y-var))
                                     (z-var (nfix z-var))))
             :in-theory (disable nfix)))))

(defthm
  collapse-congruence-lemma-1
  (implies (and (absfat-equiv (frame->root frame1)
                              (frame->root frame2))
                (syntaxp
                 (not (term-order frame1 frame2)))
                (equal (frame->frame frame1)
                       (frame->frame frame2)))
           (absfat-equiv (frame->root (collapse-this frame1 x))
                         (frame->root (collapse-this frame2 x))))
  :hints (("goal" :in-theory (enable collapse-this))))

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

  (defthmd
    collapse-congruence-lemma-3
    (implies (and (equal (frame->frame frame1)
                         (frame->frame frame2))
                  (absfat-equiv (frame->root frame1)
                                (frame->root frame2)))
             (and (absfat-equiv (mv-nth 0 (collapse frame1))
                                (mv-nth 0 (collapse frame2)))
                  (equal (mv-nth 1 (collapse frame1))
                         (mv-nth 1 (collapse frame2)))))
    :hints (("goal" :in-theory (enable collapse)
             :induct (induction-scheme frame1 frame2)
             :expand (collapse frame2)))))

(defthm
  collapse-congruence-1
  (implies
   (absfat-equiv root1 root2)
   (and
    (absfat-equiv
     (mv-nth 0
             (collapse (frame-with-root root1 frame)))
     (mv-nth 0
             (collapse (frame-with-root root2 frame))))
    (equal (mv-nth 1
                   (collapse (frame-with-root root1 frame)))
           (mv-nth 1
                   (collapse (frame-with-root root2 frame))))))
  :hints
  (("goal"
    :do-not-induct t
    :use
    ((:instance (:rewrite collapse-congruence-lemma-3)
                (frame1 (frame-with-root root1 frame))
                (frame2 (frame-with-root root2 frame))))))
  :rule-classes
  ((:congruence
    :corollary
    (implies
     (absfat-equiv root1 root2)
     (absfat-equiv
      (mv-nth 0
              (collapse (frame-with-root root1 frame)))
      (mv-nth 0
              (collapse (frame-with-root root2 frame))))))
   (:congruence
    :corollary
    (implies
     (absfat-equiv root1 root2)
     (equal
      (mv-nth 1
              (collapse (frame-with-root root1 frame)))
      (mv-nth 1
              (collapse (frame-with-root root2 frame))))))))

(defthm
  collapse-congruence-lemma-2
  (implies (and (consp (assoc-equal x frame))
                (absfat-equiv (frame-val->dir (cdr (assoc-equal x frame)))
                              (frame-val->dir val)))
           (equal (1st-complete (put-assoc-equal x val frame))
                  (1st-complete frame)))
  :hints (("goal" :in-theory (enable 1st-complete abs-separate))))

(encapsulate
  ()

  (local
   (defun
       induction-scheme (dir frame x)
     (declare (xargs :verify-guards nil
                     :measure (len (frame->frame frame))))
     (cond
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (not
         (zp
          (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (not
         (or
          (equal
           (frame-val->src
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
           (1st-complete (frame->frame frame)))
          (atom
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame))
             (frame->frame frame))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
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
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame))
             (frame->frame frame)))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src
               (cdr
                (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
              (remove-assoc-equal
               (1st-complete (frame->frame frame))
               (frame->frame frame))))))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (equal x (1st-complete (frame->frame frame))))
       (induction-scheme
        (ctx-app
         (frame-val->dir
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (frame->frame frame))))
         dir (1st-complete (frame->frame frame))
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
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (collapse-this frame
                       (1st-complete (frame->frame frame)))
        (frame-val->src
         (cdr (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))))
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (not
         (zp
          (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (not
         (or
          (equal
           (frame-val->src
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
           (1st-complete (frame->frame frame)))
          (atom
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame))
             (frame->frame frame))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
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
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame))
             (frame->frame frame)))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src
               (cdr
                (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
              (remove-assoc-equal
               (1st-complete (frame->frame frame))
               (frame->frame frame))))))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (equal x
               (frame-val->src
                (cdr
                 (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))
       (induction-scheme
        (ctx-app
         dir
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
               (cdr
                (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
              (frame->frame frame)))))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (collapse-this frame
                       (1st-complete (frame->frame frame)))
        x))
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (not
         (zp
          (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (not
         (or
          (equal
           (frame-val->src
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
           (1st-complete (frame->frame frame)))
          (atom
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame))
             (frame->frame frame))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
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
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame))
             (frame->frame frame)))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src
               (cdr
                (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
              (remove-assoc-equal
               (1st-complete (frame->frame frame))
               (frame->frame frame))))))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))))))
       (induction-scheme
        dir
        (collapse-this frame
                       (1st-complete (frame->frame frame)))
        x))
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (zp
         (frame-val->src
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))
        (ctx-app-ok
         (frame->root frame)
         (1st-complete (frame->frame frame))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))))
       (induction-scheme
        dir
        (collapse-this frame
                       (1st-complete (frame->frame frame)))
        x))
      (t (mv dir frame x)))))

  (defthm
    collapse-congruence-lemma-6
    (implies
     (and (syntaxp (variablep x))
          (consp (assoc-equal x (frame->frame frame)))
          (absfat-equiv
           (frame-val->dir
            (cdr (assoc-equal x (frame->frame frame))))
           dir))
     (and
      (equal
       (mv-nth
        1
        (collapse
         (frame-with-root
          (frame->root frame)
          (put-assoc-equal
           x
           (frame-val
            (frame-val->path
             (cdr (assoc-equal x (frame->frame frame))))
            dir
            (frame-val->src
             (cdr (assoc-equal x (frame->frame frame)))))
           (frame->frame frame)))))
       (mv-nth 1 (collapse frame)))
      (absfat-equiv
       (mv-nth
        0
        (collapse
         (frame-with-root
          (frame->root frame)
          (put-assoc-equal
           x
           (frame-val
            (frame-val->path
             (cdr (assoc-equal x (frame->frame frame))))
            dir
            (frame-val->src
             (cdr (assoc-equal x (frame->frame frame)))))
           (frame->frame frame)))))
       (mv-nth 0 (collapse frame)))))
    :hints
    (("goal"
      :in-theory
      (e/d
       (collapse collapse-this)
       ((:definition remove-assoc-equal)
        (:rewrite remove-assoc-of-remove-assoc)
        (:rewrite abs-file-alist-p-when-m1-file-alist-p)
        (:rewrite
         absfat-equiv-implies-set-equiv-names-at-1-lemma-1)
        (:rewrite put-assoc-equal-without-change . 2)
        (:definition no-duplicatesp-equal)
        (:definition member-equal)
        (:rewrite nthcdr-when->=-n-len-l)
        (:definition remove-equal)
        (:rewrite remove-when-absent)
        (:rewrite 1st-complete-of-put-assoc-2)
        (:definition put-assoc-equal)
        (:rewrite no-duplicatesp-of-strip-cars-of-put-assoc)
        (:type-prescription
         abs-addrs-of-remove-assoc-lemma-1)
        (:rewrite abs-file-alist-p-correctness-1)
        (:rewrite abs-complete-correctness-1)))
      :induct (induction-scheme dir frame x)
      :expand
      ((collapse frame)
       (collapse
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          x
          (frame-val
           (frame-val->path
            (cdr (assoc-equal x (frame->frame frame))))
           dir
           (frame-val->src
            (cdr (assoc-equal x (frame->frame frame)))))
          (frame->frame frame))))
       (collapse
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (1st-complete (frame->frame frame))
          (frame-val
           (frame-val->path
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
           dir 0)
          (frame->frame frame)))))))))

(defthm
  collapse-congruence-lemma-7
  (equal
   (collapse (frame-with-root root (remove-assoc 0 frame)))
   (collapse (frame-with-root root frame)))
  :hints
  (("goal"
    :in-theory (enable collapse collapse-this)
    :expand
    ((collapse
      (frame-with-root root (remove-assoc-equal 0 frame)))
     (collapse (frame-with-root root frame)))
    :do-not-induct t)))

;; This can be p helpful...
(defthm
  collapse-congruence-2
  (implies
   (absfat-equiv dir1 dir2)
   (and
    (absfat-equiv
     (mv-nth
      0
      (collapse
       (frame-with-root
        root
        (put-assoc-equal
         x
         (frame-val (frame-val->path (cdr (assoc-equal x frame)))
                    dir1
                    (frame-val->src (cdr (assoc-equal x frame))))
         frame))))
     (mv-nth
      0
      (collapse
       (frame-with-root
        root
        (put-assoc-equal
         x
         (frame-val (frame-val->path (cdr (assoc-equal x frame)))
                    dir2
                    (frame-val->src (cdr (assoc-equal x frame))))
         frame)))))
    (equal
     (mv-nth
      1
      (collapse
       (frame-with-root
        root
        (put-assoc-equal
         x
         (frame-val (frame-val->path (cdr (assoc-equal x frame)))
                    dir1
                    (frame-val->src (cdr (assoc-equal x frame))))
         frame))))
     (mv-nth
      1
      (collapse
       (frame-with-root
        root
        (put-assoc-equal
         x
         (frame-val (frame-val->path (cdr (assoc-equal x frame)))
                    dir2
                    (frame-val->src (cdr (assoc-equal x frame))))
         frame)))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (disable collapse-congruence-lemma-6
             (:rewrite collapse-congruence-lemma-7))
    :use
    ((:instance
      collapse-congruence-lemma-6
      (dir dir2)
      (frame
       (frame-with-root
        root
        (put-assoc-equal
         x
         (frame-val
          (frame-val->path (cdr (assoc-equal x frame)))
          dir1
          (frame-val->src (cdr (assoc-equal x frame))))
         frame))))
     (:instance
      (:rewrite collapse-congruence-lemma-7)
      (frame
       (put-assoc-equal
        0
        (frame-val (frame-val->path (cdr (assoc-equal 0 frame)))
                   dir1
                   (frame-val->src (cdr (assoc-equal 0 frame))))
        frame))
      (root root))
     (:instance
      (:rewrite collapse-congruence-lemma-7)
      (frame
       (put-assoc-equal
        0
        (frame-val (frame-val->path (cdr (assoc-equal 0 frame)))
                   dir2
                   (frame-val->src (cdr (assoc-equal 0 frame))))
        frame))
      (root root))
     (:instance
      (:rewrite collapse-congruence-lemma-7)
      (frame
       (put-assoc-equal
        x
        (frame-val (frame-val->path (cdr (assoc-equal x frame)))
                   dir2
                   (frame-val->src (cdr (assoc-equal x frame))))
        frame))
      (root root)))))
  :rule-classes
  ((:congruence
    :corollary
    (implies
     (absfat-equiv dir1 dir2)
     (absfat-equiv
      (mv-nth
       0
       (collapse
        (frame-with-root
         root
         (put-assoc-equal
          x
          (frame-val (frame-val->path (cdr (assoc-equal x frame)))
                     dir1
                     (frame-val->src (cdr (assoc-equal x frame))))
          frame))))
      (mv-nth
       0
       (collapse
        (frame-with-root
         root
         (put-assoc-equal
          x
          (frame-val (frame-val->path (cdr (assoc-equal x frame)))
                     dir2
                     (frame-val->src (cdr (assoc-equal x frame))))
          frame)))))))
   (:congruence
    :corollary
    (implies
     (absfat-equiv dir1 dir2)
     (equal
      (mv-nth
       1
       (collapse
        (frame-with-root
         root
         (put-assoc-equal
          x
          (frame-val (frame-val->path (cdr (assoc-equal x frame)))
                     dir1
                     (frame-val->src (cdr (assoc-equal x frame))))
          frame))))
      (mv-nth
       1
       (collapse
        (frame-with-root
         root
         (put-assoc-equal
          x
          (frame-val (frame-val->path (cdr (assoc-equal x frame)))
                     dir2
                     (frame-val->src (cdr (assoc-equal x frame))))
          frame)))))))))

;; Ye olde hacky definition...
(defund
  collapse-seq (frame seq)
  (declare (xargs :guard (and (frame-p frame)
                              (consp (assoc-equal 0 frame))
                              (nat-listp seq))
                  :guard-debug t
                  :measure (len (frame->frame frame))))
  (b*
      (((when (or (atom (frame->frame frame))
                  (atom seq)))
        frame)
       (head-index (car seq))
       ((when (or (zp head-index)
                  (atom (assoc-equal (car seq)
                                     (frame->frame frame)))
                  (not (abs-complete
                        (frame-val->dir
                         (cdr (assoc-equal (car seq)
                                           (frame->frame frame))))))))
        frame)
       (head-frame-val
        (cdr (assoc-equal head-index (frame->frame frame))))
       (src
        (frame-val->src (cdr (assoc-equal (car seq)
                                          (frame->frame frame))))))
    (if
        (zp src)
        (b* (((unless (ctx-app-ok (frame->root frame)
                                  head-index
                                  (frame-val->path head-frame-val)))
              frame))
          (collapse-seq (collapse-this frame (car seq))
                        (cdr seq)))
      (b*
          ((path (frame-val->path head-frame-val))
           ((when (or (equal src head-index)
                      (atom (assoc-equal src (frame->frame frame)))))
            frame)
           (src-path
            (frame-val->path
             (cdr (assoc-equal src (frame->frame frame)))))
           (src-dir
            (frame-val->dir
             (cdr (assoc-equal src (frame->frame frame)))))
           ((unless (and (prefixp src-path path)
                         (ctx-app-ok src-dir head-index
                                     (nthcdr (len src-path) path))))
            frame))
        (collapse-seq (collapse-this frame (car seq))
                      (cdr seq))))))

(defthm frame-p-of-collapse-seq
  (implies (frame-p frame)
           (frame-p (collapse-seq frame seq)))
  :hints (("goal" :in-theory (enable collapse-seq))))

(defthm frame-p-of-frame->frame-of-collapse-seq
  (implies (frame-p (frame->frame frame))
           (frame-p (frame->frame (collapse-seq frame seq))))
  :hints (("goal" :in-theory (enable collapse-seq))))

(defthm
  no-duplicatesp-of-strip-cars-of-collapse-seq
  (implies
   (no-duplicatesp (strip-cars (frame->frame frame)))
   (no-duplicatesp (strip-cars (frame->frame (collapse-seq frame seq)))))
  :hints (("goal" :in-theory (enable collapse-seq))))

(defthmd collapse-seq-of-true-list-fix
  (equal (collapse-seq (true-list-fix frame) seq)
         (true-list-fix (collapse-seq frame seq)))
  :hints (("goal" :in-theory (enable collapse-seq)
           :induct (collapse-seq frame seq)
           :expand (collapse-seq (true-list-fix frame)
                                 seq))))

(defcong list-equiv list-equiv (collapse-seq frame seq) 1
  :hints (("Goal" :use
           (collapse-seq-of-true-list-fix
            (:instance collapse-seq-of-true-list-fix (frame frame-equiv))))))

(defund valid-seqp (frame seq)
  (declare (xargs :guard (and (frame-p frame)
                              (consp (assoc-equal 0 frame))
                              (nat-listp seq))))
  (equal (len (frame->frame (collapse-seq frame seq)))
         (- (len (frame->frame frame))
            (len seq))))

(defthm
  valid-seqp-when-prefixp
  (implies (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (valid-seqp frame seq1)
                (prefixp seq2 seq1))
           (valid-seqp frame seq2))
  :hints (("goal" :in-theory (enable prefixp valid-seqp collapse-seq)
           :induct (mv (collapse-seq frame seq2)
                       (prefixp seq2 seq1)))))

(defthm
  collapse-seq-of-collapse-seq
  (implies (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (valid-seqp frame seq1))
           (equal (collapse-seq (collapse-seq frame seq1)
                                seq2)
                  (collapse-seq frame (append seq1 seq2))))
  :hints (("goal" :in-theory (e/d (collapse-seq valid-seqp))
           :induct (mv (collapse-seq frame seq1)
                       (append seq1 seq2)))))

(defthm
  strip-cars-of-frame->frame-of-collapse-seq
  (implies (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (valid-seqp frame seq))
           (equal (strip-cars (frame->frame (collapse-seq frame seq)))
                  (set-difference-equal (strip-cars (frame->frame frame))
                                        seq)))
  :hints
  (("goal"
    :in-theory (enable collapse-seq valid-seqp)
    :induct (collapse-seq frame seq)
    :expand (:with (:definition set-difference$-redefinition)
                   (set-difference-equal (strip-cars (frame->frame frame))
                                         seq))
    :do-not-induct t)))

(defund final-val (x frame)
  (frame-val->dir (cdr (assoc-equal
                        x
                        (frame->frame (collapse-iter
                                       frame
                                       (collapse-1st-index frame x)))))))

(defthm
  final-val-of-1st-complete
  (equal (final-val (1st-complete (frame->frame frame))
                    frame)
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame)))))
  :hints (("goal" :in-theory (enable final-val
                                     collapse-1st-index collapse-iter))))

(defthmd
  final-val-of-collapse-this-lemma-1
  (implies
   (atom (frame->frame frame))
   (atom
    (assoc-equal
     x
     (frame->frame (collapse-this frame
                                  (1st-complete (frame->frame frame)))))))
  :hints (("goal" :in-theory (enable collapse-this)))
  :rule-classes :type-prescription)

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies
      (and
       (mv-nth 1 (collapse frame))
       (consp (frame->frame frame))
       (consp
        (assoc-equal
         x
         (frame->frame
          (collapse-this frame
                         (1st-complete (frame->frame frame)))))))
      (equal
       (final-val
        x
        (collapse-this frame
                       (1st-complete (frame->frame frame))))
       (final-val x frame)))
     :hints
     (("goal"
       :do-not-induct t
       :in-theory
       (e/d (final-val collapse collapse-iter
                       collapse-1st-index 1st-complete)
            (collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-7
             (:rewrite nthcdr-when->=-n-len-l)
             (:definition no-duplicatesp-equal)
             (:rewrite partial-collapse-correctness-lemma-2)
             (:rewrite collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-2)
             (:definition member-equal)
             (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
             (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8
                       . 2)))
       :use (:instance
             (:rewrite collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-7)
             (x x)
             (n 1)
             (frame frame))))))

  (defthm
    final-val-of-collapse-this-1
    (implies
     (and
      (mv-nth 1 (collapse frame))
      (consp
       (assoc-equal
        x
        (frame->frame
         (collapse-this frame
                        (1st-complete (frame->frame frame)))))))
     (equal
      (final-val
       x
       (collapse-this frame
                      (1st-complete (frame->frame frame))))
      (final-val x frame)))
    :hints
    (("goal" :do-not-induct t
      :use (lemma final-val-of-collapse-this-lemma-1)))))

(defthm
  m1-file-alist-p-of-final-val
  (implies (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (frame-p (frame->frame frame))
                (mv-nth 1 (collapse frame)))
           (m1-file-alist-p (final-val x frame)))
  :hints
  (("goal"
    :in-theory
    (e/d
     (final-val)
     (collapse-1st-index-correctness-1 abs-separate-of-frame->frame-of-collapse-this-lemma-9))
    :use
    (collapse-1st-index-correctness-1
     (:instance
      abs-separate-of-frame->frame-of-collapse-this-lemma-9
      (frame (frame->frame (collapse-iter frame
                                          (collapse-1st-index frame x)))))))))

(defthm
  abs-fs-p-of-final-val
  (abs-fs-p (final-val x frame))
  :hints (("goal" :in-theory (enable final-val)))
  :rule-classes
  (:rewrite
   (:rewrite :corollary (equal (abs-fs-fix (final-val x frame))
                               (final-val x frame)))))

(defund
  final-val-seq (x frame seq)
  (frame-val->dir
   (cdr
    (assoc-equal
     x
     (frame->frame
      (collapse-seq frame (take (position x seq) seq)))))))

(defthm final-val-seq-of-take
  (implies (and (<= (nfix n) (len seq))
                (member-equal x (take n seq)))
           (equal (final-val-seq x frame (take n seq))
                  (final-val-seq x frame seq)))
  :hints (("goal" :in-theory (enable final-val-seq)
           :do-not-induct t
           :expand (:with take-fewer-of-take-more
                          (take (position-equal x seq)
                                (take n seq))))))

(defthm
  abs-fs-p-of-final-val-seq
  (abs-fs-p (final-val-seq x frame seq))
  :hints (("goal" :in-theory (enable final-val-seq)))
  :rule-classes
  (:rewrite
   (:rewrite :corollary (equal (abs-fs-fix (final-val-seq x frame seq))
                               (final-val-seq x frame seq)))))

(defthm
  m1-file-alist-p-of-final-val-seq-lemma-2
  (implies
   (not (consp (assoc-equal x (frame->frame frame))))
   (not (consp (assoc-equal x
                            (frame->frame (collapse-seq frame seq))))))
  :hints (("goal" :in-theory (enable collapse-seq)))
  :rule-classes (:rewrite :type-prescription))

;; Out of x, y and frame, at least one has to be a free variable...
(local
 (defthm m1-file-alist-p-of-final-val-seq-lemma-3
   (implies (and (consp (assoc-equal y (frame->frame frame)))
                 (not (equal x y)))
            (consp (frame->frame (collapse-this frame x))))
   :hints (("goal" :in-theory (enable collapse-this)))))

(defthm
  m1-file-alist-p-of-final-val-seq-lemma-4
  (implies
   (and
    (nat-listp seq)
    (not (equal (frame-val->src (cdr (assoc-equal (car seq)
                                                  (frame->frame frame))))
                (car seq)))
    (member-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                    (frame->frame frame))))
                  (cdr seq)))
   (<
    0
    (position-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                      (frame->frame frame))))
                    seq)))
  :rule-classes :linear
  :hints
  (("goal"
    :in-theory (disable (:type-prescription position-when-member)
                        (:rewrite position-of-nthcdr))
    :use
    ((:instance
      (:rewrite position-of-nthcdr)
      (lst seq)
      (n 1)
      (item (frame-val->src (cdr (assoc-equal (car seq)
                                              (frame->frame frame))))))
     (:instance
      (:type-prescription position-when-member)
      (lst (nthcdr 1 seq))
      (item (frame-val->src (cdr (assoc-equal (car seq)
                                              (frame->frame frame))))))))))

(defthm
  m1-file-alist-p-of-final-val-seq
  (implies (and (valid-seqp frame seq)
                (member-equal x seq)
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (nat-listp seq))
           (m1-file-alist-p (final-val-seq x frame seq)))
  :hints (("goal" :in-theory (enable final-val-seq
                                     valid-seqp collapse-seq))))

(defthm
  final-val-seq-of-collapse-this-lemma-1
  (implies
   (and (< 0
           (frame-val->src (cdr (assoc-equal (car seq)
                                             (frame->frame frame)))))
        (frame-p (frame->frame frame))
        (valid-seqp frame seq))
   (ctx-app-ok
    (frame-val->dir
     (cdr
      (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                     (frame->frame frame))))
                   (frame->frame frame))))
    (car seq)
    (nthcdr
     (len
      (frame-val->path
       (cdr
        (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                       (frame->frame frame))))
                     (frame->frame frame)))))
     (frame-val->path (cdr (assoc-equal (car seq)
                                        (frame->frame frame)))))))
  :hints (("goal" :in-theory (enable valid-seqp collapse-seq)
           :do-not-induct t)))

(defthm
  final-val-seq-of-collapse-this-lemma-2
  (implies
   (and (frame-p (frame->frame frame))
        (valid-seqp frame seq))
   (abs-complete
    (frame-val->dir (cdr (assoc-equal (car seq) (frame->frame frame))))))
  :hints (("goal" :in-theory (enable valid-seqp collapse-seq)
           :do-not-induct t)))

(defthm
  final-val-seq-of-collapse-this-lemma-3
  (implies
   (valid-seqp frame seq)
   (not (equal (frame-val->src (cdr (assoc-equal (car seq)
                                                 (frame->frame frame))))
               (car seq))))
  :hints (("goal" :in-theory (enable valid-seqp collapse-seq))))

(defthm
  final-val-seq-of-collapse-this-lemma-4
  (implies
   (and (equal (frame-val->src (cdr (assoc-equal (car seq)
                                                 (frame->frame frame))))
               0)
        (consp (assoc-equal (car seq)
                            (frame->frame frame)))
        (frame-p (frame->frame frame))
        (valid-seqp frame seq))
   (ctx-app-ok (frame->root frame)
               (car seq)
               (frame-val->path (cdr (assoc-equal (car seq)
                                                  (frame->frame frame))))))
  :hints (("goal" :in-theory (enable valid-seqp collapse-seq))))

(defthmd
  final-val-seq-of-collapse-this-lemma-5
  (implies
   (and (valid-seqp frame seq)
        (member-equal x (cdr seq))
        (< 0
           (frame-val->src (cdr (assoc-equal (car seq)
                                             (frame->frame frame))))))
   (prefixp
    (frame-val->path
     (cdr
      (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                     (frame->frame frame))))
                   (frame->frame frame))))
    (frame-val->path (cdr (assoc-equal (car seq)
                                       (frame->frame frame))))))
  :hints (("goal" :in-theory (enable valid-seqp collapse-seq))))

(defthm
  final-val-seq-of-collapse-this-lemma-6
  (implies
   (and (consp seq)
        (not (consp (assoc-equal (car seq)
                                 (frame->frame frame)))))
   (not (valid-seqp frame seq)))
  :hints (("goal" :in-theory (enable valid-seqp collapse-seq)
           :do-not-induct t))
  :rule-classes :type-prescription)

(defthm final-val-seq-of-collapse-this-lemma-7
  (implies (and (consp seq) (zp (car seq)))
           (not (valid-seqp frame seq)))
  :hints (("goal" :in-theory (enable valid-seqp collapse-seq)))
  :rule-classes :type-prescription)

(defthm
  final-val-seq-of-collapse-this-lemma-8
  (implies
   (and (< 0
           (frame-val->src (cdr (assoc-equal (car seq)
                                             (frame->frame frame)))))
        (frame-p (frame->frame frame))
        (valid-seqp frame seq))
   (consp
    (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                   (frame->frame frame))))
                 (frame->frame frame))))
  :hints (("goal" :in-theory (enable valid-seqp collapse-seq)))
  :rule-classes :type-prescription)

(defthm
  final-val-seq-of-collapse-this-1
  (implies (and (valid-seqp frame seq)
                (frame-p (frame->frame frame))
                (not (equal x (car seq)))
                (member-equal x seq)
                (nat-listp seq))
           (equal (final-val-seq x (collapse-this frame (car seq))
                                 (cdr seq))
                  (final-val-seq x frame seq)))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (final-val-seq collapse-seq
                                          final-val-seq-of-collapse-this-lemma-5)
                           ((:rewrite position-of-nthcdr)
                            position-of-cdr position-when-member))
           :expand (take (position-equal x seq) seq)
           :use ((:instance position-when-member (lst seq)
                            (item x))
                 (:instance (:rewrite position-of-nthcdr)
                            (lst seq)
                            (n 1)
                            (item x))))))

(defund frame-addrs-before-seq (frame x seq)
  (if
      (atom seq)
      nil
    (append
     (frame-addrs-before-seq frame x (nthcdr 1 seq))
     (if
         (not
          (equal (frame-val->src
                  (cdr
                   (assoc-equal
                    (nth 0 seq)
                    (frame->frame frame))))
                 x))
         nil
       (take 1 seq)))))

(defthm nat-listp-of-frame-addrs-before-seq
  (implies (and (nat-listp seq))
           (nat-listp (frame-addrs-before-seq frame x seq)))
  :hints (("goal" :in-theory (enable frame-addrs-before-seq))))

(defthm subsetp-of-frame-addrs-before-seq
  (subsetp-equal (frame-addrs-before-seq frame x seq)
                 seq)
  :hints (("goal" :in-theory (enable frame-addrs-before-seq)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (subsetp-equal seq y)
     (subsetp-equal (frame-addrs-before-seq frame x seq)
                    y)))
   (:rewrite
    :corollary
    (implies
     (not (member-equal y seq))
     (not (member-equal y (frame-addrs-before-seq frame x seq)))))))

(defthm frame-addrs-before-seq-of-append
  (equal (frame-addrs-before-seq frame x (append l1 l2))
         (append (frame-addrs-before-seq frame x l2)
                 (frame-addrs-before-seq frame x l1)))
  :hints (("goal" :in-theory (enable frame-addrs-before-seq))))

(defthm no-duplicatesp-of-frame-addrs-before-seq
  (implies (no-duplicatesp-equal seq)
           (no-duplicatesp-equal (frame-addrs-before-seq frame x seq)))
  :hints (("goal" :in-theory (enable frame-addrs-before-seq
                                     intersectp-equal))))

(defthm
  frame-addrs-before-seq-of-collapse-this
  (implies
   (and
    (not (zp x))
    (not (equal x
                (frame-val->src (cdr (assoc-equal y (frame->frame frame)))))))
   (equal (frame-addrs-before-seq (collapse-this frame y)
                                  x seq)
          (frame-addrs-before-seq frame x seq)))
  :hints
  (("goal" :in-theory (enable frame-addrs-before-seq)
    :induct (frame-addrs-before-seq frame x seq))))

(defthm
  member-of-frame-addrs-before-seq
  (implies
   (and (subsetp-equal seq (strip-cars (frame->frame frame)))
        (frame-p (frame->frame frame)))
   (iff
    (member-equal y (frame-addrs-before-seq frame x seq))
    (and (member-equal y seq)
         (consp (assoc-equal y (frame->frame frame)))
         (equal (frame-val->src (cdr (assoc-equal y (frame->frame frame))))
                x))))
  :hints (("goal" :in-theory (enable frame-addrs-before-seq)
           :induct (frame-addrs-before-seq frame x seq)
           :expand (subsetp-equal seq
                                  (strip-cars (frame->frame frame))))))

(defund
  ctx-app-list (fs relpath frame l)
  (b*
      (((when (atom l)) (mv fs t))
       ((mv tail tail-result)
        (ctx-app-list fs relpath frame (cdr l)))
       (fs
        (ctx-app
         tail (final-val (car l) frame)
         (car l)
         (nthcdr (len relpath)
                 (frame-val->path
                  (cdr (assoc-equal (car l)
                                    (frame->frame frame))))))))
    (mv
     fs
     (and
      tail-result (abs-fs-p fs)
      (prefixp relpath
               (frame-val->path
                (cdr (assoc-equal (car l)
                                  (frame->frame frame)))))
      (ctx-app-ok
       tail (car l)
       (nthcdr
        (len relpath)
        (frame-val->path
         (cdr (assoc-equal (car l)
                           (frame->frame frame))))))))))

(defthmd ctx-app-list-of-true-list-fix
  (equal (ctx-app-list fs path-len frame (true-list-fix l))
         (ctx-app-list fs path-len frame l))
  :hints (("goal" :in-theory (enable ctx-app-list))))

(defcong
  list-equiv
  equal (ctx-app-list fs path-len frame l)
  4
  :hints (("goal" :use ((:instance ctx-app-list-of-true-list-fix
                                   (l l-equiv))
                        ctx-app-list-of-true-list-fix))))

(defthm booleanp-of-ctx-app-list
  (booleanp (mv-nth 1 (ctx-app-list fs path-len frame l)))
  :hints (("goal" :in-theory (enable ctx-app-list)))
  :rule-classes :type-prescription)

(defthmd abs-file-alist-p-of-ctx-app-list
  (implies
   (abs-file-alist-p fs)
   (abs-file-alist-p (mv-nth 0 (ctx-app-list fs path-len frame l))))
  :hints (("goal" :in-theory (enable ctx-app-list))))

(defthmd ctx-app-list-correctness-1
  (equal (ctx-app-list fs path-len frame y)
         (mv (mv-nth 0 (ctx-app-list fs path-len frame y))
             (mv-nth 1 (ctx-app-list fs path-len frame y))))
  :hints (("goal" :in-theory (enable ctx-app-list))))

(defthm
  ctx-app-list-of-append
  (equal (ctx-app-list fs path-len frame (append x y))
         (mv-let (y-fs y-result)
           (ctx-app-list fs path-len frame y)
           (mv (mv-nth 0 (ctx-app-list y-fs path-len frame x))
               (and y-result
                    (mv-nth 1
                            (ctx-app-list y-fs path-len frame x))))))
  :hints
  (("goal" :in-theory (e/d (ctx-app-list)
                           ((:rewrite nthcdr-when->=-n-len-l)
                            (:rewrite partial-collapse-correctness-lemma-2)
                            (:definition len)
                            (:definition nthcdr)
                            (:rewrite ctx-app-ok-when-abs-complete)
                            (:definition abs-complete)
                            (:rewrite abs-addrs-when-m1-file-alist-p)
                            (:linear position-when-member)
                            (:linear position-equal-ac-when-member)
                            (:rewrite ctx-app-ok-when-not-natp)
                            (:type-prescription assoc-equal-when-frame-p)
                            (:definition assoc-equal)
                            (:definition member-equal)
                            (:rewrite abs-file-alist-p-correctness-1)
                            (:rewrite true-listp-when-abs-file-alist-p)
                            (:rewrite ctx-app-when-not-natp)))
    :induct (append x y))
   ("subgoal *1/1" :use ctx-app-list-correctness-1)))

(defthm ctx-app-list-when-set-equiv-lemma-1
  (implies (and (not (member-equal (fat32-filename-fix (nth n relpath))
                                   (names-at fs (take n relpath))))
                (< (nfix n) (len relpath)))
           (equal (addrs-at fs relpath) nil))
  :hints (("goal" :in-theory (enable addrs-at names-at))))

(defthmd ctx-app-list-when-set-equiv-lemma-2
  (implies (and (< (nfix n) (len relpath))
                (not (member-equal (fat32-filename-fix (nth n relpath))
                                   (names-at fs (take n relpath)))))
           (equal (names-at fs relpath) nil))
  :hints (("goal" :in-theory (enable names-at))))

;; Bizarre.
(defthm ctx-app-list-when-set-equiv-lemma-4
  (implies (natp (- (len seq)))
           (not (member-equal x seq)))
  :rule-classes :type-prescription)

(encapsulate
  ()

  (local
   (in-theory
    (disable
     (:rewrite abs-file-alist-p-correctness-1)
     (:rewrite
      abs-file-alist-p-when-m1-file-alist-p)
     (:rewrite member-of-abs-fs-fix-when-natp)
     (:rewrite m1-file-alist-p-when-subsetp-equal)
     (:rewrite abs-fs-p-correctness-1)
     subsetp-member
     (:definition nthcdr)
     (:rewrite subsetp-trans2)
     (:rewrite subsetp-trans)
     (:type-prescription assoc-when-zp-len)
     (:definition nth)
     (:rewrite nat-listp-when-unsigned-byte-listp)
     (:linear nth-when-d-e-p)
     (:rewrite ctx-app-ok-when-abs-complete)
     (:rewrite fat32-filename-list-p-of-names-at))))

  (local
   (defthm lemma-1 (equal (+ x (- x) y) (fix y))))

  (defthm
    ctx-app-list-when-set-equiv-lemma-5
    (implies
     (and
      (not
       (equal
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal (car l)
                                                   (frame->frame frame)))))
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
      (prefixp (frame-val->path (cdr (assoc-equal (car l)
                                                  (frame->frame frame))))
               (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
      (not
       (member-equal
        (nth (len (frame-val->path (cdr (assoc-equal (car l)
                                                     (frame->frame frame)))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
        (names-at
         (mv-nth 0
                 (ctx-app-list fs
                               relpath frame (remove-equal x (cdr l))))
         (nthcdr (len relpath)
                 (frame-val->path (cdr (assoc-equal (car l)
                                                    (frame->frame frame))))))))
      (prefixp relpath
               (frame-val->path (cdr (assoc-equal (car l)
                                                  (frame->frame frame))))))
     (equal
      (names-at
       (mv-nth 0
               (ctx-app-list fs
                             relpath frame (remove-equal x (cdr l))))
       (nthcdr (len relpath)
               (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
      nil))
    :hints
    (("goal"
      :in-theory (e/d (take-of-nthcdr list-equiv))
      :use
      (:instance
       (:rewrite ctx-app-list-when-set-equiv-lemma-2)
       (relpath
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
       (fs (mv-nth 0
                   (ctx-app-list fs relpath
                                 frame (remove-equal x (cdr l)))))
       (n (- (len (frame-val->path (cdr (assoc-equal (car l)
                                                     (frame->frame frame)))))
             (len relpath))))
      :expand
      ((:with
        (:rewrite fat32-filename-p-of-nth-when-fat32-filename-list-p)
        (fat32-filename-p
         (nth (len (frame-val->path (cdr (assoc-equal (car l)
                                                      (frame->frame frame)))))
              (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
       (:with
        fat32-filename-fix-when-fat32-filename-p
        (fat32-filename-fix
         (nth
          (len (frame-val->path (cdr (assoc-equal (car l)
                                                  (frame->frame frame)))))
          (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))))))

  (defthm
    ctx-app-list-when-set-equiv-lemma-6
    (implies
     (and
      (consp l)
      (absfat-equiv
       (ctx-app
        (mv-nth 0
                (ctx-app-list fs
                              relpath frame (remove-equal x (cdr l))))
        (final-val x frame)
        x
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
       (mv-nth 0
               (ctx-app-list fs relpath frame (cdr l))))
      (nat-listp l)
      (ctx-app-ok
       (mv-nth 0
               (ctx-app-list fs
                             relpath frame (remove-equal x (cdr l))))
       (car l)
       (nthcdr (len relpath)
               (frame-val->path (cdr (assoc-equal (car l)
                                                  (frame->frame frame))))))
      (prefixp relpath
               (frame-val->path (cdr (assoc-equal (car l)
                                                  (frame->frame frame)))))
      (no-duplicatesp-equal (strip-cars (frame->frame frame)))
      (frame-p (frame->frame frame))
      (mv-nth 1 (collapse frame))
      (not
       (equal
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal (car l)
                                                   (frame->frame frame)))))
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
      (prefixp (frame-val->path (cdr (assoc-equal (car l)
                                                  (frame->frame frame))))
               (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
      (not
       (member-equal
        (nth (len (frame-val->path (cdr (assoc-equal (car l)
                                                     (frame->frame frame)))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
        (names-at
         (mv-nth 0
                 (ctx-app-list fs
                               relpath frame (remove-equal x (cdr l))))
         (nthcdr (len relpath)
                 (frame-val->path (cdr (assoc-equal (car l)
                                                    (frame->frame frame)))))))))
     (ctx-app-ok
      (mv-nth 0
              (ctx-app-list fs relpath frame (cdr l)))
      (car l)
      (nthcdr (len relpath)
              (frame-val->path (cdr (assoc-equal (car l)
                                                 (frame->frame frame)))))))
    :hints
    (("goal"
      :in-theory (e/d (intersectp-equal)
                      ((:rewrite ctx-app-ok-of-ctx-app-1)))
      :use
      (:instance
       (:rewrite ctx-app-ok-of-ctx-app-1)
       (x2-path
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal (car l)
                                                   (frame->frame frame))))))
       (x2 (car l))
       (x3-path
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
       (x3 x)
       (abs-file-alist3 (final-val x frame))
       (abs-file-alist1
        (mv-nth 0
                (ctx-app-list fs relpath
                              frame (remove-equal x (cdr l)))))))))

  (local
   (defthmd
     lemma-2
     (implies
      (and (not (member-equal (fat32-filename-fix (nth n x-path))
                              (names-at abs-file-alist1 (take n x-path))))
           (< (nfix n) (len x-path)))
      (equal (ctx-app-ok abs-file-alist1 x x-path)
             nil))
     :hints (("goal" :do-not-induct t
              :in-theory (enable ctx-app-ok)))))

  (defthm
    ctx-app-list-when-set-equiv-lemma-7
    (implies
     (and
      (not
       (equal
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal (car l)
                                                   (frame->frame frame)))))
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
      (prefixp (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
               (frame-val->path (cdr (assoc-equal (car l)
                                                  (frame->frame frame)))))
      (<=
       0
       (+ (- (len relpath))
          (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
      (not
       (member-equal
        (nth (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
             (frame-val->path (cdr (assoc-equal (car l)
                                                (frame->frame frame)))))
        (names-at
         (mv-nth 0
                 (ctx-app-list fs
                               relpath frame (remove-equal x (cdr l))))
         (nthcdr
          (len relpath)
          (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))))
     (not
      (ctx-app-ok
       (mv-nth 0
               (ctx-app-list fs
                             relpath frame (remove-equal x (cdr l))))
       (car l)
       (nthcdr (len relpath)
               (frame-val->path (cdr (assoc-equal (car l)
                                                  (frame->frame frame))))))))
    :hints
    (("goal" :do-not-induct t
      :in-theory (e/d (take-of-nthcdr list-equiv)
                      ())
      :use
      (:instance
       (:rewrite lemma-2)
       (x-path
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal (car l)
                                                   (frame->frame frame))))))
       (x (car l))
       (abs-file-alist1 (mv-nth 0
                                (ctx-app-list fs relpath
                                              frame (remove-equal x (cdr l)))))
       (n (- (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
             (len relpath))))
      :expand
      ((:with
        (:rewrite fat32-filename-p-of-nth-when-fat32-filename-list-p)
        (fat32-filename-p
         (nth (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
              (frame-val->path (cdr (assoc-equal (car l)
                                                 (frame->frame frame)))))))
       (:with
        fat32-filename-fix-when-fat32-filename-p
        (fat32-filename-fix
         (nth (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
              (frame-val->path (cdr (assoc-equal (car l)
                                                 (frame->frame frame)))))))))))

  (defthm
    ctx-app-list-when-set-equiv-lemma-8
    (implies
     (and
      (absfat-equiv
       (ctx-app
        (mv-nth 0
                (ctx-app-list fs
                              relpath frame (remove-equal x (cdr l))))
        (final-val x frame)
        x
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
       (mv-nth 0
               (ctx-app-list fs relpath frame (cdr l))))
      (ctx-app-ok
       (mv-nth 0
               (ctx-app-list fs
                             relpath frame (remove-equal x (cdr l))))
       (car l)
       (nthcdr (len relpath)
               (frame-val->path (cdr (assoc-equal (car l)
                                                  (frame->frame frame))))))
      (not
       (intersectp-equal
        (names-at (final-val (car l) frame) nil)
        (names-at
         (mv-nth 0
                 (ctx-app-list fs
                               relpath frame (remove-equal x (cdr l))))
         (nthcdr (len relpath)
                 (frame-val->path (cdr (assoc-equal (car l)
                                                    (frame->frame frame))))))))
      (prefixp relpath
               (frame-val->path (cdr (assoc-equal (car l)
                                                  (frame->frame frame)))))
      (not
       (equal
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal (car l)
                                                   (frame->frame frame)))))
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
      (not
       (intersectp-equal
        (names-at (final-val x frame) nil)
        (names-at
         (mv-nth 0
                 (ctx-app-list fs
                               relpath frame (remove-equal x (cdr l))))
         (nthcdr
          (len relpath)
          (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))))
      (prefixp relpath
               (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
     (not
      (intersectp-equal
       (names-at (final-val (car l) frame) nil)
       (names-at
        (mv-nth 0
                (ctx-app-list fs relpath frame (cdr l)))
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal (car l)
                                                   (frame->frame frame)))))))))
    :hints
    (("goal"
      :in-theory
      (e/d (fat32-filename-list-equiv$inline fat32-filename-list-prefixp-alt)
           ((:rewrite names-at-of-ctx-app)))
      :use
      (:instance
       (:rewrite names-at-of-ctx-app)
       (relpath
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal (car l)
                                                   (frame->frame frame))))))
       (x-path
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
       (x x)
       (abs-file-alist (final-val x frame))
       (root (mv-nth 0
                     (ctx-app-list fs relpath
                                   frame (remove-equal x (cdr l)))))))))

  (defthm
    ctx-app-list-when-set-equiv-lemma-9
    (implies
     (and
      (mv-nth 1
              (ctx-app-list fs relpath frame (remove-equal x l)))
      (member-equal x l)
      (nat-listp l)
      (no-duplicatesp-equal (strip-cars (frame->frame frame)))
      (no-duplicatesp-equal l)
      (frame-p (frame->frame frame))
      (mv-nth 1 (collapse frame))
      (ctx-app-ok
       (mv-nth 0
               (ctx-app-list fs relpath frame (remove-equal x l)))
       x
       (nthcdr (len relpath)
               (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
      (not
       (intersectp-equal
        (names-at (final-val x frame) nil)
        (names-at
         (mv-nth 0
                 (ctx-app-list fs relpath frame (remove-equal x l)))
         (nthcdr
          (len relpath)
          (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))))
      (prefixp relpath
               (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
     (and
      (absfat-equiv
       (ctx-app
        (mv-nth 0
                (ctx-app-list fs relpath frame (remove-equal x l)))
        (final-val x frame)
        x
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
       (mv-nth 0 (ctx-app-list fs relpath frame l)))
      (mv-nth 1 (ctx-app-list fs relpath frame l))
      (not
       (intersectp-equal
        (names-at (final-val x frame) nil)
        (names-at
         (mv-nth 0
                 (ctx-app-list fs relpath frame (remove-equal x l)))
         (nthcdr
          (len relpath)
          (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))))))
    :hints
    (("goal"
      :in-theory
      (e/d (ctx-app-list intersectp-equal
                         fat32-filename-list-prefixp-alt
                         fat32-filename-list-equiv)
           ((:rewrite nthcdr-when->=-n-len-l)
            (:rewrite partial-collapse-correctness-lemma-2)
            (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8
                      . 3)
            (:definition len)
            (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
            (:rewrite prefixp-one-way-or-another . 1)
            (:definition assoc-equal)
            (:rewrite nat-listp-if-fat32-masked-entry-list-p)
            (:linear position-when-member)
            (:linear position-equal-ac-when-member)
            (:rewrite ctx-app-list-when-set-equiv-lemma-7)))))))

(encapsulate
  ()

  (local
   (defun
       induction-scheme (l1 l2)
     (cond
      ((and (not (atom l1)))
       (induction-scheme (cdr l1) (remove-equal (car l1) l2)))
      (t (mv l1 l2)))))

  (local (in-theory (enable ctx-app-list)))

  (defthmd
    ctx-app-list-when-set-equiv
    (implies (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                  (no-duplicatesp-equal l1)
                  (no-duplicatesp-equal l2)
                  (set-equiv l1 l2)
                  (nat-listp l2)
                  (frame-p (frame->frame frame))
                  (mv-nth '1 (collapse frame))
                  (mv-nth 1 (ctx-app-list fs relpath frame l1)))
             (and (absfat-equiv (mv-nth 0 (ctx-app-list fs relpath frame l1))
                                (mv-nth 0 (ctx-app-list fs relpath frame l2)))
                  (mv-nth 1 (ctx-app-list fs relpath frame l2))))
    :hints
    (("goal" :induct (induction-scheme l1 l2))
     ("subgoal *1/1.1"
      :in-theory (disable (:rewrite ctx-app-list-when-set-equiv-lemma-9))
      :use (:instance (:rewrite ctx-app-list-when-set-equiv-lemma-9)
                      (l l2)
                      (x (car l1))
                      (frame frame)
                      (relpath relpath)
                      (fs fs))))))

(defthm abs-fs-p-of-ctx-app-list
  (implies (and (abs-fs-p x)
                (mv-nth 1 (ctx-app-list x relpath frame l)))
           (abs-fs-p (mv-nth 0 (ctx-app-list x relpath frame l))))
  :hints (("goal" :in-theory (enable ctx-app-list))))

;; Inductive; probably shouldn't be disabled.
(defthm
  abs-addrs-of-ctx-app-list-lemma-1
  (implies
   (and (abs-file-alist-p x)
        (no-duplicatesp-equal (abs-addrs x))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (frame-p (frame->frame frame))
        (mv-nth 1 (collapse frame)))
   (no-duplicatesp-equal
    (abs-addrs (abs-fs-fix (mv-nth 0 (ctx-app-list x relpath frame l))))))
  :hints
  (("goal"
    :in-theory (enable ctx-app-list)
    :induct (ctx-app-list x relpath frame l)
    :expand
    (:with
     no-duplicatesp-of-abs-addrs-of-abs-fs-fix
     (no-duplicatesp-equal
      (abs-addrs
       (abs-fs-fix
        (ctx-app
         (mv-nth 0
                 (ctx-app-list x relpath frame (cdr l)))
         (final-val (car l) frame)
         (car l)
         (nthcdr
          (len relpath)
          (frame-val->path (cdr (assoc-equal (car l)
                                             (frame->frame frame)))))))))))))

(defthm
  abs-addrs-of-ctx-app-list
  (implies
   (and (frame-p (frame->frame frame))
        (mv-nth 1 (collapse frame))
        (abs-fs-p fs)
        (no-duplicatesp-equal (abs-addrs fs))
        (mv-nth 1 (ctx-app-list fs relpath frame l))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (nat-listp l))
   (and (equal (abs-addrs (mv-nth 0 (ctx-app-list fs relpath frame l)))
               (set-difference-equal (abs-addrs fs) l))
        (subsetp-equal l (abs-addrs fs))))
  :hints
  (("goal"
    :in-theory
    (e/d (ctx-app-list set-difference$-redefinition
                       subsetp-equal
                       abs-addrs-of-ctx-app-lemma-2)
         (set-difference-equal (:rewrite abs-addrs-of-ctx-app-list-lemma-1)
                               (:rewrite subsetp-car-member)
                               (:rewrite subsetp-trans)
                               (:rewrite remove-when-absent)
                               (:linear position-equal-ac-when-member)
                               (:rewrite abs-file-alist-p-correctness-1)
                               (:definition len)
                               (:definition remove-equal)
                               (:rewrite subsetp-member . 1)
                               (:rewrite abs-addrs-when-m1-file-contents-p)
                               (:type-prescription len-when-consp)))
    :induct (ctx-app-list fs relpath frame l))
   ("subgoal *1/2" :use (:instance (:rewrite abs-addrs-of-ctx-app-list-lemma-1)
                                   (l (cdr l))
                                   (frame frame)
                                   (relpath relpath)
                                   (x fs)))))

(defund
  ctx-app-list-seq (fs relpath frame l seq)
  (b*
      (((when (atom l)) (mv fs t))
       ((mv tail tail-result)
        (ctx-app-list-seq fs relpath frame (cdr l) seq))
       (fs
        (ctx-app
         tail (final-val-seq (car l) frame seq)
         (car l)
         (nthcdr (len relpath)
                 (frame-val->path
                  (cdr (assoc-equal (car l)
                                    (frame->frame frame))))))))
    (mv
     fs
     (and
      tail-result (abs-fs-p fs)
      (prefixp relpath
               (frame-val->path
                (cdr (assoc-equal (car l)
                                  (frame->frame frame)))))
      (ctx-app-ok
       tail (car l)
       (nthcdr
        (len relpath)
        (frame-val->path
         (cdr (assoc-equal (car l)
                           (frame->frame frame))))))))))

(defthm booleanp-of-ctx-app-list-seq
  (booleanp (mv-nth 1
                    (ctx-app-list-seq fs relpath frame l seq)))
  :hints (("goal" :in-theory (enable ctx-app-list-seq)))
  :rule-classes :type-prescription)

(defthmd ctx-app-list-seq-correctness-1
  (equal (ctx-app-list-seq fs relpath frame y seq)
         (mv (mv-nth 0
                     (ctx-app-list-seq fs relpath frame y seq))
             (mv-nth 1
                     (ctx-app-list-seq fs relpath frame y seq))))
  :hints (("goal" :in-theory (enable ctx-app-list-seq))))

(defthm
  ctx-app-list-seq-of-append
  (equal (ctx-app-list-seq fs relpath frame (append x y)
                           seq)
         (b* (((mv y-fs y-result)
               (ctx-app-list-seq fs relpath frame y seq)))
           (mv (mv-nth 0
                       (ctx-app-list-seq y-fs relpath frame x seq))
               (and y-result
                    (mv-nth 1
                            (ctx-app-list-seq y-fs relpath frame x seq))))))
  :hints
  (("goal" :in-theory (e/d (ctx-app-list-seq)
                           ((:rewrite nthcdr-when->=-n-len-l)
                            (:rewrite partial-collapse-correctness-lemma-2)
                            (:definition len)
                            (:definition nthcdr)
                            (:rewrite ctx-app-ok-when-abs-complete)
                            (:definition abs-complete)
                            (:definition member-equal)
                            (:linear position-when-member)
                            (:linear position-equal-ac-when-member)
                            (:rewrite ctx-app-ok-when-not-natp)
                            (:definition assoc-equal)
                            (:rewrite abs-file-alist-p-correctness-1)
                            (:rewrite true-listp-when-abs-file-alist-p)
                            (:rewrite ctx-app-when-not-natp)))
    :induct (append x y))
   ("subgoal *1/1''" :use ctx-app-list-seq-correctness-1)))

(defthm
  abs-fs-p-of-ctx-app-list-seq
  (implies (and (abs-fs-p fs)
                (mv-nth 1
                        (ctx-app-list-seq fs relpath frame l seq)))
           (abs-fs-p (mv-nth 0
                             (ctx-app-list-seq fs relpath frame l seq))))
  :hints
  (("goal" :in-theory (e/d (ctx-app-list-seq set-difference$-redefinition)
                           (set-difference-equal))
    :induct (ctx-app-list-seq fs relpath frame l seq))))

(defthmd
  abs-addrs-of-ctx-app-list-seq
  (implies
   (and (abs-fs-p fs)
        (no-duplicatesp-equal (abs-addrs fs))
        (mv-nth 1
                (ctx-app-list-seq fs relpath frame l seq))
        (nat-listp l)
        (nat-listp seq)
        (valid-seqp frame seq)
        (subsetp-equal l seq)
        (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (and
    (equal (abs-addrs (mv-nth 0
                              (ctx-app-list-seq fs relpath frame l seq)))
           (set-difference-equal (abs-addrs fs)
                                 l))
    (subsetp-equal l (abs-addrs fs))))
  :hints
  (("goal" :in-theory (e/d (ctx-app-list-seq set-difference$-redefinition subsetp-equal
                                             ABS-ADDRS-OF-CTX-APP-LEMMA-2)
                           (set-difference-equal))
    :induct (ctx-app-list-seq fs relpath frame l seq))))

;; This could potentially get really expensive if it's a rewrite rule..
(defthm
  ctx-app-ok-of-ctx-app-list-seq-lemma-1
  (implies (and (valid-seqp frame seq)
                (no-duplicatesp-equal (strip-cars (frame->frame frame))))
           (and (subsetp-equal seq (strip-cars (frame->frame frame)))
                (no-duplicatesp-equal seq)
                (not (member-equal (car seq) (cdr seq)))))
  :hints (("goal" :in-theory (enable valid-seqp collapse-seq)
           :induct (collapse-seq frame seq)))
  :rule-classes
  (:forward-chaining
   (:rewrite
    :corollary
    (implies (and (valid-seqp frame seq)
                  (no-duplicatesp-equal (strip-cars (frame->frame frame))))
             (subsetp-equal seq
                            (strip-cars (frame->frame frame)))))))

(defthm
  ctx-app-ok-of-ctx-app-list-seq
  (implies (and (not (member-equal x l))
                (mv-nth 1
                        (ctx-app-list-seq fs relpath frame l seq))
                (nat-listp l)
                (nat-listp seq)
                (valid-seqp frame seq)
                (subsetp-equal l seq)
                (no-duplicatesp-equal (strip-cars (frame->frame frame))))
           (iff (ctx-app-ok (mv-nth 0
                                    (ctx-app-list-seq fs relpath frame l seq))
                            x x-path)
                (ctx-app-ok fs x x-path)))
  :hints (("goal" :in-theory (enable ctx-app-list-seq)
           :induct (ctx-app-list-seq fs relpath frame l seq))))

(defthm
  ctx-app-list-seq-of-collapse-this
  (implies (and (valid-seqp frame seq)
                (frame-p (frame->frame frame))
                (not (member-equal (car seq) l))
                (subsetp-equal l seq)
                (nat-listp seq))
           (equal (ctx-app-list-seq fs
                                    relpath (collapse-this frame (car seq))
                                    l (cdr seq))
                  (ctx-app-list-seq fs relpath frame l seq)))
  :hints (("goal" :in-theory (enable ctx-app-list-seq))))

(local
 (defund
   seq-this
   (frame)
   (declare
    (xargs :measure (len (frame->frame frame))
           :verify-guards nil))
   (b*
       (((when (atom (frame->frame frame))) nil)
        (next-frame (collapse-iter frame 1))
        ((unless (< (len (frame->frame next-frame)) (len (frame->frame frame))))
         nil))
     (cons (1st-complete (frame->frame frame))
           (seq-this
            next-frame)))))

;; While it would be nice to see this have no hypothesis, the way
;; collapse-iter-is-collapse has no hypotheses, the fact is that it won't work
;; because of the stupid truth that a frame with duplicate variables in it will
;; be accepted by collapse but not by collapse-seq.
(local
 (defthmd
   collapse-seq-of-seq-this-is-collapse
   (implies (no-duplicatesp-equal (strip-cars (frame->frame frame)))
            (equal (collapse frame)
                   (mv (frame->root (collapse-seq frame (seq-this frame)))
                       (equal (len (seq-this frame))
                              (len (frame->frame frame))))))
   :hints
   (("goal" :in-theory (e/d (collapse collapse-seq seq-this collapse-iter)
                            ((:definition assoc-equal)
                             (:rewrite nthcdr-when->=-n-len-l)
                             (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8 . 3)
                             (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8 . 2)
                             (:definition remove-equal)
                             (:rewrite remove-when-absent)))
     :induct (seq-this frame)
     :expand ((collapse frame)
              (collapse-iter frame 1))))))

(local
 (defthm nat-listp-of-seq-this
   (nat-listp (seq-this frame))
   :hints (("goal" :in-theory (enable seq-this)))))

(local
 (defthm
   natp-of-nth-of-seq-this
   (implies (< (nfix n) (len (seq-this frame)))
            (natp (nth n (seq-this frame))))
   :hints (("goal" :in-theory (disable member-of-a-nat-list)
            :use (:instance member-of-a-nat-list
                            (x (nth n (seq-this frame)))
                            (lst (seq-this frame)))))
   :rule-classes
   (:type-prescription
    (:rewrite :corollary (implies (< (nfix n) (len (seq-this frame)))
                                  (integerp (nth n (seq-this frame)))))
    (:linear :corollary (implies (< (nfix n) (len (seq-this frame)))
                                 (<= 0 (nth n (seq-this frame))))))))

(local
 (defthm no-duplicatesp-of-seq-this-lemma-1
   (subsetp-equal (seq-this frame)
                  (strip-cars (frame->frame frame)))
   :hints (("goal" :in-theory (enable seq-this collapse-iter)
            :induct (seq-this frame)
            :expand (collapse-iter frame 1)))
   :rule-classes
   (:rewrite
    (:rewrite
     :corollary
     (implies
      (not (member-equal x
                         (strip-cars (frame->frame frame))))
      (not (member-equal x (seq-this frame)))))
    (:rewrite
     :corollary
     (implies
      (subsetp-equal x (seq-this frame))
      (subsetp-equal x (strip-cars (frame->frame frame)))))
    (:rewrite
     :corollary
     (implies
      (subsetp-equal (strip-cars (frame->frame frame)) y)
      (subsetp-equal (seq-this frame) y))))))

(local
 (defthm no-duplicatesp-of-seq-this
   (no-duplicatesp-equal (seq-this frame))
   :hints (("goal" :in-theory (enable seq-this)
            :induct (seq-this frame)
            :expand (collapse-iter frame 1)))))

;; Enabling this theorem suddenly brings a lot of things to a halt, lol.
(local
 (defthmd
   nth-of-seq-this
   (implies
    (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
         (< (nfix n) (len (seq-this frame))))
    (equal
     (nth n (seq-this frame))
     (1st-complete
      (frame->frame (collapse-seq frame (take n (seq-this frame)))))))
   :hints
   (("goal" :in-theory (e/d (seq-this collapse-iter collapse-seq)
                            ((:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
                             (:definition member-equal)
                             (:definition no-duplicatesp-equal)
                             (:definition remove-equal)
                             (:definition nthcdr)
                             (:definition assoc-equal)
                             (:rewrite nthcdr-when->=-n-len-l)))
     :induct (collapse-iter frame n)
     :expand (seq-this frame)))))

(local
 (defthm member-of-seq-this-when-zp
   (implies (zp x)
            (not (member-equal x (seq-this frame))))
   :hints (("goal" :in-theory (enable seq-this collapse-iter)))
   :rule-classes :type-prescription))

(local
 (defthm
   nth-of-seq-this-1
   (implies (< (nfix n) (len (seq-this frame)))
            (not (zp (nth n (seq-this frame)))))
   :hints (("goal" :do-not-induct t
            :in-theory (disable (:rewrite member-equal-nth))
            :use (:instance (:rewrite member-equal-nth)
                            (l (seq-this frame)))))
   :rule-classes
   (:type-prescription
    (:linear :corollary (implies (< (nfix n) (len (seq-this frame)))
                                 (< 0 (nth n (seq-this frame)))))
    (:rewrite :corollary (implies (< (nfix n) (len (seq-this frame)))
                                  (integerp (nth n (seq-this frame))))))))

(local
 (defthm len-of-seq-this-1
   (<= (len (seq-this frame))
       (len (frame->frame frame)))
   :hints (("goal" :in-theory (enable seq-this)))
   :rule-classes :linear))

(defthmd
  frame-addrs-before-seq-of-collapse-this-1
  (implies (not (member-equal y seq))
           (equal (frame-addrs-before-seq (collapse-this frame y)
                                          x seq)
                  (frame-addrs-before-seq frame x seq)))
  :hints
  (("goal" :in-theory (enable frame-addrs-before-seq)
    :induct (frame-addrs-before-seq frame x seq))))

(defthm
  valid-seqp-after-collapse-this-lemma-1
  (implies (nat-listp seq)
           (equal (final-val-seq (car seq) frame seq)
                  (frame-val->dir (cdr (assoc-equal (car seq)
                                                    (frame->frame frame))))))
  :hints (("goal" :in-theory (enable final-val-seq
                                     position-equal collapse-seq)
           :do-not-induct t)))

(defthm
  valid-seqp-after-collapse-this-lemma-2
  (implies (and (valid-seqp frame seq)
                (no-duplicatesp-equal (strip-cars (frame->frame frame))))
           (valid-seqp (collapse-this frame (car seq))
                       (cdr seq)))
  :hints (("goal" :in-theory (enable valid-seqp collapse-seq)))
  :rule-classes (:rewrite :type-prescription))

(local
 (defthm
   valid-seqp-after-collapse-this-lemma-3
   (implies
    (and (< 0
            (frame-val->src (cdr (assoc-equal (car seq)
                                              (frame->frame frame)))))
         (frame-p (frame->frame frame))
         (valid-seqp frame seq)
         (no-duplicatesp-equal (strip-cars (frame->frame frame))))
    (prefixp
     (frame-val->path
      (cdr
       (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                      (frame->frame frame))))
                    (frame->frame frame))))
     (frame-val->path (cdr (assoc-equal (car seq)
                                        (frame->frame frame))))))
   :hints (("goal" :in-theory (enable valid-seqp collapse-seq)))))

(local
 (defthm valid-seqp-after-collapse-this-lemma-4
   (implies (atom (frame->frame frame))
            (iff (valid-seqp frame seq) (atom seq)))
   :hints (("goal" :in-theory (enable valid-seqp collapse-seq)))))

(defthmd
  valid-seqp-after-collapse-this-lemma-5
  (implies
   (and (abs-separate (frame->frame frame))
        (dist-names (frame->root frame)
                    nil (frame->frame frame))
        (frame-p (frame->frame frame))
        (valid-seqp frame seq)
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (nat-listp seq))
   (and (equal (frame->root (collapse-seq frame seq))
               (mv-nth 0
                       (ctx-app-list-seq (frame->root frame)
                                         nil frame
                                         (frame-addrs-before-seq frame 0 seq)
                                         seq)))
        (mv-nth 1
                (ctx-app-list-seq (frame->root frame)
                                  nil frame
                                  (frame-addrs-before-seq frame 0 seq)
                                  seq))))
  :hints (("goal" :induct (collapse-seq frame seq)
           :in-theory (e/d (collapse-seq frame-addrs-before-seq
                                         ctx-app-list-seq
                                         frame-addrs-before-seq-of-collapse-this-1)
                           ((:definition no-duplicatesp-equal)
                            (:definition member-equal)
                            (:rewrite nthcdr-when->=-n-len-l)
                            (:definition remove-assoc-equal)
                            (:definition len))))))

(defthmd
  valid-seqp-after-collapse-this-lemma-6
  (implies (and (not (member-equal x2
                                   (frame-addrs-before-seq frame 0 seq)))
                (abs-separate (frame->frame frame))
                (dist-names (frame->root frame)
                            nil (frame->frame frame))
                (frame-p (frame->frame frame))
                (valid-seqp frame seq)
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (nat-listp seq))
           (iff (ctx-app-ok (frame->root (collapse-seq frame seq))
                            x2 x2-path)
                (ctx-app-ok (frame->root frame)
                            x2 x2-path)))
  :hints (("goal" :in-theory (disable valid-seqp-after-collapse-this-lemma-5)
           :use valid-seqp-after-collapse-this-lemma-5)))

(local
 (defthm
   valid-seqp-after-collapse-this-lemma-7
   (implies
    (equal (nth (+ -1 n)
                (seq-this (collapse-this frame x)))
           (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
    (not
     (member-equal
      (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
      (frame-addrs-before-seq
       frame
       (frame-val->src$inline
        (cdr
         (assoc-equal
          (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
          (frame->frame frame))))
       (take (binary-+ -1 n)
             (seq-this (collapse-this frame x)))))))
   :hints
   (("goal"
     :in-theory (disable (:rewrite member-equal-nth-take-when-no-duplicatesp))
     :use (:instance (:rewrite member-equal-nth-take-when-no-duplicatesp)
                     (l (seq-this (collapse-this frame x)))
                     (n (+ -1 n))
                     (x (nth (+ -1 n) (seq-this (collapse-this frame x)))))))))

(defthm
  valid-seqp-after-collapse-this-lemma-8
  (implies (not (member-equal x seq))
           (and
            (equal (frame-val->path
                    (cdr (assoc-equal x
                                      (frame->frame (collapse-seq frame seq)))))
                   (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
            (equal (frame-val->src
                    (cdr (assoc-equal x
                                      (frame->frame (collapse-seq frame seq)))))
                   (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
            (iff (consp (assoc-equal x
                                     (frame->frame (collapse-seq frame seq))))
                 (consp (assoc-equal x (frame->frame frame))))))
  :hints (("goal" :in-theory (enable collapse-seq valid-seqp))))

(local
 (defthm
   valid-seqp-after-collapse-this-lemma-9
   (implies
    (equal (nth (+ -1 n)
                (seq-this (collapse-this frame x)))
           (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
    (and
     (equal
      (frame-val->path
       (cdr
        (assoc-equal
         (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
         (frame->frame
          (collapse-seq (collapse-this frame x)
                        (take (+ -1 n)
                              (seq-this (collapse-this frame x))))))))
      (frame-val->path
       (cdr (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame (collapse-this frame x))))))
     (equal
      (frame-val->src
       (cdr
        (assoc-equal
         (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
         (frame->frame
          (collapse-seq (collapse-this frame x)
                        (take (+ -1 n)
                              (seq-this (collapse-this frame x))))))))
      (frame-val->src
       (cdr (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame (collapse-this frame x))))))
     (iff
      (consp
       (assoc-equal
        (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
        (frame->frame
         (collapse-seq (collapse-this frame x)
                       (take (+ -1 n)
                             (seq-this (collapse-this frame x)))))))
      (consp
       (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                    (frame->frame (collapse-this frame x)))))))
   :hints
   (("goal"
     :in-theory (disable (:rewrite member-equal-nth-take-when-no-duplicatesp))
     :use (:instance (:rewrite member-equal-nth-take-when-no-duplicatesp)
                     (l (seq-this (collapse-this frame x)))
                     (n (+ -1 n))
                     (x (nth (+ -1 n) (seq-this (collapse-this frame x)))))))))

(local
 (defthm
   valid-seqp-after-collapse-this-lemma-10
   (implies
    (and
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
     (not
      (consp
       (abs-addrs
        (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))))))
    (not
     (equal
      (nth (+ -1 n)
           (seq-this (collapse-this frame
                                    (1st-complete (frame->frame frame)))))
      (1st-complete (frame->frame frame)))))
   :hints
   (("goal"
     :in-theory (e/d (seq-this collapse-iter collapse-seq)
                     ((:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
                      (:definition member-equal)
                      (:definition no-duplicatesp-equal)
                      (:definition remove-equal)
                      (:definition nthcdr)
                      (:definition assoc-equal)
                      (:rewrite nthcdr-when->=-n-len-l)
                      (:rewrite member-equal-nth)))
     :use
     (:instance
      (:rewrite member-equal-nth)
      (l (seq-this (collapse-this frame
                                  (1st-complete (frame->frame frame)))))
      (n (+ -1 n)))))))

;; Inductive, so probably best left enabled.
(local
 (defthm
   valid-seqp-after-collapse-this-lemma-11
   (implies
    (and (< (nfix n) (len (seq-this frame)))
         (not (zp (frame-val->src (cdr (assoc-equal (nth n (seq-this frame))
                                                    (frame->frame frame)))))))
    (consp
     (assoc-equal
      (frame-val->src (cdr (assoc-equal (nth n (seq-this frame))
                                        (frame->frame frame))))
      (frame->frame (collapse-seq frame (take n (seq-this frame)))))))
   :hints
   (("goal" :in-theory (e/d (seq-this collapse-iter collapse-seq member-of-take)
                            ((:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
                             (:definition member-equal)
                             (:definition no-duplicatesp-equal)
                             (:definition remove-equal)
                             (:definition nthcdr)
                             (:definition assoc-equal)
                             (:rewrite nthcdr-when->=-n-len-l)
                             (:rewrite member-equal-nth)))
     :induct (collapse-iter frame n)
     :expand ((seq-this frame))))))

(local
 (defthmd
   valid-seqp-after-collapse-this-lemma-12
   (implies
    (and (<= (nfix n) (len (seq-this frame)))
         (no-duplicatesp-equal (strip-cars (frame->frame frame))))
    (iff
     (consp
      (assoc-equal
       x
       (frame->frame (collapse-seq frame (take n (seq-this frame))))))
     (and
      (consp (assoc-equal x (frame->frame frame)))
      (not (member-equal x (take n (seq-this frame)))))))
   :hints
   (("goal"
     :in-theory (e/d (seq-this collapse-seq collapse-iter)
                     ((:definition assoc-equal)
                      (:rewrite take-of-len-free)
                      (:definition member-equal)
                      (:rewrite nthcdr-when->=-n-len-l)
                      (:definition remove-equal)
                      (:rewrite remove-when-absent)
                      (:definition strip-cars)))
     :induct (collapse-iter frame n)
     :expand
     ((seq-this frame)
      (collapse-seq frame
                    (cons (1st-complete (frame->frame frame))
                          (take (+ -1 n)
                                (seq-this (collapse-iter frame 1))))))))))

(local
 (defthmd
   valid-seqp-after-collapse-this-lemma-13
   (implies
    (and
     (< (nfix n) (len (seq-this frame)))
     (not (zp (frame-val->src
               (cdr (assoc-equal (nth n (seq-this frame))
                                 (frame->frame frame))))))
     (no-duplicatesp-equal (strip-cars (frame->frame frame))))
    (not
     (member-equal
      (frame-val->src (cdr (assoc-equal (nth n (seq-this frame))
                                        (frame->frame frame))))
      (take n (seq-this frame)))))
   :hints
   (("goal"
     :in-theory (disable valid-seqp-after-collapse-this-lemma-11)
     :do-not-induct t
     :use
     ((:instance
       valid-seqp-after-collapse-this-lemma-12
       (x (frame-val->src
           (cdr (assoc-equal (nth n (seq-this frame))
                             (frame->frame frame))))))
      valid-seqp-after-collapse-this-lemma-11)))))

(local
 (defthm
   valid-seqp-after-collapse-this-lemma-14
   (implies
    (and
     (no-duplicatesp-equal (strip-cars (frame->frame frame)))
     (equal (nth (+ -1 n)
                 (seq-this (collapse-this frame x)))
            (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
     (<
      0
      (frame-val->src
       (cdr (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame))))))
    (not
     (member-equal
      (frame-val->src
       (cdr (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame))))
      (take (+ -1 n)
            (seq-this (collapse-this frame x))))))
   :hints
   (("goal"
     :use (:instance (:rewrite valid-seqp-after-collapse-this-lemma-13)
                     (frame (collapse-this frame x))
                     (n (+ -1 n)))))))

;; Inductive, so probably best left enabled etc.
(defthm
  valid-seqp-after-collapse-this-lemma-15
  (implies
   (consp (assoc-equal y
                       (frame->frame (collapse-seq frame seq))))
   (and
    (equal (frame-val->src
            (cdr (assoc-equal y
                              (frame->frame (collapse-seq frame seq)))))
           (frame-val->src (cdr (assoc-equal y (frame->frame frame)))))
    (equal (frame-val->path
            (cdr (assoc-equal y
                              (frame->frame (collapse-seq frame seq)))))
           (frame-val->path (cdr (assoc-equal y (frame->frame frame)))))))
  :hints (("goal" :in-theory (enable collapse-seq))))

(local
 (defthm
   valid-seqp-after-collapse-this-lemma-16
   (implies
    (and
     (equal
      (len
       (frame->frame (collapse-seq (collapse-this frame x)
                                   (take (+ -1 n)
                                         (seq-this (collapse-this frame x))))))
      (+ (- n) (len (frame->frame frame))))
     (mv-nth 1 (collapse frame))
     (abs-complete
      (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
     (no-duplicatesp-equal (strip-cars (frame->frame frame)))
     (< 0
        (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
     (equal (nth (+ -1 n)
                 (seq-this (collapse-this frame x)))
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
    (equal
     (len
      (frame->frame
       (collapse-this
        (collapse-seq (collapse-this frame x)
                      (take (+ -1 n)
                            (seq-this (collapse-this frame x))))
        (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))))
     (+ -1 (- n)
        (len (frame->frame frame)))))
   :hints
   (("goal"
     :cases
     ((zp
       (frame-val->src
        (cdr
         (assoc-equal
          (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
          (frame->frame
           (collapse-seq (collapse-this frame x)
                         (take (+ -1 n)
                               (seq-this (collapse-this frame x))))))))))))))

(defthm
  valid-seqp-after-collapse-this-lemma-17
  (implies
   (or
    (zp (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
    (consp
     (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame))))
   (subsetp-equal (strip-cars (frame->frame (collapse-this frame x)))
                  (strip-cars (frame->frame frame))))
  :hints (("goal" :in-theory (enable collapse-this))))

(local
 (defthm
   valid-seqp-after-collapse-this-lemma-18
   (implies (and (not (zp n))
                 (frame-p (frame->frame frame))
                 (mv-nth 1 (collapse frame))
                 (<= n
                     (len (seq-this (collapse-this frame x)))))
            (consp (assoc-equal (nth (+ -1 n)
                                     (seq-this (collapse-this frame x)))
                                (frame->frame frame))))
   :hints
   (("goal"
     :in-theory (disable (:rewrite subsetp-trans)
                         (:rewrite subsetp-member . 1))
     :use
     ((:instance (:rewrite subsetp-member . 1)
                 (y (strip-cars (frame->frame frame)))
                 (a (nth (+ -1 n)
                         (seq-this (collapse-this frame x))))
                 (x (seq-this (collapse-this frame x))))
      (:instance (:rewrite subsetp-trans)
                 (z (strip-cars (frame->frame frame)))
                 (x x)
                 (y (strip-cars (frame->frame (collapse-this frame x))))))))))

(local
 (defthm
   valid-seqp-after-collapse-this-lemma-19
   (implies (and (mv-nth 1 (collapse frame))
                 (not (zp x)))
            (not (equal (nth (+ -1 n)
                             (seq-this (collapse-this frame x)))
                        x)))
   :hints (("goal" :in-theory (disable (:rewrite member-equal-nth))
            :use (:instance (:rewrite member-equal-nth)
                            (l (seq-this (collapse-this frame x)))
                            (n (+ -1 n)))))))

(local
 (defthm
   valid-seqp-after-collapse-this-lemma-20
   (implies
    (and
     (mv-nth 1 (collapse frame))
     (not (zp x))
     (<= n
         (len (seq-this (collapse-this frame x))))
     (< 0
        (nth (+ -1 n)
             (seq-this (collapse-this frame x))))
     (not (equal (nth (+ -1 n)
                      (seq-this (collapse-this frame x)))
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
     (< 0
        (frame-val->src
         (cdr (assoc-equal (nth (+ -1 n)
                                (seq-this (collapse-this frame x)))
                           (frame->frame frame))))))
    (consp
     (assoc-equal
      (frame-val->src
       (cdr (assoc-equal (nth (+ -1 n)
                              (seq-this (collapse-this frame x)))
                         (frame->frame frame))))
      (frame->frame
       (collapse-seq (collapse-this frame x)
                     (take (+ -1 n)
                           (seq-this (collapse-this frame x))))))))
   :hints
   (("goal"
     :in-theory (disable (:rewrite valid-seqp-after-collapse-this-lemma-11))
     :use (:instance (:rewrite valid-seqp-after-collapse-this-lemma-11)
                     (frame (collapse-this frame x))
                     (n (+ -1 n)))))))

(local
 (defthm
   valid-seqp-after-collapse-this-lemma-21
   (implies
    (and
     (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            0)
     (not (zp n))
     (equal
      (len
       (frame->frame (collapse-seq (collapse-this frame x)
                                   (take (+ -1 n)
                                         (seq-this (collapse-this frame x))))))
      (+ (- n) (len (frame->frame frame))))
     (frame-p (frame->frame frame))
     (mv-nth 1 (collapse frame))
     (consp (assoc-equal x (frame->frame frame)))
     (no-duplicatesp-equal (strip-cars (frame->frame frame)))
     (<= n
         (len (seq-this (collapse-this frame x))))
     (< 0
        (nth (+ -1 n)
             (seq-this (collapse-this frame x)))))
    (equal
     (len
      (frame->frame
       (collapse-this (collapse-seq (collapse-this frame x)
                                    (take (+ -1 n)
                                          (seq-this (collapse-this frame x))))
                      (nth (+ -1 n)
                           (seq-this (collapse-this frame x))))))
     (+ -1 (- n)
        (len (frame->frame frame)))))
   :hints
   (("goal"
     :cases
     ((equal
       (frame-val->src
        (cdr
         (assoc-equal
          (nth (+ -1 n)
               (seq-this (collapse-this frame x)))
          (frame->frame
           (collapse-seq (collapse-this frame x)
                         (take (+ -1 n)
                               (seq-this (collapse-this frame x))))))))
       0))))))

(local
 (defthm
   valid-seqp-after-collapse-this-lemma-22
   (implies
    (and (equal (frame-val->src
                 (cdr (assoc-equal (nth (+ -1 n)
                                        (seq-this (collapse-this frame x)))
                                   (frame->frame frame))))
                (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
         (frame-p (frame->frame frame))
         (mv-nth 1 (collapse frame))
         (consp (assoc-equal x (frame->frame frame)))
         (no-duplicatesp-equal (strip-cars (frame->frame frame)))
         (<= n
             (len (seq-this (collapse-this frame x))))
         (< 0
            (nth (+ -1 n)
                 (seq-this (collapse-this frame x))))
         (< 0
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
    (consp
     (assoc-equal
      (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
      (frame->frame
       (collapse-seq (collapse-this frame x)
                     (take (+ -1 n)
                           (seq-this (collapse-this frame x))))))))
   :hints
   (("goal" :in-theory (e/d (valid-seqp collapse-seq seq-this
                                        consp-of-set-difference$
                                        valid-seqp-after-collapse-this-lemma-6)
                            ((:rewrite valid-seqp-after-collapse-this-lemma-20)
                             collapse-seq-of-collapse-seq
                             take set-difference-equal
                             (:definition member-equal)
                             (:rewrite different-from-own-src-1)
                             (:definition assoc-equal)
                             (:definition no-duplicatesp-equal)
                             (:rewrite final-val-seq-of-collapse-this-lemma-2)
                             (:rewrite nthcdr-when->=-n-len-l)
                             (:rewrite m1-file-alist-p-of-final-val-seq-lemma-2)))
     :use (:rewrite valid-seqp-after-collapse-this-lemma-20)))))

(defthm
  valid-seqp-after-collapse-this-lemma-23
  (implies
   (and
    (or
     (equal (frame-val->src (cdr (assoc-equal (car seq)
                                              (frame->frame frame))))
            0)
     (not (equal x
                 (frame-val->src (cdr (assoc-equal (car seq)
                                                   (frame->frame frame)))))))
    (frame-p (frame->frame frame))
    (consp
     (assoc-equal x
                  (frame->frame (collapse-seq (collapse-this frame (car seq))
                                              (cdr seq))))))
   (equal (frame-addrs-before-seq (collapse-this frame (car seq))
                                  x (cdr seq))
          (frame-addrs-before-seq frame x seq)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (frame-addrs-before-seq)
                    ((:rewrite frame-p-of-frame->frame-of-collapse-seq)))
    :use (:instance (:rewrite frame-p-of-frame->frame-of-collapse-seq)
                    (seq (cdr seq))
                    (frame (collapse-this frame (car seq)))))))

(defthm
  valid-seqp-after-collapse-this-lemma-24
  (implies
   (and
    (equal
     (frame-val->dir
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal (car seq)
                                              (frame->frame frame))))
            (frame->frame (collapse-seq (collapse-this frame (car seq))
                                        (cdr seq))))))
     (mv-nth
      0
      (ctx-app-list-seq
       (ctx-app
        (frame-val->dir
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal (car seq)
                                                 (frame->frame frame))))
               (frame->frame frame))))
        (frame-val->dir (cdr (assoc-equal (car seq)
                                          (frame->frame frame))))
        (car seq)
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (car seq)
                                                   (frame->frame frame))))
                 (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal (car seq)
                                            (frame->frame frame))))))
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal (car seq)
                                                (frame->frame frame))))
              (frame->frame frame))))
       frame
       (frame-addrs-before-seq
        frame
        (frame-val->src (cdr (assoc-equal (car seq)
                                          (frame->frame frame))))
        (cdr seq))
       seq)))
    (mv-nth
     1
     (ctx-app-list-seq
      (ctx-app
       (frame-val->dir
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal (car seq)
                                                (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->dir (cdr (assoc-equal (car seq)
                                         (frame->frame frame))))
       (car seq)
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal (car seq)
                                                  (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal (car seq)
                                           (frame->frame frame))))))
      (frame-val->path
       (cdr
        (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                       (frame->frame frame))))
                     (frame->frame frame))))
      frame
      (frame-addrs-before-seq
       frame
       (frame-val->src (cdr (assoc-equal (car seq)
                                         (frame->frame frame))))
       (cdr seq))
      seq))
    (abs-separate (frame->frame frame))
    (frame-p (frame->frame frame))
    (consp
     (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                    (frame->frame frame))))
                  (frame->frame (collapse-seq (collapse-this frame (car seq))
                                              (cdr seq)))))
    (valid-seqp frame seq)
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (nat-listp seq))
   (and
    (equal
     (frame-val->dir
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal (car seq)
                                              (frame->frame frame))))
            (frame->frame (collapse-seq (collapse-this frame (car seq))
                                        (cdr seq))))))
     (mv-nth
      0
      (ctx-app-list-seq
       (frame-val->dir
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal (car seq)
                                                (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal (car seq)
                                                (frame->frame frame))))
              (frame->frame frame))))
       frame
       (frame-addrs-before-seq
        frame
        (frame-val->src (cdr (assoc-equal (car seq)
                                          (frame->frame frame))))
        seq)
       seq)))
    (mv-nth
     1
     (ctx-app-list-seq
      (frame-val->dir
       (cdr
        (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                       (frame->frame frame))))
                     (frame->frame frame))))
      (frame-val->path
       (cdr
        (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                       (frame->frame frame))))
                     (frame->frame frame))))
      frame
      (frame-addrs-before-seq
       frame
       (frame-val->src (cdr (assoc-equal (car seq)
                                         (frame->frame frame))))
       seq)
      seq))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (collapse-seq frame-addrs-before-seq
                                  ctx-app-list-seq
                                  frame-addrs-before-seq-of-collapse-this-1)
                    ((:definition no-duplicatesp-equal)
                     (:definition member-equal)
                     (:rewrite nthcdr-when->=-n-len-l)
                     (:definition remove-assoc-equal)
                     (:definition len)))
    :expand ((frame-addrs-before-seq
              frame
              (frame-val->src (cdr (assoc-equal (car seq)
                                                (frame->frame frame))))
              seq)))))

(defthm
  valid-seqp-after-collapse-this-lemma-25
  (implies
   (and (abs-separate (frame->frame frame))
        (frame-p (frame->frame frame))
        (consp (assoc-equal x
                            (frame->frame (collapse-seq frame seq))))
        (valid-seqp frame seq)
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (nat-listp seq))
   (and
    (equal
     (frame-val->dir
      (cdr (assoc-equal x
                        (frame->frame (collapse-seq frame seq)))))
     (mv-nth 0
             (ctx-app-list-seq
              (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
              (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
              frame
              (frame-addrs-before-seq frame x seq)
              seq)))
    (mv-nth 1
            (ctx-app-list-seq
             (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
             frame
             (frame-addrs-before-seq frame x seq)
             seq))))
  :hints
  (("goal"
    :in-theory (e/d (collapse-seq frame-addrs-before-seq
                                  ctx-app-list-seq)
                    ((:definition no-duplicatesp-equal)
                     (:definition member-equal)
                     (:rewrite nthcdr-when->=-n-len-l)
                     (:definition remove-assoc-equal)
                     (:definition nthcdr)
                     (:definition len)))
    :induct (collapse-seq frame seq)
    :expand
    (:with
     frame-addrs-before-seq-of-collapse-this-1
     (frame-addrs-before-seq
      (collapse-this frame (car seq))
      (frame-val->src$inline (cdr (assoc-equal (car seq)
                                               (frame->frame frame))))
      (cdr seq))))))

(local
 (defthm
   valid-seqp-after-collapse-this-lemma-26
   (implies
    (and (not (member-equal x2
                            (frame-addrs-before-seq frame x seq)))
         (abs-separate (frame->frame frame))
         (frame-p (frame->frame frame))
         (consp (assoc-equal x
                             (frame->frame (collapse-seq frame seq))))
         (valid-seqp frame seq)
         (no-duplicatesp-equal (strip-cars (frame->frame frame)))
         (nat-listp seq))
    (iff
     (ctx-app-ok
      (frame-val->dir
       (cdr (assoc-equal x
                         (frame->frame (collapse-seq frame seq)))))
      x2 x2-path)
     (ctx-app-ok (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
                 x2 x2-path)))
   :hints (("goal" :in-theory (disable valid-seqp-after-collapse-this-lemma-25)
            :use valid-seqp-after-collapse-this-lemma-25))))

(local
 (defthm
   valid-seqp-after-collapse-this-lemma-27
   (implies
    (and
     (not (zp n))
     (equal
      (len
       (frame->frame (collapse-seq (collapse-this frame x)
                                   (take (+ -1 n)
                                         (seq-this (collapse-this frame x))))))
      (+ (- n) (len (frame->frame frame))))
     (abs-separate (frame->frame frame))
     (frame-p (frame->frame frame))
     (mv-nth 1 (collapse frame))
     (consp (assoc-equal x (frame->frame frame)))
     (abs-complete
      (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
     (no-duplicatesp-equal (strip-cars (frame->frame frame)))
     (<= n
         (len (seq-this (collapse-this frame x))))
     (< 0
        (nth (+ -1 n)
             (seq-this (collapse-this frame x))))
     (< 0
        (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
     (equal (frame-val->src
             (cdr (assoc-equal (nth (+ -1 n)
                                    (seq-this (collapse-this frame x)))
                               (frame->frame frame))))
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
    (ctx-app-ok
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
        (frame->frame
         (collapse-seq (collapse-this frame x)
                       (take (+ -1 n)
                             (seq-this (collapse-this frame x))))))))
     (nth (+ -1 n)
          (seq-this (collapse-this frame x)))
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path
       (cdr (assoc-equal (nth (+ -1 n)
                              (seq-this (collapse-this frame x)))
                         (frame->frame frame)))))))
   :hints
   (("goal"
     :in-theory (e/d (valid-seqp collapse-seq seq-this
                                 consp-of-set-difference$
                                 valid-seqp-after-collapse-this-lemma-6)
                     ((:rewrite valid-seqp-after-collapse-this-lemma-26)
                      collapse-seq-of-collapse-seq
                      take set-difference-equal
                      (:definition member-equal)
                      (:rewrite different-from-own-src-1)
                      (:definition assoc-equal)
                      (:definition no-duplicatesp-equal)
                      (:rewrite final-val-seq-of-collapse-this-lemma-2)
                      (:rewrite nthcdr-when->=-n-len-l)
                      (:rewrite m1-file-alist-p-of-final-val-seq-lemma-2)))
     :use
     (:instance
      (:rewrite valid-seqp-after-collapse-this-lemma-26)
      (x2-path
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr (assoc-equal (nth (+ -1 n)
                                    (seq-this (collapse-this frame x)))
                               (frame->frame frame))))
            (frame->frame frame)))))
        (frame-val->path
         (cdr (assoc-equal (nth (+ -1 n)
                                (seq-this (collapse-this frame x)))
                           (frame->frame frame))))))
      (x2 (nth (+ -1 n)
               (seq-this (collapse-this frame x))))
      (seq (take (+ -1 n)
                 (seq-this (collapse-this frame x))))
      (frame (collapse-this frame x))
      (x (frame-val->src
          (cdr (assoc-equal (nth (+ -1 n)
                                 (seq-this (collapse-this frame x)))
                            (frame->frame frame))))))))))

(local
 (defthm
   valid-seqp-after-collapse-this-lemma-28
   (implies
    (mv-nth 1 (collapse frame))
    (or
     (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            0)
     (and
      (consp
       (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                    (frame->frame frame)))
      (not (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  x)))))
   :hints (("goal" :in-theory (enable collapse)))
   :rule-classes
   ((:rewrite
     :corollary
     (implies (and (mv-nth 1 (collapse frame))
                   (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                   (consp (assoc-equal x (frame->frame frame)))
                   (not (zp x)))
              (equal (len (frame->frame (collapse-this frame x)))
                     (+ -1 (len (frame->frame frame)))))
     :hints
     (("goal"
       :cases
       ((equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               0))))))))

(local
 (defthm
   valid-seqp-after-collapse-this-lemma-29
   (implies
    (and
     (equal (frame-val->src
             (cdr (assoc-equal (nth (+ -1 n)
                                    (seq-this (collapse-this frame x)))
                               (frame->frame frame))))
            0)
     (not (zp n))
     (equal
      (len
       (frame->frame (collapse-seq (collapse-this frame x)
                                   (take (+ -1 n)
                                         (seq-this (collapse-this frame x))))))
      (+ (- n) (len (frame->frame frame))))
     (abs-separate (frame->frame frame))
     (frame-p (frame->frame frame))
     (dist-names (frame->root frame)
                 nil (frame->frame frame))
     (mv-nth 1 (collapse frame))
     (consp (assoc-equal x (frame->frame frame)))
     (abs-complete
      (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
     (no-duplicatesp-equal (strip-cars (frame->frame frame)))
     (<= n
         (len (seq-this (collapse-this frame x)))))
    (ctx-app-ok
     (frame->root (collapse-seq (collapse-this frame x)
                                (take (+ -1 n)
                                      (seq-this (collapse-this frame x)))))
     (nth (+ -1 n)
          (seq-this (collapse-this frame x)))
     (frame-val->path
      (cdr (assoc-equal (nth (+ -1 n)
                             (seq-this (collapse-this frame x)))
                        (frame->frame frame))))))
   :hints
   (("goal"
     :in-theory (e/d (valid-seqp collapse-seq seq-this
                                 consp-of-set-difference$
                                 valid-seqp-after-collapse-this-lemma-6)
                     (collapse-seq-of-collapse-seq
                      take set-difference-equal
                      valid-seqp-after-collapse-this-lemma-25
                      (:definition member-equal)
                      (:rewrite different-from-own-src-1)
                      (:definition assoc-equal)
                      (:definition no-duplicatesp-equal)
                      (:rewrite final-val-seq-of-collapse-this-lemma-2)
                      (:rewrite nthcdr-when->=-n-len-l)
                      (:rewrite m1-file-alist-p-of-final-val-seq-lemma-2)))
     :expand
     (:with
      valid-seqp-after-collapse-this-lemma-6
      (ctx-app-ok
       (frame->root (collapse-seq (collapse-this frame x)
                                  (take (binary-+ '-1 n)
                                        (seq-this (collapse-this frame x)))))
       (nth (binary-+ '-1 n)
            (seq-this (collapse-this frame x)))
       (frame-val->path$inline
        (cdr (assoc-equal (nth (binary-+ '-1 n)
                               (seq-this (collapse-this frame x)))
                          (frame->frame frame))))))
     :do-not-induct t))))

(local
 (defthm
   valid-seqp-after-collapse-this-lemma-30
   (implies
    (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
         (< (nfix n) (len (seq-this frame))))
    (and
     (equal
      (abs-addrs
       (frame-val->dir
        (cdr
         (assoc-equal
          (nth n (seq-this frame))
          (frame->frame (collapse-seq frame (take n (seq-this frame))))))))
      nil)
     (abs-complete
      (frame-val->dir
       (cdr
        (assoc-equal
         (nth n (seq-this frame))
         (frame->frame (collapse-seq frame (take n (seq-this frame))))))))))
   :hints
   (("goal"
     :do-not-induct t
     :in-theory (e/d nil
                     ((:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-9)))
     :use
     (nth-of-seq-this
      (:instance
       (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-9)
       (frame
        (frame->frame (collapse-seq frame (take n (seq-this frame)))))))))))

(local
 (defthm
   valid-seqp-after-collapse-this-lemma-31
   (implies
    (equal (nth (+ -1 n)
                (seq-this (collapse-this frame x)))
           (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
    (not
     (member-equal
      (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
      (frame-addrs-before-seq (collapse-this frame x)
                              0
                              (take (binary-+ -1 n)
                                    (seq-this (collapse-this frame x)))))))
   :hints
   (("goal"
     :do-not-induct t
     :in-theory (disable (:rewrite member-equal-nth-take-when-no-duplicatesp))
     :use (:instance (:rewrite member-equal-nth-take-when-no-duplicatesp)
                     (x (nth (+ -1 n) (seq-this (collapse-this frame x))))
                     (l (seq-this (collapse-this frame x)))
                     (n (+ -1 n)))))))

(local
 (defthm
   valid-seqp-after-collapse-this-lemma-32
   (implies
    (and
     (not (zp n))
     (equal
      (len
       (frame->frame (collapse-seq (collapse-this frame x)
                                   (take (+ -1 n)
                                         (seq-this (collapse-this frame x))))))
      (+ (- n) (len (frame->frame frame))))
     (abs-separate (frame->frame frame))
     (frame-p (frame->frame frame))
     (dist-names (frame->root frame)
                 nil (frame->frame frame))
     (mv-nth 1 (collapse frame))
     (consp (assoc-equal x (frame->frame frame)))
     (abs-complete
      (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
     (no-duplicatesp-equal (strip-cars (frame->frame frame)))
     (<= n
         (len (seq-this (collapse-this frame x)))))
    (equal
     (len
      (frame->frame
       (collapse-seq (collapse-seq (collapse-this frame x)
                                   (take (+ -1 n)
                                         (seq-this (collapse-this frame x))))
                     (list (nth (+ -1 n)
                                (seq-this (collapse-this frame x)))))))
     (- (len (frame->frame frame)) (+ n 1))))
   :hints
   (("goal"
     :in-theory (e/d (valid-seqp collapse-seq seq-this
                                 consp-of-set-difference$
                                 valid-seqp-after-collapse-this-lemma-6)
                     (collapse-seq-of-collapse-seq
                      take set-difference-equal
                      (:definition member-equal)
                      (:rewrite different-from-own-src-1)
                      (:definition assoc-equal)
                      (:definition no-duplicatesp-equal)
                      (:rewrite final-val-seq-of-collapse-this-lemma-2)
                      (:rewrite nthcdr-when->=-n-len-l)
                      (:rewrite m1-file-alist-p-of-final-val-seq-lemma-2)
                      (:rewrite no-duplicatesp-of-seq-this-lemma-1 . 2)
                      (:definition remove-equal)
                      (:rewrite remove-when-absent)
                      (:rewrite subsetp-of-remove1)
                      (:rewrite valid-seqp-after-collapse-this-lemma-25)))
     :expand
     (collapse-seq (collapse-seq (collapse-this frame x)
                                 (take (+ -1 n)
                                       (seq-this (collapse-this frame x))))
                   (list (nth (+ -1 n)
                              (seq-this (collapse-this frame x)))))
     :do-not-induct t))))

(local
 (encapsulate
   ()

   (local (include-book "std/basic/inductions" :dir :system))

   (local
    (defthm
      lemma
      (implies (and (valid-seqp frame
                                (cons x
                                      (take (+ -1 n)
                                            (seq-this (collapse-this frame x)))))
                    (abs-separate (frame->frame frame))
                    (frame-p (frame->frame frame))
                    (dist-names (frame->root frame)
                                nil (frame->frame frame))
                    (mv-nth 1 (collapse frame))
                    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                    (<= n
                        (len (seq-this (collapse-this frame x)))))
               (valid-seqp frame
                           (cons x
                                 (take n (seq-this (collapse-this frame x))))))
      :hints
      (("goal"
        :in-theory (e/d (valid-seqp collapse-seq seq-this)
                        ((:rewrite binary-append-take-nthcdr)
                         (:rewrite collapse-seq-of-collapse-seq)
                         (:rewrite collapse-seq-of-collapse-seq)
                         (:rewrite
                          assoc-of-frame->frame-of-collapse-this)
                         (:rewrite
                          abs-separate-of-frame->frame-of-collapse-this-lemma-8
                          . 2)
                         (:rewrite
                          final-val-seq-of-collapse-this-lemma-2)
                         (:definition assoc-equal)
                         (:rewrite
                          partial-collapse-correctness-lemma-2)
                         (:rewrite
                          different-from-own-src-1)
                         (:rewrite
                          m1-file-alist-p-of-final-val-seq-lemma-2)))
        :use
        ((:instance (:rewrite take-of-nthcdr)
                    (l (seq-this (collapse-this frame x)))
                    (n2 (+ -1 n))
                    (n1 1))
         (:instance (:rewrite collapse-seq-of-collapse-seq)
                    (seq2 (nthcdr (+ -1 n)
                                  (take n (seq-this (collapse-this frame x)))))
                    (seq1 (take (+ -1 n)
                                (take n (seq-this (collapse-this frame x)))))
                    (frame (collapse-this frame x))))))))

   (defthmd
     valid-seqp-after-collapse-this-lemma-33
     (implies
      (and
       (abs-separate (frame->frame frame))
       (frame-p (frame->frame frame))
       (dist-names (frame->root frame)
                   nil (frame->frame frame))
       (mv-nth 1 (collapse frame))
       (consp (assoc-equal x (frame->frame frame)))
       (abs-complete
        (frame-val->dir
         (cdr (assoc-equal x (frame->frame frame)))))
       (no-duplicatesp-equal (strip-cars (frame->frame frame)))
       (<= n
           (len (seq-this (collapse-this frame x)))))
      (valid-seqp
       frame
       (cons x
             (take n (seq-this (collapse-this frame x))))))
     :hints
     (("goal"
       :induct (dec-induct n)
       :in-theory (e/d (collapse-seq seq-this)
                       ((:rewrite binary-append-take-nthcdr)
                        (:rewrite collapse-seq-of-collapse-seq)))
       :expand (valid-seqp frame (list x)))))))

(local
 (defthm
   valid-seqp-after-collapse-this
   (implies
    (and (abs-separate (frame->frame frame))
         (frame-p (frame->frame frame))
         (dist-names (frame->root frame)
                     nil (frame->frame frame))
         (no-duplicatesp-equal (strip-cars (frame->frame frame)))
         (mv-nth 1 (collapse frame))
         (consp (assoc-equal x (frame->frame frame)))
         (abs-complete
          (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))))
    (valid-seqp frame
                (cons x (seq-this (collapse-this frame x)))))
   :hints
   (("goal" :do-not-induct t
     :use (:instance valid-seqp-after-collapse-this-lemma-33
                     (n (len (seq-this (collapse-this frame x)))))))))

(defund absfat-equiv-upto-n
  (frame seq n)
  (or
   (zp n)
   (and
    (absfat-equiv
     (final-val-seq (nth (- n 1) seq) frame seq)
     (final-val (nth (- n 1) seq) frame))
    (absfat-equiv-upto-n frame seq (- n 1)))))

(defthm absfat-equiv-upto-n-correctness-1
  (implies (and (absfat-equiv-upto-n frame seq n)
                (member-equal x seq)
                (< (position-equal x seq) (nfix n)))
           (absfat-equiv (final-val-seq x frame seq)
                         (final-val x frame)))
  :hints (("goal" :in-theory (enable absfat-equiv-upto-n))))

(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-1
  (implies
   (and
    (not (zp n))
    (absfat-equiv
     (mv-nth 0
             (ctx-app-list-seq
              (frame-val->dir (cdr (assoc-equal (nth m seq)
                                                (frame->frame frame))))
              (frame-val->path (cdr (assoc-equal (nth m seq)
                                                 (frame->frame frame))))
              frame
              (frame-addrs-before-seq frame (nth m seq)
                                      (take (+ -1 n) seq))
              (take m seq)))
     (mv-nth
      0
      (ctx-app-list (frame-val->dir (cdr (assoc-equal (nth m seq)
                                                      (frame->frame frame))))
                    (frame-val->path (cdr (assoc-equal (nth m seq)
                                                       (frame->frame frame))))
                    frame
                    (frame-addrs-before-seq frame (nth m seq)
                                            (take (+ -1 n) seq)))))
    (absfat-equiv-upto-n frame seq m)
    (valid-seqp frame seq)
    (< m (len seq))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (nat-listp seq)
    (integerp m)
    (<= n m))
   (absfat-equiv
    (mv-nth
     0
     (ctx-app-list-seq
      (mv-nth 0
              (ctx-app-list-seq
               (frame-val->dir (cdr (assoc-equal (nth m seq)
                                                 (frame->frame frame))))
               (frame-val->path (cdr (assoc-equal (nth m seq)
                                                  (frame->frame frame))))
               frame
               (frame-addrs-before-seq frame (nth m seq)
                                       (take (+ -1 n) seq))
               (take m seq)))
      (frame-val->path (cdr (assoc-equal (nth m seq)
                                         (frame->frame frame))))
      frame
      (frame-addrs-before-seq frame (nth m seq)
                              (nthcdr (+ -1 n) (take n seq)))
      (take m seq)))
    (mv-nth
     0
     (ctx-app-list
      (mv-nth 0
              (ctx-app-list
               (frame-val->dir (cdr (assoc-equal (nth m seq)
                                                 (frame->frame frame))))
               (frame-val->path (cdr (assoc-equal (nth m seq)
                                                  (frame->frame frame))))
               frame
               (frame-addrs-before-seq frame (nth m seq)
                                       (take (+ -1 n) seq))))
      (frame-val->path (cdr (assoc-equal (nth m seq)
                                         (frame->frame frame))))
      frame
      (frame-addrs-before-seq frame (nth m seq)
                              (nthcdr (+ -1 n) (take n seq)))))))
  :hints
  (("goal"
    :in-theory (e/d (frame-addrs-before-seq ctx-app-list ctx-app-list-seq member-of-take)
                    ((:definition member-equal)
                     (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
                     (:rewrite binary-append-take-nthcdr)))
    :use ((:instance (:rewrite binary-append-take-nthcdr)
                     (l (take n seq))
                     (i (+ -1 n)))
          (:instance (:rewrite take-of-nthcdr)
                     (l seq)
                     (n2 (+ -1 n))
                     (n1 1))))))

(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-2
  (implies
   (and (frame-p (frame->frame frame))
        (subsetp-equal l (strip-cars (frame->frame frame)))
        (not (member-equal (1st-complete (frame->frame frame))
                           l))
        (mv-nth 1 (collapse frame)))
   (equal (ctx-app-list fs path-len
                        (collapse-this frame
                                       (1st-complete (frame->frame frame)))
                        l)
          (ctx-app-list fs path-len frame l)))
  :hints (("goal" :in-theory (enable ctx-app-list subsetp-equal))))

(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-3
  (implies (and (mv-nth 1 (collapse frame))
                (<= (nfix n) (len (frame->frame frame)))
                (no-duplicatesp-equal (strip-cars (frame->frame frame))))
           (subsetp-equal (frame-addrs-before frame x n)
                          (strip-cars (frame->frame frame))))
  :hints
  (("goal" :in-theory (e/d (frame-addrs-before collapse collapse-iter)
                           ((:definition no-duplicatesp-equal)
                            (:definition assoc-equal)
                            (:definition member-equal)
                            (:rewrite nthcdr-when->=-n-len-l)
                            (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
                            (:rewrite partial-collapse-correctness-lemma-2)))
    :induct (frame-addrs-before frame x n)
    :expand (collapse-iter frame 1)))
  :rule-classes ((:rewrite
                  :corollary
                  (implies (and (mv-nth 1 (collapse frame))
                                (<= (nfix n) (len (frame->frame frame)))
                                (no-duplicatesp-equal (strip-cars (frame->frame
                                                                   frame)))
                                (subsetp-equal (strip-cars (frame->frame frame)) y))
                           (subsetp-equal (frame-addrs-before frame x n) y)))
                 (:rewrite
                  :corollary
                  (implies (and (mv-nth 1 (collapse frame))
                                (<= (nfix n) (len (frame->frame frame)))
                                (no-duplicatesp-equal (strip-cars (frame->frame
                                                                   frame)))
                                (not (member-equal y
                                                   (strip-cars (frame->frame
                                                                frame)))))
                           (not
                            (member-equal
                             y
                             (frame-addrs-before frame x n)))))))

(defthmd
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-4
  (implies
   (and (abs-separate (frame->frame frame))
        (frame-p (frame->frame frame))
        (consp (assoc-equal x
                            (frame->frame (collapse-iter frame n))))
        (mv-nth 1 (collapse frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (and
    (equal
     (frame-val->dir
      (cdr (assoc-equal x
                        (frame->frame (collapse-iter frame n)))))
     (mv-nth 0
             (ctx-app-list
              (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
              (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
              frame (frame-addrs-before frame x n))))
    (mv-nth 1
            (ctx-app-list
             (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
             frame (frame-addrs-before frame x n)))))
  :hints
  (("goal" :induct (collapse-iter frame n)
    :do-not-induct t
    :in-theory
    (e/d (collapse-iter frame-addrs-before
                        ctx-app-list collapse)
         ((:definition no-duplicatesp-equal)
          (:definition member-equal)
          (:rewrite nthcdr-when->=-n-len-l)
          (:definition strip-cars)
          (:definition remove-assoc-equal)
          (:definition nthcdr)
          (:rewrite 1st-complete-of-remove-assoc-2)
          (:rewrite collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-2)
          (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8
                    . 1)
          (:type-prescription abs-addrs-of-remove-assoc-lemma-1)
          (:rewrite 1st-complete-of-put-assoc-lemma-1)
          (:definition len)
          (:rewrite abs-file-alist-p-correctness-1))))))

(defthmd
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-5
  (implies (and (valid-seqp frame seq)
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (member-equal x seq))
           (consp (assoc-equal x (frame->frame frame))))
  :hints (("goal" :in-theory (enable valid-seqp collapse-seq))))

(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-6
  (implies (and (valid-seqp frame seq)
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (< (nfix n) (len seq)))
           (consp (assoc-equal (nth n seq)
                               (frame->frame frame))))
  :hints (("goal"
           :use (:instance 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-5
                           (x (nth n seq))))))

;; Ton of free variables here - at any rate, frame is free.
(local
 (defthm
   1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-7
   (implies
    (and
     (valid-seqp frame seq)
     (no-duplicatesp-equal (strip-cars (frame->frame frame)))
     (member-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                   seq)
     (member-equal
      x
      (abs-addrs
       (frame-val->dir
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))))
     (abs-separate (frame->frame frame))
     (frame-p (frame->frame frame)))
    (member-equal x seq))
   :hints (("goal" :induct (collapse-seq frame seq)
            :in-theory (enable valid-seqp collapse-seq)))))

(defthmd
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-8
  (implies
   (and (mv-nth 1 (collapse frame))
        (not (zp (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
        (abs-separate (frame->frame frame))
        (frame-p (frame->frame frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (member-equal
    x
    (abs-addrs
     (frame-val->dir
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame)))))))
  :hints
  (("goal" :in-theory (e/d (collapse abs-addrs-of-ctx-app-lemma-2)
                           ((:rewrite remove-assoc-of-put-assoc)
                            (:rewrite remove-assoc-of-remove-assoc)
                            (:rewrite abs-file-alist-p-when-m1-file-alist-p)))
    :induct (collapse frame))))

(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-14
  (implies
   (< (nfix m)
      (len (frame-addrs-before frame x n)))
   (equal
    (frame-val->src
     (cdr (assoc-equal (nth m (frame-addrs-before frame x n))
                       (frame->frame frame))))
    x))
  :hints
  (("goal"
    :in-theory
    (disable frame-val->src-of-cdr-of-assoc-when-member-of-frame-addrs-before)
    :use
    (:instance frame-val->src-of-cdr-of-assoc-when-member-of-frame-addrs-before
               (y (nth m (frame-addrs-before frame x n)))))))

(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-15
  (implies
   (and
    (member-equal x seq)
    (nat-listp seq)
    (not (zp n))
    (abs-separate (frame->frame frame))
    (frame-p (frame->frame frame))
    (consp
     (assoc-equal
      x
      (frame->frame (collapse-seq frame
                                  (take (position-equal x seq) seq)))))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (mv-nth 1 (collapse frame))
    (<= n
        (len (frame-addrs-before frame x (collapse-1st-index frame x)))))
   (member-equal
    (nth (binary-+ -1 n)
         (frame-addrs-before frame x (collapse-1st-index frame x)))
    (abs-addrs
     (frame-val->dir$inline (cdr (assoc-equal x (frame->frame frame)))))))
  :hints
  (("goal"
    :use
    (:instance
     1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-8
     (x (nth (binary-+ -1 n)
             (frame-addrs-before frame
                                 x (collapse-1st-index frame x))))))))

(defthmd
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-9
  (implies
   (and
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (valid-seqp frame seq)
    (member-equal x seq)
    (not (zp (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))))
   (not
    (abs-complete
     (frame-val->dir
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame)))))))
  :hints (("goal" :in-theory (enable valid-seqp collapse-seq))))

(encapsulate
  ()

  (local
   (defthm
     lemma-1
     (implies
      (and
       (equal (frame-val->src (cdr (assoc-equal (car seq)
                                                (frame->frame frame))))
              0)
       (consp (assoc-equal (car seq)
                           (frame->frame frame)))
       (abs-complete (frame-val->dir (cdr (assoc-equal (car seq)
                                                       (frame->frame frame)))))
       (ctx-app-ok (frame->root frame)
                   (car seq)
                   (frame-val->path (cdr (assoc-equal (car seq)
                                                      (frame->frame frame)))))
       (equal (len (frame->frame (collapse-seq (collapse-this frame (car seq))
                                               (cdr seq))))
              (+ -1 (- (len (cdr seq)))
                 (len (frame->frame frame))))
       (no-duplicatesp-equal (strip-cars (frame->frame frame)))
       (member-equal x (cdr seq)))
      (not
       (equal (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
              (car seq))))
     :hints
     (("goal" :in-theory (e/d (valid-seqp collapse-seq))
       :use 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-9))))

  (local
   (defthm
     lemma-2
     (implies
      (and
       (consp seq)
       (abs-complete (frame-val->dir (cdr (assoc-equal (car seq)
                                                       (frame->frame frame)))))
       (prefixp
        (frame-val->path
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                         (frame->frame frame))))
                       (frame->frame frame))))
        (frame-val->path (cdr (assoc-equal (car seq)
                                           (frame->frame frame)))))
       (ctx-app-ok
        (frame-val->dir
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                         (frame->frame frame))))
                       (frame->frame frame))))
        (car seq)
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (car seq)
                                                   (frame->frame frame))))
                 (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal (car seq)
                                            (frame->frame frame))))))
       (equal (len (frame->frame (collapse-seq (collapse-this frame (car seq))
                                               (cdr seq))))
              (+ -1 (- (len (cdr seq)))
                 (len (frame->frame frame))))
       (no-duplicatesp-equal (strip-cars (frame->frame frame)))
       (member-equal x (cdr seq)))
      (not
       (equal (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
              (car seq))))
     :hints
     (("goal" :in-theory (e/d (valid-seqp collapse-seq))
       :use (:rewrite 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-9)))))

  (defthmd
    1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-10
    (implies
     (and
      (nat-listp seq)
      (valid-seqp frame seq)
      (no-duplicatesp-equal (strip-cars (frame->frame frame)))
      (member-equal x seq)
      (not (zp (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
      (member-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                    seq))
     (< (position-equal x seq)
        (position-equal
         (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
         seq)))
    :rule-classes :linear
    :hints (("goal" :in-theory (enable valid-seqp collapse-seq)
             :induct (collapse-seq frame seq)
             :expand (position-equal (car seq) seq)))))

(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-16
  (implies
   (and
    (member-equal x seq)
    (nat-listp seq)
    (not (zp n))
    (abs-separate (frame->frame frame))
    (frame-p (frame->frame frame))
    (consp
     (assoc-equal
      x
      (frame->frame (collapse-seq frame
                                  (take (position-equal x seq) seq)))))
    (valid-seqp frame seq)
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (mv-nth 1 (collapse frame))
    (<= n
        (len (frame-addrs-before frame x (collapse-1st-index frame x)))))
   (< (position-equal
       (nth (+ -1 n)
            (frame-addrs-before frame x (collapse-1st-index frame x)))
       seq)
      (position-equal x seq)))
  :hints
  (("goal"
    :do-not-induct t
    :use (:instance
          (:linear 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-10)
          (seq seq)
          (frame frame)
          (x (nth (+ -1 n)
                  (frame-addrs-before frame
                                      x (collapse-1st-index frame x)))))))
  :rule-classes :linear)

(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-11
  (implies
   (and
    (member-equal
     (nth (+ -1 n)
          (frame-addrs-before frame x (collapse-1st-index frame x)))
     (frame-addrs-before frame x (collapse-1st-index frame x)))
    (consp
     (assoc-equal
      x
      (frame->frame (collapse-seq frame
                                  (take (position-equal x seq) seq)))))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (mv-nth 1 (collapse frame)))
   (member-equal
    (nth (+ -1 n)
         (frame-addrs-before frame x (collapse-1st-index frame x)))
    (strip-cars (frame->frame frame))))
  :instructions
  (:promote
   (:rewrite (:rewrite subsetp-member . 2)
             ((x (frame-addrs-before frame x (collapse-1st-index frame x)))))
   (:claim (and (<= (nfix (collapse-1st-index frame x))
                    (len (frame->frame frame)))
                (subsetp-equal (strip-cars (frame->frame frame))
                               (strip-cars (frame->frame frame))))
           :hints :none)
   (:rewrite 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-3)
   :bash (:dive 1 2)
   (:apply-linear collapse-1st-index-correctness-1)
   :top
   :bash :bash))

(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-12
  (implies
   (and
    (not (zp n))
    (consp
     (assoc-equal
      x
      (frame->frame (collapse-seq frame
                                  (take (position-equal x seq) seq)))))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (mv-nth 1 (collapse frame))
    (<= n
        (len (frame-addrs-before frame x (collapse-1st-index frame x)))))
   (consp (assoc-equal
           (nth (+ -1 n)
                (frame-addrs-before frame x (collapse-1st-index frame x)))
           (frame->frame frame))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable (:rewrite member-of-strip-cars)
                        member-of-a-nat-list
                        (:rewrite member-equal-nth))
    :use
    ((:instance
      (:rewrite member-of-strip-cars)
      (alist (frame->frame frame))
      (x (nth (+ -1 n)
              (frame-addrs-before frame x (collapse-1st-index frame x)))))
     (:instance
      member-of-a-nat-list
      (x (nth (+ -1 n)
              (frame-addrs-before frame x (collapse-1st-index frame x))))
      (lst (frame-addrs-before frame x (collapse-1st-index frame x))))
     (:instance (:rewrite member-equal-nth)
                (l (frame-addrs-before frame x (collapse-1st-index frame x)))
                (n (+ -1 n)))))))

(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-13
  (implies
   (consp
    (assoc-equal
     (frame-val->src (cdr (assoc-equal (nth (+ -1 n) seq)
                                       (frame->frame frame))))
     (frame->frame
      (collapse-seq
       frame
       (take (position-equal
              (frame-val->src (cdr (assoc-equal (nth (+ -1 n) seq)
                                                (frame->frame frame))))
              seq)
             seq)))))
   (consp (assoc-equal (nth (+ -1 n) seq)
                       (frame->frame frame)))))

(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-17
  (implies
   (and
    (frame-p (frame->frame frame))
    (consp
     (assoc-equal
      (frame-val->src (cdr (assoc-equal (nth (+ -1 n) seq)
                                        (frame->frame frame))))
      (frame->frame
       (collapse-seq
        frame
        (take (position-equal
               (frame-val->src (cdr (assoc-equal (nth (+ -1 n) seq)
                                                 (frame->frame frame))))
               seq)
              seq)))))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (mv-nth 1 (collapse frame)))
   (member-equal
    (nth (+ -1 n) seq)
    (frame-addrs-before
     frame
     (frame-val->src (cdr (assoc-equal (nth (+ -1 n) seq)
                                       (frame->frame frame))))
     (collapse-1st-index
      frame
      (frame-val->src (cdr (assoc-equal (nth (+ -1 n) seq)
                                        (frame->frame frame))))))))
  :hints
  (("goal"
    :do-not-induct t
    :cases
    ((equal
      (if
          (<
           (binary-+
            (len (frame->frame frame))
            (unary--
             (collapse-1st-index
              frame
              (frame-val->src$inline (cdr (assoc-equal (nth (binary-+ '-1 n) seq)
                                                       (frame->frame frame)))))))
           '0)
          '0
        (binary-+
         (len (frame->frame frame))
         (unary--
          (collapse-1st-index
           frame
           (frame-val->src$inline (cdr (assoc-equal (nth (binary-+ '-1 n) seq)
                                                    (frame->frame frame))))))))
      (binary-+
       (len (frame->frame frame))
       (unary-- (collapse-1st-index
                 frame
                 (frame-val->src$inline
                  (cdr (assoc-equal (nth (binary-+ '-1 n) seq)
                                    (frame->frame frame))))))))))))

(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-18
  (implies
   (and
    (not (zp n))
    (subsetp-equal (frame-addrs-before-seq frame x (take (+ -1 n) seq))
                   (frame-addrs-before frame x (collapse-1st-index frame x)))
    (frame-p (frame->frame frame))
    (consp
     (assoc-equal
      x
      (frame->frame (collapse-seq frame
                                  (take (position-equal x seq) seq)))))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (mv-nth 1 (collapse frame)))
   (subsetp-equal (frame-addrs-before-seq frame x (take n seq))
                  (frame-addrs-before frame x (collapse-1st-index frame x))))
  :hints
  (("goal"
    :in-theory (e/d (frame-addrs-before-seq)
                    ((:rewrite binary-append-take-nthcdr)
                     (:rewrite frame-addrs-before-seq-of-append)))
    :use
    ((:instance (:rewrite binary-append-take-nthcdr)
                (l (take n seq))
                (i (+ -1 n)))
     (:instance (:rewrite frame-addrs-before-seq-of-append)
                (l2 (nthcdr (+ -1 n) (take n seq)))
                (l1 (take (+ -1 n) seq))
                (x x)
                (frame frame))
     (:instance
      (:rewrite subsetp-append1)
      (a (nthcdr (+ -1 n) (take n seq)))
      (b (frame-addrs-before-seq
          frame
          (frame-val->src (cdr (assoc-equal (nth (+ -1 n) seq)
                                            (frame->frame frame))))
          (take (+ -1 n) seq)))
      (c
       (frame-addrs-before
        frame
        (frame-val->src (cdr (assoc-equal (nth (+ -1 n) seq)
                                          (frame->frame frame))))
        (collapse-1st-index
         frame
         (frame-val->src (cdr (assoc-equal (nth (+ -1 n) seq)
                                           (frame->frame frame))))))))
     (:instance take-of-nthcdr (l seq)
                (n2 (- n 1))
                (n1 1))))))

(encapsulate
  ()

  (local (include-book "std/basic/inductions" :dir :system))

  (local
   (defthm
     lemma
     (implies
      (and
       (member-equal x seq)
       (nat-listp seq)
       (not (zp n))
       (subsetp-equal
        (take (+ -1 n)
              (frame-addrs-before frame x (collapse-1st-index frame x)))
        (frame-addrs-before-seq frame
                                x (take (position-equal x seq) seq)))
       (abs-separate (frame->frame frame))
       (frame-p (frame->frame frame))
       (consp
        (assoc-equal
         x
         (frame->frame (collapse-seq frame
                                     (take (position-equal x seq) seq)))))
       (valid-seqp frame seq)
       (no-duplicatesp-equal (strip-cars (frame->frame frame)))
       (mv-nth 1 (collapse frame))
       (<= n
           (len (frame-addrs-before frame x (collapse-1st-index frame x)))))
      (subsetp-equal
       (take n
             (frame-addrs-before frame x (collapse-1st-index frame x)))
       (frame-addrs-before-seq frame
                               x (take (position-equal x seq) seq))))
     :hints
     (("goal"
       :do-not-induct t
       :in-theory (e/d (member-of-take)
                       ((:rewrite binary-append-take-nthcdr)
                        (:rewrite subsetp-append1)
                        valid-seqp-after-collapse-this-lemma-8))
       :use
       ((:instance
         (:rewrite binary-append-take-nthcdr)
         (l (take n
                  (frame-addrs-before frame x (collapse-1st-index frame x))))
         (i (+ -1 n)))
        (:instance
         (:rewrite subsetp-append1)
         (a (take (+ -1 n)
                  (frame-addrs-before frame x (collapse-1st-index frame x))))
         (b
          (nthcdr
           (+ -1 n)
           (take n
                 (frame-addrs-before frame x (collapse-1st-index frame x)))))
         (c (frame-addrs-before-seq frame
                                    x (take (position-equal x seq) seq))))
        (:instance (:rewrite take-of-nthcdr)
                   (l (frame-addrs-before frame x (collapse-1st-index frame x)))
                   (n2 (+ -1 n))
                   (n1 1)))))))

  (defthm
    1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-19
    (implies
     (and
      (frame-p (frame->frame frame))
      (consp
       (assoc-equal
        x
        (frame->frame (collapse-seq frame
                                    (take (position-equal x seq) seq)))))
      (no-duplicatesp-equal (strip-cars (frame->frame frame)))
      (mv-nth 1 (collapse frame)))
     (subsetp-equal (frame-addrs-before-seq frame x (take n seq))
                    (frame-addrs-before frame x (collapse-1st-index frame x))))
    :hints
    (("goal" :induct (dec-induct n))))

  (defthm
    1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-20
    (implies
     (and
      (member-equal x seq)
      (nat-listp seq)
      (abs-separate (frame->frame frame))
      (frame-p (frame->frame frame))
      (consp
       (assoc-equal
        x
        (frame->frame (collapse-seq frame
                                    (take (position-equal x seq) seq)))))
      (valid-seqp frame seq)
      (no-duplicatesp-equal (strip-cars (frame->frame frame)))
      (mv-nth 1 (collapse frame))
      (<= n
          (len (frame-addrs-before frame x (collapse-1st-index frame x)))))
     (subsetp-equal
      (take n
            (frame-addrs-before frame x (collapse-1st-index frame x)))
      (frame-addrs-before-seq frame
                              x (take (position-equal x seq) seq))))
    :hints (("goal" :in-theory (enable final-val-seq member-of-take)
             :induct (dec-induct n)))))

(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-21
  (implies
   (and
    (member-equal x seq)
    (nat-listp seq)
    (abs-separate (frame->frame frame))
    (frame-p (frame->frame frame))
    (consp
     (assoc-equal
      x
      (frame->frame (collapse-seq frame
                                  (take (position-equal x seq) seq)))))
    (valid-seqp frame seq)
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (mv-nth 1 (collapse frame)))
   (set-equiv (frame-addrs-before-seq frame
                                      x (take (position-equal x seq) seq))
              (frame-addrs-before frame x (collapse-1st-index frame x))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (set-equiv member-of-take)
                    (1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-20))
    :use
    ((:instance 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-20
                (n (position-equal x seq)))
     (:instance
      1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-20
      (n (len (frame-addrs-before frame
                                  x (collapse-1st-index frame x)))))))))

(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-22
  (implies
   (and (< (nfix m) (len seq))
        (nat-listp seq)
        (abs-separate (frame->frame frame))
        (frame-p (frame->frame frame))
        (valid-seqp frame seq)
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (mv-nth 1 (collapse frame)))
   (set-equiv (frame-addrs-before-seq frame (nth m seq)
                                      (take m seq))
              (frame-addrs-before frame (nth m seq)
                                  (collapse-1st-index frame (nth m seq)))))
  :hints (("goal" :do-not-induct t
           :in-theory (disable 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-21
                               (:definition nfix)
                               (:definition nth))
           :use (:instance 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-21
                           (x (nth m seq))))))

(defthmd
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-23
  (implies
   (and
    (abs-separate (frame->frame frame))
    (frame-p (frame->frame frame))
    (consp
     (assoc-equal
      x
      (frame->frame (collapse-seq frame
                                  (take (position-equal x seq) seq)))))
    (valid-seqp frame (take (position-equal x seq) seq))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (nat-listp (take (position-equal x seq) seq)))
   (equal
    (final-val-seq x frame seq)
    (mv-nth 0
            (ctx-app-list-seq
             (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
             frame
             (frame-addrs-before-seq frame
                                     x (take (position-equal x seq) seq))
             (take (position-equal x seq) seq)))))
  :hints (("goal" :in-theory (enable final-val-seq))))

(defthmd
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-24
  (implies
   (and
    (abs-separate (frame->frame frame))
    (frame-p (frame->frame frame))
    (consp
     (assoc-equal
      x
      (frame->frame (collapse-iter frame (collapse-1st-index frame x)))))
    (mv-nth 1 (collapse frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (equal
    (final-val x frame)
    (mv-nth 0
            (ctx-app-list
             (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
             frame
             (frame-addrs-before frame
                                 x (collapse-1st-index frame x))))))
  :hints (("goal" :in-theory (e/d (final-val))
           :use (:instance 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-4
                           (n (collapse-1st-index frame x))))))

(encapsulate
  ()

  (local (include-book "std/basic/inductions" :dir :system))

  (local
   (defthm
     lemma
     (implies
      (and
       (not (zp n))
       (absfat-equiv
        (mv-nth 0
                (ctx-app-list-seq
                 (frame-val->dir (cdr (assoc-equal (nth m seq)
                                                   (frame->frame frame))))
                 (frame-val->path (cdr (assoc-equal (nth m seq)
                                                    (frame->frame frame))))
                 frame
                 (frame-addrs-before-seq frame (nth m seq)
                                         (take (+ -1 n) seq))
                 (take m seq)))
        (mv-nth
         0
         (ctx-app-list (frame-val->dir (cdr (assoc-equal (nth m seq)
                                                         (frame->frame frame))))
                       (frame-val->path (cdr (assoc-equal (nth m seq)
                                                          (frame->frame frame))))
                       frame
                       (frame-addrs-before-seq frame (nth m seq)
                                               (take (+ -1 n) seq)))))
       (absfat-equiv-upto-n frame seq m)
       (valid-seqp frame seq)
       (< m (len seq))
       (no-duplicatesp-equal (strip-cars (frame->frame frame)))
       (nat-listp seq)
       (integerp m)
       (<= n m))
      (absfat-equiv
       (mv-nth 0
               (ctx-app-list-seq
                (frame-val->dir (cdr (assoc-equal (nth m seq)
                                                  (frame->frame frame))))
                (frame-val->path (cdr (assoc-equal (nth m seq)
                                                   (frame->frame frame))))
                frame
                (frame-addrs-before-seq frame (nth m seq)
                                        (take n seq))
                (take m seq)))
       (mv-nth
        0
        (ctx-app-list (frame-val->dir (cdr (assoc-equal (nth m seq)
                                                        (frame->frame frame))))
                      (frame-val->path (cdr (assoc-equal (nth m seq)
                                                         (frame->frame frame))))
                      frame
                      (frame-addrs-before-seq frame (nth m seq)
                                              (take n seq))))))
     :instructions
     (:promote (:claim (equal (take n seq)
                              (append (take (+ -1 n) (take n seq))
                                      (nthcdr (+ -1 n) (take n seq))))
                       :hints :none)
               (:change-goal nil t)
               (:dive 2)
               (:rewrite binary-append-take-nthcdr)
               :top :s :bash (:dive 1 2 4 3)
               := :up
               (:rewrite frame-addrs-before-seq-of-append)
               :top (:dive 2 2 4 3)
               :=
               :up (:rewrite frame-addrs-before-seq-of-append)
               :top bash)))

  (defthm
    1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-25
    (implies
     (and (absfat-equiv-upto-n frame seq m)
          (valid-seqp frame seq)
          (< m (len seq))
          (no-duplicatesp-equal (strip-cars (frame->frame frame)))
          (nat-listp seq)
          (integerp m)
          (<= n m))
     (absfat-equiv
      (mv-nth 0
              (ctx-app-list-seq
               (frame-val->dir (cdr (assoc-equal (nth m seq)
                                                 (frame->frame frame))))
               (frame-val->path (cdr (assoc-equal (nth m seq)
                                                  (frame->frame frame))))
               frame
               (frame-addrs-before-seq frame (nth m seq)
                                       (take n seq))
               (take m seq)))
      (mv-nth
       0
       (ctx-app-list (frame-val->dir (cdr (assoc-equal (nth m seq)
                                                       (frame->frame frame))))
                     (frame-val->path (cdr (assoc-equal (nth m seq)
                                                        (frame->frame frame))))
                     frame
                     (frame-addrs-before-seq frame (nth m seq)
                                             (take n seq))))))
    :hints
    (("goal"
      :in-theory (e/d (frame-addrs-before-seq ctx-app-list ctx-app-list-seq)
                      ((:definition member-equal)
                       (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)))
      :induct (dec-induct n))))

  (defthm
    1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-26
    (implies
     (and (absfat-equiv-upto-n frame seq m)
          (mv-nth 1 (collapse frame))
          (abs-separate (frame->frame frame))
          (frame-p (frame->frame frame))
          (valid-seqp frame seq)
          (< m (len seq))
          (no-duplicatesp-equal (strip-cars (frame->frame frame)))
          (nat-listp seq)
          (natp m))
     (absfat-equiv
      (mv-nth 0
              (ctx-app-list-seq
               (frame-val->dir (cdr (assoc-equal (nth m seq)
                                                 (frame->frame frame))))
               (frame-val->path (cdr (assoc-equal (nth m seq)
                                                  (frame->frame frame))))
               frame
               (frame-addrs-before-seq frame (nth m seq)
                                       (take m seq))
               (take m seq)))
      (mv-nth
       0
       (ctx-app-list
        (frame-val->dir (cdr (assoc-equal (nth m seq)
                                          (frame->frame frame))))
        (frame-val->path (cdr (assoc-equal (nth m seq)
                                           (frame->frame frame))))
        frame
        (frame-addrs-before frame (nth m seq)
                            (collapse-1st-index frame (nth m seq)))))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (e/d (1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-4)
                      ())
      :use
      (:instance
       (:rewrite ctx-app-list-when-set-equiv)
       (l1 (frame-addrs-before frame (nth m seq)
                               (collapse-1st-index frame (nth m seq))))
       (l2 (frame-addrs-before-seq frame (nth m seq)
                                   (take m seq)))
       (relpath (frame-val->path (cdr (assoc-equal (nth m seq)
                                                   (frame->frame frame)))))
       (fs (frame-val->dir (cdr (assoc-equal (nth m seq)
                                             (frame->frame frame)))))))))

  (defthm
    1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-27
    (implies (and (abs-separate (frame->frame frame))
                  (frame-p (frame->frame frame))
                  (valid-seqp frame seq)
                  (<= (nfix n) (len seq))
                  (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                  (nat-listp seq)
                  (mv-nth '1 (collapse frame)))
             (absfat-equiv-upto-n frame seq n))
    :hints
    (("goal"
      :in-theory
      (e/d
       (absfat-equiv-upto-n
        (:rewrite
         1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-24)
        (:rewrite
         1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-23))
       (hifat-equiv-when-absfat-equiv))
      :induct (dec-induct n)
      :do-not-induct t))))

(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-28
  (implies (and (abs-separate (frame->frame frame))
                (frame-p (frame->frame frame))
                (valid-seqp frame seq)
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (nat-listp seq)
                (mv-nth '1 (collapse frame)))
           (absfat-equiv-upto-n frame seq (len seq))))

(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-29
  (implies (and (abs-separate (frame->frame frame))
                (frame-p (frame->frame frame))
                (valid-seqp frame seq)
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (nat-listp seq)
                (mv-nth '1 (collapse frame))
                (member-equal x seq))
           (absfat-equiv (final-val-seq x frame seq)
                         (final-val x frame)))
  :hints (("goal" :in-theory (disable 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-28
                                      absfat-equiv-upto-n-correctness-1)
           :use ((:instance absfat-equiv-upto-n-correctness-1
                            (n (len seq)))
                 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-28))))

(defthmd
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-30
  (implies
   (and
    (abs-separate (frame->frame frame))
    (frame-p (frame->frame frame))
    (mv-nth 1 (collapse frame))
    (absfat-equiv
     (mv-nth
      0
      (ctx-app-list-seq (frame->root frame)
                        nil frame
                        (frame-addrs-before-seq frame 0 (take (+ -1 n) seq))
                        seq))
     (mv-nth
      0
      (ctx-app-list (frame->root frame)
                    nil frame
                    (frame-addrs-before-seq frame 0 (take (+ -1 n) seq)))))
    (valid-seqp frame seq)
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (nat-listp seq)
    (<= n (len seq)))
   (absfat-equiv
    (mv-nth
     0
     (ctx-app-list-seq
      (mv-nth
       0
       (ctx-app-list-seq
        (frame->root frame)
        nil frame
        (frame-addrs-before-seq frame 0 (take (+ -1 n) (take n seq)))
        seq))
      nil frame
      (frame-addrs-before-seq frame 0 (nthcdr (+ -1 n) (take n seq)))
      seq))
    (mv-nth
     0
     (ctx-app-list
      (mv-nth
       0
       (ctx-app-list
        (frame->root frame)
        nil frame
        (frame-addrs-before-seq frame 0 (take (+ -1 n) (take n seq)))))
      nil frame
      (frame-addrs-before-seq frame
                              0 (nthcdr (+ -1 n) (take n seq)))))))
  :hints (("goal" :in-theory (enable frame-addrs-before-seq
                                     ctx-app-list-seq ctx-app-list)
           :use (:instance (:rewrite take-of-nthcdr)
                           (l seq)
                           (n2 (+ -1 n))
                           (n1 1)))))

(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-31
  (implies
   (mv-nth 1
           (ctx-app-list (frame->root frame)
                         nil frame
                         (frame-addrs-before-seq frame 0 (take n seq))))
   (mv-nth
    1
    (ctx-app-list (frame->root frame)
                  nil frame
                  (frame-addrs-before-seq frame 0 (take (+ -1 n) seq)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (frame-addrs-before-seq ctx-app-list-seq ctx-app-list)
                    ((:rewrite binary-append-take-nthcdr)
                     (:rewrite frame-addrs-before-seq-of-append)))
    :use ((:instance (:rewrite binary-append-take-nthcdr)
                     (l (take n seq))
                     (i (+ -1 n)))
          (:instance (:rewrite frame-addrs-before-seq-of-append)
                     (l2 (nthcdr (+ -1 n) (take n seq)))
                     (l1 (take (+ -1 n) (take n seq)))
                     (x 0)
                     (frame frame))))))

(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-32
  (implies
   (mv-nth 1
           (ctx-app-list-seq (frame->root frame)
                             nil frame
                             (frame-addrs-before-seq frame 0 (take n seq))
                             seq))
   (mv-nth
    1
    (ctx-app-list-seq (frame->root frame)
                      nil frame
                      (frame-addrs-before-seq frame 0 (take (+ -1 n) seq))
                      seq)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (frame-addrs-before-seq ctx-app-list-seq ctx-app-list)
                    ((:rewrite binary-append-take-nthcdr)
                     (:rewrite frame-addrs-before-seq-of-append)))
    :use ((:instance (:rewrite binary-append-take-nthcdr)
                     (l (take n seq))
                     (i (+ -1 n)))
          (:instance (:rewrite frame-addrs-before-seq-of-append)
                     (l2 (nthcdr (+ -1 n) (take n seq)))
                     (l1 (take (+ -1 n) (take n seq)))
                     (x 0)
                     (frame frame))))))

(encapsulate
  ()

  (local (include-book "std/basic/inductions" :dir :system))

  (local
   (defthm
     lemma-3
     (implies
      (and
       (absfat-equiv
        (mv-nth
         0
         (ctx-app-list-seq (frame->root frame)
                           nil frame
                           (frame-addrs-before-seq frame 0 (take (+ -1 n) seq))
                           seq))
        (mv-nth
         0
         (ctx-app-list (frame->root frame)
                       nil frame
                       (frame-addrs-before-seq frame 0 (take (+ -1 n) seq)))))
       (abs-separate (frame->frame frame))
       (frame-p (frame->frame frame))
       (mv-nth 1 (collapse frame))
       (valid-seqp frame seq)
       (no-duplicatesp-equal (strip-cars (frame->frame frame)))
       (nat-listp seq)
       (<= n (len seq)))
      (absfat-equiv
       (mv-nth 0
               (ctx-app-list-seq (frame->root frame)
                                 nil frame
                                 (frame-addrs-before-seq frame 0 (take n seq))
                                 seq))
       (mv-nth 0
               (ctx-app-list (frame->root frame)
                             nil frame
                             (frame-addrs-before-seq frame 0 (take n seq))))))
     :hints
     (("goal"
       :do-not-induct t
       :in-theory (e/d (frame-addrs-before-seq ctx-app-list-seq ctx-app-list)
                       ((:rewrite binary-append-take-nthcdr)
                        (:rewrite frame-addrs-before-seq-of-append)))
       :use ((:instance (:rewrite binary-append-take-nthcdr)
                        (l (take n seq))
                        (i (+ -1 n)))
             (:instance (:rewrite frame-addrs-before-seq-of-append)
                        (l2 (nthcdr (+ -1 n) (take n seq)))
                        (l1 (take (+ -1 n) (take n seq)))
                        (x 0)
                        (frame frame))
             1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-30)))))

  (defthm
    1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-33
    (implies
     (and (abs-separate (frame->frame frame))
          (frame-p (frame->frame frame))
          (mv-nth '1 (collapse frame))
          (valid-seqp frame seq)
          (no-duplicatesp-equal (strip-cars (frame->frame frame)))
          (nat-listp seq)
          (<= n (len seq)))
     (absfat-equiv
      (mv-nth 0
              (ctx-app-list-seq (frame->root frame)
                                nil frame
                                (frame-addrs-before-seq frame 0 (take n seq))
                                seq))
      (mv-nth 0
              (ctx-app-list (frame->root frame)
                            nil frame
                            (frame-addrs-before-seq frame 0 (take n seq))))))
    :hints
    (("goal"
      :in-theory (e/d (frame-addrs-before-seq ctx-app-list ctx-app-list-seq)
                      ((:definition member-equal)
                       (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)))
      :induct (dec-induct n))))

  (local
   (defthm
     lemma-2
     (implies
      (and
       (not (zp n))
       (mv-nth
        1
        (ctx-app-list (frame->root frame)
                      nil frame
                      (frame-addrs-before-seq frame 0 (take (+ -1 n) seq))))
       (abs-separate (frame->frame frame))
       (frame-p (frame->frame frame))
       (mv-nth 1 (collapse frame))
       (valid-seqp frame seq)
       (no-duplicatesp-equal (strip-cars (frame->frame frame)))
       (nat-listp seq)
       (<= n (len seq))
       (mv-nth 1
               (ctx-app-list-seq (frame->root frame)
                                 nil frame
                                 (frame-addrs-before-seq frame 0 (take n seq))
                                 seq)))
      (mv-nth 1
              (ctx-app-list (frame->root frame)
                            nil frame
                            (frame-addrs-before-seq frame 0 (take n seq)))))
     :hints
     (("goal"
       :do-not-induct t
       :in-theory (e/d (frame-addrs-before-seq ctx-app-list-seq ctx-app-list)
                       ((:rewrite binary-append-take-nthcdr)
                        (:rewrite frame-addrs-before-seq-of-append)
                        (:rewrite member-equal-nth-take-when-no-duplicatesp)
                        (:rewrite ctx-app-ok-of-ctx-app-list-seq)
                        ctx-app-ok-of-ctx-app-list-seq-lemma-1))
       :use ((:instance (:rewrite binary-append-take-nthcdr)
                        (l (take n seq))
                        (i (+ -1 n)))
             (:instance (:rewrite frame-addrs-before-seq-of-append)
                        (l2 (nthcdr (+ -1 n) (take n seq)))
                        (l1 (take (+ -1 n) (take n seq)))
                        (x 0)
                        (frame frame))
             (:instance (:rewrite take-of-nthcdr)
                        (l seq)
                        (n2 (+ -1 n))
                        (n1 1)))))))

  (local
   (defthm
     lemma-1
     (implies
      (and
       (not (zp n))
       (mv-nth
        1
        (ctx-app-list-seq (frame->root frame)
                          nil frame
                          (frame-addrs-before-seq frame 0 (take (+ -1 n) seq))
                          seq))
       (mv-nth
        1
        (ctx-app-list (frame->root frame)
                      nil frame
                      (frame-addrs-before-seq frame 0 (take (+ -1 n) seq))))
       (abs-separate (frame->frame frame))
       (frame-p (frame->frame frame))
       (mv-nth 1 (collapse frame))
       (valid-seqp frame seq)
       (no-duplicatesp-equal (strip-cars (frame->frame frame)))
       (nat-listp seq)
       (<= n (len seq))
       (mv-nth 1
               (ctx-app-list (frame->root frame)
                             nil frame
                             (frame-addrs-before-seq frame 0 (take n seq)))))
      (mv-nth 1
              (ctx-app-list-seq (frame->root frame)
                                nil frame
                                (frame-addrs-before-seq frame 0 (take n seq))
                                seq)))
     :instructions
     ((:bash
       ("goal"
        :do-not-induct t
        :in-theory (e/d (frame-addrs-before-seq ctx-app-list-seq ctx-app-list)
                        ((:rewrite binary-append-take-nthcdr)
                         (:rewrite frame-addrs-before-seq-of-append)
                         (:rewrite member-equal-nth-take-when-no-duplicatesp)
                         (:rewrite ctx-app-ok-of-ctx-app-list-seq)
                         ctx-app-ok-of-ctx-app-list-seq-lemma-1))
        :use ((:instance (:rewrite binary-append-take-nthcdr)
                         (l (take n seq))
                         (i (+ -1 n)))
              (:instance (:rewrite frame-addrs-before-seq-of-append)
                         (l2 (nthcdr (+ -1 n) (take n seq)))
                         (l1 (take (+ -1 n) (take n seq)))
                         (x 0)
                         (frame frame))
              1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-30)))
      (:dive 2 4)
      := :up
      (:rewrite ctx-app-list-seq-of-append)
      :top :s (:contrapose 15)
      (:dive 1 2 4)
      :=
      :up (:rewrite ctx-app-list-of-append)
      :top (:bash ("goal" :in-theory (e/d (frame-addrs-before-seq
                                           ctx-app-list-seq ctx-app-list)
                                          ((:rewrite member-equal-nth-take-when-no-duplicatesp)
                                           (:rewrite ctx-app-ok-of-ctx-app-list-seq)
                                           ctx-app-ok-of-ctx-app-list-seq-lemma-1))
                   :use (:instance (:rewrite take-of-nthcdr)
                                   (l seq)
                                   (n2 (+ -1 n))
                                   (n1 1)))))))

  (defthm
    1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-34
    (implies
     (and
      (abs-separate (frame->frame frame))
      (frame-p (frame->frame frame))
      (mv-nth '1 (collapse frame))
      (valid-seqp frame seq)
      (no-duplicatesp-equal (strip-cars (frame->frame frame)))
      (nat-listp seq)
      (<= n (len seq)))
     (iff
      (mv-nth 1
              (ctx-app-list-seq (frame->root frame)
                                nil frame
                                (frame-addrs-before-seq frame 0 (take n seq))
                                seq))
      (mv-nth 1
              (ctx-app-list (frame->root frame)
                            nil frame
                            (frame-addrs-before-seq frame 0 (take n seq))))))
    :hints
    (("goal"
      :in-theory (e/d (frame-addrs-before-seq ctx-app-list ctx-app-list-seq)
                      ((:definition member-equal)
                       (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)))
      :induct (dec-induct n)))))

(defthmd
  partial-collapse-correctness-lemma-135
  (implies (and (abs-separate (frame->frame frame))
                (dist-names (frame->root frame)
                            nil (frame->frame frame))
                (frame-p (frame->frame frame))
                (valid-seqp frame seq)
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (nat-listp seq)
                (mv-nth 1 (collapse frame)))
           (and
            (absfat-equiv
             (frame->root (collapse-seq frame seq))
             (mv-nth 0
                     (ctx-app-list (frame->root frame)
                                   nil frame
                                   (frame-addrs-before-seq frame 0 seq))))
            (mv-nth 1
                    (ctx-app-list (frame->root frame)
                                  nil frame
                                  (frame-addrs-before-seq frame 0 seq)))))
  :hints
  (("goal"
    :in-theory (disable valid-seqp-after-collapse-this-lemma-5
                        (:rewrite 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-33)
                        1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-34)
    :use (valid-seqp-after-collapse-this-lemma-5
          (:instance (:rewrite 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-33)
                     (seq seq)
                     (n (len seq))
                     (frame frame))
          (:instance
           1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-34
           (seq seq)
           (n (len seq))
           (frame frame))))))

(local
 (defthmd
   1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-50
   (implies
    (and (abs-separate (frame->frame frame))
         (dist-names (frame->root frame)
                     nil (frame->frame frame))
         (frame-p (frame->frame frame))
         (no-duplicatesp-equal (strip-cars (frame->frame frame)))
         (nat-listp (cons x (seq-this (collapse-this frame x))))
         (mv-nth 1 (collapse frame))
         (consp (assoc-equal x (frame->frame frame)))
         (abs-complete
          (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))))
    (and
     (absfat-equiv
      (frame->root (collapse-seq frame
                                 (cons x (seq-this (collapse-this frame x)))))
      (mv-nth
       0
       (ctx-app-list
        (frame->root frame)
        nil frame
        (frame-addrs-before-seq frame 0
                                (cons x
                                      (seq-this (collapse-this frame x)))))))
     (mv-nth
      1
      (ctx-app-list
       (frame->root frame)
       nil frame
       (frame-addrs-before-seq frame 0
                               (cons x
                                     (seq-this (collapse-this frame x))))))))
   :hints
   (("goal" :do-not-induct t
     :in-theory (disable valid-seqp-after-collapse-this)
     :use ((:instance partial-collapse-correctness-lemma-135
                      (seq (cons x (seq-this (collapse-this frame x)))))
           valid-seqp-after-collapse-this)))))

;; This is inductive, so probably not great to disable it.
(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-35
  (implies
   (and (<= (nfix n) (len (frame->frame frame)))
        (abs-separate (frame->frame frame))
        (dist-names (frame->root frame)
                    nil (frame->frame frame))
        (frame-p (frame->frame frame))
        (mv-nth 1 (collapse frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (and (equal (frame->root (collapse-iter frame n))
               (mv-nth 0
                       (ctx-app-list (frame->root frame)
                                     nil
                                     frame (frame-addrs-before frame 0 n))))
        (mv-nth 1
                (ctx-app-list (frame->root frame)
                              nil
                              frame (frame-addrs-before frame 0 n)))))
  :hints
  (("goal" :induct (collapse-iter frame n)
    :in-theory
    (e/d (collapse-iter frame-addrs-before
                        ctx-app-list collapse)
         ((:definition no-duplicatesp-equal)
          (:definition member-equal)
          (:rewrite nthcdr-when->=-n-len-l)
          (:definition strip-cars)
          (:definition remove-assoc-equal)
          (:rewrite 1st-complete-of-remove-assoc-2)
          (:rewrite collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-2)
          (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8 . 1)
          (:type-prescription abs-addrs-of-remove-assoc-lemma-1)
          (:rewrite 1st-complete-of-put-assoc-lemma-1)
          (:definition len))))))

(encapsulate
  ()

  (local
   (defthm
     1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-36
     (implies
      (and
       (set-equiv
        (remove-equal (1st-complete (frame->frame frame))
                      (frame-addrs-root (frame->frame frame)))
        (remove-equal (1st-complete (frame->frame frame))
                      (intersection-equal (abs-addrs (frame->root frame))
                                          (strip-cars (frame->frame frame)))))
       (subsetp-equal (abs-addrs (frame->root frame))
                      (frame-addrs-root (frame->frame frame)))
       (ctx-app-ok
        (frame->root frame)
        (1st-complete (frame->frame frame))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))))
      (set-equiv (frame-addrs-root (frame->frame frame))
                 (intersection-equal (abs-addrs (frame->root frame))
                                     (strip-cars (frame->frame frame)))))
     :hints
     (("goal"
       :do-not-induct t
       :in-theory (e/d (ctx-app-ok)
                       (cons-of-remove-under-set-equiv-1))
       :use ((:instance cons-of-remove-under-set-equiv-1
                        (x (1st-complete (frame->frame frame)))
                        (l (frame-addrs-root (frame->frame frame))))
             (:instance
              cons-of-remove-under-set-equiv-1
              (x (1st-complete (frame->frame frame)))
              (l (intersection-equal (abs-addrs (frame->root frame))
                                     (strip-cars (frame->frame frame))))))))))

  (defthmd
    1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-37
    (implies (and (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
                  (abs-separate frame)
                  (subsetp-equal (abs-addrs (frame->root frame))
                                 (frame-addrs-root (frame->frame frame)))
                  (frame-p frame)
                  (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                  (mv-nth 1 (collapse frame)))
             (set-equiv (frame-addrs-root (frame->frame frame))
                        (intersection-equal (abs-addrs (frame->root frame))
                                            (strip-cars (frame->frame frame)))))
    :hints
    (("goal" :in-theory (e/d (collapse)
                             (member-equal assoc-equal remove-assoc-equal
                                           put-assoc-equal strip-cars))))))

(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-38
  (implies
   (and
    (abs-separate (frame->frame frame))
    (frame-p (frame->frame frame))
    (mv-nth 1 (collapse frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (mv-nth 1
            (ctx-app-list
             (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
             frame
             (frame-addrs-before frame x (collapse-1st-index frame x)))))
   (equal
    (set-difference-equal
     (abs-addrs (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
     (frame-addrs-before frame x (collapse-1st-index frame x)))
    nil))
  :instructions
  (:promote
   (:claim
    (equal
     nil
     (abs-addrs
      (mv-nth
       0
       (ctx-app-list
        (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
        (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
        frame
        (frame-addrs-before frame
                            x (collapse-1st-index frame x))))))
    :hints (("goal" :do-not-induct t
             :in-theory (e/d nil
                             (1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-24))
             :use 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-24)))
   :bash))

;; This could be kinda important, although for now we're keeping it disabled to
;; avoid weird stuff coming in from nowhere.
(defthmd
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-39
  (implies
   (and
    (abs-separate (frame->frame frame))
    (frame-p (frame->frame frame))
    (mv-nth 1 (collapse frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (consp (assoc-equal x (frame->frame frame))))
   (set-equiv
    (abs-addrs (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
    (frame-addrs-before frame x (collapse-1st-index frame x))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (e/d
     (set-equiv 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-4)
     (1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-38 (:rewrite abs-addrs-of-ctx-app-list)))
    :use
    (1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-38
     (:instance
      (:rewrite consp-of-set-difference$)
      (l2 (frame-addrs-before frame x (collapse-1st-index frame x)))
      (l1 (abs-addrs
           (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
     (:instance
      (:rewrite abs-addrs-of-ctx-app-list)
      (relpath (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
      (frame frame)
      (fs (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
      (l (frame-addrs-before frame
                             x (collapse-1st-index frame x))))))))

(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-40
  (implies
   (and (frame-p (frame->frame frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (not (equal (frame-val->src (cdr (assoc-equal (car seq)
                                                      (frame->frame frame))))
                    0)))
   (not (member-equal (car seq)
                      (frame-addrs-root (frame->frame frame)))))
  :hints
  (("goal" :expand
    ((:with (:rewrite member-of-frame-addrs-root)
            (member-equal (car seq)
                          (frame-addrs-root (frame->frame frame))))))))

(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-41
  (implies
   (and (atom (frame-val->path (cdr (assoc-equal 0 frame))))
        (subsetp-equal seq (strip-cars (frame->frame frame)))
        (consp seq)
        (abs-separate frame)
        (frame-p (frame->frame frame))
        (mv-nth 1 (collapse frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (equal (frame-val->src (cdr (assoc-equal (car seq)
                                                 (frame->frame frame))))
               0))
   (member-equal (car seq)
                 (abs-addrs (frame->root frame))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (ctx-app-ok)
                           (abs-separate-of-collapse-this-lemma-7))
           :use (:instance abs-separate-of-collapse-this-lemma-7
                           (x (car seq))))))

(defthmd
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-42
  (implies
   (and (atom (frame-val->path (cdr (assoc-equal 0 frame))))
        (subsetp-equal seq (strip-cars (frame->frame frame)))
        (abs-separate frame)
        (frame-p (frame->frame frame))
        (mv-nth 1 (collapse frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame))))
   (set-equiv (frame-addrs-before-seq frame 0 seq)
              (intersection-equal seq (abs-addrs (frame->root frame)))))
  :hints
  (("goal"
    :in-theory (enable frame-addrs-before-seq
                       (:rewrite 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-39))
    :induct (frame-addrs-before-seq frame 0 seq)
    :expand ((intersection-equal seq (abs-addrs (frame->root frame)))))))

(local
 (defthm
   1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-43
   (implies
    (and
     (equal
      (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))
      0)
     (< 0 (1st-complete (frame->frame frame)))
     (subsetp-equal
      (remove-equal (1st-complete (frame->frame frame))
                    (strip-cars (frame->frame frame)))
      (seq-this (collapse-this frame
                               (1st-complete (frame->frame frame)))))
     (ctx-app-ok
      (frame->root frame)
      (1st-complete (frame->frame frame))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))
    (subsetp-equal (strip-cars (frame->frame frame))
                   (seq-this frame)))
   :hints
   (("goal"
     :do-not-induct t
     :in-theory (e/d (seq-this collapse-iter)
                     ((:rewrite subsetp-append1)
                      (:rewrite prefixp-when-equal-lengths)
                      (:linear len-of-seq-this-1)
                      (:definition assoc-equal)
                      (:rewrite remove-when-absent)
                      (:definition remove-equal)
                      (:rewrite subsetp-member . 3)
                      (:rewrite assoc-of-frame->frame-of-collapse-this)
                      (:rewrite assoc-of-car-when-member)
                      (:rewrite consp-of-assoc-of-frame->frame)
                      (:rewrite subsetp-car-member)
                      (:definition len)))
     :use ((:instance (:rewrite subsetp-append1)
                      (c (seq-this frame))
                      (b (remove-equal (1st-complete (frame->frame frame))
                                       (strip-cars (frame->frame frame))))
                      (a (list (1st-complete (frame->frame frame))))))))))

(local
 (defthm
   1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-44
   (implies
    (and
     (subsetp-equal
      (remove-equal (1st-complete (frame->frame frame))
                    (strip-cars (frame->frame frame)))
      (seq-this (collapse-this frame
                               (1st-complete (frame->frame frame)))))
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
     (mv-nth 1
             (collapse (collapse-this frame
                                      (1st-complete (frame->frame frame))))))
    (subsetp-equal (strip-cars (frame->frame frame))
                   (seq-this frame)))
   :hints
   (("goal"
     :do-not-induct t
     :in-theory (e/d (seq-this collapse-iter)
                     ((:rewrite subsetp-append1)
                      (:rewrite prefixp-when-equal-lengths)
                      (:linear len-of-seq-this-1)
                      (:definition assoc-equal)
                      (:rewrite remove-when-absent)
                      (:definition remove-equal)
                      (:rewrite subsetp-member . 3)
                      (:rewrite assoc-of-frame->frame-of-collapse-this)
                      (:rewrite assoc-of-car-when-member)
                      (:rewrite consp-of-assoc-of-frame->frame)
                      (:rewrite subsetp-car-member)
                      (:definition len)
                      (:rewrite frame-addrs-root-of-frame->frame-of-collapse-this-lemma-1)))
     :use ((:instance (:rewrite subsetp-append1)
                      (c (seq-this frame))
                      (b (remove-equal (1st-complete (frame->frame frame))
                                       (strip-cars (frame->frame frame))))
                      (a (list (1st-complete (frame->frame frame))))))))))

(local
 (defthm
   1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-45
   (implies (mv-nth 1 (collapse frame))
            (subsetp-equal (strip-cars (frame->frame frame))
                           (seq-this frame)))
   :hints
   (("goal"
     :in-theory
     (e/d
      (collapse seq-this)
      (assoc-equal
       remove-assoc-equal
       put-assoc-equal strip-cars
       (:rewrite assoc-of-frame->frame-of-collapse-this)
       (:rewrite subsetp-car-member)
       (:definition member-equal)
       (:rewrite partial-collapse-correctness-lemma-2)
       (:rewrite len-when-prefixp)
       (:rewrite nthcdr-when->=-n-len-l)
       (:rewrite abs-addrs-when-m1-file-alist-p)
       (:definition remove-equal)))))))

(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-46
  (implies (and (atom (frame-val->path (cdr (assoc-equal 0 frame))))
                (abs-separate frame)
                (frame-p frame)
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (mv-nth 1 (collapse frame)))
           (set-equiv (frame-addrs-before frame 0 (len (frame->frame frame)))
                      (frame-addrs-root (frame->frame frame))))
  :hints
  (("goal"
    :in-theory (e/d (frame-addrs-before frame-addrs-root
                                        collapse len-when-consp collapse-iter)
                    (assoc-equal remove-assoc-equal put-assoc-equal
                                 member-equal strip-cars)))))

(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-47
  (implies
   (and
    (frame-p (frame->frame frame))
    (mv-nth 1 (collapse frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (consp
     (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                    (frame->frame frame))))
                  (frame->frame frame))))
   (< (collapse-1st-index frame (car seq))
      (collapse-1st-index
       frame
       (frame-val->src (cdr (assoc-equal (car seq)
                                         (frame->frame frame)))))))
  :hints
  (("goal"
    :in-theory
    (disable
     (:linear collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-1))
    :use
    (:instance
     (:linear collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-1)
     (x (car seq))
     (frame frame))))
  :rule-classes :linear)

;; Another rule probably best left disabled.
(defthmd
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-48
  (implies
   (and (abs-separate (frame->frame frame))
        (frame-p (frame->frame frame))
        (mv-nth 1 (collapse frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (consp (assoc-equal x (frame->frame frame))))
   (set-equiv
    (frame-addrs-before-seq frame x seq)
    (intersection-equal
     seq
     (abs-addrs
      (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))))))
  :hints
  (("goal"
    :in-theory (enable frame-addrs-before-seq
                       (:rewrite 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-39))
    :induct (frame-addrs-before-seq frame x seq)
    :expand
    ((:with
      (:rewrite member-of-frame-addrs-before)
      (member-equal
       (car seq)
       (frame-addrs-before
        frame
        (frame-val->src (cdr (assoc-equal (car seq)
                                          (frame->frame frame))))
        (collapse-1st-index
         frame
         (frame-val->src (cdr (assoc-equal (car seq)
                                           (frame->frame frame))))))))
     (:free (y) (intersection-equal seq y)))
    :do-not-induct t)))

;; Might enable this later, but for now it just seems like trouble.
(defthmd
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-49
  (implies
   (and (mv-nth 1 (collapse frame))
        (abs-separate (frame->frame frame))
        (frame-p (frame->frame frame))
        (consp (assoc-equal x
                            (frame->frame (collapse-seq frame seq))))
        (valid-seqp frame seq)
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (nat-listp seq))
   (equal
    (abs-addrs
     (frame-val->dir
      (cdr (assoc-equal x
                        (frame->frame (collapse-seq frame seq))))))
    (set-difference-equal
     (abs-addrs (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
     seq)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (abs-addrs-of-ctx-app-list-seq)
                    ((:rewrite set-difference$-of-intersection$-1)))
    :use
    (1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-48
     (:instance
      (:rewrite set-difference$-of-intersection$-1)
      (l2 seq)
      (l1
       (abs-addrs
        (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))))))

(defthm 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-70
  (implies (and (consp (assoc-equal x (frame->frame frame)))
                (frame-p frame))
           (natp x))
  :rule-classes :forward-chaining)

(encapsulate
  ()

  (local (include-book "chain-leading-to-complete"))

  (local
   (defthm
     lemma-1
     (implies
      (and (valid-seqp frame seq)
           (nat-listp seq)
           (mv-nth 1 (collapse frame))
           (no-duplicatesp-equal (strip-cars (frame->frame frame)))
           (consp (assoc-equal x (frame->frame frame)))
           (frame-p frame)
           (abs-separate frame)
           (atom (frame-val->path (cdr (assoc-equal 0 frame)))))
      (not
       (consp
        (abs-addrs
         (frame-val->dir
          (cdr (assoc-equal (car (chain-leading-to-complete frame x nil seq))
                            (frame->frame (collapse-seq frame seq)))))))))
     :hints
     (("goal"
       :do-not-induct t
       :in-theory (disable chain-leading-to-complete-correctness-2
                           1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-49)
       :use (chain-leading-to-complete-correctness-2
             (:instance 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-49
                        (x (car (chain-leading-to-complete frame x nil seq)))))))))

  (local
   (defthm
     lemma-2
     (implies (and (not (intersectp-equal acc seq))
                   (not (member-equal x seq))
                   (consp (chain-leading-to-complete frame x acc seq))
                   (consp (assoc-equal (car (chain-leading-to-complete frame x acc seq))
                                       (frame->frame frame))))
              (consp (assoc-equal (car (chain-leading-to-complete frame x acc seq))
                                  (frame->frame (collapse-seq frame seq)))))
     :hints
     (("goal"
       :in-theory (disable (:rewrite not-intersectp-of-chain-leading-to-complete-1
                                     . 2)
                           (:rewrite member-of-set-difference-equal))
       :use ((:instance (:rewrite member-of-set-difference-equal)
                        (y seq)
                        (x (strip-cars (frame->frame frame)))
                        (a (car (chain-leading-to-complete frame x acc seq))))
             (:rewrite not-intersectp-of-chain-leading-to-complete-1
                       . 2))))))

  (defthmd
    1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-51
    (implies (and (valid-seqp frame seq)
                  (nat-listp seq)
                  (mv-nth 1 (collapse frame))
                  (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                  (consp (assoc-equal x (frame->frame frame)))
                  (frame-p frame)
                  (abs-separate frame)
                  (atom (frame-val->path (cdr (assoc-equal 0 frame))))
                  (not (member-equal x seq)))
             (< 0
                (1st-complete (frame->frame (collapse-seq frame seq)))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d (intersectp-equal
            abs-complete-when-atom-abs-addrs)
           (lemma-1 1st-complete-correctness-2
                    subsetp-member))
      :use (lemma-1
            (:instance 1st-complete-correctness-2
                       (frame (frame->frame (collapse-seq frame seq)))
                       (x (car (chain-leading-to-complete frame x nil seq))))
            (:instance subsetp-member
                       (y (strip-cars (frame->frame frame)))
                       (a (car (chain-leading-to-complete frame x nil seq)))
                       (x (chain-leading-to-complete frame x nil seq))))))
    :rule-classes :linear)

  (local
   (defthm
     1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-52
     (implies
      (and (mv-nth 1 (collapse frame))
           (not (member-equal y acc))
           (member-equal y
                         (chain-leading-to-complete frame x acc seq)))
      (prefixp (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
               (frame-val->path (cdr (assoc-equal y (frame->frame frame))))))
     :hints (("goal" :induct (chain-leading-to-complete frame x acc seq)))))

  (local
   (defthm
     1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-53
     (implies (and (frame-p frame)
                   (atom (assoc-equal 0 frame))
                   (consp (assoc-equal y frame))
                   (abs-complete (frame-val->dir (cdr (assoc-equal y frame))))
                   (fat32-filename-list-prefixp
                    path (frame-val->path (cdr (assoc-equal y frame)))))
              (< 0 (1st-complete-under-path frame path)))
     :hints (("goal" :in-theory (enable 1st-complete-under-path)))
     :rule-classes :linear))

  (defthmd
    1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-54
    (implies
     (and (fat32-filename-list-prefixp
           path (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
          (mv-nth 1 (collapse frame))
          (valid-seqp frame seq)
          (nat-listp seq)
          (no-duplicatesp-equal (strip-cars (frame->frame frame)))
          (consp (assoc-equal x (frame->frame frame)))
          (frame-p frame)
          (abs-separate frame)
          (not (consp (frame-val->path$inline (cdr (assoc-equal 0 frame)))))
          (not (member-equal x seq)))
     (< 0
        (1st-complete-under-path (frame->frame (collapse-seq frame seq))
                                 path)))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d (abs-complete intersectp-equal)
           (1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-53 valid-seqp-after-collapse-this-lemma-25
                                           (:rewrite subsetp-car-member)))
      :use ((:instance 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-53
                       (frame (frame->frame (collapse-seq frame seq)))
                       (y (car (chain-leading-to-complete frame x nil seq))))
            (:instance (:rewrite subsetp-car-member)
                       (y (strip-cars (frame->frame frame)))
                       (x (chain-leading-to-complete frame x nil seq))))
      :restrict
      ((1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-52 ((acc nil) (seq seq))))))))

;; Something is very weird about this...
(defthmd
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-55
  (implies
   (and
    (if
        (zp (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
        (ctx-app-ok (frame->root (collapse-seq frame seq))
                    x
                    (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
      (and
       (ctx-app-ok
        (frame-val->dir
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame (collapse-seq frame seq)))))
        x
        (nthcdr
         (len
          (frame-val->path
           (cdr
            (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
       (prefixp
        (frame-val->path
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
        (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
    (abs-complete
     (frame-val->dir
      (cdr (assoc-equal x
                        (frame->frame (collapse-seq frame seq))))))
    (not (zp x))
    (consp (assoc-equal x
                        (frame->frame (collapse-seq frame seq))))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (valid-seqp frame seq))
   (equal (collapse-this (collapse-seq frame seq)
                         x)
          (collapse-seq frame (append seq (list x)))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (collapse-seq valid-seqp)
                           (collapse-seq-of-collapse-seq))
           :expand (collapse-seq (collapse-seq frame seq)
                                 (list x))
           :use (:instance collapse-seq-of-collapse-seq
                           (seq2 (list x))
                           (seq1 seq)))))

;; Inductive, so probably best left enabled etc
(defthm 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-56
  (implies
   (and
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
    (abs-separate frame)
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (consp (assoc-equal x
                        (frame->frame (collapse-seq frame seq))))
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame))))))
   (consp
    (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame (collapse-seq frame seq)))))
  :hints
  (("goal"
    :in-theory (e/d (collapse-seq valid-seqp collapse-this)
                    (valid-seqp-after-collapse-this-lemma-25
                     (:rewrite remove-assoc-of-put-assoc)
                     (:definition remove-assoc-equal)
                     (:rewrite different-from-own-src-1)
                     (:rewrite assoc-of-car-when-member)
                     (:definition member-equal)
                     (:rewrite put-assoc-equal-without-change . 2)
                     (:rewrite subsetp-car-member)
                     (:rewrite consp-of-assoc-of-frame->frame)))
    :induct t
    :do-not-induct t)))

(defthm 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-57
  (implies
   (and
    (ctx-app-ok (frame->root frame)
                x
                (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
    (abs-separate frame)
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (consp (assoc-equal x
                        (frame->frame (collapse-seq frame seq)))))
   (ctx-app-ok
    (frame->root (collapse-seq frame seq))
    x
    (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
  :hints
  (("goal"
    :in-theory (e/d (collapse-seq valid-seqp collapse-this)
                    (valid-seqp-after-collapse-this-lemma-25
                     (:rewrite remove-assoc-of-put-assoc)
                     (:definition remove-assoc-equal)
                     (:rewrite different-from-own-src-1)
                     (:rewrite assoc-of-car-when-member)
                     (:definition member-equal)
                     (:rewrite put-assoc-equal-without-change . 2)
                     (:rewrite subsetp-car-member)
                     (:rewrite consp-of-assoc-of-frame->frame))))))

(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-58
  (implies
   (not (equal (1st-complete (frame->frame (collapse-seq frame seq)))
               0))
   (consp (assoc-equal (1st-complete (frame->frame (collapse-seq frame seq)))
                       (frame->frame frame))))
  :hints
  (("goal"
    :do-not-induct t
    :use
    (:theorem
     (implies
      (and
       (not
        (consp
         (assoc-equal (1st-complete (frame->frame (collapse-seq frame seq)))
                      (frame->frame frame))))
       (not (equal (1st-complete (frame->frame (collapse-seq frame seq)))
                   0)))
      (consp
       (assoc-equal (1st-complete (frame->frame (collapse-seq frame seq)))
                    (frame->frame (collapse-seq frame seq)))))))))

;; Inductive, so probably best left enabled etc
(defthm
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-59
  (implies
   (and
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
    (abs-separate frame)
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (consp (assoc-equal x
                        (frame->frame (collapse-seq frame seq)))))
   (ctx-app-ok
    (frame-val->dir
     (cdr (assoc-equal
           (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
           (frame->frame (collapse-seq frame seq)))))
    x
    (nthcdr
     (len
      (frame-val->path
       (cdr (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame)))))
     (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
  :hints
  (("goal"
    :induct t
    :do-not-induct t
    :in-theory (e/d (collapse-seq valid-seqp collapse-this)
                    (valid-seqp-after-collapse-this-lemma-25
                     (:rewrite remove-assoc-of-put-assoc)
                     (:definition remove-assoc-equal)
                     (:rewrite different-from-own-src-1)
                     (:rewrite assoc-of-car-when-member)
                     (:definition member-equal)
                     (:rewrite put-assoc-equal-without-change . 2)
                     (:rewrite subsetp-car-member)
                     (:rewrite consp-of-assoc-of-frame->frame))))))

(local
 (defthm 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-60
   (implies
    (and
     (< (len (frame->frame (collapse-seq frame (append seq (list x)))))
        (len (frame->frame (collapse-seq frame seq))))
     (not
      (equal
       (1st-complete
        (frame->frame
         (collapse-seq
          frame
          (append seq
                  (cons x
                        (seq-this (collapse-this (collapse-seq frame seq)
                                                 x)))))))
       0))
     (no-duplicatesp-equal (strip-cars (frame->frame frame))))
    (valid-seqp frame (append seq (list x))))
   :hints
   (("goal"
     :do-not-induct t
     :induct t
     :in-theory (e/d (collapse-seq valid-seqp collapse-this)
                     (valid-seqp-after-collapse-this-lemma-25
                      (:rewrite remove-assoc-of-put-assoc)
                      (:definition remove-assoc-equal)
                      (:rewrite different-from-own-src-1)
                      (:rewrite assoc-of-car-when-member)
                      (:definition member-equal)
                      (:rewrite put-assoc-equal-without-change . 2)
                      (:rewrite subsetp-car-member)
                      (:rewrite consp-of-assoc-of-frame->frame)
                      (:definition assoc-equal)
                      (:rewrite true-listp-when-abs-file-alist-p)
                      (:linear len-when-prefixp)
                      (:rewrite abs-file-alist-p-when-m1-file-alist-p)
                      (:rewrite abs-addrs-when-m1-file-alist-p)
                      (:rewrite abs-file-alist-p-correctness-1)
                      (:rewrite abs-file-alist-p-of-put-assoc-equal)
                      (:rewrite abs-file-alist-p-of-put-assoc-equal)
                      (:rewrite consp-of-remove-assoc-1)
                      (:type-prescription assoc-when-zp-len)
                      (:rewrite ctx-app-ok-of-ctx-app-1)
                      (:rewrite len-when-prefixp)
                      (:rewrite remove-when-absent)
                      (:rewrite abs-addrs-when-m1-file-contents-p)
                      (:linear len-when-hifat-bounded-file-alist-p . 2)
                      (:linear len-when-hifat-bounded-file-alist-p . 1)
                      (:rewrite m1-file-contents-p-correctness-1)
                      (:rewrite valid-seqp-after-collapse-this-lemma-26)
                      (:rewrite member-of-frame-addrs-before-seq)
                      (:rewrite abs-addrs-of-ctx-app-2)
                      (:rewrite subsetp-of-remove1)))))))

(local
 (encapsulate
   ()

   (local (in-theory
           (e/d (valid-seqp-after-collapse-this-lemma-6
                 collapse-seq seq-this
                 collapse-iter 1st-complete)
                ((:rewrite
                  assoc-of-frame->frame-of-collapse-this)
                 (:rewrite nthcdr-when->=-n-len-l)
                 (:definition assoc-equal)
                 (:rewrite collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-2)
                 (:rewrite
                  abs-separate-of-frame->frame-of-collapse-this-lemma-8
                  . 2)
                 (:linear len-of-seq-this-1)
                 valid-seqp-after-collapse-this-lemma-25))))

   (local
    (defun induction-scheme (frame seq)
      (declare (xargs :measure (len (frame->frame (collapse-seq frame seq)))))
      (cond
       ((and
         (consp (seq-this (collapse-seq frame seq)))
         (< (len
             (frame->frame
              (collapse-seq
               frame
               (append seq (list (car (seq-this (collapse-seq frame seq))))))))
            (len (frame->frame (collapse-seq frame seq)))))
        (induction-scheme
         frame
         (append seq (list (car (seq-this (collapse-seq frame seq)))))))
       (t (mv frame seq)))))

   (defthm
     1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-61
     (implies
      (and (mv-nth 1 (collapse frame))
           (abs-separate frame)
           (frame-p (frame->frame frame))
           (no-duplicatesp-equal (strip-cars (frame->frame frame)))
           (valid-seqp frame seq)
           (nat-listp seq)
           (not (consp (frame-val->path (cdr (assoc-equal 0 frame))))))
      (equal
       (1st-complete
        (frame->frame
         (collapse-seq frame
                       (append seq
                               (seq-this (collapse-seq frame seq))))))
       0))
     :hints (("goal" :do-not-induct t
              :induct (induction-scheme frame seq)
              :expand ((seq-this (collapse-seq frame seq))
                       (collapse-iter (collapse-seq frame seq)
                                      1)))
             ("subgoal *1/2.5'"
              :in-theory (enable 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-55))
             ("subgoal *1/1.1''"
              :in-theory (enable 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-55))))))

(local
 (defthm
   1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-62
   (implies
    (and (nat-listp seq)
         (valid-seqp frame
                     (append seq
                             (seq-this (collapse-seq frame seq))))
         (mv-nth 1 (collapse frame))
         (no-duplicatesp-equal (strip-cars (frame->frame frame)))
         (consp (assoc-equal x (frame->frame frame)))
         (frame-p frame)
         (abs-separate frame)
         (not (consp (frame-val->path$inline (cdr (assoc-equal 0 frame))))))
    (member-equal x
                  (append seq
                          (seq-this (collapse-seq frame seq)))))
   :hints
   (("goal"
     :do-not-induct t
     :use ((:instance 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-51
                      (seq (append seq
                                   (seq-this (collapse-seq frame seq))))))))))

(local
 (defthm
   1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-63
   (implies
    (and
     (consp (assoc-equal y (frame->frame frame)))
     (abs-complete (frame-val->dir (cdr (assoc-equal y (frame->frame frame)))))
     (mv-nth 1 (collapse frame))
     (no-duplicatesp-equal (strip-cars (frame->frame frame)))
     (consp (assoc-equal x (frame->frame frame)))
     (frame-p frame)
     (abs-separate frame)
     (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
     (not (equal x y)))
    (member-equal x (seq-this (collapse-this frame y))))
   :hints
   (("goal"
     :do-not-induct t
     :in-theory
     (e/d
      (collapse-seq)
      (1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-62 valid-seqp-after-collapse-this))
     :use ((:instance 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-62
                      (seq (list y)))
           (:instance valid-seqp-after-collapse-this
                      (x y)))))))

(local
 (defthm
   1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-64
   (implies (and (mv-nth 1 (collapse frame))
                 (< (nfix n) (len (seq-this frame))))
            (consp (assoc-equal (nth n (seq-this frame))
                                (frame->frame frame))))
   :hints
   (("goal"
     :in-theory (e/d (seq-this nth collapse-iter collapse)
                     ((:rewrite nthcdr-when->=-n-len-l)
                      (:rewrite consp-of-assoc-of-frame->frame)
                      (:definition member-equal)
                      (:definition no-duplicatesp-equal)
                      (:rewrite partial-collapse-correctness-lemma-2)
                      (:rewrite subsetp-when-prefixp)
                      (:rewrite assoc-of-car-when-member)
                      (:rewrite subsetp-car-member)
                      (:rewrite prefixp-when-equal-lengths)
                      (:definition assoc-equal)
                      (:linear natp-of-nth-of-seq-this)
                      (:linear nth-of-seq-this-1)
                      (:rewrite abs-fs-fix-when-abs-fs-p)
                      (:rewrite valid-seqp-after-collapse-this-lemma-28)
                      (:rewrite ctx-app-ok-when-abs-complete)
                      (:rewrite frame->root-of-collapse-this)
                      (:rewrite abs-fs-p-of-ctx-app)
                      (:rewrite collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-2)
                      (:rewrite m1-file-alist-p-of-final-val-seq-lemma-3)
                      (:rewrite m1-file-alist-p-of-final-val-seq-lemma-3)))
     :induct (collapse-iter frame n))
    ("subgoal *1/1.2" :expand (seq-this frame)))))

(local
 (defthm
   1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-65
   (implies
    (and
     (natp x)
     (consp (assoc-equal x (frame->frame frame)))
     (abs-complete
      (frame-val->dir$inline (cdr (assoc-equal x (frame->frame frame)))))
     (not (zp n))
     (mv-nth 1 (collapse frame))
     (not (equal (nth (+ -1 n) (seq-this frame))
                 x))
     (< (nfix (+ -1 n))
        (len (seq-this frame)))
     (no-duplicatesp-equal (strip-cars (frame->frame frame)))
     (abs-separate frame)
     (frame-p frame)
     (not (consp (frame-val->path$inline (cdr (assoc-equal 0 frame))))))
    (member-equal (nth (+ -1 n) (seq-this frame))
                  (seq-this (collapse-this frame x))))
   :hints
   (("goal"
     :do-not-induct t
     :in-theory (disable (:rewrite valid-seqp-after-collapse-this-lemma-8))
     :use (:instance (:rewrite valid-seqp-after-collapse-this-lemma-8)
                     (seq (seq-this (collapse-this frame x)))
                     (frame (collapse-this frame x))
                     (x (nth (+ -1 n) (seq-this frame))))))))

(local
 (encapsulate
   ()

   (local (include-book "std/basic/inductions" :dir :system))

   (local
    (defthm
      lemma
      (implies
       (and
        (consp (assoc-equal x (frame->frame frame)))
        (abs-complete
         (frame-val->dir$inline (cdr (assoc-equal x (frame->frame frame)))))
        (not (zp n))
        (<= n (len (seq-this frame)))
        (subsetp-equal (take (+ -1 n) (seq-this frame))
                       (cons x (seq-this (collapse-this frame x))))
        (mv-nth 1 (collapse frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (abs-separate frame)
        (frame-p frame)
        (not (consp (frame-val->path$inline (cdr (assoc-equal 0 frame))))))
       (subsetp-equal (take n (seq-this frame))
                      (cons x (seq-this (collapse-this frame x)))))
      :hints
      (("goal" :do-not-induct t
        :in-theory (disable (:rewrite subsetp-append1))
        :use ((:instance (:rewrite subsetp-append1)
                         (c (cons x (seq-this (collapse-this frame x))))
                         (b (nthcdr (+ -1 n)
                                    (take n (seq-this frame))))
                         (a (take (+ -1 n)
                                  (take n (seq-this frame)))))
              (:instance (:rewrite take-of-nthcdr)
                         (l (seq-this frame))
                         (n2 (+ -1 n))
                         (n1 1)))))))

   (defthm
     1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-66
     (implies
      (and
       (consp (assoc-equal x (frame->frame frame)))
       (abs-complete
        (frame-val->dir$inline (cdr (assoc-equal x (frame->frame frame)))))
       (mv-nth 1 (collapse frame))
       (<= (nfix n) (len (seq-this frame)))
       (no-duplicatesp-equal (strip-cars (frame->frame frame)))
       (abs-separate frame)
       (frame-p frame)
       (not (consp (frame-val->path$inline (cdr (assoc-equal 0 frame))))))
      (subsetp-equal (take n (seq-this frame))
                     (cons x (seq-this (collapse-this frame x)))))
     :hints (("goal" :in-theory (e/d nil nil)
              :induct (dec-induct n))))))

(local
 (defthm
   1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-67
   (implies
    (and
     (abs-separate frame)
     (frame-p frame)
     (atom (frame-val->path (cdr (assoc-equal 0 frame))))
     (no-duplicatesp-equal (strip-cars (frame->frame frame)))
     (mv-nth 1 (collapse frame))
     (consp (assoc-equal x (frame->frame frame)))
     (abs-complete
      (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))))
    (set-equiv (cons x (seq-this (collapse-this frame x)))
               (strip-cars (frame->frame frame))))
   :hints (("goal" :do-not-induct t
            :in-theory (e/d (set-equiv subsetp-equal)
                            (1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-66))
            :use (:instance 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-66
                            (n (len (seq-this frame))))))))

(local
 (defthm
   1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-68
   (implies
    (and
     (atom (frame-val->path (cdr (assoc-equal 0 frame))))
     (abs-separate frame)
     (subsetp-equal (abs-addrs (frame->root frame))
                    (frame-addrs-root (frame->frame frame)))
     (frame-p frame)
     (no-duplicatesp-equal (strip-cars (frame->frame frame)))
     (mv-nth 1 (collapse frame))
     (consp (assoc-equal x (frame->frame frame)))
     (abs-complete
      (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))))
    (set-equiv
     (frame-addrs-before-seq frame 0
                             (cons x (seq-this (collapse-this frame x))))
     (frame-addrs-before frame 0 (len (frame->frame frame)))))
   :hints
   (("goal" :do-not-induct t
     :in-theory (enable 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-37)
     :use (:instance 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-42
                     (seq (cons x
                                (seq-this (collapse-this frame x)))))))))

;; This rule is trouble, because it can rewrite
;; (mv-nth 0 (collapse (collapse-this frame (1st-complete (frame->frame frame)))))
;; and
;; (mv-nth 1 (collapse (collapse-this frame (1st-complete (frame->frame frame)))))
;; terms, which arise naturally from opening up the definition of collapse...
(defthmd
  1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-69
  (implies
   (and
    (abs-separate frame)
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (mv-nth 1 (collapse frame))
    (consp (assoc-equal x (frame->frame frame)))
    (abs-complete (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
    (atom (frame-val->path$inline (cdr (assoc-equal 0 frame))))
    (subsetp-equal (abs-addrs (frame->root frame))
                   (frame-addrs-root (frame->frame frame))))
   (and (absfat-equiv (mv-nth 0 (collapse (collapse-this frame x)))
                      (mv-nth 0 (collapse frame)))
        (iff (mv-nth 1 (collapse (collapse-this frame x)))
             (mv-nth 1 (collapse frame)))))
  :hints
  (("goal"
    :do-not-induct t
    :use
    (1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-50
     (:instance 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-35
                (n (len (frame->frame frame))))
     (:instance
      (:rewrite ctx-app-list-when-set-equiv)
      (l1 (frame-addrs-before frame 0 (len (frame->frame frame))))
      (l2
       (frame-addrs-before-seq frame 0
                               (cons x (seq-this (collapse-this frame x)))))
      (frame frame)
      (relpath nil)
      (fs (frame->root frame)))
     collapse-iter-correctness-1
     (:instance (:rewrite collapse-seq-of-seq-this-is-collapse)
                (frame (collapse-this frame x)))
     (:instance set-equiv-implies-equal-len-1-when-no-duplicatesp
                (x (cons x (seq-this (collapse-this frame x))))
                (y (strip-cars (frame->frame frame)))))
    :in-theory
    (e/d (collapse-seq)
         (1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-35
          (:rewrite collapse-seq-of-seq-this-is-collapse)
          (:rewrite nthcdr-when->=-n-len-l)
          (:rewrite different-from-own-src-1)
          (:type-prescription frame-val->path$inline)
          (:definition nthcdr)
          (:type-prescription abs-addrs-of-remove-assoc-lemma-1)
          (:type-prescription assoc-when-zp-len)
          (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
          (:rewrite
           collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-2)
          hifat-equiv-when-absfat-equiv)))))

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
     (:rewrite 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-69)
     (mv-nth
      1
      (collapse (collapse-this frame
                               (1st-complete-under-path (frame->frame frame)
                                                        path))))))))

(encapsulate
  ()

  (local
   (defun induction-scheme (dir frame seq)
     (declare (xargs :measure (len (frame->frame frame))))
     (cond
      ((and
        (not (or (atom (frame->frame frame))
                 (atom seq)))
        (not
         (or
          (zp (car seq))
          (atom (assoc-equal (car seq)
                             (frame->frame frame)))
          (not (abs-complete
                (frame-val->dir (cdr (assoc-equal (car seq)
                                                  (frame->frame frame))))))))
        (not (zp (frame-val->src (cdr (assoc-equal (car seq)
                                                   (frame->frame frame))))))
        (not
         (or
          (equal (frame-val->src (cdr (assoc-equal (car seq)
                                                   (frame->frame frame))))
                 (car seq))
          (atom
           (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                          (frame->frame frame))))
                        (frame->frame frame)))))
        (and
         (prefixp
          (frame-val->path
           (cdr
            (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                           (frame->frame frame))))
                         (frame->frame frame))))
          (frame-val->path (cdr (assoc-equal (car seq)
                                             (frame->frame frame)))))
         (ctx-app-ok
          (frame-val->dir
           (cdr
            (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                           (frame->frame frame))))
                         (frame->frame frame))))
          (car seq)
          (nthcdr
           (len
            (frame-val->path
             (cdr (assoc-equal
                   (frame-val->src (cdr (assoc-equal (car seq)
                                                     (frame->frame frame))))
                   (frame->frame frame)))))
           (frame-val->path (cdr (assoc-equal (car seq)
                                              (frame->frame frame))))))))
       (induction-scheme dir (collapse-this frame (car seq))
                         (cdr seq)))
      ((and
        (not (or (atom (frame->frame frame))
                 (atom seq)))
        (not
         (or
          (zp (car seq))
          (atom (assoc-equal (car seq)
                             (frame->frame frame)))
          (not (abs-complete
                (frame-val->dir (cdr (assoc-equal (car seq)
                                                  (frame->frame frame))))))))
        (zp (frame-val->src (cdr (assoc-equal (car seq)
                                              (frame->frame frame)))))
        (ctx-app-ok (frame->root frame)
                    (car seq)
                    (frame-val->path (cdr (assoc-equal (car seq)
                                                       (frame->frame frame))))))
       (induction-scheme
        (ctx-app
         dir
         (frame-val->dir (cdr (assoc-equal (car seq)
                                           (frame->frame frame))))
         (car seq)
         (frame-val->path (cdr (assoc-equal (car seq)
                                            (frame->frame frame)))))
        (collapse-this frame (car seq))
        (cdr seq)))
      (t (mv dir frame seq)))))

  (defthm
    collapse-seq-congruence-lemma-1
    (implies
     (absfat-equiv (frame->root frame) dir)
     (equal
      (len
       (frame->frame (collapse-seq (frame-with-root dir (frame->frame frame))
                                   seq)))
      (len (frame->frame (collapse-seq frame seq)))))
    :hints (("goal" :in-theory (e/d (collapse-seq collapse-this)
                                    (len put-assoc-equal
                                         remove-assoc-equal strip-cars))
             :induct (induction-scheme dir frame seq)))))

(defthm
  collapse-seq-congruence-lemma-2
  (equal
   (len
    (frame->frame
     (collapse-seq
      (frame-with-root (frame->root frame)
                       (remove-assoc-equal 0 (frame->frame frame)))
      seq)))
   (len (frame->frame (collapse-seq frame seq))))
  :hints (("goal" :in-theory (enable collapse-seq)
           :induct (collapse-seq frame seq))))

(defthm
  collapse-seq-congruence-lemma-3
  (equal
   (len (frame->frame
         (collapse-seq (frame-with-root root (remove-assoc-equal 0 frame))
                       seq)))
   (len (frame->frame (collapse-seq (frame-with-root root frame)
                                    seq))))
  :hints (("goal" :in-theory (disable collapse-seq-congruence-lemma-2)
           :use (:instance collapse-seq-congruence-lemma-2
                           (frame (frame-with-root root frame))))))

(defthm
  collapse-seq-congruence-1
  (implies
   (absfat-equiv root1 root2)
   (equal (len (frame->frame (collapse-seq (frame-with-root root1 frame)
                                           seq)))
          (len (frame->frame (collapse-seq (frame-with-root root2 frame)
                                           seq)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable collapse-seq-congruence-lemma-1)
    :use
    ((:instance collapse-seq-congruence-lemma-1
                (frame (frame-with-root root1 frame))
                (dir root2))
     (:instance (:rewrite collapse-seq-congruence-lemma-1)
                (seq seq)
                (frame (frame-with-root root2 (remove-assoc-equal 0 frame)))
                (dir (abs-fs-fix root2))))))
  :rule-classes :congruence)

(encapsulate
  ()

  (local
   (defun induction-scheme (dir frame seq x)
     (declare (xargs :measure (len (frame->frame frame))))
     (cond
      ((and (not (atom (frame->frame frame)))
        (not (atom seq))
        (not (zp (car seq)))
        (not (atom (assoc-equal (car seq) (frame->frame frame))))
        (abs-complete (frame-val->dir (cdr (assoc-equal (car seq) (frame->frame frame)))))
        (not (zp (frame-val->src (cdr (assoc-equal (car seq) (frame->frame frame))))))
        (not (equal (frame-val->src (cdr (assoc-equal (car seq) (frame->frame frame))))
                    (car seq)))
        (not (atom (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                                  (frame->frame frame))))
                                (frame->frame frame))))
        (prefixp (frame-val->path
                  (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                                      (frame->frame frame))))
                                    (frame->frame frame))))
         (frame-val->path (cdr (assoc-equal (car seq) (frame->frame frame)))))
        (ctx-app-ok (frame-val->dir
                     (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                                         (frame->frame frame))))
                                       (frame->frame frame))))
         (car seq)
         (nthcdr (len (frame-val->path
                       (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                                           (frame->frame frame))))
                                         (frame->frame frame)))))
                 (frame-val->path (cdr (assoc-equal (car seq) (frame->frame
                                                               frame))))))
        (equal x (car seq)))
       (induction-scheme
        (abs-fs-fix
         (ctx-app
          (frame-val->dir
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (remove-assoc-equal x (frame->frame frame)))))
          dir
          x
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (remove-assoc-equal x (frame->frame frame))))))
           (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
        (collapse-this frame (car seq)) (cdr seq)
        (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
      ((and (not (atom (frame->frame frame)))
        (not (atom seq))
        (not (zp (car seq)))
        (not (atom (assoc-equal (car seq) (frame->frame frame))))
        (abs-complete (frame-val->dir (cdr (assoc-equal (car seq) (frame->frame frame)))))
        (not (zp (frame-val->src (cdr (assoc-equal (car seq) (frame->frame frame))))))
        (not (equal (frame-val->src (cdr (assoc-equal (car seq) (frame->frame frame))))
                    (car seq)))
        (not (atom (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                                  (frame->frame frame))))
                                (frame->frame frame))))
        (prefixp (frame-val->path
                  (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                                      (frame->frame frame))))
                                    (frame->frame frame))))
         (frame-val->path (cdr (assoc-equal (car seq) (frame->frame frame)))))
        (ctx-app-ok (frame-val->dir
                     (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                                         (frame->frame frame))))
                                       (frame->frame frame))))
         (car seq)
         (nthcdr (len (frame-val->path
                       (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                                           (frame->frame frame))))
                                         (frame->frame frame)))))
                 (frame-val->path (cdr (assoc-equal (car seq) (frame->frame
                                                               frame))))))
        (equal x (frame-val->src (cdr (assoc-equal (car seq)
                                                   (frame->frame frame))))))
       (induction-scheme
        (abs-fs-fix
         (ctx-app
          dir
          (frame-val->dir (cdr (assoc-equal (car seq)
                                            (frame->frame frame))))
          (car seq)
          (nthcdr
           (len
            (frame-val->path
             (cdr (assoc-equal
                   (frame-val->src
                    (cdr (assoc-equal (car seq)
                                      (frame->frame frame))))
                   (remove-assoc-equal (car seq)
                                       (frame->frame frame))))))
           (frame-val->path
            (cdr (assoc-equal (car seq)
                              (frame->frame frame)))))))
        (collapse-this frame (car seq)) (cdr seq)
        x))
      ((and (not (atom (frame->frame frame)))
        (not (atom seq))
        (not (zp (car seq)))
        (not (atom (assoc-equal (car seq) (frame->frame frame))))
        (abs-complete (frame-val->dir (cdr (assoc-equal (car seq) (frame->frame frame)))))
        (not (zp (frame-val->src (cdr (assoc-equal (car seq) (frame->frame frame))))))
        (not (equal (frame-val->src (cdr (assoc-equal (car seq) (frame->frame frame))))
                    (car seq)))
        (not (atom (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                                  (frame->frame frame))))
                                (frame->frame frame))))
        (prefixp (frame-val->path
                  (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                                      (frame->frame frame))))
                                    (frame->frame frame))))
         (frame-val->path (cdr (assoc-equal (car seq) (frame->frame frame)))))
        (ctx-app-ok (frame-val->dir
                     (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                                         (frame->frame frame))))
                                       (frame->frame frame))))
         (car seq)
         (nthcdr (len (frame-val->path
                       (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                                           (frame->frame frame))))
                                         (frame->frame frame)))))
                 (frame-val->path (cdr (assoc-equal (car seq) (frame->frame frame)))))))
       (induction-scheme dir (collapse-this frame (car seq)) (cdr seq) x))
      ((and
        (not (atom (frame->frame frame)))
        (not (atom seq))
        (not (zp (car seq)))
        (not (atom (assoc-equal (car seq) (frame->frame frame))))
        (abs-complete (frame-val->dir (cdr (assoc-equal (car seq) (frame->frame frame)))))
        (zp (frame-val->src (cdr (assoc-equal (car seq) (frame->frame frame)))))
        (ctx-app-ok (frame->root frame) (car seq)
                    (frame-val->path (cdr (assoc-equal (car seq) (frame->frame frame))))))
       (induction-scheme dir (collapse-this frame (car seq)) (cdr seq) x))
      (t (mv dir frame seq x)))))

  (defthm
    collapse-seq-congruence-lemma-4
    (implies
     (and
      (consp (assoc-equal x (frame->frame frame)))
      (absfat-equiv (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
                    dir))
     (equal
      (len
       (frame->frame
        (collapse-seq
         (frame-with-root
          (frame->root frame)
          (put-assoc-equal
           x
           (change-frame-val (cdr (assoc-equal x (frame->frame frame)))
                             :dir dir)
           (frame->frame frame)))
         seq)))
      (len (frame->frame (collapse-seq frame seq)))))
    :hints
    (("goal"
      :in-theory (e/d (collapse-seq collapse-this)
                      (len put-assoc-equal
                           remove-assoc-equal strip-cars
                           (:rewrite put-assoc-equal-without-change . 2)
                           (:type-prescription assoc-when-zp-len)
                           (:rewrite consp-of-assoc-of-frame->frame)
                           (:rewrite assoc-of-car-when-member)
                           (:rewrite
                            different-from-own-src-1)
                           (:definition member-equal)
                           (:rewrite subsetp-car-member)
                           (:definition no-duplicatesp-equal)
                           (:rewrite subsetp-when-prefixp)
                           (:rewrite valid-seqp-when-prefixp)
                           (:rewrite true-listp-when-abs-file-alist-p)
                           hifat-equiv-when-absfat-equiv
                           absfat-equiv-implies-equal-m1-file-alist-p-of-abs-fs-fix-1))
      :induct (induction-scheme dir frame seq x)
      :expand
      (collapse-seq
       (frame-with-root
        (frame->root frame)
        (put-assoc-equal
         x
         (frame-val (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
                    dir
                    (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
         (frame->frame frame)))
       seq)))))

(defthm
  collapse-seq-congruence-2
  (implies
   (absfat-equiv dir1 dir2)
   (equal
    (len
     (frame->frame
      (collapse-seq
       (frame-with-root
        root
        (put-assoc-equal
         x
         (frame-val
          (frame-val->path (cdr (assoc-equal x frame)))
          dir1
          (frame-val->src (cdr (assoc-equal x frame))))
         frame))
       seq)))
    (len
     (frame->frame
      (collapse-seq
       (frame-with-root
        root
        (put-assoc-equal
         x
         (frame-val
          (frame-val->path (cdr (assoc-equal x frame)))
          dir2
          (frame-val->src (cdr (assoc-equal x frame))))
         frame))
       seq)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (e/d (collapse-seq)
         (collapse-seq-congruence-lemma-4
          (:rewrite collapse-seq-congruence-lemma-3)))
    :use
    ((:instance
      collapse-seq-congruence-lemma-4
      (frame
       (frame-with-root
        root
        (put-assoc-equal
         x
         (change-frame-val (cdr (assoc-equal x frame))
                           :dir dir1)
         frame)))
      (dir dir2))
     (:instance
      (:rewrite collapse-seq-congruence-lemma-3)
      (seq seq)
      (frame
       (put-assoc-equal
        0
        (frame-val (frame-val->path (cdr (assoc-equal 0 frame)))
                   dir1
                   (frame-val->src (cdr (assoc-equal 0 frame))))
        frame))
      (root root))
     (:instance
      (:rewrite collapse-seq-congruence-lemma-3)
      (seq seq)
      (frame
       (put-assoc-equal
        0
        (frame-val (frame-val->path (cdr (assoc-equal 0 frame)))
                   dir2
                   (frame-val->src (cdr (assoc-equal 0 frame))))
        frame))
      (root root))))
   ("subgoal 2''"
    :use
    (:instance
     (:rewrite collapse-seq-congruence-lemma-3)
     (seq seq)
     (frame
      (put-assoc-equal
       x
       (frame-val (frame-val->path (cdr (assoc-equal x frame)))
                  dir2
                  (frame-val->src (cdr (assoc-equal x frame))))
       frame))
     (root root))))
  :rule-classes :congruence)

(defthm
  partial-collapse-correctness-lemma-1
  (implies
   (and
    (absfat-subsetp
     (ctx-app
      (ctx-app
       (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                             x)))
       y y-var (cdr y-path))
      z z-var (cdr y-path))
     (ctx-app
      (ctx-app
       (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                             x)))
       z z-var (cdr y-path))
      y y-var (cdr y-path)))
    (abs-file-alist-p x)
    (abs-no-dups-p x))
   (absfat-subsetp
    (put-assoc-equal
     (fat32-filename-fix (car y-path))
     (abs-file
      (abs-file->d-e (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                           x)))
      (ctx-app
       (ctx-app (abs-file->contents
                 (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                   x)))
                y y-var (cdr y-path))
       z z-var (cdr y-path)))
     x)
    (put-assoc-equal
     (fat32-filename-fix (car y-path))
     (abs-file
      (abs-file->d-e (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                           x)))
      (ctx-app
       (ctx-app (abs-file->contents
                 (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                   x)))
                z z-var (cdr y-path))
       y y-var (cdr y-path)))
     x)))
  :hints
  (("goal"
    :in-theory (e/d (ctx-app ctx-app-ok)
                    ((:rewrite absfat-subsetp-of-put-assoc-1)))
    :use
    ((:instance
      (:rewrite absfat-subsetp-of-put-assoc-1)
      (abs-file-alist2
       (put-assoc-equal
        (fat32-filename-fix (car y-path))
        (abs-file
         (abs-file->d-e
          (cdr (assoc-equal (fat32-filename-fix (car y-path))
                            x)))
         (ctx-app
          (ctx-app
           (abs-file->contents
            (cdr (assoc-equal (fat32-filename-fix (car y-path))
                              x)))
           z z-var (cdr y-path))
          y y-var (cdr y-path)))
        x))
      (abs-file-alist1 x)
      (val
       (abs-file
        (abs-file->d-e (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                             x)))
        (ctx-app
         (ctx-app
          (abs-file->contents
           (cdr (assoc-equal (fat32-filename-fix (car y-path))
                             x)))
          y y-var (cdr y-path))
         z z-var (cdr y-path))))
      (name (fat32-filename-fix (car y-path))))))))

(defthmd
  partial-collapse-correctness-lemma-9
  (implies
   (and
    (not (and (consp (assoc-equal x frame))
              (abs-complete (frame-val->dir (cdr (assoc-equal x frame))))))
    (no-duplicatesp-equal (strip-cars frame))
    (frame-p frame)
    (< 0 x))
   (not (equal (1st-complete frame) x)))
  :hints (("goal" :in-theory (enable 1st-complete))))

;; Inductive, thus left enabled.
(defthmd
  partial-collapse-correctness-lemma-5
  (implies
   (and (no-duplicatesp-equal (strip-cars frame))
        (not (zp (1st-complete (remove-assoc-equal x frame)))))
   (and
    (consp (assoc-equal (1st-complete (remove-assoc-equal x frame))
                        frame))
    (equal
     (abs-addrs
      (frame-val->dir
       (cdr (assoc-equal (1st-complete (remove-assoc-equal x frame))
                         frame))))
     nil)))
  :hints (("goal" :in-theory (e/d (1st-complete)
                                  (1st-complete-correctness-1)))
          ("subgoal *1/2"
           :use (:instance (:type-prescription 1st-complete-correctness-1)
                           (frame (remove-assoc-equal x (cdr frame)))))))

;; Inductive, thus left enabled.
(defthm partial-collapse-correctness-lemma-11
  (implies (and (not (zp x))
                (mv-nth 1 (collapse frame)))
           (not (member-equal x (frame-addrs-before frame x n))))
  :hints (("goal" :in-theory (enable frame-addrs-before collapse))))

;; Inductive, thus left enabled.
(local
 (defthm
   partial-collapse-correctness-lemma-4
   (implies
    (and (frame-p (frame->frame frame))
         (not (zp (frame-val->src (cdr (assoc-equal (nth n (seq-this frame))
                                                    (frame->frame frame))))))
         (no-duplicatesp-equal (strip-cars (frame->frame frame)))
         (abs-separate (frame->frame frame)))
    (ctx-app-ok
     (frame-val->dir
      (cdr
       (assoc-equal (frame-val->src (cdr (assoc-equal (nth n (seq-this frame))
                                                      (frame->frame frame))))
                    (frame->frame frame))))
     (nth n (seq-this frame))
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal (nth n (seq-this frame))
                                                (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal (nth n (seq-this frame))
                                         (frame->frame frame)))))))
   :hints
   (("goal"
     :in-theory (e/d (seq-this collapse-iter collapse-seq
                               partial-collapse-correctness-lemma-9)
                     ((:definition member-equal)
                      (:definition no-duplicatesp-equal)
                      (:definition remove-equal)
                      (:definition nthcdr)
                      (:definition assoc-equal)
                      (:rewrite member-equal-nth)
                      (:rewrite collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-2)
                      (:linear nth-of-seq-this-1)
                      (:linear natp-of-nth-of-seq-this)
                      (:definition strip-cars)
                      (:rewrite m1-file-alist-p-of-final-val-seq-lemma-3)
                      (:rewrite abs-file-alist-p-correctness-1)
                      (:rewrite nth-of-seq-this-1)
                      (:rewrite natp-of-nth-of-seq-this)
                      (:rewrite remove-when-absent)
                      (:rewrite abs-addrs-of-ctx-app-2)
                      (:rewrite ctx-app-when-not-ctx-app-ok)
                      (:linear position-when-member)))
     :induct (collapse-iter frame n)
     :expand ((seq-this frame))))))

;; Inductive, hence kept.
(local
 (defthm
   partial-collapse-correctness-lemma-10
   (implies
    (and (mv-nth 1 (collapse frame))
         (no-duplicatesp-equal (strip-cars (frame->frame frame))))
    (equal (1st-complete (frame->frame (collapse-seq frame (seq-this frame))))
           0))
   :hints
   (("goal"
     :in-theory
     (e/d
      (collapse-seq seq-this collapse-iter collapse)
      ((:rewrite assoc-of-frame->frame-of-collapse-this)
       (:rewrite nthcdr-when->=-n-len-l)
       (:definition assoc-equal)
       (:rewrite
        collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-2)
       (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8
                 . 2)
       (:linear len-of-seq-this-1)
       (:rewrite subsetp-when-prefixp)))
     :expand (collapse-iter frame 1)
     :induct (collapse frame)
     :do-not-induct t))))

(defthm
  partial-collapse-correctness-lemma-40
  (implies
   (and
    (equal
     (len
      (frame->frame
       (collapse-seq
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
          (frame-val
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
           (ctx-app
            (ctx-app
             (frame-val->dir
              (cdr
               (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame))))
             (frame-val->dir (cdr (assoc-equal (car seq)
                                               (frame->frame frame))))
             (car seq)
             (nthcdr
              (len
               (frame-val->path
                (cdr
                 (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))))
              (frame-val->path (cdr (assoc-equal (car seq)
                                                 (frame->frame frame))))))
            (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
            x
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
           (frame-val->src
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (remove-assoc-equal x
                              (remove-assoc-equal (car seq)
                                                  (frame->frame frame)))))
        (cdr seq))))
     (+ -2 (- (len (cdr seq)))
        (len (frame->frame frame))))
    (consp seq)
    (consp (assoc-equal (car seq)
                        (frame->frame frame)))
    (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
           (frame-val->src (cdr (assoc-equal (car seq)
                                             (frame->frame frame)))))
    (not (equal x (car seq)))
    (abs-complete (frame-val->dir (cdr (assoc-equal (car seq)
                                                    (frame->frame frame)))))
    (not (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (car seq)))
    (consp
     (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))
    (prefixp
     (frame-val->path
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
     (frame-val->path (cdr (assoc-equal (car seq)
                                        (frame->frame frame)))))
    (ctx-app-ok
     (frame-val->dir
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
     (car seq)
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal (car seq)
                                         (frame->frame frame))))))
    (consp (assoc-equal x (frame->frame frame)))
    (abs-separate frame)
    (abs-complete (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
    (frame-p (frame->frame frame))
    (prefixp
     (frame-val->path
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
     (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
   (equal
    (len
     (frame->frame
      (collapse-seq
       (frame-with-root
        (frame->root frame)
        (put-assoc-equal
         (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
         (frame-val
          (frame-val->path
           (cdr
            (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame))))
          (ctx-app
           (frame-val->dir
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
           (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
           x
           (nthcdr
            (len
             (frame-val->path
              (cdr
               (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
            (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
          (frame-val->src
           (cdr
            (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame)))))
         (remove-assoc-equal x (frame->frame frame))))
       seq)))
    (+ -2 (- (len (cdr seq)))
       (len (frame->frame frame)))))
  :instructions
  (:promote
   (:contrapose 1)
   (:=
    (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame))
    (assoc-equal
     (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
     (remove-assoc-equal x
                         (remove-assoc-equal (car seq)
                                             (frame->frame frame)))))
   (:dv 1 1 1 1 1 2 2 2)
   (:claim
    (and
     (abs-complete
      (abs-fs-fix
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))))
     (abs-complete
      (abs-fs-fix (frame-val->dir (cdr (assoc-equal (car seq)
                                                    (frame->frame frame))))))
     (case-split
      (and
       (not (equal (nfix x) (nfix (car seq))))
       (abs-no-dups-p
        (ctx-app
         (ctx-app
          (frame-val->dir
           (cdr
            (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (remove-assoc-equal x
                                 (remove-assoc-equal (car seq)
                                                     (frame->frame frame))))))
          (frame-val->dir (cdr (assoc-equal (car seq)
                                            (frame->frame frame))))
          (car seq)
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (remove-assoc-equal
                x
                (remove-assoc-equal (car seq)
                                    (frame->frame frame)))))))
           (frame-val->path (cdr (assoc-equal (car seq)
                                              (frame->frame frame))))))
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
         x
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (remove-assoc-equal
               x
               (remove-assoc-equal (car seq)
                                   (frame->frame frame)))))))
          (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
       (abs-no-dups-p
        (ctx-app
         (ctx-app
          (frame-val->dir
           (cdr
            (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (remove-assoc-equal x
                                 (remove-assoc-equal (car seq)
                                                     (frame->frame frame))))))
          (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
          x
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (remove-assoc-equal
                x
                (remove-assoc-equal (car seq)
                                    (frame->frame frame)))))))
           (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
         (frame-val->dir (cdr (assoc-equal (car seq)
                                           (frame->frame frame))))
         (car seq)
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (remove-assoc-equal
               x
               (remove-assoc-equal (car seq)
                                   (frame->frame frame)))))))
          (frame-val->path (cdr (assoc-equal (car seq)
                                             (frame->frame frame)))))))))
     (not
      (intersectp-equal
       (names-at (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
                 nil)
       (names-at
        (frame-val->dir
         (cdr
          (assoc-equal
           (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
           (remove-assoc-equal x
                               (remove-assoc-equal (car seq)
                                                   (frame->frame frame))))))
        (nthcdr
         (len
          (frame-val->path
           (cdr
            (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (remove-assoc-equal
              x
              (remove-assoc-equal (car seq)
                                  (frame->frame frame)))))))
         (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))))
     (not
      (intersectp-equal
       (names-at (frame-val->dir (cdr (assoc-equal (car seq)
                                                   (frame->frame frame))))
                 nil)
       (names-at
        (frame-val->dir
         (cdr
          (assoc-equal
           (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
           (remove-assoc-equal x
                               (remove-assoc-equal (car seq)
                                                   (frame->frame frame))))))
        (nthcdr
         (len
          (frame-val->path
           (cdr
            (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (remove-assoc-equal
              x
              (remove-assoc-equal (car seq)
                                  (frame->frame frame)))))))
         (frame-val->path (cdr (assoc-equal (car seq)
                                            (frame->frame frame)))))))))
    :hints
    (("goal"
      :in-theory
      (e/d (fat32-filename-list-prefixp-alt fat32-filename-list-equiv)
           (prefixp-nthcdr-nthcdr))
      :use
      ((:instance
        prefixp-nthcdr-nthcdr
        (n
         (len
          (frame-val->path
           (cdr
            (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame))))))
        (l1 (frame-val->path (cdr (assoc-equal (car seq)
                                               (frame->frame frame)))))
        (l2 (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
       (:instance
        prefixp-nthcdr-nthcdr
        (n
         (len
          (frame-val->path
           (cdr
            (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame))))))
        (l2 (frame-val->path (cdr (assoc-equal (car seq)
                                               (frame->frame frame)))))
        (l1 (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))))))
   (:rewrite ctx-app-of-ctx-app-1)
   :top (:contrapose 1)
   (:dive 1 1 1)
   :x
   :top :split
   :bash (:change-goal nil t)
   :bash (:bash ("goal" :in-theory (e/d (collapse-this)
                                        ((:rewrite abs-no-dups-p-of-ctx-app)
                                         (:rewrite names-at-of-ctx-app)))))))

;; This theorem helps with
;; (valid-seqp (collapse-this frame x) (seq-this (collapse-this frame x)))
;; which is a pre-requisite of the next theorem. Note, adding (mv-nth 1
;; (collapse frame)) kinda defeats the purpose. It seems to be useless but it's
;; inductive...
(defthm
  partial-collapse-correctness-lemma-41
  (implies
   (and
    (valid-seqp frame seq)
    (consp (assoc-equal x (frame->frame frame)))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (not (member-equal x seq))
    (abs-separate frame)
    (abs-complete (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
    (frame-p (frame->frame frame))
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (ctx-app-ok
     (frame-val->dir$inline
      (cdr
       (assoc-equal
        (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
        (frame->frame frame))))
     x
     (nthcdr
      (len
       (frame-val->path$inline
        (cdr
         (assoc-equal
          (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
          (frame->frame frame)))))
      (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame))))))
    (prefixp
     (frame-val->path
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
     (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
   (valid-seqp (collapse-this frame x)
               seq))
  :hints
  (("goal"
    :in-theory
    (e/d (collapse-seq valid-seqp collapse-this)
         ((:definition assoc-equal)
          (:definition member-equal)
          (:linear len-when-prefixp)
          (:rewrite len-when-prefixp)
          (:rewrite m1-file-contents-p-correctness-1)
          nthcdr-when->=-n-len-l
          abs-separate-of-frame->frame-of-collapse-this-lemma-8
          (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-15)
          (:rewrite different-from-own-src-1)))
    :do-not-induct t
    :induct (collapse-seq frame seq))))

(local
 (defthm
   partial-collapse-correctness-lemma-14
   (implies
    (and (abs-separate frame)
         (frame-p frame)
         (no-duplicatesp-equal (strip-cars (frame->frame frame)))
         (mv-nth 1 (collapse frame))
         (consp (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                      path)
                             (frame->frame frame)))
         (atom (frame-val->path (cdr (assoc-equal 0 frame))))
         (subsetp-equal (abs-addrs (frame->root frame))
                        (frame-addrs-root (frame->frame frame))))
    (and
     (absfat-equiv
      (mv-nth
       0
       (collapse (collapse-this frame
                                (1st-complete-under-path (frame->frame frame)
                                                         path))))
      (mv-nth 0 (collapse frame)))
     (iff
      (mv-nth
       1
       (collapse (collapse-this frame
                                (1st-complete-under-path (frame->frame frame)
                                                         path))))
      (mv-nth 1 (collapse frame)))))
   :hints
   (("goal" :use (:instance 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-69
                            (x (1st-complete-under-path (frame->frame frame)
                                                        path)))))))

(defthm
  partial-collapse-correctness-lemma-6
  (implies
   (and (frame-p (frame->frame frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (abs-separate (frame-with-root (frame->root frame)
                                       (frame->frame frame)))
        (subsetp (abs-addrs (frame->root frame))
                 (frame-addrs-root (frame->frame frame))))
   (subsetp-equal
    (abs-addrs (frame->root (partial-collapse frame path)))
    (frame-addrs-root (frame->frame (partial-collapse frame path)))))
  :hints (("goal" :in-theory (enable partial-collapse)
           :induct (partial-collapse frame path))))

(defthm
  partial-collapse-correctness-lemma-7
  (implies (and (dist-names (frame->root frame)
                            nil (frame->frame frame))
                (abs-separate (frame->frame frame))
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (frame-p (frame->frame frame)))
           (dist-names (frame->root (partial-collapse frame path))
                       nil
                       (frame->frame (partial-collapse frame path))))
  :hints (("goal" :in-theory (enable partial-collapse))))

(defthm
  partial-collapse-correctness-lemma-8
  (implies
   (and (frame-p frame)
        (no-duplicatesp-equal (strip-cars frame))
        (abs-separate frame)
        (atom (frame-val->path$inline (cdr (assoc-equal 0 frame)))))
   (not
    (consp
     (frame-val->path (cdr (assoc-equal '0
                                        (partial-collapse frame path)))))))
  :hints (("goal" :in-theory (enable partial-collapse))))

(defthm
  partial-collapse-correctness-1
  (implies
   (and (frame-p frame)
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (abs-separate frame)
        (mv-nth 1 (collapse frame))
        (atom (frame-val->path$inline (cdr (assoc-equal 0 frame))))
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame))))
   (and (absfat-equiv (mv-nth 0
                              (collapse (partial-collapse frame path)))
                      (mv-nth 0 (collapse frame)))
        (iff (mv-nth 1
                     (collapse (partial-collapse frame path)))
             (mv-nth 1 (collapse frame)))))
  :hints (("goal" :in-theory (enable partial-collapse)
           :induct (partial-collapse frame path)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (and (frame-p frame)
                  (no-duplicatesp-equal (strip-cars frame))
                  (abs-separate frame)
                  (mv-nth 1 (collapse frame))
                  (atom (frame-val->path$inline (cdr (assoc-equal 0 frame))))
                  (subsetp-equal (abs-addrs (frame->root frame))
                                 (frame-addrs-root (frame->frame frame))))
             (hifat-equiv (mv-nth 0
                                  (collapse (partial-collapse frame path)))
                          (mv-nth 0 (collapse frame)))))))

(defthm partial-collapse-correctness-lemma-12
  (implies (consp (assoc-equal 0 frame))
           (consp (assoc-equal 0 (partial-collapse frame path))))
  :hints (("goal" :in-theory (enable partial-collapse)))
  :rule-classes :type-prescription)

(defthm
  partial-collapse-correctness-lemma-15
  (implies
   (equal (frame-val->src (cdr (assoc-equal 0 frame)))
          0)
   (equal (frame-val->src (cdr (assoc-equal 0 (partial-collapse frame path))))
          0))
  :hints (("goal" :in-theory (enable partial-collapse
                                     collapse-this frame-with-root)))
  :rule-classes :type-prescription)

(defthm partial-collapse-correctness-2
  (implies (good-frame-p frame)
           (collapse-equiv (partial-collapse frame path)
                           frame))
  :hints (("goal" :in-theory (enable collapse-equiv good-frame-p)
           :do-not-induct t)))

(defund
  seq-this-under-path
  (frame path)
  (declare
   (xargs :measure (len (frame->frame frame))
          :verify-guards nil))
  (b*
      (((when (atom (frame->frame frame))) nil)
       (next-frame (collapse-seq frame (list
                                        (1st-complete-under-path (frame->frame frame)
                                                                 path))))
       ((unless (< (len (frame->frame next-frame)) (len (frame->frame frame))))
        nil))
    (cons (1st-complete-under-path (frame->frame frame)
                                   path)
          (seq-this-under-path next-frame path))))

(defthmd
  collapse-seq-of-seq-this-under-path-is-partial-collapse
  (implies (no-duplicatesp-equal (strip-cars (frame->frame frame)))
           (equal (partial-collapse frame path)
                  (collapse-seq frame
                                (seq-this-under-path frame path))))
  :hints
  (("goal" :in-theory (e/d (partial-collapse collapse-seq seq-this-under-path)
                           ((:definition assoc-equal)
                            (:rewrite nthcdr-when->=-n-len-l)
                            (:definition remove-equal)
                            (:rewrite remove-when-absent)))
    :induct (seq-this-under-path frame path)
    :expand (partial-collapse frame path))))

(defthm nat-listp-of-seq-this-under-path
  (nat-listp (seq-this-under-path frame path))
  :hints (("goal" :in-theory (enable seq-this-under-path))))

(defthmd
  seq-this-under-path-of-fat32-filename-list-fix
  (equal (seq-this-under-path frame (fat32-filename-list-fix path))
         (seq-this-under-path frame path))
  :hints
  (("goal"
    :in-theory (enable seq-this-under-path)
    :induct (seq-this-under-path frame path)
    :expand (seq-this-under-path frame (fat32-filename-list-fix path)))))

(defcong
  fat32-filename-list-equiv
  equal (seq-this-under-path frame path)
  2
  :hints
  (("goal"
    :in-theory (enable fat32-filename-list-equiv)
    :use
    ((:instance seq-this-under-path-of-fat32-filename-list-fix
                (path path-equiv))
     seq-this-under-path-of-fat32-filename-list-fix))))

(defthm
  valid-seqp-of-seq-this-under-path
  (implies (and (frame-p frame)
                (atom (frame-val->path (cdr (assoc-equal 0 frame))))
                (abs-separate frame)
                (subsetp-equal (abs-addrs (frame->root frame))
                               (frame-addrs-root (frame->frame frame)))
                (no-duplicatesp-equal (strip-cars (frame->frame frame))))
           (valid-seqp frame (seq-this-under-path frame path)))
  :hints
  (("goal"
    :in-theory
    (e/d (seq-this-under-path valid-seqp collapse-seq)
         ((:definition fat32-filename-list-prefixp)
          (:rewrite assoc-of-frame->frame-of-collapse-this)
          (:rewrite consp-of-nthcdr)
          (:rewrite ctx-app-when-not-ctx-app-ok)
          (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8
                    . 2)
          (:rewrite nthcdr-when->=-n-len-l)
          (:linear len-when-prefixp)
          (:rewrite partial-collapse-correctness-lemma-2)))
    :induct (seq-this-under-path frame path)
    :expand
    ((collapse-seq
      frame
      (cons
       (1st-complete-under-path (frame->frame frame)
                                path)
       (seq-this-under-path
        (collapse-seq frame
                      (list (1st-complete-under-path (frame->frame frame)
                                                     path)))
        path)))
     (:with
      (:rewrite 1st-complete-under-path-of-frame->frame-of-partial-collapse-lemma-69)
      (mv-nth
       1
       (collapse (collapse-this frame
                                (1st-complete-under-path (frame->frame frame)
                                                         path)))))))))
