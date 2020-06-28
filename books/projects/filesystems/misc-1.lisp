(in-package "ACL2")

(include-book "abs-find-file")
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
   (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
   (:rewrite collapse-congruence-lemma-4)
   (:rewrite abs-addrs-of-ctx-app-1-lemma-2)
   (:rewrite collapse-congruence-lemma-2)
   (:rewrite absfat-equiv-of-ctx-app-lemma-8)
   (:rewrite abs-separate-correctness-1-lemma-19)
   (:rewrite
    partial-collapse-correctness-lemma-20)
   (:rewrite m1-file-alist-p-when-subsetp-equal)
   (:rewrite
    m1-file-alist-p-of-final-val-seq-lemma-3)
   (:rewrite final-val-of-collapse-this-lemma-2)
   (:rewrite collapse-congruence-lemma-5)
   (:rewrite
    abs-find-file-helper-of-collapse-lemma-3)
   (:rewrite
    partial-collapse-correctness-lemma-106)
   (:rewrite
    abs-fs-fix-of-put-assoc-equal-lemma-2)
   final-val-of-collapse-this-lemma-3
   abs-fs-fix-of-put-assoc-equal-lemma-3
   (:type-prescription
    abs-directory-file-p-when-m1-file-p-lemma-1))))

(defthm
  abs-find-file-correctness-1-lemma-1
  (implies
   (and (not (consp (abs-addrs (abs-fs-fix root))))
        (m1-regular-file-p (mv-nth 0
                                   (abs-find-file (frame-with-root root nil)
                                                  path))))
   (equal (mv-nth 0
                  (abs-find-file (frame-with-root root nil)
                                 path))
          (mv-nth 0
                  (hifat-find-file (abs-fs-fix root)
                                   path))))
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
                                         path))
           *enoent*)
    (prefixp (fat32-filename-list-fix x-path)
             (fat32-filename-list-fix path))
    (ctx-app-ok abs-file-alist1 x x-path)
    (not (intersectp-equal (names-at abs-file-alist2 nil)
                           (names-at abs-file-alist1 x-path))))
   (and (equal (mv-nth 1
                       (abs-find-file-helper abs-file-alist1 path))
               *enoent*)
        (equal (mv-nth 1
                       (abs-find-file-helper abs-file-alist2
                                             (nthcdr (len x-path) path)))
               *enoent*))))

;; Should the corollary be a type-prescription?
(defthm
  abs-find-file-correctness-1-lemma-13
  (implies
   (and
    (not (consp (assoc-equal (fat32-filename-fix (car path))
                             abs-file-alist1)))
    (abs-fs-p (append (remove-equal x abs-file-alist1)
                      abs-file-alist2))
    (abs-fs-p abs-file-alist2)
    (equal
     (mv-nth 1
             (abs-find-file-helper (append (remove-equal x abs-file-alist1)
                                           abs-file-alist2)
                                   path))
     0))
   (equal (mv-nth 1
                  (abs-find-file-helper abs-file-alist2 path))
          0))
  :hints
  (("goal"
    :do-not-induct t
    :expand ((abs-find-file-helper abs-file-alist2 path)
             (abs-find-file-helper (append (remove-equal x abs-file-alist1)
                                           abs-file-alist2)
                                   path))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (not (consp (assoc-equal (fat32-filename-fix (car path))
                                   abs-file-alist1)))
          (abs-fs-p (append (remove-equal x abs-file-alist1)
                            abs-file-alist2))
          (abs-fs-p abs-file-alist2)
          (not (equal (mv-nth 1
                              (abs-find-file-helper abs-file-alist2 path))
                      0)))
     (not
      (equal
       (mv-nth 1
               (abs-find-file-helper (append (remove-equal x abs-file-alist1)
                                             abs-file-alist2)
                                     path))
       0))))))

(defthm
  abs-find-file-correctness-1-lemma-8
  (implies
   (and
    (abs-directory-file-p
     (cdr (assoc-equal (fat32-filename-fix (car path))
                       (abs-fs-fix abs-file-alist1))))
    (abs-fs-p (append (remove-equal x abs-file-alist1)
                      abs-file-alist2))
    (abs-fs-p abs-file-alist1)
    (integerp x)
    (equal
     (mv-nth 1
             (abs-find-file-helper abs-file-alist1 path))
     *enoent*))
   (equal (mv-nth 1
                  (abs-find-file-helper
                   (append (remove-equal x abs-file-alist1)
                           abs-file-alist2)
                   path))
          *enoent*))
  :hints
  (("goal"
    :do-not-induct t
    :expand
    ((abs-find-file-helper abs-file-alist1 path)
     (abs-find-file-helper
      (append (remove-equal x abs-file-alist1)
              abs-file-alist2)
      path)))))

(defthm
  abs-find-file-correctness-1-lemma-9
  (implies
   (and
    (not (prefixp (fat32-filename-list-fix relpath)
                  (frame-val->path (cdr (assoc-equal x frame)))))
    (prefixp (fat32-filename-list-fix relpath)
             (fat32-filename-list-fix path))
    (equal (mv-nth 1
                   (abs-find-file-helper (abs-fs-fix dir)
                                         (nthcdr (len relpath) path)))
           0)
    (equal
     (mv-nth 1
             (abs-find-file-helper
              (frame-val->dir (cdr (assoc-equal x frame)))
              (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                      path)))
     0)
    (prefixp (frame-val->path (cdr (assoc-equal x frame)))
             (fat32-filename-list-fix path)))
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
              (fat32-filename-list-fix path))))
     (:instance abs-find-file-correctness-1-lemma-6
                (fs (abs-fs-fix dir))
                (path (nthcdr (len relpath)
                                  (fat32-filename-list-fix path)))
                (n 0))
     (:instance
      abs-find-file-correctness-1-lemma-6
      (fs (frame-val->dir (cdr (assoc-equal x frame))))
      (path (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                        (fat32-filename-list-fix path)))
      (n (+ (len relpath)
            (- (len (frame-val->path (cdr (assoc-equal x frame))))))))
     (:instance len-when-prefixp
                (x (frame-val->path (cdr (assoc-equal x frame))))
                (y (fat32-filename-list-fix relpath)))
     (:instance (:rewrite car-of-nthcdr)
                (x (fat32-filename-list-fix path))
                (i (len relpath)))
     (:instance
      (:rewrite nth-of-nthcdr)
      (x (fat32-filename-list-fix path))
      (m (len (frame-val->path (cdr (assoc-equal x frame)))))
      (n (+ (len relpath)
            (- (len (frame-val->path (cdr (assoc-equal x frame))))))))
     (:instance (:rewrite take-when-prefixp)
                (y (fat32-filename-list-fix path))
                (x (fat32-filename-list-fix relpath)))))))

(defthmd
  abs-find-file-correctness-1-lemma-20
  (implies (and (< (+ (- (len relpath))
                      (len (frame-val->path (cdr (assoc-equal x frame)))))
                   0)
                (prefixp relpath path)
                (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                         path))
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
             (fat32-filename-list-fix path))
    (equal (mv-nth 1
                   (abs-find-file-helper dir (nthcdr (len relpath) path)))
           0)
    (equal
     (mv-nth 1
             (abs-find-file-helper
              (frame-val->dir (cdr (assoc-equal x frame)))
              (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                      path)))
     0)
    (prefixp (frame-val->path (cdr (assoc-equal x frame)))
             (fat32-filename-list-fix path)))
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
                              abs-find-file-correctness-1-lemma-20
                              len-of-fat32-filename-list-fix)
                    (abs-find-file-correctness-1-lemma-6
                     member-of-remove
                     (:rewrite nth-of-fat32-filename-list-fix)
                     (:rewrite take-when-prefixp)
                     (:rewrite nth-of-nthcdr)))
    :use
    ((:instance
      abs-find-file-correctness-1-lemma-6
      (fs (frame-val->dir (cdr (assoc-equal x frame))))
      (path (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                        (fat32-filename-list-fix path)))
      (n 0))
     (:instance abs-find-file-correctness-1-lemma-6
                (fs (abs-fs-fix dir))
                (path (nthcdr (len relpath)
                                  (fat32-filename-list-fix path)))
                (n (+ (len (frame-val->path (cdr (assoc-equal x frame))))
                      (- (len relpath)))))
     (:theorem (equal (+ (len relpath)
                         (- (len relpath))
                         (len (frame-val->path (cdr (assoc-equal x frame)))))
                      (len (frame-val->path (cdr (assoc-equal x frame))))))
     (:instance
      intersectp-member
      (a (nth (len (frame-val->path (cdr (assoc-equal x frame))))
              (fat32-filename-list-fix path)))
      (y (names-at
          dir
          (nthcdr (len relpath)
                  (frame-val->path (cdr (assoc-equal x frame))))))
      (x (remove-equal
          nil
          (strip-cars (frame-val->dir (cdr (assoc-equal x frame)))))))
     (:instance (:rewrite nth-of-nthcdr)
                (x (fat32-filename-list-fix path))
                (m (len relpath))
                (n (+ (- (len relpath))
                      (len (frame-val->path (cdr (assoc-equal x frame)))))))
     (:instance (:rewrite take-when-prefixp)
                (y (fat32-filename-list-fix path))
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
             (fat32-filename-list-fix path))
    (equal (mv-nth 1
                   (abs-find-file-helper (abs-fs-fix dir)
                                         (nthcdr (len relpath) path)))
           0)
    (equal
     (mv-nth 1
             (abs-find-file-helper
              (frame-val->dir (cdr (assoc-equal x frame)))
              (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                      path)))
     0)
    (prefixp (frame-val->path (cdr (assoc-equal x frame)))
             (fat32-filename-list-fix path)))
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
    (e/d (list-equiv nthcdr-when->=-n-len-l len-of-fat32-filename-list-fix)
         (nth-of-fat32-filename-list-fix (:rewrite prefixp-when-equal-lengths)
                                         member-of-remove))
    :use
    ((:instance (:rewrite prefixp-when-equal-lengths)
                (y (frame-val->path (cdr (assoc-equal x frame))))
                (x (fat32-filename-list-fix relpath)))
     (:instance
      (:rewrite intersectp-member)
      (a (nth (len (frame-val->path (cdr (assoc-equal x frame))))
              (fat32-filename-list-fix path)))
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
                   (abs-find-file-helper dir (nthcdr (len relpath) path)))
           0)
    (dist-names dir
                relpath frame)
    (consp (assoc-equal x frame))
    (prefixp (fat32-filename-list-fix relpath)
             (fat32-filename-list-fix path))
    (prefixp (frame-val->path (cdr (assoc-equal x frame)))
             (fat32-filename-list-fix path)))
   (not
    (equal
     (mv-nth 1
             (abs-find-file-helper
              (frame-val->dir (cdr (assoc-equal x frame)))
              (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                      path)))
     0)))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d
                       (abs-find-file-correctness-1-lemma-29)
                       (abs-separate-correctness-1-lemma-19
                        abs-separate-of-frame->frame-of-collapse-this-lemma-16))
           :use ((:instance abs-separate-of-frame->frame-of-collapse-this-lemma-1
                            (dir (abs-fs-fix dir)))
                 (:instance abs-separate-of-frame->frame-of-collapse-this-lemma-16
                            (dir (abs-fs-fix dir))))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and
      (equal (mv-nth 1
                     (abs-find-file-helper dir (nthcdr (len relpath) path)))
             0)
      (dist-names dir
                  relpath frame)
      (consp (assoc-equal x frame))
      (prefixp (fat32-filename-list-fix relpath)
               (fat32-filename-list-fix path))
      (prefixp (frame-val->path (cdr (assoc-equal x frame)))
               (fat32-filename-list-fix path))
      (equal (mv-nth 1 mv) 0))
     (not
      (equal
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal x frame)))
        (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                path))
       mv))))))

(defthm
  abs-find-file-correctness-1-lemma-24
  (implies
   (equal
    (mv-nth
     1
     (abs-find-file-helper (frame-val->dir (cdr (car frame)))
                           (nthcdr (len (frame-val->path (cdr (car frame))))
                                   path)))
    0)
   (equal
    (cons
     (mv-nth
      0
      (abs-find-file-helper (frame-val->dir (cdr (car frame)))
                            (nthcdr (len (frame-val->path (cdr (car frame))))
                                    path)))
     '(0))
    (abs-find-file-helper (frame-val->dir (cdr (car frame)))
                          (nthcdr (len (frame-val->path (cdr (car frame))))
                                  path))))
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
    (equal (mv-nth 1 (abs-find-file frame path))
           0)
    (equal
     (mv-nth 1
             (abs-find-file-helper
              (frame-val->dir (cdr (assoc-equal x frame)))
              (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                      path)))
     0)
    (abs-separate frame)
    (prefixp (frame-val->path (cdr (assoc-equal x frame)))
             (fat32-filename-list-fix path)))
   (equal (abs-find-file-helper
           (frame-val->dir (cdr (assoc-equal x frame)))
           (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                   path))
          (abs-find-file frame path)))
  :hints (("goal" :in-theory (enable abs-find-file abs-separate)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and
      (consp (assoc-equal x frame))
      (equal (mv-nth 1 (abs-find-file frame path))
             0)
      (equal
       (mv-nth
        1
        (hifat-find-file
         (frame-val->dir (cdr (assoc-equal x frame)))
         (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                 path)))
       0)
      (abs-separate frame)
      (prefixp (frame-val->path (cdr (assoc-equal x frame)))
               (fat32-filename-list-fix path))
      (m1-file-alist-p (frame-val->dir (cdr (assoc-equal x frame))))
      (hifat-no-dups-p (frame-val->dir (cdr (assoc-equal x frame)))))
     (equal (hifat-find-file
             (frame-val->dir (cdr (assoc-equal x frame)))
             (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                     path))
            (abs-find-file frame path))))))

(defthm
  abs-find-file-correctness-1-lemma-14
  (implies
   (and
    (equal (mv-nth 1
                   (abs-find-file (frame-with-root root frame)
                                  path))
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
       path))
     0)
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-separate (frame-with-root root frame))
    (m1-regular-file-p (mv-nth 0
                               (abs-find-file (frame-with-root root frame)
                                              path))))
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
      path))
    (mv-nth 0
            (abs-find-file (frame-with-root root frame)
                           path))))
  :hints
  (("goal" :in-theory (enable abs-find-file
                              (:rewrite abs-find-file-correctness-1-lemma-59
                                        . 2)
                              frame-with-root abs-separate)
    :do-not-induct t)))

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
           (path (frame-val->path (cdr (assoc-equal x frame))))
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

(defthm
  abs-find-file-correctness-lemma-9
  (implies (equal (mv-nth 1
                          (hifat-find-file (frame->root frame)
                                           path))
                  0)
           (equal (cons (mv-nth 0
                                (hifat-find-file (frame->root frame)
                                                 path))
                        '(0))
                  (hifat-find-file (frame->root frame)
                                   path)))
  :instructions (:promote (:dive 2)
                          (:rewrite abs-find-file-correctness-1-lemma-31)
                          :top :s))

(defthm
  abs-find-file-correctness-1-lemma-42
  (implies
   (and
    (ctx-app-ok (frame->root frame)
                x
                (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
    (not (equal (mv-nth 1
                        (abs-find-file-helper (frame->root frame)
                                              path))
                *enoent*))
    (dist-names (frame->root frame)
                nil (frame->frame frame)))
   (not
    (equal (mv-nth 1
                   (abs-find-file-helper (frame->root (collapse-this frame x))
                                         path))
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
             (fat32-filename-list-fix path)))
   (prefixp
    (frame-val->path
     (cdr
      (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                   (frame->frame (collapse-this frame x)))))
    (fat32-filename-list-fix path)))
  :hints (("goal" :in-theory (enable collapse-this))))

(defthm
  abs-find-file-correctness-1-lemma-68
  (implies
   (and (< 0
           (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
        (not (equal (mv-nth 1
                            (abs-find-file-helper (frame->root frame)
                                                  path))
                    2)))
   (not
    (equal (mv-nth 1
                   (abs-find-file-helper (frame->root (collapse-this frame x))
                                         path))
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
      path))
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
       path))
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
               path)))
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
                                   path)))
        (m1-regular-file-p
         (mv-nth 0
                 (abs-find-file (frame-with-root (frame->root frame)
                                                 (frame->frame frame))
                                path))))
   (equal (abs-find-file (frame-with-root (frame->root frame)
                                          (frame->frame frame))
                         path)
          (mv (mv-nth 0
                      (hifat-find-file (mv-nth 0 (collapse frame))
                                       path))
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
                     (:definition remove-equal)
                     abs-find-file-of-put-assoc-lemma-7))
    :induct (collapse frame))))

(defthm
  abs-find-file-correctness-lemma-25
  (implies
   (and (no-duplicatesp-equal (abs-addrs (abs-fs-fix fs)))
        (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs path))))
   (no-duplicatesp-equal
    (abs-addrs
     (abs-file->contents (mv-nth 0
                                 (abs-find-file-helper fs path))))))
  :hints (("goal" :in-theory (enable abs-find-file-helper)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (no-duplicatesp-equal (abs-addrs (abs-fs-fix fs)))
     (no-duplicatesp-equal
      (abs-addrs
       (abs-file->contents (mv-nth 0
                                   (abs-find-file-helper fs path))))))
    :hints
    (("goal"
      :in-theory (e/d (abs-file-p abs-directory-file-p abs-file-contents-p
                                  abs-file->contents abs-addrs)
                      ((:rewrite abs-find-file-helper-of-collapse-lemma-7)))
      :use (:rewrite abs-find-file-helper-of-collapse-lemma-7))))))

(defthm
  abs-find-file-correctness-lemma-26
  (implies
   (and
    (equal (mv-nth 1
                   (abs-find-file-helper (frame->root frame)
                                         path))
           2)
    (consp
     (abs-addrs
      (abs-file->contents
       (mv-nth
        0
        (abs-find-file (remove-assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))
                       path)))))
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
   (consp
    (abs-addrs
     (abs-file->contents (mv-nth 0 (abs-find-file frame path))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable (:rewrite abs-find-file-of-remove-assoc-1))
    :use
    ((:instance (:rewrite abs-find-file-of-put-assoc-lemma-4)
                (path path)
                (frame (remove-assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
     (:instance (:rewrite abs-find-file-of-remove-assoc-1)
                (path path)
                (frame (frame->frame frame))
                (x (1st-complete (frame->frame frame))))))))

(defthm
  abs-find-file-correctness-lemma-28
  (implies
   (and
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
      0))
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
      2)))
   (not
    (consp
     (abs-addrs
      (abs-file->contents
       (mv-nth
        0
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
          path))))))))
  :hints
  (("goal"
    :use
    (:instance
     (:rewrite abs-find-file-helper-of-ctx-app-lemma-4)
     (path
      (nthcdr
       (len
        (frame-val->path
         (cdr (assoc-equal
               (frame-val->src
                (cdr (assoc-equal (1st-complete (frame->frame frame))
                                  (frame->frame frame))))
               (frame->frame frame)))))
       path))
     (fs
      (frame-val->dir
       (cdr
        (assoc-equal
         (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (frame->frame frame)))))))))

(defthm
  abs-find-file-correctness-lemma-23
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
        path)))
     0)
    (prefixp
     (fat32-filename-list-fix path)
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame)))))
    (<=
     0
     (+
      (len path)
      (-
       (len
        (frame-val->path
         (cdr (assoc-equal
               (frame-val->src
                (cdr (assoc-equal (1st-complete (frame->frame frame))
                                  (frame->frame frame))))
               (frame->frame frame))))))))
    (abs-file-p
     (mv-nth
      0
      (hifat-find-file
       (mv-nth
        0
        (collapse
         (frame-with-root
          (frame->root frame)
          (put-assoc-equal
           (frame-val->src
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
           (frame-val
            (frame-val->path
             (cdr
              (assoc-equal
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
             (cdr
              (assoc-equal
               (frame-val->src
                (cdr (assoc-equal (1st-complete (frame->frame frame))
                                  (frame->frame frame))))
               (frame->frame frame)))))
           (remove-assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame))))))
       path)))
    (equal
     (abs-file->dir-ent
      (mv-nth
       0
       (hifat-find-file
        (mv-nth
         0
         (collapse
          (frame-with-root
           (frame->root frame)
           (put-assoc-equal
            (frame-val->src
             (cdr (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame))))
            (frame-val
             (frame-val->path
              (cdr
               (assoc-equal
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
              (cdr
               (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame)))))
            (remove-assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))))
        path)))
     (abs-file->dir-ent (mv-nth 0 (abs-find-file frame path))))
    (equal
     (m1-file->contents
      (mv-nth
       0
       (hifat-find-file
        (mv-nth
         0
         (collapse
          (frame-with-root
           (frame->root frame)
           (put-assoc-equal
            (frame-val->src
             (cdr (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame))))
            (frame-val
             (frame-val->path
              (cdr
               (assoc-equal
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
              (cdr
               (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame)))))
            (remove-assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))))
        path)))
     (ctx-app
      (abs-file->contents (mv-nth 0 (abs-find-file frame path)))
      (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))
      (1st-complete (frame->frame frame))
      (nthcdr
       (len path)
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))))
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (< 0 (1st-complete (frame->frame frame)))
    (consp
     (assoc-equal
      (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))
      (frame->frame frame)))
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
        (cdr
         (assoc-equal
          (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
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
           (cdr (assoc-equal
                 (frame-val->src
                  (cdr (assoc-equal (1st-complete (frame->frame frame))
                                    (frame->frame frame))))
                 (frame->frame frame))))
          (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
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
    (not
     (consp
      (abs-addrs
       (abs-file->contents (mv-nth 0 (abs-find-file frame path))))))
    (equal (mv-nth 1 (abs-find-file frame path))
           0))
   (equal
    (cons
     (abs-file
      (abs-file->dir-ent (mv-nth 0 (abs-find-file frame path)))
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
  :hints
  (("goal"
    :in-theory (disable abs-find-file-of-put-assoc-lemma-7)
    :use
    (:instance
     (:rewrite abs-find-file-of-put-assoc-lemma-6)
     (path path)
     (frame (frame->frame frame))
     (x (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))))
    :do-not-induct t)))

(defthm
  abs-find-file-correctness-lemma-30
  (implies
   (and
    (equal (mv-nth 1
                   (abs-find-file-helper (frame->root frame)
                                         path))
           2)
    (equal
     (abs-find-file (remove-assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))
                    path)
     (cons
      (mv-nth
       0
       (hifat-find-file
        (mv-nth
         0
         (collapse
          (frame-with-root
           (frame->root frame)
           (put-assoc-equal
            (frame-val->src
             (cdr (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame))))
            (frame-val
             (frame-val->path
              (cdr
               (assoc-equal
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
              (cdr
               (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame)))))
            (remove-assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))))
        path))
      '(0)))
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
    (abs-find-file frame path)))
  :hints
  (("goal"
    :in-theory (disable
                (:rewrite abs-find-file-of-remove-assoc-1))
    :use (:instance
          (:rewrite abs-find-file-of-remove-assoc-1)
          (path path)
          (frame (frame->frame frame))
          (x (1st-complete (frame->frame frame)))))))

(encapsulate
  ()

  (local (defun foo-equiv (fs1 fs2)
           (b* ((good1 (and (m1-file-alist-p fs1) (hifat-no-dups-p fs1)))
                (good2 (and (m1-file-alist-p fs2) (hifat-no-dups-p fs2))))
             (or (not (or good1 good2))
                 (and good1 good2
                      (hifat-subsetp fs1 fs2)
                      (hifat-subsetp fs2 fs1))))))

  (local (defequiv foo-equiv))

  (local (defun bar-equiv (fs1 fs2)
           (b* ((good1 (abs-fs-p fs1))
                (good2 (abs-fs-p fs2)))
             (or (not (or good1 good2))
                 (and good1 good2
                      (absfat-subsetp fs1 fs2)
                      (absfat-subsetp fs2 fs1))))))

  (local (defequiv bar-equiv))

  (local
   (defrefinement bar-equiv foo-equiv
     :hints
     (("goal"
       :in-theory (e/d (absfat-subsetp-correctness-1 abs-fs-p
                                                     absfat-equiv)
                       (abs-addrs-when-m1-file-alist-p abs-addrs-when-absfat-equiv))
       :use
       (abs-addrs-when-m1-file-alist-p
        (:instance
         abs-addrs-when-m1-file-alist-p (x y))
        abs-addrs-when-absfat-equiv))))))
