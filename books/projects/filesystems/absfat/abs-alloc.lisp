;  abs-alloc.lisp                                       Mihir Mehta

; abs-alloc allocates a new variable from the contents of an existing variable.

(in-package "ACL2")

(include-book "../abs-separate")
(local (include-book "std/lists/intersectp" :dir :system))

(local (in-theory (e/d (abs-file-p-when-m1-regular-file-p
                        len-when-consp)
                       ((:definition member-equal)
                        (:definition intersection-equal)
                        (:definition integer-listp)
                        (:rewrite true-listp-when-string-list)
                        (:definition string-listp)
                        (:linear position-equal-ac-when-member)
                        (:linear position-when-member)
                        (:rewrite nth-when->=-n-len-l)
                        (:linear len-of-remove-assoc-1)
                        (:definition position-equal-ac)
                        (:definition remove1-assoc-equal)
                        (:rewrite m1-directory-file-p-correctness-1)
                        (:rewrite assoc-of-car-when-member)
                        (:rewrite integerp-of-car-when-integer-listp)
                        (:linear
                         len-when-hifat-bounded-file-alist-p . 1)
                        (:rewrite
                         m1-file-p-of-cdar-when-m1-file-alist-p)
                        (:rewrite natp-of-car-when-nat-listp)
                        (:rewrite when-zp-src-of-1st-collapse-1)
                        (:rewrite ctx-app-ok-of-abs-fs-fix-1)
                        (:rewrite
                         abs-fs-fix-of-put-assoc-equal-lemma-2)
                        (:rewrite hifat-file-alist-fix-guard-lemma-1)
                        (:rewrite
                         abs-file-alist-p-of-abs-file->contents)
                        (:rewrite member-of-abs-fs-fix-when-natp)
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
                        take-of-too-many
                        len-of-remove-assoc-2
                        nth-of-take))))

(defund abs-alloc (fs path new-index)
  (declare (xargs :guard
                  (and (fat32-filename-list-p path)
                       (abs-fs-p fs)
                       (natp new-index))
                  :verify-guards nil
                  :measure (len path)))
  (b*
      ((fs (mbe :exec fs :logic (abs-fs-fix fs)))
       (new-index
        (mbe :exec new-index :logic (nfix new-index)))
       ((when (atom path))
        (mv fs (list new-index)))
       (alist-elem (abs-assoc
                    (mbe :exec (car path) :logic (fat32-filename-fix (car path)))
                    fs))
       ((when (or (atom alist-elem)
                  (not (abs-directory-file-p (cdr alist-elem)))))
        (mv nil fs))
       ((mv x y)
        (abs-alloc
         (abs-file->contents (cdr alist-elem))
         (cdr path)
         new-index)))
    (mv x
        (abs-put-assoc
         (mbe :exec (car path) :logic (fat32-filename-fix (car path)))
         (change-abs-file
          (cdr alist-elem)
          :contents
          y)
         fs))))

(defthm
   abs-fs-p-of-abs-alloc-1
   (abs-fs-p (mv-nth 1 (abs-alloc fs path new-index)))
   :hints (("Goal" :in-theory (enable abs-alloc abs-file-alist-p abs-no-dups-p abs-fs-p)
            :induct (abs-alloc fs path new-index))))

(defthm abs-fs-p-of-abs-alloc-2
  (abs-fs-p (mv-nth 0 (abs-alloc fs path new-index)))
  :hints (("goal" :in-theory (enable abs-alloc)
           :induct (abs-alloc fs path new-index))))

(verify-guards abs-alloc)

(defthmd abs-alloc-of-fat32-filename-list-fix
  (equal (abs-alloc fs (fat32-filename-list-fix path)
                       new-index)
         (abs-alloc fs path new-index))
  :hints (("goal" :in-theory (enable abs-alloc))))

(defthm abs-alloc-when-not-natp
  (implies (not (natp new-index))
           (equal (abs-alloc fs path new-index)
                  (abs-alloc fs path 0)))
  :hints (("Goal" :in-theory (enable abs-alloc))))

(defcong
  fat32-filename-list-equiv equal
  (abs-alloc fs path new-index)
  2
  :hints
  (("goal"
    :use (abs-alloc-of-fat32-filename-list-fix
          (:instance abs-alloc-of-fat32-filename-list-fix
                     (path path-equiv))))))

(defcong nat-equiv equal
  (abs-alloc fs path new-index)
  3
  :hints (("goal" :in-theory (enable abs-alloc))))

(defthm abs-alloc-correctness-1
  (implies (and (not (member-equal (nfix new-index)
                                   (abs-addrs (abs-fs-fix fs))))
                (equal (mv-nth 1 (abs-alloc fs path new-index))
                       (abs-fs-fix fs)))
           (equal (mv-nth 0 (abs-alloc fs path new-index))
                  nil))
  :hints (("goal" :in-theory (enable abs-alloc))))

(defthm ctx-app-of-abs-alloc
  (equal (ctx-app (mv-nth 1 (abs-alloc fs path new-index))
                  (mv-nth 0 (abs-alloc fs path new-index))
                  new-index path)
         (abs-fs-fix fs))
  :hints (("goal" :in-theory (enable ctx-app abs-alloc abs-fs-fix)
           :expand (ctx-app fs nil new-index path))))

(defthm abs-alloc-of-abs-fs-fix
  (equal (abs-alloc (abs-fs-fix fs) path new-index)
         (abs-alloc fs path new-index))
  :hints (("Goal" :in-theory (enable abs-alloc))))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies
      (and (abs-fs-p fs) (natp new-index))
      (equal
       (names-at (mv-nth 1 (abs-alloc fs path new-index))
                 relpath)
       (cond
        ((or
          (equal (mv-nth 1 (abs-alloc fs path new-index))
                 fs)
          (not (fat32-filename-list-prefixp path relpath)))
         (names-at fs relpath))
        (t nil))))
     :hints
     (("goal"
       :in-theory
       (e/d
        (abs-top-addrs names-at
                       abs-alloc fat32-filename-list-fix
                       abs-fs-p abs-file-alist-p abs-no-dups-p)
        ((:rewrite abs-fs-p-correctness-1)
         (:rewrite abs-no-dups-p-of-put-assoc-equal)
         (:rewrite subsetp-of-abs-addrs-of-put-assoc-lemma-1)
         (:rewrite abs-fs-p-when-hifat-no-dups-p)
         (:rewrite hifat-find-file-correctness-1-lemma-1)
         (:rewrite consp-of-assoc-of-abs-fs-fix)
         (:rewrite abs-file->contents-when-m1-file-p)
         (:rewrite remove-when-absent)
         (:definition remove-equal)
         (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
         (:rewrite abs-file-alist-p-when-m1-file-alist-p)
         (:rewrite abs-file-alist-p-correctness-1)
         (:rewrite abs-no-dups-p-when-m1-file-alist-p)
         (:rewrite abs-addrs-when-m1-file-alist-p)
         (:rewrite member-of-abs-addrs-when-natp . 2)
         (:rewrite member-of-abs-fs-fix-when-natp)
         (:rewrite abs-file-contents-p-when-m1-file-contents-p)
         (:rewrite fat32-filename-fix-when-fat32-filename-p)))
       :induct (mv (fat32-filename-list-prefixp path relpath)
                   (names-at fs relpath))
       :expand
       ((:free (fs) (names-at fs relpath))
        (abs-alloc fs path new-index)
        (:with
         abs-file-contents-fix-when-abs-file-contents-p
         (abs-file-contents-fix
          (mv-nth
           1
           (abs-alloc
            (abs-file->contents
             (cdr
              (assoc-equal (fat32-filename-fix (car path))
                           fs)))
            (cdr path)
            new-index)))))))))

  (defthm
    names-at-of-abs-alloc-1
    (equal
     (names-at (mv-nth 1 (abs-alloc fs path new-index))
               relpath)
     (if
      (or (equal (mv-nth 1 (abs-alloc fs path new-index))
                 (abs-fs-fix fs))
          (not (fat32-filename-list-prefixp path relpath)))
      (names-at fs relpath)
      nil))
    :hints
    (("goal" :use (:instance lemma (fs (abs-fs-fix fs))
                             (new-index (nfix new-index)))))))

(defthm dist-names-of-abs-alloc-1
  (implies (dist-names fs relpath frame)
           (dist-names (mv-nth 1 (abs-alloc fs path new-index))
                       relpath frame))
  :hints (("goal" :in-theory (enable dist-names))))

(defthm
  subsetp-of-abs-addrs-of-abs-alloc-1
  (implies
   (and (member-equal (nfix new-index) y)
        (subsetp-equal (abs-addrs (abs-fs-fix fs))
                       y))
   (subsetp-equal (abs-addrs (mv-nth 1 (abs-alloc fs path new-index)))
                  y))
  :hints (("goal" :in-theory (enable abs-alloc)
           :expand (abs-addrs (list new-index)))))

(defthm
  names-at-of-abs-alloc-lemma-1
  (implies
   (not
    (equal
     (mv-nth
      1
      (abs-alloc (abs-file->contents
                     (cdr (assoc-equal (fat32-filename-fix (car path))
                                       fs)))
                    (cdr path)
                    new-index))
     (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                           fs)))))
   (not
    (equal
     (put-assoc-equal
      (fat32-filename-fix (car path))
      (abs-file
       (abs-file->d-e
        (cdr (assoc-equal (fat32-filename-fix (car path))
                          fs)))
       (mv-nth 1
               (abs-alloc
                (abs-file->contents
                 (cdr (assoc-equal (fat32-filename-fix (car path))
                                   fs)))
                (cdr path)
                new-index)))
      fs)
     fs)))
  :hints
  (("goal"
    :in-theory (disable (:rewrite put-assoc-equal-without-change . 1))
    :use
    (:instance
     (:rewrite put-assoc-equal-without-change . 1)
     (alist fs)
     (val
      (abs-file
       (abs-file->d-e
        (cdr (assoc-equal (fat32-filename-fix (car path))
                          fs)))
       (mv-nth 1
               (abs-alloc
                (abs-file->contents
                 (cdr (assoc-equal (fat32-filename-fix (car path))
                                   fs)))
                (cdr path)
                new-index))))
     (name (fat32-filename-fix (car path)))))))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies (abs-fs-p fs)
              (equal (names-at (mv-nth 0 (abs-alloc fs path new-index))
                               relpath)
                     (if (equal (mv-nth 1 (abs-alloc fs path new-index))
                                (abs-fs-fix fs))
                         nil
                         (names-at fs (append path relpath)))))
     :hints
     (("goal"
       :in-theory
       (e/d (abs-top-addrs names-at
                           abs-alloc fat32-filename-list-fix
                           abs-fs-p abs-file-alist-p abs-no-dups-p)
            ((:rewrite abs-fs-p-correctness-1)
             (:rewrite abs-no-dups-p-of-put-assoc-equal)
             (:rewrite subsetp-of-abs-addrs-of-put-assoc-lemma-1)
             (:rewrite abs-fs-p-when-hifat-no-dups-p)
             (:rewrite hifat-find-file-correctness-1-lemma-1)
             (:rewrite consp-of-assoc-of-abs-fs-fix)
             (:rewrite abs-file->contents-when-m1-file-p)
             (:rewrite remove-when-absent)
             (:definition remove-equal)
             (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
             (:rewrite abs-file-alist-p-when-m1-file-alist-p)
             (:rewrite abs-file-alist-p-correctness-1)
             (:rewrite abs-no-dups-p-when-m1-file-alist-p)
             (:rewrite abs-addrs-when-m1-file-alist-p)
             (:rewrite member-of-abs-addrs-when-natp . 2)
             (:rewrite member-of-abs-fs-fix-when-natp)
             (:rewrite abs-file-contents-p-when-m1-file-contents-p)
             (:rewrite fat32-filename-fix-when-fat32-filename-p)))
       :induct (abs-alloc fs path new-index)
       :expand
       (:with
        (:rewrite put-assoc-equal-without-change . 1)
        (equal
         (put-assoc-equal
          (fat32-filename-fix (car path))
          (abs-file
           (abs-file->d-e
            (cdr (assoc-equal (fat32-filename-fix (car path))
                              fs)))
           (mv-nth
            1
            (abs-alloc
             (abs-file->contents
              (cdr (assoc-equal (fat32-filename-fix (car path))
                                fs)))
             (cdr path)
             new-index)))
          fs)
         fs))))))

  (defthm
    names-at-of-abs-alloc-2
    (equal (names-at (mv-nth 0 (abs-alloc fs path new-index)) relpath)
           (if (equal (mv-nth 1 (abs-alloc fs path new-index)) (abs-fs-fix fs))
               nil
             (names-at fs (append path relpath))))
    :hints
    (("goal"
      :use
      (:instance
       lemma
       (fs (abs-fs-fix fs)))))))

(defthm
  no-duplicatesp-of-abs-addrs-of-abs-alloc-1
  (implies (no-duplicatesp-equal (abs-addrs (abs-fs-fix fs)))
           (no-duplicatesp-equal
            (abs-addrs (mv-nth 0 (abs-alloc fs path new-index)))))
  :hints (("goal" :in-theory (enable abs-alloc abs-fs-fix abs-addrs))))

(defthm
  addrs-at-of-abs-alloc-1
  (equal (addrs-at (mv-nth 1 (abs-alloc fs path new-index))
                   relpath)
         (cond ((or (equal (mv-nth 1 (abs-alloc fs path new-index))
                           (abs-fs-fix fs))
                    (not (fat32-filename-list-prefixp path relpath)))
                (addrs-at (abs-fs-fix fs) relpath))
               ((fat32-filename-list-equiv relpath path)
                (list (nfix new-index)))
               (t nil)))
  :hints
  (("goal"
    :in-theory (e/d (abs-top-addrs addrs-at abs-fs-fix
                                   abs-alloc fat32-filename-list-fix
                                   fat32-filename-list-equiv
                                   fat32-filename-equiv
                                   abs-fs-p abs-file-alist-p abs-no-dups-p)
                    ((:rewrite abs-no-dups-p-of-put-assoc-equal)
                     (:rewrite subsetp-of-abs-addrs-of-put-assoc-lemma-1)
                     (:rewrite abs-fs-p-when-hifat-no-dups-p)
                     (:rewrite hifat-find-file-correctness-1-lemma-1)
                     (:rewrite consp-of-assoc-of-abs-fs-fix)
                     (:rewrite abs-file->contents-when-m1-file-p)
                     (:rewrite
                      m1-file-alist-p-of-cdr-when-m1-file-alist-p)
                     (:rewrite abs-file-alist-p-correctness-1)
                     (:rewrite abs-no-dups-p-when-m1-file-alist-p)
                     (:rewrite
                      abs-file-alist-p-when-m1-file-alist-p)
                     (:rewrite abs-alloc-correctness-1)
                     (:rewrite
                      abs-addrs-of-remove-assoc-lemma-1)
                     (:rewrite abs-no-dups-p-of-cdr)
                     (:rewrite abs-addrs-of-put-assoc-lemma-1)
                     (:rewrite abs-addrs-when-m1-file-alist-p)
                     (:rewrite
                      abs-fs-fix-of-put-assoc-equal-lemma-2)
                     (:rewrite abs-file-alist-p-of-cdr)))
    :induct (mv (fat32-filename-list-prefixp path relpath)
                (addrs-at fs relpath))
    :expand ((:free (fs) (addrs-at fs relpath))
             (abs-alloc fs path new-index)))))

(defthm ctx-app-ok-of-abs-alloc-1
  (implies
   ;; This clause becomes a test for path's existence...
   (not (equal (mv-nth 1 (abs-alloc fs path new-index))
               (abs-fs-fix fs)))
   (ctx-app-ok (mv-nth 1 (abs-alloc fs path new-index))
               new-index path))
  :hints (("goal" :in-theory (enable ctx-app-ok))))

(defthm
  no-duplicatesp-of-abs-addrs-of-abs-alloc-lemma-1
  (implies
   (not (intersectp-equal y (abs-addrs (abs-fs-fix fs))))
   (not
    (intersectp-equal
     y
     (abs-addrs (remove-assoc-equal (fat32-filename-fix (car path))
                                    (abs-fs-fix fs)))))))

(defthm
  no-duplicatesp-of-abs-addrs-of-abs-alloc-lemma-2
  (implies
   (and (not (member-equal (nfix new-index) y))
        (not (intersectp-equal y (abs-addrs (abs-fs-fix fs)))))
   (not (intersectp-equal
         y
         (abs-addrs (mv-nth 1
                            (abs-alloc fs path new-index))))))
  :hints (("goal" :in-theory (enable abs-alloc abs-addrs)
           :induct (abs-alloc fs path new-index))))

(defthm
  no-duplicatesp-of-abs-addrs-of-abs-alloc-lemma-3
  (implies
   (and (abs-directory-file-p (cdr (assoc-equal name fs)))
        (no-duplicatesp-equal (abs-addrs fs)))
   (not (intersectp-equal
         (abs-addrs (remove-assoc-equal name fs))
         (abs-addrs (abs-file->contents (cdr (assoc-equal name fs)))))))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm
  no-duplicatesp-of-abs-addrs-of-abs-alloc-2
  (implies (and (no-duplicatesp-equal (abs-addrs (abs-fs-fix fs)))
                (not (member-equal (nfix new-index)
                                   (abs-addrs (abs-fs-fix fs)))))
           (no-duplicatesp-equal
            (abs-addrs (mv-nth 1
                               (abs-alloc fs path new-index)))))
  :hints (("goal" :in-theory (e/d
                              (abs-alloc abs-addrs)
                              ((:rewrite abs-addrs-of-remove-assoc)
                               (:rewrite commutativity-of-append-under-set-equiv)
                               (:rewrite intersect-equal-of-cons-left)
                               (:rewrite intersect-with-subset . 11)
                               (:rewrite intersect-with-subset . 12)
                               (:rewrite intersectp-equal-of-atom-left)
                               (:rewrite intersectp-equal-of-atom-right)
                               (:rewrite intersectp-is-commutative)
                               (:rewrite member-of-cons)
                               (:rewrite member-when-atom)
                               (:rewrite set-difference$-when-not-intersectp)
                               (:rewrite subsetp-car-member)
                               (:rewrite subsetp-member . 3)
                               (:rewrite subsetp-of-cdr)
                               (:rewrite true-list-fix-when-true-listp)
                               (:type-prescription abs-addrs)
                               (:type-prescription abs-alloc)
                               (:type-prescription abs-fs-fix)
                               (:type-prescription set-difference-equal)))
           :induct (abs-alloc fs path new-index))))

(defthmd hifat-no-dups-p-of-abs-alloc
  (implies (and (hifat-no-dups-p fs)
                (m1-file-alist-p fs))
           (hifat-no-dups-p (mv-nth 0 (abs-alloc fs path new-index))))
  :hints (("goal" :in-theory (enable hifat-no-dups-p abs-alloc
                                     abs-fs-p-when-hifat-no-dups-p))))
