(in-package "ACL2")

;  lofat.lisp                                           Mihir Mehta

; This is a stobj model of the FAT32 filesystem.

(include-book "lofat/lofat-remove-file")
(include-book "lofat/lofat-place-file")

(local (in-theory (disable nth make-list-ac-removal last
                           make-list-ac member-equal)))

(defthm
  lofat-mkdir-refinement-lemma-14
  (equal
   (lofat-place-file fat32$c root-d-e path
                     (list (cons 'd-e d-e1)
                           (cons 'contents contents)))
   (lofat-place-file fat32$c root-d-e path
                     (list (cons 'd-e d-e2)
                           (cons 'contents contents))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lofat-place-file lofat-place-file-helper
                       lofat-regular-file-p
                       lofat-directory-file-p
                       lofat-file-p lofat-file->contents
                       m1-file-hifat-file-alist-fix m1-file)
     (m1-file-hifat-file-alist-fix-normalisation
      abs-mkdir-correctness-lemma-36
      (:rewrite lofat-file-contents-fix-when-lofat-file-contents-p)
      (:rewrite fat32-filename-p-correctness-1)
      (:rewrite lofat-file-contents-p-when-stringp)
      (:linear nth-when-d-e-p)
      (:linear len-of-explode-when-m1-file-contents-p-1)
      (:rewrite lofat-file-fix-when-lofat-file-p)
      (:rewrite lofat-file-contents-p-when-d-e-listp)
      (:rewrite nth-of-nats=>chars)
      (:rewrite m1-file-contents-p-when-stringp)
      (:type-prescription hifat-bounded-file-alist-p)
      (:rewrite stringp-when-nonempty-stringp)))))
  :rule-classes
  ((:congruence
    :corollary
    (implies
     (true-equiv d-e1 d-e2)
     (equal
      (lofat-place-file fat32$c root-d-e path
                        (list (cons 'd-e d-e1)
                              (cons 'contents contents)))
      (lofat-place-file fat32$c root-d-e path
                        (list (cons 'd-e d-e2)
                              (cons 'contents contents))))))))

(defthm
  lofat-mkdir-refinement-lemma-15
  (implies
   (not (equal d-e (d-e-fix nil)))
   (equal
    (mv-nth 1
            (lofat-place-file fat32$c root-d-e path
                              (list (cons 'd-e d-e)
                                    (cons 'contents contents))))
    (mv-nth 1
            (lofat-place-file fat32$c root-d-e path
                              (list (cons 'd-e (d-e-fix nil))
                                    (cons 'contents contents))))))
  :hints (("goal" :do-not-induct t
           :in-theory (disable lofat-mkdir-refinement-lemma-14)
           :use (:instance lofat-mkdir-refinement-lemma-14
                           (d-e1 d-e)
                           (d-e2 (d-e-fix nil))))))

(defthm
  lofat-mkdir-refinement-lemma-1
  (implies
   (and
    (good-root-d-e-p (pseudo-root-d-e fat32$c)
                     fat32$c)
    (fat32-filename-list-p path)
    (equal (mv-nth 1 (lofat-to-hifat fat32$c))
           0)
    (lofat-file-p file)
    (or (stringp (lofat-file->contents file))
        (equal (lofat-file->contents file) nil))
    (not (equal (mv-nth 1
                        (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                          path file))
                28))
    (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
       (max-entry-count fat32$c)))
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                 path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth 0
                  (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                    path file))
          (pseudo-root-d-e fat32$c))))
       (max-entry-count fat32$c)))
     0)
    (hifat-equiv
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                 path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth 0
                  (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                    path file))
          (pseudo-root-d-e fat32$c))))
       (max-entry-count fat32$c)))
     (mv-nth 0
             (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                               path
                               (m1-file d-e (lofat-file->contents file)))))
    (equal
     (mv-nth 1
             (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                               path
                               (m1-file d-e (lofat-file->contents file))))
     (mv-nth 1
             (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                               path file)))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (lofat-to-hifat root-d-e-list)
                           (lofat-place-file-correctness-1))
           :use (:instance lofat-place-file-correctness-1
                           (entry-limit (max-entry-count fat32$c))
                           (root-d-e (pseudo-root-d-e fat32$c))))))

(encapsulate
  ()

  (local
   (defthm
     lemma-1
     (implies (or (and (stringp (m1-file->contents file))
                       (<= (len (make-clusters (m1-file->contents file)
                                               (cluster-size fat32$c)))
                           (count-free-clusters (effective-fat fat32$c))))
                  (and (equal (m1-file->contents file) nil)
                       (<= 1
                           (count-free-clusters (effective-fat fat32$c)))))
              (lofat-file-contents-p (m1-file->contents file)))
     :hints
     (("goal"
       :do-not-induct t
       :in-theory (disable lofat-mkdir-refinement-lemma-1)
       :use
       (:instance lofat-mkdir-refinement-lemma-1
                  (file (make-lofat-file :d-e nil
                                         :contents (m1-file->contents file)))
                  (d-e (m1-file->d-e file)))))))

  (defthm
    lofat-mkdir-refinement-lemma-2
    (implies
     (and
      (good-root-d-e-p (pseudo-root-d-e fat32$c)
                       fat32$c)
      (fat32-filename-list-p path)
      (equal (mv-nth 1 (lofat-to-hifat fat32$c))
             0)
      (or (stringp (m1-file->contents file))
          (equal (m1-file->contents file) nil))
      (not
       (equal
        (mv-nth 1
                (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                  path
                                  (lofat-file nil (m1-file->contents file))))
        28))
      (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
         (max-entry-count fat32$c)))
     (equal
      (mv-nth 1
              (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                                path file))
      (mv-nth 1
              (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                path
                                (lofat-file nil (m1-file->contents file))))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (disable lofat-mkdir-refinement-lemma-1
                          (:congruence hifat-pwrite-correctness-lemma-1)
                          (:congruence m1-file-d-e-equiv-congruence-on-d-e)
                          (:rewrite m1-file->d-e-under-true-equiv)
                          (:rewrite m1-file-of-d-e-fix-d-e-normalize-const)
                          (:rewrite-quoted-constant true-fix-under-true-equiv))
      :use
      (:instance lofat-mkdir-refinement-lemma-1
                 (file (make-lofat-file :d-e nil
                                        :contents (m1-file->contents file)))
                 (d-e (m1-file->d-e file)))))))

(defthm
  lofat-unlink-refinement-lemma-4
  (implies
   (and (lofat-fs-p fat32$c)
        (useful-d-e-list-p d-e-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c
                                              d-e-list entry-limit))
               0))
   (equal
    (lofat-regular-file-p
     (mv-nth 0
             (lofat-find-file fat32$c d-e-list path)))
    (m1-regular-file-p
     (mv-nth 0
             (hifat-find-file
              (mv-nth 0
                      (lofat-to-hifat-helper fat32$c
                                             d-e-list entry-limit))
              path)))))
  :hints
  (("goal" :induct (lofat-find-file fat32$c d-e-list path)
    :in-theory (enable lofat-find-file hifat-find-file))))

(defthm
  lofat-pread-refinement-lemma-1
  (implies
   (and
    (useful-d-e-list-p d-e-list)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c
                                          d-e-list entry-limit))
           0)
    (<=
     (+ 2 (count-of-clusters fat32$c))
     (d-e-first-cluster (mv-nth 0
                                    (find-d-e d-e-list filename)))))
   (not (d-e-directory-p (mv-nth 0
                                     (find-d-e d-e-list filename)))))
  :hints
  (("goal"
    :in-theory
    (e/d (lofat-to-hifat-helper find-d-e useful-d-e-list-p)
         ((:definition no-duplicatesp-equal)
          (:rewrite useful-d-e-list-p-of-cdr)
          (:definition member-equal)
          (:rewrite take-of-len-free)
          (:definition take)
          (:definition assoc-equal))))))

(encapsulate
  ()

  (local
   (defthm
     lemma-1
     (implies
      (and (lofat-fs-p fat32$c)
           (equal (mv-nth 1 (lofat-to-hifat fat32$c))
                  0)
           (lofat-directory-file-p
            (mv-nth 0
                    (lofat-find-file fat32$c
                                     (mv-nth 0 (root-d-e-list fat32$c))
                                     path))))
      (equal
       (hifat-find-file (mv-nth 0 (lofat-to-hifat fat32$c))
                        path)
       (mv
        (make-m1-file
         :d-e (lofat-file->d-e
               (mv-nth 0
                       (lofat-find-file fat32$c
                                        (mv-nth 0 (root-d-e-list fat32$c))
                                        path)))
         :contents
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (lofat-file->contents
            (mv-nth 0
                    (lofat-find-file fat32$c
                                     (mv-nth 0 (root-d-e-list fat32$c))
                                     path)))
           (max-entry-count fat32$c))))
        (mv-nth 1
                (lofat-find-file fat32$c
                                 (mv-nth 0 (root-d-e-list fat32$c))
                                 path)))))
     :hints
     (("goal" :in-theory (e/d (lofat-to-hifat)
                              (lofat-find-file-correctness-2))
       :use ((:instance lofat-find-file-correctness-2
                        (d-e-list (mv-nth 0 (root-d-e-list fat32$c)))
                        (entry-limit (max-entry-count fat32$c)))
             (:instance (:rewrite hifat-find-file-correctness-2)
                        (path path)
                        (fs (mv-nth 0 (lofat-to-hifat fat32$c)))))
       :do-not-induct t))))

  (local
   (defthm
     lemma-2
     (implies
      (and (lofat-fs-p fat32$c)
           (equal (mv-nth 1 (lofat-to-hifat fat32$c))
                  0)
           (lofat-regular-file-p
            (mv-nth 0
                    (lofat-find-file fat32$c
                                     (mv-nth 0 (root-d-e-list fat32$c))
                                     path))))
      (equal
       (hifat-find-file (mv-nth 0 (lofat-to-hifat fat32$c))
                        path)
       (mv
        (make-m1-file
         :contents
         (lofat-file->contents
          (mv-nth 0
                  (lofat-find-file fat32$c
                                   (mv-nth 0 (root-d-e-list fat32$c))
                                   path)))
         :d-e (lofat-file->d-e
               (mv-nth 0
                       (lofat-find-file fat32$c
                                        (mv-nth 0 (root-d-e-list fat32$c))
                                        path))))
        (mv-nth 1
                (lofat-find-file fat32$c
                                 (mv-nth 0 (root-d-e-list fat32$c))
                                 path)))))
     :hints
     (("goal" :do-not-induct t
       :in-theory (e/d (lofat-to-hifat)
                       (lofat-find-file-correctness-1))
       :use ((:instance lofat-find-file-correctness-1
                        (d-e-list (mv-nth 0 (root-d-e-list fat32$c)))
                        (entry-limit (max-entry-count fat32$c)))
             (:instance (:rewrite hifat-find-file-correctness-2)
                        (path path)
                        (fs (mv-nth 0 (lofat-to-hifat fat32$c)))))))))

  (defthm
    lofat-mkdir-refinement-lemma-3
   (implies
    (and (lofat-fs-p fat32$c)
         (equal (mv-nth 1 (lofat-to-hifat fat32$c))
                0))
    (equal
     (hifat-find-file (mv-nth 0 (lofat-to-hifat fat32$c))
                      path)
     (if
         (lofat-directory-file-p
          (mv-nth 0
                  (lofat-find-file fat32$c
                                   (mv-nth 0 (root-d-e-list fat32$c))
                                   path)))
         (mv
          (make-m1-file
           :d-e (lofat-file->d-e
                 (mv-nth 0
                         (lofat-find-file fat32$c
                                          (mv-nth 0 (root-d-e-list fat32$c))
                                          path)))
           :contents
           (mv-nth
            0
            (lofat-to-hifat-helper
             fat32$c
             (lofat-file->contents
              (mv-nth 0
                      (lofat-find-file fat32$c
                                       (mv-nth 0 (root-d-e-list fat32$c))
                                       path)))
             (max-entry-count fat32$c))))
          (mv-nth 1
                  (lofat-find-file fat32$c
                                   (mv-nth 0 (root-d-e-list fat32$c))
                                   path)))
       (mv
        (make-m1-file
         :contents
         (lofat-file->contents
          (mv-nth 0
                  (lofat-find-file fat32$c
                                   (mv-nth 0 (root-d-e-list fat32$c))
                                   path)))
         :d-e (lofat-file->d-e
               (mv-nth 0
                       (lofat-find-file fat32$c
                                        (mv-nth 0 (root-d-e-list fat32$c))
                                        path))))
        (mv-nth 1
                (lofat-find-file fat32$c
                                 (mv-nth 0 (root-d-e-list fat32$c))
                                 path))))))
   :hints (("goal" :do-not-induct t
            :in-theory (disable
                        lemma-1
                        lemma-2)
            :use
            (lemma-1
             lemma-2))))

  (defthm
    lofat-mkdir-refinement-lemma-5
    (implies
     (or
      (lofat-directory-file-p (mv-nth 0
                                      (lofat-find-file fat32$c d-e-list path)))
      (not
       (lofat-regular-file-p (mv-nth 0
                                     (lofat-find-file fat32$c d-e-list path)))))
     (useful-d-e-list-p
      (lofat-file->contents (mv-nth 0
                                    (lofat-find-file fat32$c d-e-list path)))))
    :hints (("goal" :in-theory (enable lofat-find-file))))

  ;; This will probably be useful later.
  (defthm
    lofat-mkdir-refinement-lemma-4
    (implies
     (and (lofat-fs-p fat32$c)
          (equal (mv-nth 1 (lofat-to-hifat fat32$c))
                 0))
     (iff (m1-regular-file-p
           (mv-nth 0
                   (hifat-find-file (mv-nth 0 (lofat-to-hifat fat32$c))
                                    path)))
          (lofat-regular-file-p
           (mv-nth 0
                   (lofat-find-file fat32$c
                                    (mv-nth 0 (root-d-e-list fat32$c))
                                    path)))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (disable lemma-1
                          lemma-2)
      :use (lemma-1 lemma-2)))
    :rule-classes
    ((:rewrite
      :corollary
      (implies
       (and (lofat-fs-p fat32$c)
            (equal (mv-nth 1 (lofat-to-hifat fat32$c))
                   0))
       (equal (m1-regular-file-p
               (mv-nth 0
                       (hifat-find-file (mv-nth 0 (lofat-to-hifat fat32$c))
                                        path)))
              (lofat-regular-file-p
               (mv-nth 0
                       (lofat-find-file fat32$c
                                        (mv-nth 0 (root-d-e-list fat32$c))
                                        path))))))
     (:rewrite
      :corollary
      (implies
       (and (lofat-fs-p fat32$c)
            (equal (mv-nth 1 (lofat-to-hifat fat32$c))
                   0))
       (equal (m1-directory-file-p
               (mv-nth 0
                       (hifat-find-file (mv-nth 0 (lofat-to-hifat fat32$c))
                                        path)))
              (lofat-directory-file-p
               (mv-nth 0
                       (lofat-find-file fat32$c
                                        (mv-nth 0 (root-d-e-list fat32$c))
                                        path)))))))))

(defthm
  lofat-mkdir-refinement-lemma-6
  (implies (and (equal (lofat-file->contents file1)
                       (lofat-file->contents file2))
                (lofat-file-p file1)
                (lofat-file-p file2))
           (equal (mv-nth 1
                          (lofat-place-file fat32$c root-d-e path file2))
                  (mv-nth 1
                          (lofat-place-file fat32$c root-d-e path file1))))
  :hints (("goal" :in-theory (enable lofat-place-file lofat-place-file-helper
                                     lofat-regular-file-p
                                     lofat-directory-file-p)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (and (equal (mv-nth 1
                                 (lofat-place-file fat32$c root-d-e path file1))
                         0)
                  (equal (lofat-file->contents file1)
                         (lofat-file->contents file2))
                  (lofat-file-p file1)
                  (lofat-file-p file2))
             (equal (mv-nth 1
                            (lofat-place-file fat32$c root-d-e path file2))
                    0)))))

(defthm
  lofat-mkdir-refinement-lemma-7
  (implies
   (and (fat32-filename-list-p path)
        (consp (cdr path))
        (equal (mv-nth 1
                       (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                         path file))
               0))
   (d-e-directory-p
    (mv-nth
     '0
     (find-d-e
      (make-d-e-list
       (mv-nth '0
               (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
      (car path)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (lofat-to-hifat root-d-e-list
                                    lofat-place-file-correctness-lemma-25
                                    d-e-cc-of-lofat-place-file-coincident-1
                                    lofat-place-file hifat-place-file)
                    (lofat-place-file-correctness-1)))))

(encapsulate
  ()

  (local
   (in-theory
    (e/d (lofat-to-hifat root-d-e-list
                         d-e-cc-of-lofat-place-file-coincident-1
                         hifat-place-file)
         (lofat-place-file-correctness-1
          (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                    . 5)))))

  (set-default-hints '(("Goal" :do-not-induct t)))

  (defthm
    lofat-pwrite-refinement-lemma-30
    (implies
     (and
      (<=
       (len (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))))
       65534)
      (good-root-d-e-p (pseudo-root-d-e fat32$c)
                       fat32$c)
      (not-intersectp-list
       (mv-nth 0
               (d-e-cc fat32$c (pseudo-root-d-e fat32$c)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (max-entry-count fat32$c))))
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (max-entry-count fat32$c)))
       0))
     (<=
      (len
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents
                 (mv-nth 0
                         (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                           path file))
                 (pseudo-root-d-e fat32$c)))))
      65534))
    :hints
    (("goal" :do-not-induct t
      :cases ((consp (cdr path)))))
    :rule-classes :linear)

  (defthm
    lofat-pwrite-refinement-lemma-32
    (implies
     (and
      (good-root-d-e-p (pseudo-root-d-e fat32$c)
                       fat32$c)
      (fat32-filename-list-p path)
      (lofat-file-p file)
      (equal (mv-nth 1
                     (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                       path file))
             0)
      (equal
       (mv-nth
        1
        (find-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (car path)))
       0)
      (<
       (d-e-first-cluster
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path))))
       2)
      (< 0
         (len (explode (lofat-file->contents file)))))
     (>=
      (+ (count-free-clusters (effective-fat fat32$c))
         (- (len (make-clusters (lofat-file->contents file)
                                (cluster-size fat32$c))))
         (len (mv-nth 0
                      (d-e-cc fat32$c (pseudo-root-d-e fat32$c)))))
      (len
       (make-clusters
        (nats=>string
         (insert-d-e
          (string=>nats
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (d-e-set-first-cluster-file-size
           (mv-nth
            0
            (find-d-e
             (make-d-e-list
              (mv-nth 0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
             (car path)))
           (nth 0
                (find-n-free-clusters (effective-fat fat32$c)
                                      1))
           (len (explode (lofat-file->contents file))))))
        (cluster-size fat32$c)))))
    :hints (("goal" :cases ((consp (cdr path)))))
    :rule-classes :linear)

  (defthm
    lofat-pwrite-refinement-lemma-31
    (implies
     (and
      (good-root-d-e-p (pseudo-root-d-e fat32$c)
                       fat32$c)
      (fat32-filename-list-p path)
      (not-intersectp-list
       (mv-nth 0
               (d-e-cc fat32$c (pseudo-root-d-e fat32$c)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (max-entry-count fat32$c))))
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (max-entry-count fat32$c)))
       0)
      (lofat-file-p file)
      (not (lofat-directory-file-p file))
      (not
       (d-e-directory-p
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path)))))
      (consp path)
      (equal
       (mv-nth
        1
        (find-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (car path)))
       0)
      (<=
       2
       (d-e-first-cluster
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path)))))
      (<
       (d-e-first-cluster
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path))))
       (+ 2 (count-of-clusters fat32$c)))
      (<
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32$c)
          (mv-nth
           0
           (d-e-cc
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))))
          (make-list-ac
           (len
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path))))))
           0 nil))
         1))
       (+ 2 (count-of-clusters fat32$c)))
      (<=
       (+ -1
          (len (make-clusters (lofat-file->contents file)
                              (cluster-size fat32$c))))
       (+
        -1
        (count-free-clusters (effective-fat fat32$c))
        (len
         (mv-nth
          0
          (d-e-cc
           fat32$c
           (mv-nth
            0
            (find-d-e
             (make-d-e-list
              (mv-nth 0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
             (car path))))))))
      (< 0
         (len (explode (lofat-file->contents file)))))
     (not-intersectp-list
      (mv-nth 0
              (d-e-cc fat32$c (pseudo-root-d-e fat32$c)))
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth
         0
         (update-dir-contents
          (mv-nth
           0
           (place-contents
            (update-fati
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path)))))
                (make-list-ac
                 (len
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path))))))
                 0 nil))
               1))
             (fat32-update-lower-28
              (fati
               (nth
                0
                (find-n-free-clusters
                 (set-indices-in-fa-table
                  (effective-fat fat32$c)
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path)))))
                  (make-list-ac
                   (len
                    (mv-nth
                     0
                     (d-e-cc
                      fat32$c
                      (mv-nth
                       0
                       (find-d-e
                        (make-d-e-list
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c (pseudo-root-d-e fat32$c))))
                        (car path))))))
                   0 nil))
                 1))
               fat32$c)
              268435455)
             (mv-nth
              0
              (clear-cc
               fat32$c
               (d-e-first-cluster
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path))))
               (d-e-file-size
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))))
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))
            (lofat-file->contents file)
            (len (explode (lofat-file->contents file)))
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32$c)
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path)))))
               (make-list-ac
                (len
                 (mv-nth
                  0
                  (d-e-cc
                   fat32$c
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list
                      (mv-nth
                       0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                     (car path))))))
                0 nil))
              1))))
          (d-e-first-cluster (pseudo-root-d-e fat32$c))
          (nats=>string
           (insert-d-e
            (string=>nats
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (d-e-set-first-cluster-file-size
             (mv-nth
              0
              (find-d-e
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
               (car path)))
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path)))))
                (make-list-ac
                 (len
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path))))))
                 0 nil))
               1))
             (len (explode (lofat-file->contents file))))))))
        (place-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (d-e-set-first-cluster-file-size
          (mv-nth
           0
           (find-d-e
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (car path)))
          (nth
           0
           (find-n-free-clusters
            (set-indices-in-fa-table
             (effective-fat fat32$c)
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth
                   0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                 (car path)))))
             (make-list-ac
              (len
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path))))))
              0 nil))
            1))
          (len (explode (lofat-file->contents file)))))
        (max-entry-count fat32$c)))))
    :hints
    (("goal"
      :in-theory
      (e/d (update-dir-contents-correctness-1 place-contents-correctness-1)
           ((:rewrite place-contents-expansion-2)))
      :use
      (:instance
       (:rewrite place-contents-expansion-2)
       (first-cluster
        (nth
         0
         (find-n-free-clusters
          (set-indices-in-fa-table
           (effective-fat fat32$c)
           (mv-nth
            0
            (d-e-cc
             fat32$c
             (mv-nth
              0
              (find-d-e
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
               (car path)))))
           (make-list-ac
            (len
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth 0
                          (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                 (car path))))))
            0 nil))
          1)))
       (file-length (len (explode (lofat-file->contents file))))
       (contents (lofat-file->contents file))
       (d-e
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path))))
       (fat32$c
        (update-fati
         (nth
          0
          (find-n-free-clusters
           (set-indices-in-fa-table
            (effective-fat fat32$c)
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path)))))
            (make-list-ac
             (len
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth 0
                           (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path))))))
             0 nil))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (set-indices-in-fa-table
              (effective-fat fat32$c)
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth 0
                           (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))
              (make-list-ac
               (len
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path))))))
               0 nil))
             1))
           fat32$c)
          268435455)
         (mv-nth
          0
          (clear-cc
           fat32$c
           (d-e-first-cluster
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path))))
           (d-e-file-size
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path))))))))))))

  (defthm
    lofat-pwrite-refinement-lemma-33
    (implies
     (and
      (good-root-d-e-p (pseudo-root-d-e fat32$c)
                       fat32$c)
      (fat32-filename-list-p path)
      (not-intersectp-list
       (mv-nth 0
               (d-e-cc fat32$c (pseudo-root-d-e fat32$c)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (max-entry-count fat32$c))))
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (max-entry-count fat32$c)))
       0)
      (lofat-file-p file)
      (not (lofat-directory-file-p file))
      (not
       (d-e-directory-p
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path)))))
      (consp path)
      (equal
       (mv-nth
        1
        (find-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (car path)))
       0)
      (<=
       2
       (d-e-first-cluster
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path)))))
      (<
       (d-e-first-cluster
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path))))
       (+ 2 (count-of-clusters fat32$c)))
      (<
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32$c)
          (mv-nth
           0
           (d-e-cc
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))))
          (make-list-ac
           (len
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path))))))
           0 nil))
         1))
       (+ 2 (count-of-clusters fat32$c)))
      (<=
       (+ -1
          (len (make-clusters (lofat-file->contents file)
                              (cluster-size fat32$c))))
       (+
        -1
        (count-free-clusters (effective-fat fat32$c))
        (len
         (mv-nth
          0
          (d-e-cc
           fat32$c
           (mv-nth
            0
            (find-d-e
             (make-d-e-list
              (mv-nth 0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
             (car path))))))))
      (< 0
         (len (explode (lofat-file->contents file)))))
     (equal
      (mv-nth
       3
       (lofat-to-hifat-helper
        (mv-nth
         0
         (update-dir-contents
          (mv-nth
           0
           (place-contents
            (update-fati
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path)))))
                (make-list-ac
                 (len
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path))))))
                 0 nil))
               1))
             (fat32-update-lower-28
              (fati
               (nth
                0
                (find-n-free-clusters
                 (set-indices-in-fa-table
                  (effective-fat fat32$c)
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path)))))
                  (make-list-ac
                   (len
                    (mv-nth
                     0
                     (d-e-cc
                      fat32$c
                      (mv-nth
                       0
                       (find-d-e
                        (make-d-e-list
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c (pseudo-root-d-e fat32$c))))
                        (car path))))))
                   0 nil))
                 1))
               fat32$c)
              268435455)
             (mv-nth
              0
              (clear-cc
               fat32$c
               (d-e-first-cluster
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path))))
               (d-e-file-size
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))))
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))
            (lofat-file->contents file)
            (len (explode (lofat-file->contents file)))
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32$c)
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path)))))
               (make-list-ac
                (len
                 (mv-nth
                  0
                  (d-e-cc
                   fat32$c
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list
                      (mv-nth
                       0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                     (car path))))))
                0 nil))
              1))))
          (d-e-first-cluster (pseudo-root-d-e fat32$c))
          (nats=>string
           (insert-d-e
            (string=>nats
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (d-e-set-first-cluster-file-size
             (mv-nth
              0
              (find-d-e
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
               (car path)))
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path)))))
                (make-list-ac
                 (len
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path))))))
                 0 nil))
               1))
             (len (explode (lofat-file->contents file))))))))
        (place-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (d-e-set-first-cluster-file-size
          (mv-nth
           0
           (find-d-e
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (car path)))
          (nth
           0
           (find-n-free-clusters
            (set-indices-in-fa-table
             (effective-fat fat32$c)
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth
                   0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                 (car path)))))
             (make-list-ac
              (len
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path))))))
              0 nil))
            1))
          (len (explode (lofat-file->contents file)))))
        (max-entry-count fat32$c)))
      0))
    :hints
    (("goal"
      :in-theory
      (e/d (update-dir-contents-correctness-1 place-contents-correctness-1)
           ((:rewrite place-contents-expansion-2)))
      :use
      (:instance
       (:rewrite place-contents-expansion-2)
       (first-cluster
        (nth
         0
         (find-n-free-clusters
          (set-indices-in-fa-table
           (effective-fat fat32$c)
           (mv-nth
            0
            (d-e-cc
             fat32$c
             (mv-nth
              0
              (find-d-e
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
               (car path)))))
           (make-list-ac
            (len
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth 0
                          (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                 (car path))))))
            0 nil))
          1)))
       (file-length (len (explode (lofat-file->contents file))))
       (contents (lofat-file->contents file))
       (d-e
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path))))
       (fat32$c
        (update-fati
         (nth
          0
          (find-n-free-clusters
           (set-indices-in-fa-table
            (effective-fat fat32$c)
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path)))))
            (make-list-ac
             (len
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth 0
                           (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path))))))
             0 nil))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (set-indices-in-fa-table
              (effective-fat fat32$c)
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth 0
                           (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))
              (make-list-ac
               (len
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path))))))
               0 nil))
             1))
           fat32$c)
          268435455)
         (mv-nth
          0
          (clear-cc
           fat32$c
           (d-e-first-cluster
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path))))
           (d-e-file-size
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path))))))))))))

  (defthm
    lofat-pwrite-refinement-lemma-35
    (implies
     (and
      (good-root-d-e-p (pseudo-root-d-e fat32$c)
                       fat32$c)
      (fat32-filename-list-p path)
      (not-intersectp-list
       (mv-nth 0
               (d-e-cc fat32$c (pseudo-root-d-e fat32$c)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (max-entry-count fat32$c))))
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (max-entry-count fat32$c)))
       0)
      (lofat-file-p file)
      (not (lofat-directory-file-p file))
      (consp path)
      (equal
       (mv-nth
        1
        (find-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (car path)))
       0)
      (not
       (d-e-directory-p
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path)))))
      (<=
       2
       (d-e-first-cluster
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path)))))
      (<
       (d-e-first-cluster
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path))))
       (+ 2 (count-of-clusters fat32$c)))
      (<
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32$c)
          (mv-nth
           0
           (d-e-cc
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))))
          (make-list-ac
           (len
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path))))))
           0 nil))
         1))
       (+ 2 (count-of-clusters fat32$c)))
      (<=
       (+ -1
          (len (make-clusters (lofat-file->contents file)
                              (cluster-size fat32$c))))
       (+
        -1
        (count-free-clusters (effective-fat fat32$c))
        (len
         (mv-nth
          0
          (d-e-cc
           fat32$c
           (mv-nth
            0
            (find-d-e
             (make-d-e-list
              (mv-nth 0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
             (car path))))))))
      (< 0
         (len (explode (lofat-file->contents file))))
      (member-equal
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32$c)
          (mv-nth
           0
           (d-e-cc
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))))
          (make-list-ac
           (len
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path))))))
           0 nil))
         1))
       (mv-nth
        0
        (d-e-cc
         fat32$c
         (mv-nth
          0
          (find-d-e
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
           (car path)))))))
     (not-intersectp-list
      (find-n-free-clusters
       (update-nth
        (d-e-first-cluster (pseudo-root-d-e fat32$c))
        (fat32-update-lower-28
         (fati
          (d-e-first-cluster (pseudo-root-d-e fat32$c))
          (mv-nth
           0
           (place-contents
            (update-fati
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path)))))
                (make-list-ac
                 (len
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path))))))
                 0 nil))
               1))
             (fat32-update-lower-28
              (fati
               (nth
                0
                (find-n-free-clusters
                 (set-indices-in-fa-table
                  (effective-fat fat32$c)
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path)))))
                  (make-list-ac
                   (len
                    (mv-nth
                     0
                     (d-e-cc
                      fat32$c
                      (mv-nth
                       0
                       (find-d-e
                        (make-d-e-list
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c (pseudo-root-d-e fat32$c))))
                        (car path))))))
                   0 nil))
                 1))
               fat32$c)
              268435455)
             (mv-nth
              0
              (clear-cc
               fat32$c
               (d-e-first-cluster
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path))))
               (d-e-file-size
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))))
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))
            (lofat-file->contents file)
            (len (explode (lofat-file->contents file)))
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32$c)
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path)))))
               (make-list-ac
                (len
                 (mv-nth
                  0
                  (d-e-cc
                   fat32$c
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list
                      (mv-nth
                       0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                     (car path))))))
                0 nil))
              1)))))
         268435455)
        (set-indices-in-fa-table
         (effective-fat
          (mv-nth
           0
           (place-contents
            (update-fati
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path)))))
                (make-list-ac
                 (len
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path))))))
                 0 nil))
               1))
             (fat32-update-lower-28
              (fati
               (nth
                0
                (find-n-free-clusters
                 (set-indices-in-fa-table
                  (effective-fat fat32$c)
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path)))))
                  (make-list-ac
                   (len
                    (mv-nth
                     0
                     (d-e-cc
                      fat32$c
                      (mv-nth
                       0
                       (find-d-e
                        (make-d-e-list
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c (pseudo-root-d-e fat32$c))))
                        (car path))))))
                   0 nil))
                 1))
               fat32$c)
              268435455)
             (mv-nth
              0
              (clear-cc
               fat32$c
               (d-e-first-cluster
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path))))
               (d-e-file-size
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))))
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))
            (lofat-file->contents file)
            (len (explode (lofat-file->contents file)))
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32$c)
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path)))))
               (make-list-ac
                (len
                 (mv-nth
                  0
                  (d-e-cc
                   fat32$c
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list
                      (mv-nth
                       0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                     (car path))))))
                0 nil))
              1)))))
         (mv-nth 0
                 (d-e-cc fat32$c (pseudo-root-d-e fat32$c)))
         (make-list-ac
          (len (mv-nth 0
                       (d-e-cc fat32$c (pseudo-root-d-e fat32$c))))
          0 nil)))
       (+
        -1
        (len
         (make-clusters
          (implode
           (nats=>chars
            (insert-d-e
             (string=>nats
              (mv-nth 0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
             (d-e-set-first-cluster-file-size
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path)))
              (nth
               0
               (find-n-free-clusters
                (set-indices-in-fa-table
                 (effective-fat fat32$c)
                 (mv-nth
                  0
                  (d-e-cc
                   fat32$c
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list
                      (mv-nth
                       0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                     (car path)))))
                 (make-list-ac
                  (len
                   (mv-nth
                    0
                    (d-e-cc
                     fat32$c
                     (mv-nth
                      0
                      (find-d-e
                       (make-d-e-list
                        (mv-nth
                         0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                       (car path))))))
                  0 nil))
                1))
              (len (explode (lofat-file->contents file)))))))
          (cluster-size fat32$c)))))
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth
         0
         (update-dir-contents
          (mv-nth
           0
           (place-contents
            (update-fati
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path)))))
                (make-list-ac
                 (len
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path))))))
                 0 nil))
               1))
             (fat32-update-lower-28
              (fati
               (nth
                0
                (find-n-free-clusters
                 (set-indices-in-fa-table
                  (effective-fat fat32$c)
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path)))))
                  (make-list-ac
                   (len
                    (mv-nth
                     0
                     (d-e-cc
                      fat32$c
                      (mv-nth
                       0
                       (find-d-e
                        (make-d-e-list
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c (pseudo-root-d-e fat32$c))))
                        (car path))))))
                   0 nil))
                 1))
               fat32$c)
              268435455)
             (mv-nth
              0
              (clear-cc
               fat32$c
               (d-e-first-cluster
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path))))
               (d-e-file-size
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))))
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))
            (lofat-file->contents file)
            (len (explode (lofat-file->contents file)))
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32$c)
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path)))))
               (make-list-ac
                (len
                 (mv-nth
                  0
                  (d-e-cc
                   fat32$c
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list
                      (mv-nth
                       0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                     (car path))))))
                0 nil))
              1))))
          (d-e-first-cluster (pseudo-root-d-e fat32$c))
          (nats=>string
           (insert-d-e
            (string=>nats
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (d-e-set-first-cluster-file-size
             (mv-nth
              0
              (find-d-e
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
               (car path)))
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path)))))
                (make-list-ac
                 (len
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path))))))
                 0 nil))
               1))
             (len (explode (lofat-file->contents file))))))))
        (place-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (d-e-set-first-cluster-file-size
          (mv-nth
           0
           (find-d-e
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (car path)))
          (nth
           0
           (find-n-free-clusters
            (set-indices-in-fa-table
             (effective-fat fat32$c)
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth
                   0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                 (car path)))))
             (make-list-ac
              (len
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path))))))
              0 nil))
            1))
          (len (explode (lofat-file->contents file)))))
        (max-entry-count fat32$c)))))
    :hints
    (("goal"
      :in-theory (disable (:rewrite place-contents-expansion-2))
      :use
      (:instance
       (:rewrite place-contents-expansion-2)
       (first-cluster
        (nth
         0
         (find-n-free-clusters
          (set-indices-in-fa-table
           (effective-fat fat32$c)
           (mv-nth
            0
            (d-e-cc
             fat32$c
             (mv-nth
              0
              (find-d-e
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
               (car path)))))
           (make-list-ac
            (len
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth 0
                          (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                 (car path))))))
            0 nil))
          1)))
       (file-length (len (explode (lofat-file->contents file))))
       (contents (lofat-file->contents file))
       (d-e
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path))))
       (fat32$c
        (update-fati
         (nth
          0
          (find-n-free-clusters
           (set-indices-in-fa-table
            (effective-fat fat32$c)
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path)))))
            (make-list-ac
             (len
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth 0
                           (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path))))))
             0 nil))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (set-indices-in-fa-table
              (effective-fat fat32$c)
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth 0
                           (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))
              (make-list-ac
               (len
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path))))))
               0 nil))
             1))
           fat32$c)
          268435455)
         (mv-nth
          0
          (clear-cc
           fat32$c
           (d-e-first-cluster
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path))))
           (d-e-file-size
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path))))))))))))

  (defthm
    lofat-pwrite-refinement-lemma-39
    (implies
     (and
      (not (consp (cdr path)))
      (good-root-d-e-p (pseudo-root-d-e fat32$c)
                       fat32$c)
      (fat32-filename-list-p path)
      (not-intersectp-list
       (mv-nth 0
               (d-e-cc fat32$c (pseudo-root-d-e fat32$c)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (max-entry-count fat32$c))))
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (max-entry-count fat32$c)))
       0)
      (lofat-file-p file)
      (not (lofat-directory-file-p file))
      (not
       (d-e-directory-p
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path)))))
      (consp path)
      (equal
       (mv-nth
        1
        (find-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (car path)))
       0)
      (<=
       2
       (d-e-first-cluster
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path)))))
      (<
       (d-e-first-cluster
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path))))
       (+ 2 (count-of-clusters fat32$c)))
      (<=
       (+ -1
          (len (make-clusters (lofat-file->contents file)
                              (cluster-size fat32$c))))
       (+
        -1
        (count-free-clusters (effective-fat fat32$c))
        (len
         (mv-nth
          0
          (d-e-cc
           fat32$c
           (mv-nth
            0
            (find-d-e
             (make-d-e-list
              (mv-nth 0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
             (car path))))))))
      (< 0
         (len (explode (lofat-file->contents file))))
      (member-equal
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32$c)
          (mv-nth
           0
           (d-e-cc
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))))
          (make-list-ac
           (len
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path))))))
           0 nil))
         1))
       (mv-nth
        0
        (d-e-cc
         fat32$c
         (mv-nth
          0
          (find-d-e
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
           (car path)))))))
     (hifat-equiv
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth
         0
         (update-dir-contents
          (mv-nth
           0
           (place-contents
            (update-fati
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path)))))
                (make-list-ac
                 (len
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path))))))
                 0 nil))
               1))
             (fat32-update-lower-28
              (fati
               (nth
                0
                (find-n-free-clusters
                 (set-indices-in-fa-table
                  (effective-fat fat32$c)
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path)))))
                  (make-list-ac
                   (len
                    (mv-nth
                     0
                     (d-e-cc
                      fat32$c
                      (mv-nth
                       0
                       (find-d-e
                        (make-d-e-list
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c (pseudo-root-d-e fat32$c))))
                        (car path))))))
                   0 nil))
                 1))
               fat32$c)
              268435455)
             (mv-nth
              0
              (clear-cc
               fat32$c
               (d-e-first-cluster
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path))))
               (d-e-file-size
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth
                    0
                    (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))))
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path)))
            (lofat-file->contents file)
            (len (explode (lofat-file->contents file)))
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32$c)
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path)))))
               (make-list-ac
                (len
                 (mv-nth
                  0
                  (d-e-cc
                   fat32$c
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list
                      (mv-nth
                       0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                     (car path))))))
                0 nil))
              1))))
          (d-e-first-cluster (pseudo-root-d-e fat32$c))
          (nats=>string
           (insert-d-e
            (string=>nats
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (d-e-set-first-cluster-file-size
             (mv-nth
              0
              (find-d-e
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
               (car path)))
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path)))))
                (make-list-ac
                 (len
                  (mv-nth
                   0
                   (d-e-cc
                    fat32$c
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth
                        0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                      (car path))))))
                 0 nil))
               1))
             (len (explode (lofat-file->contents file))))))))
        (place-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
         (d-e-set-first-cluster-file-size
          (mv-nth
           0
           (find-d-e
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
            (car path)))
          (nth
           0
           (find-n-free-clusters
            (set-indices-in-fa-table
             (effective-fat fat32$c)
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth
                   0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                 (car path)))))
             (make-list-ac
              (len
               (mv-nth
                0
                (d-e-cc
                 fat32$c
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list
                    (mv-nth
                     0
                     (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                   (car path))))))
              0 nil))
            1))
          (len (explode (lofat-file->contents file)))))
        (max-entry-count fat32$c)))
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
        (m1-file d-e (lofat-file->contents file))))))
    :hints
    (("goal"
      :in-theory (e/d nil
                      ((:rewrite place-contents-expansion-2)))
      :use
      (:instance
       (:rewrite place-contents-expansion-2)
       (first-cluster
        (nth
         0
         (find-n-free-clusters
          (set-indices-in-fa-table
           (effective-fat fat32$c)
           (mv-nth
            0
            (d-e-cc
             fat32$c
             (mv-nth
              0
              (find-d-e
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
               (car path)))))
           (make-list-ac
            (len
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth 0
                          (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                 (car path))))))
            0 nil))
          1)))
       (file-length (len (explode (lofat-file->contents file))))
       (contents (lofat-file->contents file))
       (d-e
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
          (car path))))
       (fat32$c
        (update-fati
         (nth
          0
          (find-n-free-clusters
           (set-indices-in-fa-table
            (effective-fat fat32$c)
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                (car path)))))
            (make-list-ac
             (len
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth 0
                           (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path))))))
             0 nil))
           1))
         (fat32-update-lower-28
          (fati
           (nth
            0
            (find-n-free-clusters
             (set-indices-in-fa-table
              (effective-fat fat32$c)
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth 0
                           (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                  (car path)))))
              (make-list-ac
               (len
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth
                      0
                      (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
                    (car path))))))
               0 nil))
             1))
           fat32$c)
          268435455)
         (mv-nth
          0
          (clear-cc
           fat32$c
           (d-e-first-cluster
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path))))
           (d-e-file-size
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c))))
              (car path))))))))))))

  (defthm
    lofat-mkdir-refinement-lemma-10
    (implies
     (and
      (good-root-d-e-p (pseudo-root-d-e fat32$c)
                       fat32$c)
      (fat32-filename-list-p path)
      (equal (mv-nth 1 (lofat-to-hifat fat32$c))
             0)
      (lofat-file-p file)
      (or (stringp (lofat-file->contents file))
          (equal (lofat-file->contents file) nil))
      (not
       (equal
        (mv-nth 1
                (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                  path file))
        28))
      (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
         (max-entry-count fat32$c)))
     (and
      (equal
       (mv-nth
        1
        (lofat-to-hifat
         (mv-nth 0
                 (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                   path file))))
       0)
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat
         (mv-nth 0
                 (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                   path file))))
       (mv-nth
        0
        (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                          path
                          (m1-file d-e (lofat-file->contents file)))))
      (equal
       (mv-nth
        1
        (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                          path
                          (m1-file d-e (lofat-file->contents file))))
       (mv-nth 1
               (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                 path file)))))
    :hints
    (("goal"
      :do-not-induct t
      :cases ((atom (cdr path)))
      :in-theory (disable lofat-place-file hifat-place-file)
      :use (:instance lofat-place-file-correctness-1
                      (root-d-e (pseudo-root-d-e fat32$c))
                      (entry-limit (max-entry-count fat32$c)))
      :expand (:free (fat32$c file root-d-e)
                     (lofat-place-file fat32$c root-d-e nil file))
      :restrict ((not-intersectp-list-when-subsetp-1
                  ((y (mv-nth 0
                              (d-e-cc fat32$c
                                      (pseudo-root-d-e fat32$c))))))))
     (if (not stable-under-simplificationp)
         nil
       '(:in-theory (enable lofat-place-file hifat-place-file))))
    :otf-flg t))

(defthm
  lofat-mkdir-refinement-lemma-13
  (implies
   (and (lofat-fs-p fat32$c)
        (equal (mv-nth 1 (lofat-to-hifat fat32$c))
               0))
   (and
    (no-duplicatesp-equal (mv-nth 0
                                  (d-e-cc fat32$c (pseudo-root-d-e fat32$c))))
    (equal (mv-nth 1
                   (d-e-cc-contents fat32$c (pseudo-root-d-e fat32$c)))
           0)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-to-hifat))))

(defthm
  lofat-mkdir-refinement-lemma-30
  (implies
   (and
    (lofat-fs-p fat32$c)
    (fat32-filename-list-p path)
    (equal (mv-nth 1 (lofat-to-hifat fat32$c))
           0)
    (not (equal (mv-nth 1
                        (find-d-e (mv-nth 0 (root-d-e-list fat32$c))
                                  (car path)))
                0))
    (< (hifat-entry-count (mv-nth 0 (lofat-to-hifat fat32$c)))
       (max-entry-count fat32$c))
    (or (lofat-regular-file-p file)
        (equal (lofat-file->contents file) nil))
    (not (equal (mv-nth 1
                        (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                          path file))
                28)))
   (hifat-equiv
    (mv-nth 0
            (lofat-to-hifat
             (mv-nth 0
                     (lofat-place-file fat32$c (pseudo-root-d-e fat32$c)
                                       path file))))
    (mv-nth
     0
     (hifat-place-file (mv-nth 0 (lofat-to-hifat fat32$c))
                       path
                       (make-m1-file :contents (lofat-file->contents file)
                                     :d-e (lofat-file->d-e file))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (lofat-to-hifat root-d-e-list hifat-place-file)
                    nil)
    :restrict ((not-intersectp-list-when-subsetp-1
                ((y (mv-nth 0
                            (d-e-cc fat32$c
                                    (pseudo-root-d-e fat32$c))))))))))
