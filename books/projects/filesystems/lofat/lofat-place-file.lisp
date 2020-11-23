(in-package "ACL2")

(include-book "../eqfat")

;  lofat-place-file.lisp                                Mihir Mehta

;; get-cc-alt really should be disabled here if it can!
(local
 (in-theory (e/d ((:rewrite hifat-equiv-of-cons-lemma-5)
                  (:rewrite not-intersectp-list-of-cons-2))
                 ((:rewrite free-index-list-listp-of-update-nth-lemma-1)
                  (:rewrite free-index-list-listp-correctness-1)
                  (:rewrite non-free-index-list-listp-correctness-1)
                  (:rewrite count-free-clusters-of-set-indices-in-fa-table-2)
                  (:rewrite count-free-clusters-of-set-indices-in-fa-table-lemma-1)
                  (:rewrite non-free-index-listp-correctness-5)
                  (:rewrite free-index-listp-correctness-1)
                  (:rewrite consp-of-assoc-of-hifat-file-alist-fix)
                  (:linear hifat-entry-count-when-hifat-subsetp)
                  (:rewrite hifat-place-file-when-hifat-equiv-1)
                  (:rewrite consp-of-assoc-when-hifat-equiv-lemma-1)
                  (:rewrite hifat-subsetp-preserves-assoc)
                  (:rewrite abs-find-file-correctness-1-lemma-40)
                  (:rewrite hifat-file-alist-fix-guard-lemma-1)
                  (:rewrite natp-of-caar-when-fd-table-p)
                  (:rewrite natp-of-caar-when-file-table-p)
                  (:rewrite fat32-filename-p-of-car-when-fat32-filename-list-p)
                  (:rewrite d-e-list-p-of-cdr-when-d-e-list-p)
                  (:rewrite fat32-masked-entry-list-p-when-bounded-nat-listp)
                  (:linear find-n-free-clusters-correctness-1)
                  (:rewrite fat32-masked-entry-list-p-when-not-consp)
                  (:rewrite bounded-nat-listp-correctness-1)
                  (:rewrite stringp-when-nonempty-stringp)
                  (:rewrite str::hex-digit-char-listp-of-cons)
                  (:definition logtail$inline)
                  (:definition loghead$inline)
                  (:rewrite nat-listp-when-unsigned-byte-listp)
                  (:rewrite take-of-too-many)
                  (:rewrite make-list-ac-removal)
                  (:rewrite true-list-listp-when-not-consp)
                  (:rewrite true-list-listp-of-cdr-when-true-list-listp)
                  (:rewrite rationalp-of-car-when-rational-listp)
                  (:rewrite integerp-of-car-when-integer-listp)
                  (:rewrite acl2-numberp-of-car-when-acl2-number-listp)
                  (:rewrite subsetp-implies-subsetp-cdr)
                  (:rewrite revappend-removal)
                  (:rewrite not-intersectp-list-of-set-difference$-lemma-2
                            . 1)
                  (:rewrite member-intersectp-is-commutative-lemma-2)
                  (:rewrite intersectp-member-when-not-member-intersectp)
                  (:rewrite flatten-subset-no-duplicatesp-lemma-2)
                  (:rewrite not-intersectp-list-when-subsetp-2)
                  (:rewrite no-duplicatesp-of-member)
                  (:rewrite then-subseq-same-2)
                  (:rewrite subseq-of-length-1)
                  (:rewrite nth-when->=-n-len-l)
                  (:rewrite car-of-nthcdr)
                  (:rewrite assoc-of-car-when-member)
                  (:rewrite true-listp-when-string-list)
                  (:rewrite intersect-with-subset . 10)
                  (:rewrite intersect-with-subset . 8)
                  (:rewrite intersect-with-subset . 7)
                  (:rewrite intersect-with-subset . 4)
                  (:rewrite intersect-with-subset . 3)
                  (:rewrite intersect-with-subset . 2)
                  (:rewrite intersect-with-subset . 1)
                  (:rewrite subsetp-member . 4)
                  (:rewrite subsetp-member . 2)
                  (:rewrite consp-of-nthcdr)
                  (:induction integer-listp)
                  (:definition integer-listp)
                  (:definition rational-listp)
                  (:definition acl2-number-listp)
                  (:induction update-nth)
                  (:definition update-nth)
                  (:definition mod)
                  (:definition ceiling)
                  (:rewrite characterp-nth)
                  (:definition string-listp)
                  (:induction take)
                  (:definition take)
                  (:induction member-equal)
                  (:definition member-equal)
                  (:definition floor)
                  (:induction nth)
                  (:definition nth)
                  (:induction true-listp)
                  (:definition true-listp)))))

(defthm
  lofat-place-file-correctness-lemma-55
  (implies
   (and
    (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))
    (lofat-fs-p fat32$c)
    (< (d-e-first-cluster root-d-e)
       (+ 2 (count-of-clusters fat32$c)))
    (equal (mv-nth 1
                   (d-e-cc-contents fat32$c d-e))
           0)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c
                                          d-e-list entry-limit))
           0)
    (not-intersectp-list
     (mv-nth 0
             (d-e-cc fat32$c d-e))
     (mv-nth 2
             (lofat-to-hifat-helper fat32$c
                                    d-e-list entry-limit)))
    (d-e-p d-e)
    (useful-d-e-list-p d-e-list))
   (equal
    (d-e-cc-contents
     (mv-nth 0
             (lofat-place-file fat32$c
                               (mv-nth 0 (find-d-e d-e-list name))
                               path file))
     d-e)
    (d-e-cc-contents fat32$c d-e)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (e/d
     (useful-d-e-list-p)
     ((:rewrite d-e-cc-contents-of-lofat-place-file-disjoint)))
    :use
    (:instance
     (:rewrite d-e-cc-contents-of-lofat-place-file-disjoint)
     (d-e d-e)
     (root-d-e (mv-nth 0 (find-d-e d-e-list name)))
     (entry-limit entry-limit)))))

(defthm
  lofat-place-file-correctness-lemma-96
  (implies
   (and
    (useful-d-e-list-p d-e-list2)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c
                                          d-e-list2 entry-limit1))
           0)
    (not
     (member-intersectp-equal
      (mv-nth 2
              (lofat-to-hifat-helper fat32$c
                                     d-e-list1 entry-limit2))
      (mv-nth
       2
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents
                  fat32$c
                  (mv-nth 0 (find-d-e d-e-list2 name)))))
        entry-limit1))))
    (zp (mv-nth 3
                (lofat-to-hifat-helper fat32$c
                                       d-e-list1 entry-limit2)))
    (useful-d-e-list-p d-e-list1)
    (not-intersectp-list
     (mv-nth
      0
      (d-e-cc fat32$c
                            (mv-nth 0 (find-d-e d-e-list2 name))))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents
                 fat32$c
                 (mv-nth 0 (find-d-e d-e-list2 name)))))
       entry-limit1)))
    (not-intersectp-list
     (mv-nth
      0
      (d-e-cc fat32$c
                            (mv-nth 0 (find-d-e d-e-list2 name))))
     (mv-nth 2
             (lofat-to-hifat-helper fat32$c
                                    d-e-list1 entry-limit2)))
    (lofat-fs-p fat32$c)
    (d-e-directory-p (mv-nth 0 (find-d-e d-e-list2 name)))
    (let ((mv (d-e-cc-contents
               fat32$c
               (mv-nth 0 (find-d-e d-e-list2 name))))
          (root-d-e (mv-nth 0 (find-d-e d-e-list2 name))))
         (let ((ignore-0 (hide (mv-nth 0 mv)))
               (error-code (mv-nth 1 mv)))
              (mv-let (cc ignore-0)
                (d-e-cc fat32$c root-d-e)
                (declare (ignore ignore-0))
                (and (equal error-code 0)
                     (no-duplicatesp-equal cc))))))
   (equal
    (lofat-to-hifat-helper
     (mv-nth 0
             (lofat-place-file fat32$c
                               (mv-nth 0 (find-d-e d-e-list2 name))
                               path file))
     d-e-list1 entry-limit2)
    (lofat-to-hifat-helper fat32$c
                           d-e-list1 entry-limit2)))
  :hints
  (("goal"
    :in-theory (disable lofat-to-hifat-helper-of-lofat-place-file-disjoint)
    :use (:instance lofat-to-hifat-helper-of-lofat-place-file-disjoint
                    (root-d-e (mv-nth '0
                                          (find-d-e d-e-list2 name)))
                    (d-e-list d-e-list1)))))

(defthm
  lofat-place-file-correctness-lemma-89
  (implies
   (and
    (equal
     (mv-nth
      1
      (hifat-place-file
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit)))
       path
       (m1-file d-e (lofat-file->contents file))))
     0)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-place-file fat32$c (car d-e-list)
                                 path file))
       (make-d-e-list (mv-nth 0
                              (d-e-cc-contents fat32$c (car d-e-list))))
       entry-limit))
     0)
    (hifat-equiv
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-place-file fat32$c (car d-e-list)
                                 path file))
       (make-d-e-list (mv-nth 0
                              (d-e-cc-contents fat32$c (car d-e-list))))
       entry-limit))
     (mv-nth
      0
      (hifat-place-file
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit)))
       path
       (m1-file d-e (lofat-file->contents file)))))
    (lofat-regular-file-p file)
    (not (zp entry-limit))
    (<
     (+
      1
      (hifat-entry-count
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit))))
      (hifat-entry-count
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit))))))))))
     entry-limit)
    (consp (cdr path)))
   (<=
    (hifat-entry-count
     (mv-nth
      0
      (lofat-to-hifat-helper
       fat32$c (cdr d-e-list)
       (binary-+
        -1
        (binary-+
         entry-limit
         (unary--
          (hifat-entry-count
           (mv-nth
            0
            (lofat-to-hifat-helper
             fat32$c
             (make-d-e-list (mv-nth 0
                                    (d-e-cc-contents fat32$c (car d-e-list))))
             (binary-+ -1 entry-limit))))))))))
    (binary-+
     -1
     (binary-+
      entry-limit
      (unary--
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          (mv-nth 0
                  (lofat-place-file fat32$c (car d-e-list)
                                    path file))
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (binary-+ -1 entry-limit)))))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (disable
     (:definition member-intersectp-equal)
     (:rewrite len-of-nats=>chars)
     (:rewrite len-of-insert-d-e)
     (:rewrite place-contents-expansion-1)
     (:rewrite len-of-place-d-e)
     (:rewrite place-contents-expansion-2)
     (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-2)
     (:definition stobj-find-n-free-clusters-correctness-1)
     (:rewrite effective-fat-of-update-fati)
     (:linear hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e)
     (:rewrite lofat-place-file-correctness-lemma-96)
     (:definition find-d-e)
     (:rewrite not-intersectp-list-of-set-difference$-lemma-2
               . 2)
     (:rewrite nfix-when-zp)
     (:rewrite nth-of-nats=>chars)
     (:linear nth-when-d-e-p)
     (:rewrite d-e-fix-when-d-e-p)
     (:rewrite lofat-place-file-correctness-lemma-59)
     (:rewrite subsetp-cons-2)
     (:linear find-n-free-clusters-correctness-7)
     (:rewrite lofat-to-hifat-helper-of-delete-d-e-2
               . 2)
     (:rewrite len-of-find-n-free-clusters)
     (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
     (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-1
               . 1)
     (:type-prescription make-d-e-list-of-insert-d-e-lemma-1))))
  :rule-classes :linear)

(defthm
  lofat-place-file-correctness-lemma-84
  (implies
   (and
    (< 0
       (mv-nth 1
               (hifat-place-file
                (mv-nth 0
                        (lofat-to-hifat-helper fat32$c
                                               d-e-list entry-limit1))
                path file)))
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c
                                          d-e-list entry-limit1))
           0)
    (>= (nfix entry-limit2)
        (mv-nth 1
                (lofat-to-hifat-helper fat32$c
                                       d-e-list entry-limit1))))
   (< 0
      (mv-nth 1
              (hifat-place-file
               (mv-nth 0
                       (lofat-to-hifat-helper fat32$c
                                              d-e-list entry-limit2))
               path file))))
  :hints (("goal" :in-theory (disable lofat-to-hifat-helper-correctness-4)
           :use lofat-to-hifat-helper-correctness-4))
  :rule-classes :linear)

(defthm
  lofat-place-file-correctness-lemma-182
  (implies (lofat-regular-file-p file)
           (hifat-no-dups-p (lofat-file->contents file)))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (hifat-no-dups-p)
                           (lofat-place-file))
           :expand (hifat-no-dups-p (lofat-file->contents file)))))

;; Is there a contradiction in some hypotheses somewhere? Because this really
;; should go through in the rewriter. I can't really fathom why it isn't doing that.
(defthm
  lofat-place-file-correctness-lemma-25
  (implies
   (and
    (good-root-d-e-p root-d-e fat32$c)
    (lofat-regular-file-p file)
    (<= (len (make-clusters (lofat-file->contents file)
                            (cluster-size fat32$c)))
        (count-free-clusters (effective-fat fat32$c)))
    (not
     (d-e-directory-p
      (mv-nth
       0
       (find-d-e
        (make-d-e-list
         (mv-nth
          0
          (d-e-cc-contents fat32$c root-d-e)))
        (car path)))))
    (< 0
       (len (explode (lofat-file->contents file)))))
   (equal
    (d-e-cc-contents
     (mv-nth
      0
      (place-contents
       (update-fati
        (nth 0
             (find-n-free-clusters (effective-fat fat32$c)
                                   1))
        (fat32-update-lower-28
         (fati (nth 0
                    (find-n-free-clusters (effective-fat fat32$c)
                                          1))
               fat32$c)
         268435455)
        fat32$c)
       (mv-nth
        0
        (find-d-e
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents fat32$c root-d-e)))
         (car path)))
       (lofat-file->contents file)
       (len (explode (lofat-file->contents file)))
       (nth 0
            (find-n-free-clusters (effective-fat fat32$c)
                                  1))))
     (d-e-set-first-cluster-file-size
      (mv-nth
       0
       (find-d-e
        (make-d-e-list
         (mv-nth
          0
          (d-e-cc-contents fat32$c root-d-e)))
        (car path)))
      (nth 0
           (find-n-free-clusters (effective-fat fat32$c)
                                 1))
      (len (explode (lofat-file->contents file)))))
    (mv
     (implode
      (append
       (explode (lofat-file->contents file))
       (make-list-ac
        (+
         (min
          (d-e-file-size
           (d-e-set-first-cluster-file-size
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth
                0
                (d-e-cc-contents fat32$c root-d-e)))
              (car path)))
            (nth 0
                 (find-n-free-clusters (effective-fat fat32$c)
                                       1))
            (len (explode (lofat-file->contents file)))))
          (*
           (len
            (make-clusters
             (lofat-file->contents file)
             (cluster-size
              (update-fati
               (nth 0
                    (find-n-free-clusters (effective-fat fat32$c)
                                          1))
               (fat32-update-lower-28
                (fati
                 (nth 0
                      (find-n-free-clusters (effective-fat fat32$c)
                                            1))
                 fat32$c)
                268435455)
               fat32$c))))
           (cluster-size
            (update-fati
             (nth 0
                  (find-n-free-clusters (effective-fat fat32$c)
                                        1))
             (fat32-update-lower-28
              (fati (nth 0
                         (find-n-free-clusters (effective-fat fat32$c)
                                               1))
                    fat32$c)
              268435455)
             fat32$c))))
         (- (length (lofat-file->contents file))))
        (code-char 0) nil)))
     0)))
  :instructions
  (:promote
   (:dive 1)
   (:claim
    (and
     (not
      (d-e-directory-p
       (d-e-set-first-cluster-file-size
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents fat32$c root-d-e)))
          (car path)))
        (nth 0
             (find-n-free-clusters (effective-fat fat32$c)
                                   1))
        (len (explode (lofat-file->contents file))))))
     (equal
      (mv-nth
       2
       (place-contents
        (update-fati
         (nth 0
              (find-n-free-clusters (effective-fat fat32$c)
                                    1))
         (fat32-update-lower-28
          (fati (nth 0
                     (find-n-free-clusters (effective-fat fat32$c)
                                           1))
                fat32$c)
          268435455)
         fat32$c)
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents fat32$c root-d-e)))
          (car path)))
        (lofat-file->contents file)
        (len (explode (lofat-file->contents file)))
        (nth 0
             (find-n-free-clusters (effective-fat fat32$c)
                                   1))))
      0)
     (equal
      (nth 0
           (find-n-free-clusters (effective-fat fat32$c)
                                 1))
      (d-e-first-cluster
       (d-e-set-first-cluster-file-size
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents fat32$c root-d-e)))
          (car path)))
        (nth 0
             (find-n-free-clusters (effective-fat fat32$c)
                                   1))
        (len (explode (lofat-file->contents file))))))
     (not (zp (length (lofat-file->contents file))))
     (<= 2
         (nth 0
              (find-n-free-clusters (effective-fat fat32$c)
                                    1)))
     (stringp (lofat-file->contents file))
     (<=
      (length (lofat-file->contents file))
      (d-e-file-size
       (d-e-set-first-cluster-file-size
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents fat32$c root-d-e)))
          (car path)))
        (nth 0
             (find-n-free-clusters (effective-fat fat32$c)
                                   1))
        (len (explode (lofat-file->contents file))))))
     (lofat-fs-p
      (update-fati
       (nth 0
            (find-n-free-clusters (effective-fat fat32$c)
                                  1))
       (fat32-update-lower-28
        (fati (nth 0
                   (find-n-free-clusters (effective-fat fat32$c)
                                         1))
              fat32$c)
        268435455)
       fat32$c))
     (not
      (equal
       (fat32-entry-mask
        (fati
         (nth 0
              (find-n-free-clusters (effective-fat fat32$c)
                                    1))
         (update-fati
          (nth 0
               (find-n-free-clusters (effective-fat fat32$c)
                                     1))
          (fat32-update-lower-28
           (fati (nth 0
                      (find-n-free-clusters (effective-fat fat32$c)
                                            1))
                 fat32$c)
           268435455)
          fat32$c)))
       0))
     (<
      (nth 0
           (find-n-free-clusters (effective-fat fat32$c)
                                 1))
      (+
       2
       (count-of-clusters
        (update-fati
         (nth 0
              (find-n-free-clusters (effective-fat fat32$c)
                                    1))
         (fat32-update-lower-28
          (fati (nth 0
                     (find-n-free-clusters (effective-fat fat32$c)
                                           1))
                fat32$c)
          268435455)
         fat32$c))))
     (fat32-masked-entry-p
      (nth 0
           (find-n-free-clusters (effective-fat fat32$c)
                                 1))))
    :hints :none)
   (:rewrite d-e-cc-contents-of-place-contents-coincident-2)
   :top
   :bash :bash))

(defthm lofat-place-file-correctness-lemma-16
  (implies (and (equal (m1-file->contents file1)
                       (m1-file->contents file2))
                (m1-regular-file-p (m1-file-fix file1))
                (m1-regular-file-p (m1-file-fix file2)))
           (equal (hifat-equiv (put-assoc-equal name file1 fs)
                               (put-assoc-equal name file2 fs))
                  t))
  :hints (("goal" :in-theory (disable put-assoc-under-hifat-equiv-3)
           :use put-assoc-under-hifat-equiv-3)))

(defthm
  lofat-place-file-correctness-lemma-15
  (implies
   (and
    (>= (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name)))
        *ms-first-data-cluster*)
    (useful-d-e-list-p d-e-list)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c
                                          d-e-list entry-limit1))
           0)
    (not (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))))
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (place-d-e d-e-list
                  (d-e-set-first-cluster-file-size
                   (mv-nth 0 (find-d-e d-e-list name))
                   0 0))
       entry-limit1))
     0)
    (subsetp-equal
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (place-d-e d-e-list
                  (d-e-set-first-cluster-file-size
                   (mv-nth 0 (find-d-e d-e-list name))
                   0 0))
       entry-limit1))
     (cons nil
           (mv-nth 2
                   (lofat-to-hifat-helper fat32$c
                                          d-e-list entry-limit1))))))
  :hints
  (("goal"
    :induct (lofat-to-hifat-helper fat32$c
                                   d-e-list entry-limit1)
    :do-not-induct t
    :expand (:free (d-e d-e-list)
                   (lofat-to-hifat-helper fat32$c
                                          (cons d-e d-e-list)
                                          entry-limit1))
    :in-theory
    (e/d
     (lofat-to-hifat-helper find-d-e
                            place-d-e hifat-entry-count
                            lofat-to-hifat-helper-correctness-4)
     ((:rewrite lofat-place-file-correctness-1-lemma-14)
      (:rewrite nth-of-nats=>chars)
      (:rewrite
       hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e-lemma-3)
      (:linear nth-when-d-e-p)
      (:rewrite lofat-place-file-correctness-1-lemma-13)
      (:rewrite explode-of-d-e-filename)
      (:rewrite d-e-list-p-of-cdr-when-d-e-list-p)
      (:rewrite d-e-p-when-member-equal-of-d-e-list-p)
      (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
      (:rewrite intersectp-when-subsetp)
      (:rewrite subsetp-trans2)
      (:rewrite subsetp-when-atom-left)
      (:rewrite subsetp-when-atom-right)
      (:rewrite m1-file-p-of-cdar-when-m1-file-alist-p)
      (:rewrite subsetp-car-member)
      (:definition binary-append)
      (:rewrite m1-directory-file-p-when-m1-file-p)
      (:rewrite hifat-to-lofat-inversion-lemma-2)
      intersect-with-subset
      (:definition assoc-equal)
      (:rewrite consp-of-assoc-of-hifat-file-alist-fix)
      (:rewrite fat32-filename-p-of-caar-when-m1-file-alist-p)
      (:rewrite subdir-contents-p-when-zero-length)
      (:rewrite m1-file-alist-p-when-subsetp-equal)
      (:rewrite fat32-filename-p-correctness-1)
      (:rewrite m1-directory-file-p-correctness-1)
      (:rewrite m1-regular-file-p-correctness-1)
      (:rewrite hifat-no-dups-p-of-cdr))))))

(defthm
  lofat-place-file-correctness-lemma-169
  (implies
   (and
    (equal (lofat-file->contents file) "")
    (d-e-directory-p d-e)
    (equal (mv-nth 1
                   (lofat-place-file fat32$c d-e path file))
           0)
    (lofat-fs-p fat32$c)
    (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
           0)
    (equal
     (mv-nth 3
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (+ -1 entry-limit)))
     0)
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c d-e))
     (mv-nth 2
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (+ -1 entry-limit))))
    (lofat-regular-file-p file)
    (not (zp entry-limit))
    (<
     (+
      1
      (hifat-entry-count
       (mv-nth 0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                (+ -1 entry-limit))))
      (hifat-entry-count
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c d-e-list
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (+ -1 entry-limit))))))))))
     entry-limit)
    (fat32-filename-list-p path)
    (not (consp (cdr path)))
    (d-e-p d-e))
   (not-intersectp-list
    (mv-nth 0
            (d-e-cc (mv-nth 0
                            (lofat-place-file fat32$c d-e path file))
                    d-e))
    (mv-nth
     2
     (lofat-to-hifat-helper
      (mv-nth 0
              (lofat-place-file fat32$c d-e path file))
      (place-d-e
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
       (d-e-set-first-cluster-file-size
        (mv-nth
         0
         (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path)))
        0 0))
      (+ -1 entry-limit)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (disable (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
             (:definition member-intersectp-equal)
             (:definition free-index-listp)
             (:rewrite lofat-to-hifat-helper-of-update-dir-contents)
             (:rewrite lofat-to-hifat-helper-of-clear-cc)
             (:rewrite lofat-place-file-correctness-lemma-93)
             (:rewrite member-intersectp-is-commutative)
             (:rewrite lofat-place-file-correctness-1-lemma-11)
             (:rewrite consp-of-fat32-build-index-list)
             (:rewrite lofat-place-file-correctness-1-lemma-14)
             (:rewrite d-e-cc-under-iff . 3)
             (:rewrite lofat-place-file-correctness-lemma-121
                       . 1)
             (:rewrite not-intersectp-list-when-atom)
             (:rewrite hifat-to-lofat-inversion-lemma-17)
             (:definition find-d-e)))))

(defund-nx
  lofat-place-file-spec-1
  (d-e x entry-limit
       file path name d-e-list fat32$c fs)
  (implies
   (and
    (stobj-disjoins-list
     (mv-nth
      0
      (lofat-place-file fat32$c
                        (mv-nth 0 (find-d-e d-e-list name))
                        path file))
     (make-d-e-list
      (mv-nth
       0
       (d-e-cc-contents
        (mv-nth
         0
         (lofat-place-file fat32$c
                           (mv-nth 0 (find-d-e d-e-list name))
                           path file))
        (mv-nth 0 (find-d-e d-e-list name)))))
     entry-limit
     (append
      x
      (flatten
       (set-difference-equal
        (mv-nth
         2
         (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents
                    fat32$c
                    (mv-nth 0 (find-d-e d-e-list name)))))
          entry-limit))))))
    (hifat-equiv
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-place-file fat32$c
                          (mv-nth 0 (find-d-e d-e-list name))
                          path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth
           0
           (lofat-place-file fat32$c
                             (mv-nth 0 (find-d-e d-e-list name))
                             path file))
          (mv-nth 0 (find-d-e d-e-list name)))))
       entry-limit))
     fs))
   (and
    (hifat-equiv
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-place-file fat32$c
                          (mv-nth 0 (find-d-e d-e-list name))
                          path file))
       d-e-list entry-limit))
     (put-assoc-equal
      name
      (m1-file (mv-nth 0 (find-d-e d-e-list name))
               fs)
      (mv-nth
       0
       (lofat-to-hifat-helper fat32$c d-e-list entry-limit))))
    (stobj-disjoins-list
     (mv-nth
      0
      (lofat-place-file fat32$c
                        (mv-nth 0 (find-d-e d-e-list name))
                        path file))
     d-e-list entry-limit x))))

(defund-nx
  lofat-place-file-spec-2
  (d-e x entry-limit
       file path name d-e-list fat32$c)
  (implies
   (and
    (stobj-disjoins-list
     (mv-nth
      0
      (lofat-place-file fat32$c
                        (mv-nth 0 (find-d-e d-e-list name))
                        path file))
     (make-d-e-list
      (mv-nth
       0
       (d-e-cc-contents
        (mv-nth
         0
         (lofat-place-file fat32$c
                           (mv-nth 0 (find-d-e d-e-list name))
                           path file))
        (mv-nth 0 (find-d-e d-e-list name)))))
     entry-limit
     (append
      x
      (flatten
       (set-difference-equal
        (mv-nth
         2
         (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents
                    fat32$c
                    (mv-nth 0 (find-d-e d-e-list name)))))
          entry-limit))))))
    (hifat-equiv
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-place-file fat32$c
                          (mv-nth 0 (find-d-e d-e-list name))
                          path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth
           0
           (lofat-place-file fat32$c
                             (mv-nth 0 (find-d-e d-e-list name))
                             path file))
          (mv-nth 0 (find-d-e d-e-list name)))))
       entry-limit))
     (mv-nth
      0
      (hifat-place-file
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents
                   fat32$c
                   (mv-nth 0 (find-d-e d-e-list name)))))
         entry-limit))
       path
       (m1-file d-e (lofat-file->contents file))))))
   (and
    (hifat-equiv
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-place-file fat32$c
                          (mv-nth 0 (find-d-e d-e-list name))
                          path file))
       d-e-list entry-limit))
     (put-assoc-equal
      name
      (m1-file
       (mv-nth 0 (find-d-e d-e-list name))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents
                     fat32$c
                     (mv-nth 0 (find-d-e d-e-list name)))))
           entry-limit))
         path
         (m1-file d-e (lofat-file->contents file)))))
      (mv-nth
       0
       (lofat-to-hifat-helper fat32$c d-e-list entry-limit))))
    (stobj-disjoins-list
     (mv-nth
      0
      (lofat-place-file fat32$c
                        (mv-nth 0 (find-d-e d-e-list name))
                        path file))
     d-e-list entry-limit x))))

(defthm
  lofat-place-file-correctness-lemma-108
  (implies
   (and
    (equal (mv-nth 1
                   (lofat-place-file fat32$c d-e path file))
           0)
    (fat32-filename-list-p path)
    (equal
     (mv-nth 3
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              entry-limit))
     0)
    (lofat-directory-file-p file)
    (equal
     (mv-nth
      1
      (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                (car path)))
     0))
   (>=
    (d-e-first-cluster
     (mv-nth
      0
      (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                (car path))))
    2))
  :hints (("goal" :do-not-induct t))
  :rule-classes :linear)

(encapsulate
  ()

  (local
   (in-theory
    (disable
     (:definition intersectp-equal)
     (:rewrite
      lofat-place-file-correctness-lemma-70)
     (:definition len)
     (:rewrite subsetp-append1)
     (:rewrite
      nth-of-set-indices-in-fa-table-when-member)
     (:rewrite not-intersectp-list-when-subsetp-1)
     (:rewrite subsetp-trans2)
     (:rewrite subsetp-trans)
     (:rewrite natp-of-car-when-nat-listp)
     (:rewrite
      d-e-p-when-member-equal-of-d-e-list-p)
     (:linear
      lofat-place-file-correctness-1-lemma-25)
     (:definition make-list-ac)
     (:rewrite
      not-intersectp-list-of-set-difference$-lemma-1)
     (:rewrite
      d-e-cc-of-clear-cc)
     (:rewrite
      d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-10)
     (:rewrite
      nat-listp-if-fat32-masked-entry-list-p)
     (:rewrite member-of-append)
     (:definition binary-append)
     (:rewrite member-when-atom)
     (:rewrite put-assoc-equal-without-change . 2)
     (:rewrite lofat-place-file-correctness-lemma-40)
     (:rewrite lofat-place-file-correctness-lemma-3)
     (:rewrite lofat-place-file-correctness-1-lemma-17)
     (:rewrite lofat-place-file-correctness-1-lemma-16)
     (:rewrite lofat-place-file-correctness-1-lemma-15)
     (:rewrite lofat-place-file-correctness-1-lemma-14)
     (:rewrite lofat-place-file-correctness-1-lemma-13)
     (:rewrite lofat-place-file-correctness-1-lemma-11)
     (:rewrite d-e-cc-of-lofat-place-file-disjoint)
     (:rewrite d-e-cc-contents-of-lofat-place-file-disjoint)
     (:induction lofat-place-file)
     (:definition lofat-place-file)
     (:rewrite lofat-place-file-correctness-lemma-5)
     (:rewrite subdir-contents-p-when-zero-length)
     (:rewrite lofat-to-hifat-helper-of-update-dir-contents)
     (:rewrite delete-d-e-correctness-1)
     (:definition delete-d-e)
     (:rewrite fati-of-clear-cc . 3)
     (:rewrite effective-fat-of-clear-cc . 3)
     (:definition place-d-e)
     (:rewrite lofat-find-file-correctness-1-lemma-6)
     (:rewrite lofat-directory-file-p-when-lofat-file-p)
     (:rewrite hifat-to-lofat-inversion-lemma-23)
     (:rewrite hifat-to-lofat-inversion-lemma-2)
     (:rewrite place-contents-expansion-2)
     (:rewrite place-contents-expansion-1)
     (:rewrite natp-of-place-contents)
     (:rewrite disjoint-list-listp-of-lofat-to-hifat-helper)
     (:definition find-d-e)
     (:linear length-of-d-e-cc-contents . 3)
     (:linear length-of-d-e-cc-contents . 2)
     (:rewrite d-e-cc-under-iff . 3)
     (:rewrite d-e-cc-under-iff . 2)
     (:definition stobj-find-n-free-clusters-correctness-1)
     (:rewrite hifat-place-file-correctness-3)
     (:rewrite hifat-no-dups-p-of-cdr)
     (:rewrite m1-directory-file-p-when-m1-file-p)
     (:linear len-when-hifat-bounded-file-alist-p . 2)
     (:linear len-when-hifat-bounded-file-alist-p . 1)
     (:type-prescription hifat-bounded-file-alist-p)
     (:rewrite fat32-filename-p-of-caar-when-m1-file-alist-p)
     (:rewrite m1-file-p-of-cdar-when-m1-file-alist-p)
     (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
     (:rewrite m1-directory-file-p-correctness-1)
     (:rewrite m1-regular-file-p-correctness-1)
     (:rewrite m1-file-p-of-m1-file-fix)
     (:linear len-of-explode-when-m1-file-contents-p-1)
     (:rewrite fat32-filename-p-correctness-1)
     (:type-prescription fat32-filename-fix)
     (:rewrite explode-of-d-e-filename)
     (:rewrite d-e-p-of-take)
     (:rewrite d-e-p-of-chars=>nats)
     (:rewrite unsigned-byte-listp-when-d-e-p)
     (:rewrite find-n-free-clusters-when-zp)
     (:rewrite len-of-find-n-free-clusters)
     (:linear find-n-free-clusters-correctness-7)
     (:rewrite chars=>nats-of-take)
     (:rewrite nats=>chars-of-take)
     (:rewrite nth-of-nats=>chars)
     (:rewrite take-when-atom)
     (:rewrite str::consp-of-explode)
     (:rewrite str::explode-when-not-stringp)
     (:rewrite intersectp-member . 1)
     (:rewrite subsetp-when-atom-right)
     (:rewrite subsetp-when-atom-left)
     (:rewrite car-of-append)
     (:rewrite consp-of-append)
     (:rewrite not-intersectp-list-of-set-difference$)
     (:rewrite not-intersectp-list-of-set-difference$-lemma-3)
     (:rewrite member-intersectp-with-subset)
     (:rewrite not-intersectp-list-when-atom)
     (:rewrite append-atom-under-list-equiv)
     (:rewrite intersectp-when-subsetp)
     (:rewrite then-subseq-empty-1)
     (:rewrite nfix-when-zp)
     (:rewrite set-difference$-when-not-intersectp)
     (:rewrite consp-of-remove-assoc-1)
     (:rewrite remove-assoc-when-absent-1)
     (:rewrite nthcdr-when->=-n-len-l)
     (:rewrite intersect-with-subset . 11)
     (:rewrite intersect-with-subset . 9)
     (:rewrite intersect-with-subset . 6)
     (:rewrite intersect-with-subset . 5)
     (:rewrite subsetp-member . 1)
     (:rewrite take-of-len-free)
     (:rewrite rationalp-implies-acl2-numberp)
     (:definition subseq)
     (:definition subseq-list)
     (:definition remove-assoc-equal)
     (:definition nthcdr)
     (:definition min)
     (:type-prescription intersectp-equal)
     (:definition no-duplicatesp-equal)
     (:type-prescription binary-append)
     (:definition assoc-equal)
     (:definition char)
     (:rewrite
      lofat-remove-file-correctness-1-lemma-62))))

  ;; this is chosen to be the same as an earlier induction scheme. let's see
  ;; how it goes..
  (local
   (defun-nx
     induction-scheme
     (d-e-list entry-limit fat32$c x)
     (cond
      ((and
        (not (atom d-e-list))
        (not (zp entry-limit))
        (d-e-directory-p (car d-e-list))
        (>= (d-e-first-cluster (car d-e-list))
            2)
        (> (+ (count-of-clusters fat32$c)
              2)
           (d-e-first-cluster (car d-e-list))))
       (induction-scheme
        (cdr d-e-list)
        (+
         entry-limit
         (-
          (+
           1
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents
                        fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))
        fat32$c
        (append
         (mv-nth 0
                 (d-e-cc
                  fat32$c (car d-e-list)))
         (flatten
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents
                      fat32$c (car d-e-list))))
            (+ -1 entry-limit))))
         x)))
      ((and
        (not (atom d-e-list))
        (not (zp entry-limit))
        ;; (not (d-e-directory-p (car d-e-list)))
        (>= (d-e-first-cluster (car d-e-list))
            2)
        (> (+ (count-of-clusters fat32$c)
              2)
           (d-e-first-cluster (car d-e-list))))
       (induction-scheme
        (cdr d-e-list)
        (- entry-limit 1)
        fat32$c
        (append
         (mv-nth 0
                 (d-e-cc
                  fat32$c (car d-e-list)))
         x)))
      ((and
        (not (atom d-e-list))
        (not (zp entry-limit)))
       (induction-scheme
        (cdr d-e-list)
        (- entry-limit 1)
        fat32$c
        x))
      (t
       (mv d-e-list entry-limit fat32$c x)))))

  (local (include-book "std/lists/intersectp" :dir :system))

  (defthm lofat-place-file-correctness-lemma-205
    (implies
     (and
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file))
       (cdr d-e-list)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth
           0
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list (mv-nth 0
                                   (d-e-cc-contents fat32$c (car d-e-list))))
            (+ -1 entry-limit))))))
       (append
        (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
        (flatten
         (mv-nth
          2
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit))))
        x))
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (good-root-d-e-p root-d-e fat32$c)
      (not (equal (mv-nth 1
                          (find-d-e (cdr d-e-list)
                                    (d-e-filename (car d-e-list))))
                  0))
      (equal (mv-nth 1
                     (d-e-cc-contents fat32$c (car d-e-list)))
             0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit)))
       0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit))))))))
       0)
      (subdir-contents-p (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
      (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c (car d-e-list))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))
      (not
       (member-intersectp-equal
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (+ -1 entry-limit)))
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c (cdr d-e-list)
          (+
           -1 entry-limit
           (-
            (hifat-entry-count
             (mv-nth
              0
              (lofat-to-hifat-helper
               fat32$c
               (make-d-e-list (mv-nth 0
                                      (d-e-cc-contents fat32$c (car d-e-list))))
               (+ -1 entry-limit))))))))))
      (not (zp entry-limit))
      (<
       (+
        1
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit))))
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c (cdr d-e-list)
           (+
            -1 entry-limit
            (-
             (hifat-entry-count
              (mv-nth
               0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (car d-e-list))))
                (+ -1 entry-limit))))))))))
       entry-limit)
      (useful-d-e-list-p d-e-list)
      (not (intersectp-equal x
                             (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))))
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit)))))
     (stobj-disjoins-list
      (mv-nth 0
              (lofat-place-file fat32$c
                                (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                path file))
      d-e-list entry-limit x))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           stobj-disjoins-list find-d-e))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-222
    (implies
     (and
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth 0
                  (lofat-place-file fat32$c
                                    (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                    path file))
          (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
       entry-limit
       (append
        x
        (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
        (flatten
         (set-difference-equal
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list (mv-nth 0
                                   (d-e-cc-contents fat32$c (car d-e-list))))
            (+ -1 entry-limit)))
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth
              0
              (d-e-cc-contents fat32$c
                               (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
            entry-limit))))
        (flatten
         (set-difference-equal
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c (cdr d-e-list)
            (+
             -1 entry-limit
             (-
              (hifat-entry-count
               (mv-nth
                0
                (lofat-to-hifat-helper
                 fat32$c
                 (make-d-e-list
                  (mv-nth 0
                          (d-e-cc-contents fat32$c (car d-e-list))))
                 (+ -1 entry-limit))))))))
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth
              0
              (d-e-cc-contents fat32$c
                               (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
            entry-limit))))))
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c
                                   (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                   path file))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
            (mv-nth 0
                    (lofat-place-file fat32$c
                                      (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                      path file))
            (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
         entry-limit))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         (m1-file d-e (lofat-file->contents file)))))
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         (m1-file d-e (lofat-file->contents file))))
       0)
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit))))))))
       0)
      (not
       (member-intersectp-equal
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (+ -1 entry-limit)))
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c (cdr d-e-list)
          (+
           -1 entry-limit
           (-
            (hifat-entry-count
             (mv-nth
              0
              (lofat-to-hifat-helper
               fat32$c
               (make-d-e-list (mv-nth 0
                                      (d-e-cc-contents fat32$c (car d-e-list))))
               (+ -1 entry-limit))))))))))
      (lofat-regular-file-p file)
      (not (zp entry-limit))
      (<
       (+
        1
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit))))
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c (cdr d-e-list)
           (+
            -1 entry-limit
            (-
             (hifat-entry-count
              (mv-nth
               0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (car d-e-list))))
                (+ -1 entry-limit))))))))))
       entry-limit)
      (useful-d-e-list-p d-e-list))
     (stobj-disjoins-list
      (mv-nth 0
              (lofat-place-file fat32$c
                                (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                path file))
      (make-d-e-list
       (mv-nth
        0
        (d-e-cc-contents
         (mv-nth 0
                 (lofat-place-file fat32$c
                                   (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                   path file))
         (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
      (+
       -1 entry-limit
       (-
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit))))))
      (append
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (flatten
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (+ -1 entry-limit))))
       x
       (flatten
        (set-difference-equal
         (mv-nth
          2
          (lofat-to-hifat-helper
           fat32$c (cdr d-e-list)
           (+
            -1 entry-limit
            (-
             (hifat-entry-count
              (mv-nth
               0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (car d-e-list))))
                (+ -1 entry-limit))))))))
         (mv-nth
          2
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           (+
            -1 entry-limit
            (-
             (hifat-entry-count
              (mv-nth
               0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (car d-e-list))))
                (+ -1 entry-limit)))))))))))))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           stobj-disjoins-list)
                      ((:type-prescription make-d-e-list)))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-223
    (implies
     (and
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth 0
                  (lofat-place-file fat32$c
                                    (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                    path file))
          (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
       entry-limit
       (append
        x
        (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
        (flatten
         (set-difference-equal
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list (mv-nth 0
                                   (d-e-cc-contents fat32$c (car d-e-list))))
            (+ -1 entry-limit)))
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth
              0
              (d-e-cc-contents fat32$c
                               (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
            entry-limit))))
        (flatten
         (set-difference-equal
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c (cdr d-e-list)
            (+
             -1 entry-limit
             (-
              (hifat-entry-count
               (mv-nth
                0
                (lofat-to-hifat-helper
                 fat32$c
                 (make-d-e-list
                  (mv-nth 0
                          (d-e-cc-contents fat32$c (car d-e-list))))
                 (+ -1 entry-limit))))))))
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth
              0
              (d-e-cc-contents fat32$c
                               (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
            entry-limit))))))
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c
                                   (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                   path file))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
            (mv-nth 0
                    (lofat-place-file fat32$c
                                      (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                      path file))
            (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
         entry-limit))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         (m1-file d-e (lofat-file->contents file)))))
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         (m1-file d-e (lofat-file->contents file))))
       0)
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit))))))))
       0)
      (lofat-regular-file-p file)
      (not (zp entry-limit))
      (useful-d-e-list-p d-e-list))
     (hifat-equiv
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-place-file fat32$c
                                  (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                  path file))
        (make-d-e-list
         (mv-nth
          0
          (d-e-cc-contents
           (mv-nth 0
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                     path file))
           (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
        (+
         -1 entry-limit
         (-
          (hifat-entry-count
           (mv-nth
            0
            (lofat-to-hifat-helper
             fat32$c
             (make-d-e-list (mv-nth 0
                                    (d-e-cc-contents fat32$c (car d-e-list))))
             (+ -1 entry-limit))))))))
      (mv-nth
       0
       (hifat-place-file
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents fat32$c
                             (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
          (+
           -1 entry-limit
           (-
            (hifat-entry-count
             (mv-nth
              0
              (lofat-to-hifat-helper
               fat32$c
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (car d-e-list))))
               (+ -1 entry-limit))))))))
        path
        (m1-file d-e (lofat-file->contents file))))))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           stobj-disjoins-list)
                      ((:type-prescription make-d-e-list)))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))
  (defthm lofat-place-file-correctness-lemma-224
    (implies
     (and
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         (m1-file d-e (lofat-file->contents file))))
       0)
      (d-e-directory-p (car d-e-list))
      (<= 2 (d-e-first-cluster (car d-e-list)))
      (lofat-place-file-spec-2
       d-e
       (append
        (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
        (flatten
         (mv-nth
          2
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit))))
        x)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth
           0
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list (mv-nth 0
                                   (d-e-cc-contents fat32$c (car d-e-list))))
            (+ -1 entry-limit))))))
       file path name (cdr d-e-list)
       fat32$c)
      (not (equal (d-e-filename (car d-e-list))
                  name))
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (good-root-d-e-p root-d-e fat32$c)
      (not (equal (mv-nth 1
                          (find-d-e (cdr d-e-list)
                                    (d-e-filename (car d-e-list))))
                  0))
      (equal (mv-nth 1
                     (d-e-cc-contents fat32$c (car d-e-list)))
             0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit)))
       0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit))))))))
       0)
      (subdir-contents-p (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
      (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c (car d-e-list))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))
      (not
       (member-intersectp-equal
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (+ -1 entry-limit)))
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c (cdr d-e-list)
          (+
           -1 entry-limit
           (-
            (hifat-entry-count
             (mv-nth
              0
              (lofat-to-hifat-helper
               fat32$c
               (make-d-e-list (mv-nth 0
                                      (d-e-cc-contents fat32$c (car d-e-list))))
               (+ -1 entry-limit))))))))))
      (not (intersectp-equal x
                             (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))))
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit))))
      (lofat-regular-file-p file)
      (not (zp entry-limit))
      (<
       (+
        1
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit))))
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c (cdr d-e-list)
           (+
            -1 entry-limit
            (-
             (hifat-entry-count
              (mv-nth
               0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (car d-e-list))))
                (+ -1 entry-limit))))))))))
       entry-limit)
      (useful-d-e-list-p d-e-list))
     (lofat-place-file-spec-2 d-e x entry-limit
                              file path name d-e-list fat32$c))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           lofat-place-file-spec-2)
                      ((:type-prescription make-d-e-list)))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-218
    (implies
     (and
      (<= 2 (d-e-first-cluster (car d-e-list)))
      (equal (mv-nth 1
                     (d-e-cc-contents fat32$c (car d-e-list)))
             0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit)))
       0)
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit))))
      (not (zp entry-limit))
      (useful-d-e-list-p d-e-list))
     (not
      (member-equal
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents fat32$c
                            (mv-nth 0
                                    (find-d-e d-e-list
                                              (d-e-filename (car d-e-list)))))))
         entry-limit)))))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           stobj-disjoins-list find-d-e)
                      ((:type-prescription make-d-e-list)))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-219
    (implies
     (and
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-place-file
                fat32$c
                (mv-nth 0
                        (find-d-e d-e-list (d-e-filename (car d-e-list))))
                path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth
           0
           (lofat-place-file
            fat32$c
            (mv-nth 0
                    (find-d-e d-e-list (d-e-filename (car d-e-list))))
            path file))
          (mv-nth 0
                  (find-d-e d-e-list
                            (d-e-filename (car d-e-list)))))))
       entry-limit
       (append
        x
        (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
        (flatten
         (set-difference-equal
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list (mv-nth 0
                                   (d-e-cc-contents fat32$c (car d-e-list))))
            (+ -1 entry-limit)))
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents
                      fat32$c
                      (mv-nth 0
                              (find-d-e d-e-list
                                        (d-e-filename (car d-e-list)))))))
            entry-limit))))
        (flatten
         (set-difference-equal
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c (cdr d-e-list)
            (+
             -1 entry-limit
             (-
              (hifat-entry-count
               (mv-nth
                0
                (lofat-to-hifat-helper
                 fat32$c
                 (make-d-e-list
                  (mv-nth 0
                          (d-e-cc-contents fat32$c (car d-e-list))))
                 (+ -1 entry-limit))))))))
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents
                      fat32$c
                      (mv-nth 0
                              (find-d-e d-e-list
                                        (d-e-filename (car d-e-list)))))))
            entry-limit))))))
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file
                  fat32$c
                  (mv-nth 0
                          (find-d-e d-e-list (d-e-filename (car d-e-list))))
                  path file))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
            (mv-nth
             0
             (lofat-place-file
              fat32$c
              (mv-nth 0
                      (find-d-e d-e-list (d-e-filename (car d-e-list))))
              path file))
            (mv-nth 0
                    (find-d-e d-e-list
                              (d-e-filename (car d-e-list)))))))
         entry-limit))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents
                     fat32$c
                     (mv-nth 0
                             (find-d-e d-e-list
                                       (d-e-filename (car d-e-list)))))))
           entry-limit))
         path
         (m1-file d-e (lofat-file->contents file)))))
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit)))
         path
         (m1-file d-e (lofat-file->contents file))))
       0)
      (d-e-directory-p (car d-e-list))
      (good-root-d-e-p root-d-e fat32$c)
      (equal (mv-nth 1
                     (d-e-cc-contents fat32$c (car d-e-list)))
             0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit)))
       0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit))))))))
       0)
      (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c (car d-e-list))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))
      (not
       (member-intersectp-equal
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (+ -1 entry-limit)))
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c (cdr d-e-list)
          (+
           -1 entry-limit
           (-
            (hifat-entry-count
             (mv-nth
              0
              (lofat-to-hifat-helper
               fat32$c
               (make-d-e-list (mv-nth 0
                                      (d-e-cc-contents fat32$c (car d-e-list))))
               (+ -1 entry-limit))))))))))
      (lofat-regular-file-p file)
      (not (zp entry-limit))
      (<
       (+
        1
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit))))
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c (cdr d-e-list)
           (+
            -1 entry-limit
            (-
             (hifat-entry-count
              (mv-nth
               0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (car d-e-list))))
                (+ -1 entry-limit))))))))))
       entry-limit)
      (useful-d-e-list-p d-e-list))
     (hifat-equiv
      (cons
       (cons
        (d-e-filename (car d-e-list))
        (m1-file-hifat-file-alist-fix
         (car d-e-list)
         (mv-nth
          0
          (lofat-to-hifat-helper
           (mv-nth
            0
            (lofat-place-file
             fat32$c
             (mv-nth 0
                     (find-d-e d-e-list (d-e-filename (car d-e-list))))
             path file))
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents
              (mv-nth
               0
               (lofat-place-file
                fat32$c
                (mv-nth 0
                        (find-d-e d-e-list (d-e-filename (car d-e-list))))
                path file))
              (car d-e-list))))
           (+ -1 entry-limit)))))
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth
          0
          (lofat-place-file
           fat32$c
           (mv-nth 0
                   (find-d-e d-e-list (d-e-filename (car d-e-list))))
           path file))
         (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              (mv-nth
               0
               (lofat-place-file
                fat32$c
                (mv-nth 0
                        (find-d-e d-e-list (d-e-filename (car d-e-list))))
                path file))
              (make-d-e-list
               (mv-nth
                0
                (d-e-cc-contents
                 (mv-nth
                  0
                  (lofat-place-file
                   fat32$c
                   (mv-nth 0
                           (find-d-e d-e-list (d-e-filename (car d-e-list))))
                   path file))
                 (car d-e-list))))
              (+ -1 entry-limit)))))))))
      (cons
       (cons
        (d-e-filename (car d-e-list))
        (m1-file-hifat-file-alist-fix
         (mv-nth 0
                 (find-d-e d-e-list (d-e-filename (car d-e-list))))
         (mv-nth
          0
          (hifat-place-file
           (mv-nth
            0
            (lofat-to-hifat-helper
             fat32$c
             (make-d-e-list
              (mv-nth
               0
               (d-e-cc-contents
                fat32$c
                (mv-nth 0
                        (find-d-e d-e-list
                                  (d-e-filename (car d-e-list)))))))
             entry-limit))
           path
           (m1-file d-e (lofat-file->contents file))))))
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           stobj-disjoins-list find-d-e)
                      ((:type-prescription make-d-e-list)))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-220
    (implies
     (and
      (fat32-filename-list-p path)
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-place-file
                fat32$c
                (mv-nth 0
                        (find-d-e d-e-list (d-e-filename (car d-e-list))))
                path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth
           0
           (lofat-place-file
            fat32$c
            (mv-nth 0
                    (find-d-e d-e-list (d-e-filename (car d-e-list))))
            path file))
          (mv-nth 0
                  (find-d-e d-e-list
                            (d-e-filename (car d-e-list)))))))
       entry-limit
       (append
        x
        (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
        (flatten
         (set-difference-equal
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list (mv-nth 0
                                   (d-e-cc-contents fat32$c (car d-e-list))))
            (+ -1 entry-limit)))
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents
                      fat32$c
                      (mv-nth 0
                              (find-d-e d-e-list
                                        (d-e-filename (car d-e-list)))))))
            entry-limit))))
        (flatten
         (set-difference-equal
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c (cdr d-e-list)
            (+
             -1 entry-limit
             (-
              (hifat-entry-count
               (mv-nth
                0
                (lofat-to-hifat-helper
                 fat32$c
                 (make-d-e-list
                  (mv-nth 0
                          (d-e-cc-contents fat32$c (car d-e-list))))
                 (+ -1 entry-limit))))))))
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents
                      fat32$c
                      (mv-nth 0
                              (find-d-e d-e-list
                                        (d-e-filename (car d-e-list)))))))
            entry-limit))))))
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file
                  fat32$c
                  (mv-nth 0
                          (find-d-e d-e-list (d-e-filename (car d-e-list))))
                  path file))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
            (mv-nth
             0
             (lofat-place-file
              fat32$c
              (mv-nth 0
                      (find-d-e d-e-list (d-e-filename (car d-e-list))))
              path file))
            (mv-nth 0
                    (find-d-e d-e-list
                              (d-e-filename (car d-e-list)))))))
         entry-limit))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents
                     fat32$c
                     (mv-nth 0
                             (find-d-e d-e-list
                                       (d-e-filename (car d-e-list)))))))
           entry-limit))
         path
         (m1-file d-e (lofat-file->contents file)))))
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit)))
         path
         (m1-file d-e (lofat-file->contents file))))
       0)
      (d-e-directory-p (car d-e-list))
      (equal (mv-nth 1
                     (lofat-place-file fat32$c (car d-e-list)
                                       path file))
             0)
      (good-root-d-e-p root-d-e fat32$c)
      (non-free-index-listp x (effective-fat fat32$c))
      (not (equal (mv-nth 1
                          (find-d-e (cdr d-e-list)
                                    (d-e-filename (car d-e-list))))
                  0))
      (equal (mv-nth 1
                     (d-e-cc-contents fat32$c (car d-e-list)))
             0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit)))
       0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit))))))))
       0)
      (subdir-contents-p (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
      (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c (car d-e-list))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))
      (not
       (member-intersectp-equal
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (+ -1 entry-limit)))
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c (cdr d-e-list)
          (+
           -1 entry-limit
           (-
            (hifat-entry-count
             (mv-nth
              0
              (lofat-to-hifat-helper
               fat32$c
               (make-d-e-list (mv-nth 0
                                      (d-e-cc-contents fat32$c (car d-e-list))))
               (+ -1 entry-limit))))))))))
      (not (intersectp-equal x
                             (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))))
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit))))
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))
      (lofat-file-p file)
      (lofat-regular-file-p file)
      (<= (len (make-clusters (lofat-file->contents file)
                              (cluster-size fat32$c)))
          (count-free-clusters (effective-fat fat32$c)))
      (consp path)
      (not (zp entry-limit))
      (<
       (+
        1
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit))))
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c (cdr d-e-list)
           (+
            -1 entry-limit
            (-
             (hifat-entry-count
              (mv-nth
               0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (car d-e-list))))
                (+ -1 entry-limit))))))))))
       entry-limit)
      (useful-d-e-list-p d-e-list))
     (stobj-disjoins-list
      (mv-nth 0
              (lofat-place-file
               fat32$c
               (mv-nth 0
                       (find-d-e d-e-list (d-e-filename (car d-e-list))))
               path file))
      d-e-list entry-limit x))
    :hints
    (("goal"
      :in-theory
      (e/d
       (not-intersectp-list lofat-to-hifat-helper-correctness-4
                            stobj-disjoins-list find-d-e)
       ((:type-prescription make-d-e-list)
        (:definition member-intersectp-equal)
        (:rewrite lofat-place-file-correctness-lemma-83)
        (:rewrite lofat-place-file-correctness-lemma-121
                  . 1)
        (:rewrite hifat-to-lofat-inversion-lemma-17)
        (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
        (:definition free-index-listp)
        (:rewrite
         hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e-lemma-3)
        (:linear lofat-to-hifat-helper-after-delete-and-clear-1-lemma-1)
        (:linear lofat-find-file-correctness-1-lemma-8)))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-221
    (implies
     (and
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit)))
         path
         (m1-file d-e (lofat-file->contents file))))
       0)
      (d-e-directory-p (car d-e-list))
      (equal (mv-nth 1
                     (lofat-place-file fat32$c (car d-e-list)
                                       path file))
             0)
      (good-root-d-e-p root-d-e fat32$c)
      (non-free-index-listp x (effective-fat fat32$c))
      (not (equal (mv-nth 1
                          (find-d-e (cdr d-e-list)
                                    (d-e-filename (car d-e-list))))
                  0))
      (equal (mv-nth 1
                     (d-e-cc-contents fat32$c (car d-e-list)))
             0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit)))
       0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit))))))))
       0)
      (subdir-contents-p (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
      (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c (car d-e-list))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))
      (not
       (member-intersectp-equal
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (+ -1 entry-limit)))
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c (cdr d-e-list)
          (+
           -1 entry-limit
           (-
            (hifat-entry-count
             (mv-nth
              0
              (lofat-to-hifat-helper
               fat32$c
               (make-d-e-list (mv-nth 0
                                      (d-e-cc-contents fat32$c (car d-e-list))))
               (+ -1 entry-limit))))))))))
      (not (intersectp-equal x
                             (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))))
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit))))
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))
      (lofat-file-p file)
      (lofat-regular-file-p file)
      (<= (len (make-clusters (lofat-file->contents file)
                              (cluster-size fat32$c)))
          (count-free-clusters (effective-fat fat32$c)))
      (consp path)
      (not (zp entry-limit))
      (<
       (+
        1
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit))))
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c (cdr d-e-list)
           (+
            -1 entry-limit
            (-
             (hifat-entry-count
              (mv-nth
               0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (car d-e-list))))
                (+ -1 entry-limit))))))))))
       entry-limit)
      (useful-d-e-list-p d-e-list)
      (fat32-filename-list-p path))
     (lofat-place-file-spec-2 d-e x entry-limit
                              file path (d-e-filename (car d-e-list))
                              d-e-list fat32$c))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           lofat-place-file-spec-2)
                      ((:type-prescription make-d-e-list)))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-207
   (implies
    (and
     (not (d-e-directory-p (car d-e-list)))
     (< (d-e-first-cluster (car d-e-list)) 2)
     (stobj-disjoins-list
      (mv-nth 0
              (lofat-place-file fat32$c
                                (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                path file))
      (cdr d-e-list)
      (+ -1 entry-limit)
      x)
     (not (equal (mv-nth 1
                         (find-d-e (cdr d-e-list)
                                   (d-e-filename (car d-e-list))))
                 0))
     (not (zp entry-limit)))
    (stobj-disjoins-list
     (mv-nth 0
             (lofat-place-file fat32$c
                               (mv-nth 0 (find-d-e (cdr d-e-list) name))
                               path file))
     d-e-list entry-limit x))
   :hints
   (("goal"
     :in-theory (e/d (not-intersectp-list hifat-entry-count
                                          lofat-to-hifat-helper-correctness-4
                                          stobj-disjoins-list find-d-e))
     :do-not-induct t
     :expand ((:free (fat32$c entry-limit)
                     (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
              (:free (x1 x2 y)
                     (not-intersectp-list x1 (cons x2 y)))
              (:free (d-e fat32$c d-e-list entry-limit)
                     (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                            entry-limit))
              (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-211
    (implies
     (and
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth 0
                  (lofat-place-file fat32$c
                                    (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                    path file))
          (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
       entry-limit
       (append
        x
        (flatten
         (set-difference-equal
          (mv-nth 2
                  (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                         (+ -1 entry-limit)))
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth
              0
              (d-e-cc-contents fat32$c
                               (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
            entry-limit))))))
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c
                                   (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                   path file))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
            (mv-nth 0
                    (lofat-place-file fat32$c
                                      (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                      path file))
            (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
         entry-limit))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         (m1-file d-e (lofat-file->contents file)))))
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         (m1-file d-e (lofat-file->contents file))))
       0)
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                            (+ -1 entry-limit)))
             0)
      (lofat-regular-file-p file)
      (not (zp entry-limit))
      (useful-d-e-list-p d-e-list))
     (stobj-disjoins-list
      (mv-nth 0
              (lofat-place-file fat32$c
                                (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                path file))
      (make-d-e-list
       (mv-nth
        0
        (d-e-cc-contents
         (mv-nth 0
                 (lofat-place-file fat32$c
                                   (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                   path file))
         (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
      (+ -1 entry-limit)
      (append
       x
       (flatten
        (set-difference-equal
         (mv-nth 2
                 (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                        (+ -1 entry-limit)))
         (mv-nth
          2
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           (+ -1 entry-limit))))))))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           stobj-disjoins-list)
                      ((:type-prescription make-d-e-list)))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-212
    (implies
     (and
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth 0
                  (lofat-place-file fat32$c
                                    (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                    path file))
          (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
       entry-limit
       (append
        x
        (flatten
         (set-difference-equal
          (mv-nth 2
                  (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                         (+ -1 entry-limit)))
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth
              0
              (d-e-cc-contents fat32$c
                               (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
            entry-limit))))))
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c
                                   (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                   path file))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
            (mv-nth 0
                    (lofat-place-file fat32$c
                                      (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                      path file))
            (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
         entry-limit))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         (m1-file d-e (lofat-file->contents file)))))
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         (m1-file d-e (lofat-file->contents file))))
       0)
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                            (+ -1 entry-limit)))
             0)
      (lofat-regular-file-p file)
      (not (zp entry-limit))
      (useful-d-e-list-p d-e-list))
     (hifat-equiv
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-place-file fat32$c
                                  (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                  path file))
        (make-d-e-list
         (mv-nth
          0
          (d-e-cc-contents
           (mv-nth 0
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                     path file))
           (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
        (+ -1 entry-limit)))
      (mv-nth
       0
       (hifat-place-file
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents fat32$c
                             (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
          (+ -1 entry-limit)))
        path
        (m1-file d-e (lofat-file->contents file))))))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           stobj-disjoins-list)
                      ((:type-prescription make-d-e-list)))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-217
   (implies
    (and
     (equal
      (mv-nth
       1
       (hifat-place-file
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents fat32$c
                             (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
          entry-limit))
        path
        (m1-file d-e (lofat-file->contents file))))
      0)
     (< (d-e-first-cluster (car d-e-list)) 2)
     (consp d-e-list)
     (lofat-place-file-spec-2 d-e x (+ -1 entry-limit)
                              file path name (cdr d-e-list)
                              fat32$c)
     (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
     (not (d-e-directory-p (car d-e-list)))
     (equal (mv-nth 3
                    (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                           (+ -1 entry-limit)))
            0)
     (not (equal (mv-nth 1
                         (find-d-e (cdr d-e-list)
                                   (d-e-filename (car d-e-list))))
                 0))
     (lofat-regular-file-p file)
     (not (zp entry-limit))
     (useful-d-e-list-p d-e-list))
    (lofat-place-file-spec-2 d-e x entry-limit
                             file path name d-e-list fat32$c))
   :hints
   (("goal"
     :in-theory (e/d (not-intersectp-list hifat-entry-count
                                          lofat-to-hifat-helper-correctness-4
                                          lofat-place-file-spec-2)
                     ((:type-prescription make-d-e-list)))
     :do-not-induct t
     :expand ((:free (fat32$c entry-limit)
                     (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
              (:free (x1 x2 y)
                     (not-intersectp-list x1 (cons x2 y)))
              (:free (d-e fat32$c d-e-list entry-limit)
                     (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                            entry-limit))
              (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-214
    (implies
     (and
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth 0
                  (lofat-place-file fat32$c
                                    (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                    path file))
          (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
       entry-limit
       (append
        x
        (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
        (flatten
         (set-difference-equal
          (mv-nth 2
                  (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                         (+ -1 entry-limit)))
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth
              0
              (d-e-cc-contents fat32$c
                               (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
            entry-limit))))))
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c
                                   (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                   path file))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
            (mv-nth 0
                    (lofat-place-file fat32$c
                                      (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                      path file))
            (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
         entry-limit))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         (m1-file d-e (lofat-file->contents file)))))
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         (m1-file d-e (lofat-file->contents file))))
       0)
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                            (+ -1 entry-limit)))
             0)
      (lofat-regular-file-p file)
      (not (zp entry-limit))
      (useful-d-e-list-p d-e-list))
     (stobj-disjoins-list
      (mv-nth 0
              (lofat-place-file fat32$c
                                (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                path file))
      (make-d-e-list
       (mv-nth
        0
        (d-e-cc-contents
         (mv-nth 0
                 (lofat-place-file fat32$c
                                   (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                   path file))
         (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
      (+ -1 entry-limit)
      (append
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       x
       (flatten
        (set-difference-equal
         (mv-nth 2
                 (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                        (+ -1 entry-limit)))
         (mv-nth
          2
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           (+ -1 entry-limit))))))))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           stobj-disjoins-list)
                      ((:type-prescription make-d-e-list)))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-215
    (implies
     (and
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth 0
                  (lofat-place-file fat32$c
                                    (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                    path file))
          (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
       entry-limit
       (append
        x
        (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
        (flatten
         (set-difference-equal
          (mv-nth 2
                  (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                         (+ -1 entry-limit)))
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth
              0
              (d-e-cc-contents fat32$c
                               (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
            entry-limit))))))
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c
                                   (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                   path file))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
            (mv-nth 0
                    (lofat-place-file fat32$c
                                      (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                      path file))
            (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
         entry-limit))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         (m1-file d-e (lofat-file->contents file)))))
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         (m1-file d-e (lofat-file->contents file))))
       0)
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                            (+ -1 entry-limit)))
             0)
      (lofat-regular-file-p file)
      (not (zp entry-limit))
      (useful-d-e-list-p d-e-list))
     (hifat-equiv
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-place-file fat32$c
                                  (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                  path file))
        (make-d-e-list
         (mv-nth
          0
          (d-e-cc-contents
           (mv-nth 0
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                     path file))
           (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
        (+ -1 entry-limit)))
      (mv-nth
       0
       (hifat-place-file
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents fat32$c
                             (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
          (+ -1 entry-limit)))
        path
        (m1-file d-e (lofat-file->contents file))))))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           stobj-disjoins-list)
                      ((:type-prescription make-d-e-list)))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-120
    (implies
     (and
      (not (d-e-directory-p (car d-e-list)))
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file))
       (cdr d-e-list)
       (+ -1 entry-limit)
       (append (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
               x))
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (good-root-d-e-p root-d-e fat32$c)
      (not (equal (mv-nth 1
                          (find-d-e (cdr d-e-list)
                                    (d-e-filename (car d-e-list))))
                  0))
      (equal (mv-nth 1
                     (d-e-cc-contents fat32$c (car d-e-list)))
             0)
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                            (+ -1 entry-limit)))
             0)
      (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c (car d-e-list))))
      (not-intersectp-list (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
                           (mv-nth 2
                                   (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                                          (+ -1 entry-limit))))
      (not (zp entry-limit))
      (useful-d-e-list-p d-e-list)
      (not (intersectp-equal x
                             (mv-nth 0 (d-e-cc fat32$c (car d-e-list))))))
     (stobj-disjoins-list
      (mv-nth 0
              (lofat-place-file fat32$c
                                (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                path file))
      d-e-list entry-limit x))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           stobj-disjoins-list))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-216
    (implies
     (and
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         (m1-file d-e (lofat-file->contents file))))
       0)
      (not (d-e-directory-p (car d-e-list)))
      (<= 2 (d-e-first-cluster (car d-e-list)))
      (lofat-place-file-spec-2
       d-e
       (append (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
               x)
       (+ -1 entry-limit)
       file path name (cdr d-e-list)
       fat32$c)
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (good-root-d-e-p root-d-e fat32$c)
      (not (equal (mv-nth 1
                          (find-d-e (cdr d-e-list)
                                    (d-e-filename (car d-e-list))))
                  0))
      (equal (mv-nth 1
                     (d-e-cc-contents fat32$c (car d-e-list)))
             0)
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                            (+ -1 entry-limit)))
             0)
      (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c (car d-e-list))))
      (not-intersectp-list (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
                           (mv-nth 2
                                   (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                                          (+ -1 entry-limit))))
      (not (intersectp-equal x
                             (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))))
      (lofat-regular-file-p file)
      (not (zp entry-limit))
      (<
       (+
        1
        (hifat-entry-count (mv-nth 0
                                   (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                                          (+ -1 entry-limit)))))
       entry-limit)
      (useful-d-e-list-p d-e-list))
     (lofat-place-file-spec-2 d-e x entry-limit
                              file path name d-e-list fat32$c))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           lofat-place-file-spec-2)
                      ((:type-prescription make-d-e-list)))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-201
    (implies
     (and
      (<= (+ 2 (count-of-clusters fat32$c))
          (d-e-first-cluster (car d-e-list)))
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file))
       (cdr d-e-list)
       (+ -1 entry-limit)
       x)
      (not (d-e-directory-p (car d-e-list)))
      (not (zp entry-limit))
      (not (equal (mv-nth 1
                          (find-d-e (cdr d-e-list)
                                    (d-e-filename (car d-e-list))))
                  0)))
     (stobj-disjoins-list
      (mv-nth 0
              (lofat-place-file fat32$c
                                (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                path file))
      d-e-list entry-limit x))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           stobj-disjoins-list find-d-e))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-213
    (implies
     (and
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         (m1-file d-e (lofat-file->contents file))))
       0)
      (<= (+ 2 (count-of-clusters fat32$c))
          (d-e-first-cluster (car d-e-list)))
      (lofat-place-file-spec-2 d-e x (+ -1 entry-limit)
                               file path name (cdr d-e-list)
                               fat32$c)
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (not (d-e-directory-p (car d-e-list)))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                            (+ -1 entry-limit)))
             0)
      (not (equal (mv-nth 1
                          (find-d-e (cdr d-e-list)
                                    (d-e-filename (car d-e-list))))
                  0))
      (lofat-regular-file-p file)
      (< (d-e-first-cluster (mv-nth 0 (find-d-e (cdr d-e-list) name)))
         (+ 2 (count-of-clusters fat32$c)))
      (not (zp entry-limit))
      (useful-d-e-list-p d-e-list))
     (lofat-place-file-spec-2 d-e x entry-limit
                              file path name d-e-list fat32$c))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           lofat-place-file-spec-2)
                      ((:type-prescription make-d-e-list)))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  ;; Hypotheses minimised.
  (defthm
    lofat-place-file-correctness-lemma-94
    (implies
     (and
      (equal (mv-nth 1
                     (lofat-place-file fat32$c
                                       (mv-nth 0 (find-d-e d-e-list name))
                                       path file))
             0)
      (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))
      (good-root-d-e-p root-d-e fat32$c)
      (non-free-index-listp x (effective-fat fat32$c))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
             0)
      (not-intersectp-list
       x
       (mv-nth 2
               (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
      (lofat-file-p file)
      (lofat-regular-file-p file)
      (<= (len (make-clusters (lofat-file->contents file)
                              (cluster-size fat32$c)))
          (count-free-clusters (effective-fat fat32$c)))
      (consp path)
      (< (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
         entry-limit)
      (useful-d-e-list-p d-e-list)
      (fat32-filename-list-p path)
      (zp
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents fat32$c
                                     (mv-nth 0 (find-d-e d-e-list name)))))
           entry-limit))
         path
         (m1-file d-e (lofat-file->contents file))))))
     (lofat-place-file-spec-2 d-e x entry-limit
                              file path name d-e-list fat32$c))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4)
                      ((:type-prescription make-d-e-list)))
      :induct (induction-scheme d-e-list entry-limit fat32$c x)
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name))))
    :rule-classes
    ((:rewrite
      :corollary
      (implies
       (and
        (equal (mv-nth 1
                       (lofat-place-file fat32$c
                                         (mv-nth 0 (find-d-e d-e-list name))
                                         path file))
               0)
        (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))
        (equal
         (mv-nth
          3
          (lofat-to-hifat-helper
           (mv-nth 0
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e d-e-list name))
                                     path file))
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents
              (mv-nth 0
                      (lofat-place-file fat32$c
                                        (mv-nth 0 (find-d-e d-e-list name))
                                        path file))
              (mv-nth 0 (find-d-e d-e-list name)))))
           entry-limit))
         0)
        (not-intersectp-list
         x
         (mv-nth
          2
          (lofat-to-hifat-helper
           (mv-nth 0
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e d-e-list name))
                                     path file))
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents
              (mv-nth 0
                      (lofat-place-file fat32$c
                                        (mv-nth 0 (find-d-e d-e-list name))
                                        path file))
              (mv-nth 0 (find-d-e d-e-list name)))))
           entry-limit)))
        (not
         (member-intersectp-equal
          (set-difference-equal
           (mv-nth 2
                   (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
           (mv-nth
            2
            (lofat-to-hifat-helper
             fat32$c
             (make-d-e-list
              (mv-nth 0
                      (d-e-cc-contents fat32$c
                                       (mv-nth 0 (find-d-e d-e-list name)))))
             entry-limit)))
          (mv-nth
           2
           (lofat-to-hifat-helper
            (mv-nth 0
                    (lofat-place-file fat32$c
                                      (mv-nth 0 (find-d-e d-e-list name))
                                      path file))
            (make-d-e-list
             (mv-nth
              0
              (d-e-cc-contents
               (mv-nth 0
                       (lofat-place-file fat32$c
                                         (mv-nth 0 (find-d-e d-e-list name))
                                         path file))
               (mv-nth 0 (find-d-e d-e-list name)))))
            entry-limit))))
        (hifat-equiv
         (mv-nth
          0
          (lofat-to-hifat-helper
           (mv-nth 0
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e d-e-list name))
                                     path file))
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents
              (mv-nth 0
                      (lofat-place-file fat32$c
                                        (mv-nth 0 (find-d-e d-e-list name))
                                        path file))
              (mv-nth 0 (find-d-e d-e-list name)))))
           entry-limit))
         (mv-nth
          0
          (hifat-place-file
           (mv-nth
            0
            (lofat-to-hifat-helper
             fat32$c
             (make-d-e-list
              (mv-nth 0
                      (d-e-cc-contents fat32$c
                                       (mv-nth 0 (find-d-e d-e-list name)))))
             entry-limit))
           path
           (m1-file d-e (lofat-file->contents file)))))
        (good-root-d-e-p root-d-e fat32$c)
        (non-free-index-listp x (effective-fat fat32$c))
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               0)
        (not-intersectp-list
         x
         (mv-nth 2
                 (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
        (lofat-file-p file)
        (lofat-regular-file-p file)
        (<= (len (make-clusters (lofat-file->contents file)
                                (cluster-size fat32$c)))
            (count-free-clusters (effective-fat fat32$c)))
        (consp path)
        (< (hifat-entry-count
            (mv-nth 0
                    (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
           entry-limit)
        (useful-d-e-list-p d-e-list)
        (fat32-filename-list-p path)
        (zp
         (mv-nth
          1
          (hifat-place-file
           (mv-nth
            0
            (lofat-to-hifat-helper
             fat32$c
             (make-d-e-list
              (mv-nth 0
                      (d-e-cc-contents fat32$c
                                       (mv-nth 0 (find-d-e d-e-list name)))))
             entry-limit))
           path
           (m1-file d-e (lofat-file->contents file))))))
       (not-intersectp-list
        x
        (mv-nth 2
                (lofat-to-hifat-helper
                 (mv-nth 0
                         (lofat-place-file fat32$c
                                           (mv-nth 0 (find-d-e d-e-list name))
                                           path file))
                 d-e-list entry-limit))))
      :hints
      (("goal" :do-not-induct t
        :in-theory (e/d (stobj-disjoins-list lofat-place-file-spec-2)))))))

  (defthm lofat-place-file-correctness-lemma-32
    (implies
     (and
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth 0
                  (lofat-place-file fat32$c
                                    (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                    path file))
          (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
       entry-limit
       (append
        x
        (flatten
         (set-difference-equal
          (mv-nth 2
                  (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth
              0
              (d-e-cc-contents fat32$c
                               (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
            entry-limit))))))
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c
                                   (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                   path file))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
            (mv-nth 0
                    (lofat-place-file fat32$c
                                      (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                      path file))
            (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
         entry-limit))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents)))))
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents))))
       0)
      (not (d-e-directory-p (car d-e-list)))
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                            (+ -1 entry-limit)))
             0)
      (<
       (+
        1
        (hifat-entry-count (mv-nth 0
                                   (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                                          (+ -1 entry-limit)))))
       entry-limit)
      (useful-d-e-list-p d-e-list))
     (stobj-disjoins-list
      (mv-nth 0
              (lofat-place-file fat32$c
                                (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                path file))
      (make-d-e-list
       (mv-nth
        0
        (d-e-cc-contents
         (mv-nth 0
                 (lofat-place-file fat32$c
                                   (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                   path file))
         (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
      (+ -1 entry-limit)
      (append
       x
       (flatten
        (set-difference-equal
         (mv-nth 2
                 (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                        (+ -1 entry-limit)))
         (mv-nth
          2
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           (+ -1 entry-limit))))))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d
       (stobj-disjoins-list not-intersectp-list
                            lofat-to-hifat-helper-correctness-4
                            lofat-to-hifat-helper)
       (hifat-entry-count
        (:rewrite lofat-place-file-correctness-1-lemma-14)
        (:rewrite lofat-place-file-correctness-lemma-55)
        (:rewrite hifat-file-alist-fix-when-hifat-no-dups-p)
        (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
        (:definition member-intersectp-equal)
        (:rewrite not-intersectp-list-of-append-1)
        (:rewrite lofat-place-file-correctness-1-lemma-13)
        (:rewrite d-e-cc-contents-of-lofat-place-file-coincident-lemma-13)
        (:definition not-intersectp-list)
        (:rewrite lofat-place-file-correctness-lemma-56)
        (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
        (:rewrite lofat-place-file-correctness-1-lemma-14)
        (:rewrite lofat-place-file-correctness-lemma-55)
        (:rewrite hifat-file-alist-fix-when-hifat-no-dups-p)
        (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
        (:definition member-intersectp-equal)
        (:rewrite not-intersectp-list-of-append-1)
        (:definition natp)
        (:rewrite lofat-place-file-correctness-1-lemma-13)
        (:rewrite d-e-cc-contents-of-lofat-place-file-coincident-lemma-13)
        (:definition not-intersectp-list)
        (:rewrite lofat-place-file-correctness-lemma-56)
        (:rewrite nfix-when-zp)
        (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
        (:definition free-index-listp)
        (:rewrite nth-of-nats=>chars)
        (:linear nth-when-d-e-p)
        (:rewrite d-e-p-of-car-when-d-e-list-p)
        (:rewrite nth-of-effective-fat)
        (:definition find-d-e)
        (:rewrite d-e-list-p-when-useful-d-e-list-p)
        (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
        (:definition free-index-listp)
        (:rewrite nth-of-nats=>chars)
        (:linear nth-when-d-e-p)
        (:rewrite d-e-p-of-car-when-d-e-list-p)
        (:rewrite nth-of-effective-fat)
        (:definition find-d-e)
        (:rewrite d-e-list-p-when-useful-d-e-list-p)
        (:rewrite d-e-fix-when-d-e-p)
        (:rewrite
         hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e-lemma-3))))))

  (defthm lofat-place-file-correctness-lemma-101
    (implies
     (and
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c
                                   (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                   path file))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
            (mv-nth 0
                    (lofat-place-file fat32$c
                                      (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                      path file))
            (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
         entry-limit))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents)))))
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents))))
       0)
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                            (+ -1 entry-limit)))
             0)
      (not (zp entry-limit))
      (useful-d-e-list-p d-e-list)
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth 0
                  (lofat-place-file fat32$c
                                    (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                    path file))
          (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
       entry-limit
       (append
        x
        (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
        (flatten
         (set-difference-equal
          (mv-nth 2
                  (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                         (+ -1 entry-limit)))
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth
              0
              (d-e-cc-contents fat32$c
                               (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
            entry-limit)))))))
     (stobj-disjoins-list
      (mv-nth 0
              (lofat-place-file fat32$c
                                (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                path file))
      (make-d-e-list
       (mv-nth
        0
        (d-e-cc-contents
         (mv-nth 0
                 (lofat-place-file fat32$c
                                   (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                   path file))
         (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
      (+ -1 entry-limit)
      (append
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       x
       (flatten
        (set-difference-equal
         (mv-nth 2
                 (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                        (+ -1 entry-limit)))
         (mv-nth
          2
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           (+ -1 entry-limit))))))))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           stobj-disjoins-list))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-113
    (implies
     (and
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c
                                   (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                   path file))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
            (mv-nth 0
                    (lofat-place-file fat32$c
                                      (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                      path file))
            (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
         entry-limit))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents)))))
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents))))
       0)
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                            (+ -1 entry-limit)))
             0)
      (not (zp entry-limit))
      (useful-d-e-list-p d-e-list)
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth 0
                  (lofat-place-file fat32$c
                                    (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                    path file))
          (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
       entry-limit
       (append
        x
        (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
        (flatten
         (set-difference-equal
          (mv-nth 2
                  (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                         (+ -1 entry-limit)))
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth
              0
              (d-e-cc-contents fat32$c
                               (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
            entry-limit)))))))
     (hifat-equiv
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-place-file fat32$c
                                  (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                  path file))
        (make-d-e-list
         (mv-nth
          0
          (d-e-cc-contents
           (mv-nth 0
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                     path file))
           (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
        (+ -1 entry-limit)))
      (mv-nth
       0
       (hifat-place-file
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents fat32$c
                             (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
          (+ -1 entry-limit)))
        path
        '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
          (contents))))))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           stobj-disjoins-list))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-146
    (implies
     (and
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents))))
       0)
      (not (d-e-directory-p (car d-e-list)))
      (<= 2 (d-e-first-cluster (car d-e-list)))
      (lofat-place-file-spec-1
       d-e
       (append (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
               x)
       (+ -1 entry-limit)
       file path name (cdr d-e-list)
       fat32$c
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           (+ -1 entry-limit)))
         path
         (m1-file-hifat-file-alist-fix d-e nil))))
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (good-root-d-e-p root-d-e fat32$c)
      (not (equal (mv-nth 1
                          (find-d-e (cdr d-e-list)
                                    (d-e-filename (car d-e-list))))
                  0))
      (equal (mv-nth 1
                     (d-e-cc-contents fat32$c (car d-e-list)))
             0)
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                            (+ -1 entry-limit)))
             0)
      (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c (car d-e-list))))
      (not-intersectp-list (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
                           (mv-nth 2
                                   (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                                          (+ -1 entry-limit))))
      (not (zp entry-limit))
      (useful-d-e-list-p d-e-list)
      (not (intersectp-equal x
                             (mv-nth 0 (d-e-cc fat32$c (car d-e-list))))))
     (lofat-place-file-spec-1
      d-e x entry-limit
      file path name d-e-list fat32$c
      (mv-nth
       0
       (hifat-place-file
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents fat32$c
                             (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
          entry-limit))
        path
        (m1-file-hifat-file-alist-fix d-e nil)))))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           lofat-place-file-spec-1))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-209
   (implies
    (and
     (hifat-equiv
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-place-file fat32$c (car d-e-list)
                                  path file))
        (make-d-e-list (mv-nth 0
                               (d-e-cc-contents fat32$c (car d-e-list))))
        entry-limit))
      (mv-nth
       0
       (hifat-place-file
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (+ -1 entry-limit)))
        path
        '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
          (contents)))))
     (equal
      (mv-nth
       1
       (hifat-place-file
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (+ -1 entry-limit)))
        path
        '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
          (contents))))
      0)
     (consp d-e-list)
     (d-e-directory-p (car d-e-list))
     (good-root-d-e-p root-d-e fat32$c)
     (equal (mv-nth 1
                    (d-e-cc-contents fat32$c (car d-e-list)))
            0)
     (equal
      (mv-nth
       3
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list (mv-nth 0
                               (d-e-cc-contents fat32$c (car d-e-list))))
        (+ -1 entry-limit)))
      0)
     (equal
      (mv-nth
       3
       (lofat-to-hifat-helper
        fat32$c (cdr d-e-list)
        (+
         -1 entry-limit
         (-
          (hifat-entry-count
           (mv-nth
            0
            (lofat-to-hifat-helper
             fat32$c
             (make-d-e-list (mv-nth 0
                                    (d-e-cc-contents fat32$c (car d-e-list))))
             (+ -1 entry-limit))))))))
      0)
     (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c (car d-e-list))))
     (not-intersectp-list
      (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
      (mv-nth
       2
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list (mv-nth 0
                               (d-e-cc-contents fat32$c (car d-e-list))))
        (+ -1 entry-limit))))
     (not-intersectp-list
      (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
      (mv-nth
       2
       (lofat-to-hifat-helper
        fat32$c (cdr d-e-list)
        (+
         -1 entry-limit
         (-
          (hifat-entry-count
           (mv-nth
            0
            (lofat-to-hifat-helper
             fat32$c
             (make-d-e-list (mv-nth 0
                                    (d-e-cc-contents fat32$c (car d-e-list))))
             (+ -1 entry-limit)))))))))
     (not
      (member-intersectp-equal
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit))))))))))
     (not (zp entry-limit))
     (<
      (+
       1
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (+ -1 entry-limit))))
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c (cdr d-e-list)
          (+
           -1 entry-limit
           (-
            (hifat-entry-count
             (mv-nth
              0
              (lofat-to-hifat-helper
               fat32$c
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (car d-e-list))))
               (+ -1 entry-limit))))))))))
      entry-limit)
     (useful-d-e-list-p d-e-list)
     (stobj-disjoins-list
      (mv-nth 0
              (lofat-place-file fat32$c (car d-e-list)
                                path file))
      (make-d-e-list (mv-nth 0
                             (d-e-cc-contents fat32$c (car d-e-list))))
      entry-limit
      (append
       x
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (flatten
        (set-difference-equal
         (mv-nth
          2
          (lofat-to-hifat-helper
           fat32$c (cdr d-e-list)
           (+
            -1 entry-limit
            (-
             (hifat-entry-count
              (mv-nth
               0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (car d-e-list))))
                (+ -1 entry-limit))))))))
         (mv-nth
          2
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit))))))))
    (hifat-equiv
     (cons
      (cons
       (d-e-filename (car d-e-list))
       (m1-file-hifat-file-alist-fix
        (car d-e-list)
        (mv-nth
         0
         (lofat-to-hifat-helper
          (mv-nth 0
                  (lofat-place-file fat32$c (car d-e-list)
                                    path file))
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (+ -1 entry-limit)))))
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-place-file fat32$c (car d-e-list)
                                  path file))
        (cdr d-e-list)
        (+
         -1 entry-limit
         (-
          (hifat-entry-count
           (mv-nth
            0
            (lofat-to-hifat-helper
             (mv-nth 0
                     (lofat-place-file fat32$c (car d-e-list)
                                       path file))
             (make-d-e-list
              (mv-nth 0
                      (d-e-cc-contents fat32$c (car d-e-list))))
             (+ -1 entry-limit)))))))))
     (cons
      (cons
       (d-e-filename (car d-e-list))
       (m1-file-hifat-file-alist-fix
        (car d-e-list)
        (mv-nth
         0
         (hifat-place-file
          (mv-nth
           0
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list (mv-nth 0
                                   (d-e-cc-contents fat32$c (car d-e-list))))
            (+ -1 entry-limit)))
          path
          (m1-file-hifat-file-alist-fix d-e nil)))))
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32$c (cdr d-e-list)
        (+
         -1 entry-limit
         (-
          (hifat-entry-count
           (mv-nth
            0
            (lofat-to-hifat-helper
             fat32$c
             (make-d-e-list
              (mv-nth 0
                      (d-e-cc-contents fat32$c (car d-e-list))))
             (+ -1 entry-limit)))))))))))
   :hints
   (("goal"
     :in-theory (e/d (not-intersectp-list hifat-entry-count
                                          lofat-to-hifat-helper-correctness-4
                                          stobj-disjoins-list find-d-e))
     :do-not-induct t
     :expand ((:free (fat32$c entry-limit)
                     (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
              (:free (x1 x2 y)
                     (not-intersectp-list x1 (cons x2 y)))
              (:free (d-e fat32$c d-e-list entry-limit)
                     (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                            entry-limit))
              (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-210
    (implies
     (and
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit)))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents))))
       0)
      (d-e-directory-p (car d-e-list))
      (equal (mv-nth 1
                     (lofat-place-file fat32$c (car d-e-list)
                                       path file))
             0)
      (good-root-d-e-p root-d-e fat32$c)
      (non-free-index-listp x (effective-fat fat32$c))
      (fat32-filename-list-p path)
      (not (equal (mv-nth 1
                          (find-d-e (cdr d-e-list)
                                    (d-e-filename (car d-e-list))))
                  0))
      (equal (mv-nth 1
                     (d-e-cc-contents fat32$c (car d-e-list)))
             0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit)))
       0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit))))))))
       0)
      (subdir-contents-p (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
      (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c (car d-e-list))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))
      (not
       (member-intersectp-equal
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (+ -1 entry-limit)))
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c (cdr d-e-list)
          (+
           -1 entry-limit
           (-
            (hifat-entry-count
             (mv-nth
              0
              (lofat-to-hifat-helper
               fat32$c
               (make-d-e-list (mv-nth 0
                                      (d-e-cc-contents fat32$c (car d-e-list))))
               (+ -1 entry-limit))))))))))
      (lofat-file-p file)
      (not (zp entry-limit))
      (<
       (+
        1
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit))))
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c (cdr d-e-list)
           (+
            -1 entry-limit
            (-
             (hifat-entry-count
              (mv-nth
               0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (car d-e-list))))
                (+ -1 entry-limit))))))))))
       entry-limit)
      (useful-d-e-list-p d-e-list)
      (not (intersectp-equal x
                             (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))))
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit))))
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))
      (consp (cdr path))
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-place-file fat32$c (car d-e-list)
                                 path file))
       (make-d-e-list (mv-nth 0
                              (d-e-cc-contents fat32$c (car d-e-list))))
       entry-limit
       (append
        x
        (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
        (flatten
         (set-difference-equal
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c (cdr d-e-list)
            (+
             -1 entry-limit
             (-
              (hifat-entry-count
               (mv-nth
                0
                (lofat-to-hifat-helper
                 fat32$c
                 (make-d-e-list
                  (mv-nth 0
                          (d-e-cc-contents fat32$c (car d-e-list))))
                 (+ -1 entry-limit))))))))
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list (mv-nth 0
                                   (d-e-cc-contents fat32$c (car d-e-list))))
            (+ -1 entry-limit)))))))
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c (car d-e-list)
                                   path file))
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         entry-limit))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit)))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents))))))
     (stobj-disjoins-list (mv-nth 0
                                  (lofat-place-file fat32$c (car d-e-list)
                                                    path file))
                          d-e-list entry-limit x))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           stobj-disjoins-list))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-180
    (implies
     (and
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c (car d-e-list)
                                   path file))
         (place-d-e
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (d-e-set-first-cluster-file-size
           (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                      t)
           (nth 0
                (find-n-free-clusters (effective-fat fat32$c)
                                      1))
           0))
         entry-limit))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit)))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents)))))
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit)))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents))))
       0)
      (consp d-e-list)
      (d-e-directory-p (car d-e-list))
      (good-root-d-e-p root-d-e fat32$c)
      (fat32-filename-list-p path)
      (equal (mv-nth 1
                     (d-e-cc-contents fat32$c (car d-e-list)))
             0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit)))
       0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit))))))))
       0)
      (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c (car d-e-list))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))
      (not
       (member-intersectp-equal
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (+ -1 entry-limit)))
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c (cdr d-e-list)
          (+
           -1 entry-limit
           (-
            (hifat-entry-count
             (mv-nth
              0
              (lofat-to-hifat-helper
               fat32$c
               (make-d-e-list (mv-nth 0
                                      (d-e-cc-contents fat32$c (car d-e-list))))
               (+ -1 entry-limit))))))))))
      (consp path)
      (not (zp entry-limit))
      (<
       (+
        1
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit))))
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c (cdr d-e-list)
           (+
            -1 entry-limit
            (-
             (hifat-entry-count
              (mv-nth
               0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (car d-e-list))))
                (+ -1 entry-limit))))))))))
       entry-limit)
      (useful-d-e-list-p d-e-list)
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-place-file fat32$c (car d-e-list)
                                 path file))
       (place-d-e
        (make-d-e-list (mv-nth 0
                               (d-e-cc-contents fat32$c (car d-e-list))))
        (d-e-set-first-cluster-file-size
         (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                    t)
         (nth 0
              (find-n-free-clusters (effective-fat fat32$c)
                                    1))
         0))
       entry-limit
       (append
        x
        (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
        (flatten
         (set-difference-equal
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c (cdr d-e-list)
            (+
             -1 entry-limit
             (-
              (hifat-entry-count
               (mv-nth
                0
                (lofat-to-hifat-helper
                 fat32$c
                 (make-d-e-list
                  (mv-nth 0
                          (d-e-cc-contents fat32$c (car d-e-list))))
                 (+ -1 entry-limit))))))))
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list (mv-nth 0
                                   (d-e-cc-contents fat32$c (car d-e-list))))
            (+ -1 entry-limit))))))))
     (hifat-equiv
      (cons
       (cons
        (d-e-filename (car d-e-list))
        (m1-file-hifat-file-alist-fix
         (car d-e-list)
         (mv-nth
          0
          (lofat-to-hifat-helper
           (mv-nth 0
                   (lofat-place-file fat32$c (car d-e-list)
                                     path file))
           (place-d-e
            (make-d-e-list (mv-nth 0
                                   (d-e-cc-contents fat32$c (car d-e-list))))
            (d-e-set-first-cluster-file-size
             (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                        t)
             (nth 0
                  (find-n-free-clusters (effective-fat fat32$c)
                                        1))
             0))
           (+ -1 entry-limit)))))
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c (car d-e-list)
                                   path file))
         (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              (mv-nth 0
                      (lofat-place-file fat32$c (car d-e-list)
                                        path file))
              (place-d-e
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (car d-e-list))))
               (d-e-set-first-cluster-file-size
                (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                           t)
                (nth 0
                     (find-n-free-clusters (effective-fat fat32$c)
                                           1))
                0))
              (+ -1 entry-limit)))))))))
      (cons
       (cons
        (d-e-filename (car d-e-list))
        (m1-file-hifat-file-alist-fix
         (car d-e-list)
         (mv-nth
          0
          (hifat-place-file
           (mv-nth
            0
            (lofat-to-hifat-helper
             fat32$c
             (make-d-e-list (mv-nth 0
                                    (d-e-cc-contents fat32$c (car d-e-list))))
             (+ -1 entry-limit)))
           path
           (m1-file-hifat-file-alist-fix d-e nil)))))
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           stobj-disjoins-list))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-183
    (implies
     (and
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit)))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents))))
       0)
      (d-e-directory-p (car d-e-list))
      (equal (mv-nth 1
                     (lofat-place-file fat32$c (car d-e-list)
                                       path file))
             0)
      (good-root-d-e-p root-d-e fat32$c)
      (non-free-index-listp x (effective-fat fat32$c))
      (fat32-filename-list-p path)
      (not (equal (mv-nth 1
                          (find-d-e (cdr d-e-list)
                                    (d-e-filename (car d-e-list))))
                  0))
      (equal (mv-nth 1
                     (d-e-cc-contents fat32$c (car d-e-list)))
             0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit)))
       0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit))))))))
       0)
      (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c (car d-e-list))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))
      (not
       (member-intersectp-equal
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (+ -1 entry-limit)))
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c (cdr d-e-list)
          (+
           -1 entry-limit
           (-
            (hifat-entry-count
             (mv-nth
              0
              (lofat-to-hifat-helper
               fat32$c
               (make-d-e-list (mv-nth 0
                                      (d-e-cc-contents fat32$c (car d-e-list))))
               (+ -1 entry-limit))))))))))
      (lofat-file-p file)
      (<= 1
          (count-free-clusters (effective-fat fat32$c)))
      (consp path)
      (not (zp entry-limit))
      (<
       (+
        1
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit))))
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c (cdr d-e-list)
           (+
            -1 entry-limit
            (-
             (hifat-entry-count
              (mv-nth
               0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (car d-e-list))))
                (+ -1 entry-limit))))))))))
       entry-limit)
      (useful-d-e-list-p d-e-list)
      (not (intersectp-equal x
                             (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))))
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit))))
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))
      (not (consp (cdr path)))
      (lofat-directory-file-p file)
      (not
       (equal
        (mv-nth
         1
         (find-d-e
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (car path)))
        0))
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-place-file fat32$c (car d-e-list)
                                 path file))
       (place-d-e
        (make-d-e-list (mv-nth 0
                               (d-e-cc-contents fat32$c (car d-e-list))))
        (d-e-set-first-cluster-file-size
         (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                    t)
         (nth 0
              (find-n-free-clusters (effective-fat fat32$c)
                                    1))
         0))
       entry-limit
       (append
        x
        (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
        (flatten
         (set-difference-equal
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c (cdr d-e-list)
            (+
             -1 entry-limit
             (-
              (hifat-entry-count
               (mv-nth
                0
                (lofat-to-hifat-helper
                 fat32$c
                 (make-d-e-list
                  (mv-nth 0
                          (d-e-cc-contents fat32$c (car d-e-list))))
                 (+ -1 entry-limit))))))))
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list (mv-nth 0
                                   (d-e-cc-contents fat32$c (car d-e-list))))
            (+ -1 entry-limit)))))))
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c (car d-e-list)
                                   path file))
         (place-d-e
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (d-e-set-first-cluster-file-size
           (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                      t)
           (nth 0
                (find-n-free-clusters (effective-fat fat32$c)
                                      1))
           0))
         entry-limit))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit)))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents))))))
     (stobj-disjoins-list (mv-nth 0
                                  (lofat-place-file fat32$c (car d-e-list)
                                                    path file))
                          d-e-list entry-limit x))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           stobj-disjoins-list))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-184
    (implies
     (and
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c (car d-e-list)
                                   path file))
         (place-d-e
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (d-e-set-first-cluster-file-size
           (mv-nth
            0
            (find-d-e
             (make-d-e-list (mv-nth 0
                                    (d-e-cc-contents fat32$c (car d-e-list))))
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
                   (mv-nth 0
                           (d-e-cc-contents fat32$c (car d-e-list))))
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
                             (d-e-cc-contents fat32$c (car d-e-list))))
                    (car path))))))
               0 nil))
             1))
           0))
         entry-limit))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit)))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents)))))
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit)))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents))))
       0)
      (consp d-e-list)
      (d-e-directory-p (car d-e-list))
      (good-root-d-e-p root-d-e fat32$c)
      (fat32-filename-list-p path)
      (equal (mv-nth 1
                     (d-e-cc-contents fat32$c (car d-e-list)))
             0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit)))
       0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit))))))))
       0)
      (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c (car d-e-list))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))
      (not
       (member-intersectp-equal
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (+ -1 entry-limit)))
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c (cdr d-e-list)
          (+
           -1 entry-limit
           (-
            (hifat-entry-count
             (mv-nth
              0
              (lofat-to-hifat-helper
               fat32$c
               (make-d-e-list (mv-nth 0
                                      (d-e-cc-contents fat32$c (car d-e-list))))
               (+ -1 entry-limit))))))))))
      (consp path)
      (not (zp entry-limit))
      (<
       (+
        1
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit))))
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c (cdr d-e-list)
           (+
            -1 entry-limit
            (-
             (hifat-entry-count
              (mv-nth
               0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (car d-e-list))))
                (+ -1 entry-limit))))))))))
       entry-limit)
      (useful-d-e-list-p d-e-list)
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-place-file fat32$c (car d-e-list)
                                 path file))
       (place-d-e
        (make-d-e-list (mv-nth 0
                               (d-e-cc-contents fat32$c (car d-e-list))))
        (d-e-set-first-cluster-file-size
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
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
               (find-d-e (make-d-e-list
                          (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
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
                           (d-e-cc-contents fat32$c (car d-e-list))))
                  (car path))))))
             0 nil))
           1))
         0))
       entry-limit
       (append
        x
        (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
        (flatten
         (set-difference-equal
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c (cdr d-e-list)
            (+
             -1 entry-limit
             (-
              (hifat-entry-count
               (mv-nth
                0
                (lofat-to-hifat-helper
                 fat32$c
                 (make-d-e-list
                  (mv-nth 0
                          (d-e-cc-contents fat32$c (car d-e-list))))
                 (+ -1 entry-limit))))))))
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list (mv-nth 0
                                   (d-e-cc-contents fat32$c (car d-e-list))))
            (+ -1 entry-limit)))))))
      (equal
       (mv-nth
        1
        (find-d-e
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (car path)))
       0))
     (hifat-equiv
      (cons
       (cons
        (d-e-filename (car d-e-list))
        (m1-file-hifat-file-alist-fix
         (car d-e-list)
         (mv-nth
          0
          (lofat-to-hifat-helper
           (mv-nth 0
                   (lofat-place-file fat32$c (car d-e-list)
                                     path file))
           (place-d-e
            (make-d-e-list (mv-nth 0
                                   (d-e-cc-contents fat32$c (car d-e-list))))
            (d-e-set-first-cluster-file-size
             (mv-nth
              0
              (find-d-e
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (car d-e-list))))
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
                     (mv-nth 0
                             (d-e-cc-contents fat32$c (car d-e-list))))
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
                               (d-e-cc-contents fat32$c (car d-e-list))))
                      (car path))))))
                 0 nil))
               1))
             0))
           (+ -1 entry-limit)))))
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c (car d-e-list)
                                   path file))
         (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              (mv-nth 0
                      (lofat-place-file fat32$c (car d-e-list)
                                        path file))
              (place-d-e
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (car d-e-list))))
               (d-e-set-first-cluster-file-size
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list
                   (mv-nth 0
                           (d-e-cc-contents fat32$c (car d-e-list))))
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
                        (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
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
                                  (d-e-cc-contents fat32$c (car d-e-list))))
                         (car path))))))
                    0 nil))
                  1))
                0))
              (+ -1 entry-limit)))))))))
      (cons
       (cons
        (d-e-filename (car d-e-list))
        (m1-file-hifat-file-alist-fix
         (car d-e-list)
         (mv-nth
          0
          (hifat-place-file
           (mv-nth
            0
            (lofat-to-hifat-helper
             fat32$c
             (make-d-e-list (mv-nth 0
                                    (d-e-cc-contents fat32$c (car d-e-list))))
             (+ -1 entry-limit)))
           path
           (m1-file-hifat-file-alist-fix d-e nil)))))
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           stobj-disjoins-list))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-194
    (implies
     (and
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit)))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents))))
       0)
      (d-e-directory-p (car d-e-list))
      (equal (mv-nth 1
                     (lofat-place-file fat32$c (car d-e-list)
                                       path file))
             0)
      (good-root-d-e-p root-d-e fat32$c)
      (non-free-index-listp x (effective-fat fat32$c))
      (fat32-filename-list-p path)
      (not (equal (mv-nth 1
                          (find-d-e (cdr d-e-list)
                                    (d-e-filename (car d-e-list))))
                  0))
      (equal (mv-nth 1
                     (d-e-cc-contents fat32$c (car d-e-list)))
             0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit)))
       0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit))))))))
       0)
      (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c (car d-e-list))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))
      (not
       (member-intersectp-equal
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (+ -1 entry-limit)))
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c (cdr d-e-list)
          (+
           -1 entry-limit
           (-
            (hifat-entry-count
             (mv-nth
              0
              (lofat-to-hifat-helper
               fat32$c
               (make-d-e-list (mv-nth 0
                                      (d-e-cc-contents fat32$c (car d-e-list))))
               (+ -1 entry-limit))))))))))
      (lofat-file-p file)
      (consp path)
      (not (zp entry-limit))
      (<
       (+
        1
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit))))
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c (cdr d-e-list)
           (+
            -1 entry-limit
            (-
             (hifat-entry-count
              (mv-nth
               0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (car d-e-list))))
                (+ -1 entry-limit))))))))))
       entry-limit)
      (useful-d-e-list-p d-e-list)
      (not (intersectp-equal x
                             (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))))
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit))))
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))
      (not (consp (cdr path)))
      (lofat-directory-file-p file)
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-place-file fat32$c (car d-e-list)
                                 path file))
       (place-d-e
        (make-d-e-list (mv-nth 0
                               (d-e-cc-contents fat32$c (car d-e-list))))
        (d-e-set-first-cluster-file-size
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
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
               (find-d-e (make-d-e-list
                          (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
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
                           (d-e-cc-contents fat32$c (car d-e-list))))
                  (car path))))))
             0 nil))
           1))
         0))
       entry-limit
       (append
        x
        (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
        (flatten
         (set-difference-equal
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c (cdr d-e-list)
            (+
             -1 entry-limit
             (-
              (hifat-entry-count
               (mv-nth
                0
                (lofat-to-hifat-helper
                 fat32$c
                 (make-d-e-list
                  (mv-nth 0
                          (d-e-cc-contents fat32$c (car d-e-list))))
                 (+ -1 entry-limit))))))))
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list (mv-nth 0
                                   (d-e-cc-contents fat32$c (car d-e-list))))
            (+ -1 entry-limit)))))))
      (equal
       (mv-nth
        1
        (find-d-e
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (car path)))
       0)
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c (car d-e-list)
                                   path file))
         (place-d-e
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (d-e-set-first-cluster-file-size
           (mv-nth
            0
            (find-d-e
             (make-d-e-list (mv-nth 0
                                    (d-e-cc-contents fat32$c (car d-e-list))))
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
                   (mv-nth 0
                           (d-e-cc-contents fat32$c (car d-e-list))))
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
                             (d-e-cc-contents fat32$c (car d-e-list))))
                    (car path))))))
               0 nil))
             1))
           0))
         entry-limit))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit)))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents))))))
     (stobj-disjoins-list (mv-nth 0
                                  (lofat-place-file fat32$c (car d-e-list)
                                                    path file))
                          d-e-list entry-limit x))
    :hints
    (("goal"
      :in-theory
      (e/d (not-intersectp-list hifat-entry-count
                                lofat-to-hifat-helper-correctness-4
                                stobj-disjoins-list
                                member-intersectp-of-set-difference$-1))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-199
    (implies
     (and
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit)))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents))))
       0)
      (d-e-directory-p (car d-e-list))
      (equal (mv-nth 1
                     (lofat-place-file fat32$c (car d-e-list)
                                       path file))
             0)
      (good-root-d-e-p root-d-e fat32$c)
      (non-free-index-listp x (effective-fat fat32$c))
      (fat32-filename-list-p path)
      (not (equal (mv-nth 1
                          (find-d-e (cdr d-e-list)
                                    (d-e-filename (car d-e-list))))
                  0))
      (equal (mv-nth 1
                     (d-e-cc-contents fat32$c (car d-e-list)))
             0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit)))
       0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit))))))))
       0)
      (subdir-contents-p (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
      (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c (car d-e-list))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))
      (not
       (member-intersectp-equal
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (+ -1 entry-limit)))
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c (cdr d-e-list)
          (+
           -1 entry-limit
           (-
            (hifat-entry-count
             (mv-nth
              0
              (lofat-to-hifat-helper
               fat32$c
               (make-d-e-list (mv-nth 0
                                      (d-e-cc-contents fat32$c (car d-e-list))))
               (+ -1 entry-limit))))))))))
      (lofat-file-p file)
      (not (lofat-file->contents file))
      (<= 1
          (count-free-clusters (effective-fat fat32$c)))
      (consp path)
      (not (zp entry-limit))
      (<
       (+
        1
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit))))
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c (cdr d-e-list)
           (+
            -1 entry-limit
            (-
             (hifat-entry-count
              (mv-nth
               0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (car d-e-list))))
                (+ -1 entry-limit))))))))))
       entry-limit)
      (useful-d-e-list-p d-e-list)
      (not (intersectp-equal x
                             (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))))
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit))))
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit))))))))))
     (lofat-place-file-spec-1
      d-e x entry-limit
      file path (d-e-filename (car d-e-list))
      d-e-list fat32$c
      (mv-nth
       0
       (hifat-place-file
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (+ -1 entry-limit)))
        path
        (m1-file-hifat-file-alist-fix d-e nil)))))
    :hints
    (("goal"
      :in-theory
      (e/d (not-intersectp-list hifat-entry-count
                                lofat-to-hifat-helper-correctness-4
                                lofat-place-file-spec-1 find-d-e)
           ((:rewrite lofat-to-hifat-helper-of-lofat-place-file-disjoint)
            (:definition member-intersectp-equal)
            (:definition hifat-entry-count)
            (:rewrite lofat-place-file-correctness-lemma-83)
            (:rewrite member-intersectp-is-commutative)
            (:rewrite lofat-place-file-correctness-lemma-121
                      . 2)
            (:rewrite lofat-place-file-correctness-lemma-121
                      . 1)
            (:rewrite lofat-place-file-correctness-lemma-52)
            (:rewrite subsetp-cons-2)))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-200
    (implies
     (and
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c
                                   (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                   path file))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
            (mv-nth 0
                    (lofat-place-file fat32$c
                                      (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                      path file))
            (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
         entry-limit))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents)))))
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents))))
       0)
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                            (+ -1 entry-limit)))
             0)
      (not (zp entry-limit))
      (useful-d-e-list-p d-e-list)
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth 0
                  (lofat-place-file fat32$c
                                    (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                    path file))
          (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
       entry-limit
       (append
        x
        (flatten
         (set-difference-equal
          (mv-nth 2
                  (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                         (+ -1 entry-limit)))
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth
              0
              (d-e-cc-contents fat32$c
                               (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
            entry-limit)))))))
     (hifat-equiv
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-place-file fat32$c
                                  (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                  path file))
        (make-d-e-list
         (mv-nth
          0
          (d-e-cc-contents
           (mv-nth 0
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                     path file))
           (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
        (+ -1 entry-limit)))
      (mv-nth
       0
       (hifat-place-file
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents fat32$c
                             (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
          (+ -1 entry-limit)))
        path
        '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
          (contents))))))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           stobj-disjoins-list find-d-e))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-202
    (implies
     (and
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents))))
       0)
      (<= (+ 2 (count-of-clusters fat32$c))
          (d-e-first-cluster (car d-e-list)))
      (lofat-place-file-spec-1
       d-e x (+ -1 entry-limit)
       file path name (cdr d-e-list)
       fat32$c
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           (+ -1 entry-limit)))
         path
         (m1-file-hifat-file-alist-fix d-e nil))))
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (not (d-e-directory-p (car d-e-list)))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                            (+ -1 entry-limit)))
             0)
      (not (zp entry-limit))
      (not (equal (mv-nth 1
                          (find-d-e (cdr d-e-list)
                                    (d-e-filename (car d-e-list))))
                  0))
      (<
       (+
        1
        (hifat-entry-count (mv-nth 0
                                   (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                                          (+ -1 entry-limit)))))
       entry-limit)
      (useful-d-e-list-p d-e-list))
     (lofat-place-file-spec-1
      d-e x entry-limit
      file path name d-e-list fat32$c
      (mv-nth
       0
       (hifat-place-file
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents fat32$c
                             (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
          entry-limit))
        path
        (m1-file-hifat-file-alist-fix d-e nil)))))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           lofat-place-file-spec-1 find-d-e))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-203
    (implies
     (and
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth 0
                  (lofat-place-file fat32$c
                                    (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                    path file))
          (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
       entry-limit
       (append
        x
        (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
        (flatten
         (set-difference-equal
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list (mv-nth 0
                                   (d-e-cc-contents fat32$c (car d-e-list))))
            (+ -1 entry-limit)))
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth
              0
              (d-e-cc-contents fat32$c
                               (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
            entry-limit))))
        (flatten
         (set-difference-equal
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c (cdr d-e-list)
            (+
             -1 entry-limit
             (-
              (hifat-entry-count
               (mv-nth
                0
                (lofat-to-hifat-helper
                 fat32$c
                 (make-d-e-list
                  (mv-nth 0
                          (d-e-cc-contents fat32$c (car d-e-list))))
                 (+ -1 entry-limit))))))))
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth
              0
              (d-e-cc-contents fat32$c
                               (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
            entry-limit))))))
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c
                                   (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                   path file))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
            (mv-nth 0
                    (lofat-place-file fat32$c
                                      (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                      path file))
            (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
         entry-limit))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents)))))
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents))))
       0)
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit))))))))
       0)
      (not
       (member-intersectp-equal
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (+ -1 entry-limit)))
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c (cdr d-e-list)
          (+
           -1 entry-limit
           (-
            (hifat-entry-count
             (mv-nth
              0
              (lofat-to-hifat-helper
               fat32$c
               (make-d-e-list (mv-nth 0
                                      (d-e-cc-contents fat32$c (car d-e-list))))
               (+ -1 entry-limit))))))))))
      (not (zp entry-limit))
      (useful-d-e-list-p d-e-list))
     (stobj-disjoins-list
      (mv-nth 0
              (lofat-place-file fat32$c
                                (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                path file))
      (make-d-e-list
       (mv-nth
        0
        (d-e-cc-contents
         (mv-nth 0
                 (lofat-place-file fat32$c
                                   (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                   path file))
         (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
      (+
       -1 entry-limit
       (-
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit))))))
      (append
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (flatten
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (+ -1 entry-limit))))
       x
       (flatten
        (set-difference-equal
         (mv-nth
          2
          (lofat-to-hifat-helper
           fat32$c (cdr d-e-list)
           (+
            -1 entry-limit
            (-
             (hifat-entry-count
              (mv-nth
               0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (car d-e-list))))
                (+ -1 entry-limit))))))))
         (mv-nth
          2
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           (+
            -1 entry-limit
            (-
             (hifat-entry-count
              (mv-nth
               0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (car d-e-list))))
                (+ -1 entry-limit)))))))))))))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           stobj-disjoins-list find-d-e))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-204
    (implies
     (and
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth 0
                  (lofat-place-file fat32$c
                                    (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                    path file))
          (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
       entry-limit
       (append
        x
        (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
        (flatten
         (set-difference-equal
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list (mv-nth 0
                                   (d-e-cc-contents fat32$c (car d-e-list))))
            (+ -1 entry-limit)))
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth
              0
              (d-e-cc-contents fat32$c
                               (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
            entry-limit))))
        (flatten
         (set-difference-equal
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c (cdr d-e-list)
            (+
             -1 entry-limit
             (-
              (hifat-entry-count
               (mv-nth
                0
                (lofat-to-hifat-helper
                 fat32$c
                 (make-d-e-list
                  (mv-nth 0
                          (d-e-cc-contents fat32$c (car d-e-list))))
                 (+ -1 entry-limit))))))))
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth
              0
              (d-e-cc-contents fat32$c
                               (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
            entry-limit))))))
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c
                                   (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                   path file))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
            (mv-nth 0
                    (lofat-place-file fat32$c
                                      (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                      path file))
            (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
         entry-limit))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents)))))
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents))))
       0)
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit))))))))
       0)
      (not (zp entry-limit))
      (useful-d-e-list-p d-e-list))
     (hifat-equiv
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-place-file fat32$c
                                  (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                  path file))
        (make-d-e-list
         (mv-nth
          0
          (d-e-cc-contents
           (mv-nth 0
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                     path file))
           (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
        (+
         -1 entry-limit
         (-
          (hifat-entry-count
           (mv-nth
            0
            (lofat-to-hifat-helper
             fat32$c
             (make-d-e-list (mv-nth 0
                                    (d-e-cc-contents fat32$c (car d-e-list))))
             (+ -1 entry-limit))))))))
      (mv-nth
       0
       (hifat-place-file
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents fat32$c
                             (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
          (+
           -1 entry-limit
           (-
            (hifat-entry-count
             (mv-nth
              0
              (lofat-to-hifat-helper
               fat32$c
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (car d-e-list))))
               (+ -1 entry-limit))))))))
        path
        '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
          (contents))))))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           stobj-disjoins-list find-d-e))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-206
    (implies
     (and
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents))))
       0)
      (d-e-directory-p (car d-e-list))
      (lofat-place-file-spec-1
       d-e
       (append
        (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
        (flatten
         (mv-nth
          2
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit))))
        x)
       (+
        -1 entry-limit
        (-
         (hifat-entry-count
          (mv-nth
           0
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list (mv-nth 0
                                   (d-e-cc-contents fat32$c (car d-e-list))))
            (+ -1 entry-limit))))))
       file path name (cdr d-e-list)
       fat32$c
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           (+
            -1 entry-limit
            (-
             (hifat-entry-count
              (mv-nth
               0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (car d-e-list))))
                (+ -1 entry-limit))))))))
         path
         (m1-file-hifat-file-alist-fix d-e nil))))
      (not (equal (d-e-filename (car d-e-list))
                  name))
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (good-root-d-e-p root-d-e fat32$c)
      (not (equal (mv-nth 1
                          (find-d-e (cdr d-e-list)
                                    (d-e-filename (car d-e-list))))
                  0))
      (equal (mv-nth 1
                     (d-e-cc-contents fat32$c (car d-e-list)))
             0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit)))
       0)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit))))))))
       0)
      (subdir-contents-p (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
      (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c (car d-e-list))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c (cdr d-e-list)
         (+
          -1 entry-limit
          (-
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))
      (not
       (member-intersectp-equal
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (+ -1 entry-limit)))
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c (cdr d-e-list)
          (+
           -1 entry-limit
           (-
            (hifat-entry-count
             (mv-nth
              0
              (lofat-to-hifat-helper
               fat32$c
               (make-d-e-list (mv-nth 0
                                      (d-e-cc-contents fat32$c (car d-e-list))))
               (+ -1 entry-limit))))))))))
      (not (zp entry-limit))
      (<
       (+
        1
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit))))
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c (cdr d-e-list)
           (+
            -1 entry-limit
            (-
             (hifat-entry-count
              (mv-nth
               0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (car d-e-list))))
                (+ -1 entry-limit))))))))))
       entry-limit)
      (useful-d-e-list-p d-e-list)
      (not (intersectp-equal x
                             (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))))
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit)))))
     (lofat-place-file-spec-1
      d-e x entry-limit
      file path name d-e-list fat32$c
      (mv-nth
       0
       (hifat-place-file
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents fat32$c
                             (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
          entry-limit))
        path
        (m1-file-hifat-file-alist-fix d-e nil)))))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           lofat-place-file-spec-1 find-d-e))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-208
    (implies
     (and
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           entry-limit))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents))))
       0)
      (not (d-e-directory-p (car d-e-list)))
      (< (d-e-first-cluster (car d-e-list)) 2)
      (lofat-place-file-spec-1
       d-e x (+ -1 entry-limit)
       file path name (cdr d-e-list)
       fat32$c
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
           (+ -1 entry-limit)))
         path
         (m1-file-hifat-file-alist-fix d-e nil))))
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (not (equal (mv-nth 1
                          (find-d-e (cdr d-e-list)
                                    (d-e-filename (car d-e-list))))
                  0))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                            (+ -1 entry-limit)))
             0)
      (not (zp entry-limit))
      (<
       (+
        1
        (hifat-entry-count (mv-nth 0
                                   (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                                          (+ -1 entry-limit)))))
       entry-limit)
      (useful-d-e-list-p d-e-list))
     (lofat-place-file-spec-1
      d-e x entry-limit
      file path name d-e-list fat32$c
      (mv-nth
       0
       (hifat-place-file
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents fat32$c
                             (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
          entry-limit))
        path
        (m1-file-hifat-file-alist-fix d-e nil)))))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4
                                           lofat-place-file-spec-1 find-d-e))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  ;; hypotheses are minimised.
  (defthmd
    lofat-place-file-correctness-lemma-143
    (implies
     (and
      (equal (mv-nth 1
                     (lofat-place-file fat32$c
                                       (mv-nth 0 (find-d-e d-e-list name))
                                       path file))
             0)
      (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))
      (good-root-d-e-p root-d-e fat32$c)
      (non-free-index-listp x (effective-fat fat32$c))
      (fat32-filename-list-p path)
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
             0)
      (lofat-file-p file)
      (not (lofat-file->contents file))
      (<= 1
          (count-free-clusters (effective-fat fat32$c)))
      (consp path)
      (< (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
         entry-limit)
      (useful-d-e-list-p d-e-list)
      (zp
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents fat32$c
                                     (mv-nth 0 (find-d-e d-e-list name)))))
           entry-limit))
         path (m1-file d-e nil))))
      (not-intersectp-list
       x
       (mv-nth 2
               (lofat-to-hifat-helper fat32$c d-e-list entry-limit))))
     (lofat-place-file-spec-1
      d-e x entry-limit
      file path name d-e-list fat32$c
      (mv-nth
       0
       (hifat-place-file
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c
                                    (mv-nth 0 (find-d-e d-e-list name)))))
          entry-limit))
        path (m1-file d-e nil)))))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4))
      :induct (induction-scheme d-e-list entry-limit fat32$c x)
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name))))
    :rule-classes
    ((:rewrite
      :corollary
      (implies
       (and
        (equal (mv-nth 1
                       (lofat-place-file fat32$c
                                         (mv-nth 0 (find-d-e d-e-list name))
                                         path file))
               0)
        (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))
        (equal
         (mv-nth
          3
          (lofat-to-hifat-helper
           (mv-nth 0
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e d-e-list name))
                                     path file))
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents
              (mv-nth 0
                      (lofat-place-file fat32$c
                                        (mv-nth 0 (find-d-e d-e-list name))
                                        path file))
              (mv-nth 0 (find-d-e d-e-list name)))))
           entry-limit))
         0)
        (not-intersectp-list
         x
         (mv-nth
          2
          (lofat-to-hifat-helper
           (mv-nth 0
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e d-e-list name))
                                     path file))
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents
              (mv-nth 0
                      (lofat-place-file fat32$c
                                        (mv-nth 0 (find-d-e d-e-list name))
                                        path file))
              (mv-nth 0 (find-d-e d-e-list name)))))
           entry-limit)))
        (not
         (member-intersectp-equal
          (set-difference-equal
           (mv-nth 2
                   (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
           (mv-nth
            2
            (lofat-to-hifat-helper
             fat32$c
             (make-d-e-list
              (mv-nth 0
                      (d-e-cc-contents fat32$c
                                       (mv-nth 0 (find-d-e d-e-list name)))))
             entry-limit)))
          (mv-nth
           2
           (lofat-to-hifat-helper
            (mv-nth 0
                    (lofat-place-file fat32$c
                                      (mv-nth 0 (find-d-e d-e-list name))
                                      path file))
            (make-d-e-list
             (mv-nth
              0
              (d-e-cc-contents
               (mv-nth 0
                       (lofat-place-file fat32$c
                                         (mv-nth 0 (find-d-e d-e-list name))
                                         path file))
               (mv-nth 0 (find-d-e d-e-list name)))))
            entry-limit))))
        (hifat-equiv
         (mv-nth
          0
          (lofat-to-hifat-helper
           (mv-nth 0
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e d-e-list name))
                                     path file))
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents
              (mv-nth 0
                      (lofat-place-file fat32$c
                                        (mv-nth 0 (find-d-e d-e-list name))
                                        path file))
              (mv-nth 0 (find-d-e d-e-list name)))))
           entry-limit))
         (mv-nth
          0
          (hifat-place-file
           (mv-nth
            0
            (lofat-to-hifat-helper
             fat32$c
             (make-d-e-list
              (mv-nth 0
                      (d-e-cc-contents fat32$c
                                       (mv-nth 0 (find-d-e d-e-list name)))))
             entry-limit))
           path (m1-file d-e nil))))
        (good-root-d-e-p root-d-e fat32$c)
        (non-free-index-listp x (effective-fat fat32$c))
        (fat32-filename-list-p path)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               0)
        (lofat-file-p file)
        (not (lofat-file->contents file))
        (<= 1
            (count-free-clusters (effective-fat fat32$c)))
        (consp path)
        (< (hifat-entry-count
            (mv-nth 0
                    (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
           entry-limit)
        (useful-d-e-list-p d-e-list)
        (zp
         (mv-nth
          1
          (hifat-place-file
           (mv-nth
            0
            (lofat-to-hifat-helper
             fat32$c
             (make-d-e-list
              (mv-nth 0
                      (d-e-cc-contents fat32$c
                                       (mv-nth 0 (find-d-e d-e-list name)))))
             entry-limit))
           path (m1-file d-e nil))))
        (not-intersectp-list
         x
         (mv-nth 2
                 (lofat-to-hifat-helper fat32$c d-e-list entry-limit))))
       (not-intersectp-list
        x
        (mv-nth
         2
         (lofat-to-hifat-helper
          (mv-nth 0
                  (lofat-place-file fat32$c
                                    (mv-nth 0 (find-d-e d-e-list name))
                                    path file))
          d-e-list entry-limit))))
      :hints
      (("goal" :do-not-induct t
        :in-theory (e/d (stobj-disjoins-list lofat-place-file-spec-1)
                        (lofat-place-file))))))))

(defthm
  lofat-place-file-correctness-lemma-144
  (implies
   (and
    (equal (mv-nth 1
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e d-e-list name))
                                     path file))
           0)
    (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e d-e-list name))
                                 path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth 0
                  (lofat-place-file fat32$c
                                    (mv-nth 0 (find-d-e d-e-list name))
                                    path file))
          (mv-nth 0 (find-d-e d-e-list name)))))
       entry-limit))
     0)
    (not
     (member-intersectp-equal
      (set-difference-equal
       (mv-nth 2
               (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c
                                   (mv-nth 0 (find-d-e d-e-list name)))))
         entry-limit)))
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-place-file fat32$c
                                  (mv-nth 0 (find-d-e d-e-list name))
                                  path file))
        (make-d-e-list
         (mv-nth
          0
          (d-e-cc-contents
           (mv-nth 0
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e d-e-list name))
                                     path file))
           (mv-nth 0 (find-d-e d-e-list name)))))
        entry-limit))))
    (hifat-equiv
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e d-e-list name))
                                 path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth 0
                  (lofat-place-file fat32$c
                                    (mv-nth 0 (find-d-e d-e-list name))
                                    path file))
          (mv-nth 0 (find-d-e d-e-list name)))))
       entry-limit))
     (mv-nth
      0
      (hifat-place-file
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c
                                   (mv-nth 0 (find-d-e d-e-list name)))))
         entry-limit))
       path (m1-file (d-e-fix nil) nil))))
    (good-root-d-e-p root-d-e fat32$c)
    (fat32-filename-list-p path)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
           0)
    (lofat-file-p file)
    (not (lofat-file->contents file))
    (<= 1
        (count-free-clusters (effective-fat fat32$c)))
    (consp path)
    (< (hifat-entry-count
        (mv-nth 0
                (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
       entry-limit)
    (useful-d-e-list-p d-e-list)
    (zp
     (mv-nth
      1
      (hifat-place-file
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c
                                   (mv-nth 0 (find-d-e d-e-list name)))))
         entry-limit))
       path (m1-file (d-e-fix nil) nil)))))
   (and
    (hifat-equiv
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e d-e-list name))
                                 path file))
       d-e-list entry-limit))
     (put-assoc-equal
      name
      (m1-file
       (mv-nth 0 (find-d-e d-e-list name))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents fat32$c
                                     (mv-nth 0 (find-d-e d-e-list name)))))
           entry-limit))
         path (m1-file (d-e-fix nil) nil))))
      (mv-nth 0
              (lofat-to-hifat-helper fat32$c d-e-list entry-limit))))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e d-e-list name))
                                 path file))
       d-e-list entry-limit))
     0)))
  :hints
  (("goal"
    :in-theory (e/d (stobj-disjoins-list lofat-place-file-spec-1)
                    (lofat-place-file))
    :do-not-induct t
    :use (:instance lofat-place-file-correctness-lemma-143
                    (x nil)
                    (d-e (d-e-fix nil))))))

(defthm
  lofat-place-file-correctness-lemma-147
  (implies
   (and
    (equal (mv-nth 1
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e d-e-list name))
                                     path file))
           0)
    (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e d-e-list name))
                                 path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth 0
                  (lofat-place-file fat32$c
                                    (mv-nth 0 (find-d-e d-e-list name))
                                    path file))
          (mv-nth 0 (find-d-e d-e-list name)))))
       entry-limit))
     0)
    (not
     (member-intersectp-equal
      (set-difference-equal
       (mv-nth 2
               (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c
                                   (mv-nth 0 (find-d-e d-e-list name)))))
         entry-limit)))
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-place-file fat32$c
                                  (mv-nth 0 (find-d-e d-e-list name))
                                  path file))
        (make-d-e-list
         (mv-nth
          0
          (d-e-cc-contents
           (mv-nth 0
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e d-e-list name))
                                     path file))
           (mv-nth 0 (find-d-e d-e-list name)))))
        entry-limit))))
    (hifat-equiv
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e d-e-list name))
                                 path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth 0
                  (lofat-place-file fat32$c
                                    (mv-nth 0 (find-d-e d-e-list name))
                                    path file))
          (mv-nth 0 (find-d-e d-e-list name)))))
       entry-limit))
     (mv-nth
      0
      (hifat-place-file
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c
                                   (mv-nth 0 (find-d-e d-e-list name)))))
         entry-limit))
       path
       (m1-file d-e (lofat-file->contents file)))))
    (good-root-d-e-p root-d-e fat32$c)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
           0)
    (lofat-file-p file)
    (lofat-regular-file-p file)
    (<= (len (make-clusters (lofat-file->contents file)
                            (cluster-size fat32$c)))
        (count-free-clusters (effective-fat fat32$c)))
    (consp path)
    (< (hifat-entry-count
        (mv-nth 0
                (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
       entry-limit)
    (useful-d-e-list-p d-e-list)
    (fat32-filename-list-p path)
    (zp
     (mv-nth
      1
      (hifat-place-file
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c
                                   (mv-nth 0 (find-d-e d-e-list name)))))
         entry-limit))
       path
       (m1-file d-e (lofat-file->contents file))))))
   (and
    (hifat-equiv
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e d-e-list name))
                                 path file))
       d-e-list entry-limit))
     (put-assoc-equal
      name
      (m1-file
       (mv-nth 0 (find-d-e d-e-list name))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents fat32$c
                                     (mv-nth 0 (find-d-e d-e-list name)))))
           entry-limit))
         path
         (m1-file d-e (lofat-file->contents file)))))
      (mv-nth 0
              (lofat-to-hifat-helper fat32$c d-e-list entry-limit))))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e d-e-list name))
                                 path file))
       d-e-list entry-limit))
     0)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (e/d (stobj-disjoins-list lofat-place-file-spec-2)
         (lofat-place-file-correctness-lemma-94
          lofat-place-file
          (:rewrite d-e-cc-contents-of-lofat-place-file-coincident-1)))
    :use (:instance lofat-place-file-correctness-lemma-94
                    (x nil)))))

(defthm
  lofat-place-file-correctness-lemma-148
  (implies
   (and
    (equal
     (mv-nth
      1
      (lofat-place-file
       fat32$c
       (mv-nth
        0
        (find-d-e
         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         (car path)))
       (cdr path)
       file))
     0)
    (d-e-directory-p
     (mv-nth
      0
      (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                (car path))))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-place-file
         fat32$c
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (car path)))
         (cdr path)
         file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth
           0
           (lofat-place-file
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
              (car path)))
            (cdr path)
            file))
          (mv-nth
           0
           (find-d-e
            (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (car path))))))
       entry-limit))
     0)
    (not-intersectp-list
     x
     (mv-nth
      2
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-place-file
         fat32$c
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (car path)))
         (cdr path)
         file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth
           0
           (lofat-place-file
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
              (car path)))
            (cdr path)
            file))
          (mv-nth
           0
           (find-d-e
            (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (car path))))))
       entry-limit)))
    (not
     (member-intersectp-equal
      (set-difference-equal
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         entry-limit))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
              (car path))))))
         entry-limit)))
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth
         0
         (lofat-place-file
          fat32$c
          (mv-nth
           0
           (find-d-e
            (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (car path)))
          (cdr path)
          file))
        (make-d-e-list
         (mv-nth
          0
          (d-e-cc-contents
           (mv-nth
            0
            (lofat-place-file
             fat32$c
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
               (car path)))
             (cdr path)
             file))
           (mv-nth
            0
            (find-d-e
             (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
             (car path))))))
        entry-limit))))
    (hifat-equiv
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-place-file
         fat32$c
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (car path)))
         (cdr path)
         file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth
           0
           (lofat-place-file
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
              (car path)))
            (cdr path)
            file))
          (mv-nth
           0
           (find-d-e
            (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (car path))))))
       entry-limit))
     (mv-nth
      0
      (hifat-place-file
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
              (car path))))))
         entry-limit))
       (cdr path)
       '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
              0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
         (contents)))))
    (good-root-d-e-p root-d-e fat32$c)
    (non-free-index-listp x (effective-fat fat32$c))
    (fat32-filename-list-p path)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c root-d-e))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit)))
    (not-intersectp-list
     x
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit)))
    (lofat-file-p file)
    (not (lofat-file->contents file))
    (<= 1
        (count-free-clusters (effective-fat fat32$c)))
    (consp (cdr path))
    (integerp entry-limit)
    (<
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
        entry-limit)))
     entry-limit)
    (zp
     (mv-nth
      1
      (hifat-place-file
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
              (car path))))))
         entry-limit))
       (cdr path)
       (m1-file nil nil)))))
   (not-intersectp-list
    x
    (mv-nth
     2
     (lofat-to-hifat-helper
      (mv-nth
       0
       (lofat-place-file
        fat32$c
        (mv-nth
         0
         (find-d-e
          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
          (car path)))
        (cdr path)
        file))
      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
      entry-limit))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (disable (:definition lofat-place-file)
             (:rewrite length-when-stringp)
             (:rewrite len-of-nats=>chars)
             (:rewrite len-of-insert-d-e)
             (:rewrite len-of-place-d-e)
             (:rewrite place-contents-expansion-2)
             (:definition stobj-find-n-free-clusters-correctness-1)
             (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-2)
             (:rewrite place-contents-expansion-1)
             (:rewrite effective-fat-of-update-fati)
             (:rewrite lofat-place-file-correctness-lemma-144))
    :use
    (:instance
     (:rewrite lofat-place-file-correctness-lemma-143)
     (path (cdr path))
     (name (car path))
     (d-e-list
      (make-d-e-list (mv-nth 0
                             (d-e-cc-contents fat32$c root-d-e))))))))

(encapsulate
  ()

  (local
   (defun-nx
     induction-scheme
     (entry-limit fat32$c
                  file path root-d-e x)
     (cond
      ((and
        (consp path)
        (consp
         (assoc-equal
          (fat32-filename-fix (car path))
          (hifat-file-alist-fix
           (mv-nth
            0
            (lofat-to-hifat-helper
             fat32$c
             (make-d-e-list
              (mv-nth 0
                      (d-e-cc-contents
                       fat32$c root-d-e)))
             entry-limit)))))
        (m1-directory-file-p
         (cdr
          (assoc-equal
           (fat32-filename-fix (car path))
           (hifat-file-alist-fix
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents
                        fat32$c root-d-e)))
              entry-limit)))))))
       (induction-scheme
        entry-limit
        fat32$c file (cdr path)
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents
                    fat32$c root-d-e)))
          (car path)))
        (append
         x
         (flatten
          (set-difference-equal
           (mv-nth 2
                   (lofat-to-hifat-helper
                    fat32$c
                    (make-d-e-list
                     (mv-nth 0
                             (d-e-cc-contents
                              fat32$c root-d-e)))
                    entry-limit))
           (mv-nth 2
                   (lofat-to-hifat-helper
                    fat32$c
                    (make-d-e-list
                     (mv-nth 0
                             (d-e-cc-contents
                              fat32$c (mv-nth
                                       0
                                       (find-d-e
                                        (make-d-e-list
                                         (mv-nth 0
                                                 (d-e-cc-contents
                                                  fat32$c root-d-e)))
                                        (car path))))))
                    entry-limit)))))))
      (t (mv entry-limit fat32$c
             file path root-d-e x)))))

  (local (in-theory (disable
                     (:DEFINITION BUTLAST)
                     (:DEFINITION NFIX)
                     (:DEFINITION LENGTH)
                     (:DEFINITION MIN))))

  (local
   (defthm
     lofat-place-file-correctness-1-lemma-45
     (implies
      (and
       (m1-directory-file-p
        (m1-file
         (d-e-set-first-cluster-file-size
          (mv-nth
           0
           (find-d-e
            (make-d-e-list
             (mv-nth
              0
              (d-e-cc-contents fat32$c root-d-e)))
            (car path)))
          (nth 0
               (find-n-free-clusters (effective-fat fat32$c)
                                     1))
          (len (explode (lofat-file->contents file))))
         (lofat-file->contents file)))
       (lofat-regular-file-p file))
      (not-intersectp-list
       x
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
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
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
                                 fat32$c root-d-e)))
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
                                (d-e-cc-contents
                                 fat32$c root-d-e)))
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
                                   fat32$c root-d-e)))
                         (car path))))))
                    0 nil))
                  1))
                (mv-nth
                 0
                 (clear-cc
                  fat32$c
                  (d-e-first-cluster
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path))))
                  (d-e-file-size
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path)))))))
               268435455)
              (mv-nth
               0
               (clear-cc
                fat32$c
                (d-e-first-cluster
                 (mv-nth
                  0
                  (find-d-e (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path))))
                (d-e-file-size
                 (mv-nth
                  0
                  (find-d-e (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path)))))))
             (mv-nth
              0
              (find-d-e
               (make-d-e-list
                (mv-nth
                 0
                 (d-e-cc-contents fat32$c root-d-e)))
               (car path)))
             (lofat-file->contents file)
             (length (lofat-file->contents file))
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth 0
                          (find-d-e
                           (make-d-e-list
                            (mv-nth 0
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
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
                                fat32$c root-d-e)))
                      (car path))))))
                 0 nil))
               1))))
           (d-e-first-cluster root-d-e)
           (nats=>string
            (insert-d-e
             (string=>nats
              (mv-nth
               0
               (d-e-cc-contents fat32$c root-d-e)))
             (d-e-set-first-cluster-file-size
              (mv-nth
               1
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
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
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
                                    fat32$c root-d-e)))
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
                                   (d-e-cc-contents
                                    fat32$c root-d-e)))
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
                                      fat32$c root-d-e)))
                            (car path))))))
                       0 nil))
                     1))
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
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
                        (car path))))
                     (d-e-file-size
                      (mv-nth
                       0
                       (find-d-e
                        (make-d-e-list
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
                        (car path)))))))
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
                               (d-e-cc-contents
                                fat32$c root-d-e)))
                      (car path))))
                   (d-e-file-size
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth 0
                               (d-e-cc-contents
                                fat32$c root-d-e)))
                      (car path)))))))
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0
                                         (d-e-cc-contents
                                          fat32$c root-d-e)))
                  (car path)))
                (lofat-file->contents file)
                (length (lofat-file->contents file))
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
                                (d-e-cc-contents
                                 fat32$c root-d-e)))
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
                                   fat32$c root-d-e)))
                         (car path))))))
                    0 nil))
                  1))))
              (nth
               0
               (find-n-free-clusters
                (set-indices-in-fa-table
                 (effective-fat fat32$c)
                 (mv-nth
                  0
                  (d-e-cc
                   fat32$c
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
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
                                 fat32$c root-d-e)))
                       (car path))))))
                  0 nil))
                1))
              (length (lofat-file->contents file)))))))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
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
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
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
                                    fat32$c root-d-e)))
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
                                   (d-e-cc-contents
                                    fat32$c root-d-e)))
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
                                      fat32$c root-d-e)))
                            (car path))))))
                       0 nil))
                     1))
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
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
                        (car path))))
                     (d-e-file-size
                      (mv-nth
                       0
                       (find-d-e
                        (make-d-e-list
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
                        (car path)))))))
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
                               (d-e-cc-contents
                                fat32$c root-d-e)))
                      (car path))))
                   (d-e-file-size
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth 0
                               (d-e-cc-contents
                                fat32$c root-d-e)))
                      (car path)))))))
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0
                                         (d-e-cc-contents
                                          fat32$c root-d-e)))
                  (car path)))
                (lofat-file->contents file)
                (length (lofat-file->contents file))
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
                                (d-e-cc-contents
                                 fat32$c root-d-e)))
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
                                   fat32$c root-d-e)))
                         (car path))))))
                    0 nil))
                  1))))
              (d-e-first-cluster root-d-e)
              (nats=>string
               (insert-d-e
                (string=>nats
                 (mv-nth
                  0
                  (d-e-cc-contents fat32$c root-d-e)))
                (d-e-set-first-cluster-file-size
                 (mv-nth
                  1
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
                            (mv-nth 0
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
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
                                       fat32$c root-d-e)))
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
                                      (d-e-cc-contents
                                       fat32$c root-d-e)))
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
                                         fat32$c root-d-e)))
                               (car path))))))
                          0 nil))
                        1))
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
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
                           (car path))))
                        (d-e-file-size
                         (mv-nth
                          0
                          (find-d-e
                           (make-d-e-list
                            (mv-nth 0
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
                           (car path)))))))
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
                                  (d-e-cc-contents
                                   fat32$c root-d-e)))
                         (car path))))
                      (d-e-file-size
                       (mv-nth
                        0
                        (find-d-e
                         (make-d-e-list
                          (mv-nth 0
                                  (d-e-cc-contents
                                   fat32$c root-d-e)))
                         (car path)))))))
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path)))
                   (lofat-file->contents file)
                   (length (lofat-file->contents file))
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
                                   (d-e-cc-contents
                                    fat32$c root-d-e)))
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
                                      fat32$c root-d-e)))
                            (car path))))))
                       0 nil))
                     1))))
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
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
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
                                    fat32$c root-d-e)))
                          (car path))))))
                     0 nil))
                   1))
                 (length (lofat-file->contents file)))))))
            root-d-e)))
         entry-limit))))
     :hints (("goal" :in-theory
              (e/d
               ((:definition butlast)
                (:definition nfix)
                (:definition length)
                (:definition min))
               (m1-directory-file-p-of-m1-file))))))

  (local
   (defthm
     lofat-place-file-correctness-1-lemma-46
     (implies
      (and
       (m1-directory-file-p
        (m1-file
         (d-e-set-first-cluster-file-size
          (mv-nth
           0
           (find-d-e
            (make-d-e-list
             (mv-nth
              0
              (d-e-cc-contents fat32$c root-d-e)))
            (car path)))
          (nth 0
               (find-n-free-clusters (effective-fat fat32$c)
                                     1))
          (len (explode (lofat-file->contents file))))
         (lofat-file->contents file)))
       (lofat-regular-file-p file))
      (equal
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
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
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
                                 fat32$c root-d-e)))
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
                                (d-e-cc-contents
                                 fat32$c root-d-e)))
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
                                   fat32$c root-d-e)))
                         (car path))))))
                    0 nil))
                  1))
                (mv-nth
                 0
                 (clear-cc
                  fat32$c
                  (d-e-first-cluster
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path))))
                  (d-e-file-size
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path)))))))
               268435455)
              (mv-nth
               0
               (clear-cc
                fat32$c
                (d-e-first-cluster
                 (mv-nth
                  0
                  (find-d-e (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path))))
                (d-e-file-size
                 (mv-nth
                  0
                  (find-d-e (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path)))))))
             (mv-nth
              0
              (find-d-e
               (make-d-e-list
                (mv-nth
                 0
                 (d-e-cc-contents fat32$c root-d-e)))
               (car path)))
             (lofat-file->contents file)
             (length (lofat-file->contents file))
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth 0
                          (find-d-e
                           (make-d-e-list
                            (mv-nth 0
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
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
                                fat32$c root-d-e)))
                      (car path))))))
                 0 nil))
               1))))
           (d-e-first-cluster root-d-e)
           (nats=>string
            (insert-d-e
             (string=>nats
              (mv-nth
               0
               (d-e-cc-contents fat32$c root-d-e)))
             (d-e-set-first-cluster-file-size
              (mv-nth
               1
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
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
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
                                    fat32$c root-d-e)))
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
                                   (d-e-cc-contents
                                    fat32$c root-d-e)))
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
                                      fat32$c root-d-e)))
                            (car path))))))
                       0 nil))
                     1))
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
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
                        (car path))))
                     (d-e-file-size
                      (mv-nth
                       0
                       (find-d-e
                        (make-d-e-list
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
                        (car path)))))))
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
                               (d-e-cc-contents
                                fat32$c root-d-e)))
                      (car path))))
                   (d-e-file-size
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth 0
                               (d-e-cc-contents
                                fat32$c root-d-e)))
                      (car path)))))))
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0
                                         (d-e-cc-contents
                                          fat32$c root-d-e)))
                  (car path)))
                (lofat-file->contents file)
                (length (lofat-file->contents file))
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
                                (d-e-cc-contents
                                 fat32$c root-d-e)))
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
                                   fat32$c root-d-e)))
                         (car path))))))
                    0 nil))
                  1))))
              (nth
               0
               (find-n-free-clusters
                (set-indices-in-fa-table
                 (effective-fat fat32$c)
                 (mv-nth
                  0
                  (d-e-cc
                   fat32$c
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
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
                                 fat32$c root-d-e)))
                       (car path))))))
                  0 nil))
                1))
              (length (lofat-file->contents file)))))))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
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
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
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
                                    fat32$c root-d-e)))
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
                                   (d-e-cc-contents
                                    fat32$c root-d-e)))
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
                                      fat32$c root-d-e)))
                            (car path))))))
                       0 nil))
                     1))
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
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
                        (car path))))
                     (d-e-file-size
                      (mv-nth
                       0
                       (find-d-e
                        (make-d-e-list
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
                        (car path)))))))
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
                               (d-e-cc-contents
                                fat32$c root-d-e)))
                      (car path))))
                   (d-e-file-size
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth 0
                               (d-e-cc-contents
                                fat32$c root-d-e)))
                      (car path)))))))
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0
                                         (d-e-cc-contents
                                          fat32$c root-d-e)))
                  (car path)))
                (lofat-file->contents file)
                (length (lofat-file->contents file))
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
                                (d-e-cc-contents
                                 fat32$c root-d-e)))
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
                                   fat32$c root-d-e)))
                         (car path))))))
                    0 nil))
                  1))))
              (d-e-first-cluster root-d-e)
              (nats=>string
               (insert-d-e
                (string=>nats
                 (mv-nth
                  0
                  (d-e-cc-contents fat32$c root-d-e)))
                (d-e-set-first-cluster-file-size
                 (mv-nth
                  1
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
                            (mv-nth 0
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
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
                                       fat32$c root-d-e)))
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
                                      (d-e-cc-contents
                                       fat32$c root-d-e)))
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
                                         fat32$c root-d-e)))
                               (car path))))))
                          0 nil))
                        1))
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
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
                           (car path))))
                        (d-e-file-size
                         (mv-nth
                          0
                          (find-d-e
                           (make-d-e-list
                            (mv-nth 0
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
                           (car path)))))))
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
                                  (d-e-cc-contents
                                   fat32$c root-d-e)))
                         (car path))))
                      (d-e-file-size
                       (mv-nth
                        0
                        (find-d-e
                         (make-d-e-list
                          (mv-nth 0
                                  (d-e-cc-contents
                                   fat32$c root-d-e)))
                         (car path)))))))
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path)))
                   (lofat-file->contents file)
                   (length (lofat-file->contents file))
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
                                   (d-e-cc-contents
                                    fat32$c root-d-e)))
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
                                      fat32$c root-d-e)))
                            (car path))))))
                       0 nil))
                     1))))
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
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
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
                                    fat32$c root-d-e)))
                          (car path))))))
                     0 nil))
                   1))
                 (length (lofat-file->contents file)))))))
            root-d-e)))
         entry-limit))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c root-d-e)))
           entry-limit))
         path
         (m1-file
          (d-e-set-first-cluster-file-size
           (mv-nth
            0
            (find-d-e
             (make-d-e-list
              (mv-nth
               0
               (d-e-cc-contents fat32$c root-d-e)))
             (car path)))
           (nth 0
                (find-n-free-clusters (effective-fat fat32$c)
                                      1))
           (len (explode (lofat-file->contents file))))
          (lofat-file->contents file))))))
     :hints (("goal" :in-theory (e/d
                                 ((:definition butlast)
                                  (:definition nfix)
                                  (:definition length)
                                  (:definition min))
                                 (m1-directory-file-p-of-m1-file))))))

  (local
   (defthm
     lofat-place-file-correctness-1-lemma-51
     (implies
      (and
       (not
        (d-e-directory-p
         (mv-nth
          0
          (find-d-e
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c root-d-e)))
           (car path)))))
       (lofat-fs-p fat32$c)
       (<=
        4294967296
        (length
         (m1-file-contents-fix
          (mv-nth
           0
           (d-e-cc-contents
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth
                0
                (d-e-cc-contents fat32$c root-d-e)))
              (car path)))))))))
      (not-intersectp-list
       x
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
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
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
                                 fat32$c root-d-e)))
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
                                (d-e-cc-contents
                                 fat32$c root-d-e)))
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
                                   fat32$c root-d-e)))
                         (car path))))))
                    0 nil))
                  1))
                (mv-nth
                 0
                 (clear-cc
                  fat32$c
                  (d-e-first-cluster
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path))))
                  (d-e-file-size
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path)))))))
               268435455)
              (mv-nth
               0
               (clear-cc
                fat32$c
                (d-e-first-cluster
                 (mv-nth
                  0
                  (find-d-e (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path))))
                (d-e-file-size
                 (mv-nth
                  0
                  (find-d-e (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path)))))))
             (mv-nth
              0
              (find-d-e
               (make-d-e-list
                (mv-nth
                 0
                 (d-e-cc-contents fat32$c root-d-e)))
               (car path)))
             (lofat-file->contents file)
             (length (lofat-file->contents file))
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth 0
                          (find-d-e
                           (make-d-e-list
                            (mv-nth 0
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
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
                                fat32$c root-d-e)))
                      (car path))))))
                 0 nil))
               1))))
           (d-e-first-cluster root-d-e)
           (nats=>string
            (insert-d-e
             (string=>nats
              (mv-nth
               0
               (d-e-cc-contents fat32$c root-d-e)))
             (d-e-set-first-cluster-file-size
              (mv-nth
               1
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
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
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
                                    fat32$c root-d-e)))
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
                                   (d-e-cc-contents
                                    fat32$c root-d-e)))
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
                                      fat32$c root-d-e)))
                            (car path))))))
                       0 nil))
                     1))
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
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
                        (car path))))
                     (d-e-file-size
                      (mv-nth
                       0
                       (find-d-e
                        (make-d-e-list
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
                        (car path)))))))
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
                               (d-e-cc-contents
                                fat32$c root-d-e)))
                      (car path))))
                   (d-e-file-size
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth 0
                               (d-e-cc-contents
                                fat32$c root-d-e)))
                      (car path)))))))
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0
                                         (d-e-cc-contents
                                          fat32$c root-d-e)))
                  (car path)))
                (lofat-file->contents file)
                (length (lofat-file->contents file))
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
                                (d-e-cc-contents
                                 fat32$c root-d-e)))
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
                                   fat32$c root-d-e)))
                         (car path))))))
                    0 nil))
                  1))))
              (nth
               0
               (find-n-free-clusters
                (set-indices-in-fa-table
                 (effective-fat fat32$c)
                 (mv-nth
                  0
                  (d-e-cc
                   fat32$c
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
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
                                 fat32$c root-d-e)))
                       (car path))))))
                  0 nil))
                1))
              (length (lofat-file->contents file)))))))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
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
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
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
                                    fat32$c root-d-e)))
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
                                   (d-e-cc-contents
                                    fat32$c root-d-e)))
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
                                      fat32$c root-d-e)))
                            (car path))))))
                       0 nil))
                     1))
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
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
                        (car path))))
                     (d-e-file-size
                      (mv-nth
                       0
                       (find-d-e
                        (make-d-e-list
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
                        (car path)))))))
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
                               (d-e-cc-contents
                                fat32$c root-d-e)))
                      (car path))))
                   (d-e-file-size
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth 0
                               (d-e-cc-contents
                                fat32$c root-d-e)))
                      (car path)))))))
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0
                                         (d-e-cc-contents
                                          fat32$c root-d-e)))
                  (car path)))
                (lofat-file->contents file)
                (length (lofat-file->contents file))
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
                                (d-e-cc-contents
                                 fat32$c root-d-e)))
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
                                   fat32$c root-d-e)))
                         (car path))))))
                    0 nil))
                  1))))
              (d-e-first-cluster root-d-e)
              (nats=>string
               (insert-d-e
                (string=>nats
                 (mv-nth
                  0
                  (d-e-cc-contents fat32$c root-d-e)))
                (d-e-set-first-cluster-file-size
                 (mv-nth
                  1
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
                            (mv-nth 0
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
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
                                       fat32$c root-d-e)))
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
                                      (d-e-cc-contents
                                       fat32$c root-d-e)))
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
                                         fat32$c root-d-e)))
                               (car path))))))
                          0 nil))
                        1))
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
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
                           (car path))))
                        (d-e-file-size
                         (mv-nth
                          0
                          (find-d-e
                           (make-d-e-list
                            (mv-nth 0
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
                           (car path)))))))
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
                                  (d-e-cc-contents
                                   fat32$c root-d-e)))
                         (car path))))
                      (d-e-file-size
                       (mv-nth
                        0
                        (find-d-e
                         (make-d-e-list
                          (mv-nth 0
                                  (d-e-cc-contents
                                   fat32$c root-d-e)))
                         (car path)))))))
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path)))
                   (lofat-file->contents file)
                   (length (lofat-file->contents file))
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
                                   (d-e-cc-contents
                                    fat32$c root-d-e)))
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
                                      fat32$c root-d-e)))
                            (car path))))))
                       0 nil))
                     1))))
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
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
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
                                    fat32$c root-d-e)))
                          (car path))))))
                     0 nil))
                   1))
                 (length (lofat-file->contents file)))))))
            root-d-e)))
         entry-limit))))
     :hints (("goal" :in-theory (enable (:definition butlast)
                                        (:definition nfix)
                                        (:definition length)
                                        (:definition min))))))

  (local
   (defthm
     lofat-place-file-correctness-1-lemma-52
     (implies
      (and
       (m1-directory-file-p
        (m1-file
         (mv-nth
          0
          (find-d-e
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c root-d-e)))
           (car path)))
         (mv-nth
          0
          (d-e-cc-contents
           fat32$c
           (mv-nth
            0
            (find-d-e
             (make-d-e-list
              (mv-nth
               0
               (d-e-cc-contents fat32$c root-d-e)))
             (car path)))))))
       (lofat-fs-p fat32$c)
       (not
        (d-e-directory-p
         (mv-nth
          0
          (find-d-e
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c root-d-e)))
           (car path))))))
      (not-intersectp-list
       x
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
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
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
                                 fat32$c root-d-e)))
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
                                (d-e-cc-contents
                                 fat32$c root-d-e)))
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
                                   fat32$c root-d-e)))
                         (car path))))))
                    0 nil))
                  1))
                (mv-nth
                 0
                 (clear-cc
                  fat32$c
                  (d-e-first-cluster
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path))))
                  (d-e-file-size
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path)))))))
               268435455)
              (mv-nth
               0
               (clear-cc
                fat32$c
                (d-e-first-cluster
                 (mv-nth
                  0
                  (find-d-e (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path))))
                (d-e-file-size
                 (mv-nth
                  0
                  (find-d-e (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path)))))))
             (mv-nth
              0
              (find-d-e
               (make-d-e-list
                (mv-nth
                 0
                 (d-e-cc-contents fat32$c root-d-e)))
               (car path)))
             (lofat-file->contents file)
             (length (lofat-file->contents file))
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth 0
                          (find-d-e
                           (make-d-e-list
                            (mv-nth 0
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
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
                                fat32$c root-d-e)))
                      (car path))))))
                 0 nil))
               1))))
           (d-e-first-cluster root-d-e)
           (nats=>string
            (insert-d-e
             (string=>nats
              (mv-nth
               0
               (d-e-cc-contents fat32$c root-d-e)))
             (d-e-set-first-cluster-file-size
              (mv-nth
               1
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
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
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
                                    fat32$c root-d-e)))
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
                                   (d-e-cc-contents
                                    fat32$c root-d-e)))
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
                                      fat32$c root-d-e)))
                            (car path))))))
                       0 nil))
                     1))
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
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
                        (car path))))
                     (d-e-file-size
                      (mv-nth
                       0
                       (find-d-e
                        (make-d-e-list
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
                        (car path)))))))
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
                               (d-e-cc-contents
                                fat32$c root-d-e)))
                      (car path))))
                   (d-e-file-size
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth 0
                               (d-e-cc-contents
                                fat32$c root-d-e)))
                      (car path)))))))
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0
                                         (d-e-cc-contents
                                          fat32$c root-d-e)))
                  (car path)))
                (lofat-file->contents file)
                (length (lofat-file->contents file))
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
                                (d-e-cc-contents
                                 fat32$c root-d-e)))
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
                                   fat32$c root-d-e)))
                         (car path))))))
                    0 nil))
                  1))))
              (nth
               0
               (find-n-free-clusters
                (set-indices-in-fa-table
                 (effective-fat fat32$c)
                 (mv-nth
                  0
                  (d-e-cc
                   fat32$c
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
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
                                 fat32$c root-d-e)))
                       (car path))))))
                  0 nil))
                1))
              (length (lofat-file->contents file)))))))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
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
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
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
                                    fat32$c root-d-e)))
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
                                   (d-e-cc-contents
                                    fat32$c root-d-e)))
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
                                      fat32$c root-d-e)))
                            (car path))))))
                       0 nil))
                     1))
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
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
                        (car path))))
                     (d-e-file-size
                      (mv-nth
                       0
                       (find-d-e
                        (make-d-e-list
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
                        (car path)))))))
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
                               (d-e-cc-contents
                                fat32$c root-d-e)))
                      (car path))))
                   (d-e-file-size
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth 0
                               (d-e-cc-contents
                                fat32$c root-d-e)))
                      (car path)))))))
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0
                                         (d-e-cc-contents
                                          fat32$c root-d-e)))
                  (car path)))
                (lofat-file->contents file)
                (length (lofat-file->contents file))
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
                                (d-e-cc-contents
                                 fat32$c root-d-e)))
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
                                   fat32$c root-d-e)))
                         (car path))))))
                    0 nil))
                  1))))
              (d-e-first-cluster root-d-e)
              (nats=>string
               (insert-d-e
                (string=>nats
                 (mv-nth
                  0
                  (d-e-cc-contents fat32$c root-d-e)))
                (d-e-set-first-cluster-file-size
                 (mv-nth
                  1
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
                            (mv-nth 0
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
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
                                       fat32$c root-d-e)))
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
                                      (d-e-cc-contents
                                       fat32$c root-d-e)))
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
                                         fat32$c root-d-e)))
                               (car path))))))
                          0 nil))
                        1))
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
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
                           (car path))))
                        (d-e-file-size
                         (mv-nth
                          0
                          (find-d-e
                           (make-d-e-list
                            (mv-nth 0
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
                           (car path)))))))
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
                                  (d-e-cc-contents
                                   fat32$c root-d-e)))
                         (car path))))
                      (d-e-file-size
                       (mv-nth
                        0
                        (find-d-e
                         (make-d-e-list
                          (mv-nth 0
                                  (d-e-cc-contents
                                   fat32$c root-d-e)))
                         (car path)))))))
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path)))
                   (lofat-file->contents file)
                   (length (lofat-file->contents file))
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
                                   (d-e-cc-contents
                                    fat32$c root-d-e)))
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
                                      fat32$c root-d-e)))
                            (car path))))))
                       0 nil))
                     1))))
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
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
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
                                    fat32$c root-d-e)))
                          (car path))))))
                     0 nil))
                   1))
                 (length (lofat-file->contents file)))))))
            root-d-e)))
         entry-limit))))
     :hints (("goal" :in-theory (enable (:definition butlast)
                                        (:definition nfix)
                                        (:definition length)
                                        (:definition min))))))

  (local
   (defthm
     lofat-place-file-correctness-1-lemma-53
     (implies
      (and
       (m1-directory-file-p
        (m1-file
         (mv-nth
          0
          (find-d-e
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c root-d-e)))
           (car path)))
         (mv-nth
          0
          (d-e-cc-contents
           fat32$c
           (mv-nth
            0
            (find-d-e
             (make-d-e-list
              (mv-nth
               0
               (d-e-cc-contents fat32$c root-d-e)))
             (car path)))))))
       (lofat-fs-p fat32$c)
       (not
        (d-e-directory-p
         (mv-nth
          0
          (find-d-e
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c root-d-e)))
           (car path))))))
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
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
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
                                 fat32$c root-d-e)))
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
                                (d-e-cc-contents
                                 fat32$c root-d-e)))
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
                                   fat32$c root-d-e)))
                         (car path))))))
                    0 nil))
                  1))
                (mv-nth
                 0
                 (clear-cc
                  fat32$c
                  (d-e-first-cluster
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path))))
                  (d-e-file-size
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path)))))))
               268435455)
              (mv-nth
               0
               (clear-cc
                fat32$c
                (d-e-first-cluster
                 (mv-nth
                  0
                  (find-d-e (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path))))
                (d-e-file-size
                 (mv-nth
                  0
                  (find-d-e (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path)))))))
             (mv-nth
              0
              (find-d-e
               (make-d-e-list
                (mv-nth
                 0
                 (d-e-cc-contents fat32$c root-d-e)))
               (car path)))
             (lofat-file->contents file)
             (length (lofat-file->contents file))
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth 0
                          (find-d-e
                           (make-d-e-list
                            (mv-nth 0
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
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
                                fat32$c root-d-e)))
                      (car path))))))
                 0 nil))
               1))))
           (d-e-first-cluster root-d-e)
           (nats=>string
            (insert-d-e
             (string=>nats
              (mv-nth
               0
               (d-e-cc-contents fat32$c root-d-e)))
             (d-e-set-first-cluster-file-size
              (mv-nth
               1
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
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
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
                                    fat32$c root-d-e)))
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
                                   (d-e-cc-contents
                                    fat32$c root-d-e)))
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
                                      fat32$c root-d-e)))
                            (car path))))))
                       0 nil))
                     1))
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
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
                        (car path))))
                     (d-e-file-size
                      (mv-nth
                       0
                       (find-d-e
                        (make-d-e-list
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
                        (car path)))))))
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
                               (d-e-cc-contents
                                fat32$c root-d-e)))
                      (car path))))
                   (d-e-file-size
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth 0
                               (d-e-cc-contents
                                fat32$c root-d-e)))
                      (car path)))))))
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0
                                         (d-e-cc-contents
                                          fat32$c root-d-e)))
                  (car path)))
                (lofat-file->contents file)
                (length (lofat-file->contents file))
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
                                (d-e-cc-contents
                                 fat32$c root-d-e)))
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
                                   fat32$c root-d-e)))
                         (car path))))))
                    0 nil))
                  1))))
              (nth
               0
               (find-n-free-clusters
                (set-indices-in-fa-table
                 (effective-fat fat32$c)
                 (mv-nth
                  0
                  (d-e-cc
                   fat32$c
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
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
                                 fat32$c root-d-e)))
                       (car path))))))
                  0 nil))
                1))
              (length (lofat-file->contents file)))))))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
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
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
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
                                    fat32$c root-d-e)))
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
                                   (d-e-cc-contents
                                    fat32$c root-d-e)))
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
                                      fat32$c root-d-e)))
                            (car path))))))
                       0 nil))
                     1))
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
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
                        (car path))))
                     (d-e-file-size
                      (mv-nth
                       0
                       (find-d-e
                        (make-d-e-list
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
                        (car path)))))))
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
                               (d-e-cc-contents
                                fat32$c root-d-e)))
                      (car path))))
                   (d-e-file-size
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth 0
                               (d-e-cc-contents
                                fat32$c root-d-e)))
                      (car path)))))))
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0
                                         (d-e-cc-contents
                                          fat32$c root-d-e)))
                  (car path)))
                (lofat-file->contents file)
                (length (lofat-file->contents file))
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
                                (d-e-cc-contents
                                 fat32$c root-d-e)))
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
                                   fat32$c root-d-e)))
                         (car path))))))
                    0 nil))
                  1))))
              (d-e-first-cluster root-d-e)
              (nats=>string
               (insert-d-e
                (string=>nats
                 (mv-nth
                  0
                  (d-e-cc-contents fat32$c root-d-e)))
                (d-e-set-first-cluster-file-size
                 (mv-nth
                  1
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
                            (mv-nth 0
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
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
                                       fat32$c root-d-e)))
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
                                      (d-e-cc-contents
                                       fat32$c root-d-e)))
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
                                         fat32$c root-d-e)))
                               (car path))))))
                          0 nil))
                        1))
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
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
                           (car path))))
                        (d-e-file-size
                         (mv-nth
                          0
                          (find-d-e
                           (make-d-e-list
                            (mv-nth 0
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
                           (car path)))))))
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
                                  (d-e-cc-contents
                                   fat32$c root-d-e)))
                         (car path))))
                      (d-e-file-size
                       (mv-nth
                        0
                        (find-d-e
                         (make-d-e-list
                          (mv-nth 0
                                  (d-e-cc-contents
                                   fat32$c root-d-e)))
                         (car path)))))))
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path)))
                   (lofat-file->contents file)
                   (length (lofat-file->contents file))
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
                                   (d-e-cc-contents
                                    fat32$c root-d-e)))
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
                                      fat32$c root-d-e)))
                            (car path))))))
                       0 nil))
                     1))))
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
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
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
                                    fat32$c root-d-e)))
                          (car path))))))
                     0 nil))
                   1))
                 (length (lofat-file->contents file)))))))
            root-d-e)))
         entry-limit))
       0))
     :hints (("goal" :in-theory (enable (:definition butlast)
                                        (:definition nfix)
                                        (:definition length)
                                        (:definition min))))))

  (local
   (defthm
     lofat-place-file-correctness-1-lemma-55
     (implies
      (and
       (m1-directory-file-p
        (m1-file
         (mv-nth
          0
          (find-d-e
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c root-d-e)))
           (car path)))
         (mv-nth
          0
          (d-e-cc-contents
           fat32$c
           (mv-nth
            0
            (find-d-e
             (make-d-e-list
              (mv-nth
               0
               (d-e-cc-contents fat32$c root-d-e)))
             (car path)))))))
       (lofat-fs-p fat32$c)
       (not
        (d-e-directory-p
         (mv-nth
          0
          (find-d-e
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c root-d-e)))
           (car path))))))
      (equal
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
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
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
                                 fat32$c root-d-e)))
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
                                (d-e-cc-contents
                                 fat32$c root-d-e)))
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
                                   fat32$c root-d-e)))
                         (car path))))))
                    0 nil))
                  1))
                (mv-nth
                 0
                 (clear-cc
                  fat32$c
                  (d-e-first-cluster
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path))))
                  (d-e-file-size
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path)))))))
               268435455)
              (mv-nth
               0
               (clear-cc
                fat32$c
                (d-e-first-cluster
                 (mv-nth
                  0
                  (find-d-e (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path))))
                (d-e-file-size
                 (mv-nth
                  0
                  (find-d-e (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path)))))))
             (mv-nth
              0
              (find-d-e
               (make-d-e-list
                (mv-nth
                 0
                 (d-e-cc-contents fat32$c root-d-e)))
               (car path)))
             (lofat-file->contents file)
             (length (lofat-file->contents file))
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth 0
                          (find-d-e
                           (make-d-e-list
                            (mv-nth 0
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
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
                                fat32$c root-d-e)))
                      (car path))))))
                 0 nil))
               1))))
           (d-e-first-cluster root-d-e)
           (nats=>string
            (insert-d-e
             (string=>nats
              (mv-nth
               0
               (d-e-cc-contents fat32$c root-d-e)))
             (d-e-set-first-cluster-file-size
              (mv-nth
               1
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
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
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
                                    fat32$c root-d-e)))
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
                                   (d-e-cc-contents
                                    fat32$c root-d-e)))
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
                                      fat32$c root-d-e)))
                            (car path))))))
                       0 nil))
                     1))
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
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
                        (car path))))
                     (d-e-file-size
                      (mv-nth
                       0
                       (find-d-e
                        (make-d-e-list
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
                        (car path)))))))
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
                               (d-e-cc-contents
                                fat32$c root-d-e)))
                      (car path))))
                   (d-e-file-size
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth 0
                               (d-e-cc-contents
                                fat32$c root-d-e)))
                      (car path)))))))
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0
                                         (d-e-cc-contents
                                          fat32$c root-d-e)))
                  (car path)))
                (lofat-file->contents file)
                (length (lofat-file->contents file))
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
                                (d-e-cc-contents
                                 fat32$c root-d-e)))
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
                                   fat32$c root-d-e)))
                         (car path))))))
                    0 nil))
                  1))))
              (nth
               0
               (find-n-free-clusters
                (set-indices-in-fa-table
                 (effective-fat fat32$c)
                 (mv-nth
                  0
                  (d-e-cc
                   fat32$c
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
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
                                 fat32$c root-d-e)))
                       (car path))))))
                  0 nil))
                1))
              (length (lofat-file->contents file)))))))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
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
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
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
                                    fat32$c root-d-e)))
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
                                   (d-e-cc-contents
                                    fat32$c root-d-e)))
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
                                      fat32$c root-d-e)))
                            (car path))))))
                       0 nil))
                     1))
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
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
                        (car path))))
                     (d-e-file-size
                      (mv-nth
                       0
                       (find-d-e
                        (make-d-e-list
                         (mv-nth 0
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
                        (car path)))))))
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
                               (d-e-cc-contents
                                fat32$c root-d-e)))
                      (car path))))
                   (d-e-file-size
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list
                       (mv-nth 0
                               (d-e-cc-contents
                                fat32$c root-d-e)))
                      (car path)))))))
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0
                                         (d-e-cc-contents
                                          fat32$c root-d-e)))
                  (car path)))
                (lofat-file->contents file)
                (length (lofat-file->contents file))
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
                                (d-e-cc-contents
                                 fat32$c root-d-e)))
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
                                   fat32$c root-d-e)))
                         (car path))))))
                    0 nil))
                  1))))
              (d-e-first-cluster root-d-e)
              (nats=>string
               (insert-d-e
                (string=>nats
                 (mv-nth
                  0
                  (d-e-cc-contents fat32$c root-d-e)))
                (d-e-set-first-cluster-file-size
                 (mv-nth
                  1
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
                            (mv-nth 0
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
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
                                       fat32$c root-d-e)))
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
                                      (d-e-cc-contents
                                       fat32$c root-d-e)))
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
                                         fat32$c root-d-e)))
                               (car path))))))
                          0 nil))
                        1))
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
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
                           (car path))))
                        (d-e-file-size
                         (mv-nth
                          0
                          (find-d-e
                           (make-d-e-list
                            (mv-nth 0
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
                           (car path)))))))
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
                                  (d-e-cc-contents
                                   fat32$c root-d-e)))
                         (car path))))
                      (d-e-file-size
                       (mv-nth
                        0
                        (find-d-e
                         (make-d-e-list
                          (mv-nth 0
                                  (d-e-cc-contents
                                   fat32$c root-d-e)))
                         (car path)))))))
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path)))
                   (lofat-file->contents file)
                   (length (lofat-file->contents file))
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
                                   (d-e-cc-contents
                                    fat32$c root-d-e)))
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
                                      fat32$c root-d-e)))
                            (car path))))))
                       0 nil))
                     1))))
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
                                 (d-e-cc-contents
                                  fat32$c root-d-e)))
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
                                    fat32$c root-d-e)))
                          (car path))))))
                     0 nil))
                   1))
                 (length (lofat-file->contents file)))))))
            root-d-e)))
         entry-limit))
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c root-d-e)))
         entry-limit))))
     :hints (("goal" :in-theory (enable (:definition butlast)
                                        (:definition nfix)
                                        (:definition length)
                                        (:definition min))))))

  (local
   (defthm
     lofat-place-file-correctness-1-lemma-58
     (implies
      (and
       (not
        (d-e-directory-p
         (mv-nth
          0
          (find-d-e
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c root-d-e)))
           (car path)))))
       (lofat-fs-p fat32$c)
       (<=
        4294967296
        (length
         (m1-file-contents-fix
          (mv-nth
           0
           (d-e-cc-contents
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth
                0
                (d-e-cc-contents fat32$c root-d-e)))
              (car path)))))))))
      (<
       2097152
       (length
        (nats=>string
         (insert-d-e
          (string=>nats
           (mv-nth 0
                   (d-e-cc-contents fat32$c root-d-e)))
          (d-e-set-first-cluster-file-size
           (mv-nth
            1
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
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
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
                                 fat32$c root-d-e)))
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
                                (d-e-cc-contents
                                 fat32$c root-d-e)))
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
                                   fat32$c root-d-e)))
                         (car path))))))
                    0 nil))
                  1))
                (mv-nth
                 0
                 (clear-cc
                  fat32$c
                  (d-e-first-cluster
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path))))
                  (d-e-file-size
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path)))))))
               268435455)
              (mv-nth
               0
               (clear-cc
                fat32$c
                (d-e-first-cluster
                 (mv-nth
                  0
                  (find-d-e (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path))))
                (d-e-file-size
                 (mv-nth
                  0
                  (find-d-e (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path)))))))
             (mv-nth
              0
              (find-d-e
               (make-d-e-list
                (mv-nth
                 0
                 (d-e-cc-contents fat32$c root-d-e)))
               (car path)))
             (lofat-file->contents file)
             (length (lofat-file->contents file))
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth 0
                          (find-d-e
                           (make-d-e-list
                            (mv-nth 0
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
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
                                fat32$c root-d-e)))
                      (car path))))))
                 0 nil))
               1))))
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
                  (make-d-e-list (mv-nth 0
                                         (d-e-cc-contents
                                          fat32$c root-d-e)))
                  (car path)))))
              (make-list-ac
               (len
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth 0
                          (find-d-e
                           (make-d-e-list
                            (mv-nth 0
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
                           (car path))))))
               0 nil))
             1))
           (length (lofat-file->contents file))))))))
     :hints (("goal" :in-theory (enable (:definition butlast)
                                        (:definition nfix)
                                        (:definition length)
                                        (:definition min))))))

  (local
   (defthm
     lofat-place-file-correctness-1-lemma-62
     (implies
      (and
       (fat32-filename-list-p path)
       (<=
        2
        (d-e-first-cluster
         (d-e-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (cadr path)))))
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
                (effective-fat
                 (mv-nth
                  0
                  (clear-cc
                   fat32$c
                   (d-e-first-cluster
                    (d-e-set-filename
                     '(0 0 0 0 0 0 0 0 0 0 0 0
                         0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                     (cadr path)))
                   0)))
                1))
              (fat32-update-lower-28
               (fati
                (nth
                 0
                 (find-n-free-clusters
                  (effective-fat
                   (mv-nth
                    0
                    (clear-cc
                     fat32$c
                     (d-e-first-cluster
                      (d-e-set-filename
                       '(0 0 0 0 0 0 0 0 0 0 0 0
                           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                       (cadr path)))
                     0)))
                  1))
                (mv-nth
                 0
                 (clear-cc
                  fat32$c
                  (d-e-first-cluster
                   (d-e-set-filename
                    '(0 0 0 0 0 0 0 0 0 0 0 0
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                    (cadr path)))
                  0)))
               268435455)
              (mv-nth 0
                      (clear-cc
                       fat32$c
                       (d-e-first-cluster
                        (d-e-set-filename
                         '(0 0 0 0 0 0 0 0 0 0 0 0
                             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                         (cadr path)))
                       0)))
             (d-e-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                                   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                               (cadr path))
             (lofat-file->contents file)
             (length (lofat-file->contents file))
             (nth
              0
              (find-n-free-clusters
               (effective-fat
                (mv-nth
                 0
                 (clear-cc
                  fat32$c
                  (d-e-first-cluster
                   (d-e-set-filename
                    '(0 0 0 0 0 0 0 0 0 0 0 0
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                    (cadr path)))
                  0)))
               1))))
           (d-e-first-cluster
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth
                0
                (d-e-cc-contents fat32$c root-d-e)))
              (car path))))
           (nats=>string
            (insert-d-e
             (string=>nats
              (mv-nth
               0
               (d-e-cc-contents
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0
                                         (d-e-cc-contents
                                          fat32$c root-d-e)))
                  (car path))))))
             (d-e-set-first-cluster-file-size
              (mv-nth
               1
               (place-contents
                (update-fati
                 (nth
                  0
                  (find-n-free-clusters
                   (effective-fat
                    (mv-nth
                     0
                     (clear-cc
                      fat32$c
                      (d-e-first-cluster
                       (d-e-set-filename
                        '(0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                        (cadr path)))
                      0)))
                   1))
                 (fat32-update-lower-28
                  (fati
                   (nth
                    0
                    (find-n-free-clusters
                     (effective-fat
                      (mv-nth
                       0
                       (clear-cc
                        fat32$c
                        (d-e-first-cluster
                         (d-e-set-filename
                          '(0 0 0 0 0 0 0 0 0 0 0 0
                              0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                          (cadr path)))
                        0)))
                     1))
                   (mv-nth
                    0
                    (clear-cc
                     fat32$c
                     (d-e-first-cluster
                      (d-e-set-filename
                       '(0 0 0 0 0 0 0 0 0 0 0 0
                           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                       (cadr path)))
                     0)))
                  268435455)
                 (mv-nth
                  0
                  (clear-cc
                   fat32$c
                   (d-e-first-cluster
                    (d-e-set-filename
                     '(0 0 0 0 0 0 0 0 0 0 0 0
                         0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                     (cadr path)))
                   0)))
                (d-e-set-filename
                 '(0 0 0 0 0 0 0 0 0 0 0 0
                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                 (cadr path))
                (lofat-file->contents file)
                (length (lofat-file->contents file))
                (nth
                 0
                 (find-n-free-clusters
                  (effective-fat
                   (mv-nth
                    0
                    (clear-cc
                     fat32$c
                     (d-e-first-cluster
                      (d-e-set-filename
                       '(0 0 0 0 0 0 0 0 0 0 0 0
                           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                       (cadr path)))
                     0)))
                  1))))
              (nth
               0
               (find-n-free-clusters
                (effective-fat
                 (mv-nth
                  0
                  (clear-cc
                   fat32$c
                   (d-e-first-cluster
                    (d-e-set-filename
                     '(0 0 0 0 0 0 0 0 0 0 0 0
                         0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                     (cadr path)))
                   0)))
                1))
              (length (lofat-file->contents file)))))))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
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
                   (effective-fat
                    (mv-nth
                     0
                     (clear-cc
                      fat32$c
                      (d-e-first-cluster
                       (d-e-set-filename
                        '(0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                        (cadr path)))
                      0)))
                   1))
                 (fat32-update-lower-28
                  (fati
                   (nth
                    0
                    (find-n-free-clusters
                     (effective-fat
                      (mv-nth
                       0
                       (clear-cc
                        fat32$c
                        (d-e-first-cluster
                         (d-e-set-filename
                          '(0 0 0 0 0 0 0 0 0 0 0 0
                              0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                          (cadr path)))
                        0)))
                     1))
                   (mv-nth
                    0
                    (clear-cc
                     fat32$c
                     (d-e-first-cluster
                      (d-e-set-filename
                       '(0 0 0 0 0 0 0 0 0 0 0 0
                           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                       (cadr path)))
                     0)))
                  268435455)
                 (mv-nth
                  0
                  (clear-cc
                   fat32$c
                   (d-e-first-cluster
                    (d-e-set-filename
                     '(0 0 0 0 0 0 0 0 0 0 0 0
                         0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                     (cadr path)))
                   0)))
                (d-e-set-filename
                 '(0 0 0 0 0 0 0 0 0 0 0 0
                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                 (cadr path))
                (lofat-file->contents file)
                (length (lofat-file->contents file))
                (nth
                 0
                 (find-n-free-clusters
                  (effective-fat
                   (mv-nth
                    0
                    (clear-cc
                     fat32$c
                     (d-e-first-cluster
                      (d-e-set-filename
                       '(0 0 0 0 0 0 0 0 0 0 0 0
                           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                       (cadr path)))
                     0)))
                  1))))
              (d-e-first-cluster
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth
                   0
                   (d-e-cc-contents fat32$c root-d-e)))
                 (car path))))
              (nats=>string
               (insert-d-e
                (string=>nats
                 (mv-nth
                  0
                  (d-e-cc-contents
                   fat32$c
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path))))))
                (d-e-set-first-cluster-file-size
                 (mv-nth
                  1
                  (place-contents
                   (update-fati
                    (nth
                     0
                     (find-n-free-clusters
                      (effective-fat
                       (mv-nth
                        0
                        (clear-cc
                         fat32$c
                         (d-e-first-cluster
                          (d-e-set-filename
                           '(0 0 0 0 0 0 0 0 0 0 0 0
                               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (cadr path)))
                         0)))
                      1))
                    (fat32-update-lower-28
                     (fati
                      (nth
                       0
                       (find-n-free-clusters
                        (effective-fat
                         (mv-nth
                          0
                          (clear-cc
                           fat32$c
                           (d-e-first-cluster
                            (d-e-set-filename
                             '(0 0 0 0 0 0 0 0 0 0 0 0
                                 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                             (cadr path)))
                           0)))
                        1))
                      (mv-nth
                       0
                       (clear-cc
                        fat32$c
                        (d-e-first-cluster
                         (d-e-set-filename
                          '(0 0 0 0 0 0 0 0 0 0 0 0
                              0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                          (cadr path)))
                        0)))
                     268435455)
                    (mv-nth
                     0
                     (clear-cc
                      fat32$c
                      (d-e-first-cluster
                       (d-e-set-filename
                        '(0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                        (cadr path)))
                      0)))
                   (d-e-set-filename
                    '(0 0 0 0 0 0 0 0 0 0 0 0
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                    (cadr path))
                   (lofat-file->contents file)
                   (length (lofat-file->contents file))
                   (nth
                    0
                    (find-n-free-clusters
                     (effective-fat
                      (mv-nth
                       0
                       (clear-cc
                        fat32$c
                        (d-e-first-cluster
                         (d-e-set-filename
                          '(0 0 0 0 0 0 0 0 0 0 0 0
                              0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                          (cadr path)))
                        0)))
                     1))))
                 (nth
                  0
                  (find-n-free-clusters
                   (effective-fat
                    (mv-nth
                     0
                     (clear-cc
                      fat32$c
                      (d-e-first-cluster
                       (d-e-set-filename
                        '(0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                        (cadr path)))
                      0)))
                   1))
                 (length (lofat-file->contents file)))))))
            root-d-e)))
         entry-limit))
       0))
     :hints (("goal" :in-theory (enable (:definition butlast)
                                        (:definition nfix)
                                        (:definition length)
                                        (:definition min)))
             ("[1]goal" :in-theory (enable (:definition butlast)
                                           (:definition nfix)
                                           (:definition length)
                                           (:definition min))))))

  (local
   (defthm
     lofat-place-file-correctness-1-lemma-63
     (implies
      (and
       (fat32-filename-list-p path)
       (<=
        2
        (d-e-first-cluster
         (d-e-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (cadr path)))))
      (not-intersectp-list
       x
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
                (effective-fat
                 (mv-nth
                  0
                  (clear-cc
                   fat32$c
                   (d-e-first-cluster
                    (d-e-set-filename
                     '(0 0 0 0 0 0 0 0 0 0 0 0
                         0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                     (cadr path)))
                   0)))
                1))
              (fat32-update-lower-28
               (fati
                (nth
                 0
                 (find-n-free-clusters
                  (effective-fat
                   (mv-nth
                    0
                    (clear-cc
                     fat32$c
                     (d-e-first-cluster
                      (d-e-set-filename
                       '(0 0 0 0 0 0 0 0 0 0 0 0
                           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                       (cadr path)))
                     0)))
                  1))
                (mv-nth
                 0
                 (clear-cc
                  fat32$c
                  (d-e-first-cluster
                   (d-e-set-filename
                    '(0 0 0 0 0 0 0 0 0 0 0 0
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                    (cadr path)))
                  0)))
               268435455)
              (mv-nth 0
                      (clear-cc
                       fat32$c
                       (d-e-first-cluster
                        (d-e-set-filename
                         '(0 0 0 0 0 0 0 0 0 0 0 0
                             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                         (cadr path)))
                       0)))
             (d-e-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                                   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                               (cadr path))
             (lofat-file->contents file)
             (length (lofat-file->contents file))
             (nth
              0
              (find-n-free-clusters
               (effective-fat
                (mv-nth
                 0
                 (clear-cc
                  fat32$c
                  (d-e-first-cluster
                   (d-e-set-filename
                    '(0 0 0 0 0 0 0 0 0 0 0 0
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                    (cadr path)))
                  0)))
               1))))
           (d-e-first-cluster
            (mv-nth
             0
             (find-d-e
              (make-d-e-list
               (mv-nth
                0
                (d-e-cc-contents fat32$c root-d-e)))
              (car path))))
           (nats=>string
            (insert-d-e
             (string=>nats
              (mv-nth
               0
               (d-e-cc-contents
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0
                                         (d-e-cc-contents
                                          fat32$c root-d-e)))
                  (car path))))))
             (d-e-set-first-cluster-file-size
              (mv-nth
               1
               (place-contents
                (update-fati
                 (nth
                  0
                  (find-n-free-clusters
                   (effective-fat
                    (mv-nth
                     0
                     (clear-cc
                      fat32$c
                      (d-e-first-cluster
                       (d-e-set-filename
                        '(0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                        (cadr path)))
                      0)))
                   1))
                 (fat32-update-lower-28
                  (fati
                   (nth
                    0
                    (find-n-free-clusters
                     (effective-fat
                      (mv-nth
                       0
                       (clear-cc
                        fat32$c
                        (d-e-first-cluster
                         (d-e-set-filename
                          '(0 0 0 0 0 0 0 0 0 0 0 0
                              0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                          (cadr path)))
                        0)))
                     1))
                   (mv-nth
                    0
                    (clear-cc
                     fat32$c
                     (d-e-first-cluster
                      (d-e-set-filename
                       '(0 0 0 0 0 0 0 0 0 0 0 0
                           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                       (cadr path)))
                     0)))
                  268435455)
                 (mv-nth
                  0
                  (clear-cc
                   fat32$c
                   (d-e-first-cluster
                    (d-e-set-filename
                     '(0 0 0 0 0 0 0 0 0 0 0 0
                         0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                     (cadr path)))
                   0)))
                (d-e-set-filename
                 '(0 0 0 0 0 0 0 0 0 0 0 0
                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                 (cadr path))
                (lofat-file->contents file)
                (length (lofat-file->contents file))
                (nth
                 0
                 (find-n-free-clusters
                  (effective-fat
                   (mv-nth
                    0
                    (clear-cc
                     fat32$c
                     (d-e-first-cluster
                      (d-e-set-filename
                       '(0 0 0 0 0 0 0 0 0 0 0 0
                           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                       (cadr path)))
                     0)))
                  1))))
              (nth
               0
               (find-n-free-clusters
                (effective-fat
                 (mv-nth
                  0
                  (clear-cc
                   fat32$c
                   (d-e-first-cluster
                    (d-e-set-filename
                     '(0 0 0 0 0 0 0 0 0 0 0 0
                         0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                     (cadr path)))
                   0)))
                1))
              (length (lofat-file->contents file)))))))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
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
                   (effective-fat
                    (mv-nth
                     0
                     (clear-cc
                      fat32$c
                      (d-e-first-cluster
                       (d-e-set-filename
                        '(0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                        (cadr path)))
                      0)))
                   1))
                 (fat32-update-lower-28
                  (fati
                   (nth
                    0
                    (find-n-free-clusters
                     (effective-fat
                      (mv-nth
                       0
                       (clear-cc
                        fat32$c
                        (d-e-first-cluster
                         (d-e-set-filename
                          '(0 0 0 0 0 0 0 0 0 0 0 0
                              0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                          (cadr path)))
                        0)))
                     1))
                   (mv-nth
                    0
                    (clear-cc
                     fat32$c
                     (d-e-first-cluster
                      (d-e-set-filename
                       '(0 0 0 0 0 0 0 0 0 0 0 0
                           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                       (cadr path)))
                     0)))
                  268435455)
                 (mv-nth
                  0
                  (clear-cc
                   fat32$c
                   (d-e-first-cluster
                    (d-e-set-filename
                     '(0 0 0 0 0 0 0 0 0 0 0 0
                         0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                     (cadr path)))
                   0)))
                (d-e-set-filename
                 '(0 0 0 0 0 0 0 0 0 0 0 0
                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                 (cadr path))
                (lofat-file->contents file)
                (length (lofat-file->contents file))
                (nth
                 0
                 (find-n-free-clusters
                  (effective-fat
                   (mv-nth
                    0
                    (clear-cc
                     fat32$c
                     (d-e-first-cluster
                      (d-e-set-filename
                       '(0 0 0 0 0 0 0 0 0 0 0 0
                           0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                       (cadr path)))
                     0)))
                  1))))
              (d-e-first-cluster
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth
                   0
                   (d-e-cc-contents fat32$c root-d-e)))
                 (car path))))
              (nats=>string
               (insert-d-e
                (string=>nats
                 (mv-nth
                  0
                  (d-e-cc-contents
                   fat32$c
                   (mv-nth 0
                           (find-d-e
                            (make-d-e-list
                             (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c root-d-e)))
                            (car path))))))
                (d-e-set-first-cluster-file-size
                 (mv-nth
                  1
                  (place-contents
                   (update-fati
                    (nth
                     0
                     (find-n-free-clusters
                      (effective-fat
                       (mv-nth
                        0
                        (clear-cc
                         fat32$c
                         (d-e-first-cluster
                          (d-e-set-filename
                           '(0 0 0 0 0 0 0 0 0 0 0 0
                               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (cadr path)))
                         0)))
                      1))
                    (fat32-update-lower-28
                     (fati
                      (nth
                       0
                       (find-n-free-clusters
                        (effective-fat
                         (mv-nth
                          0
                          (clear-cc
                           fat32$c
                           (d-e-first-cluster
                            (d-e-set-filename
                             '(0 0 0 0 0 0 0 0 0 0 0 0
                                 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                             (cadr path)))
                           0)))
                        1))
                      (mv-nth
                       0
                       (clear-cc
                        fat32$c
                        (d-e-first-cluster
                         (d-e-set-filename
                          '(0 0 0 0 0 0 0 0 0 0 0 0
                              0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                          (cadr path)))
                        0)))
                     268435455)
                    (mv-nth
                     0
                     (clear-cc
                      fat32$c
                      (d-e-first-cluster
                       (d-e-set-filename
                        '(0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                        (cadr path)))
                      0)))
                   (d-e-set-filename
                    '(0 0 0 0 0 0 0 0 0 0 0 0
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                    (cadr path))
                   (lofat-file->contents file)
                   (length (lofat-file->contents file))
                   (nth
                    0
                    (find-n-free-clusters
                     (effective-fat
                      (mv-nth
                       0
                       (clear-cc
                        fat32$c
                        (d-e-first-cluster
                         (d-e-set-filename
                          '(0 0 0 0 0 0 0 0 0 0 0 0
                              0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                          (cadr path)))
                        0)))
                     1))))
                 (nth
                  0
                  (find-n-free-clusters
                   (effective-fat
                    (mv-nth
                     0
                     (clear-cc
                      fat32$c
                      (d-e-first-cluster
                       (d-e-set-filename
                        '(0 0 0 0 0 0 0 0 0 0 0 0
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                        (cadr path)))
                      0)))
                   1))
                 (length (lofat-file->contents file)))))))
            root-d-e)))
         entry-limit))))
     :hints (("goal" :in-theory (enable (:definition butlast)
                                        (:definition nfix)
                                        (:definition length)
                                        (:definition min)))
             ("[1]goal" :in-theory (enable (:definition butlast)
                                           (:definition nfix)
                                           (:definition length)
                                           (:definition min))))))

  (local
   (defthm
     lofat-place-file-correctness-1-lemma-67
     (implies (lofat-regular-file-p file)
              (< (length (m1-file-contents-fix (lofat-file->contents file)))
                 4294967296))
     :hints (("goal" :in-theory (enable (:definition butlast)
                                        (:definition nfix)
                                        (:definition length)
                                        (:definition min))))
     :rule-classes (:linear :rewrite)))

  (defthm
    lofat-place-file-correctness-1-lemma-44
    (implies (and (< (d-e-first-cluster root-d-e)
                     (+ 2 (count-of-clusters fat32$c)))
                  (<= 1
                      (min (count-free-clusters (effective-fat fat32$c))
                           1)))
             (< (nth '0
                     (find-n-free-clusters (effective-fat fat32$c)
                                           '1))
                (binary-+ '2
                          (count-of-clusters fat32$c))))
    :hints (("goal" :in-theory (enable (:definition butlast)
                                       (:definition nfix)
                                       (:definition length)
                                       (:definition min))))
    :rule-classes (:linear :rewrite))

  (local (include-book "std/lists/intersectp" :dir :system))

  (defthm
    lofat-place-file-correctness-1-lemma-1
    (implies
     (and
      (good-root-d-e-p root-d-e fat32$c)
      (non-free-index-listp x (effective-fat fat32$c))
      (fat32-filename-list-p path)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         entry-limit))
       0)
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c root-d-e))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         entry-limit)))
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         entry-limit)))
      (lofat-file-p file)
      (or (and (lofat-regular-file-p file)
               (<= (len (make-clusters (lofat-file->contents file)
                                       (cluster-size fat32$c)))
                   (count-free-clusters (effective-fat fat32$c))))
          (and (equal (lofat-file->contents file) nil)
               (<= 1
                   (count-free-clusters (effective-fat fat32$c)))))
      (zp (mv-nth 1
                  (lofat-place-file fat32$c root-d-e path file)))
      (integerp entry-limit)
      (<
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
          entry-limit)))
       entry-limit))
     (and
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c root-d-e path file))
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents
                   (mv-nth 0
                           (lofat-place-file fat32$c root-d-e path file))
                   root-d-e)))
         entry-limit))
       0)
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c root-d-e path file))
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents
                   (mv-nth 0
                           (lofat-place-file fat32$c root-d-e path file))
                   root-d-e)))
         entry-limit)))
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c root-d-e path file))
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents
                   (mv-nth 0
                           (lofat-place-file fat32$c root-d-e path file))
                   root-d-e)))
         entry-limit))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           entry-limit))
         path
         (m1-file d-e (lofat-file->contents file)))))
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           entry-limit))
         path
         (m1-file d-e (lofat-file->contents file))))
       0)))
    :hints
    (("goal"
      :induct (induction-scheme entry-limit
                                fat32$c file path root-d-e x)
      :expand (lofat-place-file fat32$c root-d-e path file)
      :in-theory
      (e/d (hifat-place-file (:rewrite lofat-to-hifat-inversion-lemma-4)
                             hifat-find-file)
           ((:definition find-d-e)
            (:definition place-d-e)
            (:rewrite d-e-p-when-member-equal-of-d-e-list-p)
            (:rewrite lofat-fs-p-of-lofat-place-file-lemma-1)
            (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                      . 5)))
      :do-not-induct t))
    :rule-classes
    ((:rewrite
      :corollary
      (implies
       (and
        (good-root-d-e-p root-d-e fat32$c)
        (non-free-index-listp x (effective-fat fat32$c))
        (fat32-filename-list-p path)
        (equal
         (mv-nth
          3
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           entry-limit))
         0)
        (not-intersectp-list
         (mv-nth 0 (d-e-cc fat32$c root-d-e))
         (mv-nth
          2
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           entry-limit)))
        (not-intersectp-list
         x
         (mv-nth
          2
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           entry-limit)))
        (lofat-file-p file)
        (or (and (lofat-regular-file-p file)
                 (<= (len (make-clusters (lofat-file->contents file)
                                         (cluster-size fat32$c)))
                     (count-free-clusters (effective-fat fat32$c))))
            (and (equal (lofat-file->contents file) nil)
                 (<= 1
                     (count-free-clusters (effective-fat fat32$c)))))
        (zp (mv-nth 1
                    (lofat-place-file fat32$c root-d-e path file)))
        (integerp entry-limit)
        (<
         (hifat-entry-count
          (mv-nth
           0
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            entry-limit)))
         entry-limit))
       (not-intersectp-list
        x
        (mv-nth
         2
         (lofat-to-hifat-helper
          (mv-nth 0
                  (lofat-place-file fat32$c root-d-e path file))
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents
                    (mv-nth 0
                            (lofat-place-file fat32$c root-d-e path file))
                    root-d-e)))
          entry-limit))))))))

(defthm
  lofat-place-file-correctness-1
  (implies
   (and
    (good-root-d-e-p root-d-e fat32$c)
    (fat32-filename-list-p path)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c root-d-e))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit)))
    (lofat-file-p file)
    (or (and (lofat-regular-file-p file)
             (<= (len (make-clusters (lofat-file->contents file)
                                     (cluster-size fat32$c)))
                 (count-free-clusters (effective-fat fat32$c))))
        (and (equal (lofat-file->contents file) nil)
             (<= 1
                 (count-free-clusters (effective-fat fat32$c)))))
    (zp (mv-nth 1
                (lofat-place-file fat32$c root-d-e path file)))
    (integerp entry-limit)
    (<
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
        entry-limit)))
     entry-limit))
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-place-file fat32$c root-d-e path file))
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents
                 (mv-nth 0
                         (lofat-place-file fat32$c root-d-e path file))
                 root-d-e)))
       entry-limit))
     0)
    (hifat-equiv
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-place-file fat32$c root-d-e path file))
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents
                 (mv-nth 0
                         (lofat-place-file fat32$c root-d-e path file))
                 root-d-e)))
       entry-limit))
     (mv-nth
      0
      (hifat-place-file
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         entry-limit))
       path
       (m1-file d-e (lofat-file->contents file)))))
    (equal
     (mv-nth
      1
      (hifat-place-file
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         entry-limit))
       path
       (m1-file d-e (lofat-file->contents file))))
     0)))
  :hints
  (("goal"
    :in-theory
    (disable lofat-place-file-correctness-1-lemma-1
             (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                       . 5)
             lofat-place-file)
    :use (:instance lofat-place-file-correctness-1-lemma-1
                    (x nil))
    :do-not-induct t)))
