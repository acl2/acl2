(in-package "ACL2")

(include-book "../eqfat")
(local (include-book "std/lists/intersectp" :dir :system))

;  lofat-place-file.lisp                                Mihir Mehta

;; get-cc-alt really should be disabled here if it can!
(local
 (in-theory (e/d ((:rewrite hifat-equiv-of-cons-lemma-4)
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
                  (:rewrite not-intersectp-list-when-subsetp-2)
                  (:rewrite no-duplicatesp-of-member)
                  (:rewrite then-subseq-same-2)
                  (:rewrite subseq-of-length-1)
                  (:rewrite nth-when->=-n-len-l)
                  (:rewrite car-of-nthcdr)
                  (:rewrite assoc-of-car-when-member)
                  (:rewrite true-listp-when-string-list)
                  intersect-with-subset
                  subsetp-member
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
                  (:definition true-listp)
                  (:rewrite
                   not-intersectp-list-of-set-difference$-lemma-1)
                  make-list-ac last
                  (:rewrite lofat-find-file-correctness-lemma-2)
                  binary-append
                  (:rewrite
                   get-cc-contents-of-place-contents-coincident-lemma-3)
                  (:rewrite
                   lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-4)
                  (:rewrite intersectp-when-subsetp)
                  (:rewrite subsetp-append1)
                  (:linear nth-when-d-e-p)
                  (:rewrite subsetp-when-atom-right)
                  (:rewrite
                   member-intersectp-of-set-difference$-lemma-1)
                  (:rewrite
                   d-e-p-when-member-equal-of-d-e-list-p)
                  (:type-prescription painful-debugging-lemma-9)
                  (:rewrite member-intersectp-binary-append . 1)
                  (:rewrite subsetp-trans2)
                  (:rewrite subsetp-trans)
                  (:rewrite subdir-contents-p-when-zero-length)
                  (:rewrite intersectp-member . 1)
                  (:rewrite
                   flatten-subset-no-duplicatesp-lemma-1)
                  (:rewrite last-when-equal-len-1)
                  (:rewrite m1-file-alist-p-when-subsetp-equal)
                  (:linear
                   lofat-find-file-correctness-1-lemma-6)
                  (:linear
                   lower-bounded-integer-listp-of-find-n-free-clusters)
                  (:linear find-n-free-clusters-correctness-2)
                  (:rewrite
                   find-n-free-clusters-correctness-2 . 2)
                  (:linear reserved-area-string-guard-lemma-2)
                  (:rewrite intersect-equal-of-cons-left)
                  (:rewrite effective-fat-of-clear-cc . 3)
                  (:rewrite d-e-cc-of-update-dir-contents)
                  (:rewrite d-e-cc-contents-of-update-dir-contents-disjoint)
                  (:rewrite natp-of-car-when-nat-listp)))))

(local
 (defthm
   d-e-cc-contents-of-lofat-place-file-coincident-lemma-4
   (implies (and (equal (nth 0 (explode filename))
                        (code-char 0))
                 (useful-d-e-list-p d-e-list))
            (equal (mv-nth 1 (find-d-e d-e-list filename))
                   *enoent*))
   :hints (("goal" :in-theory (enable useful-d-e-list-p)))))

;; Hypotheses minimised...
(defthm
  lofat-place-file-correctness-lemma-53
  (implies
   (and (>= (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name)))
            *ms-first-data-cluster*)
        (< (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name)))
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32$c)))
        (useful-d-e-list-p d-e-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               0))
   (not-intersectp-list
    (mv-nth 0
            (d-e-cc fat32$c
                    (mv-nth 0 (find-d-e d-e-list name))))
    (mv-nth
     2
     (lofat-to-hifat-helper
      fat32$c
      (place-d-e
       d-e-list
       (d-e-set-first-cluster-file-size (mv-nth 0 (find-d-e d-e-list name))
                                        0 0))
      entry-limit))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lofat-to-hifat-helper find-d-e place-d-e not-intersectp-list)
     ((:rewrite nth-of-effective-fat)
      (:rewrite nth-of-nats=>chars)
      (:rewrite
       hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e-lemma-3)
      (:linear nth-when-d-e-p)
      (:rewrite explode-of-d-e-filename)
      (:rewrite d-e-list-p-of-cdr-when-d-e-list-p)))
    :induct (lofat-to-hifat-helper fat32$c d-e-list entry-limit)
    :do-not-induct t)))

(defthm
  lofat-place-file-correctness-lemma-86
  (implies
   (and
    (not (equal (mv-nth 1
                        (find-d-e d-e-list
                                  (d-e-filename d-e)))
                0))
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c
                                          d-e-list entry-limit))
           0)
    (equal
     (strip-cars fs)
     (strip-cars (mv-nth 0
                         (lofat-to-hifat-helper fat32$c
                                                d-e-list entry-limit))))
    (useful-d-e-list-p d-e-list))
   (not (consp (assoc-equal (d-e-filename d-e)
                            fs))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite member-of-strip-cars))
    :use
    ((:instance (:rewrite member-of-strip-cars)
                (alist fs)
                (x (d-e-filename d-e)))
     (:instance
      (:rewrite member-of-strip-cars)
      (alist (mv-nth 0
                     (lofat-to-hifat-helper fat32$c
                                            d-e-list entry-limit)))
      (x (d-e-filename d-e)))))))

;; Hypotheses are minimal.
(defthm
  lofat-place-file-correctness-lemma-57
  (implies
   (and
    (useful-d-e-list-p d-e-list)
    (not (d-e-directory-p (d-e-fix d-e)))
    (zp (mv-nth 3
                (lofat-to-hifat-helper fat32$c
                                       d-e-list entry-limit)))
    (> (nfix entry-limit)
       (hifat-entry-count
        (mv-nth 0
                (lofat-to-hifat-helper fat32$c
                                       d-e-list entry-limit))))
    (or
     (< (d-e-first-cluster (d-e-fix d-e))
        2)
     (<= (+ 2 (count-of-clusters fat32$c))
         (d-e-first-cluster (d-e-fix d-e)))
     (and
      (equal
       (mv-nth
        1
        (d-e-cc-contents fat32$c (d-e-fix d-e)))
       0)
      (no-duplicatesp-equal
       (mv-nth 0
               (d-e-cc fat32$c (d-e-fix d-e))))
      (not-intersectp-list
       (mv-nth 0
               (d-e-cc fat32$c (d-e-fix d-e)))
       (mv-nth 2
               (lofat-to-hifat-helper fat32$c
                                      d-e-list entry-limit))))))
   (equal (mv-nth 3
                  (lofat-to-hifat-helper fat32$c
                                         (place-d-e d-e-list d-e)
                                         entry-limit))
          0))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lofat-to-hifat-helper hifat-entry-count not-intersectp-list
                            lofat-place-file-correctness-lemma-41)
     ((:rewrite nth-of-effective-fat)
      (:rewrite nth-of-nats=>chars)
      (:linear nth-when-d-e-p)
      (:rewrite explode-of-d-e-filename)
      (:rewrite take-of-len-free)
      (:rewrite
       hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e-lemma-3)
      (:rewrite put-assoc-equal-without-change . 2)
      (:rewrite nats=>chars-of-take)
      (:rewrite hifat-subsetp-reflexive-lemma-3)
      (:rewrite lofat-place-file-correctness-lemma-83)
      (:rewrite subsetp-append1)
      (:rewrite lofat-place-file-correctness-lemma-52)
      (:rewrite m1-directory-file-p-when-m1-file-p)
      (:rewrite hifat-to-lofat-inversion-lemma-2)))
    :induct (lofat-to-hifat-helper fat32$c
                                   d-e-list entry-limit)
    :do-not-induct t
    :expand (:free (fat32$c d-e d-e-list entry-limit)
                   (lofat-to-hifat-helper fat32$c
                                          (cons d-e d-e-list)
                                          entry-limit)))))

(defthm
  d-e-cc-contents-of-lofat-place-file-disjoint-lemma-1
  (implies
   (and (>= (d-e-first-cluster d-e)
            *ms-first-data-cluster*)
        (equal (mv-nth 1
                       (d-e-cc fat32$c d-e))
               0)
        (< (d-e-first-cluster d-e)
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32$c)))
        (< (nfix n1)
           (len (find-n-free-clusters (effective-fat fat32$c)
                                      n2)))
        (lofat-fs-p fat32$c))
   (not
    (member-equal (nth n1
                       (find-n-free-clusters (effective-fat fat32$c)
                                             n2))
                  (mv-nth 0
                          (d-e-cc fat32$c d-e)))))
  :hints
  (("goal"
    :in-theory (e/d (nth-when->=-n-len-l subsetp-member)
                    (non-free-index-listp-correctness-2))
    :use
    (:instance non-free-index-listp-correctness-2
               (fa-table (effective-fat fat32$c))
               (x (mv-nth 0
                          (d-e-cc fat32$c d-e)))
               (key (nth n1
                         (find-n-free-clusters (effective-fat fat32$c)
                                               n2)))))))

(defthm
  lofat-place-file-correctness-lemma-64
  (implies
   (and
    (hifat-equiv (mv-nth 0
                         (lofat-to-hifat-helper fat32$c
                                                d-e-list entry-limit1))
                 fs)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c
                                          d-e-list entry-limit1))
           0)
    (>= (nfix entry-limit2)
        (mv-nth 1
                (lofat-to-hifat-helper fat32$c
                                       d-e-list entry-limit1))))
   (hifat-equiv (mv-nth 0
                        (lofat-to-hifat-helper fat32$c
                                               d-e-list entry-limit2))
                fs))
  :hints (("goal" :do-not-induct t
           :in-theory (disable lofat-to-hifat-helper-correctness-4)
           :use lofat-to-hifat-helper-correctness-4)))

(defthm
  d-e-cc-contents-of-lofat-place-file-coincident-lemma-1
  (implies
   (and
    (<=
     2
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 name))))
    (<
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 name)))
     (+ 2 (count-of-clusters fat32$c)))
    (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
           0)
    (equal
     (mv-nth 3
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c d-e))
     (mv-nth 2
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              entry-limit))))
   (not
    (member-equal
     (nth
      '0
      (find-n-free-clusters
       (set-indices-in-fa-table
        (effective-fat fat32$c)
        (mv-nth
         '0
         (d-e-cc
          fat32$c
          (mv-nth
           '0
           (find-d-e (make-d-e-list (mv-nth '0
                                            (d-e-cc-contents fat32$c d-e)))
                     name))))
        (make-list-ac
         (len
          (mv-nth
           '0
           (d-e-cc
            fat32$c
            (mv-nth
             '0
             (find-d-e (make-d-e-list (mv-nth '0
                                              (d-e-cc-contents fat32$c d-e)))
                       name)))))
         '0
         'nil))
       '1))
     (mv-nth '0 (d-e-cc fat32$c d-e)))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite non-free-index-listp-correctness-2 . 1))
    :use
    ((:instance
      (:rewrite non-free-index-listp-correctness-2 . 1)
      (x (mv-nth 0 (d-e-cc fat32$c d-e)))
      (key
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
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              name))))
          (make-list-ac
           (len
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                name)))))
           0 nil))
         1)))
      (fa-table
       (set-indices-in-fa-table
        (effective-fat fat32$c)
        (mv-nth
         0
         (d-e-cc
          fat32$c
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     name))))
        (make-list-ac
         (len
          (mv-nth
           0
           (d-e-cc
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              name)))))
         0 nil))))))))

;; While proving the correctness of lofat-place-file, this bears remembering.
(thm
 (implies
  (and (hifat-no-dups-p fs)
       (m1-file-alist-p fs)
       (zp (mv-nth 1 (hifat-place-file fs path file)))
       (consp (assoc-equal (fat32-filename-fix (car path))
                           fs))
       (atom (cdr path)))
  (equal
   (m1-directory-file-p (cdr (assoc-equal (fat32-filename-fix (car path))
                                          fs)))
   (m1-directory-file-p (m1-file-fix file))))
 :hints (("goal" :in-theory (enable hifat-place-file))))

(encapsulate
  ()

  (local (include-book "arithmetic-3/top" :dir :system))

  (defthm lofat-place-file-helper-guard-lemma-1
    (<= (* *ms-d-e-length*
           (len (make-d-e-list dir-contents)))
        (len (explode dir-contents)))
    :hints (("goal" :do-not-induct t
             :use len-of-make-d-e-list))
    :rule-classes :linear))

(defund
  lofat-place-file-helper
  (fat32$c root-d-e path file)
  (declare
   (xargs :stobjs fat32$c
          :guard (and (lofat-fs-p fat32$c)
                      (d-e-p root-d-e)
                      (>= (d-e-first-cluster root-d-e)
                          *ms-first-data-cluster*)
                      (< (d-e-first-cluster root-d-e)
                         (+ *ms-first-data-cluster*
                            (count-of-clusters fat32$c)))
                      (fat32-filename-list-p path)
                      (lofat-file-p file)
                      (or (lofat-regular-file-p file)
                          (equal (lofat-file->contents file)
                                 nil)))
          :guard-debug t
          :guard-hints (("goal" :in-theory (disable nfix)))))
  (b*
      (((mv root-d-e-cc-contents &)
        (d-e-cc-contents fat32$c root-d-e))
       (path-head (mbe :logic (fat32-filename-fix (car path))
                       :exec (if (consp path)
                                 (fat32-filename-fix (car path))
                               *empty-fat32-name*)))
       ((mv d-e error-code)
        (find-d-e (make-d-e-list root-d-e-cc-contents)
                  path-head))
       ((mv root-d-e-cc &)
        (d-e-cc fat32$c root-d-e))
       (file-clusters
        (mbe :logic (make-clusters (lofat-file->contents file)
                                   (cluster-size fat32$c))
             :exec (if (stringp (lofat-file->contents file))
                       (make-clusters (lofat-file->contents file)
                                      (cluster-size fat32$c))
                     nil)))
       (free-clusters-2
        (stobj-find-n-free-clusters
         fat32$c
         (nfix
          (+
           (+
            (len file-clusters)
            (len
             (make-clusters
              (nats=>string
               (insert-d-e (string=>nats root-d-e-cc-contents)
                           (d-e-install-directory-bit
                            (make-d-e-with-filename path-head)
                            nil)))
              (cluster-size fat32$c))))
           (- (len root-d-e-cc))))))
       (free-clusters-3
        (stobj-find-n-free-clusters
         fat32$c
         (nfix
          (+
           (+
            (len file-clusters)
            (len
             (make-clusters
              (nats=>string
               (insert-d-e (string=>nats root-d-e-cc-contents)
                           d-e))
              (cluster-size fat32$c))))
           (- (len root-d-e-cc))))))
       (free-clusters-5 (stobj-find-n-free-clusters fat32$c 1)))
    (cond
     ((and
       (<= (len file-clusters)
           (len (stobj-find-n-free-clusters
                 fat32$c (len file-clusters))))
       (not (equal error-code 0))
       (lofat-regular-file-p file)
       (< 0
          (len (explode (lofat-file->contents file))))
       (<= 1 (len free-clusters-5))
       (<= (+ 96
              (* 32
                 (len (make-d-e-list root-d-e-cc-contents))))
           2097152)
       (<=
        (+
         (+
          (len file-clusters)
          (len
           (make-clusters
            (nats=>string
             (insert-d-e (string=>nats root-d-e-cc-contents)
                         (d-e-install-directory-bit
                          (make-d-e-with-filename path-head)
                          nil)))
            (cluster-size fat32$c))))
         (- (len root-d-e-cc)))
        (len free-clusters-2)))
      0)
     ((and
       (<= (len file-clusters)
           (len (stobj-find-n-free-clusters
                 fat32$c (len file-clusters))))
       (not (equal error-code 0))
       (lofat-regular-file-p file)
       (< 0
          (len (explode (lofat-file->contents file))))
       (<= 1 (len free-clusters-5))
       (<= (+ 96
              (* 32
                 (len (make-d-e-list root-d-e-cc-contents))))
           2097152)
       (<
        (len free-clusters-2)
        (+
         (+
          (len file-clusters)
          (len
           (make-clusters
            (nats=>string
             (insert-d-e (string=>nats root-d-e-cc-contents)
                         (d-e-install-directory-bit
                          (make-d-e-with-filename path-head)
                          nil)))
            (cluster-size fat32$c))))
         (- (len root-d-e-cc)))))
      28)
     ((and
       (not (equal error-code 0))
       (lofat-directory-file-p file)
       (<= 1 (len free-clusters-5))
       (<= (+ 96
              (* 32
                 (len (make-d-e-list root-d-e-cc-contents))))
           2097152)
       (not (lofat-file->contents file))
       (<=
        (+
         (+
          1
          (len
           (make-clusters
            (nats=>string
             (insert-d-e (string=>nats root-d-e-cc-contents)
                         (d-e-install-directory-bit
                          (make-d-e-with-filename path-head)
                          t)))
            (cluster-size fat32$c))))
         (- (len root-d-e-cc)))
        (len
         (stobj-find-n-free-clusters
          fat32$c
          (nfix
           (+
            (+
             1
             (len
              (make-clusters
               (nats=>string
                (insert-d-e
                 (string=>nats root-d-e-cc-contents)
                 (d-e-install-directory-bit
                  (make-d-e-with-filename path-head)
                  t)))
               (cluster-size fat32$c))))
            (- (len root-d-e-cc))))))))
      0)
     ((and
       (not (equal error-code 0))
       (lofat-directory-file-p file)
       (<= 1 (len free-clusters-5))
       (<= (+ 96
              (* 32
                 (len (make-d-e-list root-d-e-cc-contents))))
           2097152)
       (not (lofat-file->contents file)))
      28)
     ((and
       (equal (len (stobj-find-n-free-clusters
                    fat32$c (len file-clusters)))
              (len file-clusters))
       (equal error-code 0)
       (not (d-e-directory-p d-e))
       (lofat-regular-file-p file)
       (< 0
          (len (explode (lofat-file->contents file))))
       (<= (+ 2 (count-of-clusters fat32$c))
           (d-e-first-cluster d-e))
       (<= 1 (len free-clusters-5))
       (<= 2 (d-e-first-cluster d-e))
       (<=
        (+
         (+
          (len file-clusters)
          (len
           (make-clusters
            (nats=>string
             (insert-d-e (string=>nats root-d-e-cc-contents)
                         d-e))
            (cluster-size fat32$c))))
         (- (len root-d-e-cc)))
        (len free-clusters-3)))
      0)
     ((and
       (equal error-code 0)
       (not (d-e-directory-p d-e))
       (lofat-regular-file-p file)
       (< 0
          (len (explode (lofat-file->contents file))))
       (<= 2 (d-e-first-cluster d-e))
       (< (d-e-first-cluster d-e)
          (+ 2 (count-of-clusters fat32$c)))
       (b*
           (((mv d-e-cc &) (d-e-cc fat32$c d-e))
            (free-clusters-1
             (stobj-find-n-free-clusters
              fat32$c
              (nfix
               (+
                (+
                 (len file-clusters)
                 (len
                  (make-clusters
                   (nats=>string
                    (insert-d-e (string=>nats root-d-e-cc-contents)
                                d-e))
                   (cluster-size fat32$c))))
                (- (+ (len root-d-e-cc) (len d-e-cc)))))))
            (free-clusters-4 (stobj-find-n-free-clusters
                              fat32$c
                              (nfix (+ (len file-clusters)
                                       (- (len d-e-cc)))))))
         (and
          (<= (+ (len file-clusters) (- (len d-e-cc)))
              (len free-clusters-4))
          (<=
           (+
            (+
             (len file-clusters)
             (len
              (make-clusters
               (nats=>string
                (insert-d-e (string=>nats root-d-e-cc-contents)
                            d-e))
               (cluster-size fat32$c))))
            (- (+ (len root-d-e-cc) (len d-e-cc))))
           (len free-clusters-1)))))
      0)
     ((and
       (<=
        (+
         (+
          (len file-clusters)
          (len
           (make-clusters
            (nats=>string
             (insert-d-e (string=>nats root-d-e-cc-contents)
                         d-e))
            (cluster-size fat32$c))))
         (- (len root-d-e-cc)))
        (len free-clusters-3))
       (equal (len (stobj-find-n-free-clusters
                    fat32$c (len file-clusters)))
              (len file-clusters))
       (equal error-code 0)
       (not (d-e-directory-p d-e))
       (lofat-regular-file-p file)
       (< 0
          (len (explode (lofat-file->contents file))))
       (< (d-e-first-cluster d-e) 2)
       (<= 1 (len free-clusters-5)))
      0)
     ((lofat-regular-file-p file) 28)
     ((and
       (<= *ms-first-data-cluster*
           (d-e-first-cluster d-e))
       (< (d-e-first-cluster d-e)
          (+ *ms-first-data-cluster*
             (count-of-clusters fat32$c)))
       (b*
           (((mv d-e-cc &) (d-e-cc fat32$c d-e)))
         (<
          (len
           (stobj-find-n-free-clusters
            fat32$c
            (nfix
             (+
              (+
               1
               (len
                (make-clusters
                 (nats=>string
                  (insert-d-e (string=>nats root-d-e-cc-contents)
                              d-e))
                 (cluster-size fat32$c))))
              (- (+ (len root-d-e-cc) (len d-e-cc)))))))
          (+
           (+
            1
            (len
             (make-clusters
              (nats=>string
               (insert-d-e (string=>nats root-d-e-cc-contents)
                           d-e))
              (cluster-size fat32$c))))
           (- (+ (len root-d-e-cc) (len d-e-cc)))))))
      28)
     (t 0))))

;; This is a no-change loser.
(defun
    lofat-place-file
    (fat32$c root-d-e path file)
  (declare
   (xargs :guard (and (lofat-fs-p fat32$c)
                      (d-e-p root-d-e)
                      (>= (d-e-first-cluster root-d-e)
                          *ms-first-data-cluster*)
                      (< (d-e-first-cluster root-d-e)
                         (+ *ms-first-data-cluster*
                            (count-of-clusters fat32$c)))
                      (fat32-filename-list-p path)
                      (lofat-file-p file)
                      (or (lofat-regular-file-p file)
                          (equal (lofat-file->contents file)
                                 nil)))
          :measure (acl2-count path)
          :stobjs fat32$c
          :verify-guards nil))
  (b*
      ((file (mbe :exec file :logic (lofat-file-fix file)))
       (update-dir-contents-error-code
        (lofat-place-file-helper fat32$c root-d-e path file))
       ((unless (consp path))
        (mv fat32$c *enoent*))
       (name (mbe :logic (fat32-filename-fix (car path))
                  :exec (car path)))
       ((mv dir-contents &)
        (d-e-cc-contents fat32$c root-d-e))
       (d-e-list (make-d-e-list dir-contents))
       ((mv d-e error-code)
        (find-d-e d-e-list name))
       (d-e (if (equal error-code 0)
                d-e (make-d-e-with-filename name)))
       (d-e (if (equal error-code 0)
                d-e
              (d-e-install-directory-bit
               d-e (lofat-directory-file-p file))))
       ((when (and (not (equal error-code 0))
                   (consp (cdr path))))
        ;; This used to be the home of a bug! Initially the error code we
        ;; returned here was *enotdir* and the error code we returned in
        ;; hifat-place-file was *enoent*. Clearly, the former was wrong, which
        ;; we fixed.
        (mv fat32$c *enoent*))
       ((when (and (consp (cdr path))
                   (not (d-e-directory-p d-e))))
        (mv fat32$c *enotdir*))
       (first-cluster (d-e-first-cluster d-e))
       ((when (and (not (equal error-code 0))
                   (consp (cdr path))))
        ;; This used to be the home of a bug! Initially the error code we
        ;; returned here was *eio* and the error code we returned in
        ;; hifat-place-file was *enotdir*. Clearly, both were wrong, and in
        ;; time both were fixed.
        (mv fat32$c *enoent*))
       ((when (and (or (< first-cluster 2)
                       (<= (+ 2 (count-of-clusters fat32$c))
                           first-cluster))
                   (consp (cdr path))))
        (mv fat32$c *eio*))
       ((mv cc &)
        (if
            (and
             (<= *ms-first-data-cluster*
                 (d-e-first-cluster d-e))
             (< (d-e-first-cluster d-e)
                (+ *ms-first-data-cluster*
                   (count-of-clusters fat32$c))))
            (d-e-cc fat32$c d-e)
          (mv nil *eio*)))
       (last-value
        (mbe
         :logic
         (fat32-entry-mask (fati (car (last cc)) fat32$c))
         :exec
         (if (consp (last cc))
             (fat32-entry-mask (fati (car (last cc)) fat32$c))
           (fat32-entry-mask (fati 0 fat32$c)))))
       ((when (consp (cdr path)))
        (lofat-place-file fat32$c d-e (cdr path)
                          file))
       (length (if (d-e-directory-p d-e)
                   *ms-max-dir-size* (d-e-file-size d-e)))
       ((when (and (d-e-directory-p d-e)
                   (lofat-regular-file-p file)))
        (mv fat32$c *enoent*))
       ;; This used to be the home of a bug! We used to return *enotdir* here.
       ((when (and (not (d-e-directory-p d-e))
                   (lofat-directory-file-p file)))
        (mv fat32$c *eexist*))
       ((mv fat32$c &)
        (if (or (< first-cluster 2)
                (<= (+ 2 (count-of-clusters fat32$c))
                    first-cluster))
            (mv fat32$c 0)
          (clear-cc fat32$c first-cluster length)))
       (file-length (if (lofat-regular-file-p file)
                        (length (lofat-file->contents file))
                      (+ *ms-d-e-length* *ms-d-e-length*)))
       (new-dir-contents
        (nats=>string
         (insert-d-e (string=>nats dir-contents)
                     (d-e-set-first-cluster-file-size d-e 0 0))))
       ((when (and (zp file-length)
                   (<= (length new-dir-contents)
                       *ms-max-dir-size*)))
        (b*
            (((mv fat32$c error-code)
              (update-dir-contents fat32$c (d-e-first-cluster root-d-e)
                                   new-dir-contents))
             ((when (or
                     (equal error-code 0)
                     (atom cc)))
              (mv fat32$c error-code))
             (fat32$c (stobj-set-indices-in-fa-table
                       fat32$c cc
                       (append (cdr cc) (list last-value)))))
          (mv fat32$c error-code)))
       ((when (zp file-length))
        (b*
            (((when (atom cc))
              (mv fat32$c *ENOSPC*))
             (fat32$c (stobj-set-indices-in-fa-table
                       fat32$c cc
                       (append (cdr cc) (list last-value)))))
          (mv fat32$c *ENOSPC*)))
       (indices (stobj-find-n-free-clusters fat32$c 1))
       ((when (< (len indices) 1))
        (mv fat32$c *enospc*))
       (first-cluster (nth 0 indices))
       (first-cluster-val (fati first-cluster fat32$c))
       (fat32$c (update-fati first-cluster (fat32-update-lower-28
                                            first-cluster-val
                                            *ms-end-of-cc*)
                             fat32$c))
       (contents (if (lofat-regular-file-p file)
                     (lofat-file->contents file)
                   (make-empty-subdir-contents
                    first-cluster
                    (d-e-first-cluster root-d-e))))
       (file-length (if (lofat-regular-file-p file)
                        (length contents)
                      0))
       (new-dir-contents-length
        (b*
            (((mv & error-code)
              (find-d-e (make-d-e-list dir-contents) (d-e-filename d-e))))
          (if (zp error-code)
              (+ 64
                 (* 32
                    (len (make-d-e-list dir-contents))))
            (+ 96
               (* 32
                  (len (make-d-e-list dir-contents)))))))
       ((unless
            (and (<= new-dir-contents-length *ms-max-dir-size*)
                 (equal update-dir-contents-error-code 0)))
        (b*
            ((fat32$c (update-fati first-cluster first-cluster-val fat32$c))
             ((unless (consp cc)) (mv fat32$c *enospc*))
             (fat32$c (stobj-set-indices-in-fa-table
                       fat32$c cc
                       (append (cdr cc) (list last-value)))))
          (mv fat32$c *enospc*)))
       ((mv fat32$c d-e error-code &)
        (place-contents fat32$c
                        d-e contents file-length first-cluster))
       ((unless (equal error-code 0))
        (b*
            ((fat32$c (update-fati first-cluster first-cluster-val fat32$c))
             ((unless (consp cc)) (mv fat32$c error-code))
             (fat32$c (stobj-set-indices-in-fa-table
                       fat32$c cc
                       (append (cdr cc) (list last-value)))))
          (mv fat32$c error-code)))
       (new-dir-contents
        (nats=>string (insert-d-e (string=>nats dir-contents)
                                  d-e))))
    (update-dir-contents fat32$c (d-e-first-cluster root-d-e)
                         new-dir-contents)))

(defthm
  count-of-clusters-of-lofat-place-file
  (equal
   (count-of-clusters
    (mv-nth
     0
     (lofat-place-file
      fat32$c root-d-e path file)))
   (count-of-clusters fat32$c)))

(defthm lofat-fs-p-of-lofat-place-file-lemma-2
  (implies (and (lofat-file-p file)
                (not (lofat-directory-file-p file)))
           (stringp (lofat-file->contents file)))
  :hints (("goal" :in-theory (enable lofat-directory-file-p
                                     lofat-regular-file-p
                                     lofat-file-p lofat-file-contents-p
                                     lofat-file->contents))))

(defthm
  lofat-fs-p-of-lofat-place-file-lemma-8
  (implies (not (lofat-directory-file-p (lofat-file-fix file)))
           (stringp (lofat-file->contents file)))
  :hints
  (("goal" :use (:instance lofat-fs-p-of-lofat-place-file-lemma-2
                           (file (lofat-file-fix file)))
    :in-theory (disable lofat-fs-p-of-lofat-place-file-lemma-2))))

(defthm
  lofat-fs-p-of-lofat-place-file
  (implies
   (and (lofat-fs-p fat32$c)
        (d-e-p root-d-e)
        (>= (d-e-first-cluster root-d-e)
            *ms-first-data-cluster*)
        (< (d-e-first-cluster root-d-e)
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32$c))))
   (lofat-fs-p (mv-nth 0
                       (lofat-place-file fat32$c
                                         root-d-e path file))))
  :hints (("goal" :induct (lofat-place-file fat32$c
                                            root-d-e path file)
           :in-theory (enable subsetp-member))))

(defthm lofat-place-file-guard-lemma-8
  (implies (not (integerp i))
           (equal (fati i fat32$c)
                  (fati 0 fat32$c)))
  :hints (("goal" :in-theory (enable fati nth))))

(defthm
  lofat-place-file-guard-lemma-7
  (implies (and (d-e-p d-e)
                (< (d-e-first-cluster d-e)
                   (len (effective-fat fat32$c))))
           (< (car (last (mv-nth 0 (d-e-cc fat32$c d-e))))
              (+ 2 (count-of-clusters fat32$c))))
  :hints
  (("goal" :do-not-induct t
    :in-theory (disable car-of-last-when-bounded-nat-listp)
    :use (:instance car-of-last-when-bounded-nat-listp
                    (l (mv-nth '0 (d-e-cc fat32$c d-e)))
                    (b (binary-+ '2
                                 (count-of-clusters fat32$c))))))
  :rule-classes :linear)

(encapsulate
  ()

  (local
   (defthm
     lemma
     (implies
      (<=
       1
       (count-free-clusters
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
               (d-e-cc-contents fat32$c root-d-e)))
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
                 (d-e-cc-contents fat32$c root-d-e)))
               (car path))))))
          0 nil))))
      (not
       (<
        (nth
         '0
         (find-n-free-clusters
          (set-indices-in-fa-table
           (effective-fat fat32$c)
           (mv-nth
            '0
            (d-e-cc
             fat32$c
             (mv-nth
              '0
              (find-d-e
               (make-d-e-list
                (mv-nth
                 '0
                 (d-e-cc-contents fat32$c root-d-e)))
               (car path)))))
           (make-list-ac
            (len
             (mv-nth
              '0
              (d-e-cc
               fat32$c
               (mv-nth
                '0
                (find-d-e
                 (make-d-e-list
                  (mv-nth
                   '0
                   (d-e-cc-contents fat32$c root-d-e)))
                 (car path))))))
            '0
            'nil))
          '1))
        '0)))))

  (verify-guards
    lofat-place-file
    :hints
    (("goal" :in-theory (disable unsigned-byte-p)))))

(defthm
  pseudo-root-d-e-of-lofat-place-file
  (equal
   (pseudo-root-d-e (mv-nth 0
                            (lofat-place-file fat32$c root-d-e path file)))
   (pseudo-root-d-e fat32$c))
  :hints (("goal" :in-theory (enable lofat-place-file)
           :induct (lofat-place-file fat32$c root-d-e path file)
           :do-not-induct t)))

(defthm
  max-entry-count-of-lofat-place-file
  (equal
   (max-entry-count (mv-nth 0
                            (lofat-place-file fat32$c root-d-e path file)))
   (max-entry-count fat32$c))
  :hints (("goal" :in-theory (enable lofat-place-file)
           :induct (lofat-place-file fat32$c root-d-e path file)
           :do-not-induct t)))

(defthmd lofat-place-file-of-lofat-file-fix
  (equal (lofat-place-file fat32$c
                           root-d-e path (lofat-file-fix file))
         (lofat-place-file fat32$c root-d-e path file))
  :hints (("goal" :in-theory (enable lofat-place-file))))

(defcong
  lofat-file-equiv equal
  (lofat-place-file fat32$c root-d-e path file)
  4
  :hints
  (("goal"
    :in-theory (enable lofat-place-file-of-lofat-file-fix))))

(defthm
  lofat-place-file-correctness-lemma-29
  (implies
   (and
    (fat32$c-p (mv-nth 0
                       (clear-cc fat32$c masked-current-cluster length)))
    (< (nfix i)
       (fat-length (mv-nth 0
                           (clear-cc fat32$c
                                     masked-current-cluster length))))
    (equal (fati i
                 (mv-nth 0
                         (clear-cc fat32$c masked-current-cluster length)))
           v))
   (equal
    (update-fati i v
                 (mv-nth 0
                         (clear-cc fat32$c masked-current-cluster length)))
    (mv-nth 0
            (clear-cc fat32$c
                      masked-current-cluster length))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable update-fati-of-fati-when-fat32$c-p)
    :use
    (:instance update-fati-of-fati-when-fat32$c-p
               (fat32$c (mv-nth 0
                                (clear-cc fat32$c
                                          masked-current-cluster length)))))))

(defthm
  lofat-place-file-correctness-lemma-76
  (implies
   (and (lofat-fs-p fat32$c)
        (d-e-directory-p d-e)
        (fat32-masked-entry-p (d-e-first-cluster d-e))
        (<= 2 (d-e-first-cluster d-e))
        (< (d-e-first-cluster d-e)
           (+ (count-of-clusters fat32$c) 2)))
   (equal
    (stobj-set-indices-in-fa-table
     (mv-nth 0
             (clear-cc fat32$c (d-e-first-cluster d-e)
                       2097152))
     (mv-nth 0 (d-e-cc fat32$c d-e))
     (append
      (cdr (mv-nth 0 (d-e-cc fat32$c d-e)))
      (list
       (fat32-entry-mask (fati (car (last (mv-nth 0 (d-e-cc fat32$c d-e))))
                               fat32$c)))))
    fat32$c))
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d (d-e-cc) (clear-cc-reversibility))
    :use (:instance clear-cc-reversibility
                    (masked-current-cluster (d-e-first-cluster d-e))
                    (length *ms-max-dir-size*)))))

(defthm
  lofat-place-file-correctness-lemma-78
  (implies
   (and (lofat-fs-p fat32$c)
        (not (d-e-directory-p d-e))
        (fat32-masked-entry-p (d-e-first-cluster d-e))
        (<= 2 (d-e-first-cluster d-e))
        (< (d-e-first-cluster d-e)
           (+ (count-of-clusters fat32$c) 2)))
   (equal
    (stobj-set-indices-in-fa-table
     (mv-nth 0
             (clear-cc fat32$c (d-e-first-cluster d-e)
                       (d-e-file-size d-e)))
     (mv-nth 0 (d-e-cc fat32$c d-e))
     (append
      (cdr (mv-nth 0 (d-e-cc fat32$c d-e)))
      (list
       (fat32-entry-mask (fati (car (last (mv-nth 0 (d-e-cc fat32$c d-e))))
                               fat32$c)))))
    fat32$c))
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d (d-e-cc) (clear-cc-reversibility))
    :use (:instance clear-cc-reversibility
                    (masked-current-cluster (d-e-first-cluster d-e))
                    (length (d-e-file-size d-e))))))

(defthm
  lofat-place-file-helper-correctness-1
  (implies
   (and
    (consp path)
    (not (consp (cdr path)))
    (lofat-file-p file)
    (or (lofat-regular-file-p file)
        (equal (lofat-file->contents file) nil))
    (good-root-d-e-p root-d-e fat32$c)
    (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c root-d-e)))
    (equal
     (mv-nth 3
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
              entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c root-d-e))
     (mv-nth 2
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
              entry-limit))))
   (equal
    (lofat-place-file-helper fat32$c root-d-e path file)
    (cond
     ((and
       (equal
        (+
         1
         (min
          (count-free-clusters
           (if
               (< (nfix (nth 0
                             (find-n-free-clusters (effective-fat fat32$c)
                                                   1)))
                  (+ (count-of-clusters fat32$c) 2))
               (update-nth
                (nth 0
                     (find-n-free-clusters (effective-fat fat32$c)
                                           1))
                (fat32-update-lower-28
                 (fati (nth 0
                            (find-n-free-clusters (effective-fat fat32$c)
                                                  1))
                       fat32$c)
                 268435455)
                (effective-fat fat32$c))
             (effective-fat fat32$c)))
          (nfix (+ -1
                   (len (make-clusters (lofat-file->contents file)
                                       (cluster-size fat32$c)))))))
        (len (make-clusters (lofat-file->contents file)
                            (cluster-size fat32$c))))
       (not
        (equal
         (mv-nth
          1
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path))))
         0))
       (< 0
          (len (explode (lofat-file->contents file))))
       (<= 1
           (count-free-clusters (effective-fat fat32$c)))
       (lofat-regular-file-p file)
       (<=
        (+
         96
         (* 32
            (len (make-d-e-list (mv-nth 0
                                        (d-e-cc-contents fat32$c root-d-e))))))
        2097152)
       (<=
        (len
         (make-clusters
          (nats=>string
           (insert-d-e
            (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (d-e-set-first-cluster-file-size
             (d-e-install-directory-bit
              (make-d-e-with-filename (fat32-filename-fix (car path)))
              nil)
             (nth 0
                  (find-n-free-clusters (effective-fat fat32$c)
                                        1))
             (len (explode (lofat-file->contents file))))))
          (cluster-size fat32$c)))
        (+ (count-free-clusters (effective-fat fat32$c))
           (len (mv-nth 0 (d-e-cc fat32$c root-d-e)))
           (- (len (make-clusters (lofat-file->contents file)
                                  (cluster-size fat32$c)))))))
      0)
     ((and
       (equal
        (+
         1
         (min
          (count-free-clusters
           (if
               (< (nfix (nth 0
                             (find-n-free-clusters (effective-fat fat32$c)
                                                   1)))
                  (+ (count-of-clusters fat32$c) 2))
               (update-nth
                (nth 0
                     (find-n-free-clusters (effective-fat fat32$c)
                                           1))
                (fat32-update-lower-28
                 (fati (nth 0
                            (find-n-free-clusters (effective-fat fat32$c)
                                                  1))
                       fat32$c)
                 268435455)
                (effective-fat fat32$c))
             (effective-fat fat32$c)))
          (nfix (+ -1
                   (len (make-clusters (lofat-file->contents file)
                                       (cluster-size fat32$c)))))))
        (len (make-clusters (lofat-file->contents file)
                            (cluster-size fat32$c))))
       (not
        (equal
         (mv-nth
          1
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path))))
         0))
       (< 0
          (len (explode (lofat-file->contents file))))
       (<= 1
           (count-free-clusters (effective-fat fat32$c)))
       (<=
        (+
         96
         (* 32
            (len (make-d-e-list (mv-nth 0
                                        (d-e-cc-contents fat32$c root-d-e))))))
        2097152)
       (<
        (+ (count-free-clusters (effective-fat fat32$c))
           (len (mv-nth 0 (d-e-cc fat32$c root-d-e)))
           (- (len (make-clusters (lofat-file->contents file)
                                  (cluster-size fat32$c)))))
        (len
         (make-clusters
          (nats=>string
           (insert-d-e
            (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (d-e-set-first-cluster-file-size
             (d-e-install-directory-bit
              (make-d-e-with-filename (fat32-filename-fix (car path)))
              nil)
             (nth 0
                  (find-n-free-clusters (effective-fat fat32$c)
                                        1))
             (len (explode (lofat-file->contents file))))))
          (cluster-size fat32$c)))))
      28)
     ((and
       (not
        (equal
         (mv-nth
          1
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path))))
         0))
       (lofat-directory-file-p file)
       (not (lofat-regular-file-p file))
       (<= 1
           (count-free-clusters (effective-fat fat32$c)))
       (<=
        (+
         96
         (* 32
            (len (make-d-e-list (mv-nth 0
                                        (d-e-cc-contents fat32$c root-d-e))))))
        2097152)
       (not (lofat-file->contents file))
       (<=
        (len
         (make-clusters
          (nats=>string
           (insert-d-e
            (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (d-e-set-first-cluster-file-size
             (d-e-install-directory-bit
              (make-d-e-with-filename (fat32-filename-fix (car path)))
              t)
             (nth 0
                  (find-n-free-clusters (effective-fat fat32$c)
                                        1))
             0)))
          (cluster-size fat32$c)))
        (+ -1
           (count-free-clusters (effective-fat fat32$c))
           (len (mv-nth 0 (d-e-cc fat32$c root-d-e))))))
      0)
     ((and
       (not
        (equal
         (mv-nth
          1
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path))))
         0))
       (lofat-directory-file-p file)
       (not (lofat-regular-file-p file))
       (<= 1
           (count-free-clusters (effective-fat fat32$c)))
       (<=
        (+
         96
         (* 32
            (len (make-d-e-list (mv-nth 0
                                        (d-e-cc-contents fat32$c root-d-e))))))
        2097152)
       (not (lofat-file->contents file))
       (<
        (+ -1
           (count-free-clusters (effective-fat fat32$c))
           (len (mv-nth 0 (d-e-cc fat32$c root-d-e))))
        (len
         (make-clusters
          (nats=>string
           (insert-d-e
            (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (d-e-set-first-cluster-file-size
             (d-e-install-directory-bit
              (make-d-e-with-filename (fat32-filename-fix (car path)))
              t)
             (nth 0
                  (find-n-free-clusters (effective-fat fat32$c)
                                        1))
             0)))
          (cluster-size fat32$c)))))
      28)
     ((and
       (equal
        (+
         1
         (len
          (find-n-free-clusters
           (if
               (< (nth 0
                       (find-n-free-clusters (effective-fat fat32$c)
                                             1))
                  (+ (count-of-clusters fat32$c) 2))
               (update-nth
                (nth 0
                     (find-n-free-clusters (effective-fat fat32$c)
                                           1))
                (fat32-update-lower-28
                 (fati (nth 0
                            (find-n-free-clusters (effective-fat fat32$c)
                                                  1))
                       fat32$c)
                 268435455)
                (effective-fat fat32$c))
             (effective-fat fat32$c))
           (+ -1
              (len (make-clusters (lofat-file->contents file)
                                  (cluster-size fat32$c)))))))
        (len (make-clusters (lofat-file->contents file)
                            (cluster-size fat32$c))))
       (equal
        (mv-nth
         1
         (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                   (fat32-filename-fix (car path))))
        0)
       (not
        (d-e-directory-p
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path))))))
       (< 0
          (len (explode (lofat-file->contents file))))
       (<=
        (+ 2 (count-of-clusters fat32$c))
        (d-e-first-cluster
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path))))))
       (lofat-regular-file-p file)
       (<= 1
           (count-free-clusters (effective-fat fat32$c)))
       (<=
        2
        (d-e-first-cluster
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path))))))
       (<=
        (len
         (make-clusters
          (nats=>string
           (insert-d-e
            (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (d-e-set-first-cluster-file-size
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
               (fat32-filename-fix (car path))))
             (nth 0
                  (find-n-free-clusters (effective-fat fat32$c)
                                        1))
             (len (explode (lofat-file->contents file))))))
          (cluster-size fat32$c)))
        (+ (count-free-clusters (effective-fat fat32$c))
           (len (mv-nth 0 (d-e-cc fat32$c root-d-e)))
           (- (len (make-clusters (lofat-file->contents file)
                                  (cluster-size fat32$c)))))))
      0)
     ((and
       (equal
        (+
         1
         (len
          (find-n-free-clusters
           (if
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
                      (find-d-e (make-d-e-list
                                 (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                                (fat32-filename-fix (car path))))))
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
                          (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                         (fat32-filename-fix (car path)))))))
                    0 nil))
                  1))
                (+ (count-of-clusters fat32$c) 2))
               (update-nth
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
                                 (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                                (fat32-filename-fix (car path))))))
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
                          (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                         (fat32-filename-fix (car path)))))))
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
                          (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                         (fat32-filename-fix (car path))))))
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
                            (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                           (fat32-filename-fix (car path)))))))
                      0 nil))
                    1))
                  fat32$c)
                 268435455)
                (effective-fat
                 (mv-nth
                  0
                  (clear-cc
                   fat32$c
                   (d-e-first-cluster
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                      (fat32-filename-fix (car path)))))
                   (d-e-file-size
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                      (fat32-filename-fix (car path)))))))))
             (effective-fat
              (mv-nth
               0
               (clear-cc
                fat32$c
                (d-e-first-cluster
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                   (fat32-filename-fix (car path)))))
                (d-e-file-size
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                   (fat32-filename-fix (car path)))))))))
           (+
            -1
            (len
             (make-clusters
              (lofat-file->contents file)
              (cluster-size
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
                        (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                       (fat32-filename-fix (car path))))))
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
                          (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                         (fat32-filename-fix (car path)))))))
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
                          (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                         (fat32-filename-fix (car path))))))
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
                            (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                           (fat32-filename-fix (car path)))))))
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
                      (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                     (fat32-filename-fix (car path)))))
                  (d-e-file-size
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list
                      (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                     (fat32-filename-fix (car path)))))))))))))))
        (len
         (make-clusters
          (lofat-file->contents file)
          (cluster-size
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                   (fat32-filename-fix (car path))))))
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
                      (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                     (fat32-filename-fix (car path)))))))
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
                      (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                     (fat32-filename-fix (car path))))))
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
                        (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                       (fat32-filename-fix (car path)))))))
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
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 (fat32-filename-fix (car path)))))
              (d-e-file-size
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 (fat32-filename-fix (car path))))))))))))
       (equal
        (mv-nth
         1
         (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                   (fat32-filename-fix (car path))))
        0)
       (not
        (d-e-directory-p
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path))))))
       (< 0
          (len (explode (lofat-file->contents file))))
       (<=
        2
        (d-e-first-cluster
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path))))))
       (<
        (d-e-first-cluster
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path)))))
        (+ 2 (count-of-clusters fat32$c)))
       (not
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
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                (fat32-filename-fix (car path))))))
            (make-list-ac
             (len
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                  (fat32-filename-fix (car path)))))))
             0 nil))
           1))
         (mv-nth
          0
          (d-e-cc
           fat32$c
           (mv-nth
            0
            (find-d-e
             (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
             (fat32-filename-fix (car path))))))))
       (lofat-regular-file-p file)
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
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
               (fat32-filename-fix (car path))))))
           (make-list-ac
            (len
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 (fat32-filename-fix (car path)))))))
            0 nil))
          1))
        (+ 2 (count-of-clusters fat32$c)))
       (<=
        (len
         (make-clusters
          (nats=>string
           (insert-d-e
            (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (d-e-set-first-cluster-file-size
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
               (fat32-filename-fix (car path))))
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
                              (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                             (fat32-filename-fix (car path))))))
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
                       (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                      (fat32-filename-fix (car path)))))))
                 0 nil))
               1))
             (len (explode (lofat-file->contents file))))))
          (cluster-size fat32$c)))
        (+
         (count-free-clusters (effective-fat fat32$c))
         (len (mv-nth 0 (d-e-cc fat32$c root-d-e)))
         (- (len (make-clusters (lofat-file->contents file)
                                (cluster-size fat32$c))))
         (len
          (mv-nth
           0
           (d-e-cc
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
              (fat32-filename-fix (car path))))))))))
      0)
     ((and
       (equal
        (+
         1
         (len
          (find-n-free-clusters
           (if
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
                      (find-d-e (make-d-e-list
                                 (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                                (fat32-filename-fix (car path))))))
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
                          (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                         (fat32-filename-fix (car path)))))))
                    0 nil))
                  1))
                (+ (count-of-clusters fat32$c) 2))
               (update-nth
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
                                 (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                                (fat32-filename-fix (car path))))))
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
                          (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                         (fat32-filename-fix (car path)))))))
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
                          (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                         (fat32-filename-fix (car path))))))
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
                            (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                           (fat32-filename-fix (car path)))))))
                      0 nil))
                    1))
                  fat32$c)
                 268435455)
                (effective-fat
                 (mv-nth
                  0
                  (clear-cc
                   fat32$c
                   (d-e-first-cluster
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                      (fat32-filename-fix (car path)))))
                   (d-e-file-size
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                      (fat32-filename-fix (car path)))))))))
             (effective-fat
              (mv-nth
               0
               (clear-cc
                fat32$c
                (d-e-first-cluster
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                   (fat32-filename-fix (car path)))))
                (d-e-file-size
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                   (fat32-filename-fix (car path)))))))))
           (+
            -1
            (len
             (make-clusters
              (lofat-file->contents file)
              (cluster-size
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
                        (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                       (fat32-filename-fix (car path))))))
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
                          (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                         (fat32-filename-fix (car path)))))))
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
                          (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                         (fat32-filename-fix (car path))))))
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
                            (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                           (fat32-filename-fix (car path)))))))
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
                      (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                     (fat32-filename-fix (car path)))))
                  (d-e-file-size
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list
                      (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                     (fat32-filename-fix (car path)))))))))))))))
        (len
         (make-clusters
          (lofat-file->contents file)
          (cluster-size
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                   (fat32-filename-fix (car path))))))
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
                      (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                     (fat32-filename-fix (car path)))))))
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
                      (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                     (fat32-filename-fix (car path))))))
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
                        (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                       (fat32-filename-fix (car path)))))))
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
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 (fat32-filename-fix (car path)))))
              (d-e-file-size
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 (fat32-filename-fix (car path))))))))))))
       (equal
        (mv-nth
         1
         (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                   (fat32-filename-fix (car path))))
        0)
       (not
        (d-e-directory-p
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path))))))
       (< 0
          (len (explode (lofat-file->contents file))))
       (<=
        2
        (d-e-first-cluster
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path))))))
       (<
        (d-e-first-cluster
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path)))))
        (+ 2 (count-of-clusters fat32$c)))
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
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
               (fat32-filename-fix (car path))))))
           (make-list-ac
            (len
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 (fat32-filename-fix (car path)))))))
            0 nil))
          1))
        (mv-nth
         0
         (d-e-cc
          fat32$c
          (mv-nth
           0
           (find-d-e
            (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (fat32-filename-fix (car path)))))))
       (lofat-regular-file-p file)
       (<=
        (len
         (make-clusters
          (nats=>string
           (insert-d-e
            (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (d-e-set-first-cluster-file-size
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
               (fat32-filename-fix (car path))))
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
                              (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                             (fat32-filename-fix (car path))))))
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
                       (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                      (fat32-filename-fix (car path)))))))
                 0 nil))
               1))
             (len (explode (lofat-file->contents file))))))
          (cluster-size fat32$c)))
        (+
         (count-free-clusters (effective-fat fat32$c))
         (len (mv-nth 0 (d-e-cc fat32$c root-d-e)))
         (- (len (make-clusters (lofat-file->contents file)
                                (cluster-size fat32$c))))
         (len
          (mv-nth
           0
           (d-e-cc
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
              (fat32-filename-fix (car path)))))))))
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
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
               (fat32-filename-fix (car path))))))
           (make-list-ac
            (len
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 (fat32-filename-fix (car path)))))))
            0 nil))
          1))
        (+ 2 (count-of-clusters fat32$c))))
      0)
     ((and
       (<=
        (len
         (make-clusters
          (nats=>string
           (insert-d-e
            (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (d-e-set-first-cluster-file-size
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
               (fat32-filename-fix (car path))))
             (nth 0
                  (find-n-free-clusters (effective-fat fat32$c)
                                        1))
             (len (explode (lofat-file->contents file))))))
          (cluster-size fat32$c)))
        (+ (count-free-clusters (effective-fat fat32$c))
           (len (mv-nth 0 (d-e-cc fat32$c root-d-e)))
           (- (len (make-clusters (lofat-file->contents file)
                                  (cluster-size fat32$c))))))
       (equal
        (+
         1
         (len
          (find-n-free-clusters
           (if
               (< (nth 0
                       (find-n-free-clusters (effective-fat fat32$c)
                                             1))
                  (+ (count-of-clusters fat32$c) 2))
               (update-nth
                (nth 0
                     (find-n-free-clusters (effective-fat fat32$c)
                                           1))
                (fat32-update-lower-28
                 (fati (nth 0
                            (find-n-free-clusters (effective-fat fat32$c)
                                                  1))
                       fat32$c)
                 268435455)
                (effective-fat fat32$c))
             (effective-fat fat32$c))
           (+ -1
              (len (make-clusters (lofat-file->contents file)
                                  (cluster-size fat32$c)))))))
        (len (make-clusters (lofat-file->contents file)
                            (cluster-size fat32$c))))
       (equal
        (mv-nth
         1
         (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                   (fat32-filename-fix (car path))))
        0)
       (not
        (d-e-directory-p
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path))))))
       (< 0
          (len (explode (lofat-file->contents file))))
       (<
        (d-e-first-cluster
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path)))))
        2)
       (lofat-regular-file-p file)
       (<= 1
           (count-free-clusters (effective-fat fat32$c))))
      0)
     ((lofat-regular-file-p file) 28)
     ((and
       (<=
        (len
         (make-clusters
          (nats=>string
           (insert-d-e
            (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (d-e-set-first-cluster-file-size
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
               (fat32-filename-fix (car path))))
             (nth 0
                  (find-n-free-clusters (effective-fat fat32$c)
                                        1))
             0)))
          (cluster-size fat32$c)))
        (+ -1
           (count-free-clusters (effective-fat fat32$c))
           (len (mv-nth 0 (d-e-cc fat32$c root-d-e)))))
       (equal
        (mv-nth
         1
         (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                   (fat32-filename-fix (car path))))
        0)
       (not
        (d-e-directory-p
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path))))))
       (not (lofat-directory-file-p file))
       (<=
        (+ 2 (count-of-clusters fat32$c))
        (d-e-first-cluster
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path))))))
       (<= 1
           (count-free-clusters (effective-fat fat32$c)))
       (<=
        2
        (d-e-first-cluster
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path)))))))
      0)
     ((and
       (equal
        (mv-nth
         1
         (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                   (fat32-filename-fix (car path))))
        0)
       (not
        (d-e-directory-p
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path))))))
       (not (lofat-directory-file-p file))
       (<=
        (+ 2 (count-of-clusters fat32$c))
        (d-e-first-cluster
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path))))))
       (<= 1
           (count-free-clusters (effective-fat fat32$c)))
       (<=
        2
        (d-e-first-cluster
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path))))))
       (<
        (+ -1
           (count-free-clusters (effective-fat fat32$c))
           (len (mv-nth 0 (d-e-cc fat32$c root-d-e))))
        (len
         (make-clusters
          (nats=>string
           (insert-d-e
            (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (d-e-set-first-cluster-file-size
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
               (fat32-filename-fix (car path))))
             (nth 0
                  (find-n-free-clusters (effective-fat fat32$c)
                                        1))
             0)))
          (cluster-size fat32$c)))))
      28)
     ((and
       (equal
        (mv-nth
         1
         (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                   (fat32-filename-fix (car path))))
        0)
       (not
        (d-e-directory-p
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path))))))
       (not (lofat-directory-file-p file))
       (<=
        2
        (d-e-first-cluster
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path))))))
       (<
        (d-e-first-cluster
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path)))))
        (+ 2 (count-of-clusters fat32$c)))
       (not
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
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                (fat32-filename-fix (car path))))))
            (make-list-ac
             (len
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                  (fat32-filename-fix (car path)))))))
             0 nil))
           1))
         (mv-nth
          0
          (d-e-cc
           fat32$c
           (mv-nth
            0
            (find-d-e
             (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
             (fat32-filename-fix (car path))))))))
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
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
               (fat32-filename-fix (car path))))))
           (make-list-ac
            (len
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 (fat32-filename-fix (car path)))))))
            0 nil))
          1))
        (+ 2 (count-of-clusters fat32$c)))
       (<=
        (len
         (make-clusters
          (nats=>string
           (insert-d-e
            (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (d-e-set-first-cluster-file-size
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
               (fat32-filename-fix (car path))))
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
                              (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                             (fat32-filename-fix (car path))))))
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
                       (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                      (fat32-filename-fix (car path)))))))
                 0 nil))
               1))
             0)))
          (cluster-size fat32$c)))
        (+
         -1
         (count-free-clusters (effective-fat fat32$c))
         (len (mv-nth 0 (d-e-cc fat32$c root-d-e)))
         (len
          (mv-nth
           0
           (d-e-cc
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
              (fat32-filename-fix (car path))))))))))
      0)
     ((and
       (equal
        (mv-nth
         1
         (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                   (fat32-filename-fix (car path))))
        0)
       (not
        (d-e-directory-p
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path))))))
       (not (lofat-directory-file-p file))
       (<
        (d-e-first-cluster
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path)))))
        2)
       (<= 1
           (count-free-clusters (effective-fat fat32$c)))
       (<
        (+ -1
           (count-free-clusters (effective-fat fat32$c))
           (len (mv-nth 0 (d-e-cc fat32$c root-d-e))))
        (len
         (make-clusters
          (nats=>string
           (insert-d-e
            (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (d-e-set-first-cluster-file-size
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
               (fat32-filename-fix (car path))))
             (nth 0
                  (find-n-free-clusters (effective-fat fat32$c)
                                        1))
             0)))
          (cluster-size fat32$c)))))
      28)
     ((and
       (equal
        (mv-nth
         1
         (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                   (fat32-filename-fix (car path))))
        0)
       (not
        (d-e-directory-p
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path))))))
       (not (lofat-directory-file-p file))
       (<
        (d-e-first-cluster
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path)))))
        2)
       (<= 1
           (count-free-clusters (effective-fat fat32$c)))
       (<=
        (len
         (make-clusters
          (nats=>string
           (insert-d-e
            (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (d-e-set-first-cluster-file-size
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
               (fat32-filename-fix (car path))))
             (nth 0
                  (find-n-free-clusters (effective-fat fat32$c)
                                        1))
             0)))
          (cluster-size fat32$c)))
        (+ -1
           (count-free-clusters (effective-fat fat32$c))
           (len (mv-nth 0 (d-e-cc fat32$c root-d-e))))))
      0)
     ((and
       (<=
        2
        (d-e-first-cluster
         (mv-nth
          0
          (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                    (fat32-filename-fix (car path))))))
       (<
        (d-e-first-cluster
         (mv-nth
          0
          (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                    (fat32-filename-fix (car path)))))
        (+ 2 (count-of-clusters fat32$c)))
       (<
        (+
         -1
         (count-free-clusters (effective-fat fat32$c))
         (len (mv-nth 0 (d-e-cc fat32$c root-d-e)))
         (len
          (mv-nth
           0
           (d-e-cc
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
              (fat32-filename-fix (car path))))))))
        (len
         (make-clusters
          (nats=>string
           (insert-d-e
            (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (d-e-set-first-cluster-file-size
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
               (fat32-filename-fix (car path))))
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
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                    (fat32-filename-fix (car path))))))
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
                       (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                      (fat32-filename-fix (car path)))))))
                 0 nil))
               1))
             0)))
          (cluster-size fat32$c)))))
      28)
     (t 0))))
  :hints (("goal" :in-theory (e/d
                              (lofat-place-file-helper len-of-make-clusters
                                                       subsetp-member)
                              ((:rewrite
                                d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                                . 5))))))

(encapsulate
  ()

  (local
   (defun
       lofat-place-file-alt
       (fat32$c root-d-e path file)
     (declare
      (xargs
       :guard (and (lofat-fs-p fat32$c)
                   (d-e-p root-d-e)
                   (>= (d-e-first-cluster root-d-e) *ms-first-data-cluster*)
                   (< (d-e-first-cluster root-d-e)
                      (+ *ms-first-data-cluster*
                         (count-of-clusters fat32$c)))
                   (fat32-filename-list-p path)
                   (lofat-file-p file)
                   (or (lofat-regular-file-p file)
                       (equal (lofat-file->contents file) nil)))
       :measure (acl2-count path)
       :stobjs fat32$c
       :verify-guards nil))
     (b* (((unless (consp path)) (mv fat32$c *enoent*))
          ;; Design choice - calls which ask for the entire root directory to be affected will fail.
          (name (mbe :logic (fat32-filename-fix (car path)) :exec (car path)))
          ((mv dir-contents &) (d-e-cc-contents fat32$c root-d-e))
          (d-e-list (make-d-e-list dir-contents))
          ((mv d-e error-code) (find-d-e d-e-list name))
          ;; If it's not there, it's a new file. In either case, though, we shouldn't give it the name
          ;; of the old file, that is, we shouldn't be inserting a directory entry with the name of
          ;; the old file. We may be moving a file and changing its name in the process.
          (d-e (if (equal error-code 0) d-e
                 (make-d-e-with-filename name)))
          (d-e (if (equal error-code 0) d-e
                 (d-e-install-directory-bit d-e (lofat-directory-file-p file))))
          ((when (and (not (equal error-code 0))
                      (consp (cdr path))))
           ;; This used to be the home of a bug!
           (mv fat32$c *enoent*))
          ;; ENOTDIR - can't act on anything that supposedly exists inside a regular file.
          ((when (and (consp (cdr path)) (not (d-e-directory-p d-e))))
           (mv fat32$c *enotdir*))
          (first-cluster (d-e-first-cluster d-e))
          ((when (and (not (equal error-code 0))
                      (consp (cdr path))))
           ;; This used to be the home of a bug!
           (mv fat32$c *enoent*))
          ((when (and (or (< first-cluster 2)
                          (<= (+ 2 (count-of-clusters fat32$c)) first-cluster))
                      (consp (cdr path))))
           (mv fat32$c *eio*))
          ;; Recursion
          ((when (consp(cdr path))) (lofat-place-file-alt fat32$c d-e (cdr path) file))
          ;; After these conditionals, the only remaining possibility is that (cdr path)
          ;; is an atom, which means we need to place a regular file or an empty directory, which
          ;; we have now ensured in the guard.
          (length (if (d-e-directory-p d-e) *ms-max-dir-size* (d-e-file-size d-e)))
          ;; Replacing a directory with a regular file is not permitted.
          ((when (and (d-e-directory-p d-e)
                      (lofat-regular-file-p file)))
           (mv fat32$c *enoent*))
          ;; This used to be the home of a bug! We used to return *enotdir* here.
          ((when (and (not (d-e-directory-p d-e))
                      (lofat-directory-file-p file)))
           (mv fat32$c *eexist*))
          ((mv fat32$c &)
           (if (or (< first-cluster 2) (<= (+ 2 (count-of-clusters fat32$c)) first-cluster))
               (mv fat32$c 0) (clear-cc fat32$c first-cluster length)))
          ;; We're going to have to refer to two different values of file-length:
          ;; one which refers to how much space we need to allocate, which will be
          ;; non-zero for directories (remember, we're not adding any root
          ;; directories lol so we need to have dot and dotdot entries) and
          ;; another which refers to the filesize field in the directory entry,
          ;; which will be zero for directories.
          (file-length (if (lofat-regular-file-p file)
                           (length (lofat-file->contents file))
                         ;; 32 bytes for dot, 32 bytes for dotdot.
                         (+ *ms-d-e-length* *ms-d-e-length*)))
          ;; Note, this value of new-dir-contents only gets used when file-length
          ;; is zero - an empty regular file.
          (new-dir-contents
           (nats=>string (insert-d-e (string=>nats dir-contents)
                                     (d-e-set-first-cluster-file-size d-e 0 0))))
          ((when (and (zp file-length) (<= (length new-dir-contents) *ms-max-dir-size*)))
           (update-dir-contents fat32$c (d-e-first-cluster root-d-e)
                                new-dir-contents))
          ((when (zp file-length)) (mv fat32$c *enospc*))
          (indices (stobj-find-n-free-clusters fat32$c 1))
          ((when (< (len indices) 1)) (mv fat32$c *enospc*))
          (first-cluster (nth 0 indices))
          ;; Mark this cluster as used, without possibly interfering with any
          ;; existing clusterchains.
          (fat32$c (update-fati first-cluster (fat32-update-lower-28
                                               (fati first-cluster fat32$c)
                                               *ms-end-of-cc*)
                                fat32$c))
          (contents (if (lofat-regular-file-p file) (lofat-file->contents file)
                      ;; Our guard ensures that the contents of this directory
                      ;; file are empty - so the only thing here is to add a dot
                      ;; entry and a dotdot entry.
                      (make-empty-subdir-contents first-cluster
                                                  (d-e-first-cluster root-d-e))))
          ;; OK, we've been done with the previous value of file-length for a
          ;; while. Now, we need a value that's going in the directory entry.
          (file-length (if (lofat-regular-file-p file) (length contents) 0))
          ((mv fat32$c d-e error-code &)
           (place-contents fat32$c d-e contents file-length first-cluster))
          ((unless (zp error-code)) (mv fat32$c error-code))
          (new-dir-contents (nats=>string (insert-d-e (string=>nats dir-contents) d-e)))
          ((unless (<= (length new-dir-contents) *ms-max-dir-size*)) (mv fat32$c *enospc*)))
       (update-dir-contents
        fat32$c
        (d-e-first-cluster root-d-e)
        new-dir-contents))))

  (local
   (defthm
     lofat-place-file-alt-correctness-1
     (implies
      (and
       (good-root-d-e-p root-d-e fat32$c)
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
       (or (lofat-regular-file-p file)
           (equal (lofat-file->contents file)
                  nil)))
      (and (equal (mv-nth 1
                          (lofat-place-file fat32$c root-d-e path file))
                  (mv-nth 1
                          (lofat-place-file-alt fat32$c root-d-e path file)))
           (equal (mv-nth 0
                          (lofat-place-file fat32$c root-d-e path file))
                  (if (zp (mv-nth 1
                                  (lofat-place-file fat32$c root-d-e path file)))
                      (mv-nth 0
                              (lofat-place-file-alt fat32$c root-d-e path file))
                      fat32$c))))
     :hints
     (("goal"
       :in-theory
       (e/d (place-contents-correctness-1 update-dir-contents-correctness-1
                                          subsetp-member)
            ((:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                       . 5)))))))

  ;; This theorem proves it to be a no-change loser!
  (defthm
    lofat-place-file-correctness-2
    (implies
     (and
      (good-root-d-e-p root-d-e fat32$c)
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
      (or (lofat-regular-file-p file)
          (equal (lofat-file->contents file) nil))
      (not (zp (mv-nth 1
                       (lofat-place-file fat32$c root-d-e path file)))))
     (equal (mv-nth 0
                    (lofat-place-file fat32$c root-d-e path file))
            fat32$c))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d (place-contents-correctness-1 update-dir-contents-correctness-1)
           ((:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                      . 5)))))))

(defthm natp-of-lofat-place-file
  (natp (mv-nth 1
                (lofat-place-file fat32$c
                                  root-d-e path file)))
  :rule-classes :type-prescription)

(defthm
  d-e-cc-contents-of-lofat-place-file-disjoint
  (implies
   (and
    (lofat-fs-p fat32$c)
    (d-e-p root-d-e)
    (d-e-directory-p root-d-e)
    (d-e-p d-e)
    (equal
     (mv-nth '1
             (d-e-cc-contents fat32$c root-d-e))
     '0)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c root-d-e)))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0
             (d-e-cc fat32$c d-e))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c root-d-e)))
       entry-limit)))
    (not (intersectp-equal
          (mv-nth 0
                  (d-e-cc fat32$c root-d-e))
          (mv-nth 0
                  (d-e-cc fat32$c d-e))))
    (not-intersectp-list
     (mv-nth 0
             (d-e-cc fat32$c root-d-e))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c root-d-e)))
       entry-limit)))
    (equal (mv-nth 1
                   (d-e-cc-contents fat32$c d-e))
           0))
   (equal (d-e-cc-contents
           (mv-nth 0
                   (lofat-place-file fat32$c
                                     root-d-e path file))
           d-e)
          (d-e-cc-contents fat32$c d-e)))
  :hints (("goal" :induct (lofat-place-file fat32$c
                                            root-d-e path file)
           :in-theory
           (e/d (intersect-with-subset subsetp-member)
                ((:rewrite
                  d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                  . 5))))))

(defthm
  lofat-place-file-correctness-1-lemma-8
  (implies
   (and
    (lofat-fs-p fat32$c)
    (d-e-p root-d-e)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c root-d-e)))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0
             (d-e-cc fat32$c root-d-e))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c root-d-e)))
       entry-limit)))
    (equal
     (mv-nth 1
             (d-e-cc-contents fat32$c root-d-e))
     0)
    (d-e-directory-p
     (mv-nth
      0
      (find-d-e
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c root-d-e)))
       (car path)))))
   (equal
    (d-e-cc-contents
     (mv-nth
      '0
      (lofat-place-file
       fat32$c
       (mv-nth
        '0
        (find-d-e
         (make-d-e-list
          (mv-nth
           '0
           (d-e-cc-contents fat32$c root-d-e)))
         (car path)))
       (cdr path)
       file))
     root-d-e)
    (d-e-cc-contents fat32$c root-d-e)))
  :hints
  (("goal"
    :in-theory
    (disable
     (:rewrite d-e-cc-contents-of-lofat-place-file-disjoint))
    :use
    ((:instance
      (:rewrite d-e-cc-contents-of-lofat-place-file-disjoint)
      (d-e root-d-e)
      (file file)
      (path (cdr path))
      (root-d-e
       (mv-nth
        0
        (find-d-e
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents fat32$c root-d-e)))
         (car path))))
      (fat32$c fat32$c))))))

(defthm
  d-e-cc-contents-of-lofat-place-file-coincident-1
  (b*
      (((mv cc-contents error-code)
        (d-e-cc-contents fat32$c d-e))
       (new-d-e
        (if
            (or (< 0
                   (len (explode (lofat-file->contents file))))
                (lofat-directory-file-p file))
            (if
                (<=
                 2
                 (d-e-first-cluster
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list
                     (mv-nth 0
                             (d-e-cc-contents fat32$c d-e)))
                    (car path)))))
                (if
                    (<
                     (d-e-first-cluster
                      (mv-nth
                       0
                       (find-d-e
                        (make-d-e-list
                         (mv-nth 0
                                 (d-e-cc-contents fat32$c d-e)))
                        (car path))))
                     (+ 2 (count-of-clusters fat32$c)))
                    (d-e-set-first-cluster-file-size
                     (mv-nth
                      0
                      (find-d-e
                       (make-d-e-list
                        (mv-nth 0
                                (d-e-cc-contents fat32$c d-e)))
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
                              (d-e-cc-contents fat32$c d-e)))
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
                                (d-e-cc-contents fat32$c d-e)))
                              (car path))))))
                         0 nil))
                       1))
                     (if (lofat-directory-file-p file)
                         0
                       (len (explode (lofat-file->contents file)))))
                  (d-e-set-first-cluster-file-size
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list
                      (mv-nth 0
                              (d-e-cc-contents fat32$c d-e)))
                     (car path)))
                   (nth 0
                        (find-n-free-clusters (effective-fat fat32$c)
                                              1))
                   (if (lofat-directory-file-p file)
                       0
                     (len (explode (lofat-file->contents file))))))
              (if
                  (equal
                   (mv-nth
                    1
                    (find-d-e
                     (make-d-e-list
                      (mv-nth 0
                              (d-e-cc-contents fat32$c d-e)))
                     (car path)))
                   0)
                  (d-e-set-first-cluster-file-size
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list
                      (mv-nth 0
                              (d-e-cc-contents fat32$c d-e)))
                     (car path)))
                   (nth 0
                        (find-n-free-clusters (effective-fat fat32$c)
                                              1))
                   (if (lofat-directory-file-p file)
                       0
                     (len (explode (lofat-file->contents file)))))
                (d-e-set-first-cluster-file-size
                 (d-e-install-directory-bit
                  (make-d-e-with-filename (car path))
                  (lofat-directory-file-p file))
                 (nth 0
                      (find-n-free-clusters (effective-fat fat32$c)
                                            1))
                 (if (lofat-directory-file-p file)
                     0
                   (len (explode (lofat-file->contents file)))))))
          (if
              (equal
               (mv-nth
                1
                (find-d-e
                 (make-d-e-list
                  (mv-nth 0
                          (d-e-cc-contents fat32$c d-e)))
                 (car path)))
               0)
              (d-e-set-first-cluster-file-size
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list
                  (mv-nth 0
                          (d-e-cc-contents fat32$c d-e)))
                 (car path)))
               0 0)
            (d-e-set-first-cluster-file-size
             (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                        (lofat-directory-file-p file))
             0 0))))
       (new-contents
        (nats=>chars (insert-d-e (string=>nats cc-contents)
                                 new-d-e))))
    (implies
     (and
      (lofat-fs-p fat32$c)
      (d-e-p d-e)
      (d-e-directory-p d-e)
      (fat32-filename-list-p path)
      (equal error-code 0)
      (equal
       (mv-nth 3
               (lofat-to-hifat-helper fat32$c
                                      (make-d-e-list cc-contents)
                                      entry-limit))
       0)
      (not-intersectp-list
       (mv-nth 0
               (d-e-cc fat32$c d-e))
       (mv-nth 2
               (lofat-to-hifat-helper fat32$c
                                      (make-d-e-list cc-contents)
                                      entry-limit)))
      (equal (mv-nth 1
                     (lofat-place-file fat32$c d-e path file))
             0)
      (lofat-file-p file))
     (equal
      (d-e-cc-contents
       (mv-nth 0
               (lofat-place-file fat32$c d-e path file))
       d-e)
      (if
          (atom (cdr path))
          (mv
           (implode
            (append
             new-contents
             (make-list-ac
              (- (* (cluster-size fat32$c)
                    (len (make-clusters (implode new-contents)
                                        (cluster-size fat32$c))))
                 (len new-contents))
              (code-char 0)
              nil)))
           0)
        (d-e-cc-contents fat32$c d-e)))))
  :hints
  (("goal"
    :expand (lofat-place-file fat32$c d-e path file)
    :do-not-induct t
    :in-theory
    (e/d (update-dir-contents-correctness-1 nats=>string subsetp-member)
         (explode-of-d-e-filename clear-cc-correctness-1
                                  effective-fat-of-clear-cc)))))

(defthm
  d-e-cc-of-lofat-place-file-disjoint
  (implies
   (and
    (lofat-fs-p fat32$c)
    (d-e-p root-d-e)
    (d-e-directory-p root-d-e)
    (d-e-p d-e)
    (equal
     (mv-nth '1
             (d-e-cc fat32$c root-d-e))
     '0)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c root-d-e)))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0
             (d-e-cc fat32$c d-e))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c root-d-e)))
       entry-limit)))
    (not (intersectp-equal
          (mv-nth 0
                  (d-e-cc fat32$c root-d-e))
          (mv-nth 0
                  (d-e-cc fat32$c d-e))))
    (not-intersectp-list
     (mv-nth 0
             (d-e-cc fat32$c root-d-e))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c root-d-e)))
       entry-limit)))
    (equal (mv-nth 1
                   (d-e-cc fat32$c d-e))
           0)
    (<= 2 (d-e-first-cluster d-e))
    (<= 2 (d-e-first-cluster root-d-e)))
   (equal (d-e-cc
           (mv-nth 0
                   (lofat-place-file fat32$c
                                     root-d-e path file))
           d-e)
          (d-e-cc fat32$c d-e)))
  :hints (("goal" :induct (lofat-place-file fat32$c
                                            root-d-e path file)
           :in-theory
           (e/d
           (intersect-with-subset subsetp-member)
           ((:rewrite
             d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
             . 5))))))

(defthm
  lofat-to-hifat-helper-of-lofat-place-file-disjoint
  (implies
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c root-d-e)))
       entry-limit1))
     0)
    (not
     (member-intersectp-equal
      (mv-nth 2
              (lofat-to-hifat-helper fat32$c
                                     d-e-list entry-limit2))
      (mv-nth
       2
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list
         (mv-nth
          0
          (d-e-cc-contents fat32$c root-d-e)))
        entry-limit1))))
    (zp (mv-nth 3
                (lofat-to-hifat-helper fat32$c
                                       d-e-list entry-limit2)))
    (useful-d-e-list-p d-e-list)
    (not-intersectp-list
     (mv-nth 0
             (d-e-cc fat32$c root-d-e))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c root-d-e)))
       entry-limit1)))
    (not-intersectp-list
     (mv-nth 0
             (d-e-cc fat32$c root-d-e))
     (mv-nth 2
             (lofat-to-hifat-helper fat32$c
                                    d-e-list entry-limit2)))
    (lofat-fs-p fat32$c)
    (d-e-p root-d-e)
    (d-e-directory-p root-d-e)
    (mv-let (ignore-0 error-code)
      (d-e-cc-contents fat32$c root-d-e)
      (declare (ignore ignore-0))
      (mv-let (cc ignore-0)
        (d-e-cc fat32$c root-d-e)
        (declare (ignore ignore-0))
        (and (equal error-code 0)
             (no-duplicatesp-equal cc)))))
   (equal
    (lofat-to-hifat-helper
     (mv-nth 0
             (lofat-place-file fat32$c root-d-e path file))
     d-e-list entry-limit2)
    (lofat-to-hifat-helper fat32$c
                           d-e-list entry-limit2)))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lofat-to-hifat-helper not-intersectp-list)
     (member-intersectp-is-commutative
      (:rewrite nth-of-nats=>chars)
      (:rewrite nth-of-effective-fat)
      (:linear nth-when-d-e-p)
      (:definition find-d-e)
      (:rewrite explode-of-d-e-filename)
      (:rewrite length-when-stringp)
      (:rewrite len-of-nats=>chars)
      (:rewrite len-of-insert-d-e)
      (:rewrite d-e-fix-when-d-e-p)
      (:rewrite subsetp-append1)
      (:rewrite lofat-place-file-correctness-lemma-83)
      (:rewrite lofat-place-file-correctness-lemma-52)))
    :induct (lofat-to-hifat-helper fat32$c
                                   d-e-list entry-limit2)
    :do-not-induct t)))

;; We've actually gotten pretty close to precisely specifying when there
;; can be a space error and when there can't.
;; - We started off thinking that every directory tree with
;; (hifat-cluster-count ...) evaluating to a number less than the number of
;; available clusters would work, but we realised that would be false given the
;; recursive nature and the fact that other directory trees would, in general,
;; exist.
;;  - We then thought incrementally: the difference between clusters needed by
;; the new tree and the clusters needed by the old tree would be the number of
;; free clusters needed. This is surprisingly close to being true! However,
;; there are issues. Even in the case where we're inserting just one regular
;; file, we're going to have to update its parent directory, potentially
;; increasing its length. That gives us a correctness issue, in that we might
;; be making the directory contents longer than *ms-max-dir-size*. So... we
;; decide that inserting a new directory entry is a good time to pluck out the
;; parent and current directory entries, and discard all other useless entries
;; (i.e. entries for deleted files.) That resolves the correctness issue,
;; because it means that any directory tree which continues to satisfy
;; hifat-bounded-file-alist-p will be fine. However, that also immediately
;; raises the spectre of special treatment for the root directory, which does
;; not have parent and current directory entries. Moreover, since we're
;; changing the number of clusters in the root directory, we'll need to account
;; for those in addition to the hifat-cluster-count of the new tree... and so
;; the number of new clusters needed becomes the difference between the new
;; tree and the old tree in terms of the sum of clusters needed for the root
;; directory and clusters needed for the tree (awkward, I know, but unavoidable
;; given the definition of hifat-cluster-count.) This gives rise to a weird
;; situation where we might need, say, two free clusters for placing the
;; regular file, and we will have exactly two clusters freed up by removing
;; deleted directory entries from the root directories. We should be able to do
;; it, but we can't without entering a domain of utter madness where we
;; free all possible clusters first and then use them as needed, and the
;; atomicity of the various operations recedes far into the distance.
;; - We conclude thinking it's probably best for the *ENOSPC* error condition
;; not to be formally specified at all. We would be hamstringing ourselves
;; pretty severely if we tried to break atomicity and then (likely) had to
;; reimplement a bunch of things. We can still do some obvious things
;; though... we shouldn't be hanging on to useless directory entries when we're
;; adding new ones, and we shouldn't subject ourselves to clusters full of
;; zeroes, both of which point to sticking with the new implementation of
;; insert-d-e.

;; This works because as soon as both arguments are quoted constants, the
;; executable-counterpart will kick in. The availability of the
;; executable-counterpart will, however, have to be ensured
;; by a theory invariant. This is, BTW, not replaceable by a congruence rule -
;; the term to be rewritten is sometimes a variable, so a true-equiv rule could
;; not possibly be defined unless it was a very unselective forward-chaining
;; rule.
(defthm
  lofat-place-file-correctness-lemma-2
  (implies
   (syntaxp (quotep const))
   (and
    (hifat-equiv
     (mv-nth 0
             (hifat-place-file fs path
                               (m1-file-hifat-file-alist-fix d-e const)))
     (mv-nth 0
             (hifat-place-file fs path
                               (m1-file-hifat-file-alist-fix nil const))))
    (equal
     (mv-nth 1
             (hifat-place-file fs path
                               (m1-file-hifat-file-alist-fix d-e const)))
     (mv-nth 1
             (hifat-place-file fs path
                               (m1-file-hifat-file-alist-fix nil const))))))
  :hints
  (("goal" :use (:instance hifat-place-file-when-hifat-equiv-1
                           (file1 (m1-file-hifat-file-alist-fix d-e const))
                           (file2 (m1-file-hifat-file-alist-fix nil const))))))

(theory-invariant
 (implies
  (active-runep
   '(:rewrite lofat-place-file-correctness-lemma-2))
  (active-runep
   '(:executable-counterpart m1-file-hifat-file-alist-fix))))

(defthm
  lofat-place-file-correctness-lemma-32
  (implies
   (and
    (useful-d-e-list-p d-e-list)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
           0)
    (lofat-fs-p fat32$c)
    (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))
    (d-e-p d-e)
    (equal (mv-nth 1
                   (d-e-cc fat32$c
                           (mv-nth 0 (find-d-e d-e-list name))))
           0)
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c d-e))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c
                                 (mv-nth 0 (find-d-e d-e-list name)))))
       entry-limit)))
    (not
     (intersectp-equal (mv-nth 0
                               (d-e-cc fat32$c
                                       (mv-nth 0 (find-d-e d-e-list name))))
                       (mv-nth 0 (d-e-cc fat32$c d-e))))
    (not-intersectp-list
     (mv-nth 0
             (d-e-cc fat32$c
                     (mv-nth 0 (find-d-e d-e-list name))))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c
                                 (mv-nth 0 (find-d-e d-e-list name)))))
       entry-limit)))
    (equal (mv-nth 1 (d-e-cc fat32$c d-e))
           0)
    (<= 2 (d-e-first-cluster d-e))
    (<= 2
        (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name)))))
   (equal
    (d-e-cc (mv-nth 0
                    (lofat-place-file fat32$c
                                      (mv-nth 0 (find-d-e d-e-list name))
                                      path file))
            d-e)
    (d-e-cc fat32$c d-e)))
  :hints
  (("goal" :do-not-induct t
    :in-theory (disable lofat-find-file-correctness-1-lemma-6
                        d-e-cc-of-lofat-place-file-disjoint)
    :use ((:instance d-e-cc-of-lofat-place-file-disjoint
                     (root-d-e (mv-nth 0 (find-d-e d-e-list name))))
          lofat-find-file-correctness-1-lemma-6))))

(encapsulate
  ()

  (local
   (in-theory (e/d (lofat-place-file)
                   ((:rewrite intersectp-when-subsetp)
                    (:linear nth-when-d-e-p)
                    (:rewrite
                     d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-3)
                    (:definition find-d-e)
                    (:rewrite append-atom-under-list-equiv)
                    (:rewrite consp-of-make-list-ac)
                    (:linear make-clusters-correctness-2)
                    (:rewrite hifat-to-lofat-inversion-lemma-17)
                    (:rewrite
                     d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-11)
                    (:definition place-d-e)
                    (:rewrite
                     lofat-place-file-correctness-lemma-5)
                    (:definition binary-append)
                    (:definition unsigned-byte-p)
                    (:rewrite
                     lofat-to-hifat-helper-of-place-contents)
                    (:rewrite
                     lofat-to-hifat-helper-of-update-fati)
                    (:rewrite
                     d-e-first-cluster-of-d-e-set-first-cluster-file-size)
                    (:rewrite
                     fat32-masked-entry-fix-when-fat32-masked-entry-p)
                    (:rewrite
                     lofat-to-hifat-helper-of-clear-cc)
                    (:rewrite
                     lofat-to-hifat-helper-of-update-dir-contents)
                    (:definition member-intersectp-equal)))))

  (defthm
    lofat-place-file-correctness-lemma-66
    (implies
     (and
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
               (mv-nth
                0
                (d-e-cc-contents fat32$c root-d-e)))
              (fat32-filename-fix (car path))))))
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
                  (d-e-cc-contents fat32$c root-d-e)))
                (fat32-filename-fix (car path)))))))
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
            (mv-nth
             0
             (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path)))))))
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c root-d-e)))
         entry-limit))
       0)
      (d-e-directory-p
       (mv-nth
        0
        (find-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c root-d-e)))
         (fat32-filename-fix (car path)))))
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c root-d-e)))
         entry-limit))))
     (not
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
               (mv-nth
                0
                (d-e-cc-contents fat32$c root-d-e)))
              (fat32-filename-fix (car path))))))
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
                  (d-e-cc-contents fat32$c root-d-e)))
                (fat32-filename-fix (car path)))))))
           0 nil))
         1))
       x)))
    :hints
    (("goal"
      :in-theory (disable nth-of-effective-fat
                          (:rewrite nth-of-set-indices-in-fa-table-when-member))
      :use
      ((:instance
        (:rewrite nth-of-set-indices-in-fa-table-when-member)
        (val 0)
        (index-list
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
               (d-e-cc-contents fat32$c root-d-e)))
             (fat32-filename-fix (car path)))))))
        (fa-table (effective-fat fat32$c))
        (n
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
                  (d-e-cc-contents fat32$c root-d-e)))
                (fat32-filename-fix (car path))))))
            (make-list-ac
             (len
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e (make-d-e-list
                            (mv-nth 0
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
                           (fat32-filename-fix (car path)))))))
             0 nil))
           1))))
       (:instance
        nth-of-effective-fat
        (n
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
                  (d-e-cc-contents fat32$c root-d-e)))
                (fat32-filename-fix (car path))))))
            (make-list-ac
             (len
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e (make-d-e-list
                            (mv-nth 0
                                    (d-e-cc-contents
                                     fat32$c root-d-e)))
                           (fat32-filename-fix (car path)))))))
             0 nil))
           1))))))))

  (defthm
    lofat-place-file-correctness-lemma-65
    (implies
     (and
      (d-e-directory-p root-d-e)
      (equal (mv-nth 1
                     (lofat-place-file fat32$c root-d-e path file))
             0)
      (non-free-index-listp x (effective-fat fat32$c))
      (not (intersectp-equal
            x
            (mv-nth 0
                    (d-e-cc fat32$c root-d-e))))
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c root-d-e)))
         entry-limit))
       0)
      (lofat-fs-p fat32$c)
      (d-e-p root-d-e)
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c root-d-e)))
         entry-limit)))
      (not-intersectp-list
       (mv-nth 0
               (d-e-cc fat32$c root-d-e))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c root-d-e)))
         entry-limit)))
      (equal
       (mv-nth '1
               (d-e-cc-contents fat32$c root-d-e))
       '0))
     (not
      (intersectp-equal
       x
       (mv-nth
        0
        (d-e-cc
         (mv-nth 0
                 (lofat-place-file fat32$c root-d-e path file))
         root-d-e)))))
    :hints (("goal" :do-not-induct t
             :expand (lofat-place-file fat32$c
                                       root-d-e path file)
             :in-theory
             (e/d (intersectp-when-subsetp subsetp-member)
                  ((:rewrite
                    d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                    . 5)))))))

(defthm
  lofat-place-file-correctness-lemma-7
  (implies
   (and
    (member-equal
     i
     (mv-nth
      0
      (d-e-cc fat32$c
              (mv-nth 0 (find-d-e d-e-list2 name)))))
    (<= 2
        (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list2 name))))
    (< (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list2 name)))
       (+ 2 (count-of-clusters fat32$c)))
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c
                                          d-e-list2 entry-limit2))
           0)
    (useful-d-e-list-p d-e-list2)
    (not (member-intersectp-equal
          (mv-nth 2
                  (lofat-to-hifat-helper fat32$c
                                         d-e-list1 entry-limit1))
          (mv-nth 2
                  (lofat-to-hifat-helper fat32$c
                                         d-e-list2 entry-limit2)))))
   (not-intersectp-list
    (list i)
    (mv-nth 2
            (lofat-to-hifat-helper fat32$c
                                   d-e-list1 entry-limit1))))
  :hints
  (("goal"
    :in-theory
    (e/d ()
         ((:definition member-intersectp-equal)
          (:rewrite lofat-to-hifat-helper-of-clear-cc)
          (:rewrite lofat-place-file-correctness-lemma-56)
          (:rewrite nth-of-effective-fat)))
    :restrict
    ((not-intersectp-list-when-subsetp-1
      ((y
        (mv-nth
         0
         (d-e-cc fat32$c
                 (mv-nth 0
                         (find-d-e d-e-list2 name)))))))
     (intersectp-member-when-not-member-intersectp
      ((lst2
        (mv-nth 2
                (lofat-to-hifat-helper fat32$c
                                       d-e-list2 entry-limit2)))))))))

;; Not trivial to get rid of...
(defthm
  lofat-place-file-correctness-lemma-97
  (implies
   (and
    (d-e-directory-p d-e)
    (good-root-d-e-p root-d-e fat32$c)
    (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
           0)
    (equal
     (mv-nth 3
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              entry-limit1))
     0)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c d-e-list entry-limit2))
           0)
    (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c d-e)))
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c d-e))
     (mv-nth 2
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              entry-limit1)))
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c d-e))
     (mv-nth 2
             (lofat-to-hifat-helper fat32$c d-e-list entry-limit2)))
    (not
     (member-intersectp-equal
      (mv-nth 2
              (lofat-to-hifat-helper
               fat32$c
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
               entry-limit1))
      (mv-nth 2
              (lofat-to-hifat-helper fat32$c d-e-list entry-limit2))))
    (d-e-p d-e)
    (not (consp (cdr path))))
   (not-intersectp-list
    (mv-nth 0
            (d-e-cc (mv-nth 0
                            (lofat-place-file fat32$c d-e path file))
                    d-e))
    (mv-nth 2
            (lofat-to-hifat-helper fat32$c d-e-list entry-limit2))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (e/d
     nil
     ((:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                . 5)
      (:rewrite lofat-to-hifat-helper-of-place-contents)
      (:definition member-intersectp-equal)
      (:rewrite get-cc-contents-of-lofat-remove-file-coincident-lemma-5
                . 1)
      (:rewrite lofat-to-hifat-helper-of-update-fati)
      (:rewrite lofat-to-hifat-helper-of-update-dir-contents)
      (:linear find-n-free-clusters-correctness-1)
      (:rewrite not-intersectp-list-of-cons-2)
      (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-4)
      (:rewrite lofat-place-file-correctness-lemma-5)
      (:definition find-d-e)
      (:definition make-list-ac)
      (:definition place-d-e)
      (:linear nth-when-d-e-p)
      (:type-prescription d-e-filename)
      (:rewrite d-e-cc-contents-of-lofat-place-file-coincident-lemma-15)
      (:rewrite hifat-to-lofat-inversion-lemma-17))))))

;; Not trivial to get rid of...
(defthm
  lofat-place-file-correctness-lemma-92
  (implies
   (and
    (d-e-directory-p d-e)
    (good-root-d-e-p root-d-e fat32$c)
    (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
           0)
    (equal
     (mv-nth 3
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              entry-limit))
     0)
    (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c d-e)))
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c d-e))
     (mv-nth 2
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              entry-limit)))
    (not (consp (cdr path)))
    (d-e-p d-e))
   (no-duplicatesp-equal
    (mv-nth 0
            (d-e-cc (mv-nth 0
                            (lofat-place-file fat32$c d-e path file))
                    d-e))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (e/d
     (not-intersectp-list hifat-entry-count subsetp-member)
     ((:definition subseq)
      (:definition subseq-list)
      (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
      (:rewrite nfix-when-zp)
      (:definition delete-d-e)
      (:rewrite nth-of-nats=>chars)
      (:rewrite take-of-len-free)
      (:definition place-d-e)
      (:rewrite nats=>chars-of-take)
      (:rewrite d-e-cc-under-iff . 2)
      (:rewrite intersectp-when-subsetp)
      (:rewrite disjoint-list-listp-of-lofat-to-hifat-helper)
      (:rewrite not-intersectp-list-of-set-difference$)
      (:rewrite not-intersectp-list-when-atom)
      (:rewrite lofat-find-file-correctness-1-lemma-6)
      (:rewrite m1-file-p-of-cdar-when-m1-file-alist-p)
      (:rewrite fat32-filename-p-correctness-1)
      (:definition assoc-equal)
      (:rewrite fat32-filename-p-of-caar-when-m1-file-alist-p)
      (:rewrite car-of-append)
      (:rewrite d-e-cc-contents-of-lofat-place-file-disjoint)
      (:rewrite hifat-no-dups-p-of-cdr)
      (:type-prescription binary-append)
      (:type-prescription intersectp-equal)
      (:rewrite d-e-cc-of-lofat-place-file-disjoint)
      (:rewrite consp-of-append)
      (:rewrite not-intersectp-list-of-set-difference$-lemma-3)
      (:rewrite member-intersectp-with-subset)
      (:rewrite append-atom-under-list-equiv)
      (:rewrite lofat-place-file-correctness-lemma-5)
      (:rewrite rationalp-implies-acl2-numberp)
      (:rewrite consp-of-remove-assoc-1)
      (:rewrite member-intersectp-of-set-difference$-1
                . 1)
      (:rewrite hifat-to-lofat-inversion-lemma-23)
      (:rewrite nthcdr-when->=-n-len-l)
      (:rewrite d-e-p-of-take)
      (:linear len-of-explode-when-m1-file-contents-p-1)
      (:definition nthcdr)
      (:rewrite then-subseq-empty-1)
      (:linear length-of-d-e-cc-contents . 3)
      (:rewrite unsigned-byte-listp-when-d-e-p)
      (:rewrite d-e-p-of-chars=>nats)
      (:rewrite chars=>nats-of-take)
      (:type-prescription hifat-bounded-file-alist-p)
      (:rewrite take-when-atom)
      (:definition char)
      (:rewrite explode-of-d-e-filename)
      (:linear len-when-hifat-bounded-file-alist-p . 2)
      (:linear len-when-hifat-bounded-file-alist-p . 1)
      (:linear length-of-d-e-cc-contents . 2)
      (:rewrite str::consp-of-explode)
      (:rewrite hifat-to-lofat-inversion-lemma-2)
      (:rewrite m1-regular-file-p-correctness-1)
      (:type-prescription m1-file-fix$inline)
      (:rewrite lofat-to-hifat-helper-of-update-dir-contents)
      (:type-prescription fat32-filename-fix)
      (:rewrite m1-file-p-of-m1-file-fix)
      (:rewrite natp-of-place-contents)
      (:rewrite str::explode-when-not-stringp)
      (:rewrite set-difference$-when-not-intersectp)
      (:rewrite delete-d-e-correctness-1)
      (:definition remove-assoc-equal)
      (:rewrite abs-find-file-correctness-1-lemma-40)
      (:rewrite hifat-place-file-correctness-3)
      (:rewrite remove-assoc-when-absent-1)
      (:definition find-d-e)
      (:definition lofat-to-hifat-helper)
      (:definition not-intersectp-list)
      (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                . 5)
      (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-2)
      (:definition hifat-entry-count)
      (:definition member-intersectp-equal)
      (:rewrite lofat-to-hifat-helper-of-clear-cc)
      (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-3)
      (:rewrite not-intersectp-list-of-cons-2)
      (:rewrite get-cc-contents-of-lofat-remove-file-coincident-lemma-5
                . 1)
      (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-4)
      (:definition make-list-ac)
      (:linear nth-when-d-e-p)
      (:rewrite d-e-cc-of-place-contents-coincident-1)
      (:rewrite set-indices-in-fa-table-when-atom)
      (:rewrite not-intersectp-list-of-set-difference$-lemma-2
                . 2)
      (:rewrite not-intersectp-list-of-set-difference$-lemma-2
                . 2)
      (:rewrite hifat-to-lofat-inversion-lemma-17))))))

;; Minimising these hypotheses was so painful...
(encapsulate
  ()

  (local
   (defthmd lemma
     (implies
      (and
       (d-e-p d-e)
       (d-e-directory-p d-e)
       (equal (mv-nth 1
                      (lofat-place-file fat32$c d-e path file))
              0)
       (good-root-d-e-p root-d-e fat32$c)
       (fat32-filename-list-p path)
       (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
              0)
       (equal
        (mv-nth 3
                (lofat-to-hifat-helper
                 fat32$c
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (+ -1 entry-limit)))
        0)
       (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c d-e)))
       (not-intersectp-list
        (mv-nth 0 (d-e-cc fat32$c d-e))
        (mv-nth 2
                (lofat-to-hifat-helper
                 fat32$c
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (+ -1 entry-limit))))
       (not (consp (cdr path)))
       (lofat-directory-file-p file)
       (<=
        2
        (d-e-first-cluster
         (mv-nth
          0
          (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path))))))
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
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path))))))
               0 nil))
             1))
           0))
         (+ -1 entry-limit)))))
     :hints
     (("goal"
       :do-not-induct t
       :in-theory
       (e/d
        (subsetp-member)
        (d-e-cc-of-update-dir-contents-coincident
         (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                   . 5)
         (:rewrite lofat-to-hifat-helper-of-update-dir-contents)
         (:rewrite nfix-when-zp)
         (:definition member-intersectp-equal)
         (:rewrite lofat-to-hifat-helper-of-clear-cc)
         (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident-lemma-8)
         (:rewrite hifat-to-lofat-inversion-lemma-17)
         (:rewrite d-e-cc-contents-of-update-dir-contents-coincident)
         (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-4)
         (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-3)
         (:rewrite
          lofat-to-hifat-helper-of-hifat-to-lofat-helper-disjoint-lemma-2)
         (:definition len)
         (:type-prescription d-e-file-size)
         (:linear d-e-file-size-correctness-1)
         (:definition find-d-e)
         (:rewrite lofat-place-file-correctness-lemma-5)
         (:definition non-free-index-listp)
         (:rewrite get-cc-contents-of-lofat-remove-file-coincident-lemma-5
                   . 1)
         (:rewrite not-intersectp-list-of-find-n-free-clusters)
         (:linear nth-when-d-e-p)
         (:definition make-list-ac)
         (:definition place-d-e)
         (:rewrite member-of-nth-when-not-intersectp)
         (:rewrite non-free-index-list-listp-of-effective-fat-of-place-contents)
         (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-11)
         (:rewrite not-intersectp-list-of-set-difference$-lemma-2
                   . 2)
         (:rewrite intersectp-when-subsetp)
         (:rewrite not-intersectp-list-of-cons-2)
         (:rewrite subsetp-cons-2)))))))

  (defthm
    lofat-place-file-correctness-lemma-174
    (implies
     (and
      (integerp entry-limit)
      (d-e-p d-e)
      (d-e-directory-p d-e)
      (equal (mv-nth 1
                     (lofat-place-file fat32$c d-e path file))
             0)
      (good-root-d-e-p root-d-e fat32$c)
      (fat32-filename-list-p path)
      (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
             0)
      (equal
       (mv-nth 3
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                entry-limit))
       0)
      (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c d-e)))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c d-e))
       (mv-nth 2
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                entry-limit)))
      (not (consp (cdr path)))
      (lofat-directory-file-p file)
      (<=
       2
       (d-e-first-cluster
        (mv-nth
         0
         (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))))
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
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))))
              0 nil))
            1))
          0))
        entry-limit))))
    :hints
    (("goal"
      :do-not-induct t
      :use
      (:instance lemma (entry-limit (+ entry-limit 1)))
      :in-theory
      (e/d
       nil
       (lofat-place-file
        d-e-cc-of-update-dir-contents-coincident
        (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                  . 5)
        (:rewrite lofat-to-hifat-helper-of-update-dir-contents)
        (:rewrite nfix-when-zp)
        (:definition member-intersectp-equal)
        (:rewrite lofat-to-hifat-helper-of-clear-cc)
        (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident-lemma-8)
        (:rewrite hifat-to-lofat-inversion-lemma-17)
        (:rewrite d-e-cc-contents-of-update-dir-contents-coincident)
        (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-4)
        (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-3)
        (:rewrite
         lofat-to-hifat-helper-of-hifat-to-lofat-helper-disjoint-lemma-2)
        (:definition len)
        (:type-prescription d-e-file-size)
        (:linear d-e-file-size-correctness-1)
        (:definition find-d-e)
        (:rewrite lofat-place-file-correctness-lemma-5)
        (:definition non-free-index-listp)
        (:rewrite get-cc-contents-of-lofat-remove-file-coincident-lemma-5
                  . 1)
        (:rewrite not-intersectp-list-of-find-n-free-clusters)
        (:linear nth-when-d-e-p)
        (:definition make-list-ac)
        (:definition place-d-e)
        (:rewrite member-of-nth-when-not-intersectp)
        (:rewrite non-free-index-list-listp-of-effective-fat-of-place-contents)
        (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-11)
        (:rewrite not-intersectp-list-of-set-difference$-lemma-2
                  . 2)
        (:rewrite intersectp-when-subsetp)
        (:rewrite not-intersectp-list-of-cons-2)
        (:rewrite subsetp-cons-2)))))))

;; Decently useful.
(defthm
  lofat-place-file-correctness-lemma-51
  (implies
   (and (lofat-fs-p fat32$c)
        (d-e-p d-e)
        (d-e-directory-p d-e)
        (<= *ms-first-data-cluster*
            (d-e-first-cluster d-e))
        (< (d-e-first-cluster d-e)
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32$c)))
        (equal (mv-nth 1
                       (update-dir-contents fat32$c
                                            (d-e-first-cluster d-e)
                                            dir-contents))
               0)
        (stringp dir-contents)
        (< 0 (len (explode dir-contents)))
        (<= (len (explode dir-contents))
            *ms-max-dir-size*)
        (non-free-index-list-listp x (effective-fat fat32$c))
        (not-intersectp-list
         (mv-nth '0
                 (d-e-cc fat32$c d-e))
         x))
   (not-intersectp-list
    (mv-nth 0
            (d-e-cc
             (mv-nth 0
                     (update-dir-contents fat32$c
                                          (d-e-first-cluster d-e)
                                          dir-contents))
             d-e))
    x))
  :hints (("goal" :in-theory (enable not-intersectp-list intersect-with-subset))))

;; This is seriously aggravating to remove. It's used in two lemmas and in
;; neither case did I get rid of it by changing the computed-hint
;; theories. Nor was it fruitful to try hints on named subgoals - I think it's
;; one of those things where the simplification just happens to go off in a
;; different direction when deep inside another simplification.
(defthm
  lofat-place-file-correctness-lemma-74
  (implies
   (and
    (d-e-p d-e)
    (d-e-directory-p d-e)
    (equal (mv-nth 1
                   (lofat-place-file fat32$c d-e path file))
           0)
    (good-root-d-e-p root-d-e fat32$c)
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
    (fat32-filename-list-p path)
    (not (consp (cdr path)))
    (< 0
       (len (explode (lofat-file->contents file))))
    (<=
     2
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path)))))
    (<
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path))))
     (+ 2 (count-of-clusters fat32$c))))
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
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path))))))
            0 nil))
          1))
        (len (explode (lofat-file->contents file)))))
      (+ -1 entry-limit)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (e/d
     (subsetp-member)
     ((:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                . 5)
      (:definition member-intersectp-equal)
      (:rewrite lofat-place-file-correctness-lemma-93)
      (:rewrite lofat-to-hifat-helper-of-update-dir-contents)
      (:rewrite hifat-to-lofat-inversion-lemma-17)
      (:rewrite non-free-index-list-listp-of-effective-fat-of-place-contents)
      (:rewrite nfix-when-zp)
      (:linear nth-when-d-e-p)
      (:rewrite lofat-to-hifat-helper-of-place-contents)
      (:rewrite lofat-to-hifat-helper-of-update-fati)
      (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-3)
      (:rewrite lofat-to-hifat-helper-of-clear-cc)
      (:rewrite get-cc-contents-of-lofat-remove-file-coincident-lemma-5
                . 1)
      (:rewrite d-e-first-cluster-of-d-e-set-first-cluster-file-size)
      (:rewrite fat32-masked-entry-fix-when-fat32-masked-entry-p)
      (:rewrite intersectp-when-subsetp)
      (:definition find-d-e)
      (:rewrite lofat-place-file-correctness-lemma-5)
      (:definition position-equal-ac)
      (:rewrite fati-of-clear-cc . 3)
      (:definition make-list-ac)
      (:definition place-d-e)
      (:rewrite d-e-cc-of-place-contents-coincident-1))))))

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
  lofat-place-file-correctness-lemma-40
  (implies (lofat-regular-file-p file)
           (hifat-no-dups-p (lofat-file->contents file)))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (hifat-no-dups-p)
                           (lofat-place-file))
           :expand (hifat-no-dups-p (lofat-file->contents file)))))

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
  lofat-place-file-correctness-lemma-6
  (implies
   (and
    (equal
     (mv-nth
      1
      (hifat-place-file
       (mv-nth 0
               (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
       path file))
     fs)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
           0)
    (>= (nfix entry-limit2)
        (mv-nth 1
                (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))))
   (equal
    (mv-nth
     1
     (hifat-place-file
      (mv-nth 0
              (lofat-to-hifat-helper fat32$c d-e-list entry-limit2))
      path file))
    fs))
  :hints (("goal" :use lofat-to-hifat-helper-correctness-4)))

(defthmd
  lofat-place-file-correctness-lemma-70
  (implies
   (and (hifat-equiv
         (mv-nth 0
                 (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
         x)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
               0)
        (case-split
         (>= (nfix entry-limit2)
             (mv-nth 1
                     (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))))
        (hifat-equiv
         (cons (cons name
                     (m1-file-hifat-file-alist-fix d-e x))
               y)
         z))
   (equal
    (hifat-equiv
     (cons
      (cons
       name
       (m1-file-hifat-file-alist-fix
        d-e
        (mv-nth 0
                (lofat-to-hifat-helper fat32$c d-e-list entry-limit2))))
      y)
     z)
    t))
  :hints (("goal" :do-not-induct t
           :use lofat-to-hifat-helper-correctness-4)))

;; This lemma is somehow very destructive in terms of blowing up a lot of terms...
(defthmd
  lofat-place-file-correctness-lemma-25
  (b*
      (((mv cc-contents error-code)
        (d-e-cc-contents fat32$c d-e))
       (new-d-e
        (if
         (or (< 0
                (len (explode (lofat-file->contents file))))
             (lofat-directory-file-p file))
         (if
          (<=
           2
           (d-e-first-cluster
            (mv-nth
             0
             (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path)))))
          (if
           (<
            (d-e-first-cluster
             (mv-nth
              0
              (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                        (car path))))
            (+ 2 (count-of-clusters fat32$c)))
           (d-e-set-first-cluster-file-size
            (mv-nth
             0
             (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path))))))
                0 nil))
              1))
            (if (lofat-directory-file-p file)
                0
                (len (explode (lofat-file->contents file)))))
           (d-e-set-first-cluster-file-size
            (mv-nth
             0
             (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path)))
            (nth 0
                 (find-n-free-clusters (effective-fat fat32$c)
                                       1))
            (if (lofat-directory-file-p file)
                0
                (len (explode (lofat-file->contents file))))))
          (if
           (equal
            (mv-nth
             1
             (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path)))
            0)
           (d-e-set-first-cluster-file-size
            (mv-nth
             0
             (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path)))
            (nth 0
                 (find-n-free-clusters (effective-fat fat32$c)
                                       1))
            (if (lofat-directory-file-p file)
                0
                (len (explode (lofat-file->contents file)))))
           (d-e-set-first-cluster-file-size
            (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                       (lofat-directory-file-p file))
            (nth 0
                 (find-n-free-clusters (effective-fat fat32$c)
                                       1))
            (if (lofat-directory-file-p file)
                0
                (len (explode (lofat-file->contents file)))))))
         (if
          (equal
           (mv-nth
            1
            (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path)))
           0)
          (d-e-set-first-cluster-file-size
           (mv-nth
            0
            (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path)))
           0 0)
          (d-e-set-first-cluster-file-size
           (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                      (lofat-directory-file-p file))
           0 0))))
       (new-contents (nats=>chars (insert-d-e (string=>nats cc-contents)
                                              new-d-e))))
    (implies
     (and
      (good-root-d-e-p d-e fat32$c)
      (d-e-p d-e)
      (d-e-directory-p d-e)
      (fat32-filename-list-p path)
      (equal error-code 0)
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c (make-d-e-list cc-contents)
                                            entry-limit))
             0)
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c d-e))
       (mv-nth 2
               (lofat-to-hifat-helper fat32$c (make-d-e-list cc-contents)
                                      entry-limit)))
      (lofat-file-p file)
      (or (lofat-regular-file-p file)
          (equal (lofat-file->contents$inline file)
                 nil)))
     (equal
      (d-e-cc-contents (mv-nth 0
                               (lofat-place-file fat32$c d-e path file))
                       d-e)
      (if
       (and (equal (mv-nth 1
                           (lofat-place-file fat32$c d-e path file))
                   0)
            (atom (cdr path)))
       (mv
        (implode
         (append
          new-contents
          (make-list-ac (- (* (cluster-size fat32$c)
                              (len (make-clusters (implode new-contents)
                                                  (cluster-size fat32$c))))
                           (len new-contents))
                        (code-char 0)
                        nil)))
        0)
       (d-e-cc-contents fat32$c d-e)))))
  :hints
  (("goal" :use d-e-cc-contents-of-lofat-place-file-coincident-1
    :do-not-induct t
    :in-theory (e/d nil
                    (explode-of-d-e-filename clear-cc-correctness-1
                                             effective-fat-of-clear-cc
                                             lofat-place-file)))))

(defthmd
  lofat-place-file-correctness-lemma-214
  (implies
   (and
    (good-root-d-e-p root-d-e fat32$c)
    (lofat-file-p file)
    (or (lofat-regular-file-p file)
        (equal (lofat-file->contents file) nil))
    (non-free-index-listp x (effective-fat fat32$c))
    (not (intersectp-equal x (mv-nth 0 (d-e-cc fat32$c root-d-e))))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit))
     0)
    (not-intersectp-list
     x
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit)))
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c root-d-e))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit))))
   (and
    (not
     (intersectp-equal
      x
      (mv-nth 0
              (d-e-cc (mv-nth 0
                              (lofat-place-file fat32$c root-d-e path file))
                      root-d-e))))
    (not
     (intersectp-equal
      (mv-nth 0
              (d-e-cc (mv-nth 0
                              (lofat-place-file fat32$c root-d-e path file))
                      root-d-e))
      x))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (e/d (intersect-with-subset)
         ((:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                    . 5)
          lofat-place-file-correctness-lemma-65))
    :use lofat-place-file-correctness-lemma-65)))

(defthm
  lofat-place-file-correctness-lemma-226
  (implies
   (and
    (good-root-d-e-p root-d-e fat32$c)
    (lofat-file-p file)
    (or (lofat-regular-file-p file)
        (equal (lofat-file->contents file) nil))
    (non-free-index-list-listp l (effective-fat fat32$c))
    (not-intersectp-list (mv-nth 0 (d-e-cc fat32$c root-d-e))
                         l)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit))
     0)
    (not
     (member-intersectp-equal
      l
      (mv-nth
       2
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
        entry-limit))))
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c root-d-e))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit))))
   (not-intersectp-list
    (mv-nth 0
            (d-e-cc (mv-nth 0
                            (lofat-place-file fat32$c root-d-e path file))
                    root-d-e))
    l))
  :hints
  (("goal"
    :induct
    (not-intersectp-list
     (mv-nth 0
             (d-e-cc (mv-nth 0
                             (lofat-place-file fat32$c root-d-e path file))
                     root-d-e))
     l)
    :do-not-induct t
    :in-theory
    (e/d (lofat-place-file-correctness-lemma-214 not-intersectp-list
                                                 intersect-with-subset)
         (lofat-place-file)))))

(encapsulate
  ()

  (local
   (in-theory
    (disable
     (:definition intersectp-equal)
     (:definition len)
     (:rewrite subsetp-append1)
     (:rewrite
      nth-of-set-indices-in-fa-table-when-member)
     (:linear
      lofat-place-file-correctness-1-lemma-25)
     (:definition make-list-ac)
     (:rewrite
      not-intersectp-list-of-set-difference$-lemma-1)
     (:rewrite
      d-e-cc-of-clear-cc)
     (:rewrite
      nat-listp-if-fat32-masked-entry-list-p)
     (:rewrite member-of-append)
     (:definition binary-append)
     (:rewrite member-when-atom)
     (:rewrite put-assoc-equal-without-change . 2)
     (:rewrite d-e-cc-of-lofat-place-file-disjoint)
     (:rewrite d-e-cc-contents-of-lofat-place-file-disjoint)
     (:induction lofat-place-file)
     (:definition lofat-place-file)
     (:rewrite lofat-place-file-correctness-lemma-5)
     (:rewrite lofat-to-hifat-helper-of-update-dir-contents)
     (:rewrite delete-d-e-correctness-1)
     (:definition delete-d-e)
     (:rewrite fati-of-clear-cc . 3)
     (:definition place-d-e)
     (:rewrite lofat-find-file-correctness-1-lemma-6)
     (:rewrite hifat-to-lofat-inversion-lemma-23)
     (:rewrite hifat-to-lofat-inversion-lemma-2)
     (:rewrite natp-of-place-contents)
     (:rewrite disjoint-list-listp-of-lofat-to-hifat-helper)
     (:definition find-d-e)
     (:linear length-of-d-e-cc-contents . 3)
     (:linear length-of-d-e-cc-contents . 2)
     (:rewrite d-e-cc-under-iff . 2)
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
     (:rewrite chars=>nats-of-take)
     (:rewrite nats=>chars-of-take)
     (:rewrite nth-of-nats=>chars)
     (:rewrite take-when-atom)
     (:rewrite str::consp-of-explode)
     (:rewrite str::explode-when-not-stringp)
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
     (:rewrite take-of-len-free)
     (:rewrite rationalp-implies-acl2-numberp)
     (:definition subseq)
     (:definition subseq-list)
     (:definition remove-assoc-equal)
     (:definition nthcdr)
     (:definition min)
     (:type-prescription intersectp-equal)
     (:type-prescription binary-append)
     (:definition assoc-equal)
     (:definition char))))

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

  (defthm lofat-place-file-correctness-lemma-114
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
                                           stobj-disjoins-list find-d-e
                                           intersect-with-subset))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-94
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

  (defthm lofat-place-file-correctness-lemma-84
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

  (defthm lofat-place-file-correctness-lemma-100
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
                                           stobj-disjoins-list
                                           intersect-with-subset))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))))

  (defthm lofat-place-file-correctness-lemma-101
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

  (defthm
    lofat-place-file-correctness-lemma-8
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
            (mv-nth 0
                    (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit)))
         path
         (m1-file d-e (lofat-file->contents file))))
       0)
      (not (zp entry-limit))
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
         (make-d-e-list
          (mv-nth 0
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
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit))))))))
       0)
      (subdir-contents-p
       (mv-nth 0
               (d-e-cc-contents fat32$c (car d-e-list))))
      (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c (car d-e-list))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
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
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))
      (not
       (member-intersectp-equal
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth 0
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
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (car d-e-list))))
               (+ -1 entry-limit))))))))))
      (not
       (intersectp-equal x
                         (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))))
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
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
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))
      (lofat-file-p file)
      (lofat-regular-file-p file)
      (consp path)
      (<
       (+
        1
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth 0
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
      (fat32-filename-list-p path)
      (stobj-disjoins-list
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
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (car d-e-list))))
            (+ -1 entry-limit)))
          (mv-nth
           2
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
     (stobj-disjoins-list
      (mv-nth
       0
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
        (:rewrite
         hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e-lemma-3)
        (:linear lofat-to-hifat-helper-after-delete-and-clear-1-lemma-1)
        (:linear lofat-find-file-correctness-1-lemma-8)
        d-e-cc-of-update-dir-contents-coincident))
      :do-not-induct t
      :expand
      ((:free (fat32$c entry-limit)
              (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
       (:free (x1 x2 y)
              (not-intersectp-list x1 (cons x2 y)))
       (:free (d-e fat32$c d-e-list entry-limit)
              (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                     entry-limit))
       (find-d-e d-e-list name)))
     (if
      (not stable-under-simplificationp)
      nil
      '(:expand
        (lofat-place-file fat32$c (car d-e-list)
                          path file)))))

  (defthm
    lofat-place-file-correctness-lemma-9
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
         (m1-file d-e (lofat-file->contents file)))))
      (not (zp entry-limit))
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                            (+ -1 entry-limit)))
             0)
      (lofat-regular-file-p file)
      (useful-d-e-list-p d-e-list)
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
       (mv-nth 1
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file)))
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
               (find-d-e d-e-list name))
      :cases
      ((zp (mv-nth 1
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                     path file)))))))

  (defthm
    lofat-place-file-correctness-lemma-17
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
         (m1-file d-e (lofat-file->contents file)))))
      (not (zp entry-limit))
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                            (+ -1 entry-limit)))
             0)
      (lofat-regular-file-p file)
      (useful-d-e-list-p d-e-list)
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
       (mv-nth 1
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file)))
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
           (mv-nth 0
                   (d-e-cc-contents fat32$c
                                    (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
          (+ -1 entry-limit)))
        path
        (m1-file d-e (lofat-file->contents file))))))
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
               (find-d-e d-e-list name))
      :cases
      ((zp (mv-nth 1
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                     path file)))))))

  (defthm
    lofat-place-file-correctness-lemma-10
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
         (m1-file d-e (lofat-file->contents file)))))
      (not (zp entry-limit))
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                            (+ -1 entry-limit)))
             0)
      (lofat-regular-file-p file)
      (useful-d-e-list-p d-e-list)
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
       (mv-nth 1
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file)))
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
               (find-d-e d-e-list name))
      :cases
      ((zp (mv-nth 1
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                     path file)))))))

  (defthm
    lofat-place-file-correctness-lemma-113
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
         (m1-file d-e (lofat-file->contents file)))))
      (not (zp entry-limit))
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                            (+ -1 entry-limit)))
             0)
      (lofat-regular-file-p file)
      (useful-d-e-list-p d-e-list)
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
       (mv-nth 1
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file)))
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
           (mv-nth 0
                   (d-e-cc-contents fat32$c
                                    (mv-nth 0 (find-d-e (cdr d-e-list) name)))))
          (+ -1 entry-limit)))
        path
        (m1-file d-e (lofat-file->contents file))))))
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
               (find-d-e d-e-list name))
      :cases
      ((zp (mv-nth 1
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                     path file)))))))

  (defthm
    lofat-place-file-correctness-lemma-60
    (implies
     (and
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c (car d-e-list)
                                   path file))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents (mv-nth 0
                                    (lofat-place-file fat32$c (car d-e-list)
                                                      path file))
                            (car d-e-list))))
         entry-limit))
       0)
      (consp d-e-list)
      (not (zp entry-limit))
      (d-e-directory-p (car d-e-list))
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
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c (car d-e-list)
                                   path file))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents (mv-nth 0
                                    (lofat-place-file fat32$c (car d-e-list)
                                                      path file))
                            (car d-e-list))))
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
      (lofat-fs-p fat32$c))
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
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents (mv-nth 0
                                      (lofat-place-file fat32$c (car d-e-list)
                                                        path file))
                              (car d-e-list))))
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
                       (d-e-cc-contents
                        (mv-nth 0
                                (lofat-place-file fat32$c (car d-e-list)
                                                  path file))
                        (car d-e-list))))
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
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))))
    :instructions
    (:promote
     (:claim
      (and
       (case-split
        (<=
         (mv-nth
          1
          (lofat-to-hifat-helper
           (mv-nth 0
                   (lofat-place-file fat32$c (car d-e-list)
                                     path file))
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents (mv-nth 0
                                      (lofat-place-file fat32$c (car d-e-list)
                                                        path file))
                              (car d-e-list))))
           entry-limit))
         (nfix (+ -1 entry-limit))))
       (hifat-equiv
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
             (m1-file d-e (lofat-file->contents file))))))
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
                         (d-e-cc-contents
                          (mv-nth 0
                                  (lofat-place-file fat32$c (car d-e-list)
                                                    path file))
                          (car d-e-list))))
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
      :hints :none)
     (:rewrite
      lofat-place-file-correctness-lemma-70
      ((x
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
       (entry-limit1 entry-limit)))
     (:bash
      ("goal"
       :in-theory
       (e/d
        (not-intersectp-list lofat-to-hifat-helper-correctness-4
                             stobj-disjoins-list
                             find-d-e good-root-d-e-p)
        ((:type-prescription make-d-e-list)
         (:definition member-intersectp-equal)
         (:rewrite lofat-place-file-correctness-lemma-83)
         (:rewrite lofat-place-file-correctness-lemma-121
                   . 1)
         (:rewrite hifat-to-lofat-inversion-lemma-17)
         (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
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
                (find-d-e d-e-list name))))))

  (defthm
    lofat-place-file-correctness-lemma-160
    (implies
     (and
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
      (not (zp entry-limit))
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
            entry-limit)))))))
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
         (mv-nth 0
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
              (mv-nth 0
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
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))))
    :hints
    (("goal"
      :in-theory
      (e/d
       (not-intersectp-list lofat-to-hifat-helper-correctness-4
                            stobj-disjoins-list
                            find-d-e good-root-d-e-p)
       ((:type-prescription make-d-e-list)
        (:definition member-intersectp-equal)
        (:rewrite lofat-place-file-correctness-lemma-83)
        (:rewrite lofat-place-file-correctness-lemma-121
                  . 1)
        (:rewrite hifat-to-lofat-inversion-lemma-17)
        (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
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

  (defthm
    lofat-place-file-correctness-lemma-161
    (implies
     (and
      (consp d-e-list)
      (not (zp entry-limit))
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
      (lofat-regular-file-p file)
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
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c (car d-e-list)
                                   path file))
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit)))
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
         (m1-file d-e (lofat-file->contents file))))))
     (not-intersectp-list
      x
      (mv-nth
       2
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
             (make-d-e-list (mv-nth 0
                                    (d-e-cc-contents fat32$c (car d-e-list))))
             (+ -1 entry-limit))))))))))
    :instructions
    (:promote
     (:claim
      (equal
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          (mv-nth 0
                  (lofat-place-file fat32$c (car d-e-list)
                                    path file))
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          (+ -1 entry-limit))))
       (if
        (zp
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
           (m1-file d-e (lofat-file->contents file)))))
        (+
         (hifat-entry-count
          (mv-nth
           0
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list (mv-nth 0
                                   (d-e-cc-contents fat32$c (car d-e-list))))
            (+ -1 entry-limit))))
         (if
          (m1-regular-file-p (m1-file d-e (lofat-file->contents file)))
          0
          (hifat-entry-count
           (m1-file->contents (m1-file d-e (lofat-file->contents file)))))
         (cond
          ((not
            (zp
             (mv-nth
              1
              (hifat-find-file
               (mv-nth
                0
                (lofat-to-hifat-helper
                 fat32$c
                 (make-d-e-list
                  (mv-nth 0
                          (d-e-cc-contents fat32$c (car d-e-list))))
                 (+ -1 entry-limit)))
               path))))
           1)
          ((m1-regular-file-p
            (mv-nth
             0
             (hifat-find-file
              (mv-nth
               0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents fat32$c (car d-e-list))))
                (+ -1 entry-limit)))
              path)))
           0)
          (t
           (-
            (hifat-entry-count
             (m1-file->contents
              (mv-nth
               0
               (hifat-find-file
                (mv-nth
                 0
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list
                   (mv-nth 0
                           (d-e-cc-contents fat32$c (car d-e-list))))
                  (+ -1 entry-limit)))
                path))))))))
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit))))))
      :hints :none)
     (:change-goal nil t)
     (:=
      (hifat-entry-count
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c (car d-e-list)
                                   path file))
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit))))
      (hifat-entry-count
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
         (m1-file d-e (lofat-file->contents file))))))
     (:dive 1)
     (:claim (m1-file-p (m1-file d-e (lofat-file->contents file))))
     (:rewrite hifat-entry-count-of-hifat-place-file)
     :top
     :split
     (:bash
      ("goal"
       :in-theory
       (e/d
        (not-intersectp-list lofat-to-hifat-helper-correctness-4
                             stobj-disjoins-list find-d-e
                             lofat-place-file-correctness-lemma-25
                             lofat-place-file-correctness-lemma-214)
        ((:type-prescription make-d-e-list)
         (:definition member-intersectp-equal)
         (:rewrite lofat-place-file-correctness-lemma-83)
         (:rewrite lofat-place-file-correctness-lemma-121
                   . 1)
         (:rewrite hifat-to-lofat-inversion-lemma-17)
         (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
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
                (find-d-e d-e-list name))))))

  (defthm
    lofat-place-file-correctness-lemma-163
    (implies
     (and (d-e-directory-p (car d-e-list))
          (good-root-d-e-p root-d-e fat32$c)
          (equal (mv-nth 1
                         (d-e-cc-contents fat32$c (car d-e-list)))
                 0)
          (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c (car d-e-list))))
          (useful-d-e-list-p d-e-list))
     (good-root-d-e-p (car d-e-list)
                      fat32$c))
    :hints
    (("goal"
      :in-theory
      (e/d
       (not-intersectp-list lofat-to-hifat-helper-correctness-4
                            stobj-disjoins-list find-d-e
                            lofat-place-file-correctness-lemma-25
                            lofat-place-file-correctness-lemma-214
                            good-root-d-e-p)
       ((:type-prescription make-d-e-list)
        (:definition member-intersectp-equal)
        (:rewrite lofat-place-file-correctness-lemma-83)
        (:rewrite lofat-place-file-correctness-lemma-121
                  . 1)
        (:rewrite hifat-to-lofat-inversion-lemma-17)
        (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
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

  (defthm
    lofat-place-file-correctness-lemma-165
    (implies
     (and
      (not (zp entry-limit))
      (lofat-regular-file-p file)
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
         (m1-file d-e (lofat-file->contents file))))))
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
            entry-limit))))))))
    :rule-classes (:linear)
    :instructions
    (:promote
     (:=
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
        (m1-file d-e (lofat-file->contents file))))
      :equiv hifat-equiv)
     (:dive 1 1 2 2 1)
     (:claim (m1-file-p (m1-file d-e (lofat-file->contents file))))
     (:rewrite hifat-entry-count-of-hifat-place-file)
     :top
     (:bash
      ("goal"
       :in-theory
       (e/d
        (not-intersectp-list lofat-to-hifat-helper-correctness-4
                             stobj-disjoins-list find-d-e
                             lofat-place-file-correctness-lemma-25
                             lofat-place-file-correctness-lemma-214)
        ((:type-prescription make-d-e-list)
         (:definition member-intersectp-equal)
         (:rewrite lofat-place-file-correctness-lemma-83)
         (:rewrite lofat-place-file-correctness-lemma-121
                   . 1)
         (:rewrite hifat-to-lofat-inversion-lemma-17)
         (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
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
                (find-d-e d-e-list name))))))

  (defthm
    lofat-place-file-correctness-lemma-167
    (implies
     (and
      (not (zp entry-limit))
      (d-e-directory-p (car d-e-list))
      (<= 2 (d-e-first-cluster (car d-e-list)))
      (< (d-e-first-cluster (car d-e-list))
         (+ 2 (count-of-clusters fat32$c)))
      (good-root-d-e-p root-d-e fat32$c)
      (non-free-index-listp x (effective-fat fat32$c))
      (not
       (equal (mv-nth 1
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
         (make-d-e-list
          (mv-nth 0
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
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit))))))))
       0)
      (subdir-contents-p
       (mv-nth 0
               (d-e-cc-contents fat32$c (car d-e-list))))
      (no-duplicatesp-equal
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
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
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))
      (not
       (member-intersectp-equal
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth 0
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
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (car d-e-list))))
               (+ -1 entry-limit))))))))))
      (not (intersectp-equal
            x
            (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))))
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
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
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))
      (lofat-file-p file)
      (lofat-regular-file-p file)
      (consp path)
      (<
       (+
        1
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth 0
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
                 (mv-nth
                  0
                  (d-e-cc-contents fat32$c (car d-e-list))))
                (+ -1 entry-limit))))))))))
       entry-limit)
      (useful-d-e-list-p d-e-list)
      (fat32-filename-list-p path)
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit)))
         path
         (m1-file d-e (lofat-file->contents file))))
       (mv-nth 1
               (lofat-place-file fat32$c (car d-e-list)
                                 path file)))
      (stobj-disjoins-list
       (mv-nth
        0
        (lofat-place-file
         fat32$c
         (mv-nth
          0
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
            (mv-nth
             0
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
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (car d-e-list))))
            (+ -1 entry-limit)))
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
                  (mv-nth
                   0
                   (d-e-cc-contents fat32$c (car d-e-list))))
                 (+ -1 entry-limit))))))))
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
                (find-d-e d-e-list
                          (d-e-filename (car d-e-list)))))))
            entry-limit))))))
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
              (mv-nth
               0
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
     (stobj-disjoins-list
      (mv-nth
       0
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
                            stobj-disjoins-list find-d-e
                            lofat-place-file-correctness-lemma-25
                            lofat-place-file-correctness-lemma-214
                            intersect-with-subset)
       ((:type-prescription make-d-e-list)
        (:definition member-intersectp-equal)
        (:rewrite lofat-place-file-correctness-lemma-83)
        (:rewrite lofat-place-file-correctness-lemma-121
                  . 1)
        (:rewrite hifat-to-lofat-inversion-lemma-17)
        (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
        (:rewrite
         hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e-lemma-3)
        (:linear
         lofat-to-hifat-helper-after-delete-and-clear-1-lemma-1)
        (:linear lofat-find-file-correctness-1-lemma-8)
        d-e-cc-of-update-dir-contents-coincident))
      :do-not-induct t
      :expand
      ((:free
        (fat32$c entry-limit)
        (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
       (:free (x1 x2 y)
              (not-intersectp-list x1 (cons x2 y)))
       (:free (d-e fat32$c d-e-list entry-limit)
              (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                     entry-limit))
       (find-d-e d-e-list name)))
     (if
      (not stable-under-simplificationp)
      nil
      '(:expand
        (lofat-place-file fat32$c (car d-e-list)
                          path file)
        :cases
        ((zp (mv-nth 1
                     (lofat-place-file fat32$c (car d-e-list)
                                       path file))))))))

  (defthm
    lofat-place-file-correctness-lemma-85
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
         (m1-file d-e (lofat-file->contents file)))))
      (not (zp entry-limit))
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
      (useful-d-e-list-p d-e-list)
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
       (mv-nth 1
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file)))
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
      :in-theory
      (e/d
       (not-intersectp-list lofat-to-hifat-helper-correctness-4
                            stobj-disjoins-list find-d-e
                            lofat-place-file-correctness-lemma-25
                            lofat-place-file-correctness-lemma-214)
       ((:type-prescription make-d-e-list)
        (:definition member-intersectp-equal)
        (:rewrite lofat-place-file-correctness-lemma-83)
        (:rewrite lofat-place-file-correctness-lemma-121
                  . 1)
        (:rewrite hifat-to-lofat-inversion-lemma-17)
        (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
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
               (find-d-e d-e-list name))
      :cases
      ((zp (mv-nth 1
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                     path file)))))))

  (defthm
    lofat-place-file-correctness-lemma-179
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
         (m1-file d-e (lofat-file->contents file)))))
      (not (zp entry-limit))
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
      (useful-d-e-list-p d-e-list)
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
       (mv-nth 1
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file)))
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
           (mv-nth 0
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
               (make-d-e-list (mv-nth 0
                                      (d-e-cc-contents fat32$c (car d-e-list))))
               (+ -1 entry-limit))))))))
        path
        (m1-file d-e (lofat-file->contents file))))))
    :hints
    (("goal"
      :in-theory
      (e/d
       (not-intersectp-list lofat-to-hifat-helper-correctness-4
                            stobj-disjoins-list find-d-e
                            lofat-place-file-correctness-lemma-25
                            lofat-place-file-correctness-lemma-214)
       ((:type-prescription make-d-e-list)
        (:definition member-intersectp-equal)
        (:rewrite lofat-place-file-correctness-lemma-83)
        (:rewrite lofat-place-file-correctness-lemma-121
                  . 1)
        (:rewrite hifat-to-lofat-inversion-lemma-17)
        (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
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
               (find-d-e d-e-list name))
      :cases
      ((zp (mv-nth 1
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                     path file)))))))

  ;; hypotheses minimised.
  (defthm
    lofat-place-file-correctness-lemma-12
    (implies
     (and
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
      (consp path)
      (< (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
         entry-limit)
      (useful-d-e-list-p d-e-list)
      (fat32-filename-list-p path)
      (equal
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
         (m1-file d-e (lofat-file->contents file))))
       (mv-nth 1
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e d-e-list name))
                                 path file))))
     (lofat-place-file-spec-2 d-e x entry-limit
                              file path name d-e-list fat32$c))
    :hints
    (("goal"
      :in-theory (e/d (not-intersectp-list hifat-entry-count
                                           lofat-to-hifat-helper-correctness-4)
                      ())
      :induct (induction-scheme d-e-list entry-limit fat32$c x)
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))
     (if (not stable-under-simplificationp)
         nil
       '(:in-theory (e/d (not-intersectp-list hifat-entry-count
                                              lofat-to-hifat-helper-correctness-4
                                              lofat-place-file-spec-2)
                         ()))))
    :rule-classes
    ((:rewrite
      :corollary
      (implies
       (and
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
        (consp path)
        (< (hifat-entry-count
            (mv-nth 0
                    (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
           entry-limit)
        (useful-d-e-list-p d-e-list)
        (fat32-filename-list-p path)
        (equal
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
           (m1-file d-e (lofat-file->contents file))))
         (mv-nth 1
                 (lofat-place-file fat32$c
                                   (mv-nth 0 (find-d-e d-e-list name))
                                   path file)))
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
           (m1-file d-e (lofat-file->contents file))))))
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
      (("goal"
        :do-not-induct t
        :in-theory (e/d (stobj-disjoins-list lofat-place-file-spec-2)))))))

  (defthm
    lofat-place-file-correctness-lemma-182
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
      (not (zp entry-limit))
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                            (+ -1 entry-limit)))
             0)
      (useful-d-e-list-p d-e-list)
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
       (mv-nth 1
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file)))
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
                                           stobj-disjoins-list find-d-e))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name))
      :cases
      ((zp (mv-nth 1
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                     path file)))))))

  (defthm
    lofat-place-file-correctness-lemma-238
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
      (not (zp entry-limit))
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                            (+ -1 entry-limit)))
             0)
      (useful-d-e-list-p d-e-list)
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
       (mv-nth 1
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file)))
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
           (mv-nth 0
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
               (find-d-e d-e-list name))
      :cases
      ((zp (mv-nth 1
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                     path file)))))))

  (defthm
    lofat-place-file-correctness-lemma-88
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
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents)))))
      (not (zp entry-limit))
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                            (+ -1 entry-limit)))
             0)
      (useful-d-e-list-p d-e-list)
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
       (mv-nth 1
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file))))
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
                                           stobj-disjoins-list find-d-e))
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name))
      :cases
      ((zp (mv-nth 1
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                     path file)))))))

  (defthm
    lofat-place-file-correctness-lemma-241
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
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents)))))
      (not (zp entry-limit))
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) name)))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                            (+ -1 entry-limit)))
             0)
      (useful-d-e-list-p d-e-list)
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
       (mv-nth 1
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file))))
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
           (mv-nth 0
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
               (find-d-e d-e-list name))
      :cases
      ((zp (mv-nth 1
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                     path file)))))))

  (defthm
    lofat-place-file-correctness-lemma-99
    (implies
     (and
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-place-file fat32$c (car d-e-list)
                                 path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents (mv-nth 0
                                  (lofat-place-file fat32$c (car d-e-list)
                                                    path file))
                          (car d-e-list))))
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
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents (mv-nth 0
                                    (lofat-place-file fat32$c (car d-e-list)
                                                      path file))
                            (car d-e-list))))
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
      (consp d-e-list)
      (not (zp entry-limit))
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
       (mv-nth 1
               (lofat-place-file fat32$c (car d-e-list)
                                 path file))))
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
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents (mv-nth 0
                                      (lofat-place-file fat32$c (car d-e-list)
                                                        path file))
                              (car d-e-list))))
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
                       (d-e-cc-contents
                        (mv-nth 0
                                (lofat-place-file fat32$c (car d-e-list)
                                                  path file))
                        (car d-e-list))))
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
           '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
             (contents))))))
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
              (make-d-e-list (mv-nth 0
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
               (find-d-e d-e-list name))
      :cases ((zp (mv-nth 1
                          (lofat-place-file fat32$c (car d-e-list)
                                            path file)))))))

  (defthm
    lofat-place-file-correctness-lemma-244
    (implies
     (and
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
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-place-file fat32$c (car d-e-list)
                                 path file))
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents
                 (mv-nth 0
                         (lofat-place-file fat32$c (car d-e-list)
                                           path file))
                 (car d-e-list))))
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
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c (car d-e-list))))
            (+ -1 entry-limit)))))))
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c (car d-e-list)
                                   path file))
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents
                   (mv-nth 0
                           (lofat-place-file fat32$c (car d-e-list)
                                             path file))
                   (car d-e-list))))
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
                    (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit)))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents)))))
      (not (zp entry-limit))
      (d-e-directory-p (car d-e-list))
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
         (make-d-e-list
          (mv-nth 0
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
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit))))))))
       0)
      (subdir-contents-p
       (mv-nth 0
               (d-e-cc-contents fat32$c (car d-e-list))))
      (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c (car d-e-list))))
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
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
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))))
      (not
       (member-intersectp-equal
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth 0
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
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (car d-e-list))))
               (+ -1 entry-limit))))))))))
      (lofat-file-p file)
      (not (lofat-file->contents file))
      (consp path)
      (<
       (+
        1
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth 0
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
      (equal
       (mv-nth
        1
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit)))
         path
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents))))
       (mv-nth 1
               (lofat-place-file fat32$c (car d-e-list)
                                 path file)))
      (not
       (intersectp-equal x
                         (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))))
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit)))))
     (stobj-disjoins-list
      (mv-nth 0
              (lofat-place-file fat32$c (car d-e-list)
                                path file))
      d-e-list entry-limit x))
    :hints
    (("goal"
      :in-theory
      (e/d (not-intersectp-list hifat-entry-count
                                lofat-to-hifat-helper-correctness-4
                                stobj-disjoins-list
                                find-d-e intersect-with-subset)
           (d-e-cc-of-update-dir-contents-coincident))
      :do-not-induct t
      :expand
      ((:free (fat32$c entry-limit)
              (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
       (:free (x1 x2 y)
              (not-intersectp-list x1 (cons x2 y)))
       (:free (d-e fat32$c d-e-list entry-limit)
              (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                     entry-limit))
       (find-d-e d-e-list name))
      :cases ((zp (mv-nth 1
                          (lofat-place-file fat32$c (car d-e-list)
                                            path file)))))
     (if
      (not stable-under-simplificationp)
      nil
      '(:expand
        (lofat-place-file fat32$c (car d-e-list)
                          path file)))))

  (defthm
    lofat-place-file-correctness-lemma-89
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
      (not (zp entry-limit))
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
      (useful-d-e-list-p d-e-list)
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
       (mv-nth 1
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file))))
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
               (find-d-e d-e-list name))
      :cases
      ((zp (mv-nth 1
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                     path file)))))))

  (defthm
    lofat-place-file-correctness-lemma-105
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
      (not (zp entry-limit))
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
      (useful-d-e-list-p d-e-list)
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
       (mv-nth 1
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                 path file))))
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
           (mv-nth 0
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
               (make-d-e-list (mv-nth 0
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
               (find-d-e d-e-list name))
      :cases
      ((zp (mv-nth 1
                   (lofat-place-file fat32$c
                                     (mv-nth 0 (find-d-e (cdr d-e-list) name))
                                     path file)))))))

  (defthmd
    lofat-place-file-correctness-lemma-107
    (implies
     (and
      (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))
      (good-root-d-e-p root-d-e fat32$c)
      (non-free-index-listp x (effective-fat fat32$c))
      (fat32-filename-list-p path)
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
             0)
      (lofat-file-p file)
      (not (lofat-file->contents file))
      (consp path)
      (< (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
         entry-limit)
      (useful-d-e-list-p d-e-list)
      (equal
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
         path (m1-file d-e nil)))
       (mv-nth 1
               (lofat-place-file fat32$c
                                 (mv-nth 0 (find-d-e d-e-list name))
                                 path file)))
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
      :do-not-induct t
      :induct (induction-scheme d-e-list entry-limit fat32$c x)
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name)))
     (if (not stable-under-simplificationp)
         ()
       '(:in-theory (e/d (not-intersectp-list hifat-entry-count
                                              lofat-to-hifat-helper-correctness-4
                                              lofat-place-file-spec-1 find-d-e)))))
    :rule-classes
    ((:rewrite
      :corollary
      (implies
       (and
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
        (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))
        (good-root-d-e-p root-d-e fat32$c)
        (non-free-index-listp x (effective-fat fat32$c))
        (fat32-filename-list-p path)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               0)
        (lofat-file-p file)
        (not (lofat-file->contents file))
        (consp path)
        (< (hifat-entry-count
            (mv-nth 0
                    (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
           entry-limit)
        (useful-d-e-list-p d-e-list)
        (equal
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
           '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
             (contents))))
         (mv-nth 1
                 (lofat-place-file fat32$c
                                   (mv-nth 0 (find-d-e d-e-list name))
                                   path file)))
        (not-intersectp-list
         x
         (mv-nth 2
                 (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
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
           '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
             (contents))))))
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
    (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))
    (good-root-d-e-p root-d-e fat32$c)
    (fat32-filename-list-p path)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
           0)
    (lofat-file-p file)
    (not (lofat-file->contents file))
    (consp path)
    (< (hifat-entry-count
        (mv-nth 0
                (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
       entry-limit)
    (useful-d-e-list-p d-e-list)
    (equal
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
       '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
              0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
         (contents))))
     (mv-nth 1
             (lofat-place-file fat32$c
                               (mv-nth 0 (find-d-e d-e-list name))
                               path file)))
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
       '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
              0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
         (contents))))))
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
         '((d-e 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents)))))
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
  (("goal" :in-theory (e/d (stobj-disjoins-list lofat-place-file-spec-1
                                                non-free-index-listp)
                           (lofat-place-file))
    :do-not-induct t
    :use (:instance lofat-place-file-correctness-lemma-107
                    (x nil)
                    (d-e (d-e-fix nil))))))

(defthm
  lofat-place-file-correctness-lemma-11
  (implies
   (and
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
    (consp path)
    (< (hifat-entry-count
        (mv-nth 0
                (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
       entry-limit)
    (useful-d-e-list-p d-e-list)
    (fat32-filename-list-p path)
    (equal
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
       (m1-file d-e (lofat-file->contents file))))
     (mv-nth 1
             (lofat-place-file fat32$c
                               (mv-nth 0 (find-d-e d-e-list name))
                               path file))))
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
    (e/d (stobj-disjoins-list lofat-place-file-spec-2 non-free-index-listp)
         (lofat-place-file-correctness-lemma-12
          lofat-place-file
          (:rewrite d-e-cc-contents-of-lofat-place-file-coincident-1)))
    :use (:instance lofat-place-file-correctness-lemma-12
                    (x nil)))))

(defthm
  lofat-place-file-correctness-lemma-148
  (implies
   (and
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
    (d-e-directory-p
     (mv-nth
      0
      (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                (car path))))
    (good-root-d-e-p root-d-e fat32$c)
    (non-free-index-listp x (effective-fat fat32$c))
    (fat32-filename-list-p (cdr path))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit))
     0)
    (lofat-file-p file)
    (not (lofat-file->contents file))
    (consp (cdr path))
    (<
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
        entry-limit)))
     entry-limit)
    (useful-d-e-list-p
     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e))))
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
         (contents))))
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
       file)))
    (not-intersectp-list
     x
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
         (contents))))))
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
             (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-2)
             (:rewrite effective-fat-of-update-fati)
             (:rewrite lofat-place-file-correctness-lemma-144))
    :use
    (:instance
     (:rewrite lofat-place-file-correctness-lemma-107)
     (path (cdr path))
     (name (car path))
     (d-e-list
      (make-d-e-list (mv-nth 0
                             (d-e-cc-contents fat32$c root-d-e))))))))

(defthm
  lofat-place-file-correctness-lemma-75
  (implies
   (and
    (not
     (d-e-directory-p
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 (car path)))))
    (good-root-d-e-p root-d-e fat32$c)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit))
     0)
    (lofat-regular-file-p file)
    (<=
     2
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 (car path)))))
    (<
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 (car path))))
     (+ 2 (count-of-clusters fat32$c)))
    (< 0
       (len (explode (lofat-file->contents file))))
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
            (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
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
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
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
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (car path))))))))
    (not
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
             (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
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
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
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
          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
          (car path))))))))
   (equal
    (mv-nth
     3
     (lofat-to-hifat-helper
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
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                (car path)))))
            (make-list-ac
             (len
              (mv-nth
               0
               (d-e-cc
                fat32$c
                (mv-nth
                 0
                 (find-d-e (make-d-e-list
                            (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
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
                 (find-d-e (make-d-e-list
                            (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
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
                     (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
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
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
              (car path))))
           (d-e-file-size
            (mv-nth
             0
             (find-d-e
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
              (car path)))))))
        (mv-nth
         0
         (find-d-e
          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
          (car path)))
        (lofat-file->contents$inline file)
        (len (explode$inline (lofat-file->contents$inline file)))
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
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
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
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 (car path))))))
            0 nil))
          1))))
      (place-d-e
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       (d-e-set-first-cluster-file-size
        (mv-nth
         0
         (find-d-e
          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
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
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
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
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 (car path))))))
            0 nil))
          1))
        (len (explode$inline (lofat-file->contents$inline file)))))
      entry-limit))
    0))
  :hints
  (("goal"
    :do-not-induct t
    :expand (lofat-place-file fat32$c root-d-e path file)
    :in-theory
    (e/d (hifat-place-file (:rewrite lofat-to-hifat-inversion-lemma-4)
                           hifat-find-file)
         ((:definition find-d-e)
          (:definition place-d-e)
          (:rewrite lofat-fs-p-of-lofat-place-file-lemma-1)
          (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                    . 5))))))

(defthm
  lofat-place-file-correctness-118
  (implies
   (and
    (not
     (d-e-directory-p
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 (car path)))))
    (good-root-d-e-p root-d-e fat32$c)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit))
     0)
    (lofat-regular-file-p file)
    (<=
     2
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 (car path)))))
    (<
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 (car path))))
     (+ 2 (count-of-clusters fat32$c)))
    (< 0
       (len (explode (lofat-file->contents file))))
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
            (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
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
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
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
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (car path))))))))
    (not
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
             (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
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
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
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
          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
          (car path))))))))
   (equal
    (mv-nth
     '3
     (lofat-to-hifat-helper
      (mv-nth
       '0
       (place-contents
        (update-fati
         (nth
          '0
          (find-n-free-clusters
           (set-indices-in-fa-table
            (effective-fat fat32$c)
            (mv-nth
             '0
             (d-e-cc
              fat32$c
              (mv-nth
               '0
               (find-d-e
                (make-d-e-list (mv-nth '0
                                       (d-e-cc-contents fat32$c root-d-e)))
                (car path)))))
            (make-list-ac
             (len
              (mv-nth
               '0
               (d-e-cc
                fat32$c
                (mv-nth
                 '0
                 (find-d-e
                  (make-d-e-list (mv-nth '0
                                         (d-e-cc-contents fat32$c root-d-e)))
                  (car path))))))
             '0
             'nil))
           '1))
         (fat32-update-lower-28
          (fati
           (nth
            '0
            (find-n-free-clusters
             (set-indices-in-fa-table
              (effective-fat fat32$c)
              (mv-nth
               '0
               (d-e-cc
                fat32$c
                (mv-nth
                 '0
                 (find-d-e
                  (make-d-e-list (mv-nth '0
                                         (d-e-cc-contents fat32$c root-d-e)))
                  (car path)))))
              (make-list-ac
               (len
                (mv-nth
                 '0
                 (d-e-cc
                  fat32$c
                  (mv-nth
                   '0
                   (find-d-e (make-d-e-list
                              (mv-nth '0
                                      (d-e-cc-contents fat32$c root-d-e)))
                             (car path))))))
               '0
               'nil))
             '1))
           fat32$c)
          '268435455)
         (mv-nth
          '0
          (clear-cc
           fat32$c
           (d-e-first-cluster
            (mv-nth
             '0
             (find-d-e
              (make-d-e-list (mv-nth '0
                                     (d-e-cc-contents fat32$c root-d-e)))
              (car path))))
           (d-e-file-size
            (mv-nth
             '0
             (find-d-e
              (make-d-e-list (mv-nth '0
                                     (d-e-cc-contents fat32$c root-d-e)))
              (car path)))))))
        (mv-nth
         '0
         (find-d-e (make-d-e-list (mv-nth '0
                                          (d-e-cc-contents fat32$c root-d-e)))
                   (car path)))
        (lofat-file->contents$inline file)
        (len (explode$inline (lofat-file->contents$inline file)))
        (nth
         '0
         (find-n-free-clusters
          (set-indices-in-fa-table
           (effective-fat fat32$c)
           (mv-nth
            '0
            (d-e-cc
             fat32$c
             (mv-nth
              '0
              (find-d-e
               (make-d-e-list (mv-nth '0
                                      (d-e-cc-contents fat32$c root-d-e)))
               (car path)))))
           (make-list-ac
            (len
             (mv-nth
              '0
              (d-e-cc
               fat32$c
               (mv-nth
                '0
                (find-d-e
                 (make-d-e-list (mv-nth '0
                                        (d-e-cc-contents fat32$c root-d-e)))
                 (car path))))))
            '0
            'nil))
          '1))))
      (place-d-e
       (make-d-e-list (mv-nth '0
                              (d-e-cc-contents fat32$c root-d-e)))
       (d-e-set-first-cluster-file-size
        (mv-nth
         '0
         (find-d-e (make-d-e-list (mv-nth '0
                                          (d-e-cc-contents fat32$c root-d-e)))
                   (car path)))
        (nth
         '0
         (find-n-free-clusters
          (set-indices-in-fa-table
           (effective-fat fat32$c)
           (mv-nth
            '0
            (d-e-cc
             fat32$c
             (mv-nth
              '0
              (find-d-e
               (make-d-e-list (mv-nth '0
                                      (d-e-cc-contents fat32$c root-d-e)))
               (car path)))))
           (make-list-ac
            (len
             (mv-nth
              '0
              (d-e-cc
               fat32$c
               (mv-nth
                '0
                (find-d-e
                 (make-d-e-list (mv-nth '0
                                        (d-e-cc-contents fat32$c root-d-e)))
                 (car path))))))
            '0
            'nil))
          '1))
        (len (explode$inline (lofat-file->contents$inline file)))))
      entry-limit))
    '0))
  :hints
  (("goal"
    :in-theory
    (e/d (hifat-place-file (:rewrite lofat-to-hifat-inversion-lemma-4)
                           hifat-find-file)
         ((:definition find-d-e)
          (:definition place-d-e)
          (:rewrite lofat-fs-p-of-lofat-place-file-lemma-1)
          (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                    . 5))))))

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
    :rule-classes (:linear :rewrite))

  (defthm
    lofat-place-file-correctness-lemma-117
    (implies
     (and
      (useful-d-e-list-p d-e-list)
      (not (d-e-directory-p (d-e-fix d-e)))
      (zp
       (mv-nth
        3
        (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
      (>
       (nfix entry-limit)
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))))
     (equal
      (mv-nth
       0
       (lofat-to-hifat-helper fat32$c (place-d-e d-e-list d-e)
                              entry-limit))
      (put-assoc-equal
       (d-e-filename d-e)
       (m1-file
        d-e
        (if (or (< (d-e-first-cluster (d-e-fix d-e)) 2)
                (<= (+ 2 (count-of-clusters fat32$c))
                    (d-e-first-cluster (d-e-fix d-e))))
            ""
          (mv-nth 0
                  (d-e-cc-contents fat32$c (d-e-fix d-e)))))
       (mv-nth
        0
        (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))))
    :hints
    (("goal"
      :in-theory
      (e/d
       (lofat-to-hifat-helper hifat-entry-count)
       ((:rewrite nth-of-effective-fat)
        (:rewrite nth-of-nats=>chars)
        (:linear nth-when-d-e-p)
        (:rewrite explode-of-d-e-filename)
        (:rewrite take-of-len-free)
        (:rewrite
         hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e-lemma-3)
        (:rewrite put-assoc-equal-without-change . 2)
        (:rewrite nats=>chars-of-take)))
      :induct (lofat-to-hifat-helper fat32$c d-e-list entry-limit)
      :do-not-induct t
      :expand
      (:free (fat32$c d-e d-e-list entry-limit)
             (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                    entry-limit)))))

  (local (in-theory (disable
                     (:DEFINITION BUTLAST)
                     (:DEFINITION NFIX)
                     (:DEFINITION LENGTH)
                     (:DEFINITION MIN))))

  ;; This was a counterexample, but now it's fixed. Both hifat-place-file and
  ;; lofat-place-file needed to return *enoent*, while they were respectively
  ;; returning *enotdir* and *eio*.
  (thm
   (implies
    (and
     (fat32-filename-list-p path)
     (equal
      (mv-nth
       3
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
        entry-limit))
      0)
     (not
      (equal
       (mv-nth
        1
        (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                  (car path)))
       0))
     (consp (cdr path))
     (lofat-directory-file-p file))
    (and
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
      *enoent*)
     (equal (mv-nth 1
                    (lofat-place-file fat32$c root-d-e path file))
            *enoent*)))
   :hints
   (("goal"
     :do-not-induct t
     :expand ((lofat-place-file fat32$c root-d-e path file))
     :in-theory
     (e/d (hifat-place-file (:rewrite lofat-to-hifat-inversion-lemma-4)
                            hifat-find-file)
          ((:definition find-d-e)
           (:definition place-d-e)
           (:rewrite lofat-fs-p-of-lofat-place-file-lemma-1)
           (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                     . 5))))))

  ;; This used to be a counterexample because lofat-place-file used to return
  ;; *ENOTDIR*, but no longer.
  (thm
   (implies
    (and
     (fat32-filename-list-p path)
     (equal
      (mv-nth
       3
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
        entry-limit))
      0)
     (lofat-regular-file-p file)
     (not
      (equal
       (mv-nth
        1
        (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                  (car path)))
       0))
     (consp (cdr path)))
    (and
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
      *enoent*)
     (equal (mv-nth 1
                    (lofat-place-file fat32$c root-d-e path file))
            *enoent*)))
   :hints
   (("goal"
     :do-not-induct t
     :expand ((lofat-place-file fat32$c root-d-e path file))
     :in-theory
     (e/d (hifat-place-file (:rewrite lofat-to-hifat-inversion-lemma-4)
                            hifat-find-file)
          ((:definition find-d-e)
           (:definition place-d-e)
           (:rewrite lofat-fs-p-of-lofat-place-file-lemma-1)
           (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                     . 5))))))

  ;; This used to be a counterexample, because lofat-place-file used to return
  ;; *enotdir*.
  (thm
   (implies
    (and
     (not
      (d-e-directory-p
       (mv-nth
        0
        (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                  (car path)))))
     (fat32-filename-list-p path)
     (equal
      (mv-nth
       3
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
        entry-limit))
      0)
     (lofat-file-p file)
     (not (lofat-file->contents file))
     (<=
      2
      (d-e-first-cluster
       (mv-nth
        0
        (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                  (car path)))))
     (consp path)
     (not (consp (cdr path))))
    (and
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
      *eexist*)
     (equal (mv-nth 1
                    (lofat-place-file fat32$c root-d-e path file))
            *eexist*)))
   :hints
   (("goal"
     :do-not-induct t
     :expand ((lofat-place-file fat32$c root-d-e path file))
     :in-theory
     (e/d (hifat-place-file (:rewrite lofat-to-hifat-inversion-lemma-4)
                            hifat-find-file)
          ((:definition find-d-e)
           (:definition place-d-e)
           (:rewrite lofat-fs-p-of-lofat-place-file-lemma-1)
           (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                     . 5))))))

  (defthm
    lofat-place-file-correctness-lemma-116
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
      (or (stringp (lofat-file->contents file))
          (equal (lofat-file->contents file) nil))
      (not (equal (mv-nth 1
                          (lofat-place-file fat32$c root-d-e path file))
                  *enospc*))
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
       (mv-nth 1
               (lofat-place-file fat32$c root-d-e path file)))))
    :hints
    (("goal"
      :induct (induction-scheme entry-limit
                                fat32$c file path root-d-e x)
      :expand ((lofat-place-file fat32$c root-d-e path file))
      :in-theory
      (e/d (hifat-place-file (:rewrite lofat-to-hifat-inversion-lemma-4)
                             hifat-find-file
                             subsetp-member)
           ((:definition find-d-e)
            (:definition place-d-e)
            (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                      . 5)))))
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
        (or (lofat-regular-file-p file)
            (equal (lofat-file->contents file) nil))
        (not (equal (mv-nth 1
                            (lofat-place-file fat32$c root-d-e path file))
                    *enospc*))
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
    (or (stringp (lofat-file->contents file))
        (equal (lofat-file->contents file) nil))
    (not (equal (mv-nth 1
                        (lofat-place-file fat32$c root-d-e path file))
                *enospc*))
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
     (mv-nth 1
             (lofat-place-file fat32$c root-d-e path file)))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (non-free-index-listp)
     (lofat-place-file-correctness-lemma-116
      (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                . 5)
      lofat-place-file))
    :use (:instance lofat-place-file-correctness-lemma-116
                    (x nil))
    :do-not-induct t)))

;; Hypotheses and conditional branches pretty much minimised.
(encapsulate
  ()

  (local
   (defthmd
     lemma
     (b*
         (((mv cc-contents error-code)
           (d-e-cc-contents fat32$c d-e)))
       (implies
        (and
         (lofat-fs-p fat32$c)
         (d-e-p d-e)
         (d-e-directory-p d-e)
         (fat32-filename-list-p path)
         (equal error-code 0)
         (equal (mv-nth 3
                        (lofat-to-hifat-helper fat32$c (make-d-e-list cc-contents)
                                               entry-limit))
                0)
         (not-intersectp-list
          (mv-nth 0 (d-e-cc fat32$c d-e))
          (mv-nth 2
                  (lofat-to-hifat-helper fat32$c (make-d-e-list cc-contents)
                                         entry-limit)))
         (lofat-file-p file)
         (equal (mv-nth 1
                        (lofat-place-file fat32$c d-e path file))
                0))
        (equal
         (d-e-cc (mv-nth 0
                         (lofat-place-file fat32$c d-e path file))
                 d-e)
         (cond
          ((and
            (lofat-fs-p fat32$c)
            (d-e-p d-e)
            (d-e-directory-p d-e)
            (fat32-filename-list-p path)
            (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
                   0)
            (equal
             (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit))
             0)
            (not-intersectp-list
             (mv-nth 0 (d-e-cc fat32$c d-e))
             (mv-nth 2
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit)))
            (consp path)
            (equal
             (mv-nth
              1
              (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                        (car path)))
             0)
            (lofat-file-p file)
            (not (consp (cdr path)))
            (not
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path))))))
                  0 nil))
                1))
              (mv-nth 0 (d-e-cc fat32$c d-e))))
            (<=
             (+
              64
              (* 32
                 (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
             2097152)
            (not
             (d-e-directory-p
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (<=
             2
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (<=
             (+ 2 (count-of-clusters fat32$c))
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (lofat-regular-file-p file)
            (equal (lofat-file->contents file) "")
            (equal
             (mv-nth
              1
              (update-dir-contents
               fat32$c (d-e-first-cluster d-e)
               (implode
                (nats=>chars
                 (insert-d-e
                  (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (d-e-set-first-cluster-file-size
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))
                   0 0))))))
             0))
           (d-e-cc
            (mv-nth
             0
             (update-dir-contents
              fat32$c (d-e-first-cluster d-e)
              (implode
               (nats=>chars
                (insert-d-e
                 (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (d-e-set-first-cluster-file-size
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path)))
                  0 0))))))
            d-e))
          ((and
            (lofat-fs-p fat32$c)
            (d-e-p d-e)
            (d-e-directory-p d-e)
            (fat32-filename-list-p path)
            (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
                   0)
            (equal
             (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit))
             0)
            (not-intersectp-list
             (mv-nth 0 (d-e-cc fat32$c d-e))
             (mv-nth 2
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit)))
            (consp path)
            (equal
             (mv-nth
              1
              (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                        (car path)))
             0)
            (not (consp (cdr path)))
            (lofat-file-p file)
            (not
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path))))))
                  0 nil))
                1))
              (mv-nth 0 (d-e-cc fat32$c d-e))))
            (<=
             (+
              64
              (* 32
                 (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
             2097152)
            (not
             (d-e-directory-p
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (<=
             2
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (<=
             (+ 2 (count-of-clusters fat32$c))
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (not (lofat-directory-file-p file))
            (< 0
               (len (explode (lofat-file->contents file))))
            (<= 1
                (count-free-clusters (effective-fat fat32$c)))
            (equal (lofat-place-file-helper fat32$c d-e path file)
                   0)
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
                (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                          (car path)))
               (lofat-file->contents file)
               (len (explode (lofat-file->contents file)))
               (nth 0
                    (find-n-free-clusters (effective-fat fat32$c)
                                          1))))
             0)
            (equal
             (mv-nth
              1
              (update-dir-contents
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path)))
                 (lofat-file->contents file)
                 (len (explode (lofat-file->contents file)))
                 (nth 0
                      (find-n-free-clusters (effective-fat fat32$c)
                                            1))))
               (d-e-first-cluster d-e)
               (implode
                (nats=>chars
                 (insert-d-e
                  (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (d-e-set-first-cluster-file-size
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))
                   (nth 0
                        (find-n-free-clusters (effective-fat fat32$c)
                                              1))
                   (len (explode (lofat-file->contents file)))))))))
             0)
            (not (equal (lofat-file->contents file) "")))
           (d-e-cc
            (mv-nth
             0
             (update-dir-contents
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
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path)))
                (lofat-file->contents file)
                (len (explode (lofat-file->contents file)))
                (nth 0
                     (find-n-free-clusters (effective-fat fat32$c)
                                           1))))
              (d-e-first-cluster d-e)
              (implode
               (nats=>chars
                (insert-d-e
                 (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (d-e-set-first-cluster-file-size
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path)))
                  (nth 0
                       (find-n-free-clusters (effective-fat fat32$c)
                                             1))
                  (len (explode (lofat-file->contents file)))))))))
            d-e))
          ((and
            (not
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path))))))
                  0 nil))
                1))
              (mv-nth 0 (d-e-cc fat32$c d-e))))
            (lofat-fs-p fat32$c)
            (d-e-p d-e)
            (d-e-directory-p d-e)
            (fat32-filename-list-p path)
            (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
                   0)
            (equal
             (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit))
             0)
            (not-intersectp-list
             (mv-nth 0 (d-e-cc fat32$c d-e))
             (mv-nth 2
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit)))
            (consp path)
            (equal
             (mv-nth
              1
              (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                        (car path)))
             0)
            (<=
             (+
              64
              (* 32
                 (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
             2097152)
            (lofat-file-p file)
            (not
             (d-e-directory-p
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (<=
             2
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (<
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path))))
             (+ 2 (count-of-clusters fat32$c)))
            (not (consp (cdr path)))
            (not (equal (lofat-file->contents file) ""))
            (lofat-regular-file-p file)
            (equal (lofat-place-file-helper fat32$c d-e path file)
                   0)
            (equal
             (mv-nth
              2
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
                     (make-list-ac
                      (len
                       (mv-nth
                        0
                        (d-e-cc
                         fat32$c
                         (mv-nth
                          0
                          (find-d-e (make-d-e-list
                                     (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path))))
                  (d-e-file-size
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))))
               (mv-nth
                0
                (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                        (car path))))))
                   0 nil))
                 1))))
             0)
            (equal
             (mv-nth
              1
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
                         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
                     (make-list-ac
                      (len
                       (mv-nth
                        0
                        (d-e-cc
                         fat32$c
                         (mv-nth
                          0
                          (find-d-e (make-d-e-list
                                     (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (find-d-e (make-d-e-list
                                     (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                              (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path))))
                    (d-e-file-size
                     (mv-nth
                      0
                      (find-d-e
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path)))))))
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                          (car path))))))
                     0 nil))
                   1))))
               (d-e-first-cluster d-e)
               (implode
                (nats=>chars
                 (insert-d-e
                  (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (d-e-set-first-cluster-file-size
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                             (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                            (car path))))))
                       0 nil))
                     1))
                   (len (explode (lofat-file->contents file)))))))))
             0)
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
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))))
                 0 nil))
               1))
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                          (car path)))))))
           (d-e-cc
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
                        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                             (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))
                   (d-e-file-size
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path)))))))
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path))))))
                    0 nil))
                  1))))
              (d-e-first-cluster d-e)
              (implode
               (nats=>chars
                (insert-d-e
                 (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (d-e-set-first-cluster-file-size
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
                     (make-list-ac
                      (len
                       (mv-nth
                        0
                        (d-e-cc
                         fat32$c
                         (mv-nth
                          0
                          (find-d-e (make-d-e-list
                                     (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                                    (car path))))))
                      0 nil))
                    1))
                  (len (explode (lofat-file->contents file)))))))))
            d-e))
          ((and
            (lofat-fs-p fat32$c)
            (d-e-p d-e)
            (d-e-directory-p d-e)
            (fat32-filename-list-p path)
            (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
                   0)
            (equal
             (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit))
             0)
            (not-intersectp-list
             (mv-nth 0 (d-e-cc fat32$c d-e))
             (mv-nth 2
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit)))
            (consp path)
            (equal
             (mv-nth
              1
              (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                        (car path)))
             0)
            (not
             (d-e-directory-p
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (lofat-file-p file)
            (<=
             2
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (<
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path))))
             (+ 2 (count-of-clusters fat32$c)))
            (not (consp (cdr path)))
            (equal (lofat-file->contents file) "")
            (not
             (equal
              (mv-nth
               1
               (update-dir-contents
                fat32$c (d-e-first-cluster d-e)
                (implode
                 (nats=>chars
                  (insert-d-e
                   (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (d-e-set-first-cluster-file-size
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path)))
                    0 0))))))
              0))
            (not (equal (lofat-place-file-helper fat32$c d-e path file)
                        0))
            (lofat-regular-file-p file)
            (<=
             (+
              64
              (* 32
                 (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
             2097152)
            (equal
             (mv-nth
              1
              (update-dir-contents
               (mv-nth
                0
                (clear-cc
                 fat32$c
                 (d-e-first-cluster
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path))))
                 (d-e-file-size
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path))))))
               (d-e-first-cluster d-e)
               (implode
                (nats=>chars
                 (insert-d-e
                  (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (d-e-set-first-cluster-file-size
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))
                   0 0))))))
             0))
           (d-e-cc
            (mv-nth
             0
             (update-dir-contents
              (mv-nth
               0
               (clear-cc
                fat32$c
                (d-e-first-cluster
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))
                (d-e-file-size
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))))
              (d-e-first-cluster d-e)
              (implode
               (nats=>chars
                (insert-d-e
                 (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (d-e-set-first-cluster-file-size
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path)))
                  0 0))))))
            d-e))
          ((and
            (lofat-fs-p fat32$c)
            (d-e-p d-e)
            (d-e-directory-p d-e)
            (fat32-filename-list-p path)
            (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
                   0)
            (equal
             (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit))
             0)
            (not-intersectp-list
             (mv-nth 0 (d-e-cc fat32$c d-e))
             (mv-nth 2
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit)))
            (consp path)
            (equal
             (mv-nth
              1
              (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                        (car path)))
             0)
            (not
             (d-e-directory-p
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (lofat-file-p file)
            (<=
             2
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (<
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path))))
             (+ 2 (count-of-clusters fat32$c)))
            (not (consp (cdr path)))
            (equal (lofat-file->contents file) "")
            (not (lofat-directory-file-p file))
            (not
             (equal
              (mv-nth
               1
               (update-dir-contents
                fat32$c (d-e-first-cluster d-e)
                (implode
                 (nats=>chars
                  (insert-d-e
                   (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (d-e-set-first-cluster-file-size
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path)))
                    0 0))))))
              0))
            (equal (lofat-place-file-helper fat32$c d-e path file)
                   0)
            (<=
             (+
              64
              (* 32
                 (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
             2097152)
            (equal
             (mv-nth
              1
              (update-dir-contents
               (mv-nth
                0
                (clear-cc
                 fat32$c
                 (d-e-first-cluster
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path))))
                 (d-e-file-size
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path))))))
               (d-e-first-cluster d-e)
               (implode
                (nats=>chars
                 (insert-d-e
                  (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (d-e-set-first-cluster-file-size
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))
                   0 0))))))
             0))
           (d-e-cc
            (mv-nth
             0
             (update-dir-contents
              (mv-nth
               0
               (clear-cc
                fat32$c
                (d-e-first-cluster
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))
                (d-e-file-size
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))))
              (d-e-first-cluster d-e)
              (implode
               (nats=>chars
                (insert-d-e
                 (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (d-e-set-first-cluster-file-size
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path)))
                  0 0))))))
            d-e))
          ((and
            (not
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path))))))
                  0 nil))
                1))
              (mv-nth 0 (d-e-cc fat32$c d-e))))
            (lofat-fs-p fat32$c)
            (d-e-p d-e)
            (d-e-directory-p d-e)
            (fat32-filename-list-p path)
            (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
                   0)
            (equal
             (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit))
             0)
            (not-intersectp-list
             (mv-nth 0 (d-e-cc fat32$c d-e))
             (mv-nth 2
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit)))
            (consp path)
            (not (lofat-regular-file-p file))
            (<=
             (+
              64
              (* 32
                 (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
             2097152)
            (lofat-file-p file)
            (<=
             2
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (d-e-directory-p
             (mv-nth
              0
              (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                        (car path))))
            (<
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path))))
             (+ 2 (count-of-clusters fat32$c)))
            (equal (lofat-place-file-helper fat32$c d-e path file)
                   0)
            (equal
             (mv-nth
              1
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
                         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
                     (make-list-ac
                      (len
                       (mv-nth
                        0
                        (d-e-cc
                         fat32$c
                         (mv-nth
                          0
                          (find-d-e (make-d-e-list
                                     (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (find-d-e (make-d-e-list
                                     (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                              (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path))))
                    2097152)))
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path)))
                 (make-empty-subdir-contents
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
                         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
                     (make-list-ac
                      (len
                       (mv-nth
                        0
                        (d-e-cc
                         fat32$c
                         (mv-nth
                          0
                          (find-d-e (make-d-e-list
                                     (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                                    (car path))))))
                      0 nil))
                    1))
                  (d-e-first-cluster d-e))
                 0
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
                        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                          (car path))))))
                     0 nil))
                   1))))
               (d-e-first-cluster d-e)
               (implode
                (nats=>chars
                 (insert-d-e
                  (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (d-e-set-first-cluster-file-size
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                             (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                            (car path))))))
                       0 nil))
                     1))
                   0))))))
             0)
            (not (consp (cdr path)))
            (not
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path)))))))
            (not (equal (lofat-file->contents file) "")))
           (d-e-cc
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
                        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                             (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))
                   2097152)))
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path)))
                (make-empty-subdir-contents
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
                        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                          (car path))))))
                     0 nil))
                   1))
                 (d-e-first-cluster d-e))
                0
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path))))))
                    0 nil))
                  1))))
              (d-e-first-cluster d-e)
              (implode
               (nats=>chars
                (insert-d-e
                 (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (d-e-set-first-cluster-file-size
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
                     (make-list-ac
                      (len
                       (mv-nth
                        0
                        (d-e-cc
                         fat32$c
                         (mv-nth
                          0
                          (find-d-e (make-d-e-list
                                     (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                                    (car path))))))
                      0 nil))
                    1))
                  0))))))
            d-e))
          ((and
            (not
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path))))))
                  0 nil))
                1))
              (mv-nth 0 (d-e-cc fat32$c d-e))))
            (lofat-fs-p fat32$c)
            (d-e-p d-e)
            (d-e-directory-p d-e)
            (fat32-filename-list-p path)
            (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
                   0)
            (equal
             (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit))
             0)
            (not-intersectp-list
             (mv-nth 0 (d-e-cc fat32$c d-e))
             (mv-nth 2
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit)))
            (consp path)
            (<=
             2
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (lofat-file-p file)
            (d-e-directory-p
             (mv-nth
              0
              (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                        (car path))))
            (<
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path))))
             (+ 2 (count-of-clusters fat32$c)))
            (not (lofat-regular-file-p file))
            (<=
             (+
              64
              (* 32
                 (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
             2097152)
            (equal (lofat-place-file-helper fat32$c d-e path file)
                   0)
            (equal
             (mv-nth
              1
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
                         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
                     (make-list-ac
                      (len
                       (mv-nth
                        0
                        (d-e-cc
                         fat32$c
                         (mv-nth
                          0
                          (find-d-e (make-d-e-list
                                     (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (find-d-e (make-d-e-list
                                     (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                              (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path))))
                    2097152)))
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path)))
                 (make-empty-subdir-contents
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
                         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
                     (make-list-ac
                      (len
                       (mv-nth
                        0
                        (d-e-cc
                         fat32$c
                         (mv-nth
                          0
                          (find-d-e (make-d-e-list
                                     (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                                    (car path))))))
                      0 nil))
                    1))
                  (d-e-first-cluster d-e))
                 0
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
                        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                          (car path))))))
                     0 nil))
                   1))))
               (d-e-first-cluster d-e)
               (implode
                (nats=>chars
                 (insert-d-e
                  (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (d-e-set-first-cluster-file-size
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                             (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                            (car path))))))
                       0 nil))
                     1))
                   0))))))
             0)
            (not (consp (cdr path)))
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
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))))
                 0 nil))
               1))
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                          (car path))))))
            (not (equal (lofat-file->contents file) "")))
           (d-e-cc
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
                        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                             (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))
                   2097152)))
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path)))
                (make-empty-subdir-contents
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
                        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                          (car path))))))
                     0 nil))
                   1))
                 (d-e-first-cluster d-e))
                0
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path))))))
                    0 nil))
                  1))))
              (d-e-first-cluster d-e)
              (implode
               (nats=>chars
                (insert-d-e
                 (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (d-e-set-first-cluster-file-size
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
                     (make-list-ac
                      (len
                       (mv-nth
                        0
                        (d-e-cc
                         fat32$c
                         (mv-nth
                          0
                          (find-d-e (make-d-e-list
                                     (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                                    (car path))))))
                      0 nil))
                    1))
                  0))))))
            d-e))
          ((and
            (lofat-fs-p fat32$c)
            (d-e-p d-e)
            (d-e-directory-p d-e)
            (fat32-filename-list-p path)
            (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
                   0)
            (equal
             (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit))
             0)
            (not-intersectp-list
             (mv-nth 0 (d-e-cc fat32$c d-e))
             (mv-nth 2
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit)))
            (consp path)
            (equal
             (mv-nth
              1
              (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                        (car path)))
             0)
            (not
             (d-e-directory-p
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (lofat-file-p file)
            (<
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path))))
             (+ 2 (count-of-clusters fat32$c)))
            (not (consp (cdr path)))
            (<=
             2
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (equal (lofat-file->contents file) "")
            (not (lofat-directory-file-p file))
            (equal
             (mv-nth
              1
              (update-dir-contents
               fat32$c (d-e-first-cluster d-e)
               (implode
                (nats=>chars
                 (insert-d-e
                  (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (d-e-set-first-cluster-file-size
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))
                   0 0))))))
             0)
            (not (equal (lofat-place-file-helper fat32$c d-e path file)
                        0))
            (<=
             (+
              64
              (* 32
                 (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
             2097152)
            (equal
             (mv-nth
              1
              (update-dir-contents
               (mv-nth
                0
                (clear-cc
                 fat32$c
                 (d-e-first-cluster
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path))))
                 (d-e-file-size
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path))))))
               (d-e-first-cluster d-e)
               (implode
                (nats=>chars
                 (insert-d-e
                  (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (d-e-set-first-cluster-file-size
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))
                   0 0))))))
             0))
           (d-e-cc
            (mv-nth
             0
             (update-dir-contents
              (mv-nth
               0
               (clear-cc
                fat32$c
                (d-e-first-cluster
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))
                (d-e-file-size
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))))
              (d-e-first-cluster d-e)
              (implode
               (nats=>chars
                (insert-d-e
                 (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (d-e-set-first-cluster-file-size
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path)))
                  0 0))))))
            d-e))
          ((and
            (lofat-fs-p fat32$c)
            (d-e-p d-e)
            (d-e-directory-p d-e)
            (fat32-filename-list-p path)
            (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
                   0)
            (equal
             (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit))
             0)
            (not-intersectp-list
             (mv-nth 0 (d-e-cc fat32$c d-e))
             (mv-nth 2
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit)))
            (consp path)
            (equal
             (mv-nth
              1
              (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                        (car path)))
             0)
            (<=
             (+ 2 (count-of-clusters fat32$c))
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (not (lofat-directory-file-p file))
            (< 0
               (len (explode (lofat-file->contents file))))
            (<= 1
                (count-free-clusters (effective-fat fat32$c)))
            (<=
             (+
              64
              (* 32
                 (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
             2097152)
            (equal (lofat-place-file-helper fat32$c d-e path file)
                   0)
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
                (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                          (car path)))
               (lofat-file->contents file)
               (len (explode (lofat-file->contents file)))
               (nth 0
                    (find-n-free-clusters (effective-fat fat32$c)
                                          1))))
             0)
            (equal
             (mv-nth
              1
              (update-dir-contents
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path)))
                 (lofat-file->contents file)
                 (len (explode (lofat-file->contents file)))
                 (nth 0
                      (find-n-free-clusters (effective-fat fat32$c)
                                            1))))
               (d-e-first-cluster d-e)
               (implode
                (nats=>chars
                 (insert-d-e
                  (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (d-e-set-first-cluster-file-size
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))
                   (nth 0
                        (find-n-free-clusters (effective-fat fat32$c)
                                              1))
                   (len (explode (lofat-file->contents file)))))))))
             0)
            (lofat-file-p file)
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
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))))
                 0 nil))
               1))
             (mv-nth 0 (d-e-cc fat32$c d-e)))
            (not
             (d-e-directory-p
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (not (consp (cdr path)))
            (<=
             2
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (not (equal (lofat-file->contents file) "")))
           (d-e-cc
            (mv-nth
             0
             (update-dir-contents
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
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path)))
                (lofat-file->contents file)
                (len (explode (lofat-file->contents file)))
                (nth 0
                     (find-n-free-clusters (effective-fat fat32$c)
                                           1))))
              (d-e-first-cluster d-e)
              (implode
               (nats=>chars
                (insert-d-e
                 (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (d-e-set-first-cluster-file-size
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path)))
                  (nth 0
                       (find-n-free-clusters (effective-fat fat32$c)
                                             1))
                  (len (explode (lofat-file->contents file)))))))))
            d-e))
          ((and
            (not
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path))))))
                  0 nil))
                1))
              (mv-nth 0 (d-e-cc fat32$c d-e))))
            (lofat-fs-p fat32$c)
            (d-e-p d-e)
            (d-e-directory-p d-e)
            (fat32-filename-list-p path)
            (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
                   0)
            (equal
             (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit))
             0)
            (not-intersectp-list
             (mv-nth 0 (d-e-cc fat32$c d-e))
             (mv-nth 2
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit)))
            (consp path)
            (not (lofat-regular-file-p file))
            (<=
             (+
              64
              (* 32
                 (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
             2097152)
            (equal (lofat-place-file-helper fat32$c d-e path file)
                   0)
            (equal
             (mv-nth
              1
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
                         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
                     (make-list-ac
                      (len
                       (mv-nth
                        0
                        (d-e-cc
                         fat32$c
                         (mv-nth
                          0
                          (find-d-e (make-d-e-list
                                     (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (find-d-e (make-d-e-list
                                     (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                              (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path))))
                    2097152)))
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path)))
                 (make-empty-subdir-contents
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
                         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
                     (make-list-ac
                      (len
                       (mv-nth
                        0
                        (d-e-cc
                         fat32$c
                         (mv-nth
                          0
                          (find-d-e (make-d-e-list
                                     (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                                    (car path))))))
                      0 nil))
                    1))
                  (d-e-first-cluster d-e))
                 0
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
                        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                          (car path))))))
                     0 nil))
                   1))))
               (d-e-first-cluster d-e)
               (implode
                (nats=>chars
                 (insert-d-e
                  (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (d-e-set-first-cluster-file-size
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                             (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                            (car path))))))
                       0 nil))
                     1))
                   0))))))
             0)
            (lofat-file-p file)
            (d-e-directory-p
             (mv-nth
              0
              (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                        (car path))))
            (not (consp (cdr path)))
            (<=
             2
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (<
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path))))
             (+ 2 (count-of-clusters fat32$c)))
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
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))))
                 0 nil))
               1))
             (mv-nth
              0
              (d-e-cc
               fat32$c
               (mv-nth
                0
                (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                          (car path))))))
            (equal (lofat-file->contents file) ""))
           (d-e-cc
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
                        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                             (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))
                   2097152)))
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path)))
                (make-empty-subdir-contents
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
                        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                          (car path))))))
                     0 nil))
                   1))
                 (d-e-first-cluster d-e))
                0
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path))))))
                    0 nil))
                  1))))
              (d-e-first-cluster d-e)
              (implode
               (nats=>chars
                (insert-d-e
                 (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (d-e-set-first-cluster-file-size
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
                     (make-list-ac
                      (len
                       (mv-nth
                        0
                        (d-e-cc
                         fat32$c
                         (mv-nth
                          0
                          (find-d-e (make-d-e-list
                                     (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                                    (car path))))))
                      0 nil))
                    1))
                  0))))))
            d-e))
          ((and
            (lofat-fs-p fat32$c)
            (d-e-p d-e)
            (d-e-directory-p d-e)
            (fat32-filename-list-p path)
            (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
                   0)
            (equal
             (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit))
             0)
            (not-intersectp-list
             (mv-nth 0 (d-e-cc fat32$c d-e))
             (mv-nth 2
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit)))
            (consp path)
            (equal
             (mv-nth
              1
              (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                        (car path)))
             0)
            (not
             (d-e-directory-p
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (lofat-file-p file)
            (not (consp (cdr path)))
            (<=
             2
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (<
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path))))
             (+ 2 (count-of-clusters fat32$c)))
            (equal (lofat-file->contents file) "")
            (not (lofat-directory-file-p file))
            (equal
             (mv-nth
              1
              (update-dir-contents
               fat32$c (d-e-first-cluster d-e)
               (implode
                (nats=>chars
                 (insert-d-e
                  (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (d-e-set-first-cluster-file-size
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))
                   0 0))))))
             0)
            (equal (lofat-place-file-helper fat32$c d-e path file)
                   0)
            (<=
             (+
              64
              (* 32
                 (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
             2097152)
            (equal
             (mv-nth
              1
              (update-dir-contents
               (mv-nth
                0
                (clear-cc
                 fat32$c
                 (d-e-first-cluster
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path))))
                 (d-e-file-size
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path))))))
               (d-e-first-cluster d-e)
               (implode
                (nats=>chars
                 (insert-d-e
                  (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (d-e-set-first-cluster-file-size
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))
                   0 0))))))
             0))
           (d-e-cc
            (mv-nth
             0
             (update-dir-contents
              (mv-nth
               0
               (clear-cc
                fat32$c
                (d-e-first-cluster
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))
                (d-e-file-size
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))))
              (d-e-first-cluster d-e)
              (implode
               (nats=>chars
                (insert-d-e
                 (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (d-e-set-first-cluster-file-size
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path)))
                  0 0))))))
            d-e))
          ((and
            (lofat-fs-p fat32$c)
            (d-e-p d-e)
            (d-e-directory-p d-e)
            (fat32-filename-list-p path)
            (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
                   0)
            (equal
             (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit))
             0)
            (not-intersectp-list
             (mv-nth 0 (d-e-cc fat32$c d-e))
             (mv-nth 2
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit)))
            (consp path)
            (equal
             (mv-nth
              1
              (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                        (car path)))
             0)
            (not (consp (cdr path)))
            (lofat-file-p file)
            (<
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path))))
             2)
            (not
             (d-e-directory-p
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (not (lofat-directory-file-p file))
            (< 0
               (len (explode (lofat-file->contents file))))
            (<= 1
                (count-free-clusters (effective-fat fat32$c)))
            (<=
             (+
              64
              (* 32
                 (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
             2097152)
            (equal (lofat-place-file-helper fat32$c d-e path file)
                   0)
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
                (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                          (car path)))
               (lofat-file->contents file)
               (len (explode (lofat-file->contents file)))
               (nth 0
                    (find-n-free-clusters (effective-fat fat32$c)
                                          1))))
             0)
            (equal
             (mv-nth
              1
              (update-dir-contents
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path)))
                 (lofat-file->contents file)
                 (len (explode (lofat-file->contents file)))
                 (nth 0
                      (find-n-free-clusters (effective-fat fat32$c)
                                            1))))
               (d-e-first-cluster d-e)
               (implode
                (nats=>chars
                 (insert-d-e
                  (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (d-e-set-first-cluster-file-size
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))
                   (nth 0
                        (find-n-free-clusters (effective-fat fat32$c)
                                              1))
                   (len (explode (lofat-file->contents file)))))))))
             0)
            (<
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path))))
             (+ 2 (count-of-clusters fat32$c)))
            (not
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path))))))
                  0 nil))
                1))
              (mv-nth 0 (d-e-cc fat32$c d-e))))
            (not (equal (lofat-file->contents file) "")))
           (d-e-cc
            (mv-nth
             0
             (update-dir-contents
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
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path)))
                (lofat-file->contents file)
                (len (explode (lofat-file->contents file)))
                (nth 0
                     (find-n-free-clusters (effective-fat fat32$c)
                                           1))))
              (d-e-first-cluster d-e)
              (implode
               (nats=>chars
                (insert-d-e
                 (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (d-e-set-first-cluster-file-size
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path)))
                  (nth 0
                       (find-n-free-clusters (effective-fat fat32$c)
                                             1))
                  (len (explode (lofat-file->contents file)))))))))
            d-e))
          ((and
            (lofat-fs-p fat32$c)
            (d-e-p d-e)
            (d-e-directory-p d-e)
            (fat32-filename-list-p path)
            (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
                   0)
            (equal
             (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit))
             0)
            (not-intersectp-list
             (mv-nth 0 (d-e-cc fat32$c d-e))
             (mv-nth 2
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit)))
            (consp path)
            (equal
             (mv-nth
              1
              (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                        (car path)))
             0)
            (<
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path))))
             2)
            (not
             (d-e-directory-p
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (not (lofat-directory-file-p file))
            (< 0
               (len (explode (lofat-file->contents file))))
            (<= 1
                (count-free-clusters (effective-fat fat32$c)))
            (<=
             (+
              64
              (* 32
                 (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
             2097152)
            (equal (lofat-place-file-helper fat32$c d-e path file)
                   0)
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
                (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                          (car path)))
               (lofat-file->contents file)
               (len (explode (lofat-file->contents file)))
               (nth 0
                    (find-n-free-clusters (effective-fat fat32$c)
                                          1))))
             0)
            (equal
             (mv-nth
              1
              (update-dir-contents
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path)))
                 (lofat-file->contents file)
                 (len (explode (lofat-file->contents file)))
                 (nth 0
                      (find-n-free-clusters (effective-fat fat32$c)
                                            1))))
               (d-e-first-cluster d-e)
               (implode
                (nats=>chars
                 (insert-d-e
                  (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (d-e-set-first-cluster-file-size
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))
                   (nth 0
                        (find-n-free-clusters (effective-fat fat32$c)
                                              1))
                   (len (explode (lofat-file->contents file)))))))))
             0)
            (lofat-file-p file)
            (<
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path))))
             (+ 2 (count-of-clusters fat32$c)))
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
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))))
                 0 nil))
               1))
             (mv-nth 0 (d-e-cc fat32$c d-e)))
            (not (equal (lofat-file->contents file) ""))
            (not (consp (cdr path))))
           (d-e-cc
            (mv-nth
             0
             (update-dir-contents
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
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path)))
                (lofat-file->contents file)
                (len (explode (lofat-file->contents file)))
                (nth 0
                     (find-n-free-clusters (effective-fat fat32$c)
                                           1))))
              (d-e-first-cluster d-e)
              (implode
               (nats=>chars
                (insert-d-e
                 (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (d-e-set-first-cluster-file-size
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path)))
                  (nth 0
                       (find-n-free-clusters (effective-fat fat32$c)
                                             1))
                  (len (explode (lofat-file->contents file)))))))))
            d-e))
          ((and
            (lofat-fs-p fat32$c)
            (d-e-p d-e)
            (d-e-directory-p d-e)
            (fat32-filename-list-p path)
            (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
                   0)
            (equal
             (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit))
             0)
            (not-intersectp-list
             (mv-nth 0 (d-e-cc fat32$c d-e))
             (mv-nth 2
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit)))
            (consp path)
            (equal
             (mv-nth
              1
              (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                        (car path)))
             0)
            (<=
             (+ 2 (count-of-clusters fat32$c))
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (not
             (d-e-directory-p
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (not (lofat-directory-file-p file))
            (<=
             (+
              64
              (* 32
                 (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
             2097152)
            (lofat-file-p file)
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
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))))
                 0 nil))
               1))
             (mv-nth 0 (d-e-cc fat32$c d-e)))
            (equal (lofat-file->contents file) "")
            (not (consp (cdr path)))
            (equal
             (mv-nth
              1
              (update-dir-contents
               fat32$c (d-e-first-cluster d-e)
               (implode
                (nats=>chars
                 (insert-d-e
                  (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (d-e-set-first-cluster-file-size
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))
                   0 0))))))
             0)
            (<=
             2
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path))))))
           (d-e-cc
            (mv-nth
             0
             (update-dir-contents
              fat32$c (d-e-first-cluster d-e)
              (implode
               (nats=>chars
                (insert-d-e
                 (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (d-e-set-first-cluster-file-size
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path)))
                  0 0))))))
            d-e))
          ((and
            (not
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path))))))
                  0 nil))
                1))
              (mv-nth 0 (d-e-cc fat32$c d-e))))
            (lofat-fs-p fat32$c)
            (d-e-p d-e)
            (d-e-directory-p d-e)
            (fat32-filename-list-p path)
            (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
                   0)
            (equal
             (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit))
             0)
            (not-intersectp-list
             (mv-nth 0 (d-e-cc fat32$c d-e))
             (mv-nth 2
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit)))
            (consp path)
            (<=
             2
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (not (lofat-regular-file-p file))
            (not
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path)))))))
            (equal
             (mv-nth
              1
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
                         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
                     (make-list-ac
                      (len
                       (mv-nth
                        0
                        (d-e-cc
                         fat32$c
                         (mv-nth
                          0
                          (find-d-e (make-d-e-list
                                     (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (find-d-e (make-d-e-list
                                     (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                              (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path))))
                    2097152)))
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path)))
                 (make-empty-subdir-contents
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
                         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
                     (make-list-ac
                      (len
                       (mv-nth
                        0
                        (d-e-cc
                         fat32$c
                         (mv-nth
                          0
                          (find-d-e (make-d-e-list
                                     (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                                    (car path))))))
                      0 nil))
                    1))
                  (d-e-first-cluster d-e))
                 0
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
                        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                          (car path))))))
                     0 nil))
                   1))))
               (d-e-first-cluster d-e)
               (implode
                (nats=>chars
                 (insert-d-e
                  (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (d-e-set-first-cluster-file-size
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                             (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                            (car path))))))
                       0 nil))
                     1))
                   0))))))
             0)
            (lofat-file-p file)
            (equal (lofat-file->contents file) "")
            (not (consp (cdr path)))
            (d-e-directory-p
             (mv-nth
              0
              (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                        (car path))))
            (<
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path))))
             (+ 2 (count-of-clusters fat32$c)))
            (<=
             (+
              64
              (* 32
                 (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
             2097152)
            (equal (lofat-place-file-helper fat32$c d-e path file)
                   0))
           (d-e-cc
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
                        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                             (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))
                   2097152)))
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path)))
                (make-empty-subdir-contents
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
                        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                          (car path))))))
                     0 nil))
                   1))
                 (d-e-first-cluster d-e))
                0
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path))))))
                    0 nil))
                  1))))
              (d-e-first-cluster d-e)
              (implode
               (nats=>chars
                (insert-d-e
                 (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (d-e-set-first-cluster-file-size
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
                     (make-list-ac
                      (len
                       (mv-nth
                        0
                        (d-e-cc
                         fat32$c
                         (mv-nth
                          0
                          (find-d-e (make-d-e-list
                                     (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                                    (car path))))))
                      0 nil))
                    1))
                  0))))))
            d-e))
          ((and
            (lofat-fs-p fat32$c)
            (d-e-p d-e)
            (d-e-directory-p d-e)
            (fat32-filename-list-p path)
            (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
                   0)
            (equal
             (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit))
             0)
            (not-intersectp-list
             (mv-nth 0 (d-e-cc fat32$c d-e))
             (mv-nth 2
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit)))
            (consp path)
            (not
             (equal
              (mv-nth
               1
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))
              0))
            (not (lofat-regular-file-p file))
            (<= 1
                (count-free-clusters (effective-fat fat32$c)))
            (<=
             (+
              96
              (* 32
                 (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
             2097152)
            (equal (lofat-place-file-helper fat32$c d-e path file)
                   0)
            (equal
             (mv-nth
              1
              (update-dir-contents
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
                 (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                            t)
                 (make-empty-subdir-contents
                  (nth 0
                       (find-n-free-clusters (effective-fat fat32$c)
                                             1))
                  (d-e-first-cluster d-e))
                 0
                 (nth 0
                      (find-n-free-clusters (effective-fat fat32$c)
                                            1))))
               (d-e-first-cluster d-e)
               (implode
                (nats=>chars
                 (insert-d-e
                  (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (d-e-set-first-cluster-file-size
                   (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                              t)
                   (nth 0
                        (find-n-free-clusters (effective-fat fat32$c)
                                              1))
                   0))))))
             0)
            (lofat-file-p file)
            (not (consp (cdr path))))
           (d-e-cc
            (mv-nth
             0
             (update-dir-contents
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
                (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                           t)
                (make-empty-subdir-contents
                 (nth 0
                      (find-n-free-clusters (effective-fat fat32$c)
                                            1))
                 (d-e-first-cluster d-e))
                0
                (nth 0
                     (find-n-free-clusters (effective-fat fat32$c)
                                           1))))
              (d-e-first-cluster d-e)
              (implode
               (nats=>chars
                (insert-d-e
                 (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (d-e-set-first-cluster-file-size
                  (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                             t)
                  (nth 0
                       (find-n-free-clusters (effective-fat fat32$c)
                                             1))
                  0))))))
            d-e))
          ((and
            (lofat-fs-p fat32$c)
            (d-e-p d-e)
            (d-e-directory-p d-e)
            (fat32-filename-list-p path)
            (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
                   0)
            (equal
             (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit))
             0)
            (not-intersectp-list
             (mv-nth 0 (d-e-cc fat32$c d-e))
             (mv-nth 2
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit)))
            (consp path)
            (not
             (equal
              (mv-nth
               1
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))
              0))
            (not (lofat-directory-file-p file))
            (< 0
               (len (explode (lofat-file->contents file))))
            (<= 1
                (count-free-clusters (effective-fat fat32$c)))
            (<=
             (+
              96
              (* 32
                 (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
             2097152)
            (equal (lofat-place-file-helper fat32$c d-e path file)
                   0)
            (equal
             (mv-nth
              1
              (update-dir-contents
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
                 (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                            nil)
                 (lofat-file->contents file)
                 (len (explode (lofat-file->contents file)))
                 (nth 0
                      (find-n-free-clusters (effective-fat fat32$c)
                                            1))))
               (d-e-first-cluster d-e)
               (implode
                (nats=>chars
                 (insert-d-e
                  (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (d-e-set-first-cluster-file-size
                   (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                              nil)
                   (nth 0
                        (find-n-free-clusters (effective-fat fat32$c)
                                              1))
                   (len (explode (lofat-file->contents file)))))))))
             0)
            (lofat-file-p file)
            (not (equal (lofat-file->contents file) ""))
            (not (consp (cdr path)))
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
               (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                          nil)
               (lofat-file->contents file)
               (len (explode (lofat-file->contents file)))
               (nth 0
                    (find-n-free-clusters (effective-fat fat32$c)
                                          1))))
             0))
           (d-e-cc
            (mv-nth
             0
             (update-dir-contents
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
                (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                           nil)
                (lofat-file->contents file)
                (len (explode (lofat-file->contents file)))
                (nth 0
                     (find-n-free-clusters (effective-fat fat32$c)
                                           1))))
              (d-e-first-cluster d-e)
              (implode
               (nats=>chars
                (insert-d-e
                 (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (d-e-set-first-cluster-file-size
                  (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                             nil)
                  (nth 0
                       (find-n-free-clusters (effective-fat fat32$c)
                                             1))
                  (len (explode (lofat-file->contents file)))))))))
            d-e))
          ((and
            (equal (lofat-file->contents file) "")
            (lofat-fs-p fat32$c)
            (d-e-p d-e)
            (d-e-directory-p d-e)
            (fat32-filename-list-p path)
            (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
                   0)
            (equal
             (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit))
             0)
            (not-intersectp-list
             (mv-nth 0 (d-e-cc fat32$c d-e))
             (mv-nth 2
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit)))
            (consp path)
            (equal
             (mv-nth
              1
              (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                        (car path)))
             0)
            (not (consp (cdr path)))
            (not
             (d-e-directory-p
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (not (lofat-directory-file-p file))
            (<=
             (+
              64
              (* 32
                 (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
             2097152)
            (equal
             (mv-nth
              1
              (update-dir-contents
               fat32$c (d-e-first-cluster d-e)
               (implode
                (nats=>chars
                 (insert-d-e
                  (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (d-e-set-first-cluster-file-size
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))
                   0 0))))))
             0)
            (lofat-file-p file)
            (<
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path))))
             2))
           (d-e-cc
            (mv-nth
             0
             (update-dir-contents
              fat32$c (d-e-first-cluster d-e)
              (implode
               (nats=>chars
                (insert-d-e
                 (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (d-e-set-first-cluster-file-size
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path)))
                  0 0))))))
            d-e))
          ((and
            (equal (lofat-file->contents file) "")
            (lofat-fs-p fat32$c)
            (d-e-p d-e)
            (d-e-directory-p d-e)
            (fat32-filename-list-p path)
            (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
                   0)
            (equal
             (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit))
             0)
            (not-intersectp-list
             (mv-nth 0 (d-e-cc fat32$c d-e))
             (mv-nth 2
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit)))
            (consp path)
            (not
             (equal
              (mv-nth
               1
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))
              0))
            (not (lofat-directory-file-p file))
            (<=
             (+
              96
              (* 32
                 (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
             2097152)
            (equal
             (mv-nth
              1
              (update-dir-contents
               fat32$c (d-e-first-cluster d-e)
               (implode
                (nats=>chars
                 (insert-d-e
                  (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (d-e-set-first-cluster-file-size
                   (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                              nil)
                   0 0))))))
             0)
            (lofat-file-p file)
            (not (consp (cdr path))))
           (d-e-cc
            (mv-nth
             0
             (update-dir-contents
              fat32$c (d-e-first-cluster d-e)
              (implode
               (nats=>chars
                (insert-d-e
                 (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (d-e-set-first-cluster-file-size
                  (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                             nil)
                  0 0))))))
            d-e))
          ((and
            (not
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path))))))
                  0 nil))
                1))
              (mv-nth 0 (d-e-cc fat32$c d-e))))
            (lofat-fs-p fat32$c)
            (d-e-p d-e)
            (d-e-directory-p d-e)
            (fat32-filename-list-p path)
            (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
                   0)
            (equal
             (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit))
             0)
            (not-intersectp-list
             (mv-nth 0 (d-e-cc fat32$c d-e))
             (mv-nth 2
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      entry-limit)))
            (consp path)
            (equal
             (mv-nth
              1
              (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                        (car path)))
             0)
            (<=
             2
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (<
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path))))
             (+ 2 (count-of-clusters fat32$c)))
            (not
             (d-e-directory-p
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
            (<=
             (+
              64
              (* 32
                 (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
             2097152)
            (equal (lofat-place-file-helper fat32$c d-e path file)
                   0)
            (equal
             (mv-nth
              2
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
                     (make-list-ac
                      (len
                       (mv-nth
                        0
                        (d-e-cc
                         fat32$c
                         (mv-nth
                          0
                          (find-d-e (make-d-e-list
                                     (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path))))
                  (d-e-file-size
                   (mv-nth
                    0
                    (find-d-e
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))))
               (mv-nth
                0
                (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                        (car path))))))
                   0 nil))
                 1))))
             0)
            (equal
             (mv-nth
              1
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
                         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
                     (make-list-ac
                      (len
                       (mv-nth
                        0
                        (d-e-cc
                         fat32$c
                         (mv-nth
                          0
                          (find-d-e (make-d-e-list
                                     (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (find-d-e (make-d-e-list
                                     (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                              (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path))))
                    (d-e-file-size
                     (mv-nth
                      0
                      (find-d-e
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path)))))))
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                          (car path))))))
                     0 nil))
                   1))))
               (d-e-first-cluster d-e)
               (implode
                (nats=>chars
                 (insert-d-e
                  (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                             (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                               (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                               (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                                 (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                          (car path))))
                       (d-e-file-size
                        (mv-nth
                         0
                         (find-d-e
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                          (car path)))))))
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (find-d-e (make-d-e-list
                                     (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                              (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                             (car path))))))
                        0 nil))
                      1)))))))))
             0)
            (lofat-file-p file)
            (not (consp (cdr path)))
            (not (lofat-directory-file-p file))
            (< 0
               (len (explode (lofat-file->contents file))))
            (not
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path))))))))
           (d-e-cc
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
                        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                             (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))
                   (d-e-file-size
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path)))))))
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path))))))
                    0 nil))
                  1))))
              (d-e-first-cluster d-e)
              (implode
               (nats=>chars
                (insert-d-e
                 (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (d-e-set-first-cluster-file-size
                  (mv-nth
                   0
                   (find-d-e
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))))
                     (make-list-ac
                      (len
                       (mv-nth
                        0
                        (d-e-cc
                         fat32$c
                         (mv-nth
                          0
                          (find-d-e (make-d-e-list
                                     (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                                    (car path))))))
                      0 nil))
                    1))
                  (len (explode (lofat-file->contents file)))))))))
            d-e))
          (t
           (d-e-cc
            (mv-nth
             0
             (lofat-place-file
              fat32$c
              (mv-nth
               0
               (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path)))
              (cdr path)
              file))
            d-e))))))
     :hints
     (("goal"
       :expand (lofat-place-file fat32$c d-e path file)
       :do-not-induct t
       :in-theory
       (e/d (update-dir-contents-correctness-1 nats=>string subsetp-member)
            (explode-of-d-e-filename clear-cc-correctness-1
                                     effective-fat-of-clear-cc))))))

  ;; This looks rather different from the similarly named
  ;; d-e-cc-contents-of-lofat-place-file-coincident-1 because we chose to take
  ;; advantage of its no-change loser nature.
  ;; It's kept disabled because it really can cause havoc by expanding terms
  ;; that were smaller and easier to understand before.
  (defthmd
    d-e-cc-of-lofat-place-file-coincident-1
   (implies
    (and
     (good-root-d-e-p d-e fat32$c)
     (fat32-filename-list-p path)
     (equal
      (mv-nth 3
              (lofat-to-hifat-helper
               fat32$c
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
               entry-limit))
      0)
     (not-intersectp-list
      (mv-nth 0 (d-e-cc fat32$c d-e))
      (mv-nth 2
              (lofat-to-hifat-helper
               fat32$c
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
               entry-limit)))
     (lofat-file-p file)
     (or (lofat-regular-file-p file)
         (equal (lofat-file->contents file) nil)))
    (equal
     (d-e-cc (mv-nth 0
                     (lofat-place-file fat32$c d-e path file))
             d-e)
     (cond
      ((not (equal (mv-nth 1
                           (lofat-place-file fat32$c d-e path file))
                   0))
       (d-e-cc fat32$c d-e))
      ((and
        (lofat-fs-p fat32$c)
        (d-e-p d-e)
        (d-e-directory-p d-e)
        (fat32-filename-list-p path)
        (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
               0)
        (equal
         (mv-nth 3
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit))
         0)
        (not-intersectp-list
         (mv-nth 0 (d-e-cc fat32$c d-e))
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit)))
        (consp path)
        (equal
         (mv-nth
          1
          (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path)))
         0)
        (lofat-file-p file)
        (not (consp (cdr path)))
        (not
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
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))))
              0 nil))
            1))
          (mv-nth 0 (d-e-cc fat32$c d-e))))
        (<=
         (+ 64
            (* 32
               (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
         2097152)
        (not
         (d-e-directory-p
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (<=
         2
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (<=
         (+ 2 (count-of-clusters fat32$c))
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (lofat-regular-file-p file)
        (equal (lofat-file->contents file) "")
        (equal
         (mv-nth
          1
          (update-dir-contents
           fat32$c (d-e-first-cluster d-e)
           (implode
            (nats=>chars
             (insert-d-e
              (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (d-e-set-first-cluster-file-size
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path)))
               0 0))))))
         0))
       (d-e-cc
        (mv-nth
         0
         (update-dir-contents
          fat32$c (d-e-first-cluster d-e)
          (implode
           (nats=>chars
            (insert-d-e
             (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
             (d-e-set-first-cluster-file-size
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                (car path)))
              0 0))))))
        d-e))
      ((and
        (lofat-fs-p fat32$c)
        (d-e-p d-e)
        (d-e-directory-p d-e)
        (fat32-filename-list-p path)
        (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
               0)
        (equal
         (mv-nth 3
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit))
         0)
        (not-intersectp-list
         (mv-nth 0 (d-e-cc fat32$c d-e))
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit)))
        (consp path)
        (equal
         (mv-nth
          1
          (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path)))
         0)
        (not (consp (cdr path)))
        (lofat-file-p file)
        (not
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
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))))
              0 nil))
            1))
          (mv-nth 0 (d-e-cc fat32$c d-e))))
        (<=
         (+ 64
            (* 32
               (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
         2097152)
        (not
         (d-e-directory-p
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (<=
         2
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (<=
         (+ 2 (count-of-clusters fat32$c))
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (not (lofat-directory-file-p file))
        (< 0
           (len (explode (lofat-file->contents file))))
        (<= 1
            (count-free-clusters (effective-fat fat32$c)))
        (equal (lofat-place-file-helper fat32$c d-e path file)
               0)
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
            (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path)))
           (lofat-file->contents file)
           (len (explode (lofat-file->contents file)))
           (nth 0
                (find-n-free-clusters (effective-fat fat32$c)
                                      1))))
         0)
        (equal
         (mv-nth
          1
          (update-dir-contents
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
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
               (car path)))
             (lofat-file->contents file)
             (len (explode (lofat-file->contents file)))
             (nth 0
                  (find-n-free-clusters (effective-fat fat32$c)
                                        1))))
           (d-e-first-cluster d-e)
           (implode
            (nats=>chars
             (insert-d-e
              (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (d-e-set-first-cluster-file-size
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path)))
               (nth 0
                    (find-n-free-clusters (effective-fat fat32$c)
                                          1))
               (len (explode (lofat-file->contents file)))))))))
         0)
        (not (equal (lofat-file->contents file) "")))
       (d-e-cc
        (mv-nth
         0
         (update-dir-contents
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
             (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path)))
            (lofat-file->contents file)
            (len (explode (lofat-file->contents file)))
            (nth 0
                 (find-n-free-clusters (effective-fat fat32$c)
                                       1))))
          (d-e-first-cluster d-e)
          (implode
           (nats=>chars
            (insert-d-e
             (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
             (d-e-set-first-cluster-file-size
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                (car path)))
              (nth 0
                   (find-n-free-clusters (effective-fat fat32$c)
                                         1))
              (len (explode (lofat-file->contents file)))))))))
        d-e))
      ((and
        (not
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
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))))
              0 nil))
            1))
          (mv-nth 0 (d-e-cc fat32$c d-e))))
        (lofat-fs-p fat32$c)
        (d-e-p d-e)
        (d-e-directory-p d-e)
        (fat32-filename-list-p path)
        (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
               0)
        (equal
         (mv-nth 3
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit))
         0)
        (not-intersectp-list
         (mv-nth 0 (d-e-cc fat32$c d-e))
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit)))
        (consp path)
        (equal
         (mv-nth
          1
          (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path)))
         0)
        (<=
         (+ 64
            (* 32
               (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
         2097152)
        (lofat-file-p file)
        (not
         (d-e-directory-p
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (<=
         2
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (<
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path))))
         (+ 2 (count-of-clusters fat32$c)))
        (not (consp (cdr path)))
        (not (equal (lofat-file->contents file) ""))
        (lofat-regular-file-p file)
        (equal (lofat-place-file-helper fat32$c d-e path file)
               0)
        (equal
         (mv-nth
          2
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path))))
              (d-e-file-size
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path)))))))
           (mv-nth
            0
            (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path))))))
               0 nil))
             1))))
         0)
        (equal
         (mv-nth
          1
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))
                (d-e-file-size
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path)))))))
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))))
                 0 nil))
               1))))
           (d-e-first-cluster d-e)
           (implode
            (nats=>chars
             (insert-d-e
              (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (d-e-set-first-cluster-file-size
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path)))))
                  (make-list-ac
                   (len
                    (mv-nth
                     0
                     (d-e-cc
                      fat32$c
                      (mv-nth
                       0
                       (find-d-e (make-d-e-list
                                  (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                                 (car path))))))
                   0 nil))
                 1))
               (len (explode (lofat-file->contents file)))))))))
         0)
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
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path))))))
             0 nil))
           1))
         (mv-nth
          0
          (d-e-cc
           fat32$c
           (mv-nth
            0
            (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path)))))))
       (d-e-cc
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
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path)))))
                  (make-list-ac
                   (len
                    (mv-nth
                     0
                     (d-e-cc
                      fat32$c
                      (mv-nth
                       0
                       (find-d-e (make-d-e-list
                                  (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path))))
               (d-e-file-size
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path)))))))
            (mv-nth
             0
             (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path))))))
                0 nil))
              1))))
          (d-e-first-cluster d-e)
          (implode
           (nats=>chars
            (insert-d-e
             (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
             (d-e-set-first-cluster-file-size
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path))))))
                  0 nil))
                1))
              (len (explode (lofat-file->contents file)))))))))
        d-e))
      ((and
        (lofat-fs-p fat32$c)
        (d-e-p d-e)
        (d-e-directory-p d-e)
        (fat32-filename-list-p path)
        (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
               0)
        (equal
         (mv-nth 3
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit))
         0)
        (not-intersectp-list
         (mv-nth 0 (d-e-cc fat32$c d-e))
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit)))
        (consp path)
        (equal
         (mv-nth
          1
          (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path)))
         0)
        (not
         (d-e-directory-p
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (lofat-file-p file)
        (<=
         2
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (<
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path))))
         (+ 2 (count-of-clusters fat32$c)))
        (not (consp (cdr path)))
        (equal (lofat-file->contents file) "")
        (not
         (equal
          (mv-nth
           1
           (update-dir-contents
            fat32$c (d-e-first-cluster d-e)
            (implode
             (nats=>chars
              (insert-d-e
               (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
               (d-e-set-first-cluster-file-size
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path)))
                0 0))))))
          0))
        (not (equal (lofat-place-file-helper fat32$c d-e path file)
                    0))
        (lofat-regular-file-p file)
        (<=
         (+ 64
            (* 32
               (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
         2097152)
        (equal
         (mv-nth
          1
          (update-dir-contents
           (mv-nth
            0
            (clear-cc
             fat32$c
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                (car path))))
             (d-e-file-size
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                (car path))))))
           (d-e-first-cluster d-e)
           (implode
            (nats=>chars
             (insert-d-e
              (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (d-e-set-first-cluster-file-size
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path)))
               0 0))))))
         0))
       (d-e-cc
        (mv-nth
         0
         (update-dir-contents
          (mv-nth
           0
           (clear-cc
            fat32$c
            (d-e-first-cluster
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
               (car path))))
            (d-e-file-size
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
               (car path))))))
          (d-e-first-cluster d-e)
          (implode
           (nats=>chars
            (insert-d-e
             (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
             (d-e-set-first-cluster-file-size
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                (car path)))
              0 0))))))
        d-e))
      ((and
        (lofat-fs-p fat32$c)
        (d-e-p d-e)
        (d-e-directory-p d-e)
        (fat32-filename-list-p path)
        (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
               0)
        (equal
         (mv-nth 3
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit))
         0)
        (not-intersectp-list
         (mv-nth 0 (d-e-cc fat32$c d-e))
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit)))
        (consp path)
        (equal
         (mv-nth
          1
          (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path)))
         0)
        (not
         (d-e-directory-p
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (lofat-file-p file)
        (<=
         2
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (<
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path))))
         (+ 2 (count-of-clusters fat32$c)))
        (not (consp (cdr path)))
        (equal (lofat-file->contents file) "")
        (not (lofat-directory-file-p file))
        (not
         (equal
          (mv-nth
           1
           (update-dir-contents
            fat32$c (d-e-first-cluster d-e)
            (implode
             (nats=>chars
              (insert-d-e
               (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
               (d-e-set-first-cluster-file-size
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path)))
                0 0))))))
          0))
        (equal (lofat-place-file-helper fat32$c d-e path file)
               0)
        (<=
         (+ 64
            (* 32
               (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
         2097152)
        (equal
         (mv-nth
          1
          (update-dir-contents
           (mv-nth
            0
            (clear-cc
             fat32$c
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                (car path))))
             (d-e-file-size
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                (car path))))))
           (d-e-first-cluster d-e)
           (implode
            (nats=>chars
             (insert-d-e
              (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (d-e-set-first-cluster-file-size
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path)))
               0 0))))))
         0))
       (d-e-cc
        (mv-nth
         0
         (update-dir-contents
          (mv-nth
           0
           (clear-cc
            fat32$c
            (d-e-first-cluster
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
               (car path))))
            (d-e-file-size
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
               (car path))))))
          (d-e-first-cluster d-e)
          (implode
           (nats=>chars
            (insert-d-e
             (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
             (d-e-set-first-cluster-file-size
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                (car path)))
              0 0))))))
        d-e))
      ((and
        (not
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
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))))
              0 nil))
            1))
          (mv-nth 0 (d-e-cc fat32$c d-e))))
        (lofat-fs-p fat32$c)
        (d-e-p d-e)
        (d-e-directory-p d-e)
        (fat32-filename-list-p path)
        (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
               0)
        (equal
         (mv-nth 3
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit))
         0)
        (not-intersectp-list
         (mv-nth 0 (d-e-cc fat32$c d-e))
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit)))
        (consp path)
        (not (lofat-regular-file-p file))
        (<=
         (+ 64
            (* 32
               (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
         2097152)
        (lofat-file-p file)
        (<=
         2
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (d-e-directory-p
         (mv-nth
          0
          (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path))))
        (<
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path))))
         (+ 2 (count-of-clusters fat32$c)))
        (equal (lofat-place-file-helper fat32$c d-e path file)
               0)
        (equal
         (mv-nth
          1
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))
                2097152)))
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
               (car path)))
             (make-empty-subdir-contents
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path))))))
                  0 nil))
                1))
              (d-e-first-cluster d-e))
             0
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
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))))
                 0 nil))
               1))))
           (d-e-first-cluster d-e)
           (implode
            (nats=>chars
             (insert-d-e
              (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (d-e-set-first-cluster-file-size
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path)))))
                  (make-list-ac
                   (len
                    (mv-nth
                     0
                     (d-e-cc
                      fat32$c
                      (mv-nth
                       0
                       (find-d-e (make-d-e-list
                                  (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                                 (car path))))))
                   0 nil))
                 1))
               0))))))
         0)
        (not (consp (cdr path)))
        (not
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
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))))
              0 nil))
            1))
          (mv-nth
           0
           (d-e-cc
            fat32$c
            (mv-nth
             0
             (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path)))))))
        (not (equal (lofat-file->contents file) "")))
       (d-e-cc
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
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path)))))
                  (make-list-ac
                   (len
                    (mv-nth
                     0
                     (d-e-cc
                      fat32$c
                      (mv-nth
                       0
                       (find-d-e (make-d-e-list
                                  (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path))))
               2097152)))
            (mv-nth
             0
             (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path)))
            (make-empty-subdir-contents
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
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))))
                 0 nil))
               1))
             (d-e-first-cluster d-e))
            0
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path))))))
                0 nil))
              1))))
          (d-e-first-cluster d-e)
          (implode
           (nats=>chars
            (insert-d-e
             (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
             (d-e-set-first-cluster-file-size
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path))))))
                  0 nil))
                1))
              0))))))
        d-e))
      ((and
        (not
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
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))))
              0 nil))
            1))
          (mv-nth 0 (d-e-cc fat32$c d-e))))
        (lofat-fs-p fat32$c)
        (d-e-p d-e)
        (d-e-directory-p d-e)
        (fat32-filename-list-p path)
        (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
               0)
        (equal
         (mv-nth 3
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit))
         0)
        (not-intersectp-list
         (mv-nth 0 (d-e-cc fat32$c d-e))
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit)))
        (consp path)
        (<=
         2
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (lofat-file-p file)
        (d-e-directory-p
         (mv-nth
          0
          (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path))))
        (<
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path))))
         (+ 2 (count-of-clusters fat32$c)))
        (not (lofat-regular-file-p file))
        (<=
         (+ 64
            (* 32
               (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
         2097152)
        (equal (lofat-place-file-helper fat32$c d-e path file)
               0)
        (equal
         (mv-nth
          1
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))
                2097152)))
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
               (car path)))
             (make-empty-subdir-contents
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path))))))
                  0 nil))
                1))
              (d-e-first-cluster d-e))
             0
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
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))))
                 0 nil))
               1))))
           (d-e-first-cluster d-e)
           (implode
            (nats=>chars
             (insert-d-e
              (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (d-e-set-first-cluster-file-size
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path)))))
                  (make-list-ac
                   (len
                    (mv-nth
                     0
                     (d-e-cc
                      fat32$c
                      (mv-nth
                       0
                       (find-d-e (make-d-e-list
                                  (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                                 (car path))))))
                   0 nil))
                 1))
               0))))))
         0)
        (not (consp (cdr path)))
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
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path))))))
             0 nil))
           1))
         (mv-nth
          0
          (d-e-cc
           fat32$c
           (mv-nth
            0
            (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))))
        (not (equal (lofat-file->contents file) "")))
       (d-e-cc
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
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path)))))
                  (make-list-ac
                   (len
                    (mv-nth
                     0
                     (d-e-cc
                      fat32$c
                      (mv-nth
                       0
                       (find-d-e (make-d-e-list
                                  (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path))))
               2097152)))
            (mv-nth
             0
             (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path)))
            (make-empty-subdir-contents
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
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))))
                 0 nil))
               1))
             (d-e-first-cluster d-e))
            0
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path))))))
                0 nil))
              1))))
          (d-e-first-cluster d-e)
          (implode
           (nats=>chars
            (insert-d-e
             (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
             (d-e-set-first-cluster-file-size
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path))))))
                  0 nil))
                1))
              0))))))
        d-e))
      ((and
        (lofat-fs-p fat32$c)
        (d-e-p d-e)
        (d-e-directory-p d-e)
        (fat32-filename-list-p path)
        (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
               0)
        (equal
         (mv-nth 3
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit))
         0)
        (not-intersectp-list
         (mv-nth 0 (d-e-cc fat32$c d-e))
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit)))
        (consp path)
        (equal
         (mv-nth
          1
          (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path)))
         0)
        (not
         (d-e-directory-p
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (lofat-file-p file)
        (<
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path))))
         (+ 2 (count-of-clusters fat32$c)))
        (not (consp (cdr path)))
        (<=
         2
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (equal (lofat-file->contents file) "")
        (not (lofat-directory-file-p file))
        (equal
         (mv-nth
          1
          (update-dir-contents
           fat32$c (d-e-first-cluster d-e)
           (implode
            (nats=>chars
             (insert-d-e
              (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (d-e-set-first-cluster-file-size
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path)))
               0 0))))))
         0)
        (not (equal (lofat-place-file-helper fat32$c d-e path file)
                    0))
        (<=
         (+ 64
            (* 32
               (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
         2097152)
        (equal
         (mv-nth
          1
          (update-dir-contents
           (mv-nth
            0
            (clear-cc
             fat32$c
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                (car path))))
             (d-e-file-size
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                (car path))))))
           (d-e-first-cluster d-e)
           (implode
            (nats=>chars
             (insert-d-e
              (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (d-e-set-first-cluster-file-size
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path)))
               0 0))))))
         0))
       (d-e-cc
        (mv-nth
         0
         (update-dir-contents
          (mv-nth
           0
           (clear-cc
            fat32$c
            (d-e-first-cluster
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
               (car path))))
            (d-e-file-size
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
               (car path))))))
          (d-e-first-cluster d-e)
          (implode
           (nats=>chars
            (insert-d-e
             (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
             (d-e-set-first-cluster-file-size
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                (car path)))
              0 0))))))
        d-e))
      ((and
        (lofat-fs-p fat32$c)
        (d-e-p d-e)
        (d-e-directory-p d-e)
        (fat32-filename-list-p path)
        (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
               0)
        (equal
         (mv-nth 3
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit))
         0)
        (not-intersectp-list
         (mv-nth 0 (d-e-cc fat32$c d-e))
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit)))
        (consp path)
        (equal
         (mv-nth
          1
          (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path)))
         0)
        (<=
         (+ 2 (count-of-clusters fat32$c))
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (not (lofat-directory-file-p file))
        (< 0
           (len (explode (lofat-file->contents file))))
        (<= 1
            (count-free-clusters (effective-fat fat32$c)))
        (<=
         (+ 64
            (* 32
               (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
         2097152)
        (equal (lofat-place-file-helper fat32$c d-e path file)
               0)
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
            (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path)))
           (lofat-file->contents file)
           (len (explode (lofat-file->contents file)))
           (nth 0
                (find-n-free-clusters (effective-fat fat32$c)
                                      1))))
         0)
        (equal
         (mv-nth
          1
          (update-dir-contents
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
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
               (car path)))
             (lofat-file->contents file)
             (len (explode (lofat-file->contents file)))
             (nth 0
                  (find-n-free-clusters (effective-fat fat32$c)
                                        1))))
           (d-e-first-cluster d-e)
           (implode
            (nats=>chars
             (insert-d-e
              (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (d-e-set-first-cluster-file-size
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path)))
               (nth 0
                    (find-n-free-clusters (effective-fat fat32$c)
                                          1))
               (len (explode (lofat-file->contents file)))))))))
         0)
        (lofat-file-p file)
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
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path))))))
             0 nil))
           1))
         (mv-nth 0 (d-e-cc fat32$c d-e)))
        (not
         (d-e-directory-p
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (not (consp (cdr path)))
        (<=
         2
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (not (equal (lofat-file->contents file) "")))
       (d-e-cc
        (mv-nth
         0
         (update-dir-contents
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
             (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path)))
            (lofat-file->contents file)
            (len (explode (lofat-file->contents file)))
            (nth 0
                 (find-n-free-clusters (effective-fat fat32$c)
                                       1))))
          (d-e-first-cluster d-e)
          (implode
           (nats=>chars
            (insert-d-e
             (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
             (d-e-set-first-cluster-file-size
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                (car path)))
              (nth 0
                   (find-n-free-clusters (effective-fat fat32$c)
                                         1))
              (len (explode (lofat-file->contents file)))))))))
        d-e))
      ((and
        (not
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
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))))
              0 nil))
            1))
          (mv-nth 0 (d-e-cc fat32$c d-e))))
        (lofat-fs-p fat32$c)
        (d-e-p d-e)
        (d-e-directory-p d-e)
        (fat32-filename-list-p path)
        (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
               0)
        (equal
         (mv-nth 3
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit))
         0)
        (not-intersectp-list
         (mv-nth 0 (d-e-cc fat32$c d-e))
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit)))
        (consp path)
        (not (lofat-regular-file-p file))
        (<=
         (+ 64
            (* 32
               (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
         2097152)
        (equal (lofat-place-file-helper fat32$c d-e path file)
               0)
        (equal
         (mv-nth
          1
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))
                2097152)))
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
               (car path)))
             (make-empty-subdir-contents
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path))))))
                  0 nil))
                1))
              (d-e-first-cluster d-e))
             0
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
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))))
                 0 nil))
               1))))
           (d-e-first-cluster d-e)
           (implode
            (nats=>chars
             (insert-d-e
              (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (d-e-set-first-cluster-file-size
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path)))))
                  (make-list-ac
                   (len
                    (mv-nth
                     0
                     (d-e-cc
                      fat32$c
                      (mv-nth
                       0
                       (find-d-e (make-d-e-list
                                  (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                                 (car path))))))
                   0 nil))
                 1))
               0))))))
         0)
        (lofat-file-p file)
        (d-e-directory-p
         (mv-nth
          0
          (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path))))
        (not (consp (cdr path)))
        (<=
         2
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (<
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path))))
         (+ 2 (count-of-clusters fat32$c)))
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
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path))))))
             0 nil))
           1))
         (mv-nth
          0
          (d-e-cc
           fat32$c
           (mv-nth
            0
            (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))))
        (equal (lofat-file->contents file) ""))
       (d-e-cc
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
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path)))))
                  (make-list-ac
                   (len
                    (mv-nth
                     0
                     (d-e-cc
                      fat32$c
                      (mv-nth
                       0
                       (find-d-e (make-d-e-list
                                  (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path))))
               2097152)))
            (mv-nth
             0
             (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path)))
            (make-empty-subdir-contents
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
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))))
                 0 nil))
               1))
             (d-e-first-cluster d-e))
            0
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path))))))
                0 nil))
              1))))
          (d-e-first-cluster d-e)
          (implode
           (nats=>chars
            (insert-d-e
             (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
             (d-e-set-first-cluster-file-size
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path))))))
                  0 nil))
                1))
              0))))))
        d-e))
      ((and
        (lofat-fs-p fat32$c)
        (d-e-p d-e)
        (d-e-directory-p d-e)
        (fat32-filename-list-p path)
        (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
               0)
        (equal
         (mv-nth 3
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit))
         0)
        (not-intersectp-list
         (mv-nth 0 (d-e-cc fat32$c d-e))
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit)))
        (consp path)
        (equal
         (mv-nth
          1
          (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path)))
         0)
        (not
         (d-e-directory-p
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (lofat-file-p file)
        (not (consp (cdr path)))
        (<=
         2
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (<
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path))))
         (+ 2 (count-of-clusters fat32$c)))
        (equal (lofat-file->contents file) "")
        (not (lofat-directory-file-p file))
        (equal
         (mv-nth
          1
          (update-dir-contents
           fat32$c (d-e-first-cluster d-e)
           (implode
            (nats=>chars
             (insert-d-e
              (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (d-e-set-first-cluster-file-size
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path)))
               0 0))))))
         0)
        (equal (lofat-place-file-helper fat32$c d-e path file)
               0)
        (<=
         (+ 64
            (* 32
               (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
         2097152)
        (equal
         (mv-nth
          1
          (update-dir-contents
           (mv-nth
            0
            (clear-cc
             fat32$c
             (d-e-first-cluster
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                (car path))))
             (d-e-file-size
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                (car path))))))
           (d-e-first-cluster d-e)
           (implode
            (nats=>chars
             (insert-d-e
              (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (d-e-set-first-cluster-file-size
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path)))
               0 0))))))
         0))
       (d-e-cc
        (mv-nth
         0
         (update-dir-contents
          (mv-nth
           0
           (clear-cc
            fat32$c
            (d-e-first-cluster
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
               (car path))))
            (d-e-file-size
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
               (car path))))))
          (d-e-first-cluster d-e)
          (implode
           (nats=>chars
            (insert-d-e
             (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
             (d-e-set-first-cluster-file-size
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                (car path)))
              0 0))))))
        d-e))
      ((and
        (lofat-fs-p fat32$c)
        (d-e-p d-e)
        (d-e-directory-p d-e)
        (fat32-filename-list-p path)
        (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
               0)
        (equal
         (mv-nth 3
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit))
         0)
        (not-intersectp-list
         (mv-nth 0 (d-e-cc fat32$c d-e))
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit)))
        (consp path)
        (equal
         (mv-nth
          1
          (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path)))
         0)
        (not (consp (cdr path)))
        (lofat-file-p file)
        (<
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path))))
         2)
        (not
         (d-e-directory-p
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (not (lofat-directory-file-p file))
        (< 0
           (len (explode (lofat-file->contents file))))
        (<= 1
            (count-free-clusters (effective-fat fat32$c)))
        (<=
         (+ 64
            (* 32
               (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
         2097152)
        (equal (lofat-place-file-helper fat32$c d-e path file)
               0)
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
            (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path)))
           (lofat-file->contents file)
           (len (explode (lofat-file->contents file)))
           (nth 0
                (find-n-free-clusters (effective-fat fat32$c)
                                      1))))
         0)
        (equal
         (mv-nth
          1
          (update-dir-contents
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
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
               (car path)))
             (lofat-file->contents file)
             (len (explode (lofat-file->contents file)))
             (nth 0
                  (find-n-free-clusters (effective-fat fat32$c)
                                        1))))
           (d-e-first-cluster d-e)
           (implode
            (nats=>chars
             (insert-d-e
              (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (d-e-set-first-cluster-file-size
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path)))
               (nth 0
                    (find-n-free-clusters (effective-fat fat32$c)
                                          1))
               (len (explode (lofat-file->contents file)))))))))
         0)
        (<
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path))))
         (+ 2 (count-of-clusters fat32$c)))
        (not
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
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))))
              0 nil))
            1))
          (mv-nth 0 (d-e-cc fat32$c d-e))))
        (not (equal (lofat-file->contents file) "")))
       (d-e-cc
        (mv-nth
         0
         (update-dir-contents
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
             (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path)))
            (lofat-file->contents file)
            (len (explode (lofat-file->contents file)))
            (nth 0
                 (find-n-free-clusters (effective-fat fat32$c)
                                       1))))
          (d-e-first-cluster d-e)
          (implode
           (nats=>chars
            (insert-d-e
             (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
             (d-e-set-first-cluster-file-size
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                (car path)))
              (nth 0
                   (find-n-free-clusters (effective-fat fat32$c)
                                         1))
              (len (explode (lofat-file->contents file)))))))))
        d-e))
      ((and
        (lofat-fs-p fat32$c)
        (d-e-p d-e)
        (d-e-directory-p d-e)
        (fat32-filename-list-p path)
        (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
               0)
        (equal
         (mv-nth 3
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit))
         0)
        (not-intersectp-list
         (mv-nth 0 (d-e-cc fat32$c d-e))
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit)))
        (consp path)
        (equal
         (mv-nth
          1
          (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path)))
         0)
        (<
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path))))
         2)
        (not
         (d-e-directory-p
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (not (lofat-directory-file-p file))
        (< 0
           (len (explode (lofat-file->contents file))))
        (<= 1
            (count-free-clusters (effective-fat fat32$c)))
        (<=
         (+ 64
            (* 32
               (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
         2097152)
        (equal (lofat-place-file-helper fat32$c d-e path file)
               0)
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
            (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path)))
           (lofat-file->contents file)
           (len (explode (lofat-file->contents file)))
           (nth 0
                (find-n-free-clusters (effective-fat fat32$c)
                                      1))))
         0)
        (equal
         (mv-nth
          1
          (update-dir-contents
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
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
               (car path)))
             (lofat-file->contents file)
             (len (explode (lofat-file->contents file)))
             (nth 0
                  (find-n-free-clusters (effective-fat fat32$c)
                                        1))))
           (d-e-first-cluster d-e)
           (implode
            (nats=>chars
             (insert-d-e
              (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (d-e-set-first-cluster-file-size
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path)))
               (nth 0
                    (find-n-free-clusters (effective-fat fat32$c)
                                          1))
               (len (explode (lofat-file->contents file)))))))))
         0)
        (lofat-file-p file)
        (<
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path))))
         (+ 2 (count-of-clusters fat32$c)))
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
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path))))))
             0 nil))
           1))
         (mv-nth 0 (d-e-cc fat32$c d-e)))
        (not (equal (lofat-file->contents file) ""))
        (not (consp (cdr path))))
       (d-e-cc
        (mv-nth
         0
         (update-dir-contents
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
             (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path)))
            (lofat-file->contents file)
            (len (explode (lofat-file->contents file)))
            (nth 0
                 (find-n-free-clusters (effective-fat fat32$c)
                                       1))))
          (d-e-first-cluster d-e)
          (implode
           (nats=>chars
            (insert-d-e
             (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
             (d-e-set-first-cluster-file-size
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                (car path)))
              (nth 0
                   (find-n-free-clusters (effective-fat fat32$c)
                                         1))
              (len (explode (lofat-file->contents file)))))))))
        d-e))
      ((and
        (lofat-fs-p fat32$c)
        (d-e-p d-e)
        (d-e-directory-p d-e)
        (fat32-filename-list-p path)
        (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
               0)
        (equal
         (mv-nth 3
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit))
         0)
        (not-intersectp-list
         (mv-nth 0 (d-e-cc fat32$c d-e))
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit)))
        (consp path)
        (equal
         (mv-nth
          1
          (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path)))
         0)
        (<=
         (+ 2 (count-of-clusters fat32$c))
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (not
         (d-e-directory-p
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (not (lofat-directory-file-p file))
        (<=
         (+ 64
            (* 32
               (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
         2097152)
        (lofat-file-p file)
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
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path))))))
             0 nil))
           1))
         (mv-nth 0 (d-e-cc fat32$c d-e)))
        (equal (lofat-file->contents file) "")
        (not (consp (cdr path)))
        (equal
         (mv-nth
          1
          (update-dir-contents
           fat32$c (d-e-first-cluster d-e)
           (implode
            (nats=>chars
             (insert-d-e
              (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (d-e-set-first-cluster-file-size
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path)))
               0 0))))))
         0)
        (<=
         2
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path))))))
       (d-e-cc
        (mv-nth
         0
         (update-dir-contents
          fat32$c (d-e-first-cluster d-e)
          (implode
           (nats=>chars
            (insert-d-e
             (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
             (d-e-set-first-cluster-file-size
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                (car path)))
              0 0))))))
        d-e))
      ((and
        (not
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
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))))
              0 nil))
            1))
          (mv-nth 0 (d-e-cc fat32$c d-e))))
        (lofat-fs-p fat32$c)
        (d-e-p d-e)
        (d-e-directory-p d-e)
        (fat32-filename-list-p path)
        (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
               0)
        (equal
         (mv-nth 3
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit))
         0)
        (not-intersectp-list
         (mv-nth 0 (d-e-cc fat32$c d-e))
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit)))
        (consp path)
        (<=
         2
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (not (lofat-regular-file-p file))
        (not
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
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))))
              0 nil))
            1))
          (mv-nth
           0
           (d-e-cc
            fat32$c
            (mv-nth
             0
             (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path)))))))
        (equal
         (mv-nth
          1
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))
                2097152)))
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
               (car path)))
             (make-empty-subdir-contents
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path))))))
                  0 nil))
                1))
              (d-e-first-cluster d-e))
             0
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
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))))
                 0 nil))
               1))))
           (d-e-first-cluster d-e)
           (implode
            (nats=>chars
             (insert-d-e
              (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (d-e-set-first-cluster-file-size
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path)))))
                  (make-list-ac
                   (len
                    (mv-nth
                     0
                     (d-e-cc
                      fat32$c
                      (mv-nth
                       0
                       (find-d-e (make-d-e-list
                                  (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                                 (car path))))))
                   0 nil))
                 1))
               0))))))
         0)
        (lofat-file-p file)
        (equal (lofat-file->contents file) "")
        (not (consp (cdr path)))
        (d-e-directory-p
         (mv-nth
          0
          (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path))))
        (<
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path))))
         (+ 2 (count-of-clusters fat32$c)))
        (<=
         (+ 64
            (* 32
               (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
         2097152)
        (equal (lofat-place-file-helper fat32$c d-e path file)
               0))
       (d-e-cc
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
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path)))))
                  (make-list-ac
                   (len
                    (mv-nth
                     0
                     (d-e-cc
                      fat32$c
                      (mv-nth
                       0
                       (find-d-e (make-d-e-list
                                  (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path))))
               2097152)))
            (mv-nth
             0
             (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path)))
            (make-empty-subdir-contents
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
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))))
                 0 nil))
               1))
             (d-e-first-cluster d-e))
            0
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path))))))
                0 nil))
              1))))
          (d-e-first-cluster d-e)
          (implode
           (nats=>chars
            (insert-d-e
             (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
             (d-e-set-first-cluster-file-size
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path))))))
                  0 nil))
                1))
              0))))))
        d-e))
      ((and
        (lofat-fs-p fat32$c)
        (d-e-p d-e)
        (d-e-directory-p d-e)
        (fat32-filename-list-p path)
        (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
               0)
        (equal
         (mv-nth 3
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit))
         0)
        (not-intersectp-list
         (mv-nth 0 (d-e-cc fat32$c d-e))
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit)))
        (consp path)
        (not
         (equal
          (mv-nth
           1
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))
          0))
        (not (lofat-regular-file-p file))
        (<= 1
            (count-free-clusters (effective-fat fat32$c)))
        (<=
         (+ 96
            (* 32
               (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
         2097152)
        (equal (lofat-place-file-helper fat32$c d-e path file)
               0)
        (equal
         (mv-nth
          1
          (update-dir-contents
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
             (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                        t)
             (make-empty-subdir-contents
              (nth 0
                   (find-n-free-clusters (effective-fat fat32$c)
                                         1))
              (d-e-first-cluster d-e))
             0
             (nth 0
                  (find-n-free-clusters (effective-fat fat32$c)
                                        1))))
           (d-e-first-cluster d-e)
           (implode
            (nats=>chars
             (insert-d-e
              (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (d-e-set-first-cluster-file-size
               (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                          t)
               (nth 0
                    (find-n-free-clusters (effective-fat fat32$c)
                                          1))
               0))))))
         0)
        (lofat-file-p file)
        (not (consp (cdr path))))
       (d-e-cc
        (mv-nth
         0
         (update-dir-contents
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
            (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                       t)
            (make-empty-subdir-contents
             (nth 0
                  (find-n-free-clusters (effective-fat fat32$c)
                                        1))
             (d-e-first-cluster d-e))
            0
            (nth 0
                 (find-n-free-clusters (effective-fat fat32$c)
                                       1))))
          (d-e-first-cluster d-e)
          (implode
           (nats=>chars
            (insert-d-e
             (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
             (d-e-set-first-cluster-file-size
              (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                         t)
              (nth 0
                   (find-n-free-clusters (effective-fat fat32$c)
                                         1))
              0))))))
        d-e))
      ((and
        (lofat-fs-p fat32$c)
        (d-e-p d-e)
        (d-e-directory-p d-e)
        (fat32-filename-list-p path)
        (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
               0)
        (equal
         (mv-nth 3
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit))
         0)
        (not-intersectp-list
         (mv-nth 0 (d-e-cc fat32$c d-e))
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit)))
        (consp path)
        (not
         (equal
          (mv-nth
           1
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))
          0))
        (not (lofat-directory-file-p file))
        (< 0
           (len (explode (lofat-file->contents file))))
        (<= 1
            (count-free-clusters (effective-fat fat32$c)))
        (<=
         (+ 96
            (* 32
               (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
         2097152)
        (equal (lofat-place-file-helper fat32$c d-e path file)
               0)
        (equal
         (mv-nth
          1
          (update-dir-contents
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
             (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                        nil)
             (lofat-file->contents file)
             (len (explode (lofat-file->contents file)))
             (nth 0
                  (find-n-free-clusters (effective-fat fat32$c)
                                        1))))
           (d-e-first-cluster d-e)
           (implode
            (nats=>chars
             (insert-d-e
              (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (d-e-set-first-cluster-file-size
               (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                          nil)
               (nth 0
                    (find-n-free-clusters (effective-fat fat32$c)
                                          1))
               (len (explode (lofat-file->contents file)))))))))
         0)
        (lofat-file-p file)
        (not (equal (lofat-file->contents file) ""))
        (not (consp (cdr path)))
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
           (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                      nil)
           (lofat-file->contents file)
           (len (explode (lofat-file->contents file)))
           (nth 0
                (find-n-free-clusters (effective-fat fat32$c)
                                      1))))
         0))
       (d-e-cc
        (mv-nth
         0
         (update-dir-contents
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
            (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                       nil)
            (lofat-file->contents file)
            (len (explode (lofat-file->contents file)))
            (nth 0
                 (find-n-free-clusters (effective-fat fat32$c)
                                       1))))
          (d-e-first-cluster d-e)
          (implode
           (nats=>chars
            (insert-d-e
             (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
             (d-e-set-first-cluster-file-size
              (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                         nil)
              (nth 0
                   (find-n-free-clusters (effective-fat fat32$c)
                                         1))
              (len (explode (lofat-file->contents file)))))))))
        d-e))
      ((and
        (equal (lofat-file->contents file) "")
        (lofat-fs-p fat32$c)
        (d-e-p d-e)
        (d-e-directory-p d-e)
        (fat32-filename-list-p path)
        (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
               0)
        (equal
         (mv-nth 3
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit))
         0)
        (not-intersectp-list
         (mv-nth 0 (d-e-cc fat32$c d-e))
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit)))
        (consp path)
        (equal
         (mv-nth
          1
          (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path)))
         0)
        (not (consp (cdr path)))
        (not
         (d-e-directory-p
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (not (lofat-directory-file-p file))
        (<=
         (+ 64
            (* 32
               (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
         2097152)
        (equal
         (mv-nth
          1
          (update-dir-contents
           fat32$c (d-e-first-cluster d-e)
           (implode
            (nats=>chars
             (insert-d-e
              (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (d-e-set-first-cluster-file-size
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path)))
               0 0))))))
         0)
        (lofat-file-p file)
        (<
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path))))
         2))
       (d-e-cc
        (mv-nth
         0
         (update-dir-contents
          fat32$c (d-e-first-cluster d-e)
          (implode
           (nats=>chars
            (insert-d-e
             (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
             (d-e-set-first-cluster-file-size
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                (car path)))
              0 0))))))
        d-e))
      ((and
        (equal (lofat-file->contents file) "")
        (lofat-fs-p fat32$c)
        (d-e-p d-e)
        (d-e-directory-p d-e)
        (fat32-filename-list-p path)
        (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
               0)
        (equal
         (mv-nth 3
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit))
         0)
        (not-intersectp-list
         (mv-nth 0 (d-e-cc fat32$c d-e))
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit)))
        (consp path)
        (not
         (equal
          (mv-nth
           1
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))
          0))
        (not (lofat-directory-file-p file))
        (<=
         (+ 96
            (* 32
               (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
         2097152)
        (equal
         (mv-nth
          1
          (update-dir-contents
           fat32$c (d-e-first-cluster d-e)
           (implode
            (nats=>chars
             (insert-d-e
              (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (d-e-set-first-cluster-file-size
               (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                          nil)
               0 0))))))
         0)
        (lofat-file-p file)
        (not (consp (cdr path))))
       (d-e-cc
        (mv-nth
         0
         (update-dir-contents
          fat32$c (d-e-first-cluster d-e)
          (implode
           (nats=>chars
            (insert-d-e
             (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
             (d-e-set-first-cluster-file-size
              (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                         nil)
              0 0))))))
        d-e))
      ((and
        (not
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
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))))
              0 nil))
            1))
          (mv-nth 0 (d-e-cc fat32$c d-e))))
        (lofat-fs-p fat32$c)
        (d-e-p d-e)
        (d-e-directory-p d-e)
        (fat32-filename-list-p path)
        (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
               0)
        (equal
         (mv-nth 3
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit))
         0)
        (not-intersectp-list
         (mv-nth 0 (d-e-cc fat32$c d-e))
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  entry-limit)))
        (consp path)
        (equal
         (mv-nth
          1
          (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path)))
         0)
        (<=
         2
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (<
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path))))
         (+ 2 (count-of-clusters fat32$c)))
        (not
         (d-e-directory-p
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))))
        (<=
         (+ 64
            (* 32
               (len (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e))))))
         2097152)
        (equal (lofat-place-file-helper fat32$c d-e path file)
               0)
        (equal
         (mv-nth
          2
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path))))
              (d-e-file-size
               (mv-nth
                0
                (find-d-e
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path)))))))
           (mv-nth
            0
            (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path))))))
               0 nil))
             1))))
         0)
        (equal
         (mv-nth
          1
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))
                (d-e-file-size
                 (mv-nth
                  0
                  (find-d-e
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path)))))))
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))))
                 0 nil))
               1))))
           (d-e-first-cluster d-e)
           (implode
            (nats=>chars
             (insert-d-e
              (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (find-d-e (make-d-e-list
                                  (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                           (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                           (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                             (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))
                   (d-e-file-size
                    (mv-nth
                     0
                     (find-d-e
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path)))))))
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                          (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                         (car path))))))
                    0 nil))
                  1)))))))))
         0)
        (lofat-file-p file)
        (not (consp (cdr path)))
        (not (lofat-directory-file-p file))
        (< 0
           (len (explode (lofat-file->contents file))))
        (not
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
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path))))))
              0 nil))
            1))
          (mv-nth
           0
           (d-e-cc
            fat32$c
            (mv-nth
             0
             (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path))))))))
       (d-e-cc
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
                    (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path)))))
                  (make-list-ac
                   (len
                    (mv-nth
                     0
                     (d-e-cc
                      fat32$c
                      (mv-nth
                       0
                       (find-d-e (make-d-e-list
                                  (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path))))
               (d-e-file-size
                (mv-nth
                 0
                 (find-d-e
                  (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                  (car path)))))))
            (mv-nth
             0
             (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                   (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path))))))
                0 nil))
              1))))
          (d-e-first-cluster d-e)
          (implode
           (nats=>chars
            (insert-d-e
             (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
             (d-e-set-first-cluster-file-size
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
                       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                       (car path))))))
                  0 nil))
                1))
              (len (explode (lofat-file->contents file)))))))))
        d-e))
      (t
       (d-e-cc
        (mv-nth
         0
         (lofat-place-file
          fat32$c
          (mv-nth
           0
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))
          (cdr path)
          file))
        d-e)))))
   :hints
   (("goal"
     :use lemma
     :do-not-induct t
     :in-theory
     (e/d nil
          (lofat-place-file
           (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                     . 5)))))))
