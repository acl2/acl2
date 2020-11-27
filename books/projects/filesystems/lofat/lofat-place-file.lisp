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
                  (:definition true-listp)
                  (:rewrite
                   not-intersectp-list-of-set-difference$-lemma-1)))))

;; Consider changing to remove free variables...
(defthm
  d-e-cc-contents-of-lofat-place-file-coincident-lemma-10
  (implies (<= 2
               (d-e-first-cluster
                (mv-nth 0
                        (find-d-e d-e-list (car path)))))
           (> (len d-e-list) 0))
  :rule-classes :linear)

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
                            lofat-place-file-correctness-1-lemma-16)
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
      (:rewrite d-e-p-when-member-equal-of-d-e-list-p)
      (:rewrite lofat-place-file-correctness-lemma-52)
      (:rewrite not-intersectp-list-when-subsetp-1)
      (:rewrite subsetp-trans2)
      (:rewrite subsetp-trans)
      (:rewrite subsetp-when-atom-left)
      (:rewrite subsetp-when-atom-right)
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
    :in-theory (e/d (nth-when->=-n-len-l)
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
  lofat-place-file-correctness-lemma-7
  (implies
   (and (good-root-d-e-p root-d-e fat32$c)
        (not (intersectp-equal (mv-nth 0 (d-e-cc fat32$c root-d-e))
                               x)))
   (not (intersectp-equal
         x
         (mv-nth '0
                 (fat32-build-index-list (effective-fat fat32$c)
                                         (d-e-first-cluster root-d-e)
                                         '2097152
                                         (cluster-size fat32$c))))))
  :hints (("goal" :in-theory (enable d-e-cc good-root-d-e-p))))

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
                 (car path)))))
    (<
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path))))
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
                     (car path)))))
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
                       (car path))))))
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
              (car path)))))
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
                     (car path)))))
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

(defun
    lofat-place-file
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
       ;; ENOTDIR - can't act on anything that supposedly exists inside a regular file.
       ((when (and (consp (cdr path)) (not (d-e-directory-p d-e))))
        (mv fat32$c *enotdir*))
       (first-cluster (d-e-first-cluster d-e))
       ((when (and (or (< first-cluster 2)
                       (<= (+ 2 (count-of-clusters fat32$c)) first-cluster))
                   (consp (cdr path))))
        (mv fat32$c *eio*))
       ;; Recursion
       ((when (consp(cdr path))) (lofat-place-file fat32$c d-e (cdr path) file))
       ;; After these conditionals, the only remaining possibility is that (cdr path)
       ;; is an atom, which means we need to place a regular file or an empty directory, which
       ;; we have now ensured in the guard.
       (length (if (d-e-directory-p d-e) *ms-max-dir-size* (d-e-file-size d-e)))
       ;; Replacing a directory with a regular file is not permitted.
       ((when (or (and (d-e-directory-p d-e)
                       (lofat-regular-file-p file))
                  (and (not (d-e-directory-p d-e))
                       (lofat-directory-file-p file))))
        (mv fat32$c *enoent*))
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
                                            root-d-e path file))))

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

(defthm natp-of-lofat-place-file
  (natp (mv-nth 1
                (lofat-place-file fat32$c
                                  root-d-e path file)))
  :rule-classes :type-prescription)

;; So this is going to be harder than the same lemma for lofat-remove-file
;; because of two reasons: we're actually placing file contents here (at least
;; some of the time) which requires longer sequences of operations, and we're
;; (potentially) overwriting the contents of one file with the contents of
;; another. The longer sequences mean more things have to be saved with the
;; intention of restoring them once something fails further down the pipeline,
;; and the potential overwriting in the data region means we need to be
;; prepared to reason about reversing the effects of stobj-set-clusters, which
;; is called as part of place-contents.

;; (defthm
;;   lofat-place-file-correctness-2
;;   (implies
;;    (and
;;     (lofat-fs-p fat32$c)
;;     (d-e-p root-d-e)
;;     (>= (d-e-first-cluster root-d-e)
;;         *ms-first-data-cluster*)
;;     (< (d-e-first-cluster root-d-e)
;;        (+ *ms-first-data-cluster*
;;           (count-of-clusters fat32$c)))
;;     (fat32-filename-list-p path)
;;     (lofat-file-p file)
;;     (implies (not (lofat-regular-file-p file))
;;              (unsigned-byte-p
;;               32
;;               (* 32 (len (lofat-file->contents file)))))
;;     (not
;;      (zp (mv-nth 1
;;                  (lofat-place-file
;;                   fat32$c root-d-e path file)))))
;;    (equal (mv-nth 0
;;                   (lofat-place-file
;;                    fat32$c root-d-e path file))
;;           fat32$c))
;;   :hints (("goal" :in-theory (enable update-dir-contents-correctness-1
;;                                      clear-cc-correctness-3
;;                                      place-contents-correctness-1))))

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
           (e/d ()
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
    (e/d (update-dir-contents-correctness-1 nats=>string)
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
           (disable
            (:rewrite
             d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
             . 5)))))

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
      (:rewrite place-contents-expansion-1)
      (:rewrite place-contents-expansion-2)
      (:definition find-d-e)
      (:rewrite explode-of-d-e-filename)
      (:rewrite length-when-stringp)
      (:rewrite len-of-nats=>chars)
      (:rewrite len-of-insert-d-e)
      (:rewrite d-e-fix-when-d-e-p)
      (:rewrite lofat-place-file-correctness-1-lemma-14)
      (:rewrite subsetp-append1)
      (:rewrite lofat-place-file-correctness-lemma-83)
      (:rewrite lofat-place-file-correctness-1-lemma-13)
      (:rewrite lofat-place-file-correctness-lemma-52)
      (:rewrite not-intersectp-list-when-subsetp-1)))
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

;; After trimming hypotheses, the theorem has basically stopped making
;; reference to the directory tree returned by hifat-place-file. I'm not
;; completely sure if that's how it should work, but the theorem prover seems
;; to indicate that the hypotheses are consistent and don't imply falsity.
(defthm
  lofat-place-file-correctness-lemma-3
  (implies
   (and
    (syntaxp (variablep entry-limit))
    (not (zp entry-limit))
    (useful-d-e-list-p d-e-list)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-place-file fat32$c
                                 (mv-nth 0
                                         (find-d-e (cdr d-e-list)
                                                       filename))
                                 path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth 0
                  (lofat-place-file fat32$c
                                    (mv-nth 0
                                            (find-d-e (cdr d-e-list)
                                                          filename))
                                    path file))
          (mv-nth 0
                  (find-d-e (cdr d-e-list)
                                filename)))))
       entry-limit))
     0)
    (equal
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-place-file fat32$c
                                 (mv-nth 0
                                         (find-d-e (cdr d-e-list)
                                                       filename))
                                 path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth 0
                  (lofat-place-file fat32$c
                                    (mv-nth 0
                                            (find-d-e (cdr d-e-list)
                                                          filename))
                                    path file))
          (mv-nth 0
                  (find-d-e (cdr d-e-list)
                                filename)))))
       entry-limit))
     (mv-nth
      0
      (hifat-place-file
       (mv-nth 0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents
                          fat32$c
                          (mv-nth 0
                                  (find-d-e (cdr d-e-list)
                                                filename)))))
                (+ -1 entry-limit)))
       path
       (m1-file
        (d-e-set-first-cluster-file-size
         (mv-nth
          0
          (find-d-e
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents
                     fat32$c
                     (mv-nth 0
                             (find-d-e (cdr d-e-list)
                                           filename)))))
           (car path)))
         0 0)
        ""))))
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                          (+ -1 entry-limit)))
           0)
    (d-e-directory-p (mv-nth 0
                                 (find-d-e (cdr d-e-list)
                                               filename)))
    (not
     (m1-regular-file-p
      (mv-nth
       0
       (hifat-find-file
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents
                    fat32$c
                    (mv-nth 0
                            (find-d-e (cdr d-e-list)
                                          filename)))))
          (+ -1 entry-limit)))
        path)))))
   (equal
    (lofat-to-hifat-helper
     (mv-nth 0
             (lofat-place-file fat32$c
                               (mv-nth 0
                                       (find-d-e (cdr d-e-list)
                                                     filename))
                               path file))
     (make-d-e-list
      (mv-nth
       0
       (d-e-cc-contents
        (mv-nth 0
                (lofat-place-file fat32$c
                                  (mv-nth 0
                                          (find-d-e (cdr d-e-list)
                                                        filename))
                                  path file))
        (mv-nth 0
                (find-d-e (cdr d-e-list)
                              filename)))))
     entry-limit)
    (lofat-to-hifat-helper
     (mv-nth 0
             (lofat-place-file fat32$c
                               (mv-nth 0
                                       (find-d-e (cdr d-e-list)
                                                     filename))
                               path file))
     (make-d-e-list
      (mv-nth
       0
       (d-e-cc-contents
        (mv-nth 0
                (lofat-place-file fat32$c
                                  (mv-nth 0
                                          (find-d-e (cdr d-e-list)
                                                        filename))
                                  path file))
        (mv-nth 0
                (find-d-e (cdr d-e-list)
                              filename)))))
     (+ -1 entry-limit))))
  :hints
  (("goal"
    :use
    (:instance
     lofat-to-hifat-helper-correctness-4
     (entry-limit1 entry-limit)
     (entry-limit2 (+ -1 entry-limit))
     (d-e-list
      (make-d-e-list
       (mv-nth
        0
        (d-e-cc-contents
         (mv-nth 0
                 (lofat-place-file fat32$c
                                   (mv-nth 0
                                           (find-d-e (cdr d-e-list)
                                                         filename))
                                   path file))
         (mv-nth 0
                 (find-d-e (cdr d-e-list)
                               filename))))))
     (fat32$c
      (mv-nth 0
              (lofat-place-file fat32$c
                                (mv-nth 0
                                        (find-d-e (cdr d-e-list)
                                                      filename))
                                path file)))))))

(defthm
  lofat-place-file-correctness-lemma-40
  (implies
   (and
    (d-e-directory-p (mv-nth 0
                                 (find-d-e d-e-list name)))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-place-file fat32$c
                          (mv-nth 0
                                  (find-d-e d-e-list name))
                          path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth
           0
           (lofat-place-file fat32$c
                             (mv-nth 0
                                     (find-d-e d-e-list name))
                             path file))
          (mv-nth 0
                  (find-d-e d-e-list
                                name)))))
       entry-limit))
     0)
    (hifat-equiv
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-place-file fat32$c
                          (mv-nth 0
                                  (find-d-e d-e-list name))
                          path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth
           0
           (lofat-place-file fat32$c
                             (mv-nth 0
                                     (find-d-e d-e-list name))
                             path file))
          (mv-nth 0
                  (find-d-e d-e-list
                                name)))))
       entry-limit))
     (mv-nth
      0
      (hifat-place-file
       (mv-nth 0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents
                          fat32$c
                          (mv-nth 0
                                  (find-d-e d-e-list
                                                name)))))
                (+ -1 entry-limit)))
       path (m1-file d-e nil))))
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c d-e-list
                                          (+ -1 entry-limit)))
           0)
    (useful-d-e-list-p d-e-list))
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-place-file fat32$c
                          (mv-nth 0
                                  (find-d-e d-e-list name))
                          path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth
           0
           (lofat-place-file fat32$c
                             (mv-nth 0
                                     (find-d-e d-e-list name))
                             path file))
          (mv-nth 0
                  (find-d-e d-e-list
                                name)))))
       (+ -1 entry-limit)))
     0)
    (hifat-equiv
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-place-file fat32$c
                          (mv-nth 0
                                  (find-d-e d-e-list name))
                          path file))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth
           0
           (lofat-place-file fat32$c
                             (mv-nth 0
                                     (find-d-e d-e-list name))
                             path file))
          (mv-nth 0
                  (find-d-e d-e-list
                                name)))))
       (+ -1 entry-limit)))
     (mv-nth
      0
      (hifat-place-file
       (mv-nth 0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents
                          fat32$c
                          (mv-nth 0
                                  (find-d-e d-e-list
                                                name)))))
                (+ -1 entry-limit)))
       path (m1-file d-e nil))))))
  :hints
  (("goal"
    :do-not-induct t
    :use
    (:instance
     lofat-to-hifat-helper-correctness-4
     (entry-limit1 entry-limit)
     (entry-limit2 (+ -1 entry-limit))
     (d-e-list
      (make-d-e-list
       (mv-nth
        0
        (d-e-cc-contents
         (mv-nth
          0
          (lofat-place-file fat32$c
                            (mv-nth 0
                                    (find-d-e d-e-list name))
                            path file))
         (mv-nth 0
                 (find-d-e d-e-list
                               name))))))
     (fat32$c
      (mv-nth
       0
       (lofat-place-file fat32$c
                         (mv-nth 0
                                 (find-d-e d-e-list name))
                         path file)))))))

(defthm
  lofat-place-file-correctness-lemma-74
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

  (local (include-book "std/lists/intersectp" :dir :system))

  (local
   (in-theory (e/d (lofat-place-file)
                   ((:rewrite
                     lofat-place-file-correctness-1-lemma-14)
                    (:rewrite intersectp-when-subsetp)
                    (:linear nth-when-d-e-p)
                    (:rewrite
                     d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-3)
                    (:definition find-d-e)
                    (:rewrite append-atom-under-list-equiv)
                    (:rewrite
                     not-intersectp-list-of-lofat-to-hifat-helper)
                    (:rewrite consp-of-make-list-ac)
                    (:linear make-clusters-correctness-2)
                    (:rewrite hifat-to-lofat-inversion-lemma-17)
                    (:rewrite
                     d-e-p-when-member-equal-of-d-e-list-p)
                    (:rewrite
                     d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-11)
                    (:definition place-d-e)
                    (:rewrite
                     lofat-place-file-correctness-lemma-5)
                    (:definition free-index-listp)
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
                    (:definition member-intersectp-equal)
                    (:rewrite
                     lofat-place-file-correctness-lemma-82)))))

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
             (e/d ()
                  ((:rewrite
                    d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                    . 5)))))))

(defthm
  lofat-place-file-correctness-lemma-97
  (implies
   (and
    (lofat-fs-p fat32$c)
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
    (consp (cdr path))
    (d-e-p d-e))
   (no-duplicatesp-equal
    (mv-nth 0
            (d-e-cc (mv-nth 0
                            (lofat-place-file fat32$c d-e path file))
                    d-e))))
  :hints (("goal" :do-not-induct t)))

;; Don't ask.
(defthm
  lofat-place-file-correctness-lemma-98
  (implies
   (and
    (lofat-fs-p fat32$c)
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
    (consp (cdr path))
    (d-e-p (car d-e-list)))
   (not-intersectp-list
    (mv-nth 0
            (d-e-cc (mv-nth 0
                            (lofat-place-file fat32$c (car d-e-list)
                                              path file))
                    (car d-e-list)))
    (mv-nth
     2
     (lofat-to-hifat-helper
      fat32$c (cdr d-e-list)
      (+
       -2 entry-limit
       (-
        (hifat-entry-count
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit))))))))))
  :hints (("goal" :do-not-induct t)))

(defthm
  lofat-place-file-correctness-lemma-102
  (implies
   (and
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
    (consp (cdr path))
    (d-e-p (car d-e-list)))
   (not-intersectp-list
    (mv-nth 0
            (d-e-cc (mv-nth 0
                            (lofat-place-file fat32$c (car d-e-list)
                                              path file))
                    (car d-e-list)))
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
           (+ -1 entry-limit)))))
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
           path)))))))))
  :hints (("goal" :do-not-induct t)))

(defthm
  lofat-place-file-correctness-lemma-135
  (implies
   (and
    (consp d-e-list)
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
    (useful-d-e-list-p d-e-list)
    (consp (cdr path)))
   (not-intersectp-list
    (mv-nth 0
            (d-e-cc (mv-nth 0
                            (lofat-place-file fat32$c (car d-e-list)
                                              path file))
                    (car d-e-list)))
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
  :hints (("goal" :do-not-induct t)))

(defthm
  lofat-place-file-correctness-lemma-110
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
         ((:rewrite lofat-place-file-correctness-1-lemma-13)
          (:rewrite lofat-place-file-correctness-1-lemma-14)
          (:definition member-intersectp-equal)
          (:rewrite lofat-to-hifat-helper-of-clear-cc)
          (:rewrite lofat-place-file-correctness-lemma-56)
          (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
          (:rewrite lofat-place-file-correctness-1-lemma-11)
          (:definition free-index-listp)
          (:rewrite lofat-place-file-correctness-lemma-82)
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

(defthm
  lofat-place-file-correctness-lemma-136
  (implies
   (and
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
    (useful-d-e-list-p d-e-list)
    (not (consp (cdr path))))
   (not-intersectp-list
    (mv-nth 0
            (d-e-cc (mv-nth 0
                            (lofat-place-file fat32$c (car d-e-list)
                                              path file))
                    (car d-e-list)))
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
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (disable
     (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
               . 5)
     (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
     (:rewrite member-of-nth-when-not-intersectp)
     (:rewrite lofat-to-hifat-helper-of-place-contents)
     (:definition member-intersectp-equal)
     (:rewrite get-cc-contents-of-lofat-remove-file-coincident-lemma-5
               . 1)
     (:definition free-index-listp)
     (:rewrite lofat-to-hifat-helper-of-update-fati)
     (:definition len)
     (:rewrite place-contents-expansion-2)
     (:rewrite d-e-cc-under-iff . 3)
     (:rewrite lofat-to-hifat-helper-of-update-dir-contents)
     (:linear find-n-free-clusters-correctness-1)
     (:rewrite not-intersectp-list-of-cons-2)
     (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-4)
     (:rewrite lofat-place-file-correctness-lemma-5)
     (:definition find-d-e)
     (:rewrite lofat-place-file-correctness-1-lemma-14)
     (:definition make-list-ac)
     (:rewrite d-e-p-when-member-equal-of-d-e-list-p)
     (:definition place-d-e)
     (:linear nth-when-d-e-p)
     (:type-prescription d-e-filename)
     (:rewrite d-e-cc-contents-of-lofat-place-file-coincident-lemma-15)
     (:rewrite hifat-to-lofat-inversion-lemma-17)))))

(defthm
  lofat-place-file-correctness-lemma-137
  (implies
   (and
    (equal
     (mv-nth
      1
      (find-d-e
       (make-d-e-list (mv-nth 0
                              (d-e-cc-contents fat32$c (car d-e-list))))
       (car path)))
     0)
    (equal (mv-nth 1
                   (lofat-place-file fat32$c (car d-e-list)
                                     path file))
           0)
    (fat32-filename-list-p path)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0
                              (d-e-cc-contents fat32$c (car d-e-list))))
       (+ -1 entry-limit)))
     0)
    (lofat-directory-file-p file))
   (>
    (+ 2 (count-of-clusters fat32$c))
    (d-e-first-cluster
     (mv-nth
      0
      (find-d-e
       (make-d-e-list (mv-nth 0
                              (d-e-cc-contents fat32$c (car d-e-list))))
       (car path))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (disable
     (:rewrite lofat-place-file-correctness-1-lemma-14)
     (:definition member-intersectp-equal)
     (:rewrite lofat-to-hifat-helper-of-update-dir-contents)
     (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
     (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-4)
     (:rewrite lofat-to-hifat-helper-of-clear-cc)
     (:rewrite d-e-cc-contents-of-lofat-place-file-coincident-lemma-5)
     (:definition no-duplicatesp-equal)
     (:rewrite count-free-clusters-of-set-indices-in-fa-table-1)
     (:rewrite hifat-to-lofat-inversion-lemma-17)
     (:rewrite lofat-place-file-correctness-1-lemma-13)
     (:rewrite lofat-fs-p-of-place-contents)
     (:rewrite d-e-cc-under-iff . 3)
     (:rewrite
      lofat-to-hifat-helper-of-hifat-to-lofat-helper-disjoint-lemma-2)
     (:type-prescription true-listp-of-d-e-cc))))
  :rule-classes :linear)

(defthm
  lofat-place-file-correctness-lemma-154
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
    (consp d-e-list)
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
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
     (mv-nth
      2
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-place-file fat32$c (car d-e-list)
                                 path file))
       (make-d-e-list (mv-nth 0
                              (d-e-cc-contents fat32$c (car d-e-list))))
       entry-limit)))
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
    (consp (cdr path)))
   (not-intersectp-list
    (mv-nth 0
            (d-e-cc (mv-nth 0
                            (lofat-place-file fat32$c (car d-e-list)
                                              path file))
                    (car d-e-list)))
    (mv-nth
     2
     (lofat-to-hifat-helper
      (mv-nth 0
              (lofat-place-file fat32$c (car d-e-list)
                                path file))
      (make-d-e-list (mv-nth 0
                             (d-e-cc-contents fat32$c (car d-e-list))))
      (+ -1 entry-limit)))))
  :hints (("goal" :do-not-induct t)))

(defthm
  lofat-place-file-correctness-lemma-156
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
    (equal (mv-nth 1
                   (lofat-place-file fat32$c (car d-e-list)
                                     path file))
           0)
    (equal
     (mv-nth
      3
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
     0)
    (not
     (member-intersectp-equal
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
             (+ -1 entry-limit))))))))
      (mv-nth
       2
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
        entry-limit))))
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
    (fat32-filename-list-p path)
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
    (lofat-directory-file-p file)
    (not
     (equal
      (mv-nth
       1
       (find-d-e
        (make-d-e-list (mv-nth 0
                               (d-e-cc-contents fat32$c (car d-e-list))))
        (car path)))
      0)))
   (not
    (member-intersectp-equal
     (mv-nth
      2
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
            (+ -1 entry-limit)))))
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
            path))))))))))
  :hints (("goal" :do-not-induct t)))

(defthm
  lofat-place-file-correctness-lemma-164
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
     (not-intersectp-list hifat-entry-count)
     ((:definition subseq)
      (:definition subseq-list)
      (:rewrite lofat-place-file-correctness-1-lemma-14)
      (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
      (:rewrite nfix-when-zp)
      (:definition delete-d-e)
      (:rewrite lofat-place-file-correctness-1-lemma-13)
      (:rewrite nth-of-nats=>chars)
      (:rewrite lofat-place-file-correctness-lemma-3)
      (:rewrite take-of-len-free)
      (:definition place-d-e)
      (:rewrite nats=>chars-of-take)
      (:rewrite lofat-place-file-correctness-lemma-40)
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
      (:rewrite subdir-contents-p-when-zero-length)
      (:rewrite d-e-cc-contents-of-lofat-place-file-disjoint)
      (:rewrite hifat-no-dups-p-of-cdr)
      (:type-prescription binary-append)
      (:type-prescription intersectp-equal)
      (:rewrite d-e-cc-of-lofat-place-file-disjoint)
      (:rewrite intersectp-member . 1)
      (:rewrite intersect-with-subset . 6)
      (:rewrite intersect-with-subset . 5)
      (:rewrite intersect-with-subset . 11)
      (:rewrite intersect-with-subset . 9)
      (:rewrite consp-of-append)
      (:rewrite not-intersectp-list-of-set-difference$-lemma-3)
      (:rewrite member-intersectp-with-subset)
      (:rewrite d-e-cc-under-iff . 3)
      (:rewrite subsetp-when-atom-right)
      (:rewrite subsetp-when-atom-left)
      (:rewrite append-atom-under-list-equiv)
      (:rewrite lofat-place-file-correctness-lemma-5)
      (:rewrite m1-file-of-m1-file-contents-fix-contents-normalize-const)
      (:rewrite m1-file-of-d-e-fix-d-e-normalize-const)
      (:rewrite rationalp-implies-acl2-numberp)
      (:rewrite consp-of-remove-assoc-1)
      (:rewrite member-intersectp-of-set-difference$-1
                . 1)
      (:rewrite hifat-to-lofat-inversion-lemma-23)
      (:rewrite place-contents-expansion-2)
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
      (:rewrite effective-fat-of-clear-cc . 3)
      (:rewrite find-n-free-clusters-when-zp)
      (:rewrite str::consp-of-explode)
      (:rewrite hifat-to-lofat-inversion-lemma-2)
      (:rewrite m1-regular-file-p-correctness-1)
      (:type-prescription m1-file-fix$inline)
      (:rewrite lofat-to-hifat-helper-of-update-dir-contents)
      (:rewrite m1-file->contents$inline-of-m1-file-fix-x-normalize-const)
      (:type-prescription fat32-filename-fix)
      (:rewrite m1-file-p-of-m1-file-fix)
      (:rewrite natp-of-place-contents)
      (:rewrite str::explode-when-not-stringp)
      (:rewrite set-difference$-when-not-intersectp)
      (:linear lofat-remove-file-correctness-1-lemma-27)
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
      (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
      (:definition hifat-entry-count)
      (:definition member-intersectp-equal)
      (:rewrite lofat-to-hifat-helper-of-clear-cc)
      (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-3)
      (:rewrite member-of-nth-when-not-intersectp)
      (:rewrite not-intersectp-list-of-cons-2)
      (:definition len)
      (:definition free-index-listp)
      (:rewrite get-cc-contents-of-lofat-remove-file-coincident-lemma-5
                . 1)
      (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-4)
      (:definition make-list-ac)
      (:linear nth-when-d-e-p)
      (:rewrite d-e-p-when-member-equal-of-d-e-list-p)
      (:rewrite d-e-cc-of-place-contents-coincident-1)
      (:rewrite set-indices-in-fa-table-when-atom)
      (:rewrite not-intersectp-list-of-set-difference$-lemma-2
                . 2)
      (:rewrite not-intersectp-list-of-set-difference$-lemma-2
                . 2)
      (:rewrite hifat-to-lofat-inversion-lemma-17))))))

(defthm
  lofat-place-file-correctness-lemma-173
  (implies
   (and
    (good-root-d-e-p root-d-e fat32$c)
    (equal
     (mv-nth 3
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (+ -1 entry-limit)))
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
     (+ 2 (count-of-clusters fat32$c))))
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
           (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
            (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path)))))
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
    0))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (disable (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                       . 5)))))

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
        nil
        (d-e-cc-of-update-dir-contents-coincident
         (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                   . 5)
         (:rewrite lofat-place-file-correctness-1-lemma-14)
         (:rewrite lofat-to-hifat-helper-of-update-dir-contents)
         (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
         (:rewrite nfix-when-zp)
         (:definition member-intersectp-equal)
         (:rewrite lofat-place-file-correctness-1-lemma-13)
         (:rewrite lofat-to-hifat-helper-of-clear-cc)
         (:definition free-index-listp)
         (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident-lemma-8)
         (:rewrite hifat-to-lofat-inversion-lemma-17)
         (:rewrite d-e-cc-contents-of-update-dir-contents-coincident)
         (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-4)
         (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-3)
         (:rewrite
          lofat-to-hifat-helper-of-hifat-to-lofat-helper-disjoint-lemma-2)
         (:rewrite d-e-cc-under-iff . 3)
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
         (:rewrite lofat-place-file-correctness-lemma-82)
         (:rewrite non-free-index-list-listp-of-effective-fat-of-place-contents)
         (:rewrite lofat-remove-file-correctness-1-lemma-26)
         (:rewrite d-e-cc-of-update-dir-contents)
         (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-11)
         (:rewrite not-intersectp-list-of-set-difference$-lemma-2
                   . 2)
         (:rewrite intersectp-when-subsetp)
         (:rewrite subsetp-when-atom-left)
         (:rewrite subsetp-when-atom-right)
         (:rewrite not-intersectp-list-when-subsetp-1)
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
         (:rewrite lofat-place-file-correctness-1-lemma-14)
         (:rewrite lofat-to-hifat-helper-of-update-dir-contents)
         (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
         (:rewrite nfix-when-zp)
         (:definition member-intersectp-equal)
         (:rewrite lofat-place-file-correctness-1-lemma-13)
         (:rewrite lofat-to-hifat-helper-of-clear-cc)
         (:definition free-index-listp)
         (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident-lemma-8)
         (:rewrite hifat-to-lofat-inversion-lemma-17)
         (:rewrite d-e-cc-contents-of-update-dir-contents-coincident)
         (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-4)
         (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-3)
         (:rewrite
          lofat-to-hifat-helper-of-hifat-to-lofat-helper-disjoint-lemma-2)
         (:rewrite d-e-cc-under-iff . 3)
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
         (:rewrite lofat-place-file-correctness-lemma-82)
         (:rewrite non-free-index-list-listp-of-effective-fat-of-place-contents)
         (:rewrite lofat-remove-file-correctness-1-lemma-26)
         (:rewrite d-e-cc-of-update-dir-contents)
         (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-11)
         (:rewrite not-intersectp-list-of-set-difference$-lemma-2
                   . 2)
         (:rewrite intersectp-when-subsetp)
         (:rewrite subsetp-when-atom-left)
         (:rewrite subsetp-when-atom-right)
         (:rewrite not-intersectp-list-when-subsetp-1)
         (:rewrite not-intersectp-list-of-cons-2)
         (:rewrite subsetp-cons-2)))))))

(defthm
  lofat-place-file-correctness-lemma-176
  (implies
   (and
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
      0)))
   (not-intersectp-list
    (mv-nth 0
            (d-e-cc (mv-nth 0
                            (lofat-place-file fat32$c (car d-e-list)
                                              path file))
                    (car d-e-list)))
    (mv-nth
     2
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
  :hints
  (("goal" :do-not-induct t
    :in-theory (disable d-e-cc-of-update-dir-contents-coincident))))

(defthm
  lofat-place-file-correctness-lemma-107
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
     entry-limit))
   (<=
    (hifat-entry-count
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-place-file fat32$c (car d-e-list)
                                 path file))
       (make-d-e-list (mv-nth 0
                              (d-e-cc-contents fat32$c (car d-e-list))))
       entry-limit)))
    (binary-+ -1 entry-limit)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (disable (:rewrite place-contents-expansion-1)
             (:rewrite len-of-nats=>chars)
             (:rewrite len-of-insert-d-e)
             (:rewrite place-contents-expansion-2)
             (:rewrite len-of-place-d-e)
             (:definition stobj-find-n-free-clusters-correctness-1)
             (:rewrite effective-fat-of-update-fati)
             (:definition find-d-e)
             (:rewrite nth-of-nats=>chars)
             (:linear nth-when-d-e-p)
             (:linear find-n-free-clusters-correctness-7)
             (:rewrite len-of-find-n-free-clusters)
             (:rewrite d-e-fix-when-d-e-p))))
  :rule-classes :linear)

(defthm
  lofat-place-file-correctness-lemma-139
  (implies
   (and
    (equal (lofat-file->contents file) "")
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
    (fat32-filename-list-p path)
    (not
     (equal
      (mv-nth
       1
       (find-d-e
        (make-d-e-list (mv-nth 0
                               (d-e-cc-contents fat32$c (car d-e-list))))
        (car path)))
      0)))
   (not-intersectp-list
    (mv-nth 0
            (d-e-cc (mv-nth 0
                            (lofat-place-file fat32$c (car d-e-list)
                                              path file))
                    (car d-e-list)))
    (mv-nth
     2
     (lofat-to-hifat-helper
      (mv-nth 0
              (lofat-place-file fat32$c (car d-e-list)
                                path file))
      (place-d-e
       (make-d-e-list (mv-nth 0
                              (d-e-cc-contents fat32$c (car d-e-list))))
       (d-e-set-first-cluster-file-size
        (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                   nil)
        0 0))
      (+ -1 entry-limit)))))
  :hints (("goal" :do-not-induct t)))

(defthm
  lofat-place-file-correctness-lemma-186
  (implies
   (and
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
    (fat32-filename-list-p path)
    (not (consp (cdr path)))
    (< 0
       (len (explode (lofat-file->contents file))))
    (not
     (equal
      (mv-nth
       1
       (find-d-e
        (make-d-e-list (mv-nth 0
                               (d-e-cc-contents fat32$c (car d-e-list))))
        (car path)))
      0)))
   (not-intersectp-list
    (mv-nth 0
            (d-e-cc (mv-nth 0
                            (lofat-place-file fat32$c (car d-e-list)
                                              path file))
                    (car d-e-list)))
    (mv-nth
     2
     (lofat-to-hifat-helper
      (mv-nth 0
              (lofat-place-file fat32$c (car d-e-list)
                                path file))
      (place-d-e
       (make-d-e-list (mv-nth 0
                              (d-e-cc-contents fat32$c (car d-e-list))))
       (d-e-set-first-cluster-file-size
        (d-e-install-directory-bit (make-d-e-with-filename (car path))
                                   nil)
        (nth 0
             (find-n-free-clusters (effective-fat fat32$c)
                                   1))
        (len (explode (lofat-file->contents file)))))
      (+ -1 entry-limit)))))
  :hints
  (("goal" :do-not-induct t
    :in-theory (disable d-e-cc-of-update-dir-contents-coincident))))

(defthm
  lofat-place-file-correctness-lemma-187
  (implies
   (and
    (equal
     (mv-nth
      1
      (hifat-place-file
       (mv-nth 0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e2)))
                (+ -1 entry-limit)))
       path
       (m1-file d-e1 (lofat-file->contents file))))
     0)
    (equal
     (mv-nth 3
             (lofat-to-hifat-helper
              (mv-nth 0
                      (lofat-place-file fat32$c d-e2 path file))
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e2)))
              entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c d-e2))
     (mv-nth 2
             (lofat-to-hifat-helper
              (mv-nth 0
                      (lofat-place-file fat32$c d-e2 path file))
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e2)))
              entry-limit)))
    (hifat-equiv
     (mv-nth 0
             (lofat-to-hifat-helper
              (mv-nth 0
                      (lofat-place-file fat32$c d-e2 path file))
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e2)))
              entry-limit))
     (mv-nth
      0
      (hifat-place-file
       (mv-nth 0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e2)))
                (+ -1 entry-limit)))
       path
       (m1-file d-e1 (lofat-file->contents file)))))
    (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e2))
           0)
    (equal
     (mv-nth 3
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e2)))
              (+ -1 entry-limit)))
     0)
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c d-e2))
     (mv-nth 2
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e2)))
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
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e2)))
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
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e2)))
              (+ -1 entry-limit))))))))))
     entry-limit)
    (d-e-p d-e2)
    (consp (cdr path))
    (lofat-fs-p fat32$c))
   (not-intersectp-list
    (mv-nth 0
            (d-e-cc (mv-nth 0
                            (lofat-place-file fat32$c d-e2 path file))
                    d-e2))
    (mv-nth 2
            (lofat-to-hifat-helper
             (mv-nth 0
                     (lofat-place-file fat32$c d-e2 path file))
             (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e2)))
             (+ -1 entry-limit)))))
  :hints (("goal" :do-not-induct t)))

(defthm
  lofat-place-file-correctness-lemma-191
  (implies
   (and
    (lofat-fs-p fat32$c)
    (d-e-directory-p d-e)
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
    (lofat-regular-file-p file)
    (<= (len (make-clusters (lofat-file->contents file)
                            (cluster-size fat32$c)))
        (count-free-clusters (effective-fat fat32$c)))
    (consp path)
    (d-e-p d-e)
    (fat32-filename-list-p path)
    (not (consp (cdr path)))
    (< 0
       (len (explode (lofat-file->contents file))))
    (<
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path))))
     2)
    (equal
     (mv-nth
      1
      (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                (car path)))
     0))
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
        (nth 0
             (find-n-free-clusters (effective-fat fat32$c)
                                   1))
        (len (explode (lofat-file->contents file)))))
      entry-limit))))
  :hints
  (("goal" :do-not-induct t
    :in-theory (disable d-e-cc-of-update-dir-contents-coincident))))

(defthm
  lofat-place-file-correctness-lemma-192
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
       (mv-nth 0
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
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
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (+ -1 entry-limit))))))))))
     entry-limit)
    (d-e-p d-e)
    (fat32-filename-list-p path)
    (not (consp (cdr path)))
    (< 0
       (len (explode (lofat-file->contents file))))
    (<=
     (+ 2 (count-of-clusters fat32$c))
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
        (nth 0
             (find-n-free-clusters (effective-fat fat32$c)
                                   1))
        (len (explode (lofat-file->contents file)))))
      (+ -1 entry-limit)))))
  :hints
  (("goal" :do-not-induct t
    :in-theory (disable d-e-cc-of-update-dir-contents-coincident))))

(encapsulate
  ()

  (local
   (defthm lemma
     (implies (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
                     0)
              (> (len (mv-nth 0 (d-e-cc fat32$c d-e)))
                 0))
     :hints (("goal" :do-not-induct t
              :expand ((len (mv-nth 0 (d-e-cc fat32$c d-e))))))
     :rule-classes :linear))

  (defthm
    lofat-place-file-correctness-lemma-195
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
      (disable
       (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                 . 5)
       (:definition member-intersectp-equal)
       (:rewrite lofat-place-file-correctness-lemma-93)
       (:rewrite lofat-to-hifat-helper-of-update-dir-contents)
       (:rewrite hifat-to-lofat-inversion-lemma-17)
       (:rewrite non-free-index-list-listp-of-effective-fat-of-place-contents)
       (:rewrite nfix-when-zp)
       (:rewrite lofat-place-file-correctness-1-lemma-14)
       (:linear nth-when-d-e-p)
       (:rewrite lofat-place-file-correctness-1-lemma-11)
       (:rewrite lofat-to-hifat-helper-of-place-contents)
       (:rewrite lofat-to-hifat-helper-of-update-fati)
       (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
       (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-3)
       (:definition free-index-listp)
       (:rewrite lofat-to-hifat-helper-of-clear-cc)
       (:rewrite get-cc-contents-of-lofat-remove-file-coincident-lemma-5
                 . 1)
       (:rewrite lofat-place-file-correctness-lemma-82)
       (:rewrite d-e-cc-under-iff . 3)
       (:rewrite d-e-first-cluster-of-d-e-set-first-cluster-file-size)
       (:rewrite fat32-masked-entry-fix-when-fat32-masked-entry-p)
       (:rewrite intersectp-when-subsetp)
       (:rewrite subsetp-when-atom-left)
       (:definition find-d-e)
       (:rewrite lofat-place-file-correctness-lemma-5)
       (:definition position-equal-ac)
       (:rewrite fati-of-clear-cc . 3)
       (:definition make-list-ac)
       (:linear lower-bounded-integer-listp-of-find-n-free-clusters)
       (:rewrite subsetp-when-atom-right)
       (:rewrite d-e-p-when-member-equal-of-d-e-list-p)
       (:linear find-n-free-clusters-correctness-2)
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
                            place-d-e
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
      (:rewrite hifat-no-dups-p-of-cdr)
      (:rewrite lofat-to-hifat-helper-correctness-4)
      (:rewrite nth-of-effective-fat)
      (:rewrite lofat-place-file-correctness-lemma-83)
      (:rewrite lofat-place-file-correctness-1-lemma-11)
      (:rewrite natp-of-car-when-nat-listp)
      (:type-prescription assoc-when-zp-len)
      (:rewrite not-intersectp-list-when-subsetp-1)
      (:rewrite lofat-remove-file-correctness-lemma-31)
      (:rewrite m1-file-fix-when-m1-file-p)
      (:linear lofat-fs-p-correctness-1)
      (:rewrite fat32-filename-fix-when-fat32-filename-p))))))

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
      nat-listp-if-fat32-masked-entry-list-p)
     (:rewrite member-of-append)
     (:definition binary-append)
     (:rewrite member-when-atom)
     (:rewrite put-assoc-equal-without-change . 2)
     (:rewrite lofat-place-file-correctness-lemma-40)
     (:rewrite lofat-place-file-correctness-lemma-3)
     (:rewrite lofat-place-file-correctness-1-lemma-16)
     (:rewrite lofat-place-file-correctness-lemma-82)
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
