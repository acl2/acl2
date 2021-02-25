(in-package "ACL2")

(include-book "../eqfat")
(local (include-book "std/lists/intersectp" :dir :system))

;  lofat-remove-file.lisp                               Mihir Mehta

;; These are some rules from other books which are either interacting badly
;; with the theory I've built up so far, or else causing a lot of unnecessary
;; frames and tries.
(local
 (in-theory (disable take-of-too-many make-list-ac-removal
                     revappend-removal str::hex-digit-char-listp-of-cons
                     loghead logtail nth-when->=-n-len-l
                     integer-listp)))

(local
 (in-theory (disable nth update-nth ceiling floor mod true-listp take member-equal)))

;; get-cc-alt really should be disabled here if it can!
(local
 (in-theory
  (e/d
   (hifat-equiv-of-cons-lemma-4)
   (non-free-index-list-listp-correctness-1
    intersectp-member-when-not-member-intersectp
    no-duplicatesp-of-member
    free-index-list-listp-correctness-1
    consp-of-nthcdr car-of-nthcdr
    count-free-clusters-of-set-indices-in-fa-table-2
    (:rewrite subsetp-implies-subsetp-cdr)
    (:rewrite stringp-when-nonempty-stringp)
    (:rewrite acl2-numberp-of-car-when-acl2-number-listp)
    (:rewrite rationalp-of-car-when-rational-listp)
    (:definition acl2-number-listp)
    (:definition rational-listp)
    (:rewrite true-listp-when-string-list)
    (:rewrite integerp-of-car-when-integer-listp)
    (:definition string-listp)
    (:rewrite subseq-of-length-1)
    (:rewrite assoc-of-car-when-member)
    (:rewrite characterp-nth)
    (:rewrite hifat-file-alist-fix-guard-lemma-1)
    (:rewrite subsetp-member . 2)
    (:rewrite d-e-list-p-of-cdr-when-d-e-list-p)
    (:rewrite intersect-with-subset . 8)
    (:rewrite intersect-with-subset . 1)
    (:rewrite intersect-with-subset . 3)
    (:rewrite intersect-with-subset . 4)
    (:rewrite intersect-with-subset . 2)
    (:rewrite intersect-with-subset . 7)
    (:rewrite intersect-with-subset . 10)
    (:rewrite subsetp-member . 4)
    (:rewrite natp-of-caar-when-file-table-p)
    (:rewrite natp-of-caar-when-fd-table-p)
    (:rewrite
     fat32-filename-p-of-car-when-fat32-filename-list-p)
    (:rewrite free-index-listp-correctness-1)
    (:rewrite consp-of-assoc-of-hifat-file-alist-fix)
    (:linear hifat-entry-count-when-hifat-subsetp)
    (:rewrite true-list-listp-of-cdr-when-true-list-listp)
    (:rewrite not-intersectp-list-when-subsetp-2)
    (:definition subsetp-equal)
    (:rewrite not-intersectp-list-of-set-difference$-lemma-2
              . 1)
    (:rewrite true-list-listp-when-not-consp)
    (:rewrite member-intersectp-is-commutative-lemma-2)
    (:rewrite non-free-index-listp-correctness-5)
    (:rewrite then-subseq-same-2)
    (:rewrite
     count-free-clusters-of-set-indices-in-fa-table-lemma-1)
    (:linear find-n-free-clusters-correctness-1)
    (:rewrite fat32-masked-entry-list-p-when-not-consp)
    (:rewrite fat32-masked-entry-list-p-when-bounded-nat-listp)
    (:rewrite nat-listp-when-unsigned-byte-listp)
    (:rewrite bounded-nat-listp-correctness-1)
    (:rewrite hifat-subsetp-preserves-assoc)
    (:rewrite consp-of-assoc-when-hifat-equiv-lemma-1)
    (:rewrite free-index-list-listp-of-update-nth-lemma-1)
    (:rewrite abs-find-file-correctness-1-lemma-40)
    (:rewrite nth-of-nats=>chars)
    (:rewrite subsetp-of-cons)
    (:rewrite
     lofat-place-file-correctness-lemma-52)
    (:definition binary-append)
    (:rewrite nth-of-effective-fat)
    (:rewrite
     not-intersectp-list-of-set-difference$-lemma-1)
    (:rewrite nats=>chars-of-take)
    (:rewrite intersectp-when-subsetp)
    (:rewrite take-of-len-free)))))

(defthm
  d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-10
  (implies
   (and (lofat-fs-p fat32$c)
        (d-e-p d-e1)
        (not (d-e-directory-p d-e1))
        (d-e-p d-e2)
        (<= *ms-first-data-cluster*
            (d-e-first-cluster d-e1))
        (not (intersectp-equal
              (mv-nth '0
                      (d-e-cc fat32$c d-e1))
              (mv-nth '0
                      (d-e-cc fat32$c d-e2)))))
   (equal (d-e-cc-contents
           (mv-nth 0
                   (clear-cc fat32$c
                             (d-e-first-cluster d-e1)
                             (d-e-file-size d-e1)))
           d-e2)
          (d-e-cc-contents fat32$c d-e2)))
  :hints
  (("goal"
    :in-theory (e/d (d-e-cc)
                    (d-e-cc-contents-of-clear-cc))
    :use (:instance d-e-cc-contents-of-clear-cc
                    (d-e d-e2)
                    (masked-current-cluster (d-e-first-cluster d-e1))
                    (length (d-e-file-size d-e1))))))

(defthm
  d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-9
  (implies
   (and (lofat-fs-p fat32$c)
        (d-e-directory-p d-e1)
        (not (intersectp-equal (mv-nth '0 (d-e-cc fat32$c d-e1))
                               (mv-nth '0 (d-e-cc fat32$c d-e2)))))
   (equal (d-e-cc-contents (mv-nth 0
                                   (clear-cc fat32$c (d-e-first-cluster d-e1)
                                             *ms-max-dir-size*))
                           d-e2)
          (d-e-cc-contents fat32$c d-e2)))
  :hints
  (("goal" :in-theory (e/d (d-e-cc)
                           (d-e-cc-contents-of-clear-cc))
    :use (:instance d-e-cc-contents-of-clear-cc (d-e d-e2)
                    (masked-current-cluster (d-e-first-cluster d-e1))
                    (length *ms-max-dir-size*)))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (make-event
   `(defthm
      lofat-remove-file-correctness-lemma-70
      (implies
       (and
        (d-e-directory-p (car d-e-list))
        (lofat-fs-p fat32$c)
        (fat32-filename-p filename2)
        (subdir-contents-p
         (mv-nth
          0
          (d-e-cc-contents fat32$c (car d-e-list)))))
       (subdir-contents-p
        (implode
         (append
          (nats=>chars
           (clear-d-e
            (string=>nats
             (mv-nth
              0
              (d-e-cc-contents fat32$c (car d-e-list))))
            filename2))
          (make-list-ac
           (+
            (- (len (explode (mv-nth 0
                                     (d-e-cc-contents
                                      fat32$c (car d-e-list))))))
            (*
             (cluster-size fat32$c)
             (len
              (make-clusters
               (nats=>string
                (clear-d-e
                 (string=>nats (mv-nth 0
                                       (d-e-cc-contents
                                        fat32$c (car d-e-list))))
                 filename2))
               (cluster-size fat32$c)))))
           ,(code-char 0) nil)))))
      :hints
      (("goal"
        :use
        (:instance
         (:rewrite lofat-place-file-correctness-lemma-142)
         (n
          (+
           (- (len (explode (mv-nth 0
                                    (d-e-cc-contents
                                     fat32$c (car d-e-list))))))
           (*
            (cluster-size fat32$c)
            (len
             (make-clusters
              (nats=>string
               (clear-d-e
                (string=>nats (mv-nth 0
                                      (d-e-cc-contents
                                       fat32$c (car d-e-list))))
                filename2))
              (cluster-size fat32$c))))))
         (filename filename2)
         (dir-contents
          (string=>nats
           (mv-nth 0
                   (d-e-cc-contents fat32$c
                                    (car d-e-list)))))))))))

(defthm
  d-e-cc-contents-of-lofat-remove-file-coincident-lemma-3
  (implies
   (and
    (d-e-directory-p
     (mv-nth
      0
      (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                (car path))))
    (equal
     (mv-nth 3
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              entry-limit))
     0)
    (<=
     2
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e
        (make-d-e-list
         (mv-nth
          0
          (d-e-cc-contents
           fat32$c
           (mv-nth
            0
            (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))))
        (cadr path)))))
    (<
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e
        (make-d-e-list
         (mv-nth
          0
          (d-e-cc-contents
           fat32$c
           (mv-nth
            0
            (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                      (car path))))))
        (cadr path))))
     (+ 2 (count-of-clusters fat32$c))))
   (equal
    (mv-nth
     '1
     (d-e-cc-contents
      fat32$c
      (mv-nth
       '0
       (find-d-e
        (make-d-e-list
         (mv-nth
          '0
          (d-e-cc-contents
           fat32$c
           (mv-nth
            '0
            (find-d-e (make-d-e-list (mv-nth '0
                                             (d-e-cc-contents fat32$c d-e)))
                      (car path))))))
        (car (cdr path))))))
    0))
  :hints
  (("goal"
    :in-theory
    (disable (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-4))
    :use
    (:instance
     (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-4)
     (filename (cadr path))
     (d-e-list
      (make-d-e-list
       (mv-nth
        0
        (d-e-cc-contents
         fat32$c
         (mv-nth
          0
          (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                    (car path)))))))
     (fat32$c fat32$c)))))

(defthm
  lofat-remove-file-correctness-lemma-71
  (implies
   (and (syntaxp (variablep entry-limit))
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                              (+ -1 entry-limit)))
               0)
        (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) filename1)))
        (useful-d-e-list-p d-e-list))
   (equal
    (put-assoc-equal
     filename1
     (m1-file
      (mv-nth 0 (find-d-e (cdr d-e-list) filename1))
      (remove-assoc-equal
       filename2
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents fat32$c
                            (mv-nth 0
                                    (find-d-e (cdr d-e-list) filename1)))))
         (+ -1 entry-limit)))))
     (mv-nth 0
             (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                    (+ -1 entry-limit))))
    (put-assoc-equal
     filename1
     (m1-file
      (mv-nth 0 (find-d-e (cdr d-e-list) filename1))
      (remove-assoc-equal
       filename2
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents fat32$c
                            (mv-nth 0
                                    (find-d-e (cdr d-e-list) filename1)))))
         entry-limit))))
     (mv-nth 0
             (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                    (+ -1 entry-limit))))))
  :hints
  (("goal"
    :in-theory (enable nfix)
    :use
    (:instance
     (:rewrite lofat-to-hifat-helper-correctness-4)
     (entry-limit1 (- entry-limit 1))
     (entry-limit2 entry-limit)
     (d-e-list
      (make-d-e-list
       (mv-nth
        0
        (d-e-cc-contents fat32$c
                         (mv-nth 0
                                 (find-d-e (cdr d-e-list) filename1))))))
     (fat32$c fat32$c)))))

(defund
  lofat-remove-file-helper
  (fat32$c root-d-e path)
  (declare
   (xargs
    :guard (and (lofat-fs-p fat32$c)
                (d-e-p root-d-e)
                (>= (d-e-first-cluster root-d-e) *ms-first-data-cluster*)
                (< (d-e-first-cluster root-d-e)
                   (+ *ms-first-data-cluster*
                      (count-of-clusters fat32$c)))
                (fat32-filename-list-p path))
    :stobjs fat32$c))
  (b*
      (((unless (consp path))
        (mv fat32$c *enoent*))
       ;; Design choice - calls which ask for the entire root directory to be
       ;; affected will fail.
       (name (mbe :logic (fat32-filename-fix (car path))
                  :exec (car path)))
       ((mv dir-contents &)
        (d-e-cc-contents fat32$c root-d-e))
       (d-e-list
        (make-d-e-list dir-contents))
       ((mv d-e error-code)
        (find-d-e d-e-list name))
       ;; If it's not there, it can't be removed
       ((unless (equal error-code 0))
        (mv fat32$c *enoent*))
       ;; ENOTDIR - can't delete anything that supposedly exists inside a
       ;; regular file.
       ((when (and (consp (cdr path)) (not (d-e-directory-p d-e))))
        (mv fat32$c *enotdir*))
       (first-cluster (d-e-first-cluster d-e))
       ((when
            (and
             (or (< first-cluster *ms-first-data-cluster*)
                 (<= (+ *ms-first-data-cluster*
                        (count-of-clusters fat32$c))
                     first-cluster))
             (consp (cdr path))))
        (mv fat32$c *eio*))
       ;; After these conditionals, the only remaining possibility is that
       ;; (cdr path) is an atom, which means we need to delete a file or
       ;; a(n empty) directory.
       ((mv fat32$c error-code)
        (update-dir-contents fat32$c
                             (d-e-first-cluster root-d-e)
                             (nats=>string (clear-d-e (string=>nats
                                                       dir-contents)
                                                      name))))
       ((unless (equal error-code 0))
        (mv fat32$c error-code))
       (length (if (d-e-directory-p d-e)
                   *ms-max-dir-size*
                 (d-e-file-size d-e)))
       ((mv fat32$c &)
        (if
            (or (< first-cluster *ms-first-data-cluster*)
                (<= (+ *ms-first-data-cluster*
                       (count-of-clusters fat32$c))
                    first-cluster))
            (mv fat32$c 0)
          (clear-cc
           fat32$c
           first-cluster
           length))))
    (mv fat32$c 0)))

(defund
  lofat-remove-file
  (fat32$c root-d-e path)
  (declare
   (xargs :guard (and (lofat-fs-p fat32$c)
                      (d-e-p root-d-e)
                      (>= (d-e-first-cluster root-d-e)
                          *ms-first-data-cluster*)
                      (< (d-e-first-cluster root-d-e)
                         (+ *ms-first-data-cluster*
                            (count-of-clusters fat32$c)))
                      (fat32-filename-list-p path))
          :measure (len path)
          :stobjs fat32$c))
  (b* (((mv root-dir-contents &)
        (d-e-cc-contents fat32$c root-d-e))
       ((unless (consp path))
        (lofat-remove-file-helper fat32$c root-d-e path))
       ((mv d-e error-code)
        (find-d-e (make-d-e-list root-dir-contents)
                  (fat32-filename-fix (car path))))
       ((when (and (zp error-code)
                   (consp (cdr path))
                   (d-e-directory-p d-e)
                   (<= *ms-first-data-cluster* (d-e-first-cluster d-e))
                   (< (d-e-first-cluster d-e)
                      (+ *ms-first-data-cluster* (count-of-clusters fat32$c)))))
        (lofat-remove-file fat32$c d-e (cdr path))))
    (lofat-remove-file-helper fat32$c root-d-e path)))

(encapsulate
  ()

  ;; This was the original definition of lofat-remove-file. We're renaming it
  ;; to lofat-remove-file-alt so that we can name the refactored version
  ;; lofat-remove-file and have that name in all our lemmas.
  ;;
  ;; We're going to have to add a weird stipulation here about the length of a
  ;; directory file's contents being more than 0 (which is true, because dot and
  ;; dotdot entries have to be everywhere other than the root.)
  (local
   (defun
       lofat-remove-file-alt
       (fat32$c root-d-e path)
     (declare
      (xargs
       :guard (and (lofat-fs-p fat32$c)
                   (d-e-p root-d-e)
                   (>= (d-e-first-cluster root-d-e) *ms-first-data-cluster*)
                   (< (d-e-first-cluster root-d-e)
                      (+ *ms-first-data-cluster*
                         (count-of-clusters fat32$c)))
                   (fat32-filename-list-p path))
       :measure (len path)
       :stobjs fat32$c))
     (b*
         (((unless (consp path))
           (mv fat32$c *enoent*))
          ;; Design choice - calls which ask for the entire root directory to be
          ;; affected will fail.
          (name (mbe :logic (fat32-filename-fix (car path))
                     :exec (car path)))
          ((mv dir-contents &)
           (d-e-cc-contents fat32$c root-d-e))
          (d-e-list
           (make-d-e-list dir-contents))
          ((mv d-e error-code)
           (find-d-e d-e-list name))
          ;; If it's not there, it can't be removed
          ((unless (equal error-code 0))
           (mv fat32$c *enoent*))
          ;; ENOTDIR - can't delete anything that supposedly exists inside a
          ;; regular file.
          ((when (and (consp (cdr path)) (not (d-e-directory-p d-e))))
           (mv fat32$c *enotdir*))
          (first-cluster (d-e-first-cluster d-e))
          ((when
               (and
                (or (< first-cluster *ms-first-data-cluster*)
                    (<= (+ *ms-first-data-cluster*
                           (count-of-clusters fat32$c))
                        first-cluster))
                (consp (cdr path))))
           (mv fat32$c *eio*))
          ((when (consp (cdr path)))
           ;; Recursion
           (lofat-remove-file-alt
            fat32$c
            d-e
            (cdr path)))
          ;; After these conditionals, the only remaining possibility is that
          ;; (cdr path) is an atom, which means we need to delete a file or
          ;; a(n empty) directory.
          ((mv fat32$c error-code)
           (update-dir-contents fat32$c
                                (d-e-first-cluster root-d-e)
                                (nats=>string (clear-d-e (string=>nats
                                                          dir-contents)
                                                         name))))
          ((unless (equal error-code 0))
           (mv fat32$c error-code))
          (length (if (d-e-directory-p d-e)
                      *ms-max-dir-size*
                    (d-e-file-size d-e)))
          ((mv fat32$c &)
           (if
               (or (< first-cluster *ms-first-data-cluster*)
                   (<= (+ *ms-first-data-cluster*
                          (count-of-clusters fat32$c))
                       first-cluster))
               (mv fat32$c 0)
             (clear-cc
              fat32$c
              first-cluster
              length))))
       (mv fat32$c 0))))

  (thm
   (equal (lofat-remove-file-alt fat32$c root-d-e path)
          (lofat-remove-file fat32$c root-d-e path))
   :hints (("goal" :in-theory (enable lofat-remove-file-alt lofat-remove-file
                                      lofat-remove-file-helper)))))

(defthm
  max-entry-count-of-lofat-remove-file-helper
  (equal (max-entry-count (mv-nth 0
                                  (lofat-remove-file-helper fat32$c d-e path)))
         (max-entry-count fat32$c))
  :hints (("goal" :in-theory (enable lofat-remove-file-helper))))

(defthm
  max-entry-count-of-lofat-remove-file
  (equal (max-entry-count (mv-nth 0
                                  (lofat-remove-file fat32$c d-e path)))
         (max-entry-count fat32$c))
  :hints (("goal" :in-theory (enable lofat-remove-file))))

(defthm
  pseudo-root-d-e-of-lofat-remove-file-helper
  (equal
   (pseudo-root-d-e
    (mv-nth
     0
     (lofat-remove-file-helper fat32$c root-d-e path)))
   (pseudo-root-d-e fat32$c))
  :hints (("Goal" :in-theory (enable lofat-remove-file-helper))))

(defthm
  pseudo-root-d-e-of-lofat-remove-file
  (equal
   (pseudo-root-d-e
    (mv-nth
     0
     (lofat-remove-file fat32$c root-d-e path)))
   (pseudo-root-d-e fat32$c))
  :hints (("Goal" :in-theory (enable lofat-remove-file))))

(defthm
  count-of-clusters-of-lofat-remove-file-helper
  (equal (count-of-clusters
          (mv-nth 0
                  (lofat-remove-file-helper fat32$c rootclus path)))
         (count-of-clusters fat32$c))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

(defthm
  count-of-clusters-of-lofat-remove-file
  (equal
   (count-of-clusters (mv-nth 0
                              (lofat-remove-file fat32$c rootclus path)))
   (count-of-clusters fat32$c))
  :hints (("goal" :in-theory (enable lofat-remove-file))))

(defthm lofat-remove-file-correctness-3
  (natp (mv-nth 1
                (lofat-remove-file fat32$c root-d-e path)))
  :hints (("goal" :in-theory (enable lofat-remove-file
                                     lofat-remove-file-helper)))
  :rule-classes :type-prescription)

(encapsulate
  ()

  (local
   (in-theory
    (enable hifat-remove-file
            (:rewrite lofat-to-hifat-inversion-lemma-4)
            lofat-to-hifat-inversion-lemma-15
            lofat-remove-file-helper)))

  (defthm
    lofat-remove-file-correctness-lemma-35
    (implies
     (and
      (good-root-d-e-p root-d-e fat32$c)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         entry-limit))
       0)
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c root-d-e))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         entry-limit))))
     (equal
      (mv-nth
       3
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-remove-file-helper fat32$c root-d-e path))
        (make-d-e-list
         (mv-nth
          0
          (d-e-cc-contents
           (mv-nth
            0
            (lofat-remove-file-helper fat32$c root-d-e path))
           root-d-e)))
        entry-limit))
      0)))

  (defthm
    lofat-remove-file-correctness-lemma-67
    (implies
     (and
      (good-root-d-e-p root-d-e fat32$c)
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         entry-limit))
       0)
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c root-d-e))
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         entry-limit)))
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         entry-limit))))
     (not-intersectp-list
      x
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-remove-file-helper fat32$c root-d-e path))
        (make-d-e-list
         (mv-nth
          0
          (d-e-cc-contents
           (mv-nth
            0
            (lofat-remove-file-helper fat32$c root-d-e path))
           root-d-e)))
        entry-limit))))))

(defthm
  d-e-cc-of-lofat-remove-file-disjoint-lemma-4
  (implies
   (and
    (lofat-fs-p fat32$c)
    (<= 2 (d-e-first-cluster root-d-e))
    (< (d-e-first-cluster root-d-e)
       (+ 2 (count-of-clusters fat32$c)))
    (d-e-p root-d-e)
    (d-e-directory-p root-d-e)
    (d-e-p d-e)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c d-e))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit)))
    (not (intersectp-equal (mv-nth 0 (d-e-cc fat32$c d-e))
                           (mv-nth 0 (d-e-cc fat32$c root-d-e))))
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c root-d-e))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit)))
    (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
           0))
   (equal (d-e-cc (mv-nth 0
                          (lofat-remove-file-helper fat32$c root-d-e path))
                  d-e)
          (d-e-cc fat32$c d-e)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

(defthm
  d-e-cc-of-lofat-remove-file-disjoint
  (implies
   (and
    (lofat-fs-p fat32$c)
    (<= *ms-first-data-cluster*
        (d-e-first-cluster root-d-e))
    (< (d-e-first-cluster root-d-e)
       (+ *ms-first-data-cluster*
          (count-of-clusters fat32$c)))
    (d-e-p root-d-e)
    (d-e-directory-p root-d-e)
    (d-e-p d-e)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c d-e))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit)))
    (not (intersectp-equal (mv-nth 0 (d-e-cc fat32$c root-d-e))
                           (mv-nth 0 (d-e-cc fat32$c d-e))))
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c root-d-e))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit)))
    (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
           0))
   (equal (d-e-cc (mv-nth 0
                          (lofat-remove-file fat32$c root-d-e path))
                  d-e)
          (d-e-cc fat32$c d-e)))
  :hints (("goal" :induct (lofat-remove-file fat32$c root-d-e path)
           :in-theory (enable lofat-remove-file))))

(defthm
  d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-8
  (implies
   (and
    (lofat-fs-p fat32$c)
    (<= 2 (d-e-first-cluster root-d-e))
    (< (d-e-first-cluster root-d-e)
       (+ 2 (count-of-clusters fat32$c)))
    (d-e-p root-d-e)
    (d-e-directory-p root-d-e)
    (d-e-p d-e)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c d-e))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit)))
    (not (intersectp-equal (mv-nth 0 (d-e-cc fat32$c d-e))
                           (mv-nth 0 (d-e-cc fat32$c root-d-e))))
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c root-d-e))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit)))
    (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
           0))
   (equal (d-e-cc-contents
           (mv-nth 0
                   (lofat-remove-file-helper fat32$c root-d-e path))
           d-e)
          (d-e-cc-contents fat32$c d-e)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

(defthm
  d-e-cc-contents-of-lofat-remove-file-disjoint
  (implies
   (and
    (lofat-fs-p fat32$c)
    (<= *ms-first-data-cluster*
        (d-e-first-cluster root-d-e))
    (< (d-e-first-cluster root-d-e)
       (+ *ms-first-data-cluster*
          (count-of-clusters fat32$c)))
    (d-e-p root-d-e)
    (d-e-directory-p root-d-e)
    (d-e-p d-e)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c d-e))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit)))
    (not (intersectp-equal (mv-nth 0 (d-e-cc fat32$c root-d-e))
                           (mv-nth 0 (d-e-cc fat32$c d-e))))
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c root-d-e))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit)))
    (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
           0))
   (equal
    (d-e-cc-contents (mv-nth 0
                             (lofat-remove-file fat32$c root-d-e path))
                     d-e)
    (d-e-cc-contents fat32$c d-e)))
  :hints (("goal" :in-theory (enable lofat-remove-file)
           :induct (lofat-remove-file fat32$c root-d-e path))))

(defthm
  lofat-remove-file-correctness-lemma-16
  (implies
   (and
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
           0)
    (lofat-fs-p fat32$c)
    (<= 2
        (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name))))
    (< (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name)))
       (+ 2 (count-of-clusters fat32$c)))
    (d-e-p d-e)
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
    (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
           0)
    (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))
    (useful-d-e-list-p d-e-list))
   (equal
    (d-e-cc-contents
     (mv-nth 0
             (lofat-remove-file fat32$c
                                (mv-nth 0 (find-d-e d-e-list name))
                                path))
     d-e)
    (d-e-cc-contents fat32$c d-e)))
  :hints
  (("goal"
    :in-theory (disable d-e-cc-contents-of-lofat-remove-file-disjoint
                        lofat-find-file-correctness-1-lemma-6)
    :use ((:instance d-e-cc-contents-of-lofat-remove-file-disjoint
                     (root-d-e (mv-nth 0 (find-d-e d-e-list name))))
          lofat-find-file-correctness-1-lemma-6))))

(defthm
  d-e-cc-contents-of-lofat-remove-file-coincident-lemma-10
  (> (mv-nth 1
             (lofat-remove-file-helper fat32$c d-e nil))
     0)
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper)))
  :rule-classes :linear)

(defthm
  d-e-cc-contents-of-lofat-remove-file-coincident-lemma-11
  (implies
   (and
    (lofat-fs-p fat32$c)
    (d-e-p d-e)
    (d-e-directory-p d-e)
    (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
           0)
    (not (equal (mv-nth 1
                        (lofat-remove-file-helper fat32$c d-e path))
                0)))
   (equal
    (d-e-cc-contents (mv-nth 0
                             (lofat-remove-file-helper fat32$c d-e path))
                     d-e)
    (d-e-cc-contents fat32$c d-e)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

(defthm
  d-e-cc-contents-of-lofat-remove-file-coincident-lemma-12
  (implies
   (and
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
    (equal (mv-nth 1
                   (lofat-remove-file-helper fat32$c d-e path))
           0))
   (equal
    (d-e-cc-contents (mv-nth 0
                             (lofat-remove-file-helper fat32$c d-e path))
                     d-e)
    (mv
     (implode
      (append
       (nats=>chars
        (clear-d-e (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                   (car path)))
       (make-list-ac
        (+
         (- (len (explode (mv-nth 0 (d-e-cc-contents fat32$c d-e)))))
         (*
          (cluster-size fat32$c)
          (len
           (make-clusters
            (nats=>string
             (clear-d-e
              (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              (car path)))
            (cluster-size fat32$c)))))
        (code-char 0) nil)))
     0)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

(defthm
  d-e-cc-contents-of-lofat-remove-file-coincident-lemma-13
  (implies
   (and
    (fat32-filename-list-p path)
    (consp (cdr path))
    (<=
     (+ 2 (count-of-clusters fat32$c))
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path))))))
   (equal
    (d-e-cc-contents (mv-nth 0
                             (lofat-remove-file-helper fat32$c d-e path))
                     d-e)
    (d-e-cc-contents fat32$c d-e)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

(defthm
  d-e-cc-contents-of-lofat-remove-file-coincident-lemma-5
  (implies
   (and
    (fat32-filename-list-p path)
    (consp (cdr path))
    (not
     (d-e-directory-p
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path))))))
   (equal
    (d-e-cc-contents (mv-nth 0
                             (lofat-remove-file-helper fat32$c d-e path))
                     d-e)
    (d-e-cc-contents fat32$c d-e)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

(defthm
  d-e-cc-contents-of-lofat-remove-file-coincident-lemma-14
  (implies
   (and
    (fat32-filename-list-p path)
    (consp (cdr path))
    (<
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path))))
     2))
   (equal
    (d-e-cc-contents (mv-nth 0
                             (lofat-remove-file-helper fat32$c d-e path))
                     d-e)
    (d-e-cc-contents fat32$c d-e)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

;; Reformulated in a way that avoids case splits.
(defthm
  d-e-cc-contents-of-lofat-remove-file-coincident
  (implies
   (and
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
              entry-limit))))
   (and
    (implies
     (or (not (equal (mv-nth 1
                             (lofat-remove-file fat32$c d-e path))
                     0))
         (consp (cdr path)))
     (equal
      (d-e-cc-contents (mv-nth 0
                               (lofat-remove-file fat32$c d-e path))
                       d-e)
      (d-e-cc-contents fat32$c d-e)))
    (implies
     (and (equal (mv-nth 1
                         (lofat-remove-file fat32$c d-e path))
                 0)
          (not
           (consp (cdr path))))
     (equal
      (d-e-cc-contents (mv-nth 0
                               (lofat-remove-file fat32$c d-e path))
                       d-e)
      (mv
       (implode
        (append
         (nats=>chars
          (clear-d-e (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                     (car path)))
         (make-list-ac
          (+
           (- (len (explode (mv-nth 0 (d-e-cc-contents fat32$c d-e)))))
           (*
            (cluster-size fat32$c)
            (len
             (make-clusters
              (nats=>string
               (clear-d-e
                (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                (car path)))
              (cluster-size fat32$c)))))
          (code-char 0)
          nil)))
       0)))))
  :hints (("goal" :do-not-induct t
           :expand (lofat-remove-file fat32$c d-e path))))

(defthm
  lofat-fs-p-of-lofat-remove-file-lemma-2
  (implies
   (and
    (<
     0
     (mv-nth
      1
      (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                (fat32-filename-fix (car path)))))
    (lofat-fs-p fat32$c))
   (lofat-fs-p (mv-nth 0
                       (lofat-remove-file-helper fat32$c root-d-e path))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

(defthm
  lofat-fs-p-of-lofat-remove-file-lemma-2
  (implies
   (and
    (<
     0
     (mv-nth
      1
      (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                (fat32-filename-fix (car path)))))
    (lofat-fs-p fat32$c))
   (lofat-fs-p (mv-nth 0
                       (lofat-remove-file-helper fat32$c root-d-e path))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

(defthm
  lofat-fs-p-of-lofat-remove-file-lemma-4
  (implies
   (and (lofat-fs-p fat32$c)
        (d-e-p root-d-e)
        (<= 2 (d-e-first-cluster root-d-e))
        (< (d-e-first-cluster root-d-e)
           (+ 2 (count-of-clusters fat32$c))))
   (lofat-fs-p (mv-nth 0
                       (lofat-remove-file-helper fat32$c root-d-e path))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

(defthm
  lofat-fs-p-of-lofat-remove-file
  (implies
   (and (lofat-fs-p fat32$c)
        (d-e-p root-d-e)
        (>= (d-e-first-cluster root-d-e)
            *ms-first-data-cluster*)
        (< (d-e-first-cluster root-d-e)
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32$c))))
   (lofat-fs-p (mv-nth 0
                       (lofat-remove-file fat32$c root-d-e path))))
  :hints (("goal" :in-theory (enable lofat-remove-file))))

(defthm
  lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-7
  (implies
   (and
    (useful-d-e-list-p d-e-list)
    (lofat-fs-p fat32$c)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
           0)
    (d-e-p root-d-e)
    (d-e-directory-p root-d-e)
    (<= 2 (d-e-first-cluster root-d-e))
    (< (d-e-first-cluster root-d-e)
       (+ 2 (count-of-clusters fat32$c)))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit2))
     0)
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c root-d-e))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit2)))
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c root-d-e))
     (mv-nth 2
             (lofat-to-hifat-helper fat32$c d-e-list entry-limit1)))
    (not
     (member-intersectp-equal
      (mv-nth 2
              (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
      (mv-nth
       2
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
        entry-limit2)))))
   (equal (lofat-to-hifat-helper
           (mv-nth 0
                   (lofat-remove-file-helper fat32$c root-d-e path))
           d-e-list entry-limit1)
          (lofat-to-hifat-helper fat32$c d-e-list entry-limit1)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

(defthm
  lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-9
  (implies
   (and
    (<
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 (fat32-filename-fix (car path)))))
     2)
    (useful-d-e-list-p d-e-list)
    (lofat-fs-p fat32$c)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
           0)
    (d-e-p root-d-e)
    (d-e-directory-p root-d-e)
    (<= 2 (d-e-first-cluster root-d-e))
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c root-d-e))
     (mv-nth 2
             (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))))
   (equal (lofat-to-hifat-helper
           (mv-nth 0
                   (lofat-remove-file-helper fat32$c root-d-e path))
           d-e-list entry-limit1)
          (lofat-to-hifat-helper fat32$c d-e-list entry-limit1)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

(defthm
  lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-5
  (implies
   (and
    (<=
     (+ 2 (count-of-clusters fat32$c))
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 (fat32-filename-fix (car path))))))
    (useful-d-e-list-p d-e-list)
    (lofat-fs-p fat32$c)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
           0)
    (d-e-p root-d-e)
    (d-e-directory-p root-d-e)
    (<= 2 (d-e-first-cluster root-d-e))
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c root-d-e))
     (mv-nth 2
             (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))))
   (equal (lofat-to-hifat-helper
           (mv-nth 0
                   (lofat-remove-file-helper fat32$c root-d-e path))
           d-e-list entry-limit1)
          (lofat-to-hifat-helper fat32$c d-e-list entry-limit1)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

;; It looks like this theorem needs to have its hypothesis about
;; (mv-nth 3 (lofat-to-hifat-helper ...)) because it relies on
;; get-cc-contents-of-lofat-remove-file-coincident-lemma-5.
(defthm
  lofat-to-hifat-helper-of-lofat-remove-file-disjoint
  (implies
   (and
    (useful-d-e-list-p d-e-list)
    (lofat-fs-p fat32$c)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
           0)
    (d-e-p root-d-e)
    (d-e-directory-p root-d-e)
    (>= (d-e-first-cluster root-d-e)
        *ms-first-data-cluster*)
    (< (d-e-first-cluster root-d-e)
       (+ *ms-first-data-cluster*
          (count-of-clusters fat32$c)))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit2))
     0)
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c root-d-e))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit2)))
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c root-d-e))
     (mv-nth 2
             (lofat-to-hifat-helper fat32$c d-e-list entry-limit1)))
    (not
     (member-intersectp-equal
      (mv-nth
       2
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
        entry-limit2))
      (mv-nth 2
              (lofat-to-hifat-helper fat32$c d-e-list entry-limit1)))))
   (equal (lofat-to-hifat-helper
           (mv-nth 0
                   (lofat-remove-file fat32$c root-d-e path))
           d-e-list entry-limit1)
          (lofat-to-hifat-helper fat32$c d-e-list entry-limit1)))
  :hints (("goal" :induct (lofat-remove-file fat32$c root-d-e path)
           :in-theory (enable lofat-remove-file))))

(defthm
  lofat-remove-file-correctness-lemma-18
  (implies
   (and
    (<
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path))))
     2)
    (consp (cdr path))
    (fat32-filename-list-p path))
   (equal (d-e-cc (mv-nth 0
                          (lofat-remove-file-helper fat32$c d-e path))
                  d-e)
          (d-e-cc fat32$c d-e)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

(defthm
  lofat-remove-file-correctness-lemma-19
  (implies
   (and
    (consp (cdr path))
    (fat32-filename-list-p path)
    (not
     (d-e-directory-p
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path))))))
   (equal (d-e-cc (mv-nth 0
                          (lofat-remove-file-helper fat32$c d-e path))
                  d-e)
          (d-e-cc fat32$c d-e)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

(defthm
  lofat-remove-file-correctness-lemma-20
  (implies
   (and
    (consp (cdr path))
    (fat32-filename-list-p path)
    (<=
     (+ 2 (count-of-clusters fat32$c))
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path))))))
   (equal (d-e-cc (mv-nth 0
                          (lofat-remove-file-helper fat32$c d-e path))
                  d-e)
          (d-e-cc fat32$c d-e)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

(defthm
  lofat-remove-file-correctness-lemma-21
  (implies
   (and
    (d-e-p d-e)
    (consp (cdr path))
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
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c d-e))
     (mv-nth 2
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
              entry-limit)))
    (fat32-filename-list-p path))
   (equal (d-e-cc (mv-nth 0
                          (lofat-remove-file fat32$c d-e path))
                  d-e)
          (d-e-cc fat32$c d-e)))
  :hints
  (("goal"
    :expand (lofat-remove-file fat32$c d-e path)
    :in-theory (disable (:rewrite d-e-cc-of-lofat-remove-file-disjoint))
    :use
    (:instance
     (:rewrite d-e-cc-of-lofat-remove-file-disjoint)
     (d-e d-e)
     (path (cdr path))
     (root-d-e
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 (car path))))
     (fat32$c fat32$c)))))

(defthm
  lofat-remove-file-correctness-lemma-25
  (implies
   (and
    (useful-d-e-list-p d-e-list2)
    (lofat-fs-p fat32$c)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c d-e-list2 entry-limit1))
           0)
    (<= 2
        (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list1 name))))
    (< (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list1 name)))
       (+ 2 (count-of-clusters fat32$c)))
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c d-e-list1 entry-limit2))
           0)
    (not-intersectp-list
     (mv-nth 0
             (d-e-cc fat32$c
                     (mv-nth 0 (find-d-e d-e-list1 name))))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c
                                 (mv-nth 0 (find-d-e d-e-list1 name)))))
       entry-limit2)))
    (not-intersectp-list
     (mv-nth 0
             (d-e-cc fat32$c
                     (mv-nth 0 (find-d-e d-e-list1 name))))
     (mv-nth 2
             (lofat-to-hifat-helper fat32$c d-e-list2 entry-limit1)))
    (not
     (member-intersectp-equal
      (mv-nth
       2
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c
                                  (mv-nth 0 (find-d-e d-e-list1 name)))))
        entry-limit2))
      (mv-nth 2
              (lofat-to-hifat-helper fat32$c d-e-list2 entry-limit1))))
    (d-e-directory-p (mv-nth 0 (find-d-e d-e-list1 name)))
    (useful-d-e-list-p d-e-list1))
   (equal
    (lofat-to-hifat-helper
     (mv-nth 0
             (lofat-remove-file fat32$c
                                (mv-nth 0 (find-d-e d-e-list1 name))
                                path))
     d-e-list2 entry-limit1)
    (lofat-to-hifat-helper fat32$c d-e-list2 entry-limit1)))
  :hints
  (("goal"
    :in-theory
    (disable lofat-to-hifat-helper-of-lofat-remove-file-disjoint
             (:rewrite lofat-find-file-correctness-1-lemma-6))
    :use ((:instance lofat-to-hifat-helper-of-lofat-remove-file-disjoint
                     (root-d-e (mv-nth 0 (find-d-e d-e-list1 name)))
                     (d-e-list d-e-list2))
          (:instance (:rewrite lofat-find-file-correctness-1-lemma-6)
                     (entry-limit entry-limit2)
                     (name name)
                     (d-e-list d-e-list1)
                     (fat32$c fat32$c))))))

(defthm
  lofat-remove-file-correctness-lemma-30
  (implies
   (not (consp path))
   (equal (mv-nth 0
                  (lofat-remove-file-helper fat32$c root-d-e path))
          fat32$c))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

(defthm
  lofat-remove-file-correctness-lemma-33
  (implies
   (and
    (lofat-fs-p fat32$c)
    (d-e-p root-d-e)
    (<= 2 (d-e-first-cluster root-d-e))
    (< (d-e-first-cluster root-d-e)
       (+ 2 (count-of-clusters fat32$c)))
    (not (equal (mv-nth 1
                        (lofat-remove-file-helper fat32$c root-d-e path))
                0)))
   (equal (mv-nth 0
                  (lofat-remove-file-helper fat32$c root-d-e path))
          fat32$c))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper
                              update-dir-contents-correctness-1
                              clear-cc-correctness-3))))

(defthm
  lofat-remove-file-correctness-2
  (implies
   (and (lofat-fs-p fat32$c)
        (d-e-p root-d-e)
        (>= (d-e-first-cluster root-d-e)
            *ms-first-data-cluster*)
        (< (d-e-first-cluster root-d-e)
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32$c)))
        (not (equal (mv-nth 1
                            (lofat-remove-file fat32$c root-d-e path))
                    0)))
   (equal (mv-nth 0
                  (lofat-remove-file fat32$c root-d-e path))
          fat32$c))
  :hints (("goal" :in-theory (enable update-dir-contents-correctness-1
                                     clear-cc-correctness-3
                                     lofat-remove-file))))

(defthm lofat-remove-file-correctness-lemma-28
  (implies
   (and
    (fat32-filename-list-p path)
    (not
     (d-e-directory-p
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 (car path)))))
    (consp (cdr path)))
   (equal
    (mv-nth
     0
     (lofat-to-hifat-helper
      (mv-nth 0
              (lofat-remove-file-helper fat32$c root-d-e path))
      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
      entry-limit))
    (mv-nth
     0
     (lofat-to-hifat-helper
      fat32$c
      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
      entry-limit))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

(defthm lofat-remove-file-correctness-lemma-34
  (equal
   (mv-nth 1
           (lofat-remove-file-helper fat32$c root-d-e nil))
   *enoent*)
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

(defthm lofat-remove-file-correctness-lemma-36
  (implies
   (and
    (fat32-filename-list-p path)
    (not
     (equal
      (mv-nth
       1
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 (car path)))
      0)))
   (equal
    (mv-nth 1
            (lofat-remove-file-helper fat32$c root-d-e path))
    *enoent*))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

(defthm lofat-remove-file-correctness-lemma-37
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
    (equal
     (mv-nth
      1
      (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                (car path)))
     0))
   (equal
    (mv-nth
     0
     (lofat-to-hifat-helper
      (mv-nth 0
              (lofat-remove-file-helper fat32$c root-d-e path))
      (delete-d-e
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       (car path))
      entry-limit))
    (remove-assoc-equal
     (car path)
     (mv-nth
      0
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit)))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

(defthm lofat-remove-file-correctness-lemma-38
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
    (<=
     (+ 2 (count-of-clusters fat32$c))
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 (car path)))))
    (equal
     (mv-nth
      1
      (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                (car path)))
     0)
    (consp (cdr path)))
   (equal
    (mv-nth 1
            (lofat-remove-file-helper fat32$c root-d-e path))
    *enotdir*))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

(defthm lofat-remove-file-correctness-lemma-39
  (implies
   (and
    (fat32-filename-list-p path)
    (not
     (d-e-directory-p
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 (car path)))))
    (equal
     (mv-nth
      1
      (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                (car path)))
     0)
    (consp (cdr path)))
   (equal
    (mv-nth 1
            (lofat-remove-file-helper fat32$c root-d-e path))
    *enotdir*))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

(defthm lofat-remove-file-correctness-lemma-40
  (implies
   (and
    (not (consp (cdr path)))
    (consp path)
    (equal
     (mv-nth
      1
      (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                (car path)))
     0)
    (good-root-d-e-p root-d-e fat32$c)
    (fat32-filename-list-p path))
   (equal
    (mv-nth 1
            (lofat-remove-file-helper fat32$c root-d-e path))
    0))
  :hints (("goal" :do-not-induct t
           :in-theory (enable lofat-remove-file-helper))))

(defthm
  lofat-remove-file-correctness-lemma-17
  (implies
   (and
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
           0)
    (lofat-fs-p fat32$c)
    (<= 2
        (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name))))
    (< (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name)))
       (+ 2 (count-of-clusters fat32$c)))
    (d-e-p d-e)
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
    (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
           0)
    (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))
    (useful-d-e-list-p d-e-list))
   (equal
    (d-e-cc (mv-nth 0
                    (lofat-remove-file fat32$c
                                       (mv-nth 0 (find-d-e d-e-list name))
                                       path))
            d-e)
    (d-e-cc fat32$c d-e)))
  :hints
  (("goal" :do-not-induct t
    :in-theory (disable d-e-cc-of-lofat-remove-file-disjoint
                        lofat-find-file-correctness-1-lemma-6)
    :use ((:instance d-e-cc-of-lofat-remove-file-disjoint
                     (root-d-e (mv-nth 0 (find-d-e d-e-list name))))
          lofat-find-file-correctness-1-lemma-6))))

(defthm
  lofat-remove-file-correctness-lemma-15
  (implies
   (and
    (equal
     (put-assoc-equal
      filename
      (m1-file-hifat-file-alist-fix
       d-e
       (mv-nth 0
               (lofat-to-hifat-helper fat32$c d-e-list entry-limit1)))
      fs)
     x)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
           0)
    (>= (nfix entry-limit2)
        (mv-nth 1
                (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))))
   (equal
    (put-assoc-equal
     filename
     (m1-file-hifat-file-alist-fix
      d-e
      (mv-nth 0
              (lofat-to-hifat-helper fat32$c d-e-list entry-limit2)))
     fs)
    x))
  :hints (("goal" :do-not-induct t
           :use lofat-to-hifat-helper-correctness-4)))

(defthm
  lofat-remove-file-correctness-lemma-72
  (implies
   (and (useful-d-e-list-p d-e-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               0)
        (d-e-directory-p (mv-nth 0 (find-d-e d-e-list filename))))
   (not
    (member-intersectp-equal
     (mv-nth 2
             (lofat-to-hifat-helper fat32$c (delete-d-e d-e-list filename)
                                    entry-limit))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c
                                 (mv-nth 0 (find-d-e d-e-list filename)))))
       entry-limit)))))
  :hints
  (("goal"
    :in-theory
    (e/d (lofat-to-hifat-helper useful-d-e-list-p)
         (member-intersectp-is-commutative
          (:rewrite nth-of-effective-fat)
          (:rewrite take-of-len-free)
          (:rewrite lofat-place-file-correctness-lemma-83)
          (:rewrite subsetp-append1)
          (:rewrite not-intersectp-list-when-subsetp-1)))
    :do-not-induct t
    :induct (mv (mv-nth 0
                        (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
                (mv-nth 0 (find-d-e d-e-list filename)))
    :expand
    ((:with
      member-intersectp-is-commutative
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
         (+ -1 entry-limit)))))))))

(defthm
  lofat-remove-file-correctness-lemma-22
  (implies
   (and (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
               0)
        (>= (nfix entry-limit2)
            (mv-nth 1
                    (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))))
   (iff
    (equal
     (remove-assoc-equal
      name
      (mv-nth 0
              (lofat-to-hifat-helper fat32$c d-e-list entry-limit2)))
     (remove-assoc-equal
      name
      (mv-nth 0
              (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))))
    t))
  :hints (("goal" :in-theory (disable lofat-to-hifat-helper-correctness-4)
           :use lofat-to-hifat-helper-correctness-4)))

;; Hypotheses minimised.
(defthm
  lofat-remove-file-correctness-lemma-68
  (implies
   (and
    (useful-d-e-list-p d-e-list)
    (<=
     2
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e
        (make-d-e-list
         (mv-nth
          0
          (d-e-cc-contents
           fat32$c
           (mv-nth 0 (find-d-e d-e-list filename1)))))
        filename2))))
    (<
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e
        (make-d-e-list
         (mv-nth
          0
          (d-e-cc-contents
           fat32$c
           (mv-nth 0 (find-d-e d-e-list filename1)))))
        filename2)))
     (+ 2 (count-of-clusters fat32$c)))
    (equal
     (mv-nth
      1
      (update-dir-contents
       fat32$c
       (d-e-first-cluster
        (mv-nth 0 (find-d-e d-e-list filename1)))
       (nats=>string
        (clear-d-e
         (string=>nats
          (mv-nth
           0
           (d-e-cc-contents
            fat32$c
            (mv-nth 0 (find-d-e d-e-list filename1)))))
         filename2))))
     0)
    (equal
     (mv-nth
      1
      (find-d-e
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          fat32$c
          (mv-nth 0 (find-d-e d-e-list filename1)))))
       filename2))
     0)
    (lofat-fs-p fat32$c)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
     0)
    (d-e-directory-p (mv-nth 0 (find-d-e d-e-list filename1))))
   (not-intersectp-list
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
          (d-e-cc-contents
           fat32$c
           (mv-nth 0 (find-d-e d-e-list filename1)))))
        filename2))))
    (mv-nth
     2
     (lofat-to-hifat-helper
      (mv-nth
       0
       (update-dir-contents
        fat32$c
        (d-e-first-cluster
         (mv-nth 0 (find-d-e d-e-list filename1)))
        (nats=>string
         (clear-d-e
          (string=>nats
           (mv-nth
            0
            (d-e-cc-contents
             fat32$c
             (mv-nth 0 (find-d-e d-e-list filename1)))))
          filename2))))
      d-e-list entry-limit))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lofat-to-hifat-helper lofat-to-hifat-helper-correctness-4
                            not-intersectp-list)
     (nth-of-effective-fat
      (:definition binary-append)
      (:definition len)
      (:rewrite lofat-to-hifat-helper-of-update-dir-contents)
      (:linear lofat-to-hifat-helper-correctness-3)
      (:rewrite member-intersectp-binary-append . 1)
      (:rewrite subdir-contents-p-when-zero-length)
      (:rewrite member-intersectp-is-commutative-lemma-2)
      (:rewrite lofat-to-hifat-helper-of-delete-d-e-2
                . 1)
      (:rewrite
       get-cc-contents-of-lofat-remove-file-coincident-lemma-5
       . 2)
      (:rewrite consp-of-make-list-ac)
      (:definition delete-d-e)
      (:rewrite delete-d-e-correctness-1)
      (:definition non-free-index-list-listp)
      (:definition remove-assoc-equal)
      (:linear make-clusters-correctness-2)
      (:rewrite len-of-effective-fat)
      (:definition make-list-ac)
      (:rewrite subsetp-car-member)
      (:rewrite subsetp-implies-subsetp-cdr)
      (:rewrite not-intersectp-list-when-atom)
      (:rewrite d-e-p-when-member-equal-of-d-e-list-p)
      (:rewrite another-lemma-about-member-intersectp)
      (:rewrite d-e-cc-of-update-dir-contents-coincident)
      (:rewrite lofat-place-file-correctness-lemma-56)
      (:rewrite lofat-place-file-correctness-lemma-83)
      (:rewrite subsetp-append1)
      (:rewrite lofat-place-file-correctness-lemma-93)
      (:definition nfix)
      (:rewrite lofat-place-file-correctness-lemma-58)
      lofat-place-file-correctness-lemma-121
      (:rewrite not-intersectp-list-when-subsetp-1)
      (:rewrite member-intersectp-of-set-difference$-lemma-1)
      (:rewrite subsetp-when-atom-right)
      (:rewrite subsetp-when-atom-left)
      (:rewrite lofat-place-file-correctness-lemma-46)
      (:rewrite subsetp-trans2)
      (:rewrite subsetp-trans)))
    :induct
    (lofat-to-hifat-helper fat32$c d-e-list entry-limit)
    :do-not-induct t
    :expand ((:free (y) (intersectp-equal nil y))
             (:free (fat32$c entry-limit)
                    (lofat-to-hifat-helper
                     fat32$c d-e-list entry-limit))))))

(defund-nx lofat-remove-file-spec-1
  (fat32$c d-e-list entry-limit x fs filename path d-e)
  (implies
   (and
    (<
     (hifat-entry-count fs)
     (hifat-entry-count
      (mv-nth 0
              (lofat-to-hifat-helper
               fat32$c
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
               entry-limit))))
    (stobj-disjoins-list
     (mv-nth 0 (lofat-remove-file fat32$c d-e path))
     (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
     entry-limit
     (append
      x (mv-nth 0 (d-e-cc fat32$c d-e))
      (flatten
       (mv-nth 2
               (lofat-to-hifat-helper fat32$c (delete-d-e d-e-list filename)
                                      entry-limit))))))
   (and
    (stobj-disjoins-list (mv-nth 0 (lofat-remove-file fat32$c d-e path))
                         d-e-list entry-limit x)
    (equal
     (mv-nth
      0
      (lofat-to-hifat-helper (mv-nth 0 (lofat-remove-file fat32$c d-e path))
                             d-e-list entry-limit))
     (put-assoc-equal
      filename (m1-file d-e fs)
      (mv-nth 0
              (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))))))

(encapsulate
  ()

  (local
   (in-theory
    (e/d
     (lofat-to-hifat-helper)
     (nth-of-effective-fat
      (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
      (:definition no-duplicatesp-equal)
      (:rewrite assoc-of-car-when-member)
      (:rewrite take-of-len-free)
      (:rewrite lofat-to-hifat-helper-of-delete-d-e-2
                . 2)
      (:rewrite hifat-to-lofat-inversion-lemma-2)
      (:definition assoc-equal)
      (:rewrite not-intersectp-list-when-atom)
      (:rewrite subdir-contents-p-when-zero-length)
      (:rewrite hifat-no-dups-p-of-cdr)
      (:rewrite free-index-list-listp-correctness-1)
      (:rewrite m1-file-alist-p-when-subsetp-equal)
      (:linear hifat-entry-count-when-hifat-subsetp)
      (:definition remove-assoc-equal)
      (:definition alistp)
      (:rewrite m1-file-alist-p-of-remove-assoc-equal)
      (:definition len)
      (:definition take)
      (:type-prescription fat32-entry-mask)
      (:rewrite d-e-cc-under-iff . 2)
      (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident-lemma-8)
      (:linear d-e-file-size-correctness-1)
      subsetp-append1
      (:rewrite
       d-e-cc-of-lofat-remove-file-disjoint)
      (:rewrite
       d-e-cc-contents-of-lofat-remove-file-disjoint)
      (:rewrite not-intersectp-list-when-subsetp-1)
      (:rewrite not-intersectp-list-of-set-difference$-lemma-3))
     ()
     ((:rewrite not-intersectp-list-when-subsetp-2)
      (:rewrite subsetp-when-atom-right)
      (:rewrite subsetp-trans2)
      (:rewrite subsetp-trans)
      (:rewrite member-of-append)
      (:rewrite
       not-intersectp-list-of-set-difference$-lemma-2
       . 1)
      (:rewrite
       not-intersectp-list-of-set-difference$-lemma-1)
      (:rewrite natp-of-car-when-nat-listp)
      (:definition binary-append)
      (:rewrite
       d-e-p-when-member-equal-of-d-e-list-p)
      (:rewrite
       lofat-to-hifat-helper-of-update-dir-contents)
      (:rewrite
       fat32-build-index-list-of-effective-fat-of-place-contents-disjoint)
      (:rewrite
       nat-listp-if-fat32-masked-entry-list-p)
      (:rewrite len-of-insert-d-e)
      (:rewrite
       d-e-cc-of-clear-cc)
      (:rewrite place-contents-expansion-2)
      (:rewrite len-of-place-d-e)
      (:rewrite member-when-atom)
      (:rewrite
       useful-d-e-list-p-of-place-d-e)
      (:rewrite fat32-filename-p-correctness-1)
      (:rewrite
       lofat-to-hifat-helper-of-clear-cc)
      (:rewrite
       d-e-cc-of-update-dir-contents)
      (:rewrite
       d-e-cc-contents-of-update-dir-contents-disjoint)
      (:rewrite len-of-find-n-free-clusters)
      (:rewrite
       d-e-cc-contents-of-clear-cc)
      (:definition
       stobj-find-n-free-clusters-correctness-1)))))

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

  (defthm
    lofat-remove-file-correctness-1-lemma-2
    (implies
     (and
      (lofat-fs-p fat32$c)
      (useful-d-e-list-p d-e-list)
      (fat32-filename-p filename1)
      (fat32-filename-p filename2)
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c
                                            d-e-list entry-limit))
             0)
      (d-e-directory-p (mv-nth 0
                               (find-d-e d-e-list filename1)))
      (equal
       (mv-nth
        1
        (find-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents
                   fat32$c
                   (mv-nth 0
                           (find-d-e d-e-list filename1)))))
         filename2))
       0)
      (equal
       (mv-nth
        1
        (update-dir-contents
         fat32$c
         (d-e-first-cluster (mv-nth 0
                                    (find-d-e d-e-list filename1)))
         (nats=>string
          (clear-d-e
           (string=>nats
            (mv-nth 0
                    (d-e-cc-contents
                     fat32$c
                     (mv-nth 0
                             (find-d-e d-e-list filename1)))))
           filename2))))
       0)
      (non-free-index-listp x (effective-fat fat32$c))
      (not-intersectp-list
       x
       (mv-nth 2
               (lofat-to-hifat-helper fat32$c
                                      d-e-list entry-limit))))
     (and
      (equal
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth
          0
          (update-dir-contents
           fat32$c
           (d-e-first-cluster (mv-nth 0
                                      (find-d-e d-e-list filename1)))
           (nats=>string
            (clear-d-e
             (string=>nats
              (mv-nth 0
                      (d-e-cc-contents
                       fat32$c
                       (mv-nth 0
                               (find-d-e d-e-list filename1)))))
             filename2))))
         d-e-list entry-limit))
       (put-assoc-equal
        filename1
        (m1-file
         (mv-nth 0 (find-d-e d-e-list filename1))
         (remove-assoc-equal
          filename2
          (mv-nth
           0
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents
                      fat32$c
                      (mv-nth 0
                              (find-d-e d-e-list filename1)))))
            entry-limit))))
        (mv-nth 0
                (lofat-to-hifat-helper fat32$c
                                       d-e-list entry-limit))))
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         (mv-nth
          0
          (update-dir-contents
           fat32$c
           (d-e-first-cluster (mv-nth 0
                                      (find-d-e d-e-list filename1)))
           (nats=>string
            (clear-d-e
             (string=>nats
              (mv-nth 0
                      (d-e-cc-contents
                       fat32$c
                       (mv-nth 0
                               (find-d-e d-e-list filename1)))))
             filename2))))
         d-e-list entry-limit))
       0)
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         (mv-nth
          0
          (update-dir-contents
           fat32$c
           (d-e-first-cluster (mv-nth 0
                                      (find-d-e d-e-list filename1)))
           (nats=>string
            (clear-d-e
             (string=>nats
              (mv-nth 0
                      (d-e-cc-contents
                       fat32$c
                       (mv-nth 0
                               (find-d-e d-e-list filename1)))))
             filename2))))
         d-e-list entry-limit)))))
    :hints
    (("goal"
      :in-theory
      (e/d (lofat-to-hifat-helper not-intersectp-list
                                  (:rewrite lofat-to-hifat-helper-of-delete-d-e-2
                                            . 2)
                                  (:rewrite m1-file-alist-p-of-remove-assoc-equal)
                                  (:rewrite not-intersectp-list-when-atom)
                                  (:rewrite subdir-contents-p-when-zero-length))
           (nth-of-effective-fat
            (:rewrite d-e-cc-of-update-dir-contents-coincident)
            (:rewrite subsetp-append1)
            (:rewrite not-intersectp-list-when-subsetp-1)
            (:rewrite subsetp-when-atom-left)
            (:rewrite lofat-find-file-correctness-1-lemma-6)
            (:rewrite get-cc-contents-of-lofat-remove-file-coincident-lemma-5
                      . 1)
            (:rewrite intersectp-member . 1)
            (:rewrite intersect-with-subset . 11)
            (:rewrite intersect-with-subset . 9)
            (:rewrite intersect-with-subset . 6)
            (:rewrite intersect-with-subset . 5)
            (:rewrite d-e-cc-under-iff . 2)
            (:linear d-e-file-size-correctness-1)
            (:rewrite append-atom-under-list-equiv)
            (:rewrite not-intersectp-list-of-set-difference$-lemma-3)
            (:definition remove-assoc-equal)
            (:rewrite consp-of-make-list-ac)
            (:linear hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e)
            (:rewrite lofat-place-file-correctness-lemma-83)
            (:linear lofat-find-file-correctness-1-lemma-6)
            (:rewrite lofat-place-file-correctness-lemma-46)
            (:definition nfix)
            (:rewrite member-intersectp-of-set-difference$-lemma-1)
            (:rewrite member-intersectp-binary-append . 1)
            (:rewrite lofat-place-file-correctness-lemma-27)
            (:rewrite delete-d-e-correctness-1)
            (:definition delete-d-e)
            (:rewrite rationalp-implies-acl2-numberp)
            (:rewrite remove-assoc-when-absent-1)
            (:rewrite str::explode-when-not-stringp)
            (:definition non-free-index-list-listp)
            (:rewrite lofat-place-file-correctness-lemma-5)
            (:rewrite put-assoc-equal-without-change . 1)
            (:definition unsigned-byte-p)
            (:type-prescription hifat-bounded-file-alist-p)
            (:definition integer-range-p)
            (:linear length-of-d-e-cc-contents . 1)
            (:linear len-when-hifat-bounded-file-alist-p . 2)
            (:linear len-when-hifat-bounded-file-alist-p . 1)
            (:linear position-when-member-of-take)
            (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                      . 1)
            (:definition make-list-ac)
            (:rewrite lofat-fs-p-of-update-dir-contents)
            (:rewrite another-lemma-about-member-intersectp)))
      :induct
      (induction-scheme
       d-e-list entry-limit fat32$c x)
      :expand (:free (fat32$c entry-limit)
                     (lofat-to-hifat-helper fat32$c
                                            d-e-list entry-limit))))
    :rule-classes
    ((:rewrite
      :corollary
      (implies
       (and
        (lofat-fs-p fat32$c)
        (useful-d-e-list-p d-e-list)
        (fat32-filename-p filename1)
        (fat32-filename-p filename2)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c
                                              d-e-list entry-limit))
               0)
        (d-e-directory-p (mv-nth 0
                                 (find-d-e d-e-list filename1)))
        (equal
         (mv-nth
          1
          (find-d-e
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents
                     fat32$c
                     (mv-nth 0
                             (find-d-e d-e-list filename1)))))
           filename2))
         0)
        (equal
         (mv-nth
          1
          (update-dir-contents
           fat32$c
           (d-e-first-cluster (mv-nth 0
                                      (find-d-e d-e-list filename1)))
           (nats=>string
            (clear-d-e
             (string=>nats
              (mv-nth 0
                      (d-e-cc-contents
                       fat32$c
                       (mv-nth 0
                               (find-d-e d-e-list filename1)))))
             filename2))))
         0)
        (non-free-index-listp x (effective-fat fat32$c))
        (not-intersectp-list
         x
         (mv-nth 2
                 (lofat-to-hifat-helper fat32$c
                                        d-e-list entry-limit))))
       (not-intersectp-list
        x
        (mv-nth
         2
         (lofat-to-hifat-helper
          (mv-nth
           0
           (update-dir-contents
            fat32$c
            (d-e-first-cluster (mv-nth 0
                                       (find-d-e d-e-list filename1)))
            (nats=>string
             (clear-d-e
              (string=>nats
               (mv-nth 0
                       (d-e-cc-contents
                        fat32$c
                        (mv-nth 0
                                (find-d-e d-e-list filename1)))))
              filename2))))
          d-e-list entry-limit)))))))

  (defthm
    lofat-remove-file-correctness-1-lemma-4
    (implies
     (and
      (lofat-fs-p fat32$c)
      (useful-d-e-list-p d-e-list)
      (fat32-filename-p filename1)
      (fat32-filename-p filename2)
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c
                                            d-e-list entry-limit))
             0)
      (d-e-directory-p (mv-nth 0
                               (find-d-e d-e-list filename1)))
      (equal
       (mv-nth
        1
        (find-d-e
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents
                   fat32$c
                   (mv-nth 0
                           (find-d-e d-e-list filename1)))))
         filename2))
       0)
      (equal
       (mv-nth
        1
        (update-dir-contents
         fat32$c
         (d-e-first-cluster (mv-nth 0
                                    (find-d-e d-e-list filename1)))
         (nats=>string
          (clear-d-e
           (string=>nats
            (mv-nth 0
                    (d-e-cc-contents
                     fat32$c
                     (mv-nth 0
                             (find-d-e d-e-list filename1)))))
           filename2))))
       0))
     (and
      (equal
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth
          0
          (update-dir-contents
           fat32$c
           (d-e-first-cluster (mv-nth 0
                                      (find-d-e d-e-list filename1)))
           (nats=>string
            (clear-d-e
             (string=>nats
              (mv-nth 0
                      (d-e-cc-contents
                       fat32$c
                       (mv-nth 0
                               (find-d-e d-e-list filename1)))))
             filename2))))
         d-e-list entry-limit))
       (put-assoc-equal
        filename1
        (m1-file
         (mv-nth 0 (find-d-e d-e-list filename1))
         (remove-assoc-equal
          filename2
          (mv-nth
           0
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents
                      fat32$c
                      (mv-nth 0
                              (find-d-e d-e-list filename1)))))
            entry-limit))))
        (mv-nth 0
                (lofat-to-hifat-helper fat32$c
                                       d-e-list entry-limit))))
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         (mv-nth
          0
          (update-dir-contents
           fat32$c
           (d-e-first-cluster (mv-nth 0
                                      (find-d-e d-e-list filename1)))
           (nats=>string
            (clear-d-e
             (string=>nats
              (mv-nth 0
                      (d-e-cc-contents
                       fat32$c
                       (mv-nth 0
                               (find-d-e d-e-list filename1)))))
             filename2))))
         d-e-list entry-limit))
       0)))
    :hints
    (("goal" :in-theory (e/d
                         (non-free-index-listp)
                         (lofat-remove-file-correctness-1-lemma-2))
      :use (:instance
            lofat-remove-file-correctness-1-lemma-2
            (x nil)))))

  (defthm
    lofat-remove-file-correctness-lemma-29
    (implies
     (and
      (consp path)
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
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         entry-limit)))
      (d-e-directory-p
       (mv-nth
        0
        (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                  (car path)))))
     (not-intersectp-list
      x
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth
         0
         (lofat-remove-file-helper
          fat32$c
          (mv-nth
           0
           (find-d-e
            (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (car path)))
          (cdr path)))
        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
        entry-limit))))
    :hints (("goal" :do-not-induct t
             :in-theory (enable lofat-remove-file-helper))))

  (defthm
    lofat-remove-file-correctness-lemma-42
    (implies
     (and
      (useful-d-e-list-p d-e-list)
      (equal
       (d-e-cc-contents
        (mv-nth 0
                (lofat-remove-file-helper fat32$c
                                          (mv-nth 0 (find-d-e d-e-list name))
                                          path))
        (mv-nth 0 (find-d-e d-e-list name)))
       (mv
        (implode
         (append
          (nats=>chars
           (clear-d-e
            (string=>nats
             (mv-nth 0
                     (d-e-cc-contents fat32$c
                                      (mv-nth 0 (find-d-e d-e-list name)))))
            (car path)))
          (make-list-ac
           (+
            (-
             (len
              (explode
               (mv-nth 0
                       (d-e-cc-contents fat32$c
                                        (mv-nth 0 (find-d-e d-e-list name)))))))
            (*
             (cluster-size fat32$c)
             (len
              (make-clusters
               (nats=>string
                (clear-d-e
                 (string=>nats
                  (mv-nth
                   0
                   (d-e-cc-contents fat32$c
                                    (mv-nth 0 (find-d-e d-e-list name)))))
                 (car path)))
               (cluster-size fat32$c)))))
           (code-char 0)
           nil)))
        0))
      (equal
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-remove-file-helper fat32$c
                                           (mv-nth 0 (find-d-e d-e-list name))
                                           path))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
            (mv-nth
             0
             (lofat-remove-file-helper fat32$c
                                       (mv-nth 0 (find-d-e d-e-list name))
                                       path))
            (mv-nth 0 (find-d-e d-e-list name)))))
         entry-limit))
       (mv-nth
        0
        (hifat-remove-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents fat32$c
                                     (mv-nth 0 (find-d-e d-e-list name)))))
           entry-limit))
         path)))
      (lofat-fs-p fat32$c)
      (fat32-filename-p name)
      (fat32-filename-list-p path)
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
             0)
      (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name))))
     (equal
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-remove-file-helper fat32$c
                                          (mv-nth 0 (find-d-e d-e-list name))
                                          path))
        d-e-list entry-limit))
      (put-assoc-equal
       name
       (m1-file-hifat-file-alist-fix
        (mv-nth 0 (find-d-e d-e-list name))
        (mv-nth
         0
         (hifat-remove-file
          (mv-nth
           0
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c
                                      (mv-nth 0 (find-d-e d-e-list name)))))
            entry-limit))
          path)))
       (mv-nth 0
               (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d (lofat-remove-file-helper)
           ((:definition find-d-e)
            (:rewrite lofat-place-file-correctness-lemma-56)
            (:definition member-intersectp-equal)
            (:rewrite lofat-place-file-correctness-lemma-59)
            (:rewrite lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2)
            (:linear hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e)
            (:rewrite not-intersectp-list-of-append-1)
            (:rewrite d-e-fix-when-d-e-p)
            (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
            (:rewrite d-e-p-of-car-when-d-e-list-p)
            (:definition free-index-listp))))))

  (defthm
    lofat-remove-file-correctness-lemma-43
    (implies
     (and
      (consp path)
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
      (d-e-directory-p
       (mv-nth
        0
        (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                  (car path)))))
     (equal
      (mv-nth
       3
       (lofat-to-hifat-helper
        (mv-nth
         0
         (lofat-remove-file-helper
          fat32$c
          (mv-nth
           0
           (find-d-e
            (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (car path)))
          (cdr path)))
        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
        entry-limit))
      0))
    :hints (("goal" :do-not-induct t
             :in-theory (enable lofat-remove-file-helper))))

  (defthm
    lofat-remove-file-correctness-lemma-46
    (implies
     (and
      (stobj-disjoins-list
       (mv-nth 0 (lofat-remove-file fat32$c d-e path))
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
       entry-limit x)
      (not (zp entry-limit))
      (<
       (hifat-entry-count
        (mv-nth 0
                (lofat-to-hifat-helper
                 (mv-nth 0 (lofat-remove-file fat32$c d-e path))
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 entry-limit)))
       (hifat-entry-count
        (mv-nth 0
                (lofat-to-hifat-helper
                 fat32$c
                 (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
                 entry-limit)))))
     (stobj-disjoins-list
      (mv-nth 0 (lofat-remove-file fat32$c d-e path))
      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c d-e)))
      (+ -1 entry-limit)
      x))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d
       (stobj-disjoins-list lofat-to-hifat-helper-correctness-4)
       ((:rewrite lofat-remove-file-correctness-lemma-25)
        (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-2))))))

  (defthm
    lofat-remove-file-correctness-lemma-47
    (implies
     (and
      (not (d-e-directory-p (car d-e-list)))
      (< (d-e-first-cluster (car d-e-list)) 2)
      (consp d-e-list)
      (not (zp entry-limit))
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-remove-file fat32$c
                                  (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                                  path))
       (cdr d-e-list)
       (+ -1 entry-limit)
       x)
      (not (equal (mv-nth 1
                          (find-d-e (cdr d-e-list)
                                    (d-e-filename (car d-e-list))))
                  0)))
     (stobj-disjoins-list
      (mv-nth 0
              (lofat-remove-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                                 path))
      d-e-list entry-limit x))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d
       (stobj-disjoins-list lofat-to-hifat-helper-correctness-4)
       ((:rewrite lofat-remove-file-correctness-lemma-25)
        (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-2))))))

  (defthm
    lofat-remove-file-correctness-lemma-48
    (implies
     (and
      (not (zp entry-limit))
      (equal
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-remove-file fat32$c
                                    (mv-nth 0 (find-d-e d-e-list filename))
                                    path))
         d-e-list (+ -1 entry-limit)))
       (put-assoc-equal
        filename
        (m1-file-hifat-file-alist-fix
         (mv-nth 0 (find-d-e d-e-list filename))
         (mv-nth
          0
          (lofat-to-hifat-helper
           (mv-nth 0
                   (lofat-remove-file fat32$c
                                      (mv-nth 0 (find-d-e d-e-list filename))
                                      path))
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents fat32$c
                                     (mv-nth 0 (find-d-e d-e-list filename)))))
           (+ -1 entry-limit))))
        (mv-nth 0
                (lofat-to-hifat-helper fat32$c d-e-list (+ -1 entry-limit)))))
      (<
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          (mv-nth 0
                  (lofat-remove-file fat32$c
                                     (mv-nth 0 (find-d-e d-e-list filename))
                                     path))
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c
                                    (mv-nth 0 (find-d-e d-e-list filename)))))
          entry-limit)))
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c
                                    (mv-nth 0 (find-d-e d-e-list filename)))))
          entry-limit))))
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-remove-file fat32$c
                                  (mv-nth 0 (find-d-e d-e-list filename))
                                  path))
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c
                                 (mv-nth 0 (find-d-e d-e-list filename)))))
       entry-limit
       (append
        x
        (mv-nth 0
                (d-e-cc fat32$c
                        (mv-nth 0 (find-d-e d-e-list filename))))
        (flatten
         (mv-nth 2
                 (lofat-to-hifat-helper fat32$c (delete-d-e d-e-list filename)
                                        (+ -1 entry-limit)))))))
     (iff
      (equal
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-remove-file fat32$c
                                    (mv-nth 0 (find-d-e d-e-list filename))
                                    path))
         d-e-list (+ -1 entry-limit)))
       (put-assoc-equal
        filename
        (m1-file-hifat-file-alist-fix
         (mv-nth 0 (find-d-e d-e-list filename))
         (mv-nth
          0
          (lofat-to-hifat-helper
           (mv-nth 0
                   (lofat-remove-file fat32$c
                                      (mv-nth 0 (find-d-e d-e-list filename))
                                      path))
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents fat32$c
                                     (mv-nth 0 (find-d-e d-e-list filename)))))
           entry-limit)))
        (mv-nth 0
                (lofat-to-hifat-helper fat32$c d-e-list (+ -1 entry-limit)))))
      t))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d
       (stobj-disjoins-list lofat-to-hifat-helper-correctness-4)
       ((:rewrite lofat-remove-file-correctness-lemma-25)
        (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-2))))))

  (defthm
    lofat-remove-file-correctness-lemma-50
    (implies
     (and
      (not (d-e-directory-p (car d-e-list)))
      (<= (+ 2 (count-of-clusters fat32$c))
          (d-e-first-cluster (car d-e-list)))
      (consp d-e-list)
      (not (zp entry-limit))
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-remove-file fat32$c
                                  (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                                  path))
       (cdr d-e-list)
       (+ -1 entry-limit)
       x)
      (not (equal (mv-nth 1
                          (find-d-e (cdr d-e-list)
                                    (d-e-filename (car d-e-list))))
                  0)))
     (stobj-disjoins-list
      (mv-nth 0
              (lofat-remove-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                                 path))
      d-e-list entry-limit x))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d
       (stobj-disjoins-list lofat-to-hifat-helper-correctness-4)
       ((:rewrite lofat-remove-file-correctness-lemma-25)
        (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-2))))))

  (defthm
    lofat-remove-file-correctness-lemma-52
    (implies
     (and
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-remove-file fat32$c
                                  (mv-nth 0 (find-d-e d-e-list filename))
                                  path))
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c
                                 (mv-nth 0 (find-d-e d-e-list filename)))))
       entry-limit2 y)
      (>
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c
                                    (mv-nth 0 (find-d-e d-e-list filename)))))
          entry-limit2)))
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          (mv-nth 0
                  (lofat-remove-file fat32$c
                                     (mv-nth 0 (find-d-e d-e-list filename))
                                     path))
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c
                                    (mv-nth 0 (find-d-e d-e-list filename)))))
          entry-limit2))))
      (not (zp entry-limit2))
      (useful-d-e-list-p d-e-list)
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
             0)
      (d-e-directory-p (mv-nth 0 (find-d-e d-e-list filename)))
      (< (nfix entry-limit1) entry-limit2))
     (>
      (hifat-entry-count
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c
                                   (mv-nth 0 (find-d-e d-e-list filename)))))
         entry-limit1)))
      (hifat-entry-count
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-remove-file fat32$c
                                    (mv-nth 0 (find-d-e d-e-list filename))
                                    path))
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c
                                   (mv-nth 0 (find-d-e d-e-list filename)))))
         entry-limit1)))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d (stobj-disjoins-list lofat-to-hifat-helper-correctness-4)
           ((:rewrite lofat-remove-file-correctness-lemma-25)
            (:linear nth-when-d-e-p)))))
    :rule-classes :linear)

  (defthm
    lofat-remove-file-correctness-lemma-53
    (implies
     (and
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-remove-file fat32$c
                                  (mv-nth 0 (find-d-e d-e-list filename))
                                  path))
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c
                                 (mv-nth 0 (find-d-e d-e-list filename)))))
       entry-limit
       (append
        x
        (mv-nth 0
                (d-e-cc fat32$c
                        (mv-nth 0 (find-d-e d-e-list filename))))
        (mv-nth 0 (d-e-cc fat32$c d-e))
        (flatten
         (mv-nth 2
                 (lofat-to-hifat-helper fat32$c (delete-d-e d-e-list filename)
                                        (+ -1 entry-limit))))))
      (not (zp entry-limit))
      (<
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          (mv-nth 0
                  (lofat-remove-file fat32$c
                                     (mv-nth 0 (find-d-e d-e-list filename))
                                     path))
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c
                                    (mv-nth 0 (find-d-e d-e-list filename)))))
          entry-limit)))
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c
                                    (mv-nth 0 (find-d-e d-e-list filename)))))
          entry-limit)))))
     (stobj-disjoins-list
      (mv-nth 0
              (lofat-remove-file fat32$c
                                 (mv-nth 0 (find-d-e d-e-list filename))
                                 path))
      (make-d-e-list
       (mv-nth 0
               (d-e-cc-contents fat32$c
                                (mv-nth 0 (find-d-e d-e-list filename)))))
      (+ -1 entry-limit)
      (append
       (mv-nth 0 (d-e-cc fat32$c d-e))
       x
       (mv-nth 0
               (d-e-cc fat32$c
                       (mv-nth 0 (find-d-e d-e-list filename))))
       (flatten
        (mv-nth 2
                (lofat-to-hifat-helper fat32$c (delete-d-e d-e-list filename)
                                       (+ -1 entry-limit)))))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d (stobj-disjoins-list lofat-to-hifat-helper-correctness-4)
           ((:rewrite lofat-remove-file-correctness-lemma-25)
            (:linear nth-when-d-e-p))))))

  (defthm
    lofat-remove-file-correctness-lemma-54
    (implies
     (and
      (not (d-e-directory-p (car d-e-list)))
      (consp d-e-list)
      (not (zp entry-limit))
      (<= 2 (d-e-first-cluster (car d-e-list)))
      (< (d-e-first-cluster (car d-e-list))
         (+ 2 (count-of-clusters fat32$c)))
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-remove-file fat32$c
                                  (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                                  path))
       (cdr d-e-list)
       (+ -1 entry-limit)
       (append (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
               x))
      (lofat-fs-p fat32$c)
      (useful-d-e-list-p d-e-list)
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
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) filename)))
      (not (intersectp-equal x
                             (mv-nth 0 (d-e-cc fat32$c (car d-e-list))))))
     (stobj-disjoins-list
      (mv-nth 0
              (lofat-remove-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                                 path))
      d-e-list entry-limit x))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d (stobj-disjoins-list lofat-to-hifat-helper-correctness-4
                                not-intersectp-list)
           ((:rewrite lofat-remove-file-correctness-lemma-25)
            (:linear nth-when-d-e-p))))))

  (defthm
    lofat-remove-file-correctness-lemma-55
    (implies
     (and
      (not (zp entry-limit))
      (equal
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-remove-file
                  fat32$c
                  (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                  path))
         (cdr d-e-list)
         (+ -1 entry-limit)))
       (put-assoc-equal
        filename
        (m1-file-hifat-file-alist-fix
         (mv-nth 0 (find-d-e (cdr d-e-list) filename))
         (mv-nth
          0
          (lofat-to-hifat-helper
           (mv-nth 0
                   (lofat-remove-file
                    fat32$c
                    (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                    path))
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents
              fat32$c
              (mv-nth 0 (find-d-e (cdr d-e-list) filename)))))
           (+ -1 entry-limit))))
        (mv-nth 0
                (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                       (+ -1 entry-limit)))))
      (<
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          (mv-nth 0
                  (lofat-remove-file
                   fat32$c
                   (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                   path))
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents
             fat32$c
             (mv-nth 0 (find-d-e (cdr d-e-list) filename)))))
          entry-limit)))
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents
             fat32$c
             (mv-nth 0 (find-d-e (cdr d-e-list) filename)))))
          entry-limit))))
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-remove-file
                fat32$c
                (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                path))
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents
                 fat32$c
                 (mv-nth 0 (find-d-e (cdr d-e-list) filename)))))
       entry-limit
       (append
        x
        (mv-nth 0
                (d-e-cc fat32$c
                        (mv-nth 0 (find-d-e (cdr d-e-list) filename))))
        (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
        (flatten
         (mv-nth
          2
          (lofat-to-hifat-helper fat32$c
                                 (delete-d-e (cdr d-e-list) filename)
                                 (+ -1 entry-limit)))))))
     (equal
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-remove-file
                 fat32$c
                 (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                 path))
        (cdr d-e-list)
        (+ -1 entry-limit)))
      (put-assoc-equal
       filename
       (m1-file-hifat-file-alist-fix
        (mv-nth 0 (find-d-e (cdr d-e-list) filename))
        (mv-nth
         0
         (lofat-to-hifat-helper
          (mv-nth 0
                  (lofat-remove-file
                   fat32$c
                   (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                   path))
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents
             fat32$c
             (mv-nth 0 (find-d-e (cdr d-e-list) filename)))))
          entry-limit)))
       (mv-nth 0
               (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                      (+ -1 entry-limit))))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d
       (stobj-disjoins-list lofat-to-hifat-helper-correctness-4)
       ((:rewrite lofat-remove-file-correctness-lemma-25)
        (:linear nth-when-d-e-p))))))

  (defthm
    lofat-remove-file-correctness-lemma-57
    (implies
     (and
      (d-e-directory-p (car d-e-list))
      (consp (cdr path))
      (lofat-fs-p fat32$c)
      (useful-d-e-list-p d-e-list)
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
      (fat32-filename-list-p path)
      (not (equal (mv-nth 1
                          (find-d-e (cdr d-e-list)
                                    (d-e-filename (car d-e-list))))
                  0))
      (not (intersectp-equal x
                             (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))))
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
      (<
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          (mv-nth 0
                  (lofat-remove-file fat32$c (car d-e-list)
                                     path))
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          entry-limit)))
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          entry-limit))))
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-remove-file fat32$c (car d-e-list)
                                  path))
       (make-d-e-list (mv-nth 0
                              (d-e-cc-contents fat32$c (car d-e-list))))
       entry-limit
       (append x
               (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
               (flatten (mv-nth 2
                                (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                                       entry-limit))))))
     (stobj-disjoins-list (mv-nth 0
                                  (lofat-remove-file fat32$c (car d-e-list)
                                                     path))
                          d-e-list entry-limit x))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d
       (stobj-disjoins-list lofat-to-hifat-helper-correctness-4
                            not-intersectp-list)
       ((:rewrite lofat-remove-file-correctness-lemma-25)
        (:linear nth-when-d-e-p)
        (:definition member-intersectp-equal)
        (:rewrite nfix-when-zp)
        (:definition find-d-e)
        (:rewrite
         hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e-lemma-3)
        (:rewrite d-e-fix-when-d-e-p)
        (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
        (:rewrite intersectp-when-subsetp)
        (:rewrite d-e-cc-contents-of-lofat-place-file-coincident-lemma-15)
        (:definition free-index-listp)
        (:rewrite intersectp-equal-of-atom-right)
        (:rewrite intersect-with-subset . 11)
        (:rewrite lofat-place-file-correctness-lemma-52)
        (:rewrite intersectp-equal-of-atom-left)
        (:rewrite intersectp-member . 1)
        (:rewrite intersect-with-subset . 9)
        (:rewrite intersect-with-subset . 6)
        (:rewrite intersect-with-subset . 5)
        (:rewrite lofat-place-file-correctness-lemma-121
                  . 1)))
      :expand
      ((lofat-to-hifat-helper (mv-nth '0
                                      (lofat-remove-file fat32$c (car d-e-list)
                                                         path))
                              d-e-list entry-limit)))))

  (defthm
    lofat-remove-file-correctness-lemma-61
    (implies
     (and
      (<
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          (mv-nth
           0
           (lofat-remove-file fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                              path))
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents fat32$c
                             (mv-nth 0 (find-d-e (cdr d-e-list) filename)))))
          entry-limit)))
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents fat32$c
                             (mv-nth 0 (find-d-e (cdr d-e-list) filename)))))
          entry-limit))))
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-remove-file fat32$c
                                  (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                                  path))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents fat32$c
                          (mv-nth 0 (find-d-e (cdr d-e-list) filename)))))
       entry-limit
       (append
        x
        (mv-nth 0
                (d-e-cc fat32$c
                        (mv-nth 0 (find-d-e (cdr d-e-list) filename))))
        (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
        (flatten
         (mv-nth
          2
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit))))
        (flatten
         (mv-nth
          2
          (lofat-to-hifat-helper
           fat32$c
           (delete-d-e (cdr d-e-list) filename)
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
      (not (zp entry-limit))
      (useful-d-e-list-p d-e-list)
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
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) filename))))
     (stobj-disjoins-list
      (mv-nth 0
              (lofat-remove-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                                 path))
      (make-d-e-list
       (mv-nth
        0
        (d-e-cc-contents fat32$c
                         (mv-nth 0 (find-d-e (cdr d-e-list) filename)))))
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
       (mv-nth 0
               (d-e-cc fat32$c
                       (mv-nth 0 (find-d-e (cdr d-e-list) filename))))
       (flatten
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c
          (delete-d-e (cdr d-e-list) filename)
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
               (+ -1 entry-limit))))))))))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d
       (stobj-disjoins-list lofat-to-hifat-helper-correctness-4
                            not-intersectp-list)
       ((:rewrite lofat-remove-file-correctness-lemma-25)
        (:linear nth-when-d-e-p)
        (:definition member-intersectp-equal)
        (:rewrite nfix-when-zp)
        (:definition find-d-e)
        (:rewrite
         hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e-lemma-3)
        (:rewrite d-e-fix-when-d-e-p)
        (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
        (:rewrite intersectp-when-subsetp)
        (:rewrite d-e-cc-contents-of-lofat-place-file-coincident-lemma-15)
        (:definition free-index-listp)
        (:rewrite intersectp-equal-of-atom-right)
        (:rewrite intersect-with-subset . 11)
        (:rewrite lofat-place-file-correctness-lemma-52)
        (:rewrite intersectp-equal-of-atom-left)
        (:rewrite intersectp-member . 1)
        (:rewrite intersect-with-subset . 9)
        (:rewrite intersect-with-subset . 6)
        (:rewrite intersect-with-subset . 5)
        (:rewrite lofat-place-file-correctness-lemma-121
                  . 1)))
      :expand
      ((lofat-to-hifat-helper (mv-nth '0
                                      (lofat-remove-file fat32$c (car d-e-list)
                                                         path))
                              d-e-list entry-limit)))))

  (defthm
    lofat-remove-file-correctness-lemma-45
    (implies
     (and
      (consp d-e-list)
      (not (zp entry-limit))
      (d-e-directory-p (car d-e-list))
      (lofat-fs-p fat32$c)
      (useful-d-e-list-p d-e-list)
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
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          (mv-nth 0
                  (lofat-remove-file fat32$c (car d-e-list)
                                     path))
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          entry-limit)))
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          entry-limit))))
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-remove-file fat32$c (car d-e-list)
                                  path))
       (make-d-e-list (mv-nth 0
                              (d-e-cc-contents fat32$c (car d-e-list))))
       entry-limit
       (append x
               (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
               (flatten (mv-nth 2
                                (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                                       entry-limit))))))
     (equal
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-remove-file fat32$c (car d-e-list)
                                   path))
        (cdr d-e-list)
        (+
         -1 entry-limit
         (-
          (hifat-entry-count
           (mv-nth
            0
            (lofat-to-hifat-helper
             (mv-nth 0
                     (lofat-remove-file fat32$c (car d-e-list)
                                        path))
             (make-d-e-list (mv-nth 0
                                    (d-e-cc-contents fat32$c (car d-e-list))))
             (+ -1 entry-limit))))))))
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
             (+ -1 entry-limit))))))))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d
       (stobj-disjoins-list lofat-to-hifat-helper-correctness-4)
       ((:rewrite lofat-remove-file-correctness-lemma-25)
        (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-2))))))

  (defthm
    lofat-remove-file-correctness-lemma-49
    (implies
     (and
      (not (zp entry-limit))
      (<
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          (mv-nth 0
                  (lofat-remove-file fat32$c (car d-e-list)
                                     path))
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          entry-limit)))
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list (mv-nth 0
                                 (d-e-cc-contents fat32$c (car d-e-list))))
          entry-limit))))
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-remove-file fat32$c (car d-e-list)
                                  path))
       (make-d-e-list (mv-nth 0
                              (d-e-cc-contents fat32$c (car d-e-list))))
       entry-limit
       (append x
               (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
               (flatten (mv-nth 2
                                (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                                       entry-limit))))))
     (equal
      (m1-file-hifat-file-alist-fix
       (car d-e-list)
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-remove-file fat32$c (car d-e-list)
                                    path))
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit))))
      (m1-file-hifat-file-alist-fix
       (car d-e-list)
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-remove-file fat32$c (car d-e-list)
                                    path))
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         entry-limit)))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d
       (stobj-disjoins-list lofat-to-hifat-helper-correctness-4)
       ((:rewrite lofat-remove-file-correctness-lemma-25)
        (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-2))))))

  (defthm
    lofat-remove-file-correctness-lemma-51
    (implies
     (and
      (lofat-fs-p fat32$c)
      (useful-d-e-list-p d-e-list)
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
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) filename))))
     (equal
      (m1-file-hifat-file-alist-fix
       (car d-e-list)
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth
          0
          (lofat-remove-file fat32$c
                             (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                             path))
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit))))
      (m1-file-hifat-file-alist-fix
       (car d-e-list)
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list (mv-nth 0
                                (d-e-cc-contents fat32$c (car d-e-list))))
         (+ -1 entry-limit))))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d
       (stobj-disjoins-list
        lofat-to-hifat-helper-correctness-4
        not-intersectp-list
        (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-1
                  . 1))
       ((:linear nth-when-d-e-p)
        (:definition member-intersectp-equal)
        (:rewrite nfix-when-zp)
        (:definition find-d-e)
        (:rewrite
         hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e-lemma-3)
        (:rewrite d-e-fix-when-d-e-p)
        (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
        (:rewrite intersectp-when-subsetp)
        (:rewrite d-e-cc-contents-of-lofat-place-file-coincident-lemma-15)
        (:definition free-index-listp)
        (:rewrite intersectp-equal-of-atom-right)
        (:rewrite intersect-with-subset . 11)
        (:rewrite lofat-place-file-correctness-lemma-52)
        (:rewrite intersectp-equal-of-atom-left)
        (:rewrite intersectp-member . 1)
        (:rewrite intersect-with-subset . 9)
        (:rewrite intersect-with-subset . 6)
        (:rewrite intersect-with-subset . 5)
        (:rewrite lofat-place-file-correctness-lemma-121
                  . 1)
        (:rewrite lofat-remove-file-correctness-lemma-55)
        (:rewrite not-intersectp-list-of-set-difference$-lemma-2
                  . 2)
        (:rewrite lofat-place-file-correctness-lemma-59)
        (:rewrite lofat-remove-file-correctness-lemma-31)
        (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint)
        (:rewrite lofat-place-file-correctness-lemma-83)
        (:linear lofat-find-file-correctness-1-lemma-6)
        (:rewrite subsetp-when-atom-left)))
      :expand
      ((lofat-to-hifat-helper
        (mv-nth '0
                (lofat-remove-file fat32$c
                                   (mv-nth '0
                                           (find-d-e (cdr d-e-list) filename))
                                   path))
        d-e-list entry-limit)))))

  (defthm
    lofat-remove-file-correctness-lemma-56
    (implies
     (and
      (not (zp entry-limit))
      (equal
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth
          0
          (lofat-remove-file fat32$c
                             (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                             path))
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
              (+ -1 entry-limit))))))))
       (put-assoc-equal
        filename
        (m1-file-hifat-file-alist-fix
         (mv-nth 0 (find-d-e (cdr d-e-list) filename))
         (mv-nth
          0
          (lofat-to-hifat-helper
           (mv-nth
            0
            (lofat-remove-file fat32$c
                               (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                               path))
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) filename)))))
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
               (+ -1 entry-limit))))))))))
      (lofat-fs-p fat32$c)
      (useful-d-e-list-p d-e-list)
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
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) filename)))
      (<
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          (mv-nth
           0
           (lofat-remove-file fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                              path))
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents fat32$c
                             (mv-nth 0 (find-d-e (cdr d-e-list) filename)))))
          entry-limit)))
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents fat32$c
                             (mv-nth 0 (find-d-e (cdr d-e-list) filename)))))
          entry-limit))))
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-remove-file fat32$c
                                  (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                                  path))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents fat32$c
                          (mv-nth 0 (find-d-e (cdr d-e-list) filename)))))
       entry-limit
       (append
        x
        (mv-nth 0
                (d-e-cc fat32$c
                        (mv-nth 0 (find-d-e (cdr d-e-list) filename))))
        (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
        (flatten
         (mv-nth
          2
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit))))
        (flatten
         (mv-nth
          2
          (lofat-to-hifat-helper
           fat32$c
           (delete-d-e (cdr d-e-list) filename)
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
                (+ -1 entry-limit))))))))))))
     (equal
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-remove-file fat32$c
                                   (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                                   path))
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
              (lofat-remove-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                                 path))
             (make-d-e-list (mv-nth 0
                                    (d-e-cc-contents fat32$c (car d-e-list))))
             (+ -1 entry-limit))))))))
      (put-assoc-equal
       filename
       (m1-file-hifat-file-alist-fix
        (mv-nth 0 (find-d-e (cdr d-e-list) filename))
        (mv-nth
         0
         (lofat-to-hifat-helper
          (mv-nth
           0
           (lofat-remove-file fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                              path))
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents fat32$c
                             (mv-nth 0 (find-d-e (cdr d-e-list) filename)))))
          entry-limit)))
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
      :do-not-induct t
      :in-theory
      (e/d
       (stobj-disjoins-list
        lofat-to-hifat-helper-correctness-4
        not-intersectp-list
        (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-1
                  . 1))
       ((:linear nth-when-d-e-p)
        (:definition member-intersectp-equal)
        (:rewrite nfix-when-zp)
        (:definition find-d-e)
        (:rewrite
         hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e-lemma-3)
        (:rewrite d-e-fix-when-d-e-p)
        (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
        (:rewrite intersectp-when-subsetp)
        (:rewrite d-e-cc-contents-of-lofat-place-file-coincident-lemma-15)
        (:definition free-index-listp)
        (:rewrite intersectp-equal-of-atom-right)
        (:rewrite intersect-with-subset . 11)
        (:rewrite lofat-place-file-correctness-lemma-52)
        (:rewrite intersectp-equal-of-atom-left)
        (:rewrite intersectp-member . 1)
        (:rewrite intersect-with-subset . 9)
        (:rewrite intersect-with-subset . 6)
        (:rewrite intersect-with-subset . 5)
        (:rewrite lofat-place-file-correctness-lemma-121
                  . 1)
        (:rewrite lofat-remove-file-correctness-lemma-55)
        (:rewrite not-intersectp-list-of-set-difference$-lemma-2
                  . 2)
        (:rewrite lofat-place-file-correctness-lemma-59)
        (:rewrite lofat-remove-file-correctness-lemma-31)
        (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint)
        (:rewrite lofat-place-file-correctness-lemma-83)
        (:linear lofat-find-file-correctness-1-lemma-6)
        (:rewrite subsetp-when-atom-left)))
      :expand
      ((lofat-to-hifat-helper
        (mv-nth '0
                (lofat-remove-file fat32$c
                                   (mv-nth '0
                                           (find-d-e (cdr d-e-list) filename))
                                   path))
        d-e-list entry-limit)))))

  (defthm
    lofat-remove-file-correctness-lemma-27
    (implies
     (and
      (stobj-disjoins-list
       (mv-nth 0
               (lofat-remove-file fat32$c
                                  (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                                  path))
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
      (lofat-fs-p fat32$c)
      (useful-d-e-list-p d-e-list)
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
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) filename)))
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
      (<
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          (mv-nth
           0
           (lofat-remove-file fat32$c
                              (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                              path))
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents fat32$c
                             (mv-nth 0 (find-d-e (cdr d-e-list) filename)))))
          entry-limit)))
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents fat32$c
                             (mv-nth 0 (find-d-e (cdr d-e-list) filename)))))
          entry-limit)))))
     (stobj-disjoins-list
      (mv-nth 0
              (lofat-remove-file fat32$c
                                 (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                                 path))
      d-e-list entry-limit x))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d
       (stobj-disjoins-list
        lofat-to-hifat-helper-correctness-4
        not-intersectp-list
        (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-1
                  . 1))
       ((:linear nth-when-d-e-p)
        (:definition member-intersectp-equal)
        (:rewrite nfix-when-zp)
        (:definition find-d-e)
        (:rewrite
         hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e-lemma-3)
        (:rewrite d-e-fix-when-d-e-p)
        (:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
        (:rewrite intersectp-when-subsetp)
        (:rewrite d-e-cc-contents-of-lofat-place-file-coincident-lemma-15)
        (:definition free-index-listp)
        (:rewrite intersectp-equal-of-atom-right)
        (:rewrite intersect-with-subset . 11)
        (:rewrite lofat-place-file-correctness-lemma-52)
        (:rewrite intersectp-equal-of-atom-left)
        (:rewrite intersectp-member . 1)
        (:rewrite intersect-with-subset . 9)
        (:rewrite intersect-with-subset . 6)
        (:rewrite intersect-with-subset . 5)
        (:rewrite lofat-place-file-correctness-lemma-121
                  . 1)
        (:rewrite lofat-remove-file-correctness-lemma-55)
        (:rewrite not-intersectp-list-of-set-difference$-lemma-2
                  . 2)
        (:rewrite lofat-place-file-correctness-lemma-59)
        (:rewrite lofat-remove-file-correctness-lemma-31)
        (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint)
        (:rewrite lofat-place-file-correctness-lemma-83)
        (:linear lofat-find-file-correctness-1-lemma-6)
        (:rewrite subsetp-when-atom-left)))
      :expand
      ((lofat-to-hifat-helper
        (mv-nth '0
                (lofat-remove-file fat32$c
                                   (mv-nth '0
                                           (find-d-e (cdr d-e-list) filename))
                                   path))
        d-e-list entry-limit)))))

  (defthmd
    lofat-remove-file-correctness-lemma-32
    (implies
     (and (consp (cdr path))
          (lofat-fs-p fat32$c)
          (useful-d-e-list-p d-e-list)
          (equal (mv-nth 3
                         (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
                 0)
          (fat32-filename-list-p path)
          (d-e-directory-p (mv-nth 0 (find-d-e d-e-list filename)))
          (not-intersectp-list
           x
           (mv-nth 2
                   (lofat-to-hifat-helper fat32$c d-e-list entry-limit))))
     (lofat-remove-file-spec-1
      fat32$c d-e-list entry-limit x
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-remove-file fat32$c
                                   (mv-nth 0 (find-d-e d-e-list filename))
                                   path))
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c
                                  (mv-nth 0 (find-d-e d-e-list filename)))))
        entry-limit))
      filename path
      (mv-nth 0 (find-d-e d-e-list filename))))
    :hints
    (("goal"
      :induct (induction-scheme d-e-list entry-limit fat32$c x)
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (intersectp-equal nil x))
      :in-theory
      (disable
       (:rewrite lofat-remove-file-correctness-lemma-25)
       (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-2)
       (:rewrite lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-1
                 . 1)
       (:rewrite member-intersectp-is-commutative)
       (:linear nth-when-d-e-p)
       (:rewrite lofat-place-file-correctness-lemma-83)))
     (if (not stable-under-simplificationp)
         nil
       '(:do-not-induct t
                        :in-theory
                        (e/d
                         (lofat-remove-file-spec-1)
                         ((:rewrite lofat-remove-file-correctness-lemma-25)
                          (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-2))))))
    :rule-classes
    ((:rewrite
      :corollary
      (implies
       (and
        (consp (cdr path))
        (equal
         (mv-nth
          3
          (lofat-to-hifat-helper
           (mv-nth 0
                   (lofat-remove-file fat32$c
                                      (mv-nth 0 (find-d-e d-e-list filename))
                                      path))
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents fat32$c
                                     (mv-nth 0 (find-d-e d-e-list filename)))))
           entry-limit))
         0)
        (not-intersectp-list
         (mv-nth 0
                 (d-e-cc fat32$c
                         (mv-nth 0 (find-d-e d-e-list filename))))
         (mv-nth
          2
          (lofat-to-hifat-helper
           (mv-nth 0
                   (lofat-remove-file fat32$c
                                      (mv-nth 0 (find-d-e d-e-list filename))
                                      path))
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents fat32$c
                                     (mv-nth 0 (find-d-e d-e-list filename)))))
           entry-limit)))
        (not
         (member-intersectp-equal
          (mv-nth 2
                  (lofat-to-hifat-helper fat32$c (delete-d-e d-e-list filename)
                                         entry-limit))
          (mv-nth
           2
           (lofat-to-hifat-helper
            (mv-nth 0
                    (lofat-remove-file fat32$c
                                       (mv-nth 0 (find-d-e d-e-list filename))
                                       path))
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c
                                      (mv-nth 0 (find-d-e d-e-list filename)))))
            entry-limit))))
        (not-intersectp-list
         x
         (mv-nth
          2
          (lofat-to-hifat-helper
           (mv-nth 0
                   (lofat-remove-file fat32$c
                                      (mv-nth 0 (find-d-e d-e-list filename))
                                      path))
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents fat32$c
                                     (mv-nth 0 (find-d-e d-e-list filename)))))
           entry-limit)))
        (lofat-fs-p fat32$c)
        (useful-d-e-list-p d-e-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               0)
        (fat32-filename-list-p path)
        (d-e-directory-p (mv-nth 0 (find-d-e d-e-list filename)))
        (not-intersectp-list
         x
         (mv-nth 2
                 (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
        (<
         (hifat-entry-count
          (mv-nth
           0
           (lofat-to-hifat-helper
            (mv-nth 0
                    (lofat-remove-file fat32$c
                                       (mv-nth 0 (find-d-e d-e-list filename))
                                       path))
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c
                                      (mv-nth 0 (find-d-e d-e-list filename)))))
            entry-limit)))
         (hifat-entry-count
          (mv-nth
           0
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents fat32$c
                                      (mv-nth 0 (find-d-e d-e-list filename)))))
            entry-limit)))))
       (not-intersectp-list
        x
        (mv-nth
         2
         (lofat-to-hifat-helper
          (mv-nth 0
                  (lofat-remove-file fat32$c
                                     (mv-nth 0 (find-d-e d-e-list filename))
                                     path))
          d-e-list entry-limit))))
      :hints (("goal" :in-theory (enable lofat-remove-file-spec-1
                                         stobj-disjoins-list)
               :do-not-induct t))))))

(defthmd
  lofat-remove-file-correctness-lemma-24
  (implies
   (and
    (consp (cdr path))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-remove-file fat32$c
                                  (mv-nth 0 (find-d-e d-e-list filename))
                                  path))
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c
                                 (mv-nth 0 (find-d-e d-e-list filename)))))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0
             (d-e-cc fat32$c
                     (mv-nth 0 (find-d-e d-e-list filename))))
     (mv-nth
      2
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-remove-file fat32$c
                                  (mv-nth 0 (find-d-e d-e-list filename))
                                  path))
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents fat32$c
                                 (mv-nth 0 (find-d-e d-e-list filename)))))
       entry-limit)))
    (not
     (member-intersectp-equal
      (mv-nth 2
              (lofat-to-hifat-helper fat32$c (delete-d-e d-e-list filename)
                                     entry-limit))
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-remove-file fat32$c
                                   (mv-nth 0 (find-d-e d-e-list filename))
                                   path))
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c
                                  (mv-nth 0 (find-d-e d-e-list filename)))))
        entry-limit))))
    (lofat-fs-p fat32$c)
    (useful-d-e-list-p d-e-list)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
           0)
    (fat32-filename-list-p path)
    (d-e-directory-p (mv-nth 0 (find-d-e d-e-list filename)))
    (< (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list filename)))
       (+ 2 (count-of-clusters fat32$c)))
    (<
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-remove-file fat32$c
                                   (mv-nth 0 (find-d-e d-e-list filename))
                                   path))
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c
                                  (mv-nth 0 (find-d-e d-e-list filename)))))
        entry-limit)))
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents fat32$c
                                  (mv-nth 0 (find-d-e d-e-list filename)))))
        entry-limit)))))
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-remove-file fat32$c
                                  (mv-nth 0 (find-d-e d-e-list filename))
                                  path))
       d-e-list entry-limit))
     0)
    (equal
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth 0
               (lofat-remove-file fat32$c
                                  (mv-nth 0 (find-d-e d-e-list filename))
                                  path))
       d-e-list entry-limit))
     (put-assoc-equal
      filename
      (m1-file
       (mv-nth 0 (find-d-e d-e-list filename))
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-remove-file fat32$c
                                    (mv-nth 0 (find-d-e d-e-list filename))
                                    path))
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c
                                   (mv-nth 0 (find-d-e d-e-list filename)))))
         entry-limit)))
      (mv-nth 0
              (lofat-to-hifat-helper fat32$c d-e-list entry-limit))))))
  :hints (("goal" :use (:instance lofat-remove-file-correctness-lemma-32
                                  (x nil))
           :in-theory (enable lofat-remove-file-spec-1
                              stobj-disjoins-list)
           :do-not-induct t)))

(defthm lofat-remove-file-correctness-lemma-41
  (implies
   (and
    (consp path)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-remove-file
         fat32$c
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (car path)))
         (cdr path)))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth
           0
           (lofat-remove-file
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
              (car path)))
            (cdr path)))
          (mv-nth
           0
           (find-d-e
            (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (car path))))))
       entry-limit))
     0)
    (equal
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-remove-file
         fat32$c
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (car path)))
         (cdr path)))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth
           0
           (lofat-remove-file
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
              (car path)))
            (cdr path)))
          (mv-nth
           0
           (find-d-e
            (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (car path))))))
       entry-limit))
     (mv-nth
      0
      (hifat-remove-file
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
       (cdr path))))
    (not-intersectp-list
     (mv-nth
      0
      (d-e-cc
       fat32$c
       (mv-nth
        0
        (find-d-e
         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         (car path)))))
     (mv-nth
      2
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-remove-file
         fat32$c
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (car path)))
         (cdr path)))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth
           0
           (lofat-remove-file
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
              (car path)))
            (cdr path)))
          (mv-nth
           0
           (find-d-e
            (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (car path))))))
       entry-limit)))
    (not
     (member-intersectp-equal
      (mv-nth
       2
       (lofat-to-hifat-helper
        fat32$c
        (delete-d-e
         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         (car path))
        entry-limit))
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth
         0
         (lofat-remove-file
          fat32$c
          (mv-nth
           0
           (find-d-e
            (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (car path)))
          (cdr path)))
        (make-d-e-list
         (mv-nth
          0
          (d-e-cc-contents
           (mv-nth
            0
            (lofat-remove-file
             fat32$c
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
               (car path)))
             (cdr path)))
           (mv-nth
            0
            (find-d-e
             (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
             (car path))))))
        entry-limit))))
    (not-intersectp-list
     x
     (mv-nth
      2
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-remove-file
         fat32$c
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (car path)))
         (cdr path)))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth
           0
           (lofat-remove-file
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
              (car path)))
            (cdr path)))
          (mv-nth
           0
           (find-d-e
            (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (car path))))))
       entry-limit)))
    (equal
     (mv-nth
      1
      (hifat-remove-file
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
       (cdr path)))
     (mv-nth
      1
      (lofat-remove-file
       fat32$c
       (mv-nth
        0
        (find-d-e
         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         (car path)))
       (cdr path))))
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
     x
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit)))
    (d-e-directory-p
     (mv-nth
      0
      (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                (car path)))))
   (not-intersectp-list
    x
    (mv-nth
     2
     (lofat-to-hifat-helper
      (mv-nth
       0
       (lofat-remove-file
        fat32$c
        (mv-nth
         0
         (find-d-e
          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
          (car path)))
        (cdr path)))
      (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
      entry-limit))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (e/d (lofat-remove-file)
         ((:rewrite d-e-cc-contents-of-lofat-remove-file-coincident)
          (:linear hifat-entry-count-of-hifat-remove-file)))
    :use
    ((:instance
      (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident)
      (path (cdr path))
      (d-e
       (mv-nth
        0
        (find-d-e
         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         (car path))))
      (fat32$c fat32$c))
     (:instance
      (:rewrite lofat-remove-file-correctness-lemma-32)
      (entry-limit entry-limit)
      (path (cdr path))
      (filename (car path))
      (d-e-list (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e))))
      (fat32$c fat32$c)
      (x x))
     (:instance
      (:linear hifat-entry-count-of-hifat-remove-file)
      (path (cdr path))
      (fs
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
         entry-limit))))))))

(defthm
  lofat-remove-file-correctness-lemma-44
  (implies
   (and
    (consp path)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-remove-file
         fat32$c
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (car path)))
         (cdr path)))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth
           0
           (lofat-remove-file
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
              (car path)))
            (cdr path)))
          (mv-nth
           0
           (find-d-e
            (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (car path))))))
       entry-limit))
     0)
    (equal
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-remove-file
         fat32$c
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (car path)))
         (cdr path)))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth
           0
           (lofat-remove-file
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
              (car path)))
            (cdr path)))
          (mv-nth
           0
           (find-d-e
            (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (car path))))))
       entry-limit))
     (mv-nth
      0
      (hifat-remove-file
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
       (cdr path))))
    (not-intersectp-list
     (mv-nth
      0
      (d-e-cc
       fat32$c
       (mv-nth
        0
        (find-d-e
         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         (car path)))))
     (mv-nth
      2
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-remove-file
         fat32$c
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (car path)))
         (cdr path)))
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          (mv-nth
           0
           (lofat-remove-file
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
              (car path)))
            (cdr path)))
          (mv-nth
           0
           (find-d-e
            (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (car path))))))
       entry-limit)))
    (not
     (member-intersectp-equal
      (mv-nth
       2
       (lofat-to-hifat-helper
        fat32$c
        (delete-d-e
         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         (car path))
        entry-limit))
      (mv-nth
       2
       (lofat-to-hifat-helper
        (mv-nth
         0
         (lofat-remove-file
          fat32$c
          (mv-nth
           0
           (find-d-e
            (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            (car path)))
          (cdr path)))
        (make-d-e-list
         (mv-nth
          0
          (d-e-cc-contents
           (mv-nth
            0
            (lofat-remove-file
             fat32$c
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
               (car path)))
             (cdr path)))
           (mv-nth
            0
            (find-d-e
             (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
             (car path))))))
        entry-limit))))
    (equal
     (mv-nth
      1
      (hifat-remove-file
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
       (cdr path)))
     (mv-nth
      1
      (lofat-remove-file
       fat32$c
       (mv-nth
        0
        (find-d-e
         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         (car path)))
       (cdr path))))
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
    (d-e-directory-p
     (mv-nth
      0
      (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                (car path)))))
   (and
    (equal
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-remove-file
         fat32$c
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (car path)))
         (cdr path)))
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit))
     (put-assoc-equal
      (car path)
      (m1-file-hifat-file-alist-fix
       (mv-nth
        0
        (find-d-e
         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         (car path)))
       (mv-nth
        0
        (hifat-remove-file
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
         (cdr path))))
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
        entry-limit))))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth
        0
        (lofat-remove-file
         fat32$c
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           (car path)))
         (cdr path)))
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit))
     0)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (e/d (lofat-remove-file)
         ((:rewrite d-e-cc-contents-of-lofat-remove-file-coincident)
          (:linear hifat-entry-count-of-hifat-remove-file)))
    :use
    ((:instance
      (:rewrite d-e-cc-contents-of-lofat-remove-file-coincident)
      (path (cdr path))
      (d-e
       (mv-nth
        0
        (find-d-e
         (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
         (car path))))
      (fat32$c fat32$c))
     (:instance
      lofat-remove-file-correctness-lemma-24
      (entry-limit entry-limit)
      (path (cdr path))
      (filename (car path))
      (d-e-list (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e))))
      (fat32$c fat32$c))
     (:instance
      (:linear hifat-entry-count-of-hifat-remove-file)
      (path (cdr path))
      (fs
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
         entry-limit))))))))

(encapsulate
  ()

  (local
   (defun-nx
     induction-scheme
     (entry-limit fat32$c path root-d-e x)
     (cond
      ((and
        (consp path)
        (equal
         (mv-nth
          1
          (find-d-e
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path))))
         0)
        (d-e-directory-p
         (mv-nth
          0
          (find-d-e
           (make-d-e-list
            (mv-nth
             0
             (d-e-cc-contents fat32$c root-d-e)))
           (fat32-filename-fix (car path)))))
        (consp (cdr path)))
       (induction-scheme
        entry-limit
        fat32$c (cdr path)
        (mv-nth
         0
         (find-d-e
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c root-d-e)))
          (fat32-filename-fix (car path))))
        (append
         (mv-nth
          0
          (d-e-cc
           fat32$c
           (mv-nth
            0
            (find-d-e
             (make-d-e-list
              (mv-nth 0
                      (d-e-cc-contents fat32$c root-d-e)))
             (fat32-filename-fix (car path))))))
         (flatten
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (delete-d-e
             (make-d-e-list
              (mv-nth 0
                      (d-e-cc-contents fat32$c root-d-e)))
             (fat32-filename-fix (car path)))
            entry-limit)))
         x)))
      (t
       (mv entry-limit fat32$c path root-d-e x)))))

  ;; hypotheses trimmed.
  (defthm
    lofat-remove-file-correctness-lemma-1
    (b*
        (((mv fs error-code)
          (hifat-remove-file
           (mv-nth 0
                   (lofat-to-hifat-helper
                    fat32$c
                    (make-d-e-list
                     (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                    entry-limit))
           path)))
      (implies
       (and
        (good-root-d-e-p root-d-e fat32$c)
        (non-free-index-listp x (effective-fat fat32$c))
        (fat32-filename-list-p path)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper
                        fat32$c
                        (make-d-e-list
                         (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                        entry-limit))
               0)
        (not-intersectp-list
         (mv-nth 0 (d-e-cc fat32$c root-d-e))
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list
                   (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                  entry-limit)))
        (not-intersectp-list
         x
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list
                   (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                  entry-limit))))
       (and
        (equal
         (mv-nth 3
                 (lofat-to-hifat-helper
                  (mv-nth
                   0
                   (lofat-remove-file fat32$c root-d-e path))
                  (make-d-e-list
                   (mv-nth 0
                           (d-e-cc-contents
                            (mv-nth
                             0
                             (lofat-remove-file fat32$c root-d-e path))
                            root-d-e)))
                  entry-limit))
         0)
        (equal
         (mv-nth 0
                 (lofat-to-hifat-helper
                  (mv-nth
                   0
                   (lofat-remove-file fat32$c root-d-e path))
                  (make-d-e-list
                   (mv-nth 0
                           (d-e-cc-contents
                            (mv-nth
                             0
                             (lofat-remove-file fat32$c root-d-e path))
                            root-d-e)))
                  entry-limit))
         fs)
        (not-intersectp-list
         x
         (mv-nth 2
                 (lofat-to-hifat-helper
                  (mv-nth
                   0
                   (lofat-remove-file fat32$c root-d-e path))
                  (make-d-e-list
                   (mv-nth 0
                           (d-e-cc-contents
                            (mv-nth
                             0
                             (lofat-remove-file fat32$c root-d-e path))
                            root-d-e)))
                  entry-limit)))
        (equal error-code
               (mv-nth
                1
                (lofat-remove-file fat32$c root-d-e path))))))
    :hints
    (("goal"
      :induct
      (induction-scheme
       entry-limit fat32$c path root-d-e x)
      :expand
      (lofat-remove-file fat32$c root-d-e path)
      :in-theory (e/d
                  (hifat-remove-file
                   (:rewrite lofat-to-hifat-inversion-lemma-4)
                   lofat-to-hifat-inversion-lemma-15
                   lofat-remove-file)
                  ((:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-9)
                   (:rewrite intersectp-is-commutative)))))
    :rule-classes
    ((:rewrite
      :corollary
      (implies
       (and
        (good-root-d-e-p root-d-e fat32$c)
        (non-free-index-listp x (effective-fat fat32$c))
        (fat32-filename-list-p path)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper
                        fat32$c
                        (make-d-e-list
                         (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                        entry-limit))
               0)
        (not-intersectp-list
         (mv-nth 0 (d-e-cc fat32$c root-d-e))
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list
                   (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                  entry-limit)))
        (not-intersectp-list
         x
         (mv-nth 2
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list
                   (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                  entry-limit))))
       (not-intersectp-list
        x
        (mv-nth 2
                (lofat-to-hifat-helper
                 (mv-nth
                  0
                  (lofat-remove-file fat32$c root-d-e path))
                 (make-d-e-list
                  (mv-nth 0
                          (d-e-cc-contents
                           (mv-nth
                            0
                            (lofat-remove-file fat32$c root-d-e path))
                           root-d-e)))
                 entry-limit))))))))

(defthm
  lofat-remove-file-correctness-1
  (b*
      (((mv fs error-code)
        (hifat-remove-file
         (mv-nth 0
                 (lofat-to-hifat-helper
                  fat32$c
                  (make-d-e-list
                   (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                  entry-limit))
         path)))
    (implies
     (and
      (good-root-d-e-p root-d-e fat32$c)
      (fat32-filename-list-p path)
      (equal (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32$c
                      (make-d-e-list
                       (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                      entry-limit))
             0)
      (not-intersectp-list
       (mv-nth 0 (d-e-cc fat32$c root-d-e))
       (mv-nth 2
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list
                 (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                entry-limit))))
     (and
      (equal
       (mv-nth 3
               (lofat-to-hifat-helper
                (mv-nth
                 0
                 (lofat-remove-file fat32$c root-d-e path))
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents
                          (mv-nth
                           0
                           (lofat-remove-file fat32$c root-d-e path))
                          root-d-e)))
                entry-limit))
       0)
      (equal
       (mv-nth 0
               (lofat-to-hifat-helper
                (mv-nth
                 0
                 (lofat-remove-file fat32$c root-d-e path))
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents
                          (mv-nth
                           0
                           (lofat-remove-file fat32$c root-d-e path))
                          root-d-e)))
                entry-limit))
       fs)
      (equal error-code
             (mv-nth
              1
              (lofat-remove-file fat32$c root-d-e path))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d
                (non-free-index-listp)
                (lofat-remove-file-correctness-lemma-1))
    :use
    (:instance
     lofat-remove-file-correctness-lemma-1
     (x nil)))))
