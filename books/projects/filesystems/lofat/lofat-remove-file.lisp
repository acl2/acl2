(in-package "ACL2")

(include-book "../eqfat")

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
   (hifat-equiv-of-cons-lemma-5)
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
    (:rewrite flatten-subset-no-duplicatesp-lemma-2)
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
    (:rewrite hifat-place-file-when-hifat-equiv-1)
    (:rewrite nat-listp-when-unsigned-byte-listp)
    (:rewrite bounded-nat-listp-correctness-1)
    (:rewrite hifat-subsetp-preserves-assoc)
    (:rewrite consp-of-assoc-when-hifat-equiv-lemma-1)
    (:rewrite free-index-list-listp-of-update-nth-lemma-1)
    (:rewrite abs-find-file-correctness-1-lemma-40)
    (:rewrite lofat-place-file-correctness-1-lemma-13)
    (:rewrite lofat-place-file-correctness-1-lemma-14)
    (:rewrite
     d-e-cc-contents-of-lofat-place-file-coincident-lemma-13)
    (:rewrite nth-of-nats=>chars)))))

(defund stobj-disjoins-list
  (fat32$c d-e-list entry-limit x)
  (declare (xargs :stobjs fat32$c :verify-guards nil))
  (b*
      (((mv & & cc-list error-code)
        (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
    (and (zp error-code)
         (not-intersectp-list x cc-list))))

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
      (:rewrite lofat-place-file-correctness-lemma-57)
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
      (:rewrite subsetp-car-member)
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
      (:rewrite put-assoc-equal-without-change . 2)
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

  (local (include-book "std/lists/intersectp" :dir :system))

  (defthm
    lofat-remove-file-correctness-lemma-45
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
       entry-limit2
       (append
        x
        (mv-nth 0
                (d-e-cc fat32$c
                        (mv-nth 0 (find-d-e d-e-list filename))))
        (flatten
         (mv-nth 2
                 (lofat-to-hifat-helper fat32$c (delete-d-e d-e-list filename)
                                        entry-limit1)))))
      (integerp entry-limit2)
      (< (nfix entry-limit1) entry-limit2)
      (useful-d-e-list-p d-e-list)
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
             0)
      (d-e-directory-p (mv-nth 0 (find-d-e d-e-list filename)))
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
          entry-limit2)))
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents fat32$c
                                    (mv-nth 0 (find-d-e d-e-list filename)))))
          entry-limit2)))))
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
         entry-limit1)))
      (hifat-entry-count
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents fat32$c
                                   (mv-nth 0 (find-d-e d-e-list filename)))))
         entry-limit1)))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d
       (stobj-disjoins-list lofat-to-hifat-helper-correctness-4)
       ((:rewrite lofat-remove-file-correctness-lemma-25)
        (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-2)
        (:rewrite lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2
                  . 1)
        (:linear lofat-remove-file-correctness-lemma-22)))))
    :rule-classes :linear)

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
        (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-2)
        (:rewrite lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2
                  . 1)
        (:linear lofat-remove-file-correctness-lemma-22))))))

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
        (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-2)
        (:rewrite lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2
                  . 1)
        (:linear lofat-remove-file-correctness-lemma-22))))))

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
        (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-2)
        (:rewrite lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2
                  . 1)
        (:linear lofat-remove-file-correctness-lemma-22))))))

  (defthm
    lofat-remove-file-correctness-lemma-49
    (implies
     (and
      (not (d-e-directory-p (car d-e-list)))
      (< (d-e-first-cluster (car d-e-list)) 2)
      (lofat-remove-file-spec-1
       fat32$c (cdr d-e-list)
       (+ -1 entry-limit)
       x
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
         (+ -1 entry-limit)))
       filename path
       (mv-nth 0 (find-d-e (cdr d-e-list) filename)))
      (useful-d-e-list-p d-e-list)
      (not (equal (mv-nth 1
                          (find-d-e (cdr d-e-list)
                                    (d-e-filename (car d-e-list))))
                  0))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                            (+ -1 entry-limit)))
             0)
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) filename))))
     (lofat-remove-file-spec-1
      fat32$c d-e-list entry-limit x
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-remove-file fat32$c
                                   (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                                   path))
        (make-d-e-list
         (mv-nth
          0
          (d-e-cc-contents fat32$c
                           (mv-nth 0 (find-d-e (cdr d-e-list) filename)))))
        entry-limit))
      filename path
      (mv-nth 0 (find-d-e (cdr d-e-list) filename))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d
       (lofat-remove-file-spec-1)
       ((:rewrite lofat-remove-file-correctness-lemma-25)
        (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-2)
        (:rewrite lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2
                  . 1)
        (:linear lofat-remove-file-correctness-lemma-22))))))

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
        (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-2)
        (:rewrite lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2
                  . 1)
        (:linear lofat-remove-file-correctness-lemma-22))))))

  (defthm
    lofat-remove-file-correctness-lemma-51
    (implies
     (and
      (not (d-e-directory-p (car d-e-list)))
      (<= (+ 2 (count-of-clusters fat32$c))
          (d-e-first-cluster (car d-e-list)))
      (lofat-remove-file-spec-1
       fat32$c (cdr d-e-list)
       (+ -1 entry-limit)
       x
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
         (+ -1 entry-limit)))
       filename path
       (mv-nth 0 (find-d-e (cdr d-e-list) filename)))
      (useful-d-e-list-p d-e-list)
      (not (equal (mv-nth 1
                          (find-d-e (cdr d-e-list)
                                    (d-e-filename (car d-e-list))))
                  0))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c (cdr d-e-list)
                                            (+ -1 entry-limit)))
             0)
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) filename))))
     (lofat-remove-file-spec-1
      fat32$c d-e-list entry-limit x
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-remove-file fat32$c
                                   (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                                   path))
        (make-d-e-list
         (mv-nth
          0
          (d-e-cc-contents fat32$c
                           (mv-nth 0 (find-d-e (cdr d-e-list) filename)))))
        entry-limit))
      filename path
      (mv-nth 0 (find-d-e (cdr d-e-list) filename))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d
       (lofat-remove-file-spec-1)
       ((:rewrite lofat-remove-file-correctness-lemma-25)
        (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-2)
        (:rewrite lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2
                  . 1)
        (:linear lofat-remove-file-correctness-lemma-22))))))

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
            (:rewrite lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2
                      . 1)
            (:linear lofat-remove-file-correctness-lemma-22)
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
            (:rewrite lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2
                      . 1)
            (:linear lofat-remove-file-correctness-lemma-22)
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
            (:rewrite lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2
                      . 1)
            (:linear lofat-remove-file-correctness-lemma-22)
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
        (:rewrite
         lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2
         . 1)
        (:rewrite
         d-e-cc-contents-of-lofat-place-file-coincident-lemma-13)
        (:linear lofat-remove-file-correctness-lemma-22)
        (:linear nth-when-d-e-p))))))

  (defthm
    lofat-remove-file-correctness-lemma-56
    (implies
     (and
      (not (d-e-directory-p (car d-e-list)))
      (lofat-remove-file-spec-1
       fat32$c (cdr d-e-list)
       (+ -1 entry-limit)
       (append (mv-nth 0 (d-e-cc fat32$c (car d-e-list)))
               x)
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
         (+ -1 entry-limit)))
       filename path
       (mv-nth 0 (find-d-e (cdr d-e-list) filename)))
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
     (lofat-remove-file-spec-1
      fat32$c d-e-list entry-limit x
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
        entry-limit))
      filename path
      (mv-nth 0 (find-d-e (cdr d-e-list) filename))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d
       (lofat-remove-file-spec-1)
       ((:rewrite lofat-remove-file-correctness-lemma-25)
        (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-2)
        (:rewrite lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2
                  . 1)
        (:linear lofat-remove-file-correctness-lemma-22))))))

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
        (:rewrite lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2
                  . 1)
        (:linear lofat-remove-file-correctness-lemma-22)
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
    lofat-remove-file-correctness-lemma-58
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
     (iff
      (equal
       (mv-nth 0
               (lofat-to-hifat-helper
                (mv-nth 0
                        (lofat-remove-file fat32$c (car d-e-list)
                                           path))
                d-e-list entry-limit))
       (cons
        (cons
         (d-e-filename (car d-e-list))
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
            entry-limit))))
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
      t))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d
       (stobj-disjoins-list lofat-to-hifat-helper-correctness-4
                            not-intersectp-list)
       ((:rewrite lofat-remove-file-correctness-lemma-25)
        (:rewrite lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2
                  . 1)
        (:linear lofat-remove-file-correctness-lemma-22)
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
    lofat-remove-file-correctness-lemma-59
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
     (iff
      (equal
       (mv-nth 0
               (lofat-to-hifat-helper
                (mv-nth 0
                        (lofat-remove-file fat32$c (car d-e-list)
                                           path))
                d-e-list entry-limit))
       (cons
        (cons
         (d-e-filename (car d-e-list))
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
            entry-limit))))
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
      t))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d
       (stobj-disjoins-list lofat-to-hifat-helper-correctness-4
                            not-intersectp-list)
       ((:rewrite lofat-remove-file-correctness-lemma-25)
        (:rewrite lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2
                  . 1)
        (:linear lofat-remove-file-correctness-lemma-22)
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
    lofat-remove-file-correctness-lemma-60
    (implies
     (and
      (d-e-directory-p (car d-e-list))
      (<= 2 (d-e-first-cluster (car d-e-list)))
      (< (d-e-first-cluster (car d-e-list))
         (+ 2 (count-of-clusters fat32$c)))
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
              (+ -1 entry-limit))))))))))
     (lofat-remove-file-spec-1
      fat32$c d-e-list entry-limit x
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth 0
                (lofat-remove-file fat32$c (car d-e-list)
                                   path))
        (make-d-e-list (mv-nth 0
                               (d-e-cc-contents fat32$c (car d-e-list))))
        entry-limit))
      (d-e-filename (car d-e-list))
      path (car d-e-list)))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d
       (lofat-remove-file-spec-1)
       ((:rewrite lofat-remove-file-correctness-lemma-25)
        (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-2)
        (:rewrite lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2
                  . 1)
        (:linear lofat-remove-file-correctness-lemma-22))))))

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
        (:rewrite lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2
                  . 1)
        (:linear lofat-remove-file-correctness-lemma-22)
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
    lofat-remove-file-correctness-lemma-62
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
         (+ -1 entry-limit)))))
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
       ((:linear lofat-remove-file-correctness-lemma-22)
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
    lofat-remove-file-correctness-lemma-63
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
      (d-e-directory-p (car d-e-list))
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
      (d-e-directory-p (mv-nth 0 (find-d-e (cdr d-e-list) filename))))
     (equal
      (mv-nth
       0
       (lofat-to-hifat-helper
        (mv-nth
         0
         (lofat-remove-file fat32$c
                            (mv-nth 0 (find-d-e (cdr d-e-list) filename))
                            path))
        d-e-list entry-limit))
      (cons
       (cons
        (d-e-filename (car d-e-list))
        (m1-file-hifat-file-alist-fix
         (car d-e-list)
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list (mv-nth 0
                                  (d-e-cc-contents fat32$c (car d-e-list))))
           (+ -1 entry-limit)))))
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
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents fat32$c (car d-e-list))))
               (+ -1 entry-limit))))))))))))
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
       ((:linear lofat-remove-file-correctness-lemma-22)
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
    lofat-remove-file-correctness-lemma-64
    (implies
     (and
      (d-e-directory-p (car d-e-list))
      (<= 2 (d-e-first-cluster (car d-e-list)))
      (< (d-e-first-cluster (car d-e-list))
         (+ 2 (count-of-clusters fat32$c)))
      (lofat-remove-file-spec-1
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
        x)
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
              (make-d-e-list (mv-nth 0
                                     (d-e-cc-contents fat32$c (car d-e-list))))
              (+ -1 entry-limit))))))))
       filename path
       (mv-nth 0 (find-d-e (cdr d-e-list) filename)))
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
         (+ -1 entry-limit)))))
     (lofat-remove-file-spec-1
      fat32$c d-e-list entry-limit x
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
        entry-limit))
      filename path
      (mv-nth 0 (find-d-e (cdr d-e-list) filename))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d
       (lofat-remove-file-spec-1)
       ((:rewrite lofat-remove-file-correctness-lemma-25)
        (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-2)
        (:rewrite lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2
                  . 1)
        (:linear lofat-remove-file-correctness-lemma-22))))))

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
       (:rewrite lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2
                 . 1)
       (:rewrite member-intersectp-is-commutative)
       (:linear nth-when-d-e-p)
       (:rewrite lofat-place-file-correctness-lemma-83))))
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
    :in-theory (disable
                lofat-remove-file-correctness-lemma-1)
    :use
    (:instance
     lofat-remove-file-correctness-lemma-1
     (x nil)))))
