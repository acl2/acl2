(in-package "ACL2")

(include-book "../eqfat")

;  lofat-place-file.lisp                                Mihir Mehta

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
 (in-theory (e/d (hifat-equiv-of-cons-lemma-5)
                 (non-free-index-list-listp-correctness-1
                  intersectp-member-when-not-member-intersectp
                  no-duplicatesp-of-member
                  free-index-list-listp-correctness-1
                  consp-of-nthcdr car-of-nthcdr
                  count-free-clusters-of-set-indices-in-fa-table-2
                  (:rewrite subsetp-implies-subsetp-cdr)
                  (:rewrite stringp-when-nonempty-stringp)
                  (:rewrite
                   acl2-numberp-of-car-when-acl2-number-listp)
                  (:rewrite
                   rationalp-of-car-when-rational-listp)
                  (:definition acl2-number-listp)
                  (:rewrite
                   flatten-subset-no-duplicatesp-lemma-2)
                  (:definition rational-listp)
                  (:rewrite true-listp-when-string-list)
                  (:rewrite integerp-of-car-when-integer-listp)
                  (:definition string-listp)
                  (:rewrite subseq-of-length-1)
                  (:rewrite assoc-of-car-when-member)
                  (:rewrite characterp-nth)
                  (:rewrite hifat-file-alist-fix-guard-lemma-1)
                  (:rewrite subsetp-member . 2)
                  (:rewrite
                   d-e-list-p-of-cdr-when-d-e-list-p)
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
                  (:rewrite
                   consp-of-assoc-of-hifat-file-alist-fix)
                  (:linear hifat-entry-count-when-hifat-subsetp)
                  (:rewrite
                   true-list-listp-of-cdr-when-true-list-listp)
                  (:rewrite not-intersectp-list-when-subsetp-2)
                  (:definition subsetp-equal)
                  (:rewrite
                   not-intersectp-list-of-set-difference$-lemma-2
                   . 1)
                  (:rewrite true-list-listp-when-not-consp)
                  (:rewrite
                   member-intersectp-is-commutative-lemma-2)
                  (:rewrite non-free-index-listp-correctness-5)
                  (:rewrite then-subseq-same-2)
                  (:rewrite
                   count-free-clusters-of-set-indices-in-fa-table-lemma-1)
                  (:linear find-n-free-clusters-correctness-1)
                  (:rewrite
                   fat32-masked-entry-list-p-when-not-consp)
                  (:rewrite
                   fat32-masked-entry-list-p-when-bounded-nat-listp)
                  (:rewrite hifat-place-file-when-hifat-equiv-1)
                  (:rewrite nat-listp-when-unsigned-byte-listp)
                  (:rewrite bounded-nat-listp-correctness-1)
                  (:rewrite hifat-subsetp-preserves-assoc)
                  (:rewrite
                   consp-of-assoc-when-hifat-equiv-lemma-1)
                  (:rewrite free-index-list-listp-of-update-nth-lemma-1)
                  (:rewrite
                   abs-find-file-correctness-1-lemma-40)))))

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
     (:rewrite put-assoc-equal-without-change . 2))))

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

  ;; hypotheses are minimised.
  (defthm
    lofat-place-file-correctness-lemma-143
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
      (< (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name)))
         (+ 2 (count-of-clusters fat32$c)))
      (integerp entry-limit)
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
           path (m1-file d-e nil))))
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
         d-e-list entry-limit)))))
    :hints
    (("goal"
      :in-theory
      (e/d
       (not-intersectp-list hifat-entry-count
                            lofat-to-hifat-helper-correctness-4)
       (lofat-place-file-correctness-lemma-75
        lofat-place-file (:definition subseq)
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
        (:rewrite lofat-place-file-correctness-lemma-57)
        (:rewrite d-e-cc-under-iff . 2)
        (:rewrite intersectp-when-subsetp)
        (:rewrite disjoint-list-listp-of-lofat-to-hifat-helper)
        (:rewrite not-intersectp-list-of-set-difference$)
        (:rewrite not-intersectp-list-when-atom)
        (:rewrite lofat-find-file-correctness-1-lemma-6)
        (:rewrite m1-file-p-of-cdar-when-m1-file-alist-p)
        (:rewrite fat32-filename-p-correctness-1)
        (:definition no-duplicatesp-equal)
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
        (:rewrite place-contents-expansion-1)
        (:rewrite lofat-to-hifat-helper-of-update-dir-contents)
        (:rewrite m1-file->contents$inline-of-m1-file-fix-x-normalize-const)
        (:type-prescription fat32-filename-fix)
        (:rewrite lofat-directory-file-p-when-lofat-file-p)
        (:rewrite fati-of-clear-cc . 3)
        (:rewrite m1-file-p-of-m1-file-fix)
        (:rewrite natp-of-place-contents)
        (:rewrite len-of-find-n-free-clusters)
        (:linear find-n-free-clusters-correctness-7)
        (:rewrite str::explode-when-not-stringp)
        (:definition min)
        (:definition stobj-find-n-free-clusters-correctness-1)
        (:rewrite set-difference$-when-not-intersectp)
        (:rewrite subsetp-member . 1)
        (:linear lofat-remove-file-correctness-1-lemma-27)
        (:rewrite lofat-place-file-correctness-lemma-42)
        (:rewrite delete-d-e-correctness-1)
        (:definition remove-assoc-equal)
        (:rewrite abs-find-file-correctness-1-lemma-40)
        (:rewrite hifat-place-file-correctness-3)
        (:rewrite remove-assoc-when-absent-1)
        (:rewrite lofat-place-file-correctness-1-lemma-68)
        (:definition find-d-e)
        (:definition lofat-to-hifat-helper)
        (:definition not-intersectp-list)
        (:rewrite m1-directory-file-p-when-m1-file-p)
        (:rewrite m1-directory-file-p-correctness-1)
        (:rewrite lofat-place-file-correctness-1-lemma-11)
        (:rewrite lofat-place-file-correctness-1-lemma-16)
        (:rewrite lofat-place-file-correctness-1-lemma-15)
        (:rewrite lofat-place-file-correctness-1-lemma-17)
        (:rewrite lofat-remove-file-correctness-lemma-14)))
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
        (< (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name)))
           (+ 2 (count-of-clusters fat32$c)))
        (integerp entry-limit)
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
      :hints (("goal" :do-not-induct t
               :in-theory (disable (:definition lofat-place-file)))))))

  ;; hypotheses are minimised.
  (defthm
    lofat-place-file-correctness-lemma-94
    (implies
     (and
      (equal
       (mv-nth 1
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
                 (lofat-to-hifat-helper fat32$c
                                        d-e-list entry-limit))
         (mv-nth
          2
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents
                     fat32$c
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
             (mv-nth
              0
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
                    (d-e-cc-contents
                     fat32$c
                     (mv-nth 0 (find-d-e d-e-list name)))))
           entry-limit))
         path
         (m1-file d-e (lofat-file->contents file)))))
      (good-root-d-e-p root-d-e fat32$c)
      (non-free-index-listp x (effective-fat fat32$c))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c
                                            d-e-list entry-limit))
             0)
      (not-intersectp-list
       (mv-nth 0
               (d-e-cc fat32$c root-d-e))
       (mv-nth 2
               (lofat-to-hifat-helper fat32$c
                                      d-e-list entry-limit)))
      (not-intersectp-list
       x
       (mv-nth 2
               (lofat-to-hifat-helper fat32$c
                                      d-e-list entry-limit)))
      (lofat-file-p file)
      (lofat-regular-file-p file)
      (<= (len (make-clusters (lofat-file->contents file)
                              (cluster-size fat32$c)))
          (count-free-clusters (effective-fat fat32$c)))
      (consp path)
      (<= 2
          (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name))))
      (< (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name)))
         (+ 2 (count-of-clusters fat32$c)))
      (integerp entry-limit)
      (< (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper fat32$c
                                         d-e-list entry-limit)))
         entry-limit)
      (useful-d-e-list-p d-e-list)
      (fat32-filename-list-p path)
      (fat32-filename-p name)
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
                (lofat-to-hifat-helper fat32$c
                                       d-e-list entry-limit))))
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         (mv-nth 0
                 (lofat-place-file fat32$c
                                   (mv-nth 0 (find-d-e d-e-list name))
                                   path file))
         d-e-list entry-limit))
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
         d-e-list entry-limit)))))
    :hints
    (("goal"
      :in-theory
      (e/d
       (not-intersectp-list hifat-entry-count
                            lofat-to-hifat-helper-correctness-4)
       (;; there's a lot of useless case-splitting because of the following
        ;; rule - disabling it should allow some of these to be handled
        ;; separately...
        lofat-place-file-correctness-lemma-75
        ;; there are some fairly dramatic differences to be seen in how acl2
        ;; creates case splits when lofat-place-file is enabled vs when it is
        ;; disabled. this seems like a good time to decide to keep this
        ;; disabled so we can take greater advantage of the information about
        ;; useless runes.
        lofat-place-file
        (:definition subseq)
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
        (:rewrite lofat-place-file-correctness-lemma-57)
        (:rewrite d-e-cc-under-iff . 2)
        (:rewrite intersectp-when-subsetp)
        (:rewrite disjoint-list-listp-of-lofat-to-hifat-helper)
        (:rewrite not-intersectp-list-of-set-difference$)
        (:rewrite not-intersectp-list-when-atom)
        (:rewrite lofat-find-file-correctness-1-lemma-6)
        (:rewrite m1-file-p-of-cdar-when-m1-file-alist-p)
        (:rewrite fat32-filename-p-correctness-1)
        (:definition no-duplicatesp-equal)
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
        (:rewrite hifat-subsetp-preserves-assoc)
        (:rewrite consp-of-assoc-when-hifat-equiv-lemma-1)
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
        (:linear length-of-d-e-cc-contents
                 . 3)
        (:rewrite unsigned-byte-listp-when-d-e-p)
        (:rewrite d-e-p-of-chars=>nats)
        (:rewrite chars=>nats-of-take)
        (:type-prescription hifat-bounded-file-alist-p)
        (:rewrite take-when-atom)
        (:definition char)
        (:rewrite explode-of-d-e-filename)
        (:linear len-when-hifat-bounded-file-alist-p . 2)
        (:linear len-when-hifat-bounded-file-alist-p . 1)
        (:linear length-of-d-e-cc-contents
                 . 2)
        (:rewrite effective-fat-of-clear-cc . 3)
        (:rewrite find-n-free-clusters-when-zp)
        (:rewrite str::consp-of-explode)
        (:rewrite hifat-to-lofat-inversion-lemma-2)
        (:rewrite m1-regular-file-p-correctness-1)
        (:type-prescription m1-file-fix$inline)
        (:rewrite place-contents-expansion-1)
        (:rewrite lofat-to-hifat-helper-of-update-dir-contents)
        (:rewrite m1-file->contents$inline-of-m1-file-fix-x-normalize-const)
        (:type-prescription fat32-filename-fix)
        (:rewrite lofat-directory-file-p-when-lofat-file-p)
        (:rewrite fati-of-clear-cc . 3)
        (:rewrite m1-file-p-of-m1-file-fix)
        (:rewrite natp-of-place-contents)
        (:rewrite len-of-find-n-free-clusters)
        (:linear find-n-free-clusters-correctness-7)
        (:rewrite str::explode-when-not-stringp)
        (:definition min)
        (:definition stobj-find-n-free-clusters-correctness-1)
        (:rewrite set-difference$-when-not-intersectp)
        (:rewrite subsetp-member . 1)
        (:linear lofat-remove-file-correctness-1-lemma-27)
        (:rewrite lofat-place-file-correctness-lemma-42)
        (:rewrite delete-d-e-correctness-1)
        (:definition remove-assoc-equal)
        (:rewrite abs-find-file-correctness-1-lemma-40)
        (:rewrite hifat-place-file-correctness-3)
        (:rewrite remove-assoc-when-absent-1)
        (:rewrite lofat-place-file-correctness-1-lemma-68)
        (:definition find-d-e)
        (:definition lofat-to-hifat-helper)
        (:definition not-intersectp-list)
        (:rewrite lofat-place-file-correctness-1-lemma-11)
        (:rewrite m1-directory-file-p-when-m1-file-p)
        (:rewrite m1-directory-file-p-correctness-1)
        (:rewrite lofat-place-file-correctness-1-lemma-17)
        (:rewrite lofat-place-file-correctness-1-lemma-16)
        (:rewrite lofat-place-file-correctness-1-lemma-15)
        (:rewrite lofat-place-file-correctness-lemma-143)
        (:type-prescription make-d-e-list)))
      :induct (induction-scheme d-e-list
                                entry-limit fat32$c x)
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c
                                             d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c
                           d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c
                                             (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name))))))

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
    (integerp entry-limit)
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
  :hints (("goal" :in-theory (disable lofat-place-file-correctness-lemma-143
                                      lofat-place-file)
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
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c root-d-e))
     (mv-nth 2
             (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
    (lofat-file-p file)
    (lofat-regular-file-p file)
    (<= (len (make-clusters (lofat-file->contents file)
                            (cluster-size fat32$c)))
        (count-free-clusters (effective-fat fat32$c)))
    (consp path)
    (integerp entry-limit)
    (< (hifat-entry-count
        (mv-nth 0
                (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
       entry-limit)
    (useful-d-e-list-p d-e-list)
    (fat32-filename-list-p path)
    (fat32-filename-p name)
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
    (disable lofat-place-file-correctness-lemma-94
             lofat-place-file
             (:rewrite d-e-cc-contents-of-lofat-place-file-coincident-1))
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
    (disable (:rewrite lofat-place-file-correctness-lemma-143)
             (:definition lofat-place-file)
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

  ;; Interesting. This now goes through with only two skipped proofs.
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
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents
                   fat32$c root-d-e)))
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
                  (d-e-cc-contents
                   fat32$c root-d-e)))
         entry-limit)))
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents
                   fat32$c root-d-e)))
         entry-limit)))
      (lofat-file-p file)
      (or
       (and
        (lofat-regular-file-p file)
        (<= (len (make-clusters (lofat-file->contents file)
                                (cluster-size fat32$c)))
            (count-free-clusters (effective-fat fat32$c))))
       (and
        (equal (lofat-file->contents file) nil)
        (<= 1
            (count-free-clusters (effective-fat fat32$c)))))
      (zp (mv-nth 1
                  (lofat-place-file fat32$c
                                    root-d-e path file)))
      (integerp entry-limit)
      (<
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents
                    fat32$c root-d-e)))
          entry-limit)))
       entry-limit))
     (and
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         (mv-nth
          0
          (lofat-place-file fat32$c root-d-e path file))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
            (mv-nth 0
                    (lofat-place-file
                     fat32$c root-d-e path file))
            root-d-e)))
         entry-limit))
       0)
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         (mv-nth
          0
          (lofat-place-file fat32$c root-d-e path file))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
            (mv-nth 0
                    (lofat-place-file
                     fat32$c root-d-e path file))
            root-d-e)))
         entry-limit)))
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth
          0
          (lofat-place-file fat32$c root-d-e path file))
         (make-d-e-list
          (mv-nth
           0
           (d-e-cc-contents
            (mv-nth 0
                    (lofat-place-file
                     fat32$c root-d-e path file))
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
            (mv-nth 0
                    (d-e-cc-contents
                     fat32$c root-d-e)))
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
            (mv-nth 0
                    (d-e-cc-contents
                     fat32$c root-d-e)))
           entry-limit))
         path
         (m1-file d-e (lofat-file->contents file))))
       0)))
    :hints
    (("goal"
      :induct
      (induction-scheme
       entry-limit fat32$c file path root-d-e x)
      :expand
      (lofat-place-file fat32$c root-d-e path file)
      :in-theory
      (e/d (hifat-place-file
            (:rewrite lofat-to-hifat-inversion-lemma-4)
            hifat-find-file)
           ((:definition find-d-e)
            (:definition place-d-e)
            (:rewrite
             d-e-p-when-member-equal-of-d-e-list-p)
            (:rewrite
             lofat-fs-p-of-lofat-place-file-lemma-1)
            (:rewrite
             clear-cc-reversibility-lemma-1)
            ;; This lemma leads to specious simplifications.
            (:rewrite
             d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
             . 5)))
      ;; we can add more of these restrict bindings if needed... but right now
      ;; we want to save space.
      :restrict
      ((put-assoc-under-hifat-equiv-3
        ((file2
          (m1-file d-e "")))
        ((file2 (m1-file d-e
                         (lofat-file->contents$inline file))))))))))
