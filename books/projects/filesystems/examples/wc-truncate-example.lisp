(in-package "ACL2")

(include-book "../test-stuff")

(defun
    truncate-list-extra-hypothesis
    (fat32$c name-list size)
  (declare (xargs :stobjs fat32$c
                  :guard (and (lofat-fs-p fat32$c)
                              (string-listp name-list)
                              (natp size))
                  :guard-hints (("Goal" :in-theory (enable hifat-no-dups-p)))
                  :measure (len name-list)))
  (b*
      (((when (atom name-list))
        (mv fat32$c t))
       (fat32-path (path-to-fat32-path
                        (coerce (car name-list) 'list)))
       ((unless (fat32-filename-list-p fat32-path))
        (mv fat32$c nil))
       ((mv fs error-code)
        (lofat-to-hifat fat32$c))
       ((unless (equal error-code 0))
        (mv fat32$c nil))
       ((mv fs retval &)
        (hifat-truncate fs fat32-path size))
       ((unless (and (equal retval 0)
                     (hifat-bounded-file-alist-p fs)
                     (<= (hifat-entry-count fs) (max-entry-count fat32$c))))
        (mv fat32$c nil))
       ((mv fat32$c error-code)
        (hifat-to-lofat fat32$c fs))
       ((unless (equal error-code 0))
        (mv fat32$c nil)))
    (truncate-list-extra-hypothesis fat32$c (cdr name-list) size)))

(defthm
  truncate-list-correctness-1-lemma-1
  (implies
   (lofat-fs-p fat32$c)
   (lofat-fs-p
    (mv-nth 0
            (truncate-list fat32$c
                           name-list size exit-status)))))

(defthm
  truncate-list-correctness-1-lemma-2
  (implies
   (and (lofat-fs-p fat32$c)
        (hifat-bounded-file-alist-p fs)
        (<= (hifat-entry-count fs)
            (max-entry-count fat32$c))
        (zp (mv-nth 1 (hifat-to-lofat fat32$c fs)))
        (m1-file-alist-p fs)
        (hifat-no-dups-p fs)
        (m1-regular-file-p (mv-nth 0 (hifat-find-file fs path))))
   (equal
    (m1-file->contents
     (mv-nth
      0
      (hifat-find-file
       (mv-nth
        0
        (lofat-to-hifat (mv-nth 0 (hifat-to-lofat fat32$c fs))))
       path)))
    (m1-file->contents (mv-nth 0
                               (hifat-find-file fs path)))))
  :hints
  (("goal"
    :in-theory (disable hifat-find-file-correctness-3)
    :use
    (:instance
     hifat-find-file-correctness-3
     (m1-file-alist1 fs)
     (m1-file-alist2
      (mv-nth
       0
       (lofat-to-hifat (mv-nth 0
                               (hifat-to-lofat fat32$c fs)))))))))

(defthm
  truncate-list-correctness-1-lemma-4
  (implies
   (and
    (consp path-list)
    (not
     (equal
      (mv-nth
       1
       (hifat-find-file
        (mv-nth 0 (lofat-to-hifat fat32$c))
        (path-to-fat32-path (explode (car path-list)))))
      0))
    (equal
     (mv-nth
      1
      (hifat-place-file
       (mv-nth 0 (lofat-to-hifat fat32$c))
       (path-to-fat32-path (explode (car path-list)))
       (m1-file
        '(0 0 0 0 0 0 0 0 0 0 0 0
            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
        (implode
         (repeat
          (len
           (explode
            (m1-file->contents
             (mv-nth 0
                     (hifat-find-file
                      (mv-nth 0 (lofat-to-hifat fat32$c))
                      (path-to-fat32-path (explode path)))))))
          nil)))))
     0)
    (lofat-fs-p fat32$c)
    (equal
     (mv-nth
      1
      (hifat-find-file (mv-nth 0 (lofat-to-hifat fat32$c))
                       (path-to-fat32-path (explode path))))
     0)
    (m1-regular-file-p
     (mv-nth 0
             (hifat-find-file
              (mv-nth 0 (lofat-to-hifat fat32$c))
              (path-to-fat32-path (explode path)))))
    (mv-nth
     1
     (truncate-list-extra-hypothesis
      fat32$c path-list
      (len
       (explode
        (m1-file->contents
         (mv-nth 0
                 (hifat-find-file
                  (mv-nth 0 (lofat-to-hifat fat32$c))
                  (path-to-fat32-path (explode path))))))))))
   (equal
    (len
     (explode
      (m1-file->contents
       (mv-nth
        0
        (hifat-find-file
         (mv-nth
          0
          (lofat-to-hifat
           (mv-nth
            0
            (hifat-to-lofat
             fat32$c
             (mv-nth
              0
              (hifat-place-file
               (mv-nth 0 (lofat-to-hifat fat32$c))
               (path-to-fat32-path (explode (car path-list)))
               (m1-file
                '(0 0 0 0 0 0 0 0 0 0 0 0
                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                (implode
                 (repeat
                  (len
                   (explode
                    (m1-file->contents
                     (mv-nth
                      0
                      (hifat-find-file
                       (mv-nth 0 (lofat-to-hifat fat32$c))
                       (path-to-fat32-path (explode path)))))))
                  nil)))))))))
         (path-to-fat32-path (explode path)))))))
    (len
     (explode
      (m1-file->contents
       (mv-nth 0
               (hifat-find-file
                (mv-nth 0 (lofat-to-hifat fat32$c))
                (path-to-fat32-path (explode path)))))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d
                (hifat-no-dups-p)
                (truncate-list-correctness-1-lemma-2))
    :use
    (:instance
     truncate-list-correctness-1-lemma-2
     (path (path-to-fat32-path (explode path)))
     (fs
      (mv-nth
       0
       (hifat-place-file
        (mv-nth 0 (lofat-to-hifat fat32$c))
        (path-to-fat32-path (explode (car path-list)))
        (m1-file
         '(0 0 0 0 0 0 0 0 0 0 0 0
             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
         (implode
          (repeat
           (len
            (explode
             (m1-file->contents
              (mv-nth
               0
               (hifat-find-file
                (mv-nth 0 (lofat-to-hifat fat32$c))
                (path-to-fat32-path (explode path)))))))
           nil))))))))))

;; (defthm
;;   truncate-list-correctness-1-lemma-6
;;   (implies
;;    (and
;;     (equal
;;      (mv-nth 1
;;              (hifat-find-file
;;               (mv-nth 0 (lofat-to-hifat fat32$c))
;;               (path-to-fat32-path (explode (car path-list)))))
;;      0)
;;     (not
;;      (m1-directory-file-p
;;       (mv-nth
;;        0
;;        (hifat-find-file
;;         (mv-nth 0 (lofat-to-hifat fat32$c))
;;         (path-to-fat32-path (explode (car path-list)))))))
;;     (equal
;;      (mv-nth
;;       1
;;       (hifat-place-file
;;        (mv-nth 0 (lofat-to-hifat fat32$c))
;;        (path-to-fat32-path (explode (car path-list)))
;;        (m1-file
;;         (m1-file->d-e
;;          (mv-nth
;;           0
;;           (hifat-find-file
;;            (mv-nth 0 (lofat-to-hifat fat32$c))
;;            (path-to-fat32-path (explode (car path-list))))))
;;         (implode
;;          (take
;;           (len
;;            (explode
;;             (m1-file->contents
;;              (mv-nth 0
;;                      (hifat-find-file
;;                       (mv-nth 0 (lofat-to-hifat fat32$c))
;;                       (path-to-fat32-path (explode path)))))))
;;           (explode
;;            (m1-file->contents
;;             (mv-nth 0
;;                     (hifat-find-file
;;                      (mv-nth 0 (lofat-to-hifat fat32$c))
;;                      (path-to-fat32-path
;;                       (explode (car path-list))))))))))))
;;      0)
;;     (lofat-fs-p fat32$c)
;;     (equal
;;      (mv-nth
;;       1
;;       (hifat-find-file (mv-nth 0 (lofat-to-hifat fat32$c))
;;                        (path-to-fat32-path (explode path))))
;;      0)
;;     (m1-regular-file-p
;;      (mv-nth 0
;;              (hifat-find-file
;;               (mv-nth 0 (lofat-to-hifat fat32$c))
;;               (path-to-fat32-path (explode path)))))
;;     (mv-nth
;;      1
;;      (truncate-list-extra-hypothesis
;;       fat32$c path-list
;;       (len
;;        (explode
;;         (m1-file->contents
;;          (mv-nth 0
;;                  (hifat-find-file
;;                   (mv-nth 0 (lofat-to-hifat fat32$c))
;;                   (path-to-fat32-path (explode path))))))))))
;;    (equal
;;     (len
;;      (explode
;;       (m1-file->contents
;;        (mv-nth
;;         0
;;         (hifat-find-file
;;          (mv-nth
;;           0
;;           (lofat-to-hifat
;;            (mv-nth
;;             0
;;             (hifat-to-lofat
;;              fat32$c
;;              (mv-nth
;;               0
;;               (hifat-place-file
;;                (mv-nth 0 (lofat-to-hifat fat32$c))
;;                (path-to-fat32-path (explode (car path-list)))
;;                (m1-file
;;                 (m1-file->d-e
;;                  (mv-nth 0
;;                          (hifat-find-file
;;                           (mv-nth 0 (lofat-to-hifat fat32$c))
;;                           (path-to-fat32-path
;;                            (explode (car path-list))))))
;;                 (implode
;;                  (take
;;                   (len
;;                    (explode
;;                     (m1-file->contents
;;                      (mv-nth
;;                       0
;;                       (hifat-find-file
;;                        (mv-nth 0 (lofat-to-hifat fat32$c))
;;                        (path-to-fat32-path (explode path)))))))
;;                   (explode
;;                    (m1-file->contents
;;                     (mv-nth
;;                      0
;;                      (hifat-find-file
;;                       (mv-nth 0 (lofat-to-hifat fat32$c))
;;                       (path-to-fat32-path
;;                        (explode (car path-list))))))))))))))))
;;          (path-to-fat32-path (explode path)))))))
;;     (len
;;      (explode
;;       (m1-file->contents
;;        (mv-nth 0
;;                (hifat-find-file
;;                 (mv-nth 0 (lofat-to-hifat fat32$c))
;;                 (path-to-fat32-path (explode path)))))))))
;;   :hints
;;   (("goal"
;;     :in-theory (e/d (hifat-find-file hifat-no-dups-p)
;;                     ((:rewrite truncate-list-correctness-1-lemma-2)))
;;     :use
;;     (:instance
;;      (:rewrite truncate-list-correctness-1-lemma-2)
;;      (path (path-to-fat32-path (explode path)))
;;      (fs
;;       (mv-nth
;;        0
;;        (hifat-place-file
;;         (mv-nth 0 (lofat-to-hifat fat32$c))
;;         (path-to-fat32-path (explode (car path-list)))
;;         (m1-file
;;          (m1-file->d-e
;;           (mv-nth
;;            0
;;            (hifat-find-file
;;             (mv-nth 0 (lofat-to-hifat fat32$c))
;;             (path-to-fat32-path (explode (car path-list))))))
;;          (implode
;;           (take
;;            (len
;;             (explode
;;              (m1-file->contents
;;               (mv-nth
;;                0
;;                (hifat-find-file
;;                 (mv-nth 0 (lofat-to-hifat fat32$c))
;;                 (path-to-fat32-path (explode path)))))))
;;            (explode
;;             (m1-file->contents
;;              (mv-nth 0
;;                      (hifat-find-file
;;                       (mv-nth 0 (lofat-to-hifat fat32$c))
;;                       (path-to-fat32-path
;;                        (explode (car path-list)))))))))))))
;;      (fat32$c fat32$c)))))

;; (defthm
;;   truncate-list-correctness-1-lemma-3
;;   (implies
;;    (and
;;     (lofat-fs-p fat32$c)
;;     (equal
;;      (mv-nth
;;       1
;;       (hifat-find-file
;;        (mv-nth 0 (lofat-to-hifat fat32$c))
;;        (path-to-fat32-path (explode path))))
;;      0)
;;     (m1-regular-file-p
;;      (mv-nth
;;       0
;;       (hifat-find-file
;;        (mv-nth 0 (lofat-to-hifat fat32$c))
;;        (path-to-fat32-path (explode path)))))
;;     (equal
;;      (len
;;       (explode
;;        (m1-file->contents
;;         (mv-nth
;;          0
;;          (hifat-find-file
;;           (mv-nth 0 (lofat-to-hifat fat32$c))
;;           (path-to-fat32-path (explode path)))))))
;;      size)
;;     (not
;;      (null (mv-nth 1
;;                    (truncate-list-extra-hypothesis
;;                     fat32$c path-list size)))))
;;    (and
;;     (equal
;;      (mv-nth
;;       1
;;       (hifat-find-file
;;        (mv-nth
;;         0
;;         (lofat-to-hifat
;;          (mv-nth
;;           0
;;           (truncate-list fat32$c
;;                          path-list size exit-status))))
;;        (path-to-fat32-path (explode path))))
;;      0)
;;     (m1-regular-file-p
;;      (mv-nth
;;       0
;;       (hifat-find-file
;;        (mv-nth
;;         0
;;         (lofat-to-hifat
;;          (mv-nth
;;           0
;;           (truncate-list fat32$c
;;                          path-list size exit-status))))
;;        (path-to-fat32-path (explode path)))))
;;     (equal
;;      (len
;;       (explode
;;        (m1-file->contents
;;         (mv-nth
;;          0
;;          (hifat-find-file
;;           (mv-nth
;;            0
;;            (lofat-to-hifat
;;             (mv-nth
;;              0
;;              (truncate-list fat32$c
;;                             path-list size exit-status))))
;;           (path-to-fat32-path (explode path)))))))
;;      size)))
;;   :hints
;;   (("goal"
;;     :induct (truncate-list fat32$c
;;                            path-list size exit-status)
;;     :in-theory
;;     (e/d
;;      (lofat-truncate hifat-no-dups-p)
;;      ((:rewrite take-of-take-split)
;;       (:linear len-of-member)
;;       (:rewrite fat32-filename-fix-when-fat32-filename-p)
;;       (:rewrite str::make-character-list-when-character-listp)
;;       (:rewrite hifat-to-lofat-inversion-lemma-2)
;;       (:definition take))))))

;; (defthm
;;   truncate-list-correctness-1-lemma-5
;;   (implies
;;    (and
;;     (lofat-fs-p fat32$c)
;;     (integerp size)
;;     (<= 0 size)
;;     (< size 4294967296)
;;     (equal
;;      (mv-nth 1
;;              (hifat-find-file
;;               (mv-nth 0 (lofat-to-hifat fat32$c))
;;               (path-to-fat32-path (explode (car path-list)))))
;;      0)
;;     (not
;;      (m1-directory-file-p
;;       (mv-nth
;;        0
;;        (hifat-find-file
;;         (mv-nth 0 (lofat-to-hifat fat32$c))
;;         (path-to-fat32-path (explode (car path-list)))))))
;;     (equal
;;      (mv-nth
;;       1
;;       (hifat-place-file
;;        (mv-nth 0 (lofat-to-hifat fat32$c))
;;        (path-to-fat32-path (explode (car path-list)))
;;        (m1-file
;;         (m1-file->d-e
;;          (mv-nth
;;           0
;;           (hifat-find-file
;;            (mv-nth 0 (lofat-to-hifat fat32$c))
;;            (path-to-fat32-path (explode (car path-list))))))
;;         (implode
;;          (take
;;           size
;;           (explode
;;            (m1-file->contents
;;             (mv-nth 0
;;                     (hifat-find-file
;;                      (mv-nth 0 (lofat-to-hifat fat32$c))
;;                      (path-to-fat32-path
;;                       (explode (car path-list))))))))))))
;;      0)
;;     (hifat-bounded-file-alist-p
;;      (mv-nth
;;       0
;;       (hifat-place-file
;;        (mv-nth 0 (lofat-to-hifat fat32$c))
;;        (path-to-fat32-path (explode (car path-list)))
;;        (m1-file
;;         (m1-file->d-e
;;          (mv-nth
;;           0
;;           (hifat-find-file
;;            (mv-nth 0 (lofat-to-hifat fat32$c))
;;            (path-to-fat32-path (explode (car path-list))))))
;;         (implode
;;          (take
;;           size
;;           (explode
;;            (m1-file->contents
;;             (mv-nth 0
;;                     (hifat-find-file
;;                      (mv-nth 0 (lofat-to-hifat fat32$c))
;;                      (path-to-fat32-path
;;                       (explode (car path-list)))))))))))))
;;     (<=
;;      (hifat-entry-count
;;       (mv-nth
;;        0
;;        (hifat-place-file
;;         (mv-nth 0 (lofat-to-hifat fat32$c))
;;         (path-to-fat32-path (explode (car path-list)))
;;         (m1-file
;;          (m1-file->d-e
;;           (mv-nth
;;            0
;;            (hifat-find-file
;;             (mv-nth 0 (lofat-to-hifat fat32$c))
;;             (path-to-fat32-path (explode (car path-list))))))
;;          (implode
;;           (take
;;            size
;;            (explode
;;             (m1-file->contents
;;              (mv-nth 0
;;                      (hifat-find-file
;;                       (mv-nth 0 (lofat-to-hifat fat32$c))
;;                       (path-to-fat32-path
;;                        (explode (car path-list)))))))))))))
;;      (max-entry-count fat32$c))
;;     (equal
;;      (mv-nth
;;       1
;;       (hifat-to-lofat
;;        fat32$c
;;        (mv-nth
;;         0
;;         (hifat-place-file
;;          (mv-nth 0 (lofat-to-hifat fat32$c))
;;          (path-to-fat32-path (explode (car path-list)))
;;          (m1-file
;;           (m1-file->d-e
;;            (mv-nth
;;             0
;;             (hifat-find-file
;;              (mv-nth 0 (lofat-to-hifat fat32$c))
;;              (path-to-fat32-path (explode (car path-list))))))
;;           (implode
;;            (take
;;             size
;;             (explode
;;              (m1-file->contents
;;               (mv-nth 0
;;                       (hifat-find-file
;;                        (mv-nth 0 (lofat-to-hifat fat32$c))
;;                        (path-to-fat32-path
;;                         (explode (car path-list))))))))))))))
;;      0)
;;     (mv-nth
;;      1
;;      (truncate-list-extra-hypothesis
;;       (mv-nth
;;        0
;;        (hifat-to-lofat
;;         fat32$c
;;         (mv-nth
;;          0
;;          (hifat-place-file
;;           (mv-nth 0 (lofat-to-hifat fat32$c))
;;           (path-to-fat32-path (explode (car path-list)))
;;           (m1-file
;;            (m1-file->d-e
;;             (mv-nth
;;              0
;;              (hifat-find-file
;;               (mv-nth 0 (lofat-to-hifat fat32$c))
;;               (path-to-fat32-path (explode (car path-list))))))
;;            (implode
;;             (take
;;              size
;;              (explode
;;               (m1-file->contents
;;                (mv-nth 0
;;                        (hifat-find-file
;;                         (mv-nth 0 (lofat-to-hifat fat32$c))
;;                         (path-to-fat32-path
;;                          (explode (car path-list))))))))))))))
;;       (cdr path-list)
;;       size)))
;;    (and
;;     (equal
;;      (mv-nth
;;       1
;;       (hifat-find-file
;;        (mv-nth
;;         0
;;         (lofat-to-hifat
;;          (mv-nth
;;           0
;;           (truncate-list
;;            (mv-nth
;;             0
;;             (hifat-to-lofat
;;              fat32$c
;;              (mv-nth
;;               0
;;               (hifat-place-file
;;                (mv-nth 0 (lofat-to-hifat fat32$c))
;;                (path-to-fat32-path (explode (car path-list)))
;;                (m1-file
;;                 (m1-file->d-e
;;                  (mv-nth 0
;;                          (hifat-find-file
;;                           (mv-nth 0 (lofat-to-hifat fat32$c))
;;                           (path-to-fat32-path
;;                            (explode (car path-list))))))
;;                 (implode
;;                  (take
;;                   size
;;                   (explode
;;                    (m1-file->contents
;;                     (mv-nth 0
;;                             (hifat-find-file
;;                              (mv-nth 0 (lofat-to-hifat fat32$c))
;;                              (path-to-fat32-path
;;                               (explode (car path-list))))))))))))))
;;            (cdr path-list)
;;            size exit-status))))
;;        (path-to-fat32-path (explode (car path-list)))))
;;      0)
;;     (m1-regular-file-p
;;      (mv-nth
;;       0
;;       (hifat-find-file
;;        (mv-nth
;;         0
;;         (lofat-to-hifat
;;          (mv-nth
;;           0
;;           (truncate-list
;;            (mv-nth
;;             0
;;             (hifat-to-lofat
;;              fat32$c
;;              (mv-nth
;;               0
;;               (hifat-place-file
;;                (mv-nth 0 (lofat-to-hifat fat32$c))
;;                (path-to-fat32-path (explode (car path-list)))
;;                (m1-file
;;                 (m1-file->d-e
;;                  (mv-nth 0
;;                          (hifat-find-file
;;                           (mv-nth 0 (lofat-to-hifat fat32$c))
;;                           (path-to-fat32-path
;;                            (explode (car path-list))))))
;;                 (implode
;;                  (take
;;                   size
;;                   (explode
;;                    (m1-file->contents
;;                     (mv-nth 0
;;                             (hifat-find-file
;;                              (mv-nth 0 (lofat-to-hifat fat32$c))
;;                              (path-to-fat32-path
;;                               (explode (car path-list))))))))))))))
;;            (cdr path-list)
;;            size exit-status))))
;;        (path-to-fat32-path (explode (car path-list))))))
;;     (equal
;;      (len
;;       (explode
;;        (m1-file->contents
;;         (mv-nth
;;          0
;;          (hifat-find-file
;;           (mv-nth
;;            0
;;            (lofat-to-hifat
;;             (mv-nth
;;              0
;;              (truncate-list
;;               (mv-nth
;;                0
;;                (hifat-to-lofat
;;                 fat32$c
;;                 (mv-nth
;;                  0
;;                  (hifat-place-file
;;                   (mv-nth 0 (lofat-to-hifat fat32$c))
;;                   (path-to-fat32-path (explode (car path-list)))
;;                   (m1-file
;;                    (m1-file->d-e
;;                     (mv-nth 0
;;                             (hifat-find-file
;;                              (mv-nth 0 (lofat-to-hifat fat32$c))
;;                              (path-to-fat32-path
;;                               (explode (car path-list))))))
;;                    (implode
;;                     (take
;;                      size
;;                      (explode
;;                       (m1-file->contents
;;                        (mv-nth 0
;;                                (hifat-find-file
;;                                 (mv-nth 0 (lofat-to-hifat fat32$c))
;;                                 (path-to-fat32-path
;;                                  (explode (car path-list))))))))))))))
;;               (cdr path-list)
;;               size exit-status))))
;;           (path-to-fat32-path (explode (car path-list))))))))
;;      size)))
;;   :hints
;;   (("goal"
;;     :in-theory (e/d
;;                 (hifat-no-dups-p)
;;                 ((:rewrite m1-directory-file-p-when-m1-file-p)))
;;     :use
;;     (:instance
;;      (:rewrite m1-directory-file-p-when-m1-file-p)
;;      (x
;;       (mv-nth
;;        0
;;        (hifat-find-file
;;         (mv-nth 0 (lofat-to-hifat fat32$c))
;;         (path-to-fat32-path (explode (car path-list))))))))))

;; (defthm
;;   truncate-list-correctness-1
;;   (implies
;;    (and
;;     (lofat-fs-p fat32$c)
;;     (member-equal path path-list)
;;     (not
;;      (null
;;       (mv-nth
;;        1
;;        (truncate-list-extra-hypothesis fat32$c path-list size)))))
;;    (and
;;     (equal
;;      (mv-nth
;;       1
;;       (hifat-find-file
;;        (mv-nth 0
;;                (lofat-to-hifat
;;                 (mv-nth 0
;;                         (truncate-list fat32$c
;;                                        path-list size exit-status))))
;;        (path-to-fat32-path (explode path))))
;;      0)
;;     (m1-regular-file-p
;;      (mv-nth
;;       0
;;       (hifat-find-file
;;        (mv-nth 0
;;                (lofat-to-hifat
;;                 (mv-nth 0
;;                         (truncate-list fat32$c
;;                                        path-list size exit-status))))
;;        (path-to-fat32-path (explode path)))))
;;     (equal
;;      (len
;;       (explode
;;        (m1-file->contents
;;         (mv-nth
;;          0
;;          (hifat-find-file
;;           (mv-nth 0
;;                   (lofat-to-hifat
;;                    (mv-nth 0
;;                            (truncate-list fat32$c
;;                                           path-list size exit-status))))
;;           (path-to-fat32-path (explode path)))))))
;;      size)))
;;   :hints (("goal" :in-theory (e/d (lofat-truncate hifat-no-dups-p)
;;                                   ((:rewrite take-of-take-split)
;;                                    (:linear len-of-member)
;;                                    (:definition take)
;;                                    (:rewrite take-of-len-free))))))

;; (defthm
;;   wc-after-truncate
;;   (implies
;;    (and
;;     (lofat-fs-p fat32$c)
;;     (member-equal path path-list)
;;     (not
;;      (null
;;       (mv-nth
;;        1
;;        (truncate-list-extra-hypothesis fat32$c path-list size))))
;;     (equal
;;      (mv-nth
;;       '1
;;       (lofat-to-hifat (mv-nth '0
;;                               (truncate-list fat32$c
;;                                              path-list size exit-status))))
;;      '0)
;;     ;; Consider trimming this hypothesis
;;     (fat32-filename-list-p (path-to-fat32-path (explode path))))
;;    (and
;;     (equal
;;      (mv-nth
;;       3
;;       (wc-1
;;        (mv-nth 0
;;                (truncate-list fat32$c
;;                               path-list size exit-status))
;;        path))
;;      0)
;;     (equal
;;      (mv-nth
;;       2
;;       (wc-1
;;        (mv-nth 0
;;                (truncate-list fat32$c
;;                               path-list size exit-status))
;;        path))
;;      size)))
;;   :hints (("goal" :do-not-induct t
;;            :in-theory (e/d (wc-1 lofat-open hifat-pread hifat-open hifat-lstat)
;;                            (truncate-list-correctness-1))
;;            :use
;;            truncate-list-correctness-1)))
