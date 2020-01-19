(in-package "ACL2")

(include-book "test-stuff")

(defun
    truncate-list-extra-hypothesis
    (fat32-in-memory name-list size)
  (declare (xargs :stobjs fat32-in-memory
                  :guard (and (lofat-fs-p fat32-in-memory)
                              (string-listp name-list)
                              (natp size))
                  :measure (len name-list)))
  (b*
      (((when (atom name-list))
        (mv fat32-in-memory t))
       (fat32-pathname (pathname-to-fat32-pathname
                        (coerce (car name-list) 'list)))
       ((unless (fat32-filename-list-p fat32-pathname))
        (mv fat32-in-memory nil))
       ((mv fs error-code)
        (lofat-to-hifat fat32-in-memory))
       ((unless (equal error-code 0))
        (mv fat32-in-memory nil))
       ((mv fs retval &)
        (hifat-truncate fs fat32-pathname size))
       ((unless (and (equal retval 0)
                     (hifat-bounded-file-alist-p fs)
                     (<= (hifat-entry-count fs) (max-entry-count fat32-in-memory))))
        (mv fat32-in-memory nil))
       ((mv fat32-in-memory error-code)
        (hifat-to-lofat fat32-in-memory fs))
       ((unless (equal error-code 0))
        (mv fat32-in-memory nil)))
    (truncate-list-extra-hypothesis fat32-in-memory (cdr name-list) size)))

(defthm
  truncate-list-correctness-1-lemma-1
  (implies
   (lofat-fs-p fat32-in-memory)
   (lofat-fs-p
    (mv-nth 0
            (truncate-list fat32-in-memory
                           name-list size exit-status)))))

(defthm
  truncate-list-correctness-1-lemma-2
  (implies
   (and (lofat-fs-p fat32-in-memory)
        (hifat-bounded-file-alist-p fs)
        (<= (hifat-entry-count fs)
            (max-entry-count fat32-in-memory))
        (zp (mv-nth 1 (hifat-to-lofat fat32-in-memory fs)))
        (m1-file-alist-p fs)
        (hifat-no-dups-p fs)
        (m1-regular-file-p (mv-nth 0 (hifat-find-file fs pathname))))
   (equal
    (m1-file->contents
     (mv-nth
      0
      (hifat-find-file
       (mv-nth
        0
        (lofat-to-hifat (mv-nth 0 (hifat-to-lofat fat32-in-memory fs))))
       pathname)))
    (m1-file->contents (mv-nth 0
                               (hifat-find-file fs pathname)))))
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
                               (hifat-to-lofat fat32-in-memory fs)))))))))

(defthm
  truncate-list-correctness-1-lemma-4
  (implies
   (and
    (consp pathname-list)
    (not
     (equal
      (mv-nth
       1
       (hifat-find-file
        (mv-nth 0 (lofat-to-hifat fat32-in-memory))
        (pathname-to-fat32-pathname (explode (car pathname-list)))))
      0))
    (equal
     (mv-nth
      1
      (hifat-place-file
       (mv-nth 0 (lofat-to-hifat fat32-in-memory))
       (pathname-to-fat32-pathname (explode (car pathname-list)))
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
                      (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                      (pathname-to-fat32-pathname (explode pathname)))))))
          nil)))))
     0)
    (lofat-fs-p fat32-in-memory)
    (equal
     (mv-nth
      1
      (hifat-find-file (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                       (pathname-to-fat32-pathname (explode pathname))))
     0)
    (m1-regular-file-p
     (mv-nth 0
             (hifat-find-file
              (mv-nth 0 (lofat-to-hifat fat32-in-memory))
              (pathname-to-fat32-pathname (explode pathname)))))
    (mv-nth
     1
     (truncate-list-extra-hypothesis
      fat32-in-memory pathname-list
      (len
       (explode
        (m1-file->contents
         (mv-nth 0
                 (hifat-find-file
                  (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                  (pathname-to-fat32-pathname (explode pathname))))))))))
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
             fat32-in-memory
             (mv-nth
              0
              (hifat-place-file
               (mv-nth 0 (lofat-to-hifat fat32-in-memory))
               (pathname-to-fat32-pathname (explode (car pathname-list)))
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
                       (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                       (pathname-to-fat32-pathname (explode pathname)))))))
                  nil)))))))))
         (pathname-to-fat32-pathname (explode pathname)))))))
    (len
     (explode
      (m1-file->contents
       (mv-nth 0
               (hifat-find-file
                (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                (pathname-to-fat32-pathname (explode pathname)))))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable truncate-list-correctness-1-lemma-2)
    :use
    (:instance
     truncate-list-correctness-1-lemma-2
     (pathname (pathname-to-fat32-pathname (explode pathname)))
     (fs
      (mv-nth
       0
       (hifat-place-file
        (mv-nth 0 (lofat-to-hifat fat32-in-memory))
        (pathname-to-fat32-pathname (explode (car pathname-list)))
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
                (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                (pathname-to-fat32-pathname (explode pathname)))))))
           nil))))))
     (fat32-in-memory fat32-in-memory)))))

(defthm
  truncate-list-correctness-1-lemma-6
  (implies
   (and
    (equal
     (mv-nth 1
             (hifat-find-file
              (mv-nth 0 (lofat-to-hifat fat32-in-memory))
              (pathname-to-fat32-pathname (explode (car pathname-list)))))
     0)
    (not
     (m1-directory-file-p
      (mv-nth
       0
       (hifat-find-file
        (mv-nth 0 (lofat-to-hifat fat32-in-memory))
        (pathname-to-fat32-pathname (explode (car pathname-list)))))))
    (equal
     (mv-nth
      1
      (hifat-place-file
       (mv-nth 0 (lofat-to-hifat fat32-in-memory))
       (pathname-to-fat32-pathname (explode (car pathname-list)))
       (m1-file
        (m1-file->dir-ent
         (mv-nth
          0
          (hifat-find-file
           (mv-nth 0 (lofat-to-hifat fat32-in-memory))
           (pathname-to-fat32-pathname (explode (car pathname-list))))))
        (implode
         (take
          (len
           (explode
            (m1-file->contents
             (mv-nth 0
                     (hifat-find-file
                      (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                      (pathname-to-fat32-pathname (explode pathname)))))))
          (explode
           (m1-file->contents
            (mv-nth 0
                    (hifat-find-file
                     (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                     (pathname-to-fat32-pathname
                      (explode (car pathname-list))))))))))))
     0)
    (lofat-fs-p fat32-in-memory)
    (equal
     (mv-nth
      1
      (hifat-find-file (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                       (pathname-to-fat32-pathname (explode pathname))))
     0)
    (m1-regular-file-p
     (mv-nth 0
             (hifat-find-file
              (mv-nth 0 (lofat-to-hifat fat32-in-memory))
              (pathname-to-fat32-pathname (explode pathname)))))
    (mv-nth
     1
     (truncate-list-extra-hypothesis
      fat32-in-memory pathname-list
      (len
       (explode
        (m1-file->contents
         (mv-nth 0
                 (hifat-find-file
                  (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                  (pathname-to-fat32-pathname (explode pathname))))))))))
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
             fat32-in-memory
             (mv-nth
              0
              (hifat-place-file
               (mv-nth 0 (lofat-to-hifat fat32-in-memory))
               (pathname-to-fat32-pathname (explode (car pathname-list)))
               (m1-file
                (m1-file->dir-ent
                 (mv-nth 0
                         (hifat-find-file
                          (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                          (pathname-to-fat32-pathname
                           (explode (car pathname-list))))))
                (implode
                 (take
                  (len
                   (explode
                    (m1-file->contents
                     (mv-nth
                      0
                      (hifat-find-file
                       (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                       (pathname-to-fat32-pathname (explode pathname)))))))
                  (explode
                   (m1-file->contents
                    (mv-nth
                     0
                     (hifat-find-file
                      (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                      (pathname-to-fat32-pathname
                       (explode (car pathname-list))))))))))))))))
         (pathname-to-fat32-pathname (explode pathname)))))))
    (len
     (explode
      (m1-file->contents
       (mv-nth 0
               (hifat-find-file
                (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                (pathname-to-fat32-pathname (explode pathname)))))))))
  :hints
  (("goal"
    :in-theory (e/d (hifat-find-file)
                    ((:rewrite truncate-list-correctness-1-lemma-2)))
    :use
    (:instance
     (:rewrite truncate-list-correctness-1-lemma-2)
     (pathname (pathname-to-fat32-pathname (explode pathname)))
     (fs
      (mv-nth
       0
       (hifat-place-file
        (mv-nth 0 (lofat-to-hifat fat32-in-memory))
        (pathname-to-fat32-pathname (explode (car pathname-list)))
        (m1-file
         (m1-file->dir-ent
          (mv-nth
           0
           (hifat-find-file
            (mv-nth 0 (lofat-to-hifat fat32-in-memory))
            (pathname-to-fat32-pathname (explode (car pathname-list))))))
         (implode
          (take
           (len
            (explode
             (m1-file->contents
              (mv-nth
               0
               (hifat-find-file
                (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                (pathname-to-fat32-pathname (explode pathname)))))))
           (explode
            (m1-file->contents
             (mv-nth 0
                     (hifat-find-file
                      (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                      (pathname-to-fat32-pathname
                       (explode (car pathname-list)))))))))))))
     (fat32-in-memory fat32-in-memory)))))

(defthm
  truncate-list-correctness-1-lemma-3
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (equal
     (mv-nth
      1
      (hifat-find-file
       (mv-nth 0 (lofat-to-hifat fat32-in-memory))
       (pathname-to-fat32-pathname (explode pathname))))
     0)
    (m1-regular-file-p
     (mv-nth
      0
      (hifat-find-file
       (mv-nth 0 (lofat-to-hifat fat32-in-memory))
       (pathname-to-fat32-pathname (explode pathname)))))
    (equal
     (len
      (explode
       (m1-file->contents
        (mv-nth
         0
         (hifat-find-file
          (mv-nth 0 (lofat-to-hifat fat32-in-memory))
          (pathname-to-fat32-pathname (explode pathname)))))))
     size)
    (not
     (null (mv-nth 1
                   (truncate-list-extra-hypothesis
                    fat32-in-memory pathname-list size)))))
   (and
    (equal
     (mv-nth
      1
      (hifat-find-file
       (mv-nth
        0
        (lofat-to-hifat
         (mv-nth
          0
          (truncate-list fat32-in-memory
                         pathname-list size exit-status))))
       (pathname-to-fat32-pathname (explode pathname))))
     0)
    (m1-regular-file-p
     (mv-nth
      0
      (hifat-find-file
       (mv-nth
        0
        (lofat-to-hifat
         (mv-nth
          0
          (truncate-list fat32-in-memory
                         pathname-list size exit-status))))
       (pathname-to-fat32-pathname (explode pathname)))))
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
             (truncate-list fat32-in-memory
                            pathname-list size exit-status))))
          (pathname-to-fat32-pathname (explode pathname)))))))
     size)))
  :hints
  (("goal"
    :induct (truncate-list fat32-in-memory
                           pathname-list size exit-status)
    :in-theory
    (e/d
     (lofat-truncate)
     ((:rewrite take-of-take-split)
      (:linear len-of-member-equal)
      (:rewrite fat32-filename-p-when-fat32-filename-p)
      (:rewrite str::make-character-list-when-character-listp)
      (:rewrite hifat-to-lofat-inversion-lemma-2)
      (:definition take))))))

(defthm
  truncate-list-correctness-1-lemma-5
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (integerp size)
    (<= 0 size)
    (< size 4294967296)
    (equal
     (mv-nth 1
             (hifat-find-file
              (mv-nth 0 (lofat-to-hifat fat32-in-memory))
              (pathname-to-fat32-pathname (explode (car pathname-list)))))
     0)
    (not
     (m1-directory-file-p
      (mv-nth
       0
       (hifat-find-file
        (mv-nth 0 (lofat-to-hifat fat32-in-memory))
        (pathname-to-fat32-pathname (explode (car pathname-list)))))))
    (equal
     (mv-nth
      1
      (hifat-place-file
       (mv-nth 0 (lofat-to-hifat fat32-in-memory))
       (pathname-to-fat32-pathname (explode (car pathname-list)))
       (m1-file
        (m1-file->dir-ent
         (mv-nth
          0
          (hifat-find-file
           (mv-nth 0 (lofat-to-hifat fat32-in-memory))
           (pathname-to-fat32-pathname (explode (car pathname-list))))))
        (implode
         (take
          size
          (explode
           (m1-file->contents
            (mv-nth 0
                    (hifat-find-file
                     (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                     (pathname-to-fat32-pathname
                      (explode (car pathname-list))))))))))))
     0)
    (hifat-bounded-file-alist-p
     (mv-nth
      0
      (hifat-place-file
       (mv-nth 0 (lofat-to-hifat fat32-in-memory))
       (pathname-to-fat32-pathname (explode (car pathname-list)))
       (m1-file
        (m1-file->dir-ent
         (mv-nth
          0
          (hifat-find-file
           (mv-nth 0 (lofat-to-hifat fat32-in-memory))
           (pathname-to-fat32-pathname (explode (car pathname-list))))))
        (implode
         (take
          size
          (explode
           (m1-file->contents
            (mv-nth 0
                    (hifat-find-file
                     (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                     (pathname-to-fat32-pathname
                      (explode (car pathname-list)))))))))))))
    (<=
     (hifat-entry-count
      (mv-nth
       0
       (hifat-place-file
        (mv-nth 0 (lofat-to-hifat fat32-in-memory))
        (pathname-to-fat32-pathname (explode (car pathname-list)))
        (m1-file
         (m1-file->dir-ent
          (mv-nth
           0
           (hifat-find-file
            (mv-nth 0 (lofat-to-hifat fat32-in-memory))
            (pathname-to-fat32-pathname (explode (car pathname-list))))))
         (implode
          (take
           size
           (explode
            (m1-file->contents
             (mv-nth 0
                     (hifat-find-file
                      (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                      (pathname-to-fat32-pathname
                       (explode (car pathname-list)))))))))))))
     (max-entry-count fat32-in-memory))
    (equal
     (mv-nth
      1
      (hifat-to-lofat
       fat32-in-memory
       (mv-nth
        0
        (hifat-place-file
         (mv-nth 0 (lofat-to-hifat fat32-in-memory))
         (pathname-to-fat32-pathname (explode (car pathname-list)))
         (m1-file
          (m1-file->dir-ent
           (mv-nth
            0
            (hifat-find-file
             (mv-nth 0 (lofat-to-hifat fat32-in-memory))
             (pathname-to-fat32-pathname (explode (car pathname-list))))))
          (implode
           (take
            size
            (explode
             (m1-file->contents
              (mv-nth 0
                      (hifat-find-file
                       (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                       (pathname-to-fat32-pathname
                        (explode (car pathname-list))))))))))))))
     0)
    (mv-nth
     1
     (truncate-list-extra-hypothesis
      (mv-nth
       0
       (hifat-to-lofat
        fat32-in-memory
        (mv-nth
         0
         (hifat-place-file
          (mv-nth 0 (lofat-to-hifat fat32-in-memory))
          (pathname-to-fat32-pathname (explode (car pathname-list)))
          (m1-file
           (m1-file->dir-ent
            (mv-nth
             0
             (hifat-find-file
              (mv-nth 0 (lofat-to-hifat fat32-in-memory))
              (pathname-to-fat32-pathname (explode (car pathname-list))))))
           (implode
            (take
             size
             (explode
              (m1-file->contents
               (mv-nth 0
                       (hifat-find-file
                        (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                        (pathname-to-fat32-pathname
                         (explode (car pathname-list))))))))))))))
      (cdr pathname-list)
      size)))
   (and
    (equal
     (mv-nth
      1
      (hifat-find-file
       (mv-nth
        0
        (lofat-to-hifat
         (mv-nth
          0
          (truncate-list
           (mv-nth
            0
            (hifat-to-lofat
             fat32-in-memory
             (mv-nth
              0
              (hifat-place-file
               (mv-nth 0 (lofat-to-hifat fat32-in-memory))
               (pathname-to-fat32-pathname (explode (car pathname-list)))
               (m1-file
                (m1-file->dir-ent
                 (mv-nth 0
                         (hifat-find-file
                          (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                          (pathname-to-fat32-pathname
                           (explode (car pathname-list))))))
                (implode
                 (take
                  size
                  (explode
                   (m1-file->contents
                    (mv-nth 0
                            (hifat-find-file
                             (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                             (pathname-to-fat32-pathname
                              (explode (car pathname-list))))))))))))))
           (cdr pathname-list)
           size exit-status))))
       (pathname-to-fat32-pathname (explode (car pathname-list)))))
     0)
    (m1-regular-file-p
     (mv-nth
      0
      (hifat-find-file
       (mv-nth
        0
        (lofat-to-hifat
         (mv-nth
          0
          (truncate-list
           (mv-nth
            0
            (hifat-to-lofat
             fat32-in-memory
             (mv-nth
              0
              (hifat-place-file
               (mv-nth 0 (lofat-to-hifat fat32-in-memory))
               (pathname-to-fat32-pathname (explode (car pathname-list)))
               (m1-file
                (m1-file->dir-ent
                 (mv-nth 0
                         (hifat-find-file
                          (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                          (pathname-to-fat32-pathname
                           (explode (car pathname-list))))))
                (implode
                 (take
                  size
                  (explode
                   (m1-file->contents
                    (mv-nth 0
                            (hifat-find-file
                             (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                             (pathname-to-fat32-pathname
                              (explode (car pathname-list))))))))))))))
           (cdr pathname-list)
           size exit-status))))
       (pathname-to-fat32-pathname (explode (car pathname-list))))))
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
             (truncate-list
              (mv-nth
               0
               (hifat-to-lofat
                fat32-in-memory
                (mv-nth
                 0
                 (hifat-place-file
                  (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                  (pathname-to-fat32-pathname (explode (car pathname-list)))
                  (m1-file
                   (m1-file->dir-ent
                    (mv-nth 0
                            (hifat-find-file
                             (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                             (pathname-to-fat32-pathname
                              (explode (car pathname-list))))))
                   (implode
                    (take
                     size
                     (explode
                      (m1-file->contents
                       (mv-nth 0
                               (hifat-find-file
                                (mv-nth 0 (lofat-to-hifat fat32-in-memory))
                                (pathname-to-fat32-pathname
                                 (explode (car pathname-list))))))))))))))
              (cdr pathname-list)
              size exit-status))))
          (pathname-to-fat32-pathname (explode (car pathname-list))))))))
     size)))
  :hints
  (("goal"
    :in-theory (disable (:rewrite m1-directory-file-p-when-m1-file-p))
    :use
    (:instance
     (:rewrite m1-directory-file-p-when-m1-file-p)
     (x
      (mv-nth
       0
       (hifat-find-file
        (mv-nth 0 (lofat-to-hifat fat32-in-memory))
        (pathname-to-fat32-pathname (explode (car pathname-list))))))))))

(defthm
  truncate-list-correctness-1
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (member-equal pathname pathname-list)
    (not
     (null
      (mv-nth
       1
       (truncate-list-extra-hypothesis fat32-in-memory pathname-list size)))))
   (and
    (equal
     (mv-nth
      1
      (hifat-find-file
       (mv-nth 0
               (lofat-to-hifat
                (mv-nth 0
                        (truncate-list fat32-in-memory
                                       pathname-list size exit-status))))
       (pathname-to-fat32-pathname (explode pathname))))
     0)
    (m1-regular-file-p
     (mv-nth
      0
      (hifat-find-file
       (mv-nth 0
               (lofat-to-hifat
                (mv-nth 0
                        (truncate-list fat32-in-memory
                                       pathname-list size exit-status))))
       (pathname-to-fat32-pathname (explode pathname)))))
    (equal
     (len
      (explode
       (m1-file->contents
        (mv-nth
         0
         (hifat-find-file
          (mv-nth 0
                  (lofat-to-hifat
                   (mv-nth 0
                           (truncate-list fat32-in-memory
                                          pathname-list size exit-status))))
          (pathname-to-fat32-pathname (explode pathname)))))))
     size)))
  :hints (("goal" :in-theory (e/d (lofat-truncate)
                                  ((:rewrite take-of-take-split)
                                   (:linear len-of-member-equal)
                                   (:definition take)
                                   (:rewrite take-of-len-free))))))

(defthm
  wc-after-truncate
  (implies
   (and
    (lofat-fs-p fat32-in-memory)
    (member-equal pathname pathname-list)
    (not
     (null
      (mv-nth
       1
       (truncate-list-extra-hypothesis fat32-in-memory pathname-list size))))
    (equal
     (mv-nth
      '1
      (lofat-to-hifat (mv-nth '0
                              (truncate-list fat32-in-memory
                                             pathname-list size exit-status))))
     '0)
    ;; Consider trimming this hypothesis
    (fat32-filename-list-p (pathname-to-fat32-pathname (explode pathname))))
   (and
    (equal
     (mv-nth
      3
      (wc-1
       (mv-nth 0
               (truncate-list fat32-in-memory
                              pathname-list size exit-status))
       pathname))
     0)
    (equal
     (mv-nth
      2
      (wc-1
       (mv-nth 0
               (truncate-list fat32-in-memory
                              pathname-list size exit-status))
       pathname))
     size)))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (wc-1 lofat-open)
                           (truncate-list-correctness-1))
           :use
           truncate-list-correctness-1)))
