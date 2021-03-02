(in-package "ACL2")

;  hifat-cluster-count.lisp                               Mihir Mehta

; hifat-cluster-count is related to the problem of counting the number of
; clusters taken up by a HiFAT instance when stored on the disk.

(include-book "../hifat")
(include-book "../utilities/cluster-listp")

(local (in-theory (disable ceiling)))

;; In the subdirectory case, we need to place all the entries (32 bytes each)
;; and two entries (dot and dotdot). The space taken up for these things is
;; determined by the rule len-of-make-clusters, which expresses the length in
;; terms of the greatest integer function.
(defund
  hifat-cluster-count (fs cluster-size)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (integerp cluster-size)
                              (< 0 cluster-size))))
  (b*
      (((unless (consp fs)) 0)
       (head (car fs))
       (contents (m1-file->contents (cdr head))))
    (+
     (hifat-cluster-count (cdr fs)
                          cluster-size)
     (if
         (m1-regular-file-p (cdr head))
         (len (make-clusters contents cluster-size))
       (+ (hifat-cluster-count contents cluster-size)
          ;; This mbe form is here to help make a good type-prescription rule,
          ;; which identifies this thing as a natural number - not just an
          ;; integer. As an aside, I guess the battle over whether 0 is a
          ;; natural number has been lost for a while, since nobody seems to use
          ;; the term "whole number" any more.
          (mbe :exec (ceiling (* 32 (+ 2 (len contents)))
                              cluster-size)
               :logic (nfix (ceiling (* 32 (+ 2 (len contents)))
                                     cluster-size))))))))

(defthm
  hifat-cluster-count-of-put-assoc
  (implies
   (m1-file-alist-p fs)
   (equal
    (hifat-cluster-count (put-assoc-equal name file fs)
                         cluster-size)
    (b*
        ((new-contents (m1-file->contents file))
         ((when (and (atom (assoc-equal name fs))
                     (m1-regular-file-p file)))
          (+ (hifat-cluster-count fs cluster-size)
             (len (make-clusters new-contents cluster-size))))
         ((when (atom (assoc-equal name fs)))
          (+ (hifat-cluster-count fs cluster-size)
             (+ (hifat-cluster-count new-contents cluster-size)
                (nfix (ceiling (* 32 (+ 2 (len new-contents)))
                               cluster-size)))))
         (old-contents
          (m1-file->contents (cdr (assoc-equal name fs))))
         ((when
              (and (m1-directory-file-p (cdr (assoc-equal name fs)))
                   (m1-regular-file-p file)))
          (+ (hifat-cluster-count fs cluster-size)
             (len (make-clusters new-contents cluster-size))
             (- (hifat-cluster-count old-contents cluster-size))
             (- (nfix (ceiling (* 32 (+ 2 (len old-contents)))
                               cluster-size)))))
         ((when (m1-directory-file-p (cdr (assoc-equal name fs))))
          (+ (hifat-cluster-count fs cluster-size)
             (hifat-cluster-count new-contents cluster-size)
             (nfix (ceiling (* 32 (+ 2 (len new-contents)))
                            cluster-size))
             (- (hifat-cluster-count old-contents cluster-size))
             (- (nfix (ceiling (* 32 (+ 2 (len old-contents)))
                               cluster-size)))))
         ((when (m1-regular-file-p file))
          (+ (hifat-cluster-count fs cluster-size)
             (len (make-clusters new-contents cluster-size))
             (- (len (make-clusters old-contents cluster-size))))))
      (+ (hifat-cluster-count fs cluster-size)
         (hifat-cluster-count new-contents cluster-size)
         (nfix (ceiling (* 32 (+ 2 (len new-contents)))
                        cluster-size))
         (- (len (make-clusters old-contents cluster-size)))))))
  :hints (("goal" :in-theory (enable hifat-cluster-count)
           :induct (put-assoc-equal name file fs))))

(defthm
  hifat-cluster-count-of-hifat-place-file-lemma-2
  (implies
   (and
    (equal (len (cdr path)) 1)
    (m1-directory-file-p (cdr (assoc-equal (car path) fs)))
    (m1-file-alist-p fs)
    (hifat-no-dups-p fs)
    (fat32-filename-list-p path)
    (consp
     (assoc-equal (cadr path)
                  (m1-file->contents (cdr (assoc-equal (car path) fs))))))
   (equal
    (mv-nth 1
            (hifat-find-file
             (m1-file->contents (cdr (assoc-equal (car path) fs)))
             (cdr path)))
    0))
  :hints
  (("goal"
    :expand ((hifat-find-file
              (m1-file->contents (cdr (assoc-equal (car path) fs)))
              (cdr path))
             (len (cdr path))
             (len (cddr path))))))

(defthmd hifat-cluster-count-of-hifat-place-file-lemma-3
  (implies (equal (+ 1 (len (cddr path))) 1)
           (not (consp (cddr path))))
  :hints (("goal" :expand (len (cddr path)))))

(encapsulate
  ()

  (local (include-book "arithmetic-3/top" :dir :system))

  (defthm
    hifat-cluster-count-of-hifat-place-file-lemma-6
    (implies (and (integerp cluster-size)
                  (<= 512 cluster-size))
             (and
              (equal (ceiling 64 cluster-size)
                     1)
              (equal (ceiling 96 cluster-size)
                     1)))))

(defthm
  hifat-cluster-count-of-hifat-place-file-lemma-1
  (implies
   (and
    (consp path)
    (m1-directory-file-p (cdr (assoc-equal (car path) fs)))
    (< 1 (len (cdr path)))
    (equal
     (hifat-cluster-count
      (mv-nth 0
              (hifat-place-file
               (m1-file->contents (cdr (assoc-equal (car path) fs)))
               (cdr path)
               file))
      cluster-size)
     (+
      (len (make-clusters (m1-file->contents file)
                          cluster-size))
      (hifat-cluster-count
       (m1-file->contents (cdr (assoc-equal (car path) fs)))
       cluster-size)
      (-
       (ceiling
        (+
         64
         (*
          32
          (len
           (m1-file->contents
            (mv-nth
             0
             (hifat-find-file
              (m1-file->contents (cdr (assoc-equal (car path) fs)))
              (take (+ -1 (len (cdr path)))
                    (cdr path))))))))
        cluster-size))
      (ceiling
       (+
        96
        (*
         32
         (len
          (m1-file->contents
           (mv-nth
            0
            (hifat-find-file
             (m1-file->contents (cdr (assoc-equal (car path) fs)))
             (take (+ -1 (len (cdr path)))
                   (cdr path))))))))
       cluster-size)))
    (m1-file-alist-p fs)
    (hifat-no-dups-p fs)
    (fat32-filename-list-p path))
   (equal
    (+
     (hifat-cluster-count fs cluster-size)
     (- (hifat-cluster-count
         (m1-file->contents (cdr (assoc-equal (car path) fs)))
         cluster-size))
     (hifat-cluster-count
      (mv-nth 0
              (hifat-place-file
               (m1-file->contents (cdr (assoc-equal (car path) fs)))
               (cdr path)
               file))
      cluster-size))
    (+
     (hifat-cluster-count fs cluster-size)
     (len (make-clusters (m1-file->contents file)
                         cluster-size))
     (-
      (ceiling
       (+ 64
          (* 32
             (len (m1-file->contents
                   (mv-nth 0
                           (hifat-find-file fs
                                            (take (len (cdr path))
                                                  path)))))))
       cluster-size))
     (ceiling
      (+ 96
         (* 32
            (len (m1-file->contents
                  (mv-nth 0
                          (hifat-find-file fs
                                           (take (len (cdr path))
                                                 path)))))))
      cluster-size))))
  :hints (("goal" :expand ((hifat-find-file fs
                                            (cons (car path)
                                                  (take (len (cddr path))
                                                        (cdr path))))
                           (take (+ 1 (len (cddr path)))
                                 path))
           :cases ((equal (consp (cdr (take (+ 1 (len (cddr path)))
                                            path)))
                          (< 1
                             (len (take (+ 1 (len (cddr path)))
                                        path))))))))

(defthm
  hifat-cluster-count-of-hifat-place-file-lemma-4
  (implies
   (and
    (m1-directory-file-p (cdr (assoc-equal (car path) fs)))
    (< 1 (len (cdr path)))
    (equal
     (hifat-cluster-count
      (mv-nth 0
              (hifat-place-file
               (m1-file->contents (cdr (assoc-equal (car path) fs)))
               (cdr path)
               file))
      cluster-size)
     (+
      (hifat-cluster-count (m1-file->contents file)
                           cluster-size)
      (ceiling (+ 64
                  (* 32 (len (m1-file->contents file))))
               cluster-size)
      (hifat-cluster-count
       (m1-file->contents (cdr (assoc-equal (car path) fs)))
       cluster-size)
      (-
       (ceiling
        (+
         64
         (*
          32
          (len
           (m1-file->contents
            (mv-nth
             0
             (hifat-find-file
              (m1-file->contents (cdr (assoc-equal (car path) fs)))
              (take (+ -1 (len (cdr path)))
                    (cdr path))))))))
        cluster-size))
      (ceiling
       (+
        96
        (*
         32
         (len
          (m1-file->contents
           (mv-nth
            0
            (hifat-find-file
             (m1-file->contents (cdr (assoc-equal (car path) fs)))
             (take (+ -1 (len (cdr path)))
                   (cdr path))))))))
       cluster-size)))
    (m1-file-alist-p fs)
    (hifat-no-dups-p fs)
    (fat32-filename-list-p path))
   (equal
    (+
     (hifat-cluster-count fs cluster-size)
     (- (hifat-cluster-count
         (m1-file->contents (cdr (assoc-equal (car path) fs)))
         cluster-size))
     (hifat-cluster-count
      (mv-nth 0
              (hifat-place-file
               (m1-file->contents (cdr (assoc-equal (car path) fs)))
               (cdr path)
               file))
      cluster-size))
    (+
     (hifat-cluster-count fs cluster-size)
     (hifat-cluster-count (m1-file->contents file)
                          cluster-size)
     (ceiling (+ 64
                 (* 32 (len (m1-file->contents file))))
              cluster-size)
     (-
      (ceiling
       (+ 64
          (* 32
             (len (m1-file->contents
                   (mv-nth 0
                           (hifat-find-file fs
                                            (take (len (cdr path))
                                                  path)))))))
       cluster-size))
     (ceiling
      (+ 96
         (* 32
            (len (m1-file->contents
                  (mv-nth 0
                          (hifat-find-file fs
                                           (take (len (cdr path))
                                                 path)))))))
      cluster-size))))
  :hints (("goal" :expand ((hifat-find-file fs
                                            (cons (car path)
                                                  (take (len (cddr path))
                                                        (cdr path))))
                           (take (+ 1 (len (cddr path)))
                                 path))
           :cases ((equal (consp (cdr (take (+ 1 (len (cddr path)))
                                            path)))
                          (< 1
                             (len (take (+ 1 (len (cddr path)))
                                        path))))))))

(encapsulate
  ()

  (local
   (defthmd
     hifat-cluster-count-of-hifat-place-file-lemma-5
     (implies
      (and (m1-file-alist-p fs)
           (hifat-no-dups-p fs)
           (fat32-filename-list-p path)
           (m1-file-p file)
           (integerp cluster-size)
           (<= 512 cluster-size))
      (equal
       (hifat-cluster-count
        (mv-nth 0 (hifat-place-file fs path file))
        cluster-size)
       (b*
           ((new-contents (m1-file->contents file))
            ((when
                 (not (zp (mv-nth 1
                                  (hifat-place-file fs path file)))))
             (hifat-cluster-count fs cluster-size))
            ;; This may be inaccurate because the parent directory's length
            ;; will change.
            ((when
                 (and (not (zp (mv-nth 1 (hifat-find-file fs path))))
                      (m1-regular-file-p file)))
             (+
              (hifat-cluster-count fs cluster-size)
              (len (make-clusters new-contents cluster-size))
              (nfix
               (ceiling
                (*
                 32
                 (+
                  3
                  (len
                   (m1-file->contents
                    (mv-nth
                     0
                     (hifat-find-file fs (butlast path 1)))))))
                cluster-size))
              (-
               (nfix
                (ceiling
                 (*
                  32
                  (+
                   2
                   (len
                    (m1-file->contents
                     (mv-nth
                      0
                      (hifat-find-file fs (butlast path 1)))))))
                 cluster-size)))))
            ;; This may be inaccurate because the parent directory's length
            ;; will change.
            ((when
                 (not (zp (mv-nth 1 (hifat-find-file fs path)))))
             (+ (hifat-cluster-count fs cluster-size)
                (hifat-cluster-count new-contents cluster-size)
                (nfix (ceiling (* 32 (+ 2 (len new-contents)))
                               cluster-size))
                (nfix
                 (ceiling
                  (*
                   32
                   (+
                    3
                    (len
                     (m1-file->contents
                      (mv-nth
                       0
                       (hifat-find-file fs (butlast path 1)))))))
                  cluster-size))
                (-
                 (nfix
                  (ceiling
                   (*
                    32
                    (+
                     2
                     (len
                      (m1-file->contents
                       (mv-nth
                        0
                        (hifat-find-file fs (butlast path 1)))))))
                   cluster-size)))))
            (old-file (mv-nth 0 (hifat-find-file fs path)))
            (old-contents (m1-file->contents old-file))
            ((when (and (m1-regular-file-p file)
                        (m1-regular-file-p old-file)))
             (+ (hifat-cluster-count fs cluster-size)
                (len (make-clusters new-contents cluster-size))
                (- (len (make-clusters old-contents cluster-size)))))
            ((when (m1-regular-file-p file))
             (+ (hifat-cluster-count fs cluster-size)
                (len (make-clusters new-contents cluster-size))
                (- (hifat-cluster-count old-contents cluster-size))
                (- (nfix (ceiling (* 32 (+ 2 (len old-contents)))
                                  cluster-size)))))
            ((when (m1-regular-file-p old-file))
             (+ (hifat-cluster-count fs cluster-size)
                (hifat-cluster-count new-contents cluster-size)
                (nfix (ceiling (* 32 (+ 2 (len new-contents)))
                               cluster-size))
                (- (len (make-clusters old-contents cluster-size))))))
         (+ (hifat-cluster-count fs cluster-size)
            (hifat-cluster-count new-contents cluster-size)
            (nfix (ceiling (* 32 (+ 2 (len new-contents)))
                           cluster-size))
            (- (hifat-cluster-count old-contents cluster-size))
            (- (nfix (ceiling (* 32 (+ 2 (len old-contents)))
                              cluster-size)))))))
     :hints
     (("goal" :in-theory
       (e/d (nfix hifat-place-file hifat-find-file
                  hifat-cluster-count-of-hifat-place-file-lemma-3)
            ((:rewrite nfix-when-natp)))
       :induct (hifat-place-file fs path file)))))

  (defthm
    hifat-cluster-count-of-hifat-place-file
    (implies
     (and (integerp cluster-size)
          (<= 512 cluster-size))
     (equal
      (hifat-cluster-count
       (mv-nth 0 (hifat-place-file fs path file))
       cluster-size)
      (b*
          ((new-contents (m1-file->contents file))
           (fs (hifat-file-alist-fix fs))
           (path (fat32-filename-list-fix path))
           (file (m1-file-fix file))
           ((when
                (not (zp (mv-nth 1
                                 (hifat-place-file fs path file)))))
            (hifat-cluster-count fs cluster-size))
           ;; This may be inaccurate because the parent directory's length
           ;; will change.
           ((when
                (and (not (zp (mv-nth 1 (hifat-find-file fs path))))
                     (m1-regular-file-p file)))
            (+
             (hifat-cluster-count fs cluster-size)
             (len (make-clusters new-contents cluster-size))
             (nfix
              (ceiling
               (*
                32
                (+
                 3
                 (len
                  (m1-file->contents
                   (mv-nth
                    0
                    (hifat-find-file fs (butlast path 1)))))))
               cluster-size))
             (-
              (nfix
               (ceiling
                (*
                 32
                 (+
                  2
                  (len
                   (m1-file->contents
                    (mv-nth
                     0
                     (hifat-find-file fs (butlast path 1)))))))
                cluster-size)))))
           ;; This may be inaccurate because the parent directory's length
           ;; will change.
           ((when
                (not (zp (mv-nth 1 (hifat-find-file fs path)))))
            (+ (hifat-cluster-count fs cluster-size)
               (hifat-cluster-count new-contents cluster-size)
               (nfix (ceiling (* 32 (+ 2 (len new-contents)))
                              cluster-size))
               (nfix
                (ceiling
                 (*
                  32
                  (+
                   3
                   (len
                    (m1-file->contents
                     (mv-nth
                      0
                      (hifat-find-file fs (butlast path 1)))))))
                 cluster-size))
               (-
                (nfix
                 (ceiling
                  (*
                   32
                   (+
                    2
                    (len
                     (m1-file->contents
                      (mv-nth
                       0
                       (hifat-find-file fs (butlast path 1)))))))
                  cluster-size)))))
           (old-file (mv-nth 0 (hifat-find-file fs path)))
           (old-contents (m1-file->contents old-file))
           ((when (and (m1-regular-file-p file)
                       (m1-regular-file-p old-file)))
            (+ (hifat-cluster-count fs cluster-size)
               (len (make-clusters new-contents cluster-size))
               (- (len (make-clusters old-contents cluster-size)))))
           ((when (m1-regular-file-p file))
            (+ (hifat-cluster-count fs cluster-size)
               (len (make-clusters new-contents cluster-size))
               (- (hifat-cluster-count old-contents cluster-size))
               (- (nfix (ceiling (* 32 (+ 2 (len old-contents)))
                                 cluster-size)))))
           ((when (m1-regular-file-p old-file))
            (+ (hifat-cluster-count fs cluster-size)
               (hifat-cluster-count new-contents cluster-size)
               (nfix (ceiling (* 32 (+ 2 (len new-contents)))
                              cluster-size))
               (- (len (make-clusters old-contents cluster-size))))))
        (+ (hifat-cluster-count fs cluster-size)
           (hifat-cluster-count new-contents cluster-size)
           (nfix (ceiling (* 32 (+ 2 (len new-contents)))
                          cluster-size))
           (- (hifat-cluster-count old-contents cluster-size))
           (- (nfix (ceiling (* 32 (+ 2 (len old-contents)))
                             cluster-size)))))))
    :hints
    (("goal"
      :use (:instance
            hifat-cluster-count-of-hifat-place-file-lemma-5
            (fs (hifat-file-alist-fix fs))
            (path (fat32-filename-list-fix path))
            (file (m1-file-fix file)))))))
