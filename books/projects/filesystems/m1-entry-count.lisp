; Copyright (C) 2017, Regents of the University of Texas
; Written by Mihir Mehta
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

;  m1-entry-count.lisp                                 Mihir Mehta

; m1-entry-count is related to the problem of transforming a potentially loopy
; FAT32 disk image into a tree in a bounded amount of time. Some lemmas for
; reasoning about it are placed here.

(include-book "m1-dir-equiv")

;; We're not counting this very directory, because the root does not have a
;; directory entry for itself.
(defun m1-entry-count (fs)
  (declare (xargs :guard (m1-file-alist-p fs)))
  (if
      (atom fs)
      0
    (if (m1-directory-file-p (cdar fs))
        (+ 1
           (m1-entry-count (m1-file->contents (cdar fs)))
           (m1-entry-count (cdr fs)))
      (+ 1
         (m1-entry-count (cdr fs))))))

(defthmd
  m1-entry-count-when-m1-file-no-dups-p
  (implies
   (and (m1-file-alist-p m1-file-alist)
        (m1-file-no-dups-p m1-file-alist)
        (consp (assoc-equal x m1-file-alist)))
   (equal
    (m1-entry-count m1-file-alist)
    (+
     (m1-entry-count (remove1-assoc x m1-file-alist))
     (if
      (m1-directory-file-p (cdr (assoc-equal x m1-file-alist)))
      (+ 1
         (m1-entry-count
          (m1-file->contents
           (cdr (assoc-equal x m1-file-alist)))))
      1)))))

(encapsulate
  ()

  (local
   (defun
       induction-scheme
       (m1-file-alist1 m1-file-alist2)
     (declare
      (xargs
       :guard (and (m1-file-alist-p m1-file-alist1)
                   (m1-file-alist-p m1-file-alist2))
       :hints (("goal" :in-theory (enable m1-file->contents
                                          m1-directory-file-p)))))
     (b* (((when (atom m1-file-alist1)) t)
          ((when (or (atom (car m1-file-alist1))
                     (not (stringp (car (car m1-file-alist1))))))
           (and (member-equal (car m1-file-alist1)
                              m1-file-alist2)
                (induction-scheme (cdr m1-file-alist1)
                                  (remove1-assoc-equal
                                   (caar m1-file-alist1)
                                   m1-file-alist2))))
          (name (caar m1-file-alist1))
          (file1 (cdar m1-file-alist1))
          ((unless (consp (assoc-equal name m1-file-alist2)))
           nil)
          (file2 (cdr (assoc-equal name m1-file-alist2))))
       (if (not (m1-directory-file-p file1))
           (and (not (m1-directory-file-p file2))
                (induction-scheme (cdr m1-file-alist1)
                                  (remove1-assoc-equal
                                   name
                                   m1-file-alist2))
                (equal (m1-file->contents file1)
                       (m1-file->contents file2)))
         (and (m1-directory-file-p file2)
              (induction-scheme (cdr m1-file-alist1)
                                (remove1-assoc-equal
                                 name
                                 m1-file-alist2))
              (induction-scheme (m1-file->contents file1)
                                (m1-file->contents file2)))))))

  (local
   (defthm induction-scheme-correctness
     (implies
      (and (m1-file-no-dups-p m1-file-alist1)
           (m1-file-no-dups-p m1-file-alist2)
           (m1-file-alist-p m1-file-alist1)
           (m1-file-alist-p m1-file-alist2))
      (iff
       (induction-scheme
        m1-file-alist1 m1-file-alist2)
       (m1-dir-subsetp m1-file-alist1 m1-file-alist2)))
     :hints (("Goal" :induct (induction-scheme
                              m1-file-alist1 m1-file-alist2)) )))

  (defthm
    m1-entry-count-when-m1-dir-subsetp
    (implies (and (m1-file-no-dups-p m1-file-alist1)
                  (m1-file-no-dups-p m1-file-alist2)
                  (m1-file-alist-p m1-file-alist1)
                  (m1-file-alist-p m1-file-alist2)
                  (m1-dir-subsetp m1-file-alist1 m1-file-alist2))
             (<= (m1-entry-count m1-file-alist1)
                 (m1-entry-count m1-file-alist2)))
    :rule-classes :linear
    :hints
    (("goal"
      :induct (induction-scheme m1-file-alist1 m1-file-alist2))
     ("subgoal *1/7"
      :use
      (:instance (:rewrite m1-entry-count-when-m1-file-no-dups-p)
                 (m1-file-alist m1-file-alist2)
                 (x (car (car m1-file-alist1)))))
     ("subgoal *1/4"
      :use
      (:instance (:rewrite m1-entry-count-when-m1-file-no-dups-p)
                 (m1-file-alist m1-file-alist2)
                 (x (car (car m1-file-alist1))))))))

(defthm
  m1-entry-count-when-m1-dir-equiv
  (implies (and (m1-dir-equiv m1-file-alist1 m1-file-alist2)
                (m1-file-alist-p m1-file-alist2)
                (m1-file-no-dups-p m1-file-alist2))
           (equal (m1-entry-count m1-file-alist1)
                  (m1-entry-count m1-file-alist2)))
  :hints
  (("goal" :in-theory (e/d (m1-dir-equiv)
                           (m1-entry-count-when-m1-dir-subsetp))
    :do-not-induct t
    :use ((:instance m1-entry-count-when-m1-dir-subsetp
                     (m1-file-alist1 m1-file-alist2)
                     (m1-file-alist2 m1-file-alist1))
          m1-entry-count-when-m1-dir-subsetp))))
