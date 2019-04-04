(in-package "ACL2")

;  m1-entry-count.lisp                                 Mihir Mehta

; m1-entry-count is related to the problem of transforming a potentially loopy
; FAT32 disk image into a tree in a bounded amount of time. Some lemmas for
; reasoning about it are placed here.

(include-book "hifat-equiv")

;; We're not counting this very directory, because the root does not have a
;; directory entry for itself.
;;
;; Before disabling, this rule used to cause 436909 frames and 8297 tries in
;; the main book; now those numbers are 4997 and 63 respectively.
(defund m1-entry-count (fs)
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

;; This function is kinda weirdly named now that the when-m1-file-no-dups-p
;; part has been shorn by remove-hyps...
(defthmd
  m1-entry-count-when-m1-file-no-dups-p
  (implies
   (consp (assoc-equal x m1-file-alist))
   (equal
    (m1-entry-count m1-file-alist)
    (+ (m1-entry-count (remove1-assoc x m1-file-alist))
       (if (m1-directory-file-p (cdr (assoc-equal x m1-file-alist)))
           (+ 1
              (m1-entry-count
               (m1-file->contents (cdr (assoc-equal x m1-file-alist)))))
         1))))
  :hints (("goal" :in-theory (enable m1-entry-count))))

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
   (defthm
     induction-scheme-correctness
     (implies (and (m1-file-no-dups-p m1-file-alist1)
                   (m1-file-alist-p m1-file-alist1))
              (iff (induction-scheme m1-file-alist1 m1-file-alist2)
                   (hifat-subsetp m1-file-alist1 m1-file-alist2)))
     :hints (("goal" :induct (induction-scheme m1-file-alist1 m1-file-alist2)
              :in-theory (enable m1-file-no-dups-p)))))

  (defthm
    m1-entry-count-when-hifat-subsetp
    (implies (and (m1-file-no-dups-p m1-file-alist1)
                  (m1-file-alist-p m1-file-alist1)
                  (hifat-subsetp m1-file-alist1 m1-file-alist2))
             (<= (m1-entry-count m1-file-alist1)
                 (m1-entry-count m1-file-alist2)))
    :rule-classes :linear
    :hints
    (("goal" :induct (induction-scheme m1-file-alist1 m1-file-alist2)
      :in-theory (enable m1-file-no-dups-p m1-entry-count))
     ("subgoal *1/7"
      :use (:instance (:rewrite m1-entry-count-when-m1-file-no-dups-p)
                      (m1-file-alist m1-file-alist2)
                      (x (car (car m1-file-alist1)))))
     ("subgoal *1/4"
      :use (:instance (:rewrite m1-entry-count-when-m1-file-no-dups-p)
                      (m1-file-alist m1-file-alist2)
                      (x (car (car m1-file-alist1))))))))

(defthm
  m1-entry-count-when-hifat-equiv
  (implies (and (hifat-equiv m1-file-alist1 m1-file-alist2)
                (m1-file-alist-p m1-file-alist2)
                (m1-file-no-dups-p m1-file-alist2))
           (equal (m1-entry-count m1-file-alist1)
                  (m1-entry-count m1-file-alist2)))
  :hints
  (("goal" :in-theory (e/d (hifat-equiv)
                           (m1-entry-count-when-hifat-subsetp))
    :do-not-induct t
    :use ((:instance m1-entry-count-when-hifat-subsetp
                     (m1-file-alist1 m1-file-alist2)
                     (m1-file-alist2 m1-file-alist1))
          m1-entry-count-when-hifat-subsetp))))
