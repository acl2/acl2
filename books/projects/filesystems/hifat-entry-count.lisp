(in-package "ACL2")

;  hifat-entry-count.lisp                                 Mihir Mehta

; hifat-entry-count is related to the problem of transforming a potentially loopy
; FAT32 disk image into a tree in a bounded amount of time. Some lemmas for
; reasoning about it are placed here.

(include-book "hifat-equiv")

;; We're not counting this very directory, because the root does not have a
;; directory entry for itself.
;;
;; Before disabling, this rule used to cause 436909 frames and 8297 tries in
;; the main book; now those numbers are 4997 and 63 respectively.
(defund
  hifat-entry-count (fs)
  (declare (xargs :guard (and (m1-file-alist-p fs)
                              (hifat-no-dups-p fs))))
  (if
   (atom fs)
   0
   (+
    (hifat-entry-count (cdr fs))
    (if
     (consp
      (assoc-equal (mbe :logic (fat32-filename-fix (caar fs))
                        :exec (caar fs))
                   (mbe :logic (hifat-file-alist-fix (cdr fs))
                        :exec (cdr fs))))
     0
     (if
      (m1-directory-file-p (mbe :logic (m1-file-fix (cdar fs))
                                :exec (cdar fs)))
      (+ 1
         (hifat-entry-count (m1-file->contents (cdar fs))))
      1)))))

(defthm hifat-entry-count-of-hifat-file-alist-fix
  (equal (hifat-entry-count (hifat-file-alist-fix fs))
         (hifat-entry-count fs))
  :hints (("Goal" :in-theory (enable hifat-entry-count)) ))

(defthm
  m1-file-alist-p-of-remove1-assoc-equal
  (implies (m1-file-alist-p m1-file-alist)
           (m1-file-alist-p (remove1-assoc-equal key m1-file-alist))))

(defthmd
  hifat-entry-count-when-hifat-no-dups-p
  (implies
   (and (m1-file-alist-p m1-file-alist)
        (hifat-no-dups-p m1-file-alist)
        (consp (assoc-equal x m1-file-alist)))
   (equal
    (hifat-entry-count m1-file-alist)
    (+
     (hifat-entry-count (remove1-assoc x m1-file-alist))
     1
     (if
      (m1-directory-file-p (cdr (assoc-equal x m1-file-alist)))
      (hifat-entry-count
       (m1-file->contents (cdr (assoc-equal x m1-file-alist))))
      0))))
  :hints
  (("goal"
    :in-theory (enable hifat-entry-count hifat-no-dups-p))))

(defthm
  hifat-entry-count-of-cdr-1
  (implies (and (consp fs)
                (m1-file-alist-p fs)
                (hifat-no-dups-p fs))
           (< (hifat-entry-count (cdr fs))
              (hifat-entry-count fs)))
  :rule-classes :linear
  :hints
  (("goal"
    :in-theory (enable hifat-no-dups-p hifat-entry-count))))

(defthm
  hifat-entry-count-of-cdr-2
  (implies
   (and (consp fs)
        (hifat-no-dups-p fs)
        (m1-file-alist-p fs)
        (not (m1-regular-file-p (cdr (car fs)))))
   (< (+ (hifat-entry-count (m1-file->contents (cdr (car fs))))
         (hifat-entry-count (cdr fs)))
      (hifat-entry-count fs)))
  :rule-classes :linear
  :hints (("goal" :in-theory (enable hifat-no-dups-p)
           :expand (hifat-entry-count fs))))

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
     (implies (and (hifat-no-dups-p m1-file-alist1)
                   (m1-file-alist-p m1-file-alist1))
              (iff (induction-scheme m1-file-alist1 m1-file-alist2)
                   (hifat-subsetp m1-file-alist1 m1-file-alist2)))
     :hints (("goal" :induct (induction-scheme m1-file-alist1 m1-file-alist2)
              :in-theory (enable hifat-no-dups-p)))))

  (defthm
    hifat-entry-count-when-hifat-subsetp
    (implies (and (hifat-no-dups-p m1-file-alist1)
                  (m1-file-alist-p m1-file-alist1)
                  (hifat-no-dups-p m1-file-alist2)
                  (m1-file-alist-p m1-file-alist2)
                  (hifat-subsetp m1-file-alist1 m1-file-alist2))
             (<= (hifat-entry-count m1-file-alist1)
                 (hifat-entry-count m1-file-alist2)))
    :rule-classes :linear
    :hints
    (("goal" :induct (induction-scheme m1-file-alist1 m1-file-alist2)
      :in-theory (enable hifat-no-dups-p hifat-entry-count))
     ("subgoal *1/7"
      :use (:instance (:rewrite hifat-entry-count-when-hifat-no-dups-p)
                      (m1-file-alist m1-file-alist2)
                      (x (car (car m1-file-alist1)))))
     ("subgoal *1/4"
      :use (:instance (:rewrite hifat-entry-count-when-hifat-no-dups-p)
                      (m1-file-alist m1-file-alist2)
                      (x (car (car m1-file-alist1))))))))

;; This rule is kinda problematic because it has caused an infinite rewrite at
;; least once in hifat-to-lofat-inversion-big-induction, which was only
;; resolved by disabling it. It would be nice to make this a plain congruence
;; rule - but that would require the m1-file-alist and hifat-no-dups-p
;; hypotheses to be removed, which in turn would require the definition of
;; hifat-entry-count to be changed.
(defthm
  hifat-entry-count-when-hifat-equiv
  (implies (hifat-equiv m1-file-alist1 m1-file-alist2)
           (equal (hifat-entry-count m1-file-alist1)
                  (hifat-entry-count m1-file-alist2)))
  :rule-classes :congruence
  :hints
  (("goal"
    :in-theory (e/d (hifat-equiv)
                    (hifat-entry-count-when-hifat-subsetp))
    :use
    ((:instance hifat-entry-count-when-hifat-subsetp
                (m1-file-alist1 (hifat-file-alist-fix m1-file-alist2))
                (m1-file-alist2 (hifat-file-alist-fix m1-file-alist1)))
     (:instance hifat-entry-count-when-hifat-subsetp
                (m1-file-alist1 (hifat-file-alist-fix m1-file-alist1))
                (m1-file-alist2 (hifat-file-alist-fix m1-file-alist2)))))))

(defthm hifat-entry-count-of-remove-assoc-equal
  (implies (and (m1-file-alist-p fs)
                (hifat-no-dups-p fs)
                (consp (assoc-equal x fs)))
           (< (hifat-entry-count (remove-assoc-equal x fs))
              (hifat-entry-count fs)))
  :hints (("goal" :in-theory (e/d (hifat-entry-count hifat-no-dups-p))
           :induct (assoc-equal x fs)))
  :rule-classes :linear)

(local
 (defthm hifat-entry-count-of-put-assoc-equal-lemma-1
   (implies (and (m1-file-alist-p fs)
                 (not (fat32-filename-p x)))
            (not (consp (assoc-equal x fs))))
   :hints (("goal" :in-theory (enable m1-file-alist-p)))))

(defthm
  hifat-entry-count-of-put-assoc-equal-lemma-2
  (implies
   (and
    (not (equal name (car (car fs))))
    (equal
     (hifat-entry-count (put-assoc-equal name val (cdr fs)))
     (+ (hifat-entry-count (cdr fs))
        (hifat-entry-count (m1-file->contents val))
        (- (hifat-entry-count
            (m1-file->contents (cdr (assoc-equal name (cdr fs))))))))
    (m1-file-alist-p fs)
    (hifat-no-dups-p fs)
    (m1-directory-file-p (cdr (assoc-equal name (cdr fs))))
    (m1-directory-file-p val)
    (hifat-no-dups-p (m1-file->contents val))
    (consp (assoc-equal
            (car (car fs))
            (hifat-file-alist-fix (put-assoc-equal name val (cdr fs))))))
   (equal
    (hifat-entry-count (put-assoc-equal name val (cdr fs)))
    (+ (hifat-entry-count fs)
       (hifat-entry-count (m1-file->contents val))
       (- (hifat-entry-count
           (m1-file->contents (cdr (assoc-equal name (cdr fs)))))))))
  :hints
  (("goal"
    :in-theory (e/d (hifat-entry-count hifat-no-dups-p)
                    (hifat-file-alist-fix-when-hifat-no-dups-p))
    :use ((:instance (:rewrite hifat-file-alist-fix-when-hifat-no-dups-p)
                     (hifat-file-alist (put-assoc-equal name val (cdr fs))))
          (:instance (:rewrite hifat-file-alist-fix-when-hifat-no-dups-p)
                     (hifat-file-alist (cdr fs)))))))

(defthm
  consp-of-assoc-of-hifat-file-alist-fix
  (implies (m1-file-alist-p hifat-file-alist)
           (iff (consp (assoc-equal name
                                    (hifat-file-alist-fix hifat-file-alist)))
                (consp (assoc-equal name hifat-file-alist))))
  :hints (("goal" :in-theory (enable hifat-file-alist-fix)
           :induct (assoc-equal name hifat-file-alist))))

(defthm
  hifat-entry-count-of-put-assoc-equal
  (implies
   (and (m1-file-alist-p fs)
        (hifat-no-dups-p fs)
        (m1-file-p val)
        (fat32-filename-p name))
   (equal
    (hifat-entry-count (put-assoc-equal name val fs))
    (+
     (hifat-entry-count fs)
     (if
      (atom (assoc-equal name fs))
      1
      (if
       (m1-directory-file-p (cdr (assoc-equal name fs)))
       (- (hifat-entry-count (m1-file->contents (cdr (assoc-equal name fs)))))
       0))
     (if (m1-directory-file-p val)
         (hifat-entry-count (m1-file->contents val))
         0))))
  :hints (("goal" :in-theory (enable hifat-entry-count hifat-no-dups-p)
           :induct (assoc-equal name fs))))

(defthm
  hifat-entry-count-of-hifat-remove-file
  (implies (equal (mv-nth 1 (hifat-remove-file fs pathname))
                  0)
           (< (hifat-entry-count (mv-nth 0 (hifat-remove-file fs pathname)))
              (hifat-entry-count fs)))
  :hints (("goal" :in-theory (enable hifat-remove-file)))
  :rule-classes :linear)
