; Copyright (C) 2017, Regents of the University of Texas
; Written by Mihir Mehta
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

;  file-system-4.lisp                                  Mihir Mehta

; Here we define a more complex file system with a disk and an allocation bitmap.
; We first start with a file-system recognizer, and then we define various
; file-system operations.

; There used to be a long comment here about converting an instance of l4 to an
; instance of l3. We ended up bypassing this by converting to l2 instead, so
; the comment is no longer pertinent.

(include-book "file-system-3")
(include-book "find-n-free-blocks")
(include-book "set-indices")

(defthm mv-nth-replacement
  (equal (mv-nth n (cons a b))
         (if (zp n) a (mv-nth (- n 1) b))))

(in-theory (disable mv-nth))

;; could be handled differently using repeat... let's see.
(defun indices-marked-p (index-list alv)
  (declare (xargs :guard (and (nat-listp index-list) (boolean-listp alv))))
  (or (atom index-list)
      (and (nth (car index-list) alv) (indices-marked-p (cdr index-list) alv))))

(defthm indices-marked-p-correctness-1
  (implies (and (indices-marked-p index-list alv)
                (equal b (len alv))
                (nat-listp index-list))
           (bounded-nat-listp index-list b)))

(defthm indices-marked-p-correctness-2
  (equal
   (indices-marked-p (binary-append x y) alv)
   (and (indices-marked-p x alv) (indices-marked-p y alv))))

(defthm
  indices-marked-p-correctness-3
  (implies (and (nat-listp index-list1)
                (nat-listp index-list2)
                (boolean-listp alv)
                (indices-marked-p index-list1 alv)
                (bounded-nat-listp index-list1 (len alv)))
           (indices-marked-p index-list1
                             (set-indices-in-alv alv index-list2 t)))
  :hints
  (("subgoal *1/5''" :in-theory (disable set-indices-in-alv-correctness-3
                                         set-indices-in-alv-correctness-4)
    :use ((:instance set-indices-in-alv-correctness-3
                     (value t)
                     (n (car index-list1))
                     (index-list index-list2))
          (:instance set-indices-in-alv-correctness-4
                     (value t)
                     (n (car index-list1))
                     (index-list index-list2)))
    :cases (member-equal (car index-list1)
                         index-list2))))

(encapsulate
  ()

  (local (defun induction-scheme (l1 l2)
           (if (atom l2)
               l1
             (induction-scheme (binary-append l1 (cons (car l2) nil)) (cdr l2)))))

  (defthm
    indices-marked-p-correctness-4
    (implies (and (boolean-listp alv)
                  (bounded-nat-listp index-list1 (len alv))
                  (bounded-nat-listp index-list2 (len alv)))
             (indices-marked-p
              index-list2
              (set-indices-in-alv alv
                                  (binary-append index-list1 index-list2)
                                  t)))
    :hints (("Goal" :induct (induction-scheme index-list1 index-list2))))

  )

(defthm
  indices-marked-p-correctness-5
  (implies (and (boolean-listp alv)
                (bounded-nat-listp index-list (len alv)))
           (indices-marked-p index-list
                             (set-indices-in-alv alv index-list t)))
  :hints (("Goal" :in-theory (disable indices-marked-p-correctness-4)
           :use (:instance indices-marked-p-correctness-4
                           (index-list2 index-list)
                           (index-list1 nil)))))

(defun l4-regular-file-entry-p (entry)
  (declare (xargs :guard t))
  (l3-regular-file-entry-p entry))

(defun l4-fs-p (fs)
  (declare (xargs :guard t))
  (l3-fs-p fs))

(defun l4-stat (hns fs disk)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l4-fs-p fs)
                              (block-listp disk))))
  (l3-stat hns fs disk))

(defun l4-rdchs (hns fs disk start n)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l4-fs-p fs)
                              (natp start)
                              (natp n)
                              (block-listp disk))))
  (l3-rdchs hns fs disk start n))

(defun l4-wrchs (hns fs disk alv start text)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l4-fs-p fs)
                              (natp start)
                              (stringp text)
                              (block-listp disk)
                              (boolean-listp alv)
                              (equal (len alv) (len disk)))))
  (if (atom hns)
      (mv fs disk alv) ;; error - showed up at fs with no name  - so leave fs unchanged
    (if (atom fs)
        (mv nil disk alv) ;; error, so leave fs unchanged
      (let ((sd (assoc (car hns) fs)))
        (if (atom sd)
            (mv fs disk alv) ;; file-not-found error, so leave fs unchanged
          (let ((contents (cdr sd)))
            (if (l3-regular-file-entry-p contents)
                (if (cdr hns)
                    (mv (cons (cons (car sd) contents)
                              (delete-assoc (car hns) fs))
                        disk
                        alv) ;; error, so leave fs unchanged
                  (let* ((old-text
                          (unmake-blocks
                           (fetch-blocks-by-indices disk (car contents))
                           (cdr contents)))
                         (alv-after-free
                          (set-indices-in-alv alv (car contents) nil))
                         (new-text (insert-text old-text start text))
                         (new-blocks (make-blocks new-text))
                         (new-indices
                          (find-n-free-blocks alv-after-free (len new-blocks))))
                    (if (not (equal (len new-indices) (len new-blocks)))
                        ;; we have an error because of insufficient disk space
                        ;; - so we leave the fs unchanged
                        (mv (cons (cons (car sd) contents)
                                  (delete-assoc (car hns) fs))
                            disk
                            alv)
                      (mv (cons (cons (car sd)
                                      (cons new-indices (len new-text)))
                                (delete-assoc (car hns) fs))
                          ;; this (take) means we write as many blocks as we can
                          ;; if we run out of space
                          (set-indices disk new-indices new-blocks)
                          (set-indices-in-alv alv-after-free new-indices t)))))
              (mv-let (new-contents new-disk new-alv)
                (l4-wrchs (cdr hns) contents disk alv start text)
                (mv (cons (cons (car sd) new-contents)
                          (delete-assoc (car hns) fs))
                    new-disk
                    new-alv)))
            ))))))

(defund
  l4-list-all-indices (fs)
  (declare (xargs :guard (l4-fs-p fs)))
  (if (atom fs)
      nil
      (binary-append
       (let ((directory-or-file-entry (car fs)))
            (let ((entry (cdr directory-or-file-entry)))
                 (if (l4-regular-file-entry-p entry)
                     (car entry)
                     (l4-list-all-indices entry))))
       (l4-list-all-indices (cdr fs)))))

(defthm l4-list-all-indices-correctness-1
  (implies (l4-fs-p fs)
           (nat-listp (l4-list-all-indices fs)))
  :hints (("Goal" :in-theory (enable l4-list-all-indices)) ))

(defun l4-stricter-fs-p (fs alv)
  (declare (xargs :guard t))
  (and (l4-fs-p fs)
       (boolean-listp alv)
       (let ( (all-indices (l4-list-all-indices fs)))
         (and (nat-listp all-indices)
              (no-duplicatesp all-indices)
              (indices-marked-p all-indices alv)))))

(defthm l4-wrchs-returns-fs
  (implies (and (symbol-listp hns)
                (l3-fs-p fs)
                (boolean-listp alv)
                (integerp start)
                (<= 0 start)
                (stringp text)
                (block-listp disk))
           (l3-fs-p (mv-nth 0 (l4-wrchs hns fs disk alv start text))))
  :hints (("Subgoal *1/5'''" :in-theory (enable l3-regular-file-entry-p))
          ("Subgoal *1/6'4'" :in-theory (enable l3-regular-file-entry-p))))

(defthm l4-wrchs-returns-alv
  (implies (and (symbol-listp hns)
                (l3-fs-p fs)
                (boolean-listp alv)
                (integerp start)
                (<= 0 start)
                (stringp text)
                (block-listp disk))
           (boolean-listp (mv-nth 2 (l4-wrchs hns fs disk alv start text)))))

(defun l4-collect-all-index-lists (fs)
  (declare (xargs :guard (l4-fs-p fs)))
  (if (atom fs)
      nil
    (let* ((directory-or-file-entry (car fs))
           (entry (cdr directory-or-file-entry))
           (tail (l4-collect-all-index-lists (cdr fs))))
      (if (l4-regular-file-entry-p entry)
          (cons (car entry) tail)
        (binary-append (l4-collect-all-index-lists entry) tail))))
  )

(defthm l4-collect-all-index-lists-correctness-1
  (implies (l3-fs-p fs)
           (true-list-listp (l4-collect-all-index-lists fs))))

(include-book "flatten-lemmas")

  ;; This theorem shows the equivalence between two ways of listing indices

(defthm l4-collect-all-index-lists-correctness-2
  (implies (l3-fs-p fs)
           (equal (flatten (l4-collect-all-index-lists fs))
                  (l4-list-all-indices fs)))
  :hints (("Goal" :in-theory (enable l4-list-all-indices)) ))

(defthm
  l4-collect-all-index-lists-correctness-3
  (implies
   (l3-fs-p fs)
   (equal (no-duplicatesp-equal (l4-list-all-indices fs))
          (and (disjoint-list-listp (l4-collect-all-index-lists fs))
               (no-duplicates-listp (l4-collect-all-index-lists fs)))))
  :hints
  (("goal" :in-theory (disable flatten-disjoint-lists)
    :use ((:instance flatten-disjoint-lists
                     (l (l4-collect-all-index-lists fs)))))))

(defun indices-marked-listp (l alv)
  (if (atom l)
      (equal l nil)
    (and (indices-marked-p (car l) alv) (indices-marked-listp (cdr l) alv))))

(defthm indices-marked-p-of-flatten
  (implies (true-listp l)
           (equal (indices-marked-p (flatten l) alv)
                  (indices-marked-listp l alv))))

(defthm l4-indices-marked-p-of-list-all-indices
  (implies (l3-fs-p fs)
           (equal (indices-marked-p (l4-list-all-indices fs)
                                    alv)
                  (indices-marked-listp (l4-collect-all-index-lists fs)
                                        alv)))
  :hints (("goal" :in-theory (disable indices-marked-p-of-flatten)
           :use (:instance indices-marked-p-of-flatten
                           (l (l4-collect-all-index-lists fs))))))

(defthm indices-marked-listp-of-binary-append
  (implies (true-listp l1)
   (equal (indices-marked-listp (binary-append l1 l2) alv)
          (and (indices-marked-listp l1 alv)
               (indices-marked-listp l2 alv)))))

;; this should be where the encapsulate ends

(defthm l4-wrchs-returns-stricter-fs-lemma-1
  (implies
   (and
    (consp (assoc-equal name fs))
    (not (l3-regular-file-entry-p (cdr (assoc-equal name fs))))
    (l3-fs-p fs)
    (disjoint-list-listp (l4-collect-all-index-lists fs)))
   (disjoint-list-listp
    (l4-collect-all-index-lists (cdr (assoc-equal name fs))))))

(defthm l4-wrchs-returns-stricter-fs-lemma-2
  (implies
   (and (consp (assoc-equal name fs))
        (not (l3-regular-file-entry-p (cdr (assoc-equal name fs))))
        (l3-fs-p fs)
        (indices-marked-listp (l4-collect-all-index-lists fs)
                              alv))
   (indices-marked-listp
    (l4-collect-all-index-lists (cdr (assoc-equal name fs)))
    alv)))

(defthm l4-wrchs-returns-stricter-fs-lemma-3
  (implies
   (and
    (consp (assoc-equal name fs))
    (not (l3-regular-file-entry-p (cdr (assoc-equal name fs))))
    (l3-fs-p fs)
    (no-duplicates-listp (l4-collect-all-index-lists fs)))
   (no-duplicates-listp
    (l4-collect-all-index-lists (cdr (assoc-equal name fs))))))

(defthm l4-wrchs-returns-stricter-fs-lemma-4
  (implies (member-intersectp-equal l b)
           (member-intersectp-equal l (cons a b))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-5
  (implies
   (and (l3-fs-p fs)
        (not (member-intersectp-equal (l4-collect-all-index-lists fs)
                                      l)))
   (not (member-intersectp-equal
         l
         (l4-collect-all-index-lists (delete-assoc-equal name fs))))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-6
  (implies (and (l3-fs-p fs)
                (not-intersectp-list l (l4-collect-all-index-lists fs)))
           (not-intersectp-list
            l
            (l4-collect-all-index-lists (delete-assoc-equal name fs)))))

(defthm l4-wrchs-returns-stricter-fs-lemma-7
  (implies
   (and (l3-fs-p fs)
        (disjoint-list-listp (l4-collect-all-index-lists fs)))
   (disjoint-list-listp
    (l4-collect-all-index-lists (delete-assoc-equal name fs)))))

(defthm l4-wrchs-returns-stricter-fs-lemma-8
  (implies
   (and (l3-fs-p fs)
        (no-duplicates-listp (l4-collect-all-index-lists fs)))
   (no-duplicates-listp
    (l4-collect-all-index-lists (delete-assoc-equal name fs)))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-9
  (implies (and (l3-fs-p fs)
                (boolean-listp alv)
                (indices-marked-listp (l4-collect-all-index-lists fs)
                                      alv))
           (indices-marked-listp
            (l4-collect-all-index-lists (delete-assoc-equal name fs))
            alv)))

(defthm l4-wrchs-returns-stricter-fs-lemma-10
  (implies (and (l3-regular-file-entry-p (cdr (assoc-equal name fs)))
                (l3-fs-p fs)
                (boolean-listp alv)
                (indices-marked-listp (l4-collect-all-index-lists fs)
                                      alv))
           (indices-marked-p (cadr (assoc-equal name fs))
                             alv)))

(defthm l4-wrchs-returns-stricter-fs-lemma-11
  (implies (and (l3-regular-file-entry-p (cdr (assoc-equal name fs)))
                (l3-fs-p fs)
                (no-duplicates-listp (l4-collect-all-index-lists fs)))
           (no-duplicatesp-equal (cadr (assoc-equal name fs)))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-12
  (implies (and (l3-regular-file-entry-p (cdr (assoc-equal name fs)))
                (l3-fs-p fs)
                (not-intersectp-list l (l4-collect-all-index-lists fs)))
           (not (intersectp-equal l (cadr (assoc-equal name fs))))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-13
  (implies (and (l3-regular-file-entry-p (cdr (assoc-equal name fs)))
                (l3-fs-p fs)
                (not (member-intersectp-equal (l4-collect-all-index-lists fs)
                                              l)))
           (not-intersectp-list (cadr (assoc-equal name fs))
                                l)))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-14
  (implies (and (l3-regular-file-entry-p (cdr (assoc-equal name fs)))
                (l3-fs-p fs)
                (disjoint-list-listp (l4-collect-all-index-lists fs)))
           (not-intersectp-list
            (cadr (assoc-equal name fs))
            (l4-collect-all-index-lists (delete-assoc-equal name fs)))))

(defthm l4-wrchs-returns-stricter-fs-lemma-15
  (implies (and (boolean-listp alv)
                (indices-marked-p l alv)
                (natp n))
           (not (intersectp-equal l (find-n-free-blocks alv n)))))

(defthm l4-wrchs-returns-stricter-fs-lemma-16
  (implies (and (natp n)
                (l3-fs-p fs)
                (boolean-listp alv)
                (indices-marked-listp (l4-collect-all-index-lists fs)
                                      alv))
           (not-intersectp-list (find-n-free-blocks alv n)
                                (l4-collect-all-index-lists fs))))

(encapsulate ()
  (local (include-book "std/basic/inductions" :dir :system))

  (defcong list-equiv equal (indices-marked-p index-list alv) 1
    :hints
    (("goal"
      :induct (cdr-cdr-induct index-list index-list-equiv))))

  (defcong list-equiv equal (fetch-blocks-by-indices block-list index-list) 2
    :hints
    (("goal"
      :induct (cdr-cdr-induct index-list index-list-equiv))))


  (defcong list-equiv equal (l4-list-all-indices fs) 1
    :hints (("Goal" :in-theory (enable l4-list-all-indices)
             :induct (cdr-cdr-induct fs fs-equiv))
            ("Subgoal *1/2''" :expand ((l4-list-all-indices fs)
                                       (l4-list-all-indices fs-equiv)))))

  (defcong list-equiv equal (l3-to-l2-fs fs disk) 1
    :hints (("goal" :induct (cdr-cdr-induct fs fs-equiv))
            ("Subgoal *1/2''" :expand ((l3-to-l2-fs fs disk)
                                       (l3-to-l2-fs fs-equiv disk)))))

  )

(defcong list-equiv equal (indices-marked-p index-list alv) 2)

(defcong list-equiv list-equiv
  (set-indices-in-alv alv index-list value) 1
  :hints (("goal" :in-theory (enable set-indices-in-alv))))

(defthm l4-wrchs-returns-stricter-fs-lemma-17
  (implies (and (boolean-listp alv)
                (nat-listp l)
                (bounded-nat-listp index-list (len alv))
                (indices-marked-p index-list alv)
                (not (intersectp-equal l index-list)))
           (indices-marked-p index-list
                             (set-indices-in-alv alv l nil))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-18
  (implies (and (l3-fs-p fs)
                (nat-listp l)
                (boolean-listp alv)
                (indices-marked-listp (l4-collect-all-index-lists fs)
                                      alv)
                (not-intersectp-list l (l4-collect-all-index-lists fs)))
           (indices-marked-listp (l4-collect-all-index-lists fs)
                                 (set-indices-in-alv alv l nil))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-19
  (implies (and (l3-fs-p fs)
                (nat-listp l)
                (boolean-listp alv)
                (indices-marked-listp (l4-collect-all-index-lists fs)
                                      alv))
           (indices-marked-listp (l4-collect-all-index-lists fs)
                                 (set-indices-in-alv alv l t))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-20
  (implies
   (and (consp (assoc-equal name fs))
        (not (l3-regular-file-entry-p (cdr (assoc-equal name fs))))
        (l3-fs-p fs)
        (not (member-intersectp-equal l (l4-collect-all-index-lists fs))))
   (not (member-intersectp-equal
         l
         (l4-collect-all-index-lists (cdr (assoc-equal name fs)))))))

(defthm l4-wrchs-returns-stricter-fs-lemma-21
  (implies (and (natp n)
                (boolean-listp alv)
                (indices-marked-listp l alv))
           (not-intersectp-list (find-n-free-blocks alv n)
                                l)))

(defcong list-equiv equal (INDICES-MARKED-LISTP L ALV) 2)

(defthm
  l4-wrchs-returns-stricter-fs-lemma-22
  (implies (and (boolean-listp alv)
                (nat-listp index-list)
                (true-list-listp l)
                (bounded-nat-listp (flatten l)
                                   (len alv))
                (indices-marked-listp l alv)
                (not-intersectp-list index-list l))
           (indices-marked-listp l
                                 (set-indices-in-alv alv index-list nil)))
  :hints (("Subgoal *1/6" :expand (flatten l))))

(defthm l4-wrchs-returns-stricter-fs-lemma-23
  (implies (and (true-list-listp l)
                (indices-marked-listp l alv)
                (nat-listp (flatten l)))
           (bounded-nat-listp (flatten l) (len alv))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-24
  (implies (and (l3-regular-file-entry-p (cdr (assoc-equal name fs)))
                (l3-fs-p fs)
                (boolean-listp alv)
                (bounded-nat-listp (l4-list-all-indices fs)
                                   (len alv)))
           (bounded-nat-listp (cadr (assoc-equal name fs))
                              (len alv)))
  :hints (("goal" :induct (l4-list-all-indices fs)
           :in-theory (enable l4-list-all-indices))))

(defthm l4-wrchs-returns-stricter-fs-lemma-25
  (implies (and (l3-fs-p fs)
                (boolean-listp alv)
                (indices-marked-listp (l4-collect-all-index-lists fs)
                                      alv))
           (bounded-nat-listp (l4-list-all-indices fs)
                              (len alv)))
  :hints (("goal" :induct (l4-list-all-indices fs)
           :in-theory (enable l4-list-all-indices))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-26
  (implies (and (consp (assoc-equal name fs))
                (not (l3-regular-file-entry-p (cdr (assoc-equal name fs))))
                (l3-fs-p fs)
                (not-intersectp-list l (l4-collect-all-index-lists fs)))
           (not-intersectp-list
            l
            (l4-collect-all-index-lists (cdr (assoc-equal name fs))))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-27
  (implies
   (and
    (l3-fs-p fs)
    (symbol-listp hns)
    (boolean-listp alv)
    (indices-marked-listp (l4-collect-all-index-lists fs)
                          alv)
    (integerp start)
    (<= 0 start)
    (stringp text)
    (block-listp disk)
    (equal (len alv) (len disk))
    (bounded-nat-listp l (len alv))
    (not-intersectp-list l (l4-collect-all-index-lists fs))
    (indices-marked-p l alv))
   (indices-marked-p l
                     (mv-nth 2
                             (l4-wrchs hns fs disk alv start text))))
  :hints
  (("Subgoal *1/5"
    :in-theory (disable indices-marked-p-correctness-3)
    :use
    ((:instance
      indices-marked-p-correctness-3
      (index-list1 l)
      (alv (set-indices-in-alv alv (cadr (assoc-equal (car hns) fs))
                               nil))
      (index-list2
       (find-n-free-blocks
        (set-indices-in-alv alv (cadr (assoc-equal (car hns) fs))
                            nil)
        (len
         (make-blocks
          (insert-text
           (unmake-blocks
            (fetch-blocks-by-indices disk (cadr (assoc-equal (car hns) fs)))
            (cddr (assoc-equal (car hns) fs)))
           start text))))))
     (:instance set-indices-in-alv-correctness-2
                (index-list (cadr (assoc-equal (car hns) fs)))
                (value nil))
     (:instance
      indices-marked-p-correctness-1
      (index-list l)
      (b (len (set-indices-in-alv alv (cadr (assoc-equal (car hns) fs))
                                  nil))))))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-28
  (implies
   (and (l3-fs-p fs)
        (symbol-listp hns)
        (boolean-listp alv)
        (indices-marked-listp (l4-collect-all-index-lists fs)
                              alv)
        (integerp start)
        (<= 0 start)
        (stringp text)
        (block-listp disk)
        (equal (len alv) (len disk))
        (bounded-nat-listp (flatten l)
                           (len alv))
        (not (member-intersectp-equal l (l4-collect-all-index-lists fs)))
        (indices-marked-listp l alv)
        (true-list-listp l))
   (indices-marked-listp l
                         (mv-nth 2
                                 (l4-wrchs hns fs disk alv start text))))
  :hints (("Goal" :induct (indices-marked-listp l alv))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-29
  (implies
   (and (l3-fs-p fs)
        (boolean-listp alv)
        (indices-marked-listp (l4-collect-all-index-lists fs)
                              alv))
   (bounded-nat-listp
    (flatten (l4-collect-all-index-lists (delete-assoc-equal (car hns) fs)))
    (len alv)))
  :hints
  (("Goal" :in-theory (disable l4-collect-all-index-lists-correctness-2))
   ("Subgoal *1/2.2'"
    :in-theory (disable indices-marked-p-correctness-1)
    :use
    ((:instance indices-marked-p-correctness-1
                (index-list (flatten (l4-collect-all-index-lists (cdr fs))))
                (b (len alv)))))
   ("Subgoal *1/3.1'"
    :in-theory (disable indices-marked-p-correctness-1)
    :use
    ((:instance
      indices-marked-p-correctness-1
      (index-list (flatten (l4-collect-all-index-lists (cdr (car fs)))))
      (b (len alv)))))
   ("Subgoal *1/3.2'"
    :in-theory (disable indices-marked-p-correctness-1)
    :use
    ((:instance indices-marked-p-correctness-1
                (index-list (flatten (l4-collect-all-index-lists (cdr fs))))
                (b (len alv)))))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-30
  (implies
   (and (consp (assoc-equal name fs))
        (not (l3-regular-file-entry-p (cdr (assoc-equal name fs))))
        (l3-fs-p fs)
        (disjoint-list-listp (l4-collect-all-index-lists fs))
        (no-duplicates-listp (l4-collect-all-index-lists fs)))
   (not (member-intersectp-equal
         (l4-collect-all-index-lists (delete-assoc-equal name fs))
         (l4-collect-all-index-lists (cdr (assoc-equal name fs))))))
  :hints
  (("Subgoal *1/7''"
    :in-theory (disable member-intersectp-is-commutative)
    :use
    (:instance
     member-intersectp-is-commutative
     (x (l4-collect-all-index-lists (cdr (assoc-equal name (cdr fs)))))
     (y
      (cons
       (cadr (car fs))
       (l4-collect-all-index-lists (delete-assoc-equal name
                                                       (cdr fs)))))))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-31
  (implies
   (and (symbol-listp hns)
        (l3-fs-p fs)
        (boolean-listp alv)
        (indices-marked-listp (l4-collect-all-index-lists fs)
                              alv)
        (integerp start)
        (<= 0 start)
        (stringp text)
        (block-listp disk)
        (equal (len alv) (len disk))
        (not-intersectp-list l (l4-collect-all-index-lists fs))
        (indices-marked-p l alv)
        (nat-listp l))
   (not-intersectp-list l
                        (l4-collect-all-index-lists
                         (mv-nth 0
                                 (l4-wrchs hns fs disk alv start text)))))
  :hints (("subgoal *1/6.2" :in-theory (enable l3-regular-file-entry-p))
          ("subgoal *1/5.2" :in-theory (enable l3-regular-file-entry-p))
          ("subgoal *1/4.2" :in-theory (enable l3-regular-file-entry-p))
          ("subgoal *1/3.2" :in-theory (enable l3-regular-file-entry-p))))

(defthm
  l4-wrchs-returns-stricter-fs-lemma-32
  (implies
   (and (symbol-listp hns)
        (l3-fs-p fs)
        (boolean-listp alv)
        (indices-marked-listp (l4-collect-all-index-lists fs)
                              alv)
        (integerp start)
        (<= 0 start)
        (stringp text)
        (block-listp disk)
        (equal (len alv) (len disk))
        (not (member-intersectp-equal l (l4-collect-all-index-lists fs)))
        (indices-marked-listp l alv)
        (nat-listp (flatten l))
        (true-list-listp l))
   (not (member-intersectp-equal
         l
         (l4-collect-all-index-lists
          (mv-nth 0
                  (l4-wrchs hns fs disk alv start text))))))
  :hints (("Goal" :induct (indices-marked-listp l alv))
          ("Subgoal *1/2" :expand (flatten l))))

(defthm l4-wrchs-returns-stricter-fs-lemma-33
  (implies
   (and (symbol-listp hns)
        (l3-fs-p fs)
        (boolean-listp alv)
        (disjoint-list-listp (l4-collect-all-index-lists fs))
        (no-duplicates-listp (l4-collect-all-index-lists fs))
        (indices-marked-listp (l4-collect-all-index-lists fs)
                              alv)
        (integerp start)
        (<= 0 start)
        (stringp text)
        (block-listp disk)
        (equal (len alv) (len disk)))
   (and
    (indices-marked-listp
     (l4-collect-all-index-lists (mv-nth 0
                                         (l4-wrchs hns fs disk alv start text)))
     (mv-nth 2
             (l4-wrchs hns fs disk alv start text)))
    (disjoint-list-listp (l4-collect-all-index-lists
                          (mv-nth 0
                                  (l4-wrchs hns fs disk alv start text))))))
  :hints (("Goal" :induct t)
          ("Subgoal *1/7.2" :in-theory (disable l4-collect-all-index-lists-correctness-2))
          ("Subgoal *1/7''" :in-theory (disable l4-collect-all-index-lists-correctness-2))
          ("subgoal *1/6" :in-theory (enable l3-regular-file-entry-p))))

;; find a simpler problem that doesn't have all these details, that shows the
;; same kind of issue
(defthm l4-wrchs-returns-stricter-fs
  (implies (and (symbol-listp hns)
                (l4-stricter-fs-p fs alv)
                (natp start)
                (stringp text)
                (block-listp disk)
                (equal (len alv) (len disk)))
           (mv-let (new-fs new-disk new-alv)
             (l4-wrchs hns fs disk alv start text)
             (declare (ignore new-disk))
             (l4-stricter-fs-p new-fs new-alv)))
  :hints (("Subgoal *1/6" :in-theory (enable L3-REGULAR-FILE-ENTRY-P))))

(defun l4-to-l2-fs (fs disk)
  (declare (xargs :guard (and (l4-fs-p fs) (block-listp disk))
                  ))
  (l3-to-l2-fs fs disk))

;; This theorem shows the type-correctness of l4-to-l2-fs.
(defthm l4-to-l2-fs-correctness-1
  (implies (and (l4-fs-p fs) (block-listp disk))
           (l2-fs-p (l4-to-l2-fs fs disk))))

;; This is the first of two theorems showing the equivalence of the l4 and l2
;; versions of stat.
(defthm l4-stat-correctness-1
  (implies (and (symbol-listp hns)
                (l4-fs-p fs)
                (block-listp disk)
                (stringp (l4-stat hns fs disk)))
           (equal (l2-stat hns (l4-to-l2-fs fs disk))
                  (l4-stat hns fs disk))))

;; This is the second of two theorems showing the equivalence of the l4 and l2
;; versions of stat.
(defthm l4-stat-correctness-2
  (implies (and (symbol-listp hns)
                (l4-fs-p fs)
                (block-listp disk)
                (l4-fs-p (l4-stat hns fs disk)))
           (equal (l2-stat hns (l4-to-l2-fs fs disk))
                  (l4-to-l2-fs (l4-stat hns fs disk) disk)))
  )

;; This theorem proves the equivalence of the l4 and l2 versions of rdchs.
(defthm l4-rdchs-correctness-1
  (implies (and (symbol-listp hns)
                (l4-fs-p fs)
                (natp start)
                (natp n)
                (block-listp disk))
           (equal (l2-rdchs hns (l4-to-l2-fs fs disk) start n)
                  (l4-rdchs hns fs disk start n))))

(defcong list-equiv equal (fetch-blocks-by-indices block-list index-list) 1)

(defthm
  l4-wrchs-correctness-1-lemma-1
  (implies (and (natp key)
                (< key (len block-list))
                (block-listp block-list)
                (nat-listp index-list)
                (not (member-equal key index-list)))
           (equal (fetch-blocks-by-indices (update-nth key val block-list)
                                           index-list)
                  (fetch-blocks-by-indices block-list index-list))))

(defthm l4-wrchs-correctness-1-lemma-2
  (implies (and (l3-regular-file-entry-p (cdr (car fs)))
                (not (member-equal index (l4-list-all-indices fs))))
           (not (member-equal index (cadr (car fs)))))
  :hints (("goal" :in-theory (enable l4-list-all-indices))))

(defthm
  l4-wrchs-correctness-1-lemma-3
  (implies (and (consp fs)
                (l3-fs-p fs)
                (member-equal index (l4-list-all-indices (cdr fs))))
           (member-equal index (l4-list-all-indices fs)))
  :hints (("goal" :expand (l4-list-all-indices fs))))

(defthm
  l4-wrchs-correctness-1-lemma-4
  (implies (and (l3-fs-p fs)
                (consp (car fs))
                (l3-fs-p (cdr (car fs)))
                (member-equal index
                              (l4-list-all-indices (cdr (car fs)))))
           (member-equal index (l4-list-all-indices fs)))
  :hints (("goal" :expand (l4-list-all-indices fs))))

(defcong list-equiv equal (l3-to-l2-fs fs disk) 2)

(defthm l4-wrchs-correctness-1-lemma-5
  (implies (and (l3-fs-p fs)
                (block-listp disk)
                (integerp index)
                (<= 0 index)
                (< index (len disk))
                (not (member-equal index (l4-list-all-indices fs))))
           (equal (l3-to-l2-fs fs (update-nth index value disk))
                  (l3-to-l2-fs fs disk))))

(defthm l4-wrchs-correctness-1-lemma-6
  (implies (and (consp index-list)
                (member-equal (car index-list)
                              (l4-list-all-indices fs))
                (l3-fs-p fs)
                (nat-listp (cdr index-list)))
           (not (not-intersectp-list index-list
                                     (l4-collect-all-index-lists fs))))
  :hints (("goal" :in-theory (enable l4-list-all-indices))))

(defthm
  l4-wrchs-correctness-1-lemma-7
  (implies (and (consp index-list)
                (not (not-intersectp-list (cdr index-list)
                                          (l4-collect-all-index-lists fs)))
                (l3-fs-p fs))
           (not (not-intersectp-list index-list
                                     (l4-collect-all-index-lists fs))))
  :hints (("goal" :in-theory (enable l4-collect-all-index-lists))))

(defthm l4-wrchs-correctness-1-lemma-8
  (implies (and (block-listp disk)
                (natp key)
                (< key (len disk))
                (character-listp val)
                (equal (len val) *blocksize*))
           (block-listp (update-nth key val disk))))

(defthm
  l4-wrchs-correctness-1-lemma-9
  (implies (and (l3-fs-p fs)
                (block-listp disk)
                (not-intersectp-list index-list
                                     (l4-collect-all-index-lists fs))
                (bounded-nat-listp index-list (len disk))
                (block-listp value-list)
                (equal (len value-list)
                       (len index-list)))
           (equal (l3-to-l2-fs fs
                               (set-indices disk index-list value-list))
                  (l3-to-l2-fs fs disk)))
  :hints
  (("subgoal *1/7''" :in-theory (disable l4-wrchs-correctness-1-lemma-5)
    :use (:instance l4-wrchs-correctness-1-lemma-5
                    (index (car index-list))
                    (value (car value-list))))))

(defthm
  l4-wrchs-correctness-1-lemma-10
  (implies (and (natp n)
                (boolean-listp alv)
                (indices-marked-p index-list alv))
           (not (intersectp-equal index-list (find-n-free-blocks alv n)))))

(defthm l4-wrchs-correctness-1-lemma-11
  (implies (and (natp n)
                (boolean-listp alv)
                (indices-marked-listp l alv))
           (not-intersectp-list (find-n-free-blocks alv n)
                                l)))

(defthm
  l4-wrchs-correctness-1-lemma-12
  (implies
   (and (l3-fs-p fs1)
        (equal (l2-wrchs hns (l3-to-l2-fs fs1 disk)
                         start text)
               (l3-to-l2-fs (mv-nth 0
                                    (l4-wrchs hns fs1 disk alv start text))
                            (mv-nth 1
                                    (l4-wrchs hns fs1 disk alv start text))))
        (l3-fs-p fs2)
        (boolean-listp alv)
        (disjoint-list-listp (l4-collect-all-index-lists fs1))
        (no-duplicates-listp (l4-collect-all-index-lists fs1))
        (indices-marked-listp (l4-collect-all-index-lists fs1)
                              alv)
        (indices-marked-listp (l4-collect-all-index-lists fs2)
                              alv)
        (stringp text)
        (integerp start)
        (<= 0 start)
        (symbol-listp hns)
        (block-listp disk)
        (equal (len alv) (len disk))
        (<= 0 (count-free-blocks alv))
        (not (member-intersectp-equal (l4-collect-all-index-lists fs1)
                                      (l4-collect-all-index-lists fs2))))
   (equal (l3-to-l2-fs fs2
                       (mv-nth 1
                               (l4-wrchs hns fs1 disk alv start text)))
          (l3-to-l2-fs fs2 disk)))
  :instructions
  ((:prove
    :hints
    (("subgoal *1/11.2''"
      :in-theory (disable l4-wrchs-correctness-1-lemma-9
                          find-n-free-blocks-correctness-7)
      :use
      ((:instance
        find-n-free-blocks-correctness-7
        (alv (set-indices-in-alv alv (cadr (assoc-equal (car hns) fs1))
                                 nil))
        (n
         (len
          (make-blocks
           (insert-text
            (unmake-blocks
             (fetch-blocks-by-indices disk (cadr (assoc-equal (car hns) fs1)))
             (cddr (assoc-equal (car hns) fs1)))
            start text)))))
       (:instance
        l4-wrchs-correctness-1-lemma-9 (fs fs2)
        (index-list
         (find-n-free-blocks
          (set-indices-in-alv alv (cadr (assoc-equal (car hns) fs1))
                              nil)
          (len
           (make-blocks
            (insert-text
             (unmake-blocks (fetch-blocks-by-indices
                             disk (cadr (assoc-equal (car hns) fs1)))
                            (cddr (assoc-equal (car hns) fs1)))
             start text)))))
        (value-list
         (make-blocks
          (insert-text
           (unmake-blocks
            (fetch-blocks-by-indices disk (cadr (assoc-equal (car hns) fs1)))
            (cddr (assoc-equal (car hns) fs1)))
           start text))))))
     ("subgoal *1/10.2''"
      :in-theory (disable l4-wrchs-correctness-1-lemma-9
                          find-n-free-blocks-correctness-7)
      :use
      ((:instance
        find-n-free-blocks-correctness-7
        (alv (set-indices-in-alv alv (cadr (assoc-equal (car hns) fs1))
                                 nil))
        (n
         (len
          (make-blocks
           (insert-text
            (unmake-blocks
             (fetch-blocks-by-indices disk (cadr (assoc-equal (car hns) fs1)))
             (cddr (assoc-equal (car hns) fs1)))
            start text)))))
       (:instance
        l4-wrchs-correctness-1-lemma-9 (fs fs2)
        (index-list
         (find-n-free-blocks
          (set-indices-in-alv alv (cadr (assoc-equal (car hns) fs1))
                              nil)
          (len
           (make-blocks
            (insert-text
             (unmake-blocks (fetch-blocks-by-indices
                             disk (cadr (assoc-equal (car hns) fs1)))
                            (cddr (assoc-equal (car hns) fs1)))
             start text)))))
        (value-list
         (make-blocks
          (insert-text
           (unmake-blocks
            (fetch-blocks-by-indices disk (cadr (assoc-equal (car hns) fs1)))
            (cddr (assoc-equal (car hns) fs1)))
           start text))))))
     ("subgoal *1/8.2''"
      :in-theory (disable l4-wrchs-correctness-1-lemma-9
                          find-n-free-blocks-correctness-7)
      :use
      ((:instance
        find-n-free-blocks-correctness-7
        (alv (set-indices-in-alv alv (cadr (assoc-equal (car hns) fs1))
                                 nil))
        (n
         (len
          (make-blocks
           (insert-text
            (unmake-blocks
             (fetch-blocks-by-indices disk (cadr (assoc-equal (car hns) fs1)))
             (cddr (assoc-equal (car hns) fs1)))
            start text)))))
       (:instance
        l4-wrchs-correctness-1-lemma-9 (fs fs2)
        (index-list
         (find-n-free-blocks
          (set-indices-in-alv alv (cadr (assoc-equal (car hns) fs1))
                              nil)
          (len
           (make-blocks
            (insert-text
             (unmake-blocks (fetch-blocks-by-indices
                             disk (cadr (assoc-equal (car hns) fs1)))
                            (cddr (assoc-equal (car hns) fs1)))
             start text)))))
        (value-list
         (make-blocks
          (insert-text
           (unmake-blocks
            (fetch-blocks-by-indices disk (cadr (assoc-equal (car hns) fs1)))
            (cddr (assoc-equal (car hns) fs1)))
           start text))))))
     ("subgoal *1/7.2''"
      :in-theory (disable l4-wrchs-correctness-1-lemma-9
                          find-n-free-blocks-correctness-7)
      :use
      ((:instance
        find-n-free-blocks-correctness-7
        (alv (set-indices-in-alv alv (cadr (assoc-equal (car hns) fs1))
                                 nil))
        (n
         (len
          (make-blocks
           (insert-text
            (unmake-blocks
             (fetch-blocks-by-indices disk (cadr (assoc-equal (car hns) fs1)))
             (cddr (assoc-equal (car hns) fs1)))
            start text)))))
       (:instance
        l4-wrchs-correctness-1-lemma-9 (fs fs2)
        (index-list
         (find-n-free-blocks
          (set-indices-in-alv alv (cadr (assoc-equal (car hns) fs1))
                              nil)
          (len
           (make-blocks
            (insert-text
             (unmake-blocks (fetch-blocks-by-indices
                             disk (cadr (assoc-equal (car hns) fs1)))
                            (cddr (assoc-equal (car hns) fs1)))
             start text)))))
        (value-list
         (make-blocks
          (insert-text
           (unmake-blocks
            (fetch-blocks-by-indices disk (cadr (assoc-equal (car hns) fs1)))
            (cddr (assoc-equal (car hns) fs1)))
           start text))))))
     ("subgoal *1/6.2''"
      :in-theory (disable l4-wrchs-correctness-1-lemma-9
                          find-n-free-blocks-correctness-7)
      :use
      ((:instance
        find-n-free-blocks-correctness-7
        (alv (set-indices-in-alv alv (cadr (assoc-equal (car hns) fs1))
                                 nil))
        (n
         (len
          (make-blocks
           (insert-text
            (unmake-blocks
             (fetch-blocks-by-indices disk (cadr (assoc-equal (car hns) fs1)))
             (cddr (assoc-equal (car hns) fs1)))
            start text)))))
       (:instance
        l4-wrchs-correctness-1-lemma-9 (fs fs2)
        (index-list
         (find-n-free-blocks
          (set-indices-in-alv alv (cadr (assoc-equal (car hns) fs1))
                              nil)
          (len
           (make-blocks
            (insert-text
             (unmake-blocks (fetch-blocks-by-indices
                             disk (cadr (assoc-equal (car hns) fs1)))
                            (cddr (assoc-equal (car hns) fs1)))
             start text)))))
        (value-list
         (make-blocks
          (insert-text
           (unmake-blocks
            (fetch-blocks-by-indices disk (cadr (assoc-equal (car hns) fs1)))
            (cddr (assoc-equal (car hns) fs1)))
           start text))))))
     ("subgoal *1/4.2''"
      :in-theory (disable l4-wrchs-correctness-1-lemma-9
                          find-n-free-blocks-correctness-7)
      :use
      ((:instance
        find-n-free-blocks-correctness-7
        (alv (set-indices-in-alv alv (cadr (assoc-equal (car hns) fs1))
                                 nil))
        (n
         (len
          (make-blocks
           (insert-text
            (unmake-blocks
             (fetch-blocks-by-indices disk (cadr (assoc-equal (car hns) fs1)))
             (cddr (assoc-equal (car hns) fs1)))
            start text)))))
       (:instance
        l4-wrchs-correctness-1-lemma-9 (fs fs2)
        (index-list
         (find-n-free-blocks
          (set-indices-in-alv alv (cadr (assoc-equal (car hns) fs1))
                              nil)
          (len
           (make-blocks
            (insert-text
             (unmake-blocks (fetch-blocks-by-indices
                             disk (cadr (assoc-equal (car hns) fs1)))
                            (cddr (assoc-equal (car hns) fs1)))
             start text)))))
        (value-list
         (make-blocks
          (insert-text
           (unmake-blocks
            (fetch-blocks-by-indices disk (cadr (assoc-equal (car hns) fs1)))
            (cddr (assoc-equal (car hns) fs1)))
           start text))))))))))

(defthm
  l4-wrchs-correctness-1-lemma-13
  (implies
   (and (bounded-nat-listp index-list (len v))
        (no-duplicatesp index-list)
        (block-listp value-list)
        (equal (len index-list)
               (len value-list)))
   (equal (fetch-blocks-by-indices (set-indices v index-list value-list)
                                   index-list)
          value-list)))

(defun count-free-blocks-alt (alv n)
  (declare (xargs :guard (and (natp n) (boolean-listp alv))))
  (if (zp n)
      0
    (+ (if (nth (- n 1) alv) 0 1)
       (count-free-blocks-alt alv (- n 1)))))

(defthm
  count-free-blocks-alt-correctness-1
  (implies (and (boolean-listp alv)
                (boolean-listp ac)
                (natp n)
                (<= n (len alv)))
           (equal (count-free-blocks-alt (revappend ac alv)
                                         (+ n (len ac)))
                  (count-free-blocks (first-n-ac n alv ac))))
  :hints (("goal" :induct (first-n-ac n alv ac))))

(defthm
  count-free-blocks-alt-correctness-2
  (implies (and (boolean-listp alv)
                (equal n (len alv)))
           (equal (count-free-blocks-alt alv n)
                  (count-free-blocks alv)))
  :hints (("goal" :in-theory (disable count-free-blocks-alt-correctness-1)
           :use (:instance count-free-blocks-alt-correctness-1
                           (ac nil)))))

(defthm
  l4-wrchs-correctness-1-lemma-14
  (implies (and (boolean-listp alv)
                (integerp n)
                (<= 0 n)
                (<= n (len alv)))
           (equal (count-free-blocks-alt (set-indices-in-alv alv nil nil)
                                         n)
                  (count-free-blocks-alt alv n))))

(defun count-before-n (l b)
      (declare (xargs :guard (and (natp b) (nat-listp l))))
      (if (atom l) 0 (+ (if (< (car l) b) 1 0) (count-before-n (cdr l) b))))

(defthm count-before-n-correctness-1
  (<= (count-before-n l b) (len l))
  :rule-classes (:linear))

(defthm count-before-n-correctness-2
  (implies (nat-listp l)
           (iff (equal (count-before-n l b) (len l))
                (bounded-nat-listp l b))))

(defthm count-before-n-correctness-3
  (implies (nat-listp l)
           (equal (count-before-n l 0) 0)))

(defthm l4-wrchs-correctness-1-lemma-15
  (implies (and (boolean-listp alv)
                (nat-listp index-list)
                (natp n)
                (< n (len alv))
                (not (equal n (car index-list))))
           (iff (nth n
                     (set-indices-in-alv alv index-list nil))
                (nth n
                     (set-indices-in-alv alv (cdr index-list)
                                         nil))))
  :instructions ((:casesplit (member-equal n (cdr index-list)))
                 :bash :bash))

(defthm
  l4-wrchs-correctness-1-lemma-16
  (implies
   (and (consp index-list)
        (boolean-listp alv)
        (natp n)
        (<= n (len alv))
        (nat-listp index-list)
        (indices-marked-p index-list alv)
        (no-duplicatesp-equal index-list))
   (equal
    (count-free-blocks-alt (set-indices-in-alv alv index-list nil)
                           n)
    (if (< (car index-list) n)
        (+ 1
           (count-free-blocks-alt (set-indices-in-alv alv (cdr index-list)
                                                      nil)
                                  n))
      (count-free-blocks-alt (set-indices-in-alv alv (cdr index-list)
                                                 nil)
                             n))))
  :hints
  (("goal" :induct (count-free-blocks-alt alv n))))

(defthm
  l4-wrchs-correctness-1-lemma-17
  (implies
   (and (boolean-listp alv)
        (natp n)
        (<= n (len alv))
        (nat-listp index-list)
        (indices-marked-p index-list alv)
        (no-duplicatesp-equal index-list))
   (equal (count-free-blocks-alt (set-indices-in-alv alv index-list nil)
                                 n)
          (+ (count-free-blocks-alt alv n)
             (count-before-n index-list n))))
  :hints (("goal" :induct (count-before-n index-list n))))

(defthm
  l4-wrchs-correctness-1-lemma-18
  (implies (and (boolean-listp alv)
                (indices-marked-p index-list alv)
                (no-duplicatesp-equal index-list)
                (bounded-nat-listp index-list (len alv)))
           (equal (count-free-blocks (set-indices-in-alv alv index-list nil))
                  (+ (count-free-blocks alv)
                     (len index-list))))
  :hints
  (("goal"
    :in-theory (disable count-free-blocks-alt-correctness-2
                        count-free-blocks
                        l4-wrchs-correctness-1-lemma-15
                        count-before-n-correctness-2)
    :use ((:instance count-free-blocks-alt-correctness-2
                     (n (len alv)))
          (:instance count-free-blocks-alt-correctness-2
                     (alv (set-indices-in-alv alv index-list nil))
                     (n (len (set-indices-in-alv alv index-list nil))))
          (:instance l4-wrchs-correctness-1-lemma-15
                     (n (len alv)))
          (:instance count-before-n-correctness-2
                     (l index-list)
                     (b (len alv)))))))

(encapsulate ()
  (local (include-book "std/lists/nthcdr" :dir :system))

  (local (defun nthcdr-*blocksize*-induction-2 (text1 text2)
           (cond ((or (atom text1) (atom text2))
                  (list text1 text2))
                 (t (nthcdr-*blocksize*-induction-2 (nthcdr *blocksize* text1)
                                                    (nthcdr *blocksize* text2))))))

  (defthm
    make-blocks-correctness-4
    (implies (equal (len text1) (len text2))
             (equal (len (make-blocks text1))
                    (len (make-blocks text2))))
    :hints (("goal" :induct (nthcdr-*blocksize*-induction-2 text1 text2)))))

(defthm
  len-of-make-unmake
  (implies (and (block-listp blocks)
                (natp n)
                (feasible-file-length-p (len blocks) n))
           (equal (len (make-blocks (unmake-blocks blocks n)))
                  (len blocks)))
  :hints
  (("goal" :in-theory (enable feasible-file-length-p))
   ("subgoal *1/8.1'"
    :expand (append (car blocks)
                    (unmake-blocks (cdr blocks) (+ -8 n))))
   ("subgoal *1/5.1'"
    :expand (append (car blocks)
                    (unmake-blocks (cdr blocks) (+ -8 n))))
   ("subgoal *1/2'4'" :expand (make-blocks (first-n-ac n (car blocks) nil)))
   ("subgoal *1/2.1'" :in-theory (disable len-of-first-n-ac)
    :use (:instance len-of-first-n-ac (i n)
                    (l (car blocks))
                    (ac nil)))
   ("subgoal *1/5.2'" :cases ((atom (cdr blocks))))
   ("subgoal *1/5.2'''" :expand (len (cdr blocks)))))

(defthm
  l4-wrchs-correctness-1-lemma-19
  (implies
   (and (boolean-listp alv)
        (stringp text)
        (integerp start)
        (<= 0 start)
        (block-listp disk)
        (equal (len alv) (len disk))
        (<= (len (make-blocks (insert-text nil start text)))
            (count-free-blocks alv))
        (l3-regular-file-entry-p entry)
        (indices-marked-p (car entry) alv)
        (no-duplicatesp-equal (car entry))
        (bounded-nat-listp (car entry)
                           (len alv)))
   (equal
    (len
     (find-n-free-blocks
      (set-indices-in-alv alv (car entry) nil)
      (len
       (make-blocks
        (insert-text (unmake-blocks (fetch-blocks-by-indices disk (car entry))
                                    (cdr entry))
                     start text)))))
    (len
     (make-blocks
      (insert-text (unmake-blocks (fetch-blocks-by-indices disk (car entry))
                                  (cdr entry))
                   start text)))))
  :instructions
  (:promote
   (:dive 1)
   (:rewrite find-n-free-blocks-correctness-2)
   :top :bash :s-prop (:dive 1 1)
   (:rewrite l4-wrchs-correctness-1-lemma-18)
   :top
   (:claim
    (<=
     (len
      (make-blocks
       (insert-text (unmake-blocks (fetch-blocks-by-indices disk (car entry))
                                   (cdr entry))
                    start text)))
     (+ (len (make-blocks (insert-text nil start text)))
        (len (car entry))))
    :hints :none)
   :bash :s-prop
   (:casesplit
    (>= (len (unmake-blocks (fetch-blocks-by-indices disk (car entry))
                            (cdr entry)))
        (+ start (len (coerce text 'list)))))
   (:dive 1 2)
   (:rewrite make-blocks-correctness-4
             ((text2 (unmake-blocks (fetch-blocks-by-indices disk (car entry))
                                    (cdr entry)))))
   (:dive 1)
   :top
   (:claim
    (equal
     (len
      (make-blocks (unmake-blocks (fetch-blocks-by-indices disk (car entry))
                                  (cdr entry))))
     (len (fetch-blocks-by-indices disk (car entry))))
    :hints :none)
   :bash (:change-goal nil t)
   (:dive 1)
   (:rewrite len-of-insert-text)
   :top :bash :bash (:dive 1 2)
   (:rewrite make-blocks-correctness-4
             ((text2 (insert-text nil start text))))
   :top :bash (:dive 1)
   (:rewrite len-of-insert-text)
   :nx (:rewrite len-of-insert-text)
   :top
   :bash :bash
   :bash :bash))

(defthm
  l4-wrchs-correctness-1-lemma-20
  (implies
   (and (consp hns)
        (l3-fs-p fs)
        (boolean-listp alv)
        (disjoint-list-listp (l4-collect-all-index-lists fs))
        (no-duplicates-listp (l4-collect-all-index-lists fs))
        (indices-marked-listp (l4-collect-all-index-lists fs)
                              alv)
        (stringp text)
        (integerp start)
        (<= 0 start)
        (block-listp disk)
        (equal (len alv) (len disk))
        (<= (len (make-blocks (insert-text nil start text)))
            (count-free-blocks alv))
        (consp fs)
        (consp (assoc-equal (car hns) fs))
        (not (cdr hns))
        (l3-regular-file-entry-p (cdr (assoc-equal (car hns) fs))))
   (l3-regular-file-entry-p
    (cons
     (find-n-free-blocks
      (set-indices-in-alv alv (cadr (assoc-equal (car hns) fs))
                          nil)
      (len
       (make-blocks
        (insert-text
         (unmake-blocks
          (fetch-blocks-by-indices disk (cadr (assoc-equal (car hns) fs)))
          (cddr (assoc-equal (car hns) fs)))
         start text))))
     (len
      (insert-text
       (unmake-blocks
        (fetch-blocks-by-indices disk (cadr (assoc-equal (car hns) fs)))
        (cddr (assoc-equal (car hns) fs)))
       start text)))))
  :hints
  (("goal"
    :expand
    (l3-regular-file-entry-p
     (cons
      (find-n-free-blocks
       (set-indices-in-alv alv (cadr (assoc-equal (car hns) fs))
                           nil)
       (len
        (make-blocks
         (insert-text
          (unmake-blocks
           (fetch-blocks-by-indices disk (cadr (assoc-equal (car hns) fs)))
           (cddr (assoc-equal (car hns) fs)))
          start text))))
      (len
       (insert-text
        (unmake-blocks
         (fetch-blocks-by-indices disk (cadr (assoc-equal (car hns) fs)))
         (cddr (assoc-equal (car hns) fs)))
        start text)))))))

;; This theorem shows the equivalence of the l4 and l2 versions of wrchs.
(defthm
  l4-wrchs-correctness-1
  (implies (and (l4-stricter-fs-p fs alv)
                (stringp text)
                (natp start)
                (symbol-listp hns)
                (block-listp disk)
                (equal (len alv) (len disk))
                (<= (len (make-blocks (insert-text nil start text)))
                    (count-free-blocks alv)))
           (equal (l2-wrchs hns (l4-to-l2-fs fs disk)
                            start text)
                  (mv-let (new-fs new-disk new-alv)
                    (l4-wrchs hns fs disk alv start text)
                    (declare (ignore new-alv))
                    (l4-to-l2-fs new-fs new-disk))))
  :hints
  (("subgoal *1/7.4.4"
    :in-theory (disable find-n-free-blocks-correctness-7)
    :use
    (:instance
     find-n-free-blocks-correctness-7
     (alv (set-indices-in-alv alv (cadr (assoc-equal (car hns) fs))
                              nil))
     (n
      (len
       (make-blocks
        (insert-text
         (unmake-blocks
          (fetch-blocks-by-indices disk (cadr (assoc-equal (car hns) fs)))
          (cddr (assoc-equal (car hns) fs)))
         start text))))))
   ("subgoal *1/7.4" :in-theory (enable l3-regular-file-entry-p))))

(defthm
  l4-read-after-write-1
  (implies (and (l4-stricter-fs-p fs alv)
                (stringp text)
                (natp start)
                (symbol-listp hns)
                (block-listp disk)
                (equal (len alv) (len disk))
                (<= (len (make-blocks (insert-text nil start text)))
                    (count-free-blocks alv))
                (equal n (length text))
                (stringp (l4-stat hns fs disk)))
           (mv-let (new-fs new-disk new-alv)
             (l4-wrchs HNS FS DISK ALV START TEXT)
             (declare (ignore new-alv))
             (equal (l4-rdchs hns new-fs new-disk start n)
                    text))))

(defthm l4-wrchs-returns-disk-lemma-1
  (implies (and (equal (len index-list)
                       (len value-list))
                (block-listp disk)
                (block-listp value-list)
                (bounded-nat-listp index-list (len disk)))
           (block-listp (set-indices disk index-list value-list))))

(defthm
  l4-wrchs-returns-disk-lemma-2
  (implies
   (and (consp (assoc-equal name fs))
        (not (l3-regular-file-entry-p (cdr (assoc-equal name fs))))
        (l3-fs-p fs)
        (boolean-listp alv)
        (bounded-nat-listp (l4-list-all-indices fs)
                           (len alv)))
   (bounded-nat-listp (l4-list-all-indices (cdr (assoc-equal name fs)))
                      (len alv)))
  :hints (("goal" :in-theory (enable l4-list-all-indices)
           :induct (l4-list-all-indices fs))))

(defthm l4-wrchs-returns-disk
  (implies (and (symbol-listp hns)
                (l3-fs-p fs)
                (boolean-listp alv)
                (integerp start)
                (<= 0 start)
                (stringp text)
                (block-listp disk)
                (equal (len disk) (len alv))
                (bounded-nat-listp (l4-list-all-indices fs) (len disk)))
           (block-listp (mv-nth 1 (l4-wrchs hns fs disk alv start text)))))

(defthm
  l4-read-after-write-2
  (implies (and (l4-stricter-fs-p fs alv)
                (stringp text1)
                (stringp text2)
                (natp start1)
                (natp start2)
                (symbol-listp hns1)
                (symbol-listp hns2)
                (not (equal hns1 hns2))
                (natp n1)
                (natp n2)
                (block-listp disk)
                (boolean-listp alv)
                (equal (len alv) (len disk))
                (<= (len (make-blocks (insert-text nil start2 text2)))
                    (count-free-blocks alv))
                (stringp (l4-stat hns1 fs disk)))
           (mv-let (new-fs new-disk new-alv)
             (l4-wrchs hns2 fs disk alv start2 text2)
             (declare (ignore new-alv))
             (equal (l4-rdchs hns1 new-fs new-disk start1 n1)
                    (l4-rdchs hns1 fs disk start1 n1))))
  :hints
  (("goal"
    :in-theory (disable l4-rdchs-correctness-1
                        l4-wrchs-correctness-1
                        l4-wrchs-returns-fs)
    :use
    ((:instance l4-rdchs-correctness-1 (hns hns1)
                (start start1)
                (n n1))
     (:instance l4-rdchs-correctness-1 (hns hns1)
                (start start1)
                (n n1)
                (fs (mv-nth 0
                            (l4-wrchs hns2 fs disk alv start2 text2)))
                (disk (mv-nth 1
                              (l4-wrchs hns2 fs disk alv start2 text2))))
     (:instance l4-wrchs-correctness-1 (hns hns2)
                (start start2)
                (text text2))
     (:instance l4-wrchs-returns-fs (hns hns2)
                (start start2)
                (text text2))))))

