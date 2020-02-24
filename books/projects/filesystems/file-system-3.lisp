(in-package "ACL2")

;  file-system-3.lisp                                  Mihir Mehta

; Here we define a more complex file system with length tracking and a disk.
; We first start with a file-system recognizer, and then we define various
; file-system operations.

(include-book "std/testing/assert" :dir :system)
(include-book "bounded-nat-listp")
(include-book "block-listp")
(include-book "generate-index-list")
(include-book "file-system-2")

;; This function serves to get the specified blocks from a disk. If the block
;; is not found (most likely because of an invalid index) we return a null block
;; as noted above.
(defun
  fetch-blocks-by-indices
  (block-list index-list)
  (declare (xargs :guard (and (block-listp block-list)
                              (nat-listp index-list))))
  (if
   (atom index-list)
   nil
   (let
    ((tail
      (fetch-blocks-by-indices block-list (cdr index-list))))
    (if (>= (car index-list) (len block-list))
        (cons *nullblock* tail)
        (cons (nth (car index-list) block-list)
              tail)))))

;; Prove that a proper block-list is returned.
(defthm fetch-blocks-by-indices-correctness-1
  (implies (and (block-listp block-list) (nat-listp index-list))
           (block-listp (fetch-blocks-by-indices block-list index-list))))

;; Prove that a list of the appropriate length is returned.
(defthm fetch-blocks-by-indices-correctness-2
  (implies (and (block-listp block-list) (nat-listp index-list))
           (equal (len (fetch-blocks-by-indices block-list index-list))
                  (len index-list))))

(defthm
  fetch-blocks-by-indices-correctness-3
  (implies
   (and (block-listp block-list)
        (bounded-nat-listp index-list (len block-list)))
   (equal (fetch-blocks-by-indices (binary-append block-list extra-blocks)
                                   index-list)
          (fetch-blocks-by-indices block-list index-list))))

;; This function, which is kept disabled, recognises a regular file entry. I am
;; deciding not to make things overly complicated by making getter and setter
;; functions for file entries.
(defund l3-regular-file-entry-p (entry)
  (declare (xargs :guard t))
  (and (consp entry)
       (nat-listp (car entry))
       (natp (cdr entry))
       (feasible-file-length-p (len (car entry)) (cdr entry))))

(defthm l3-regular-file-entry-p-correctness-1
  (implies (l3-regular-file-entry-p entry)
           (and (true-listp (car entry))
                (nat-listp (car entry))
                (natp (cdr entry))
                (feasible-file-length-p (len (car entry)) (cdr entry))))
  :hints (("Goal" :in-theory (enable l3-regular-file-entry-p)) ))

(defthm l3-regular-file-entry-p-correctness-2
  (implies (l3-regular-file-entry-p entry)
           (consp entry))
  :hints (("Goal" :use l3-regular-file-entry-p-correctness-1) )
  :rule-classes (:forward-chaining))

; This function defines a valid filesystem. It's an alist where all the cars
; are symbols and all the cdrs are either further filesystems or regular files,
; separated into text (represented by a nat-list of indices which we use to
; look up an external disk) and metadata (currently, only length).
(defun l3-fs-p (fs)
  (declare (xargs :guard t))
  (if (atom fs)
      (null fs)
    (and (let ((directory-or-file-entry (car fs)))
           (if (atom directory-or-file-entry)
               nil
             (let ((name (car directory-or-file-entry))
                   (entry (cdr directory-or-file-entry)))
               (and (symbolp name)
                    (or (l3-regular-file-entry-p entry)
                        (l3-fs-p entry))))))
         (l3-fs-p (cdr fs)))))

(defthm l3-regular-file-entry-p-correctness-3
  (implies (l3-regular-file-entry-p entry)
           (not (l3-fs-p entry)))
  :hints (("Goal" :in-theory (enable l3-regular-file-entry-p)) )
  :rule-classes (:rewrite (:rewrite :corollary
                                    (implies (l3-fs-p entry)
                                             (not (l3-regular-file-entry-p entry))))))

(defthm alistp-l3-fs-p
  (implies (l3-fs-p fs)
           (alistp fs)))

(defthm l3-fs-p-assoc
  (implies (and (l3-fs-p fs)
                (consp (assoc-equal name fs))
                (not (l3-regular-file-entry-p (cdr (assoc-equal name fs)))))
           (l3-fs-p (cdr (assoc-equal name fs)))))

(assert!
 (l3-fs-p '((a (1 2) . 10) (b (3 4) . 11) (c (a (5 6) . 12) (b (7 8) . 13)))))

; This function is a further restricted filesystem. This is not used as our
; only filesystem definition because it has a dependence on the disk, which we
; want to keep separate, at least at this stage.
(defund l3-bounded-fs-p (fs disk-length)
  (declare (xargs :guard (natp disk-length)))
  (if (atom fs)
      (null fs)
    (and (let ((directory-or-file-entry (car fs)))
           (if (atom directory-or-file-entry)
               nil
             (let ((name (car directory-or-file-entry))
                   (entry (cdr directory-or-file-entry)))
               (and (symbolp name)
                    (or (and (consp entry)
                             (bounded-nat-listp (car entry) disk-length)
                             (natp (cdr entry))
                             (feasible-file-length-p (len (car entry)) (cdr entry)))
                        (l3-bounded-fs-p entry disk-length))))))
         (l3-bounded-fs-p (cdr fs) disk-length))))

(defthm l3-bounded-fs-p-correctness-1
  (implies (l3-bounded-fs-p fs disk-length)
           (l3-fs-p fs))
  :hints (("Goal" :in-theory (enable l3-bounded-fs-p l3-regular-file-entry-p)) )
  :rule-classes (:forward-chaining))

(defthm l3-bounded-fs-p-correctness-2
  (implies (l3-regular-file-entry-p entry)
           (not (l3-bounded-fs-p entry disk-length)))
  :hints (("Goal" :in-theory (disable l3-regular-file-entry-p-correctness-3)
           :use l3-regular-file-entry-p-correctness-3)))

(defthm l3-bounded-fs-p-assoc
  (implies (and (l3-bounded-fs-p fs disk-length)
                (consp (assoc-equal name fs))
                (not (l3-regular-file-entry-p (cdr (assoc-equal name fs)))))
           (l3-bounded-fs-p (cdr (assoc-equal name fs)) disk-length))
  :hints (("Goal" :in-theory (enable l3-bounded-fs-p l3-regular-file-entry-p)) ))

(defthm l3-to-l2-fs-guard-lemma-1
  (implies (and (feasible-file-length-p (len blocks) n)
                (block-listp blocks))
           (character-listp (unmake-blocks blocks n)))
  :hints (("Goal" :in-theory (enable feasible-file-length-p)) ))

;; This function transforms an instance of l3 into an equivalent instance of l2.
(defun l3-to-l2-fs (fs disk)
  (declare (xargs :guard (and (l3-fs-p fs) (block-listp disk))
                  :guard-hints (("Subgoal 2.6" :in-theory (enable feasible-file-length-p)))
                  ))
  (if (atom fs)
      nil
    (cons (let* ((directory-or-file-entry (car fs))
                 (name (car directory-or-file-entry))
                 (entry (cdr directory-or-file-entry)))
            (cons name
                  (if (l3-regular-file-entry-p entry)
                      (cons (coerce (unmake-blocks
                                     (fetch-blocks-by-indices disk (car entry))
                                     (cdr entry)) 'string)
                            (cdr entry))
                    (l3-to-l2-fs entry disk))))
          (l3-to-l2-fs (cdr fs) disk))))

;; This theorem shows the type-correctness of l3-to-l2-fs.
(defthm l3-to-l2-fs-correctness-1
  (implies (and (l3-fs-p fs) (block-listp disk))
           (l2-fs-p (l3-to-l2-fs fs disk))))

;; This function allows a file or directory to be found in a filesystem given a path.
(defun l3-stat (hns fs disk)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l3-fs-p fs)
                              (block-listp disk))))
  (if (atom hns)
      fs
    (if (atom fs)
        nil
      (let ((sd (assoc (car hns) fs)))
        (if (atom sd)
            nil
          (let ((contents (cdr sd)))
            (if (l3-regular-file-entry-p contents)
                (and (null (cdr hns))
                     (coerce
                      (unmake-blocks (fetch-blocks-by-indices disk (car contents))
                                     (cdr contents))
                      'string))
              (l3-stat (cdr hns) contents disk))))))))

(defthm
  l3-stat-correctness-1-lemma-1
  (implies (and (l3-fs-p fs)
                (l3-regular-file-entry-p (cdr (assoc-equal name fs)))
                (block-listp disk)
                (consp (assoc-equal name fs)))
           (stringp (cadr (assoc-equal name
                                       (l3-to-l2-fs fs disk))))))

(defthm l3-stat-correctness-1-lemma-2
  (implies (and (l3-fs-p fs) (block-listp disk))
           (equal (consp (assoc-equal name (l3-to-l2-fs fs disk)))
                  (consp (assoc-equal name fs)))))

(defthm
  l3-stat-correctness-1-lemma-3
  (implies
   (and (l3-fs-p fs)
        (block-listp disk)
        (consp (assoc-equal name fs))
        (l3-regular-file-entry-p (cdr (assoc-equal name fs))))
   (equal
    (cadr (assoc-equal name (l3-to-l2-fs fs disk)))
    (coerce (unmake-blocks
             (fetch-blocks-by-indices disk (cadr (assoc-equal name fs)))
             (cddr (assoc-equal name fs)))
            'string))))

(defthm l3-stat-correctness-1-lemma-4
  (implies (and (l3-fs-p fs)
                (block-listp disk)
                (l3-fs-p (cdr (assoc-equal name fs))))
           (equal (cdr (assoc-equal name (l3-to-l2-fs fs disk)))
                  (l3-to-l2-fs (cdr (assoc-equal name fs))
                               disk))))

(defthm
  l3-stat-correctness-1-lemma-5
  (implies (and (consp (assoc-equal name fs))
                (l3-fs-p fs)
                (block-listp disk)
                (not (l3-regular-file-entry-p (cdr (assoc-equal name fs)))))
           (not (stringp (car (l3-to-l2-fs (cdr (assoc-equal name fs))
                                           disk))))))

;; This is the first of two theorems showing the equivalence of the l3 and l2
;; versions of stat.
(defthm l3-stat-correctness-1
  (implies (and (symbol-listp hns)
                (l3-fs-p fs)
                (block-listp disk)
                (stringp (l3-stat hns fs disk)))
           (equal (l2-stat hns (l3-to-l2-fs fs disk))
                  (l3-stat hns fs disk))))

(defthm l3-stat-correctness-2-lemma-1
  (implies (l3-fs-p fs)
           (equal (consp (l3-to-l2-fs fs disk))
                  (consp fs))))

(defthm l3-stat-correctness-2-lemma-2
  (implies (and (consp (assoc-equal name fs))
                (l3-fs-p fs)
                (block-listp disk)
                (stringp (cadr (assoc-equal name fs)))
                (cdr hns))
           (l3-regular-file-entry-p (cdr (assoc-equal name fs)))))

;; This is the second of two theorems showing the equivalence of the l3 and l2
;; versions of stat.
(defthm l3-stat-correctness-2
  (implies (and (symbol-listp hns)
                (l3-fs-p fs)
                (block-listp disk)
                (l3-fs-p (l3-stat hns fs disk)))
           (equal (l2-stat hns (l3-to-l2-fs fs disk))
                  (l3-to-l2-fs (l3-stat hns fs disk) disk)))
  )

;; This is simply a useful property of stat.
(defthm l3-stat-of-stat
  (implies (and (symbol-listp inside)
                (symbol-listp outside)
                (l3-stat outside fs disk)
                (l3-fs-p fs)
                (block-listp disk))
           (equal (l3-stat inside (l3-stat outside fs disk) disk)
                  (l3-stat (append outside inside) fs disk)))
  :hints
  (("Goal" :induct (l3-stat outside fs disk))))

;; This function finds a text file given its path and reads a segment of
;; that text file.
(defun l3-rdchs (hns fs disk start n)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l3-fs-p fs)
                              (natp start)
                              (natp n)
                              (block-listp disk))))
  (let ((file (l3-stat hns fs disk)))
    (if (not (stringp file))
        nil
      (let ((file-length (length file))
            (end (+ start n)))
        (if (< file-length end)
            nil
          (subseq file start (+ start n)))))))

(defthm l3-rdchs-correctness-1-lemma-1
  (implies (and (symbol-listp hns)
                (l3-fs-p fs)
                (block-listp disk))
           (equal (stringp (l2-stat hns (l3-to-l2-fs fs disk)))
                  (stringp (l3-stat hns fs disk)))))

;; This theorem proves the equivalence of the l3 and l2 versions of rdchs.
(defthm l3-rdchs-correctness-1
  (implies (and (symbol-listp hns)
                (l3-fs-p fs)
                (natp start)
                (natp n)
                (block-listp disk))
           (equal (l2-rdchs hns (l3-to-l2-fs fs disk) start n)
                  (l3-rdchs hns fs disk start n))))

; This function deletes a file or directory given its path.

; Note that we don't need to do anything with the disk - the blocks can just
; lie there, forever unreferred to. In model 4, we start re-using the blocks.
(defun l3-unlink (hns fs)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l3-fs-p fs))))
  (if (atom hns)
      fs ;;error case, basically
    (if (atom (cdr hns))
        (remove1-assoc (car hns) fs)
      (if (atom fs)
          nil
        (let ((sd (assoc (car hns) fs)))
          (if (atom sd)
              fs
            (let ((contents (cdr sd)))
              (if (l3-regular-file-entry-p contents)
                  fs ;; we still have names but we're at a regular file - error
                (cons (cons (car sd)
                            (l3-unlink (cdr hns) contents))
                      (remove1-assoc (car hns) fs))))))))
    ))

(defthmd l3-unlink-returns-fs-lemma-1
  (implies (and (consp (assoc-equal s fs))
                (l3-fs-p fs))
           (and (equal (car (assoc-equal s fs)) s) (symbolp s))))

;; This theorem shows that the property l3-fs-p is preserved by unlink.
(defthm l3-unlink-returns-fs
  (implies (and (l3-fs-p fs))
           (l3-fs-p (l3-unlink hns fs)))
  :hints (("Goal" :in-theory (enable l3-unlink-returns-fs-lemma-1)) ))

(defthm l3-unlink-correctness-1-lemma-1
  (implies (and (l3-fs-p fs) (block-listp disk))
           (equal (remove1-assoc-equal name (l3-to-l2-fs fs disk))
                  (l3-to-l2-fs (remove1-assoc-equal name fs)
                               disk))))

(defthm
  l3-unlink-correctness-1-lemma-2
  (implies
   (and (consp (cdr hns))
        (consp fs)
        (l3-fs-p fs)
        (block-listp disk))
   (implies
    (not (l3-regular-file-entry-p (cdr (assoc-equal name fs))))
    (not (l3-regular-file-entry-p (l3-unlink (cdr hns)
                                             (cdr (assoc-equal name fs))))))))

;; This theorem shows the equivalence of the l3 and l2 versions of unlink.
(defthm l3-unlink-correctness-1
  (implies (and (symbol-listp hns)
                (l3-fs-p fs)
                (block-listp disk))
           (equal (l2-unlink hns (l3-to-l2-fs fs disk))
                  (l3-to-l2-fs (l3-unlink hns fs) disk))))

;; putting these lemmas on the back burner because we would need to add uniquep
;; to our l3-fs-p definition to make this work
;; (defthm l3-unlink-works-lemma-1 (not (assoc-equal key (remove1-assoc-equal key alist))))

;; (defthm l3-unlink-works (implies (l3-fs-p fs) (not (l3-stat hns (l3-unlink hns fs)))))

(encapsulate
  ()

  (local (defun induction-scheme (x y)
           (if (atom y)
               x
             (induction-scheme (binary-append x (cons (car y) nil)) (cdr y)))))

  (defthm
    generate-index-list-correctness-3
    (implies
     (and (block-listp disk)
          (block-listp newblocks))
     (equal (fetch-blocks-by-indices (binary-append disk newblocks)
                                     (generate-index-list (len disk)
                                                          (len newblocks)))
            newblocks))
     :hints (("Goal" :induct (induction-scheme disk newblocks)))))

; This function writes a specified text string to a specified position to a
; text file at a specified path.
(defun l3-wrchs (hns fs disk start text)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l3-fs-p fs)
                              (natp start)
                              (stringp text)
                              (block-listp disk))))
  (if (atom hns)
      (mv fs disk) ;; error - showed up at fs with no name  - so leave fs unchanged
    (if (atom fs)
        (mv nil disk) ;; error, so leave fs unchanged
      (let ((sd (assoc (car hns) fs)))
        (if (atom sd)
            (mv fs disk) ;; file-not-found error, so leave fs unchanged
          (let ((contents (cdr sd)))
            (if (l3-regular-file-entry-p contents)
                (if (cdr hns)
                    (mv (cons (cons (car sd) contents)
                              (remove1-assoc (car hns) fs))
                        disk) ;; error, so leave fs unchanged
                  (let* ((oldtext
                          (unmake-blocks
                           (fetch-blocks-by-indices disk (car contents))
                           (cdr contents)))
                         (newtext (insert-text oldtext start text))
                         (newblocks (make-blocks newtext)))
                    (mv (cons (cons (car sd)
                                    (cons (generate-index-list
                                           (len disk)
                                           (len newblocks))
                                          (len newtext)))
                              (remove1-assoc (car hns) fs))
                        (binary-append disk newblocks))))
              (mv-let (new-contents new-disk) (l3-wrchs (cdr hns) contents disk start text)
                (mv (cons (cons (car sd) new-contents)
                          (remove1-assoc (car hns) fs))
                    new-disk)))
            ))))))

(defthm l3-wrchs-returns-fs-lemma-1
  (implies (l3-fs-p fs)
           (l3-fs-p (remove1-assoc-equal s fs))))

(defthmd l3-wrchs-returns-fs-lemma-2
  (implies (and (consp (assoc-equal s fs))
                (l3-fs-p fs)
                (consp (cdr (assoc-equal s fs)))
                (l3-regular-file-entry-p (cdr (assoc-equal s fs))))
           (feasible-file-length-p
            (len (cadr (assoc-equal s fs)))
            (cddr (assoc-equal s fs))))
  :hints ( ("Goal" :induct (assoc-equal s fs))))

(defthm
  l3-wrchs-returns-fs-lemma-3
  (implies
   (and (block-listp disk)
        (character-listp cl))
   (l3-regular-file-entry-p (cons (generate-index-list (len disk)
                                                       (len (make-blocks cl)))
                                  (len cl))))
  :hints (("Goal" :in-theory (enable l3-regular-file-entry-p))))

;; This theorem shows that the property l3-fs-p is preserved by wrchs, and
;; additionally the property block-listp is preseved for the disk.
(defthm l3-wrchs-returns-fs
  (implies (and (l3-fs-p fs)
                (block-listp disk)
                (integerp start)
                (<= 0 start)
                (stringp text))
           (mv-let (new-fs new-disk)
             (l3-wrchs hns fs disk start text)
             (and (l3-fs-p new-fs) (block-listp new-disk))))
  :hints (("Goal" :in-theory (enable l3-unlink-returns-fs-lemma-1)) ))

(defthm
  l3-wrchs-correctness-1-lemma-1
  (implies (and (l3-fs-p fs)
                (consp (assoc-equal name fs))
                (not (l3-regular-file-entry-p (cdr (assoc-equal name fs)))))
           (not (l3-regular-file-entry-p (cddr (assoc-equal name fs))))))

(defthm l3-wrchs-correctness-1-lemma-2
  (implies (and (consp fs)
                (l3-fs-p fs)
                (block-listp disk))
           (consp (car (l3-to-l2-fs fs disk)))))

(defthm l3-wrchs-correctness-1-lemma-3
        (implies (and (l3-bounded-fs-p fs (len disk))
                      (block-listp disk)
                      (l3-regular-file-entry-p (cdr (car fs))))
                 (bounded-nat-listp (cadr (car fs))
                                    (len disk)))
        :hints (("Goal" :in-theory (enable l3-bounded-fs-p))))

(defthm l3-wrchs-correctness-1-lemma-4
  (implies (and (l3-bounded-fs-p fs (len disk))
                (block-listp disk))
           (equal (l3-to-l2-fs fs (binary-append disk extra-blocks))
                  (l3-to-l2-fs fs disk)))
  :hints (("Goal" :in-theory (enable l3-bounded-fs-p l3-regular-file-entry-p))))

(defthm
  l3-wrchs-correctness-1-lemma-5
  (implies
   (and (consp (assoc-equal name fs))
        (l3-fs-p (cdr (assoc-equal name fs)))
        (l3-fs-p fs)
        (block-listp disk))
   (equal (cdr (assoc-equal name
                            (l3-to-l2-fs fs (append disk extra-blocks))))
          (l3-to-l2-fs (cdr (assoc-equal name fs))
                       (append disk extra-blocks)))))

(defthm l3-wrchs-correctness-1-lemma-6
  (implies (l3-bounded-fs-p fs disk-length)
           (l3-bounded-fs-p (remove1-assoc-equal name fs)
                            disk-length))
  :hints (("Goal" :in-theory (enable l3-bounded-fs-p))))

(defthm
  l3-wrchs-correctness-1-lemma-7
  (implies (and (l3-regular-file-entry-p (cdr (assoc-equal (car hns) fs)))
                (l3-fs-p fs)
                (block-listp disk))
           (consp (cdr (assoc-equal (car hns)
                                    (l3-to-l2-fs fs disk))))))

(defthm
  l3-wrchs-correctness-1-lemma-8
  (implies
   (and (consp (assoc-equal name fs))
        (l3-regular-file-entry-p (cdr (assoc-equal name fs)))
        (l3-fs-p fs)
        (block-listp disk))
   (equal
    (cdr (assoc-equal name (l3-to-l2-fs fs disk)))
    (cons
     (coerce (unmake-blocks
              (fetch-blocks-by-indices disk (cadr (assoc-equal name fs)))
              (cddr (assoc-equal name fs)))
             'string)
     (cddr (assoc-equal name fs))))))

(defthm
  l3-wrchs-correctness-1-lemma-9
  (implies
   (and (l3-bounded-fs-p fs1 (len disk))
        (block-listp disk))
   (equal (l3-to-l2-fs fs1
                       (mv-nth 1 (l3-wrchs hns fs2 disk start text)))
          (l3-to-l2-fs fs1 disk))))

;; This theorem shows the equivalence of the l3 and l2 versions of wrchs.
(defthm
  l3-wrchs-correctness-1
  (implies (and (l3-bounded-fs-p fs (len disk))
                (stringp text)
                (natp start)
                (symbol-listp hns)
                (block-listp disk))
           (equal (l2-wrchs hns (l3-to-l2-fs fs disk)
                            start text)
                  (mv-let (new-fs new-disk)
                    (l3-wrchs hns fs disk start text)
                    (l3-to-l2-fs new-fs new-disk))))
  :hints (("subgoal *1/8'''"
           :in-theory (disable l3-wrchs-returns-fs)
           :use (:instance l3-wrchs-returns-fs (hns (cdr hns))
                           (fs (cdr (assoc-equal (car hns) fs)))))))

;; This function creates a text file (and all necessary subdirectories) given a
;; path and some initial text.
(defun l3-create (hns fs disk text)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l3-fs-p fs)
                              (stringp text)
                              (block-listp disk))))
  (if (atom hns)
      (mv fs disk) ;; error - showed up at fs with no name  - so leave fs unchanged
    (let ((sd (assoc (car hns) fs)))
      (if (atom sd)
          (if (atom (cdr hns))
              (let ((blocks (make-blocks (coerce text 'list))))
                (mv (cons (cons (car hns)
                                (cons (generate-index-list
                                       (len disk)
                                       (len blocks))
                                      (length text)))
                          fs)
                    (binary-append disk blocks)))
            (mv-let (new-fs new-disk) (l3-create (cdr hns) nil disk text)
              (mv (cons (cons (car hns) new-fs) fs) new-disk)))
        (let ((contents (cdr sd)))
          (if (l3-regular-file-entry-p contents)
              (mv (cons (cons (car sd) contents) ;; file already exists, so leave fs unchanged
                        (remove1-assoc (car hns) fs))
                  disk)
            (mv-let (new-fs new-disk) (l3-create (cdr hns) contents disk text)
              (mv (cons (cons (car sd)
                              new-fs)
                        (remove1-assoc (car hns) fs))
                  new-disk)))
          )))))

;; This theorem shows that the property l3-fs-p is preserved by create, and
;; additionally the property block-listp is preseved for the disk.
(defthm l3-create-returns-fs
  (implies (and (l3-fs-p fs)
                (block-listp disk)
                (stringp text)
                (symbol-listp hns))
           (mv-let (new-fs new-disk)
             (l3-create hns fs disk text)
             (and (l3-fs-p new-fs) (block-listp new-disk)))))

(defthm l3-create-correctness-1-lemma-1
  (equal (mv-nth 1
                 (l3-create hns fs (binary-append disk1 disk2)
                            text))
         (binary-append disk1
                        (mv-nth 1 (l3-create hns fs disk2 text)))))

(defthm l3-create-correctness-1-lemma-2
  (implies (and (l3-bounded-fs-p fs1 (len disk))
                (l3-fs-p fs2)
                (block-listp disk)
                (stringp text)
                (symbol-listp hns))
           (equal (l3-to-l2-fs fs1
                               (mv-nth 1
                                       (l3-create hns fs2 disk text)))
                  (l3-to-l2-fs fs1
                               disk))))

;; This theorem shows the equivalence of the l3 and l2 versions of create.
(defthm l3-create-correctness-1
    (implies (and (l3-bounded-fs-p fs (len disk))
                (stringp text)
                (symbol-listp hns)
                (block-listp disk))
           (equal (l2-create hns (l3-to-l2-fs fs disk) text)
                  (mv-let (new-fs new-disk) (l3-create hns fs disk text)
                    (l3-to-l2-fs new-fs new-disk))))
    :hints (("Subgoal *1/9'''"
             :use (:instance l3-create-returns-fs (hns (cdr hns))
                             (fs (cdr (assoc-equal (car hns) fs)))))
            ("Subgoal *1/5.2'"
             :use (:instance l3-create-returns-fs (hns (cdr hns))
                             (fs nil)))
            ("Subgoal *1/3.2'"
             :use (:instance l3-create-returns-fs (hns (cdr hns))
                             (fs nil)))
            ("Subgoal *1/3.1'" :in-theory (enable l3-bounded-fs-p))))

(defthm l3-read-after-write-1-lemma-1
  (implies (and (l3-fs-p fs) (stringp text) (block-listp disk) (integerp start)
  (<= 0 start))
           (equal (stringp (l3-stat hns (mv-nth 0 (l3-wrchs hns fs disk start text))
                                    (mv-nth 1 (l3-wrchs hns fs disk start text))))
                  (stringp (l3-stat hns fs disk))))
  :hints (("Subgoal *1/7.2'"
           :in-theory (disable l3-wrchs-returns-fs)
           :use (:instance l3-wrchs-returns-fs (hns (cdr hns))
                           (fs (cdr (assoc-equal (car hns) fs))))) ))

(defthm l3-read-after-write-1-lemma-2
  (implies (and (l3-fs-p fs)
                (block-listp disk)
                (not (stringp (l3-stat hns fs disk))))
           (l3-fs-p (l3-stat hns fs disk))))

(defthm
  l3-read-after-write-1-lemma-3
  (implies
   (and (l3-bounded-fs-p fs (len disk))
        (block-listp disk)
        (symbol-listp hns1)
        (symbol-listp hns2)
        (stringp text2)
        (natp start2))
   (mv-let (new-fs new-disk)
     (l3-wrchs hns2 fs disk start2 text2)
     (equal (stringp (l3-stat hns1 new-fs new-disk))
            (stringp (l3-stat hns1 fs disk)))))
  :hints
  (("goal"
    :in-theory (disable l2-read-after-write-2-lemma-4
                        l3-stat-correctness-1
                        l3-stat-correctness-2
                        l3-wrchs-returns-fs)
    :use
    ((:instance l2-read-after-write-2-lemma-4
                (fs (l3-to-l2-fs fs disk)))
     (:instance
      l3-stat-correctness-1 (hns hns1)
      (fs (mv-nth 0 (l3-wrchs hns2 fs disk start2 text2)))
      (disk (mv-nth 1
                    (l3-wrchs hns2 fs disk start2 text2))))
     (:instance
      l3-stat-correctness-2 (hns hns1)
      (fs (mv-nth 0 (l3-wrchs hns2 fs disk start2 text2)))
      (disk (mv-nth 1
                    (l3-wrchs hns2 fs disk start2 text2))))
     (:instance l3-wrchs-returns-fs (hns hns2)
                (start start2)
                (text text2))))))

(defthm
  l3-stat-after-write
  (implies
   (and (l3-bounded-fs-p fs (len disk))
        (stringp text2)
        (symbol-listp hns1)
        (symbol-listp hns2)
        (natp start2)
        (stringp (l3-stat hns1 fs disk))
        (block-listp disk))
   (mv-let
     (new-fs new-disk)
     (l3-wrchs hns2 fs disk start2 text2)
     (equal
      (l3-stat hns1 new-fs new-disk)
      (if
       (equal hns1 hns2)
       (coerce (insert-text (coerce (l3-stat hns1 fs disk) 'list)
                            start2 text2)
               'string)
       (l3-stat hns1 fs disk)))))
  :hints
  (("goal"
    :in-theory (disable l3-stat-correctness-1
                        l2-stat-after-write l3-wrchs-returns-fs)
    :use
    ((:instance l3-stat-correctness-1 (hns hns1))
     (:instance
      l3-stat-correctness-1 (hns hns1)
      (fs (mv-nth 0 (l3-wrchs hns2 fs disk start2 text2)))
      (disk (mv-nth 1
                    (l3-wrchs hns2 fs disk start2 text2))))
     (:instance l2-stat-after-write
                (fs (l3-to-l2-fs fs disk)))
     (:instance l3-wrchs-returns-fs (hns hns2)
                (start start2)
                (text text2))))))

;; This is a proof of the first read-after-write property.
(defthm
  l3-read-after-write-1
  (implies (and (l3-bounded-fs-p fs (len disk))
                (stringp text)
                (symbol-listp hns)
                (natp start)
                (equal n (length text))
                (stringp (l3-stat hns fs disk))
                (block-listp disk))
           (mv-let (new-fs new-disk)
             (l3-wrchs hns fs disk start text)
             (equal (l3-rdchs hns new-fs new-disk start n)
                    text)))
  :hints
  (("goal"
    :in-theory (disable l3-read-after-write-1-lemma-3
                        l3-stat-after-write)
    :use ((:instance l3-read-after-write-1-lemma-3 (hns1 hns)
                     (hns2 hns)
                     (start2 start)
                     (text2 text))
          (:instance l3-stat-after-write (hns1 hns)
                     (hns2 hns)
                     (start2 start)
                     (text2 text))))))

;; This is a proof of the second read-after-write property.
(defthm
  l3-read-after-write-2
  (implies
   (and (block-listp disk)
        (l3-bounded-fs-p fs (len disk))
        (stringp text1)
        (stringp text2)
        (symbol-listp hns1)
        (symbol-listp hns2)
        (not (equal hns1 hns2))
        (natp start1)
        (natp start2)
        (natp n1)
        (natp n2))
   (mv-let (new-fs new-disk)
     (l3-wrchs hns2 fs disk start2 text2)
     (equal (l3-rdchs hns1 new-fs new-disk start1 n1)
            (l3-rdchs hns1 fs disk start1 n1))))
  :hints
  (("goal"
    :in-theory (disable l3-read-after-write-1-lemma-3
                        l3-stat-after-write)
    :use (l3-read-after-write-1-lemma-3 l3-stat-after-write))))

;; This proves the equivalent of the first read-after-write property for
;; create.
(defthm l3-read-after-create-1
  (implies (and (l3-bounded-fs-p fs (len disk))
                (stringp text)
                (symbol-listp hns)
                (equal n (length text))
                (not (l3-stat hns fs disk))
                (block-listp disk))
           (mv-let (new-fs new-disk)
             (l3-create hns fs disk text)
             (implies
              (stringp (l3-stat hns new-fs new-disk))
              (equal (l3-rdchs hns new-fs new-disk 0 n) text))))
  :hints (("Goal" :in-theory (disable
                              (:rewrite l2-read-after-create-1)
                              (:rewrite l3-to-l2-fs-correctness-1)
                              (:rewrite l3-create-correctness-1)
                              (:rewrite l3-stat-correctness-1)
                              (:rewrite l3-create-returns-fs))
           :use ((:instance l2-read-after-create-1
                                   (fs (l3-to-l2-fs fs disk)))
                        l3-to-l2-fs-correctness-1
                        (:instance l3-bounded-fs-p-correctness-1
                                   (disk-length (len disk)))
                        l3-create-correctness-1
                        (:instance l3-stat-correctness-1
                                   (fs (mv-nth 0 (l3-create hns fs disk text)))
                                   (disk (mv-nth 1 (l3-create hns fs disk text))))
                        l3-create-returns-fs))))

;; This proves the equivalent of the second read-after-write property for
;; create.
(defthm l3-read-after-create-2
  (implies (and (l3-bounded-fs-p fs (len disk))
                (stringp text2)
                (symbol-listp hns1)
                (symbol-listp hns2)
                (not (equal hns1 hns2))
                (natp start1)
                (natp n1)
                (not (l3-stat hns2 fs disk))
                (stringp (l3-stat hns1 fs disk))
                (block-listp disk))
           (mv-let (new-fs new-disk) (l3-create hns2 fs disk text2)
             (implies
              (stringp (l3-stat hns2 new-fs new-disk))
              (equal (l3-rdchs hns1 new-fs new-disk start1 n1)
                     (l3-rdchs hns1 fs disk start1 n1)))))
  :hints (("Goal"
           :in-theory (disable
                       (:rewrite l2-read-after-create-2)
                       (:rewrite l3-to-l2-fs-correctness-1)
                       (:rewrite l3-stat-correctness-2)
                       (:rewrite l3-create-returns-fs)
                       (:rewrite l3-stat-correctness-1)
                       (:rewrite l3-create-correctness-1)
                       (:rewrite l3-rdchs-correctness-1)
                       l3-bounded-fs-p-correctness-1)
           :use ((:instance l2-read-after-create-2
                            (fs (l3-to-l2-fs fs disk)))
                 l3-to-l2-fs-correctness-1
                 (:instance l3-stat-correctness-2 (hns hns2))
                 (:instance l3-stat-correctness-1 (hns hns1))
                 (:instance l3-stat-correctness-1 (hns hns2)
                            (fs (mv-nth 0 (l3-create hns2 fs disk text2)))
                            (disk (mv-nth 1 (l3-create hns2 fs disk text2))))
                 (:instance l3-create-returns-fs (hns hns2)
                            (text text2))
                 (:instance l3-stat-correctness-1 (hns hns2)
                            (fs (mv-nth 0 (l3-create hns2 fs disk text2)))
                            (disk (mv-nth 1 (l3-create hns2 fs disk text2))))
                 (:instance l3-create-correctness-1 (hns hns2)
                            (text text2))
                 (:instance l3-bounded-fs-p-correctness-1
                            (disk-length (len disk)))
                 (:instance l3-rdchs-correctness-1 (hns hns1)
                            (start start1)
                            (n n1))
                 (:instance l3-rdchs-correctness-1 (hns hns1)
                            (start start1)
                            (n n1)
                            (fs (mv-nth 0 (l3-create hns2 fs disk text2)))
                            (disk (mv-nth 1 (l3-create hns2 fs disk text2))))))))

; Find length of file
(defun wc-len (hns fs disk)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l3-fs-p fs)
                              (block-listp disk))))
  (let ((file (l3-stat hns fs disk)))
    (if (not (stringp file))
        nil
      (length file))))

; Prove (list-of-chars-to-string (string-to-chars str))
;       (string-to-chars (list-of-chars-to-string char-list))
; and then, you will be positioned to use either form.
#||From :doc STR::STD/STRINGS/COERCE
  Theorem: <coerce-inverse-1-better>

    (defthm coerce-inverse-1-better
            (equal (coerce (coerce x 'string) 'list)
                   (if (stringp x)
                       nil (make-character-list x))))

  Theorem: <coerce-inverse-2-better>

    (defthm coerce-inverse-2-better
            (equal (coerce (coerce x 'list) 'string)
                   (if (stringp x) x "")))
That takes care of that
||#
; Correspond (or not) with Linux system calls -- the low-level stuff...

; Add file -- or, if you will, create a file with some initial contents

; and so on...
