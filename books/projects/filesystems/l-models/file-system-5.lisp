(in-package "ACL2")

;  file-system-5.lisp                                  Mihir Mehta

; Here we build on model 4 to add permissions to the file system. We'll go with
; something simple: let users be defined by integers, and not belong to groups
; at this point. Thus, only read and write permissions exist, and they are
; limited to being on/off for the creating user, and on/off for others.

; Further, we're not changing anything about directories at this point.

(include-book "file-system-4")
(in-theory (disable l4-stricter-fs-p))

(defund l5-regular-file-entry-p (entry)
  (declare (xargs :guard t))
  (and (equal (len entry) 6)
       (nat-listp (car entry))
       (natp (cadr entry))
       (feasible-file-length-p (len (car entry)) (cadr entry))
       (booleanp (car (cddr entry)))
       (booleanp (cadr (cddr entry)))
       (booleanp (car (cddr (cddr entry))))
       (booleanp (cadr (cddr (cddr entry))))
       (natp (cddr (cddr (cddr entry))))))

(defund l5-regular-file-contents (entry)
  (declare (xargs :guard (l5-regular-file-entry-p entry)
                  :guard-hints (("Goal" :in-theory (enable l5-regular-file-entry-p)))))
  (car entry))

(defund l5-regular-file-length (entry)
  (declare (xargs :guard (l5-regular-file-entry-p entry)
                  :guard-hints (("Goal" :in-theory (enable l5-regular-file-entry-p)))))
  (cadr entry))

(defund l5-regular-file-user-read (entry)
  (declare (xargs :guard (l5-regular-file-entry-p entry)
                  :guard-hints (("Goal" :in-theory (enable l5-regular-file-entry-p)))))
  (car (cddr entry)))

(defund l5-regular-file-user-write (entry)
  (declare (xargs :guard (l5-regular-file-entry-p entry)
                  :guard-hints (("Goal" :in-theory (enable l5-regular-file-entry-p)))))
  (cadr (cddr entry)))

(defund l5-regular-file-other-read (entry)
  (declare (xargs :guard (l5-regular-file-entry-p entry)
                  :guard-hints (("Goal" :in-theory (enable l5-regular-file-entry-p)))))
  (car (cddr (cddr entry))))

(defund l5-regular-file-other-write (entry)
  (declare (xargs :guard (l5-regular-file-entry-p entry)
                  :guard-hints (("Goal" :in-theory (enable l5-regular-file-entry-p)))))
  (cadr (cddr (cddr entry))))

(defund l5-regular-file-user (entry)
  (declare (xargs :guard (l5-regular-file-entry-p entry)
                  :guard-hints (("Goal" :in-theory (enable l5-regular-file-entry-p)))))
  (cddr (cddr (cddr entry))))

(defund l5-make-regular-file
  (contents length user-read user-write other-read other-write user)
  (declare (xargs :guard
                  (and (nat-listp contents)
                       (natp length)
                       (feasible-file-length-p (len contents)
                                               length)
                       (booleanp user-read)
                       (booleanp user-write)
                       (booleanp other-read)
                       (booleanp other-write)
                       (natp user))))
  (list* contents length user-read user-write other-read other-write user))

(defthm
  l5-make-regular-file-correctness-1
  (implies (and (nat-listp contents)
                (natp length)
                (feasible-file-length-p (len contents)
                                        length)
                (booleanp user-read)
                (booleanp user-write)
                (booleanp other-read)
                (booleanp other-write)
                (natp user))
           (l5-regular-file-entry-p
            (l5-make-regular-file contents length user-read user-write
                                  other-read other-write user)))
  :hints (("goal" :in-theory (enable l5-regular-file-entry-p
                                     l5-make-regular-file))))

(defthm
  l5-make-regular-file-correctness-2
  (let ((entry (l5-make-regular-file contents length user-read user-write
                                     other-read other-write user)))
    (and (equal (l5-regular-file-contents entry)
                contents)
         (equal (l5-regular-file-length entry)
                length)
         (equal (l5-regular-file-user-read entry)
                user-read)
         (equal (l5-regular-file-user-write entry)
                user-write)
         (equal (l5-regular-file-other-read entry)
                other-read)
         (equal (l5-regular-file-other-write entry)
                other-write)
         (equal (l5-regular-file-user entry)
                user)))
  :hints (("goal" :in-theory (enable l5-regular-file-entry-p
                                     l5-make-regular-file
                                     l5-regular-file-contents
                                     l5-regular-file-length
                                     l5-regular-file-user-read
                                     l5-regular-file-user-write
                                     l5-regular-file-other-read
                                     l5-regular-file-other-write
                                     l5-regular-file-user))))

(defthm
  l5-regular-file-entry-p-correctness-1
  (implies (l5-regular-file-entry-p entry)
           (and (nat-listp (l5-regular-file-contents entry))
                (natp (l5-regular-file-length entry))
                (feasible-file-length-p (len (l5-regular-file-contents entry))
                                        (l5-regular-file-length entry))
                (booleanp (l5-regular-file-user-read entry))
                (booleanp (l5-regular-file-user-write entry))
                (booleanp (l5-regular-file-other-read entry))
                (booleanp (l5-regular-file-other-write entry))
                (natp (l5-regular-file-user entry))))
  :hints (("goal" :in-theory (enable l5-regular-file-entry-p
                                     l5-regular-file-contents
                                     l5-regular-file-length
                                     l5-regular-file-user-read
                                     l5-regular-file-user-write
                                     l5-regular-file-other-read
                                     l5-regular-file-other-write
                                     l5-regular-file-user))))

(defthm l5-regular-file-entry-p-correctness-2
  (booleanp (l5-regular-file-entry-p entry))
  :hints (("goal" :in-theory (enable l5-regular-file-entry-p))))

; This function defines a valid filesystem. It's an alist where all the cars
; are symbols and all the cdrs are either further filesystems or regular files.
(defun l5-fs-p (fs)
  (declare (xargs :guard t))
  (if (atom fs)
      (null fs)
    (and (let ((directory-or-file-entry (car fs)))
           (if (atom directory-or-file-entry)
               nil
             (let ((name (car directory-or-file-entry))
                   (entry (cdr directory-or-file-entry)))
               (and (symbolp name)
                    (or (l5-regular-file-entry-p entry)
                        (l5-fs-p entry))))))
         (l5-fs-p (cdr fs)))))

(defthm
  l5-regular-file-entry-p-correctness-3
  (implies (l5-regular-file-entry-p entry)
           (not (l5-fs-p entry)))
  :rule-classes
  (:rewrite
   (:rewrite :corollary (implies (l5-fs-p entry)
                                 (not (l5-regular-file-entry-p entry)))))
  :hints (("goal" :in-theory (enable l5-regular-file-entry-p))))

(defthm alistp-l5-fs-p
  (implies (l5-fs-p fs)
           (alistp fs)))

(defthm l5-fs-p-assoc
  (implies (and (l5-fs-p fs)
                (consp (assoc-equal name fs))
                (not (l5-regular-file-entry-p (cdr (assoc-equal name fs)))))
           (l5-fs-p (cdr (assoc-equal name fs)))))

(defund l5-regular-file-readable-p (entry user)
  (declare (xargs :guard (l5-regular-file-entry-p entry)))
  (if (equal (l5-regular-file-user entry) user)
      (l5-regular-file-user-read entry)
    (l5-regular-file-other-read entry)))

;; This function allows a file or directory to be found in a filesystem given a
;; path.
;; Important change from l4: we are now returning the file object, rather than
;; the text contents of the file. Without this, stating the stat correctness
;; theorems will be pretty close to impossible.
(defun l5-stat (hns fs disk)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l5-fs-p fs)
                              (block-listp disk))))
  (if (atom hns)
      fs
    (if (atom fs)
        nil
      (let ((sd (assoc (car hns) fs)))
        (if (atom sd)
            nil
          (if (l5-regular-file-entry-p (cdr sd))
              (and (null (cdr hns))
                   (cdr sd))
            (l5-stat (cdr hns) (cdr sd) disk)))))))

(defund l5-regular-file-writable-p (entry user)
  (declare (xargs :guard (l5-regular-file-entry-p entry)))
  (if (equal (l5-regular-file-user entry) user)
      (l5-regular-file-user-write entry)
    (l5-regular-file-other-write entry)))

;; This function finds a text file given its path and reads a segment of
;; that text file.
(defun l5-rdchs (hns fs disk start n user)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l5-fs-p fs)
                              (natp start)
                              (natp n)
                              (block-listp disk)
                              (natp user))))
  (let ((file (l5-stat hns fs disk)))
    (if (or (not (l5-regular-file-entry-p file))
            (not (l5-regular-file-readable-p file user)))
        nil
      (let* ((file-text
              (coerce
               (unmake-blocks (fetch-blocks-by-indices
                               disk
                               (l5-regular-file-contents file))
                              (l5-regular-file-length file))
               'string))
             (file-length (length file-text))
             (end (+ start n)))
        (if (< file-length end)
            nil
          (subseq file-text start (+ start n)))))))

; This function writes a specified text string to a specified position to a
; text file at a specified path.
(defun l5-wrchs (hns fs disk alv start text user)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l5-fs-p fs)
                              (natp start)
                              (stringp text)
                              (block-listp disk)
                              (boolean-listp alv)
                              (equal (len alv) (len disk)))
                  :guard-debug t))
  (if (atom hns)
      (mv fs disk alv) ;; error - showed up at fs with no name  - so leave fs unchanged
    (if (atom fs)
        (mv nil disk alv) ;; error, so leave fs unchanged
      (let ((sd (assoc (car hns) fs)))
        (if (atom sd)
            (mv fs disk alv) ;; file-not-found error, so leave fs unchanged
          (let ((contents (cdr sd)))
            (if (l5-regular-file-entry-p (cdr sd))
                (if (or (cdr hns) (not (l5-regular-file-writable-p (cdr sd) user)))
                    (mv (cons (cons (car sd) (cdr sd))
                              (remove1-assoc (car hns) fs))
                        disk
                        alv) ;; error, so leave fs unchanged
                  (let* ((old-text
                          (unmake-blocks
                           (fetch-blocks-by-indices disk (l5-regular-file-contents (cdr sd)))
                           (l5-regular-file-length (cdr sd))))
                         (alv-after-free
                          (set-indices-in-alv alv (l5-regular-file-contents (cdr sd)) nil))
                         (new-text (insert-text old-text start text))
                         (new-blocks (make-blocks new-text))
                         (new-indices
                          (find-n-free-blocks alv-after-free (len new-blocks))))
                    (if (not (equal (len new-indices) (len new-blocks)))
                        ;; we have an error because of insufficient disk space
                        ;; - so we leave the fs unchanged
                        (mv (cons (cons (car sd) contents)
                                  (remove1-assoc (car hns) fs))
                            disk
                            alv)
                      (mv (cons (cons (car sd)
                                      (l5-make-regular-file
                                       new-indices
                                       (len new-text)
                                       (l5-regular-file-user-read (cdr sd))
                                       (l5-regular-file-user-write (cdr sd))
                                       (l5-regular-file-other-read (cdr sd))
                                       (l5-regular-file-other-write (cdr sd))
                                       (l5-regular-file-user (cdr sd))))
                                (remove1-assoc (car hns) fs))
                          ;; this (take) means we write as many blocks as we can
                          ;; if we run out of space
                          (set-indices disk new-indices new-blocks)
                          (set-indices-in-alv alv-after-free new-indices t)))))
              (mv-let (new-contents new-disk new-alv)
                (l5-wrchs (cdr hns) contents disk alv start text user)
                (mv (cons (cons (car sd) new-contents)
                          (remove1-assoc (car hns) fs))
                    new-disk
                    new-alv)))
            ))))))

(defun l5-to-l4-fs (fs)
  (declare (xargs :guard (l5-fs-p fs)))
  (if (atom fs)
      nil
    (cons (let ((directory-or-file-entry (car fs)))
            (let ((name (car directory-or-file-entry))
                  (entry (cdr directory-or-file-entry)))
              (if (l5-regular-file-entry-p entry)
                  (list* name
                         (l5-regular-file-contents entry)
                         (l5-regular-file-length entry))
                (cons name (l5-to-l4-fs entry)))))
          (l5-to-l4-fs (cdr fs)))))

(defthm
  l5-to-l4-fs-correctness-1
  (implies (l5-fs-p fs)
           (l3-fs-p (l5-to-l4-fs fs)))
  :rule-classes
  (:rewrite
   (:rewrite :corollary (implies (l5-fs-p fs)
                                 (l4-fs-p (l5-to-l4-fs fs)))))
  :hints (("goal" :in-theory (enable l3-regular-file-entry-p))))

(defthm l5-stat-correctness-1-lemma-1
  (implies (and (l5-fs-p fs)
                (consp (assoc-equal name fs)))
           (consp (assoc-equal name (l5-to-l4-fs fs)))))

(defthm l5-stat-correctness-1-lemma-2
  (implies (and (consp fs))
           (consp (l5-to-l4-fs fs))))

(defthm l5-stat-correctness-1-lemma-3
  (implies
   (and (consp (assoc-equal name fs))
        (l5-regular-file-entry-p (cdr (assoc-equal name fs)))
        (l5-fs-p fs))
   (and (consp (assoc-equal name (l5-to-l4-fs fs)))
        (l3-regular-file-entry-p (cdr (assoc-equal name (l5-to-l4-fs fs))))
        (equal (cadr (assoc-equal name
                                  (l5-to-l4-fs fs)))
               (l5-regular-file-contents (cdr (assoc-equal name fs))))
        (equal (cddr (assoc-equal name
                                  (l5-to-l4-fs fs)))
               (l5-regular-file-length (cdr (assoc-equal name fs))))))
  :hints (("goal" :in-theory (enable l3-regular-file-entry-p)) ))

(defthm l5-stat-correctness-1-lemma-4
  (implies (and (l5-fs-p fs)
                (l5-fs-p (cdr (assoc-equal name fs))))
           (equal (cdr (assoc-equal name (l5-to-l4-fs fs)))
                  (l5-to-l4-fs (cdr (assoc-equal name fs))))))

;; This is the first of two theorems showing the equivalence of the l5 and l4
;; versions of stat.
(defthm
  l5-stat-correctness-1
  (implies
   (and (symbol-listp hns)
        (l5-fs-p fs)
        (block-listp disk))
   (let
       ((file (l5-stat hns fs disk)))
     (implies
      (and (l5-regular-file-entry-p file)
           (l5-regular-file-readable-p file user))
      (equal
       (l3-stat hns (l5-to-l4-fs fs) disk)
       (coerce
        (unmake-blocks
         (fetch-blocks-by-indices disk (l5-regular-file-contents file))
         (l5-regular-file-length file))
        'string)))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (symbol-listp hns)
          (l5-fs-p fs)
          (block-listp disk))
     (let
         ((file (l5-stat hns fs disk)))
       (implies
        (and (l5-regular-file-entry-p file)
             (l5-regular-file-readable-p file user)
             (natp user))
        (equal
         (l4-stat hns (l5-to-l4-fs fs) disk)
         (coerce
          (unmake-blocks
           (fetch-blocks-by-indices disk (l5-regular-file-contents file))
           (l5-regular-file-length file))
          'string))))))))

(defthm
  l5-stat-correctness-2-lemma-1
  (implies
   (and (consp (assoc-equal name (l5-to-l4-fs fs)))
        (l5-fs-p fs))
   (equal (l3-regular-file-entry-p (cdr (assoc-equal name (l5-to-l4-fs fs))))
          (l5-regular-file-entry-p (cdr (assoc-equal name fs)))))
  :hints (("goal" :in-theory (enable l3-regular-file-entry-p))))

;; This is the second of two theorems showing the equivalence of the l5 and l4
;; versions of stat.
(defthm
  l5-stat-correctness-2
  (implies (and (symbol-listp hns)
                (l5-fs-p fs)
                (block-listp disk)
                (natp user)
                (l5-fs-p (l5-stat hns fs disk)))
           (equal (l3-stat hns (l5-to-l4-fs fs) disk)
                  (l5-to-l4-fs (l5-stat hns fs disk))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary (implies (and (symbol-listp hns)
                             (l5-fs-p fs)
                             (block-listp disk)
                             (natp user)
                             (l5-fs-p (l5-stat hns fs disk)))
                        (equal (l4-stat hns (l5-to-l4-fs fs) disk)
                               (l5-to-l4-fs (l5-stat hns fs disk)))))))

(defthm l5-wrchs-returns-fs-lemma-1
  (implies (l5-fs-p fs)
           (l5-fs-p (remove1-assoc-equal name fs))))

(defthm
  l5-wrchs-returns-fs-lemma-2
  (implies
   (and
    (l5-regular-file-entry-p (cdr (assoc-equal name fs)))
    (l5-regular-file-writable-p (cdr (assoc-equal name fs))
                                user)
    (equal
     (count-free-blocks
      (set-indices-in-alv
       alv
       (l5-regular-file-contents (cdr (assoc-equal name fs)))
       nil))
     (len
      (make-blocks
       (insert-text
        (unmake-blocks
         (fetch-blocks-by-indices
          disk
          (l5-regular-file-contents
           (cdr (assoc-equal name fs))))
         (l5-regular-file-length (cdr (assoc-equal name fs))))
        start text))))
    (consp (assoc-equal name fs))
    (l5-fs-p fs)
    (boolean-listp alv)
    (stringp text)
    (integerp start)
    (<= 0 start)
    (block-listp disk)
    (equal (len alv) (len disk))
    (integerp user))
   (l5-regular-file-entry-p
    (l5-make-regular-file
     (find-n-free-blocks
      (set-indices-in-alv
       alv
       (l5-regular-file-contents (cdr (assoc-equal name fs)))
       nil)
      (count-free-blocks
       (set-indices-in-alv
        alv
        (l5-regular-file-contents (cdr (assoc-equal name fs)))
        nil)))
     (len
      (insert-text
       (unmake-blocks
        (fetch-blocks-by-indices
         disk
         (l5-regular-file-contents (cdr (assoc-equal name fs))))
        (l5-regular-file-length (cdr (assoc-equal name fs))))
       start text))
     (l5-regular-file-user-read (cdr (assoc-equal name fs)))
     (l5-regular-file-user-write (cdr (assoc-equal name fs)))
     (l5-regular-file-other-read (cdr (assoc-equal name fs)))
     (l5-regular-file-other-write (cdr (assoc-equal name fs)))
     (l5-regular-file-user (cdr (assoc-equal name fs))))))
  :hints
  (("goal"
    :in-theory (disable l5-make-regular-file-correctness-1)
    :use
    (:instance
     l5-make-regular-file-correctness-1
     (contents
      (find-n-free-blocks
       (set-indices-in-alv
        alv
        (l5-regular-file-contents (cdr (assoc-equal name fs)))
        nil)
       (count-free-blocks
        (set-indices-in-alv
         alv
         (l5-regular-file-contents (cdr (assoc-equal name fs)))
         nil))))
     (length
      (len
       (insert-text
        (unmake-blocks
         (fetch-blocks-by-indices
          disk
          (l5-regular-file-contents
           (cdr (assoc-equal name fs))))
         (l5-regular-file-length (cdr (assoc-equal name fs))))
        start text)))
     (user-read
      (l5-regular-file-user-read (cdr (assoc-equal name fs))))
     (user-write
      (l5-regular-file-user-write (cdr (assoc-equal name fs))))
     (other-read
      (l5-regular-file-other-read (cdr (assoc-equal name fs))))
     (other-write
      (l5-regular-file-other-write (cdr (assoc-equal name fs))))
     (user
      (l5-regular-file-user (cdr (assoc-equal name fs))))))))

(defthm
  l5-wrchs-returns-fs
  (implies
   (and (l5-fs-p fs)
        (stringp text)
        (integerp start)
        (<= 0 start)
        (integerp user)
        (<= 0 user)
        (symbol-listp hns)
        (block-listp disk)
        (equal (len alv) (len disk))
        (boolean-listp alv))
   (l5-fs-p
    (mv-nth 0
            (l5-wrchs hns fs disk alv start text user)))))

(defthm l5-wrchs-correctness-1-lemma-1
  (implies (l5-fs-p fs)
           (equal (remove1-assoc-equal name (l5-to-l4-fs fs))
                  (l5-to-l4-fs (remove1-assoc-equal name fs)))))

(defthm
  l5-wrchs-correctness-1-lemma-2
  (implies
   (and (consp (assoc-equal name fs))
        (l5-fs-p (cdr (assoc-equal name fs)))
        (l5-fs-p fs)
        (boolean-listp alv)
        (indices-marked-listp (l4-collect-all-index-lists (l5-to-l4-fs fs))
                              alv))
   (indices-marked-listp
    (l4-collect-all-index-lists (l5-to-l4-fs (cdr (assoc-equal name fs))))
    alv)))

(defthm
  l5-wrchs-correctness-1-lemma-3
  (implies
   (and (l5-fs-p (cdr (assoc-equal name fs)))
        (disjoint-list-listp (l4-collect-all-index-lists (l5-to-l4-fs fs))))
   (disjoint-list-listp
    (l4-collect-all-index-lists (l5-to-l4-fs (cdr (assoc-equal name fs))))))
  :hints (("goal" :in-theory (enable disjoint-list-listp))))

(defthm
  l5-wrchs-correctness-1-lemma-4
  (implies
   (and (consp (assoc-equal name fs))
        (l5-fs-p (cdr (assoc-equal name fs)))
        (l5-fs-p fs)
        (no-duplicates-listp (l4-collect-all-index-lists (l5-to-l4-fs fs))))
   (no-duplicates-listp
    (l4-collect-all-index-lists (l5-to-l4-fs (cdr (assoc-equal name fs)))))))

(defthm l5-wrchs-correctness-1-lemma-5
  (implies (and (l5-fs-p fs)
                (consp (assoc-equal name fs))
                (l5-fs-p (cdr (assoc-equal name fs)))
                (l4-stricter-fs-p (l5-to-l4-fs fs) alv))
           (l4-stricter-fs-p (l5-to-l4-fs (cdr (assoc-equal name fs)))
                             alv))
  :hints (("goal" :in-theory (enable l4-stricter-fs-p))))

(defthm
  l5-wrchs-correctness-1-lemma-6
  (implies
   (and (consp (assoc-equal name fs))
        (l5-regular-file-entry-p (cdr (assoc-equal name fs)))
        (l5-fs-p fs))
   (equal (cdr (assoc-equal name (l5-to-l4-fs fs)))
          (cons (l5-regular-file-contents (cdr (assoc-equal name fs)))
                (l5-regular-file-length (cdr (assoc-equal name fs)))))))

(defthm l5-wrchs-correctness-1-lemma-7
  (implies (and (l5-fs-p fs))
           (equal (consp (assoc-equal name (l5-to-l4-fs fs)))
                  (consp (assoc-equal name fs)))))

(defthm l5-wrchs-correctness-1-lemma-8
  (implies (l4-stricter-fs-p fs alv)
           (and (boolean-listp alv)
                (bounded-nat-listp (l4-list-all-indices fs) (len alv))))
  :hints (("goal" :in-theory (enable l4-stricter-fs-p))))

(defthm
  l5-wrchs-correctness-1
  (implies
   (and (l5-fs-p fs)
        (stringp text)
        (natp start)
        (natp user)
        (symbol-listp hns)
        (block-listp disk)
        (equal (len alv) (len disk))
        (<= (len (make-blocks (insert-text nil start text)))
            (count-free-blocks alv)))
   (let ((l4-fs (l5-to-l4-fs fs))
         (file (l5-stat hns fs disk)))
     (implies (and (l4-stricter-fs-p l4-fs alv)
                   (or (not (l5-regular-file-entry-p file))
                       (l5-regular-file-writable-p file user)))
              (equal (l4-wrchs hns l4-fs disk alv start text)
                     (mv-let (new-fs new-disk new-alv)
                       (l5-wrchs hns fs disk alv start text user)
                       (mv (l5-to-l4-fs new-fs)
                           new-disk new-alv))))))
  :hints
  (("goal" :in-theory (enable l3-regular-file-entry-p)
    :induct (l5-stat hns fs disk))))

(defthm l5-rdchs-correctness-1-lemma-1
  (implies (and (symbol-listp hns)
                (l5-fs-p fs)
                (block-listp disk)
                (integerp user)
                (<= 0 user))
           (equal (stringp (l3-stat hns (l5-to-l4-fs fs) disk))
                  (l5-regular-file-entry-p (l5-stat hns fs disk))))
  :hints (("goal" :in-theory (enable l3-regular-file-entry-p))))

;; This theorem proves the equivalence of the l5 and l4 versions of rdchs.
(defthm l5-rdchs-correctness-1
  (implies (and (symbol-listp hns)
                (l5-fs-p fs)
                (natp start)
                (natp n)
                (block-listp disk)
                (let ((file (l5-stat hns fs disk)))
                  (and (or (not (l5-regular-file-entry-p file))
                           (l5-regular-file-readable-p file user))))
                (natp user))
           (equal (l4-rdchs hns (l5-to-l4-fs fs)
                            disk start n)
                  (l5-rdchs hns fs disk start n user))))

(defthm
  l5-wrchs-returns-disk-lemma-1
  (implies
   (l5-regular-file-entry-p entry)
   (equal (bounded-nat-listp (binary-append (l5-regular-file-contents entry)
                                            y)
                             b)
          (and (bounded-nat-listp (l5-regular-file-contents entry)
                                  b)
               (bounded-nat-listp y b))))
  :hints (("goal" :in-theory (disable bounded-nat-listp-correctness-2)
           :use (:instance bounded-nat-listp-correctness-2
                           (x (l5-regular-file-contents entry))))))

(defthm
  l5-wrchs-returns-disk-lemma-2
  (implies
   (and
    (l5-fs-p fs)
    (boolean-listp alv)
    (bounded-nat-listp (l4-list-all-indices (l5-to-l4-fs fs))
                       b))
   (bounded-nat-listp
    (l4-list-all-indices (l5-to-l4-fs (cdr fs)))
    b))
  :hints (("goal" :in-theory (enable l4-list-all-indices))))

(defthm
  l5-wrchs-returns-disk-lemma-3
  (implies
   (and (consp (assoc-equal name fs))
        (l5-fs-p (cdr (assoc-equal name fs)))
        (l5-fs-p fs)
        (boolean-listp alv)
        (bounded-nat-listp (l4-list-all-indices (l5-to-l4-fs fs))
                           b))
   (bounded-nat-listp
    (l4-list-all-indices (l5-to-l4-fs (cdr (assoc-equal name fs))))
    b))
  :hints (("goal" :in-theory (enable l4-list-all-indices))))

(defthm
  l5-wrchs-returns-disk-lemma-4
  (implies
   (and
    (consp (assoc-equal name fs))
    (l5-regular-file-entry-p (cdr (assoc-equal name fs)))
    (l5-fs-p fs)
    (bounded-nat-listp (l4-list-all-indices (l5-to-l4-fs fs)) b))
   (bounded-nat-listp
    (l5-regular-file-contents (cdr (assoc-equal name fs))) b))
  :hints (("goal" :in-theory (enable l4-list-all-indices l3-regular-file-entry-p)) ))

(defthm
  l5-wrchs-returns-disk
  (implies (and (l5-fs-p fs)
                (stringp text)
                (integerp start)
                (<= 0 start)
                (integerp user)
                (<= 0 user)
                (symbol-listp hns)
                (block-listp disk)
                (equal (len alv) (len disk))
                (boolean-listp alv)
                (bounded-nat-listp (l4-list-all-indices (l5-to-l4-fs fs))
                                   (len disk)))
           (block-listp (mv-nth 1
                                (l5-wrchs hns fs disk alv start text user)))))

(defthm
  l5-read-after-write-1-lemma-1
  (implies
   (and (l5-fs-p fs)
        (boolean-listp alv)
        (stringp text)
        (integerp start)
        (<= 0 start)
        (symbol-listp hns)
        (block-listp disk)
        (equal (len alv) (len disk))
        (integerp user)
        (<= 0 user)
        (l5-regular-file-entry-p (l5-stat hns fs disk)))
   (equal (l5-regular-file-entry-p
           (l5-stat hns
                    (mv-nth 0
                            (l5-wrchs hns fs disk alv start text user))
                    (mv-nth 1
                            (l5-wrchs hns fs disk alv start text user))))
          (l5-regular-file-entry-p (l5-stat hns fs disk)))))

(defthm
  l5-read-after-write-1-lemma-2
  (implies
   (and (l5-fs-p fs)
        (boolean-listp alv)
        (stringp text)
        (integerp start)
        (<= 0 start)
        (symbol-listp hns)
        (block-listp disk)
        (equal (len alv) (len disk))
        (integerp user)
        (<= 0 user))
   (let
       ((file (l5-stat hns fs disk))
        (new-file (l5-stat hns
                           (mv-nth 0
                                   (l5-wrchs hns fs disk alv start text user))
                           (mv-nth 1
                                   (l5-wrchs hns fs disk alv start text user)))))
     (implies (l5-regular-file-entry-p file)
              (and (equal (l5-regular-file-user-read new-file)
                          (l5-regular-file-user-read file))
                   (equal (l5-regular-file-user new-file)
                          (l5-regular-file-user file))
                   (equal (l5-regular-file-other-read new-file)
                          (l5-regular-file-other-read file)))))))

(defthm
  l5-read-after-write-1-lemma-3
  (implies
   (and (l5-fs-p fs)
        (boolean-listp alv)
        (stringp text)
        (integerp start)
        (<= 0 start)
        (symbol-listp hns)
        (block-listp disk)
        (equal (len alv) (len disk))
        (integerp user1)
        (<= 0 user1)
        (integerp user2)
        (<= 0 user2))
   (let ((file (l5-stat hns fs disk))
         (new-file
          (l5-stat hns
                   (mv-nth 0
                           (l5-wrchs hns fs disk alv start text user2))
                   (mv-nth 1
                           (l5-wrchs hns fs disk alv start text user2)))))
     (implies (l5-regular-file-entry-p file)
              (equal (l5-regular-file-readable-p new-file user1)
                     (l5-regular-file-readable-p file user1)))))
  :hints (("goal" :in-theory (enable l5-regular-file-readable-p))))

(defthm
  l5-read-after-write-1
  (implies (and (l5-fs-p fs)
                (l4-stricter-fs-p (l5-to-l4-fs fs) alv)
                (stringp text)
                (natp start)
                (symbol-listp hns)
                (boolean-listp alv)
                (block-listp disk)
                (equal (len alv) (len disk))
                (natp user1)
                (natp user2)
                (<= (len (make-blocks (insert-text nil start text)))
                    (count-free-blocks alv))
                (equal n (length text))
                (l5-regular-file-entry-p (l5-stat hns fs disk))
                (l5-regular-file-readable-p (l5-stat hns fs disk)
                                            user1)
                (l5-regular-file-writable-p (l5-stat hns fs disk)
                                            user2))
           (mv-let (new-fs new-disk new-alv)
             (l5-wrchs hns fs disk alv start text user2)
             (declare (ignore new-alv))
             (equal (l5-rdchs hns new-fs new-disk start n user1)
                    text)))
  :hints
  (("goal"
    :in-theory (disable l5-rdchs-correctness-1
                        l5-wrchs-correctness-1
                        l4-read-after-write-1)
    :use
    ((:instance l5-rdchs-correctness-1
                (fs (mv-nth 0
                            (l5-wrchs hns fs disk alv start text user2)))
                (disk (mv-nth 1
                              (l5-wrchs hns fs disk alv start text user2)))
                (user user1))
     (:instance l5-wrchs-correctness-1 (user user2))
     (:instance l4-read-after-write-1
                (fs (l5-to-l4-fs fs)))))))

(defthmd
  l5-read-after-write-2-lemma-6
  (implies
   (and (l5-fs-p fs))
   (and (equal (l5-regular-file-user-read (l5-stat hns fs disk1))
               (l5-regular-file-user-read (l5-stat hns fs disk2)))
        (equal (l5-regular-file-user-write (l5-stat hns fs disk1))
               (l5-regular-file-user-write (l5-stat hns fs disk2)))
        (equal (l5-regular-file-other-read (l5-stat hns fs disk1))
               (l5-regular-file-other-read (l5-stat hns fs disk2)))
        (equal (l5-regular-file-other-write (l5-stat hns fs disk1))
               (l5-regular-file-other-write (l5-stat hns fs disk2)))
        (equal (l5-regular-file-user (l5-stat hns fs disk1))
               (l5-regular-file-user (l5-stat hns fs disk2))))))

(encapsulate
  ()

  (local
   (defun
       induction-scheme (hns1 hns2 fs)
     (if
         (atom hns1)
         fs
       (if
           (atom fs)
           nil
         (let
             ((sd (assoc (car hns2) fs)))
           (if
               (atom sd)
               fs
             (if
                 (atom hns2)
                 fs
               (if (not (equal (car hns1) (car hns2)))
                   fs
                 (let ((contents (cdr sd)))
                   (if (atom (cdr hns1))
                       (cons (cons (car sd) contents)
                             (remove1-assoc (car hns2) fs))
                     (cons (cons (car sd)
                                 (induction-scheme (cdr hns1)
                                                   (cdr hns2)
                                                   contents))
                           (remove1-assoc (car hns2) fs))))))))))))

  (defthm
    l5-read-after-write-2-lemma-5
    (implies
     (and (l4-stricter-fs-p (l5-to-l4-fs fs) alv)
          (l5-fs-p fs)
          (natp user)
          (stringp text2)
          (natp start2)
          (symbol-listp hns1)
          (symbol-listp hns2)
          (not (equal hns1 hns2))
          (natp n2)
          (block-listp disk)
          (boolean-listp alv)
          (equal (len alv) (len disk))
          (<= (len (make-blocks (insert-text nil start2 text2)))
              (count-free-blocks alv)))
     (equal
      (l5-regular-file-entry-p
       (l5-stat hns1
                (mv-nth 0
                        (l5-wrchs hns2 fs disk alv start2 text2 user))
                (mv-nth 1
                        (l5-wrchs hns2 fs disk alv start2 text2 user))))
      (l5-regular-file-entry-p (l5-stat hns1 fs disk))))
    :hints (("goal" :induct (induction-scheme hns1 hns2 fs))))

  (defthm
    l5-read-after-write-2-lemma-7
    (implies
     (and (l4-stricter-fs-p (l5-to-l4-fs fs) alv)
          (l5-fs-p fs)
          (natp user)
          (stringp text2)
          (natp start2)
          (symbol-listp hns1)
          (symbol-listp hns2)
          (not (equal hns1 hns2))
          (natp n2)
          (block-listp disk)
          (boolean-listp alv)
          (equal (len alv) (len disk))
          (<= (len (make-blocks (insert-text nil start2 text2)))
              (count-free-blocks alv)))
     (let
         ((file (l5-stat hns1 fs disk))
          (new-file
           (l5-stat hns1
                    (mv-nth 0
                            (l5-wrchs hns2 fs disk alv start2 text2 user))
                    (mv-nth 1
                            (l5-wrchs hns2 fs disk alv start2 text2 user)))))
       (implies (l5-regular-file-entry-p file)
                (and (equal (l5-regular-file-user new-file)
                            (l5-regular-file-user file))
                     (equal (l5-regular-file-user-read new-file)
                            (l5-regular-file-user-read file))
                     (equal (l5-regular-file-user-write new-file)
                            (l5-regular-file-user-write file))
                     (equal (l5-regular-file-other-read new-file)
                            (l5-regular-file-other-read file))
                     (equal (l5-regular-file-other-write new-file)
                            (l5-regular-file-other-write file))))))
    :hints
    (("goal"
      :induct (induction-scheme hns1 hns2 fs))
     ("subgoal *1/5"
      :expand ((l5-wrchs hns2 fs disk alv start2 text2 user)
               (l5-stat hns1 fs disk))
      :use
      ((:instance l5-read-after-write-2-lemma-6
                  (hns (cdr hns1))
                  (fs (cdr (assoc-equal (car hns1) fs)))
                  (disk1 (mv-nth 1
                                 (l5-wrchs (cdr hns2)
                                           (cdr (assoc-equal (car hns2) fs))
                                           disk alv start2 text2 user)))
                  (disk2 disk))
       (:instance
        l5-read-after-write-2-lemma-6
        (hns (cdr hns1))
        (fs (cdr (assoc-equal (car hns1) fs)))
        (disk1
         (set-indices
          disk
          (find-n-free-blocks
           (set-indices-in-alv
            alv
            (l5-regular-file-contents (cdr (assoc-equal (car hns2) fs)))
            nil)
           (len
            (make-blocks
             (insert-text
              (unmake-blocks
               (fetch-blocks-by-indices
                disk
                (l5-regular-file-contents (cdr (assoc-equal (car hns2) fs))))
               (l5-regular-file-length (cdr (assoc-equal (car hns2) fs))))
              start2 text2))))
          (make-blocks
           (insert-text
            (unmake-blocks
             (fetch-blocks-by-indices
              disk
              (l5-regular-file-contents (cdr (assoc-equal (car hns2) fs))))
             (l5-regular-file-length (cdr (assoc-equal (car hns2) fs))))
            start2 text2))))
        (disk2 disk))))))

  (defthm
    l5-read-after-write-2-lemma-8
    (implies
     (and (l4-stricter-fs-p (l5-to-l4-fs fs) alv)
          (l5-fs-p fs)
          (natp user1)
          (natp user2)
          (stringp text1)
          (stringp text2)
          (integerp start1)
          (<= 0 start1)
          (integerp start2)
          (<= 0 start2)
          (symbol-listp hns1)
          (symbol-listp hns2)
          (not (equal hns1 hns2))
          (integerp n1)
          (<= 0 n1)
          (integerp n2)
          (<= 0 n2)
          (block-listp disk)
          (boolean-listp alv)
          (equal (len alv) (len disk))
          (<= (len (make-blocks (insert-text nil start2 text2)))
              (count-free-blocks alv))
          (l5-regular-file-entry-p (l5-stat hns1 fs disk))
          (l5-regular-file-readable-p (l5-stat hns1 fs disk)
                                      user1)
          (l5-regular-file-writable-p (l5-stat hns2 fs disk)
                                      user2))
     (l5-regular-file-readable-p
      (l5-stat hns1
               (mv-nth 0
                       (l5-wrchs hns2 fs disk alv start2 text2 user2))
               (mv-nth 1
                       (l5-wrchs hns2 fs disk alv start2 text2 user2)))
      user1))
    :hints (("goal" :in-theory (enable l5-regular-file-readable-p)
             :induct (induction-scheme hns1 hns2 fs))))
  )

(defthm
  l5-read-after-write-2
  (implies (and (l4-stricter-fs-p (l5-to-l4-fs fs) alv)
                (l5-fs-p fs)
                (natp user1)
                (natp user2)
                (stringp text1)
                (stringp text2)
                (natp start1)
                (natp start2)
                (symbol-listp hns1)
                (symbol-listp hns2)
                (not (equal hns1 hns2))
                (integerp n1)
                (<= 0 n1)
                (integerp n2)
                (<= 0 n2)
                (block-listp disk)
                (boolean-listp alv)
                (equal (len alv) (len disk))
                (<= (len (make-blocks (insert-text nil start2 text2)))
                    (count-free-blocks alv))
                (l5-regular-file-entry-p (l5-stat hns1 fs disk))
                (l5-regular-file-readable-p (l5-stat hns1 fs disk)
                                            user1)
                (l5-regular-file-writable-p (l5-stat hns2 fs disk)
                                            user2))
           (mv-let (new-fs new-disk new-alv)
             (l5-wrchs hns2 fs disk alv start2 text2 user2)
             (declare (ignore new-alv))
             (equal (l5-rdchs hns1 new-fs new-disk start1 n1 user1)
                    (l5-rdchs hns1 fs disk start1 n1 user1))))
  :hints
  (("goal"
    :in-theory (disable l5-rdchs-correctness-1
                        l5-wrchs-correctness-1
                        l4-read-after-write-2
                        (:DEFINITION L5-WRCHS)
                        (:DEFINITION NTH)
                        (:DEFINITION UNMAKE-BLOCKS)
                        (:DEFINITION MAKE-BLOCKS)
                        (:DEFINITION TRUE-LISTP)
                        (:TYPE-PRESCRIPTION L3-REGULAR-FILE-ENTRY-P)
                        (:DEFINITION L4-WRCHS)
                        (:DEFINITION L5-STAT)
                        (:DEFINITION L2-FS-P)
                        (:REWRITE DEFAULT-CDR)
                        (:REWRITE
                         L5-REGULAR-FILE-ENTRY-P-CORRECTNESS-3 . 2)
                        (:REWRITE DEFAULT-CAR)
                        (:REWRITE DEFAULT-+-2)
                        (:DEFINITION L3-STAT)
                        (:REWRITE DEFAULT-+-1)
                        (:REWRITE L5-STAT-CORRECTNESS-2 . 1)
                        (:TYPE-PRESCRIPTION L2-FS-P)
                        (:REWRITE ZP-OPEN)
                        (:DEFINITION L3-FS-P)
                        (:REWRITE FIND-N-FREE-BLOCKS-CORRECTNESS-2)
                        (:DEFINITION ASSOC-EQUAL)
                        (:DEFINITION CHARACTER-LISTP)
                        (:DEFINITION FETCH-BLOCKS-BY-INDICES)
                        (:REWRITE DEFAULT-COERCE-1)
                        (:DEFINITION L5-TO-L4-FS)
                        (:TYPE-PRESCRIPTION FETCH-BLOCKS-BY-INDICES)
                        (:TYPE-PRESCRIPTION L3-FS-P)
                        (:REWRITE L5-FS-P-ASSOC)
                        (:REWRITE UNMAKE-MAKE-BLOCKS-LEMMA-1)
                        (:REWRITE
                         L3-REGULAR-FILE-ENTRY-P-CORRECTNESS-1)
                        (:DEFINITION BOOLEAN-LISTP)
                        (:TYPE-PRESCRIPTION MAKE-BLOCKS)
                        (:REWRITE L5-WRCHS-CORRECTNESS-1-LEMMA-1)
                        (:REWRITE L5-STAT-CORRECTNESS-2-LEMMA-1)
                        (:DEFINITION MAKE-CHARACTER-LIST)
                        (:DEFINITION SET-INDICES)
                        (:REWRITE DEFAULT-<-2)
                        (:REWRITE DEFAULT-<-1)
                        (:REWRITE L2-FSCK-AFTER-L2-WRCHS-LEMMA-5)
                        (:REWRITE L5-WRCHS-CORRECTNESS-1-LEMMA-7)
                        (:REWRITE L5-STAT-CORRECTNESS-1-LEMMA-4)
                        (:REWRITE L2-CREATE-CORRECTNESS-1-LEMMA-2)
                        (:REWRITE L5-STAT-CORRECTNESS-1-LEMMA-3)
                        (:REWRITE L4-WRCHS-CORRECTNESS-1-LEMMA-18)
                        (:TYPE-PRESCRIPTION TRUE-LISTP)
                        (:REWRITE L5-WRCHS-CORRECTNESS-1-LEMMA-6)
                        (:REWRITE INSERT-TEXT-CORRECTNESS-1)
                        (:DEFINITION INDICES-MARKED-P)
                        (:DEFINITION UPDATE-NTH)
                        (:DEFINITION COUNT-FREE-BLOCKS)
                        (:REWRITE FOLD-CONSTS-IN-+)
                        (:DEFINITION BINARY-APPEND)
                        (:DEFINITION NTHCDR)
                        (:TYPE-PRESCRIPTION INDICES-MARKED-P)
                        (:REWRITE
                         L3-REGULAR-FILE-ENTRY-P-CORRECTNESS-3 . 2)
                        (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)
                        (:REWRITE DEFAULT-COERCE-3)
                        (:REWRITE L2-READ-AFTER-WRITE-1-LEMMA-1)
                        (:REWRITE DEFAULT-COERCE-2)
                        (:REWRITE L2-WRCHS-RETURNS-FS-LEMMA-4)
                        (:REWRITE SET-INDICES-IN-ALV-CORRECTNESS-1)
                        (:REWRITE L3-FS-P-ASSOC)
                        (:REWRITE MAKE-BLOCKS-CORRECTNESS-4)
                        (:TYPE-PRESCRIPTION SET-INDICES-IN-ALV)
                        (:TYPE-PRESCRIPTION
                         SET-INDICES-IN-ALV-CORRECTNESS-1)
                        (:REWRITE L4-WRCHS-RETURNS-FS)
                        (:TYPE-PRESCRIPTION NATP)
                        (:REWRITE L5-STAT-CORRECTNESS-1-LEMMA-2)
                        (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV)
                        (:REWRITE L5-TO-L4-FS-CORRECTNESS-1 . 1)
                        (:REWRITE
                         L5-REGULAR-FILE-ENTRY-P-CORRECTNESS-3 . 1)
                        (:REWRITE DEFAULT-UNARY-MINUS)
                        (:TYPE-PRESCRIPTION
                         TRUE-LISTP-SUBSEQ-TYPE-PRESCRIPTION)
                        )
    :use
    ((:instance
      l5-rdchs-correctness-1 (hns hns1)
      (fs (mv-nth 0
                  (l5-wrchs hns2 fs disk alv start2 text2 user2)))
      (disk (mv-nth 1
                    (l5-wrchs hns2 fs disk alv start2 text2 user2)))
      (start start1)
      (n n1)
      (user user1))
     (:instance l5-rdchs-correctness-1 (hns hns1)
                (start start1)
                (n n1)
                (user user1))
     (:instance l5-wrchs-correctness-1 (hns hns2)
                (text text2)
                (start start2)
                (user user2))
     (:instance l4-read-after-write-2
                (fs (l5-to-l4-fs fs)))))))
