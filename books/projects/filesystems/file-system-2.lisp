(in-package "ACL2")

;  file-system-2.lisp                                  Mihir Mehta

; Here we define the rudiments of a file system with length tracking.  We first
; start with a file-system recognizer, and then we define various file-system
; operations.

; The important functions are l2-to-l1-fs, l2-stat, l2-rdchs and
; l2-wrchs. Each of them is preceded by an explanatory comment. Equivalence
; theorems are stated and proved between each of these and the corresponding
; function in file-system-1.lisp. Moreover, the theorems l2-read-after-write-1
; and l2-read-after-write-2 prove two important properties of l2-rdchs and
; l2-wrchs anew, although they were proved in file-system-1 for the filesystem
; described therein.

(include-book "std/testing/assert" :dir :system)
(include-book "file-system-1")

; This function defines a valid filesystem. It's an alist where all the cars
; are symbols and all the cdrs are either further filesystems or files,
; separated into text (a string) and metadata (currently, only file length).
(defun l2-fs-p (fs)
  (declare (xargs :guard t))
  (if (atom fs)
      (null fs)
    (and (let ((directory-or-file-entry (car fs)))
           (if (atom directory-or-file-entry)
               nil
             (let ((name (car directory-or-file-entry))
                   (entry (cdr directory-or-file-entry)))
               (and (symbolp name)
                    (or (and (consp entry) (stringp (car entry)) (natp (cdr entry)))
                        (l2-fs-p entry))))))
         (l2-fs-p (cdr fs)))))

;; This function transforms an instance of l2 into an equivalent instance of l1.
(defun l2-to-l1-fs (fs)
  (declare (xargs :guard (l2-fs-p fs)))
  (if (atom fs)
      fs
    (cons (let* ((directory-or-file-entry (car fs))
                 (name (car directory-or-file-entry))
                 (entry (cdr directory-or-file-entry)))
            (cons name
                (if (and (consp entry) (stringp (car entry)))
                    (car entry)
                  (l2-to-l1-fs entry))))
          (l2-to-l1-fs (cdr fs)))))

;; This theorem shows the type-correctness of l2-to-l1-fs.
(defthm l2-to-l1-fs-correctness-1
  (implies (l2-fs-p fs)
           (l1-fs-p (l2-to-l1-fs fs))))

(defthm alistp-l2-fs-p
  (implies (l2-fs-p fs)
           (alistp fs)))

(defthm l2-fs-p-assoc
  (implies (and (l2-fs-p fs)
                (consp (assoc-equal name fs))
                (consp (cddr (assoc-equal name fs))))
           (l2-fs-p (cdr (assoc-equal name fs)))))

;; This function allows a file or directory to be found in a filesystem given a path.
(defun l2-stat (hns fs)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l2-fs-p fs))))
  (if (atom hns)
      fs
    (if (atom fs)
        nil
      (let ((sd (assoc (car hns) fs)))
        (if (atom sd)
            nil
          (let ((contents (cdr sd)))
            (if (stringp (car contents))
                (and (null (cdr hns))
                     (car contents))
              (l2-stat (cdr hns) contents))))))))

(defthm l2-stat-correctness-1-lemma-1
  (implies (and (l2-fs-p fs))
           (iff (consp (assoc-equal name (l2-to-l1-fs fs)))
                (consp (assoc-equal name fs)))))

(defthm l2-stat-correctness-1-lemma-2
  (implies (and (l2-fs-p fs)
                (consp (assoc-equal name fs))
                (consp (cdr (assoc-equal name fs)))
                (stringp (car (cdr (assoc-equal name fs)))))
           (equal (cdr (assoc-equal name (l2-to-l1-fs fs)))
                  (car (cdr (assoc-equal name fs))))))

(defthm l2-stat-correctness-1-lemma-3
  (implies (and (l2-fs-p fs)
                (consp (assoc-equal name fs))
                (not (and (consp (cdr (assoc-equal name fs)))
                          (stringp (car (cdr (assoc-equal name fs)))))))
           (equal (cdr (assoc-equal name (l2-to-l1-fs fs)))
                  (l2-to-l1-fs (cdr (assoc-equal name fs))))))

(defthm l2-stat-correctness-1-lemma-4
  (implies (and (l2-fs-p fs) (stringp (cadr (assoc-equal name fs))))
           (equal (cdr (assoc-equal name (l2-to-l1-fs fs)))
                  (cadr (assoc-equal name fs)))))

(defthm l2-stat-correctness-1-lemma-5
  (implies (and (consp (assoc-equal name fs))
                (not (stringp (cadr (assoc-equal name fs))))
                (l2-fs-p fs))
           (l2-fs-p (cdr (assoc-equal name fs)))))

;; This is the first of two theorems showing the equivalence of the l2 and l1
;; versions of stat.
(defthm
  l2-stat-correctness-1
  (implies (and (l2-fs-p fs)
                (stringp (l2-stat hns fs)))
           (equal (l1-stat hns (l2-to-l1-fs fs))
                  (l2-stat hns fs)))
  :hints
  (("subgoal *1/5.2'"
    :in-theory (disable l2-to-l1-fs-correctness-1)
    :use (:instance l2-to-l1-fs-correctness-1
                    (fs (cdr (assoc-equal (car hns) fs)))))))

(defthm l2-stat-correctness-2-lemma-1
  (implies (and (l2-fs-p fs) (consp (assoc-equal name fs)))
           (implies (not (stringp (cadr (assoc-equal name fs))))
                    (not (stringp (cdr (assoc-equal name (l2-to-l1-fs fs))))))))

(defthm l2-stat-correctness-2-lemma-2
  (implies (not (stringp fs))
           (not (stringp (l2-to-l1-fs fs)))))

;; This is the second of two theorems showing the equivalence of the l2 and l1
;; versions of stat.
(defthm l2-stat-correctness-2
  (implies (and (l2-fs-p fs)
                (l2-fs-p (l2-stat hns fs)))
           (equal (l1-stat hns (l2-to-l1-fs fs))
                  (l2-to-l1-fs (l2-stat hns fs)))))

;; This is simply a useful property of stat.
(defthm l2-stat-of-stat
  (implies (and (symbol-listp inside)
                (symbol-listp outside)
                (l2-stat outside fs)
                (l2-fs-p fs))
           (equal (l2-stat inside (l2-stat outside fs))
                  (l2-stat (append outside inside) fs)))
  :hints
  (("Goal"
    :induct (l2-stat outside fs))))

;; This function finds a text file given its path and reads a segment of
;; that text file.
(defun l2-rdchs (hns fs start n)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l2-fs-p fs)
                              (natp start)
                              (natp n))))
  (let ((file (l2-stat hns fs)))
    (if (not (stringp file))
        nil
      (let ((file-length (length file))
            (end (+ start n)))
        (if (< file-length end)
            nil
          (subseq file start (+ start n)))))))

(defthm l2-rdchs-correctness-1-lemma-1
  (implies (and (l2-fs-p fs)
                (symbol-listp hns)
                (not (stringp (l2-stat hns fs))))
           (not (stringp (l1-stat hns (l2-to-l1-fs fs))))))

(defthm l2-rdchs-correctness-1-lemma-2
  (implies (l2-fs-p fs)
           (not (stringp (l2-to-l1-fs fs)))))

;; This theorem proves the equivalence of the l2 and l1 versions of rdchs.
(defthm l2-rdchs-correctness-1
  (implies (and (symbol-listp hns)
                (l2-fs-p fs)
                (natp start)
                (natp n))
           (equal (l1-rdchs hns (l2-to-l1-fs fs) start n)
                  (l2-rdchs hns fs start n))))

; This function deletes a file or directory given its path.
(defun l2-unlink (hns fs)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l2-fs-p fs))))
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
              (if (stringp (car contents))
                  fs ;; we still have names but we're at a regular file - error
                (cons (cons (car sd)
                            (l2-unlink (cdr hns) contents))
                      (remove1-assoc (car hns) fs))))))))
    ))

; This function writes a specified text string to a specified position to a
; text file at a specified path.
(defun l2-wrchs (hns fs start text)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l2-fs-p fs)
                              (natp start)
                              (stringp text))
                  :guard-hints
                  (("Subgoal 1.4" :use (:instance character-listp-coerce (str ()))) )))
  (if (atom hns)
      fs ;; error - showed up at fs with no name  - so leave fs unchanged
    (if (atom fs)
        nil ;; error, so leave fs unchanged
      (let ((sd (assoc (car hns) fs)))
        (if (atom sd)
            fs ;; file-not-found error, so leave fs unchanged
          (let ((contents (cdr sd)))
            (cons (cons (car sd)
                        (if (and (consp (cdr sd)) (stringp (cadr sd)))
                            (let ((file (cdr sd)))
                              (if (consp (cdr hns))
                                  file ;; error, so leave fs unchanged
                                (let* ((oldtext (coerce (car file) 'list))
                                       (newtext
                                        (insert-text oldtext start text))
                                       (newlength (len newtext)))
                                  (cons
                                   (coerce newtext 'string)
                                   newlength))))
                          (l2-wrchs (cdr hns) contents start text)))
                  (remove1-assoc (car hns) fs))))))))

(defthm l2-wrchs-returns-fs-lemma-1
  (implies (and (consp (assoc-equal s fs))
                (l2-fs-p fs))
           (symbolp (car (assoc-equal s fs)))))

(defthm l2-wrchs-returns-fs-lemma-2
  (implies (l2-fs-p fs)
           (l2-fs-p (remove1-assoc-equal s fs))))

(defthm l2-wrchs-returns-fs-lemma-3
  (implies (and (consp fs) (l2-fs-p fs)
                (consp (assoc-equal s fs))
                (not (stringp (cadr (assoc-equal s fs)))))
           (l2-fs-p (cdr (assoc-equal s fs)))))

(defthmd l2-wrchs-returns-fs-lemma-4
  (implies (and (consp (assoc-equal name fs))
                (l2-fs-p fs)
                (consp (cdr (assoc-equal name fs)))
                (stringp (cadr (assoc-equal name fs))))
           (and (integerp (cddr (assoc-equal name fs)))
                (<= 0 (cddr (assoc-equal name fs))))))

(defthm l2-wrchs-returns-fs-lemma-5
  (implies (and (consp (assoc-equal name fs))
                (l2-fs-p fs))
           (symbolp name))
  :rule-classes :forward-chaining)

;; This theorem shows that the property l2-fs-p is preserved by wrchs.
(defthm
  l2-wrchs-returns-fs
  (implies (l2-fs-p fs)
           (l2-fs-p (l2-wrchs hns fs start text)))
  :hints (("goal" :in-theory (enable l2-wrchs-returns-fs-lemma-4))))

;; This theorem shows that the property l2-fs-p is preserved by unlink.
(defthm l2-unlink-returns-fs
  (implies (and (l2-fs-p fs))
           (l2-fs-p (l2-unlink hns fs))))

(defthm l2-wrchs-correctness-1-lemma-1
  (implies (l2-fs-p fs)
           (equal (remove1-assoc-equal name (l2-to-l1-fs fs))
                  (l2-to-l1-fs (remove1-assoc-equal name fs)))))

(defthm l2-wrchs-correctness-1-lemma-2
  (implies (and (consp fs)
                (l2-fs-p fs))
           (consp (l2-to-l1-fs fs))))

;; This theorem shows the equivalence of the l2 and l1 versions of wrchs.
(defthm
  l2-wrchs-correctness-1
  (implies (l2-fs-p fs)
           (equal (l1-wrchs hns (l2-to-l1-fs fs)
                            start text)
                  (l2-to-l1-fs (l2-wrchs hns fs start text))))
  :hints
  (("subgoal *1/5.1''"
    :in-theory (disable l2-wrchs-returns-fs)
    :use (:instance l2-wrchs-returns-fs (hns (cdr hns))
                    (fs (cdr (assoc-equal (car hns) fs)))))))

;; This function creates a text file (and all necessary subdirectories) given a
;; path and some initial text.
(defun l2-create (hns fs text)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l2-fs-p fs)
                              (stringp text))))
  (if (atom hns)
      fs ;; error - showed up at fs with no name  - so leave fs unchanged
    (let ((sd (assoc (car hns) fs)))
      (if (atom sd)
          (cons
           (cons
            (car hns)
            (if (atom (cdr hns))
                (cons text (length text))
              (l2-create (cdr hns) nil text)))
           fs)
        (let ((contents (cdr sd)))
          (cons (cons (car sd)
                      (if (and (consp (cdr sd)) (stringp (cadr sd)))
                          contents ;; file already exists, so leave fs unchanged
                        (l2-create (cdr hns) contents text)))
                (remove1-assoc (car hns) fs))
          )))))

;; This theorem shows that the property l2-fs-p is preserved by create.
(defthm
  l2-create-returns-fs
  (implies (and (symbol-listp hns)
                (l2-fs-p fs)
                (stringp text))
           (l2-fs-p (l2-create hns fs text)))
  :hints (("goal" :in-theory (enable l2-wrchs-returns-fs-lemma-4))))

(defthm l2-create-correctness-1-lemma-1
  (implies (and (not (consp (cdr (assoc-equal name fs))))
                (consp (assoc-equal name fs))
                (l2-fs-p fs))
           (not (cdr (assoc-equal name fs))))
  :rule-classes (:forward-chaining))

(defthm l2-create-correctness-1-lemma-2
  (implies (l2-fs-p fs)
           (not (stringp (car fs)))))

;; This theorem shows the equivalence of the l2 and l1 versions of create.
(defthm l2-create-correctness-1
  (implies (and (symbol-listp hns)
                (l2-fs-p fs)
                (stringp text))
           (equal (l1-create hns (l2-to-l1-fs fs) text)
                  (l2-to-l1-fs (l2-create hns fs text)))))

(defthm l2-read-after-write-1-lemma-1
  (implies (consp (assoc-equal name alist))
           (equal (car (assoc-equal name alist)) name)))

(defthm l2-read-after-write-1-lemma-3
  (implies (l2-rdchs hns fs start n)
           (stringp (l2-stat hns fs))))

(defthm l2-read-after-write-1-lemma-4
  (implies (and (l2-fs-p fs)
                (stringp text)
                (symbol-listp hns)
                (natp start)
                (stringp (l2-stat hns fs)))
           (<= (+ start (len (coerce text 'list)))
               (len (coerce (l2-stat hns (l2-wrchs hns fs start text))
                            'list)))))

(defthm l2-read-after-write-2-lemma-1
  (implies (l2-fs-p fs)
           (not (stringp (cdr (assoc-equal name fs))))))

(defthm l2-read-after-write-2-lemma-2
  (implies (and (consp hns1)
                (consp fs)
                (consp (assoc-equal (car hns1) fs))
                (l2-fs-p fs)
                (symbolp (car hns1))
                (not (cdr hns1))
                (stringp (l2-stat hns1 fs)))
           (equal (l2-stat hns1 fs) (cadr (assoc (car hns1) fs)))))

(defthm l2-read-after-write-2-lemma-3
  (implies (and (not (stringp (l2-stat hns fs)))
                (l2-fs-p fs))
           (l2-fs-p (l2-stat hns fs))))

(defthm
  l2-read-after-write-2-lemma-4
  (implies
   (l2-fs-p fs)
   (equal
    (stringp (l2-stat hns1 (l2-wrchs hns2 fs start2 text2)))
    (stringp (l2-stat hns1 fs))))
  :hints
  (("goal"
    :in-theory (disable l1-read-after-write-2-lemma-3
                        l2-stat-correctness-1)
    :use ((:instance l1-read-after-write-2-lemma-3
                     (fs (l2-to-l1-fs fs)))
          (:instance l2-stat-correctness-1 (hns hns1)
                     (fs (l2-wrchs hns2 fs start2 text2)))
          (:instance l2-stat-correctness-1 (hns hns1))))))

(defthm
  l2-stat-after-write
  (implies
   (and (l2-fs-p fs)
        (stringp text2)
        (symbol-listp hns1)
        (symbol-listp hns2)
        (natp start2)
        (stringp (l2-stat hns1 fs)))
   (equal
    (l2-stat hns1 (l2-wrchs hns2 fs start2 text2))
    (if (equal hns1 hns2)
        (coerce (insert-text (coerce (l2-stat hns1 fs) 'list)
                             start2 text2)
                'string)
        (l2-stat hns1 fs))))
  :hints
  (("goal"
    :in-theory (disable l2-stat-correctness-1
                        l1-stat-after-write)
    :use ((:instance l2-stat-correctness-1 (hns hns1))
          (:instance l2-stat-correctness-1 (hns hns1)
                     (fs (l2-wrchs hns2 fs start2 text2)))
          (:instance l1-stat-after-write
                     (fs (l2-to-l1-fs fs)))))))

(defthm l2-read-after-write-1
  (implies (and (l2-fs-p fs)
                (stringp text)
                (symbol-listp hns)
                (natp start)
                (equal n (length text))
                (stringp (l2-stat hns fs)))
           (equal (l2-rdchs hns (l2-wrchs hns fs start text) start n) text)))

(defthm
  l2-read-after-write-2
  (implies (and (l2-fs-p fs)
                (stringp text2)
                (symbol-listp hns1)
                (symbol-listp hns2)
                (not (equal hns1 hns2))
                (natp start1)
                (natp start2)
                (natp n1))
           (equal (l2-rdchs hns1 (l2-wrchs hns2 fs start2 text2)
                            start1 n1)
                  (l2-rdchs hns1 fs start1 n1))))

;; This proves the equivalent of the first read-after-write property for
;; create.
(defthm l2-read-after-create-1
  (implies (and (l2-fs-p fs)
                (stringp text)
                (symbol-listp hns)
                (equal n (length text))
                (not (l2-stat hns fs))
                (stringp (l2-stat hns (l2-create hns fs text))))
           (equal (l2-rdchs hns (l2-create hns fs text) 0 n) text)))

;; This proves the equivalent of the second read-after-write property for
;; create.
(defthm l2-read-after-create-2
  (implies (and (l2-fs-p fs)
                (stringp text2)
                (symbol-listp hns1)
                (symbol-listp hns2)
                (not (equal hns1 hns2))
                (natp start1)
                (natp n1)
                (not (l2-stat hns2 fs))
                (stringp (l2-stat hns2 (l2-create hns2 fs text2)))
                (stringp (l2-stat hns1 fs)))
           (equal (l2-rdchs hns1 (l2-create hns2 fs text2)
                            start1 n1)
                  (l2-rdchs hns1 fs start1 n1)))
  :hints (("Goal" :use ((:instance
                         l2-create-correctness-1 (hns hns2)
                         (text text2))
                        (:instance
                         l2-rdchs-correctness-1 (hns hns1)
                         (start start1)
                         (n n1))
                        (:instance
                         l2-rdchs-correctness-1 (hns hns1)
                         (start start1)
                         (n n1))
                        (:instance
                         l2-rdchs-correctness-1 (hns hns1)
                         (fs (l2-create hns2 fs text2))
                         (start start1)
                         (n n1))
                        (:instance
                         l2-create-returns-fs (hns hns2)
                         (text text2))
                        (:instance l1-read-after-create-2
                                   (fs (l2-to-l1-fs fs)))))))

;; This function checks that the file lengths associated with text files are
;; accurate.
(defun l2-fsck (fs)
  (declare (xargs :guard (l2-fs-p fs)))
  (or (atom fs)
    (and (let ((directory-or-file-entry (car fs)))
           (let ((entry (cdr directory-or-file-entry)))
             (if (and (consp entry) (stringp (car entry)))
                 (equal (length (car entry)) (cdr entry))
               (l2-fsck entry))))
         (l2-fsck (cdr fs)))))

(defthm l2-fsck-after-l2-wrchs-lemma-1
  (implies (and (l2-fs-p fs) (l2-fsck fs))
           (l2-fsck (remove1-assoc-equal name fs))))

(defthm l2-fsck-after-l2-wrchs-lemma-2
  (implies (and (l2-fs-p fs) (l2-fsck fs))
           (l2-fsck (cdr (assoc-equal (car hns) fs)))))

(defthm l2-fsck-after-l2-wrchs-lemma-4
  (implies (and (consp fs)
                (consp (assoc-equal name fs))
                (l2-fs-p fs)
                (stringp text)
                (l2-fsck fs)
                (consp (cdr (assoc-equal name fs)))
                (stringp (cadr (assoc-equal name fs))))
           (equal (len (coerce (cadr (assoc-equal name fs))
                               'list))
                  (cddr (assoc-equal name fs))))
)

(encapsulate ()
  (local (include-book "std/strings/coerce" :dir :system))

  (defthm l2-fsck-after-l2-wrchs-lemma-5
    (implies (character-listp cl)
             (equal (coerce (coerce cl 'string) 'list)
                    cl)))

  )

;; This theorem shows that l2-fsck is preserved by l2-wrchs
(defthm l2-fsck-after-l2-wrchs
  (implies (and (l2-fs-p fs) (natp start) (stringp text) (l2-fsck fs))
           (l2-fsck (l2-wrchs hns fs start text))))

;; This theorem shows that l2-fsck is preserved by l2-unlink
(defthm l2-fsck-after-l2-unlink
  (implies (and (l2-fs-p fs) (l2-fsck fs))
           (l2-fsck (l2-unlink hns fs))))

; This function finds the length of the text file at a specified path
(defun l2-wc-len (hns fs)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l2-fs-p fs))))
  (let ((file (l2-stat hns fs)))
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
