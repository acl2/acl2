(in-package "ACL2")

;  file-system-1.lisp                                  Mihir Mehta

; Here we define the rudiments of a file system.  We first start with
; a file-system recognizer, and then we define various file-system
; operations.

(include-book "std/testing/assert" :dir :system)
(include-book "file-system-lemmas")
(include-book "insert-text")

(defun l1-fs-p (fs)
  (declare (xargs :guard t))
  (if (atom fs)
      (null fs)
    (and (let ((directory-or-file-entry (car fs)))
           (if (atom directory-or-file-entry)
               nil
             (let ((name (car directory-or-file-entry))
                   (entry (cdr directory-or-file-entry)))
               (and (symbolp name)
                    (or (stringp entry) (l1-fs-p entry))))))
         (l1-fs-p (cdr fs)))))

(defthm alistp-l1-fs-p
  (implies (l1-fs-p fs)
           (alistp fs)))

(defthm l1-fs-p-assoc
  (implies (and (l1-fs-p fs)
                (consp (assoc-equal name fs))
                (consp (cdr (assoc-equal name fs))))
           (l1-fs-p (cdr (assoc-equal name fs)))))

(defun l1-stat (hns fs)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l1-fs-p fs))))
  (if (atom hns)
      fs
    (if (atom fs)
        nil
      (let ((sd (assoc (car hns) fs)))
        (if (atom sd)
            nil
          (let ((contents (cdr sd)))
            (if (stringp contents)
                (and (null (cdr hns))
                     contents)
              (l1-stat (cdr hns) contents))))))))

(defthm l1-stat-of-l1-stat-lemma-1
  (implies (and (l1-fs-p fs)
                (consp (assoc-equal name fs))
                (not (stringp (cdr (assoc-equal name fs)))))
           (l1-fs-p (cdr (assoc-equal name fs)))))

(defthm l1-stat-of-l1-stat
  (implies (and (symbol-listp inside)
                (symbol-listp outside)
                (l1-stat outside fs)
                (l1-fs-p fs))
           (equal (l1-stat inside (l1-stat outside fs))
                  (l1-stat (append outside inside) fs)))
  :hints
  (("Goal"
    :induct (l1-stat outside fs))))

(defun l1-rdchs (hns fs start n)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l1-fs-p fs)
                              (natp start)
                              (natp n))))
  (let ((file (l1-stat hns fs)))
    (if (not (stringp file))
        nil
      (let ((file-length (length file))
            (end (+ start n)))
        (if (< file-length end)
            nil
          (subseq file start (+ start n)))))))

; Delete file
(defun
    l1-unlink (hns fs)
  (declare (xargs :guard (and (symbol-listp hns) (l1-fs-p fs))))
  (if
      (atom hns)
      fs ;;error case, basically
    (if
        (atom (cdr hns))
        (remove1-assoc (car hns) fs)
      (if
          (atom fs)
          nil
        (let
            ((sd (assoc (car hns) fs)))
          (if (atom sd)
              fs
            (let ((contents (cdr sd)))
              (if (atom contents)
                  (and (null (cdr hns)) contents)
                (cons (cons (car sd)
                            (l1-unlink (cdr hns) contents))
                      (remove1-assoc (car hns) fs))))))))))

; The problem with this definition of l1-wrchs is that it deletes a directory if
; it's found where a text file is expected
(defun
    l1-wrchs (hns fs start text)
  (declare (xargs :guard (and (symbol-listp hns)
                              (or (stringp fs) (l1-fs-p fs))
                              (natp start)
                              (stringp text))))
  (if
      (atom hns)
      (let ((file fs))
        (if (not (stringp file))
            file ;; error, so leave fs unchanged
          (coerce (insert-text (coerce file 'list)
                               start text)
                  'string)))
    (if (atom fs)
        fs ;; error, so leave fs unchanged
      (let ((sd (assoc (car hns) fs)))
        (if (atom sd)
            fs ;; error, so leave fs unchanged
          (let ((contents (cdr sd)))
            (cons (cons (car sd)
                        (l1-wrchs (cdr hns)
                                  contents start text))
                  (remove1-assoc (car hns) fs))))))))

(defthm l1-wrchs-returns-fs-lemma-1
  (implies (and (consp (assoc-equal s fs))
                (l1-fs-p fs))
           (symbolp (car (assoc-equal s fs)))))

(defthm l1-wrchs-returns-fs-lemma-2
  (implies (l1-fs-p fs)
           (l1-fs-p (remove1-assoc-equal s fs))))

(defthm
  l1-wrchs-returns-fs-lemma-3
  (implies (and (not (l1-fs-p (cdr (assoc-equal (car hns) fs))))
                (l1-fs-p fs)
                (not (stringp (l1-wrchs (cdr hns)
                                        (cdr (assoc-equal (car hns) fs))
                                        start text))))
           (l1-fs-p (l1-wrchs (cdr hns)
                              (cdr (assoc-equal (car hns) fs))
                              start text)))
  :hints (("goal" :in-theory (disable l1-wrchs-returns-fs-lemma-1)
           :use (:instance l1-wrchs-returns-fs-lemma-1
                           (s (car hns))))))

(defthm l1-wrchs-returns-fs
  (implies (l1-fs-p fs)
           (l1-fs-p (l1-wrchs hns fs start text))))

(defthm l1-unlink-returns-fs
  (implies (and (l1-fs-p fs))
           (l1-fs-p (l1-unlink hns fs))))

(defun l1-create (hns fs text)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l1-fs-p fs)
                              (stringp text))))
  (if (atom hns)
      fs ;; error - showed up at fs with no name  - so leave fs unchanged
    (let ((sd (assoc (car hns) fs)))
      (if (atom sd)
          (cons
           (cons
            (car hns)
            (if (atom (cdr hns))
                text
              (l1-create (cdr hns) nil text)))
           fs)
        (let ((contents (cdr sd)))
          (cons (cons (car sd)
                      (if (stringp (cdr sd))
                          contents ;; file already exists, so leave fs unchanged
                        (l1-create (cdr hns) contents text)))
                (remove1-assoc (car hns) fs))
          )))))

(defthm l1-create-returns-fs
  (implies (and (symbol-listp hns)
                (l1-fs-p fs)
                (stringp text))
           (l1-fs-p (l1-create hns fs text)))
  :rule-classes (:rewrite :type-prescription))

(defthm l1-read-after-write-1-lemma-1
  (implies (consp (assoc-equal name alist))
           (equal (car (assoc-equal name alist)) name)))

(defthm l1-read-after-write-1-lemma-2
  (implies (l1-fs-p fs)
           (equal (stringp (l1-stat hns (l1-wrchs hns fs start text)))
                  (stringp (l1-stat hns fs)))))

(defthm l1-read-after-write-2-lemma-1
  (implies (l1-fs-p fs)
           (not (stringp (assoc-equal name fs)))))

(defthm l1-read-after-write-2-lemma-2
  (implies (and (consp hns1)
                (consp fs)
                (consp (assoc-equal (car hns1) fs))
                (l1-fs-p fs)
                (symbolp (car hns1))
                (not (cdr hns1))
                (stringp (l1-stat hns1 fs)))
           (equal (l1-stat hns1 fs) (cdr (assoc (car hns1) fs)))))

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
    l1-read-after-write-2-lemma-3
    (implies
     (l1-fs-p fs)
     (equal
      (stringp (l1-stat hns1 (l1-wrchs hns2 fs start2 text2)))
      (stringp (l1-stat hns1 fs))))
    :hints (("goal" :induct (induction-scheme hns1 hns2 fs))))

  (defthm
    l1-stat-after-write
    (implies (and (l1-fs-p fs)
                  (stringp text2)
                  (symbol-listp hns1)
                  (symbol-listp hns2)
                  (natp start2)
                  (stringp (l1-stat hns1 fs)))
             (equal (l1-stat hns1 (l1-wrchs hns2 fs start2 text2))
                    (if (not (equal hns1 hns2))
                        (l1-stat hns1 fs)
                        (coerce (insert-text (coerce (l1-stat hns1 fs) 'list)
                                             start2 text2)
                                'string))))
    :hints (("goal" :induct (induction-scheme hns1 hns2 fs)))))

(defthm l1-read-after-write-1
  (implies (and (l1-fs-p fs)
                (stringp text)
                (symbol-listp hns)
                (natp start)
                (equal n (length text))
                (stringp (l1-stat hns fs)))
           (equal (l1-rdchs hns (l1-wrchs hns fs start text) start n) text)))

(defthm l1-read-after-write-2
  (implies (and (l1-fs-p fs)
                (stringp text2)
                (symbol-listp hns1)
                (symbol-listp hns2)
                (not (equal hns1 hns2))
                (natp start1)
                (natp start2)
                (natp n1))
           (equal (l1-rdchs hns1 (l1-wrchs hns2 fs start2 text2) start1 n1)
                  (l1-rdchs hns1 fs start1 n1))))

;; Induction argument for the proof of
;; (implies
;;  (and (l1-fs-p fs)
;;       (stringp text2)
;;       (symbol-listp hns1)
;;       (symbol-listp hns2)
;;       (not (equal hns1 hns2))
;;       (not (l1-stat hns2 fs))
;;       (stringp (l1-stat hns2 (l1-create hns2 fs text2)))
;;       (stringp (l1-stat hns1 fs)))
;;  (equal (l1-stat hns1 (l1-create hns2 fs text2)) (l1-stat hns1 fs)))
;; now, let's semi-formally write the cases we want.
;; case 1: (atom hns1) - this will violate the hypothesis
;; (stringp (l1-stat hns1 fs))
;; case 2: (and (consp hns1) (atom fs)) - this will violate the hypothesis
;; (stringp (l1-stat hns1 fs))
;; case 3: (and (consp hns1) (consp fs) (atom (assoc (car hns1) fs))) - this
;; will violate the hypothesis (stringp (l1-stat hns1 fs))
;; case 4: (and (consp hns1) (consp fs) (consp (assoc (car hns1) fs))
;;              (atom hns2)) - this will violate the hypothesis
;; (not (l1-stat hns2 fs))
;; case 5: (and (consp hns1) (consp fs) (consp (assoc (car hns1) fs))
;;              (consp hns2) (equal (car hns1) (car hns2))
;;              (stringp (cdr (assoc (car hns1) fs)))) - this will violate the
;; hypothesis (not (l1-stat hns2 fs))
;; case 6: (and (consp hns1) (consp fs) (consp (assoc (car hns1) fs))
;;              (consp hns2) (equal (car hns1) (car hns2))
;;              (not (stringp (cdr (assoc (car hns1) fs))))) - in this case,
;; (l1-stat hns1 (l1-create hns2 fs text2)) =
;; (l1-stat (cdr hns1) (cdr (assoc (car hns1) (l1-create hns2 fs text2)))) =
;; (l1-stat (cdr hns1) (l1-create (cdr hns2) (cdr (assoc (car hns1) fs)) text2)) =
;; (l1-stat (cdr hns1) (cdr (assoc (car hns1) fs))) = (induction hypothesis)
;; (l1-stat hns1 fs)
;; case 7: (and (consp hns1) (consp fs) (consp (assoc (car hns1) fs))
;;              (consp hns2) (not (equal (car hns1) (car hns2)))) - in this
;; case,
;; (l1-stat hns1 (l1-create hns2 fs text2)) =
;; (l1-stat (cdr hns1) (cdr (assoc (car hns1) fs))) =
;; (l1-stat hns1 fs)

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
             ((sd (assoc (car hns1) fs)))
           (if
               (atom sd)
               fs
             (if
                 (atom hns2)
                 fs
               (if (not (equal (car hns1) (car hns2)))
                   fs
                 (let ((contents (cdr sd)))
                   (if (stringp (cdr sd))
                       (cons (cons (car sd) contents)
                             (remove1-assoc (car hns2) fs))
                     (cons (cons (car sd)
                                 (induction-scheme (cdr hns1)
                                                   (cdr hns2)
                                                   contents))
                           (remove1-assoc (car hns2) fs))))))))))))

  (defthm
    l1-stat-after-create
    (implies
     (and (l1-fs-p fs)
          (stringp text2)
          (symbol-listp hns1)
          (symbol-listp hns2)
          (not (l1-stat hns2 fs))
          (stringp (l1-stat hns2 (l1-create hns2 fs text2)))
          (stringp (l1-stat hns1 fs)))
     (equal (l1-stat hns1 (l1-create hns2 fs text2))
            (if (equal hns1 hns2)
                text2 (l1-stat hns1 fs))))
    :hints (("goal" :induct (induction-scheme hns1 hns2 fs)))))

(defthm l1-read-after-create-1
  (implies (and (l1-fs-p fs)
                (stringp text)
                (symbol-listp hns)
                (equal n (length text))
                (not (l1-stat hns fs))
                (stringp (l1-stat hns (l1-create hns fs text))))
           (equal (l1-rdchs hns (l1-create hns fs text) 0 n) text)))

(defthm l1-read-after-create-2
  (implies (and (l1-fs-p fs)
                (stringp text2)
                (symbol-listp hns1)
                (symbol-listp hns2)
                (not (equal hns1 hns2))
                (natp start1)
                (natp n1)
                (not (l1-stat hns2 fs))
                (stringp (l1-stat hns2 (l1-create hns2 fs text2)))
                (stringp (l1-stat hns1 fs)))
           (equal (l1-rdchs hns1 (l1-create hns2 fs text2) start1 n1)
                  (l1-rdchs hns1 fs start1 n1))))

; Find length of file
(defun l1-wc-len (hns fs)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l1-fs-p fs))))
  (let ((file (l1-stat hns fs)))
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
