;; Recognizers for sequences, at this point, very general

(in-package "ACL2")
(include-book "misc/hons-help2" :dir :system)
(include-book "../gen-trees/top")

;; possible taxon names are any atom
(defun valid-taxon (x)
  (declare (xargs :guard t))
  (not (consp x)))

;; possible character states are any atom
(defun valid-char (x)
  (declare (xargs :guard t))
  (not (consp x)))

;; a sequence is made up of valid-chars
(defun valid-seq (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (valid-char (car x))
           (valid-seq (cdr x)))
    t))

;; a set of sequences is a list of valid-seqs
(defun valid-sequences (x)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a set of sequences as structurally well-formed~/
;  ~/
;  Arguments:
;    (1) x - a set of potential sequences

;  "
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp (car x))
           (valid-taxon (caar x))
           (valid-seq (cdar x))
           (valid-sequences (cdr x)))
    t))

;; check for same length
(defun valid-sequences-length-n (x n)
  (declare (xargs :guard (integerp n)))
  (if (consp x)
      (and (consp (car x))
           (valid-taxon (caar x))
           (valid-seq (cdar x))
           (equal (len (cdar x)) n)
           (valid-sequences-length-n (cdr x) n))
    t))

;; sequences with same length
(defun valid-sequences-same-length (x)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Recognizes a set of sequences as structurally well-formed and of equal length~/
;  ~/
;  Arguments:
;     (1) x - a set of potential sequences

; "
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp (car x))
           (valid-taxon (caar x))
           (valid-seq (cdar x))
           (valid-sequences-length-n x (len (cdar x))))
    t))

(defun get-taxa-from-sequences (x)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Returns the taxa-list implied by a set of sequences~/
;  ~/
;  Arguments:
;     (1) x - a valid set of sequences

; "
  (declare (xargs :guard (valid-sequences x)))
  (strip-cars-gen x))

;; Recognizes a tree whose terminals are taxon names from the sequence table
;; sequences.
;;(defun tree-matches-sequences (tree seqs)
;;  (declare (xargs :guard (alistp-gen seqs)))
;;  (subset (mytips tree) (strip-cars-gen seqs)))

(defun tree-matches-sequences (flg x sequences)

;;; Legacy doc string replaced Nov. 2014 by auto-generated defxdoc form;
;;; see projects/taspi/taspi-xdoc.lisp.

; ":Doc-Section TASPI
;  Determines if a tree is made up of taxa for which sequences are available~/
;  ~/
;  Arguments:
;     (1) flg - non-nil for a single tree, nil for a set of trees
;     (2) x - a tree
;     (3) sequences - a set of sequences

;  Details: Does not care if x is a valid tree, but sequences must be
;           well-formed."
  (declare (xargs :guard (valid-sequences sequences)
                  :measure (tree-measure x flg)))
  (if flg
      (if (atom x)
          (het x sequences)
        (tree-matches-sequences nil x sequences))
    (if (atom x)
        t
      (and (tree-matches-sequences t (car x) sequences)
           (tree-matches-sequences nil (cdr x) sequences)))))


;; A few properties
(defthm valid-sequences-same-length-valid-sequences
  (implies (valid-sequences-same-length x)
           (valid-sequences x)))

(defthm assoc-hqual-valid-sequences-length-n
  (implies (and (valid-sequences-length-n sequences len)
                (assoc-hqual x sequences))
           (equal (len (cdr (assoc-hqual x sequences)))
                  len)))

(defthm valid-sequences-same-length-assoc-hqual
  (implies (and (valid-sequences-same-length sequences)
                (assoc-hqual x sequences))
           (and
            (valid-seq (cdr (assoc-hqual x sequences)))
            (equal (len (cdr (assoc-hqual x sequences)))
                   (len (cdar sequences))))))

(defthm valid-seqs-alistp-gen
  (implies (valid-sequences seqs)
           (alistp-gen seqs)))
