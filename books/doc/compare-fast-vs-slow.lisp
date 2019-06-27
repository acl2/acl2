; Copyright (C) 2019, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; After building rendered-doc-combined.lsp and rendered-doc-combined-fast.lsp,
; evaluate (write-compare-topics) -- takes under 15 seconds on my laptop -- in
; the directory of those two files to get reports of the differences between
; those manuals.  Differences in subtopics and source files are ignored (but
; the original topics, unabridged, are in the reports).  Note that subtopic
; differences should be reflected anyhow in topic differences, and differences
; only in source file probably don't matter.  See the definition of
; write-compare-topics for optional arguments.

(in-package "ACL2")

(program)

(defun strip-subtopics (str)
  (let ((pos (search "
Subtopics
"
                     str)))
    (if pos
        (subseq str 0 pos)
      str)))

(defun strip-subtopics-lst (topics acc)

; Reverses the stripped topics.

  (cond ((endp topics) (reverse acc))
        (t (strip-subtopics-lst
            (cdr topics)
            (let ((topic (car topics)))
              (cons (list* (car topic) ; name
                           (cadr topic) ; parents
                           (and (caddr topic) ; always true?
                                (strip-subtopics (caddr topic)))
                           nil ; (cdddr topic) ; ignore source for now
                           )
                    acc))))))

(defun all-whitespace-p (pos len str)
  (cond ((>= pos len) t)
        ((member (char str pos) '(#\Space #\Newline #\Tab))
         (all-whitespace-p (1+ pos) len str))
        (t nil)))

(defun equal-mod-whitespace-at-end-1 (pos min len1 len2 str1 str2)
  (cond ((>= pos min)
         (if (= min len1)
             (all-whitespace-p len1 len2 str2)
           (all-whitespace-p len2 len1 str1)))
        ((eql (char str1 pos) (char str2 pos))
         (equal-mod-whitespace-at-end-1 (1+ pos) min len1 len2 str1 str2))
        (t (and (all-whitespace-p pos len1 str1)
                (all-whitespace-p pos len2 str2)))))

(defun equal-mod-whitespace-at-end (str1 str2)
  (or (equal str1 str2) ; optimization
      (let* ((len1 (length str1))
             (len2 (length str2))
             (min (min len1 len2)))
        (equal-mod-whitespace-at-end-1 0 min len1 len2 str1 str2))))

(defun compare-topics1 (lst1 lst2 slst1 slst2 only1 only2 diff1 diff2)

; Slsti is (strip-topics-lst lsti nil).  Each lsti (hence each slsti) is
; strictly sorted by the symbol-name of its car (which is a symbol).  We
; accumulate into only1 those entries in lst1 whose car doesn't associate into
; lst2; similarly for only2.  We accumulate into diff1 and diff2 those
; corresponding entries of lst1 and lst2 -- corresponding in the same of same
; car -- whose corresponding entries in slst1 and slst2 differ.  Ultimately we
; return those accumulators, reversed.

  (cond ((or (endp lst1)
             (endp lst2))
         (mv (revappend only1 lst1)
             (revappend only2 lst2)
             (reverse diff1)
             (reverse diff2)))
        ((string< (symbol-name (caar lst1)) (symbol-name (caar lst2)))
         (compare-topics1 (cdr lst1) lst2 (cdr slst1) slst2
                          (cons (car lst1) only1) only2 diff1 diff2))
        ((string< (symbol-name (caar lst2)) (symbol-name (caar lst1)))
         (compare-topics1 lst1 (cdr lst2) slst1 (cdr slst2)
                          only1 (cons (car lst2) only2) diff1 diff2))
        ((equal (car slst1) (car slst2))
         (compare-topics1 (cdr lst1) (cdr lst2) (cdr slst1) (cdr slst2)
                          only1 only2 diff1 diff2))
        (t
         (compare-topics1 (cdr lst1) (cdr lst2) (cdr slst1) (cdr slst2)
                          only1 only2
                          (cons (car lst1) diff1)
                          (cons (car lst2) diff2)))))

(defun compare-topics (lst1 lst2)

; See compare-topics1.

  (compare-topics1 lst1 lst2
                   (strip-subtopics-lst lst1 nil)
                   (strip-subtopics-lst lst2 nil)
                   nil nil nil nil))

(set-state-ok t)

(defun read-topics (filename state)
  (er-let* ((forms (read-file filename state)))
    (let ((defconst-form (cadr forms)))
      (assert$ (and (eql (length forms) 2)
                    (equal (car forms) '(in-package "ACL2"))
                    (eql (length defconst-form) 3)
                    (eq (car defconst-form) 'DEFCONST)
                    (eq (cadr defconst-form) '*ACL2+BOOKS-DOCUMENTATION*)
                    (consp (caddr defconst-form))
                    (eq (car (caddr defconst-form)) 'QUOTE)
                    (null (cddr (caddr defconst-form))))
               (value (cadr (caddr defconst-form)))))))

(defun print-objects-to-file (lst filename state)
  (mv-let
    (channel state)
    (open-output-channel filename :object state)
    (pprogn (print-objects lst channel state)
            (close-output-channel channel state))))

(defun write-compare-topics-fn (slow fast slow-only fast-only
                                     slow-diff fast-diff state)
  (er-let* ((s (read-topics slow state))
            (f (read-topics fast state)))
    (mv-let (only-s only-f diff-s diff-f)
      (compare-topics s f)
      (pprogn (print-objects-to-file only-s slow-only state)
              (print-objects-to-file only-f fast-only state)
              (print-objects-to-file diff-s slow-diff state)
              (print-objects-to-file diff-f fast-diff state)
              (value (list :slow-only slow-only
                           :fast-only fast-only
                           :slow-diff slow-diff
                           :fast-diff fast-diff))))))

(defmacro write-compare-topics
    (&optional
     (slow '"rendered-doc-combined.lsp")
     (fast '"rendered-doc-combined-fast.lsp")
     (slow-only '"slow-only.lsp") ; topics only in the slow manual
     (fast-only '"fast-only.lsp") ; topics only in the fast manual
     (slow-diff '"slow-diff.lsp") ; topics in both as they appear in the slow manual
     (fast-diff '"fast-diff.lsp") ; topics in both as they appear in the fast manual
     )
  (list 'write-compare-topics-fn
        slow fast slow-only fast-only slow-diff fast-diff 'state))
