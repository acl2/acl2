; Running a corpus of test vector files
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

;; Runs a corpus whose vectors were made outside ACL2, by a converter or a
;; generator, and reports the results.  Each file NAME of the corpus is a pair
;; of files in one directory: NAME.sexp holds the vectors (see
;; read-vectors.lisp), and NAME.not-run.sexp holds one alist, from reasons to
;; the numbers of tests not made into vectors for them.  A corpus script calls
;; run-corpus and exits with a nonzero status if any file failed.

(include-book "harness")
(include-book "read-vectors")

;; The theorems about summaries below conclude summaryp, so keep it closed.
(local (in-theory (disable summaryp)))

;; Reads the alist of tests not made into vectors from FILENAME, which must
;; hold it as its only object.  Returns (mv erp not-run state).
(defund read-not-run (filename state)
  (declare (xargs :guard (stringp filename)
                  :stobjs state))
  (mv-let (erp objects state)
    (acl2::read-objects-from-file filename state)
    (cond (erp (mv erp nil state))
          ((and (consp objects)
                (null (cdr objects))
                (count-alistp (car objects)))
           (mv nil (car objects) state))
          (t (mv (list :bad-not-run-file filename) nil state)))))

(defthm count-alistp-of-mv-nth-1-of-read-not-run
  (count-alistp (mv-nth 1 (read-not-run filename state)))
  :hints (("Goal" :in-theory (enable read-not-run))))

(defthm state-p1-of-mv-nth-2-of-read-not-run
  (implies (and (stringp filename)
                (state-p1 state))
           (state-p1 (mv-nth 2 (read-not-run filename state))))
  :hints (("Goal" :in-theory (enable read-not-run))))

;; Runs the vectors of the file NAME, in the directory DIR, of the corpus
;; CORPUS with WAIVERS, prints their summary, listing at most MAX mismatches
;; and gap keys, and writes it to NAME.sexp in RESULTS-DIR.  Returns (mv
;; unreadablep summary state), where SUMMARY is nil if the file was not run.
;; A file whose vectors have not been made is reported and is not unreadable.
(defund run-vector-file (corpus name dir results-dir waivers max state)
  (declare (xargs :guard (and (stringp corpus)
                              (stringp name)
                              (stringp dir)
                              (stringp results-dir)
                              (waiver-listp waivers)
                              (natp max))
                  :stobjs state))
  (b* ((label (concatenate 'string corpus "/" name))
       ((mv erp vectors state)
        (read-vectors (concatenate 'string dir name ".sexp") state))
       ((when (and (consp erp) (eq (car erp) :could-not-open-channel)))
        (prog2$ (cw "~s0: no vectors~%" label)
                (mv nil nil state)))
       ((when erp)
        (prog2$ (cw "~s0: could not read the vectors: ~x1~%" label erp)
                (mv t nil state)))
       ((mv erp not-run state)
        (read-not-run (concatenate 'string dir name ".not-run.sexp") state))
       ((when erp)
        (prog2$ (cw "~s0: could not read the tests not run: ~x1~%" label erp)
                (mv t nil state)))
       (summary (time$ (summarize-vectors label vectors waivers not-run)
                       :msg "~s0: ran in ~st seconds~%"
                       :args (list label)))
       (- (print-summary summary max nil))
       ((mv erp state)
        (write-summary summary (concatenate 'string results-dir name ".sexp")
                       state))
       (- (and erp (cw "Could not write the summary: ~x0~%" erp))))
    (mv nil summary state)))

(defthm summaryp-of-mv-nth-1-of-run-vector-file
  (implies (and (stringp corpus)
                (stringp name)
                (mv-nth 1 (run-vector-file corpus name dir results-dir waivers max state)))
           (summaryp (mv-nth 1 (run-vector-file corpus name dir results-dir waivers max state))))
  :hints (("Goal" :in-theory (enable run-vector-file))))

(defthm state-p1-of-mv-nth-2-of-run-vector-file
  (implies (and (stringp dir)
                (stringp name)
                (stringp results-dir)
                (state-p1 state))
           (state-p1 (mv-nth 2 (run-vector-file corpus name dir results-dir waivers max state))))
  :hints (("Goal" :in-theory (enable run-vector-file))))

;; Runs the files NAMES of the corpus CORPUS (see run-vector-file).  Returns
;; (mv failures summaries state), where FAILURES are the names of the files
;; that could not be read or have mismatches no waiver excuses, and SUMMARIES
;; are the summaries of the files run.
(defund run-vector-files (corpus names dir results-dir waivers max state)
  (declare (xargs :guard (and (stringp corpus)
                              (string-listp names)
                              (stringp dir)
                              (stringp results-dir)
                              (waiver-listp waivers)
                              (natp max))
                  :stobjs state))
  (if (endp names)
      (mv nil nil state)
    (b* (((mv unreadablep summary state)
          (run-vector-file corpus (car names) dir results-dir waivers max state))
         ((mv failures summaries state)
          (run-vector-files corpus (cdr names) dir results-dir waivers max state)))
      (mv (if (or unreadablep
                  (and summary (not (check-summary summary))))
              (cons (car names) failures)
            failures)
          (if summary (cons summary summaries) summaries)
          state))))

(defthm summary-listp-of-mv-nth-1-of-run-vector-files
  (implies (and (stringp corpus)
                (string-listp names))
           (summary-listp (mv-nth 1 (run-vector-files corpus names dir results-dir waivers max state))))
  :hints (("Goal" :in-theory (enable run-vector-files))))

(defthm state-p1-of-mv-nth-2-of-run-vector-files
  (implies (and (string-listp names)
                (stringp dir)
                (stringp results-dir)
                (state-p1 state))
           (state-p1 (mv-nth 2 (run-vector-files corpus names dir results-dir waivers max state))))
  :hints (("Goal" :in-theory (enable run-vector-files))))

;; Runs the files NAMES of the corpus CORPUS (see run-vector-file), then
;; prints the summary of all the files run together, and a final line,
;; starting with "SUMMARY", that names the files that failed.  Returns (mv
;; failures state).
(defun run-corpus (corpus names dir results-dir waivers max state)
  (declare (xargs :guard (and (stringp corpus)
                              (string-listp names)
                              (stringp dir)
                              (stringp results-dir)
                              (waiver-listp waivers)
                              (natp max))
                  :stobjs state))
  (b* (((mv failures summaries state)
        (run-vector-files corpus names dir results-dir waivers max state))
       (- (and (consp summaries)
               (print-summary (merge-summaries
                               (concatenate 'string corpus " (all files run)")
                               summaries)
                              max t)))
       (- (cw "SUMMARY ~s0: ~x1 of ~x2 files run, ~x3 files failed: ~x4~%"
              corpus (len summaries) (len names) (len failures) failures)))
    (mv failures state)))
