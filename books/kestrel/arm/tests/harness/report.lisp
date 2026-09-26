; Summarizing the results of running a model on test vectors
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

;; This book summarizes the results of running a model on test vectors.  It
;; knows nothing about ARM32: it never sees a vector, a state, or an error
;; value of the model, only one record per vector, which the model's harness
;; builds (see report-records in harness.lisp).  So another model can use it
;; too, and it will move to a directory of its own when one does.
;;
;; A record is a keyword-value list with these keys:
;;
;;   :id           the vector's id
;;   :name         the name of the instruction, or nil if the model's decoder
;;                 rejects it
;;   :word         the instruction word, a natural number
;;   :gap-key      for an instruction the decoder rejects, what to tally it by
;;   :error-class  nil, or the outcome class of the vector when the model's
;;                 error alone decides it (see below)
;;   :mismatches   the vector's real mismatches, each a list (FIELD :expected
;;                 EXPECTED :actual ACTUAL)
;;   :unknown      the fields of the vector that depend on an UNKNOWN value
;;
;; Each vector gets one of these outcome classes:
;;
;;   :pass               the model agreed with the expectations
;;   :mismatch           the model disagreed, and no waiver excused it; this is
;;                       the only class that fails a run
;;   :waived             the model disagreed, and waivers excused every
;;                       disagreement
;;   :unknown-dependent  no disagreement, but some field depends on an UNKNOWN
;;                       value, so it could not be compared
;;   :coverage-gap       the model's decoder rejected the instruction
;;   :unsupported        the model decodes the instruction but does not model
;;                       it
;;   :unpredictable      the architecture leaves the result UNPREDICTABLE, so
;;                       nothing was compared
;;   :skipped            the model cannot run the vector
;;
;; A record with an :error-class has that class, and its mismatches are not
;; considered.  Otherwise its class is :mismatch if a mismatch remains after
;; waivers, :waived if waivers excused them all, :unknown-dependent if some
;; field depends on an UNKNOWN value, and :pass otherwise.
;;
;; A waiver excuses the mismatches of some instructions on some field.  It is a
;; keyword-value list with these keys:
;;
;;   :name     the name of the instructions it applies to, or else
;;   :mask     a mask and a value: it applies to the instruction words whose
;;   :value      bits under the mask equal the value
;;   :field    the field it applies to, such as :apsr, or the first element of
;;             the fields it applies to, such as :reg for all of (:reg 0) to
;;             (:reg 14)
;;   :bits     optional: the bits it applies to, for a numeric field; it then
;;             applies only when the expected and actual values differ in no
;;             other bits
;;   :reason   why the mismatch is not a bug in the model: :unknown (UNKNOWN
;;             per the manual), :implementation-defined (IMPLEMENTATION
;;             DEFINED per the manual), :oracle-limitation (the expectation is
;;             wrong or arbitrary), or :model-feature-absent (the model lacks
;;             a feature by design)
;;   :cite     the section of the manual, or the design decision, that
;;             justifies it
;;   :note     optional: an explanation
;;
;; A waiver applies only to what would otherwise be a mismatch.  A waiver that
;; excuses nothing is reported as unused, so that stale waivers get removed.
;;
;; A summary is a keyword-value list with these keys:
;;
;;   :name            what was run
;;   :vectors         the number of vectors
;;   :not-run         an alist from reasons to the numbers of tests that could
;;                    not be made into vectors for them (supplied by the caller)
;;   :counts          an alist from every outcome class to its number of vectors
;;   :by-name         an alist from instruction names to alists from outcome
;;                    classes to numbers of vectors
;;   :gaps            an alist from gap keys to numbers of coverage gaps,
;;                    largest first
;;   :mismatches      for each vector of class :mismatch, a list (ID NAME WORD
;;                    . MISMATCHES) of the mismatches no waiver excused
;;   :waived          for each vector with excused mismatches, a list (ID NAME
;;                    WORD . WAIVED), each element of WAIVED a list (MISMATCH
;;                    REASON CITE)
;;   :unknown         for each vector with fields that depend on an UNKNOWN
;;                    value, a pair (ID . FIELDS)
;;   :unexercised     the instructions no vector exercised
;;   :unused-waivers  the waivers that excused nothing

(include-book "../../portcullis") ; only for the "ARM" package
(include-book "std/util/bstar" :dir :system)
(local (include-book "kestrel/file-io-light/open-output-channel" :dir :system))
(local (include-book "kestrel/file-io-light/close-output-channel" :dir :system))
(local (include-book "kestrel/file-io-light/print-object-dollar-fn" :dir :system))

;; Looks up KEY in the keyword-value list X, returning DEFAULT if absent.
;; Kept disabled for the same reason as vec-get in vectors.lisp.
(defund report-get (key x default)
  (declare (xargs :guard (and (keywordp key)
                              (keyword-value-listp x))))
  (let ((tail (assoc-keyword key x)))
    (if tail (cadr tail) default)))

(defconst *outcome-class-labels*
  '((:pass . "pass")
    (:mismatch . "mismatch")
    (:waived . "waived")
    (:unknown-dependent . "UNKNOWN-dependent")
    (:coverage-gap . "coverage gap")
    (:unsupported . "unsupported")
    (:unpredictable . "unpredictable")
    (:skipped . "skipped")))

(defconst *outcome-classes* (strip-cars *outcome-class-labels*))

;; The classes a record's :error-class can give.
(defconst *error-classes*
  '(:pass :coverage-gap :unsupported :unpredictable :skipped))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Records and waivers.

;; A mismatch, (FIELD :expected EXPECTED :actual ACTUAL).
(defun mismatchp (x)
  (declare (xargs :guard t))
  (and (consp x)
       (keyword-value-listp (cdr x))))

(defun mismatch-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (mismatchp (car x))
         (mismatch-listp (cdr x)))))

(defthm alistp-when-mismatch-listp
  (implies (mismatch-listp x)
           (alistp x)))

(defthm mismatch-listp-of-append
  (implies (and (mismatch-listp x)
                (mismatch-listp y))
           (mismatch-listp (append x y))))

(defthm mismatch-listp-of-intersection-equal
  (implies (mismatch-listp x)
           (mismatch-listp (intersection-equal x y))))

(defthm keyword-value-listp-of-cdr-of-assoc-equal-when-mismatch-listp
  (implies (mismatch-listp x)
           (keyword-value-listp (cdr (assoc-equal key x)))))

(defthm consp-of-assoc-equal-when-mismatch-listp
  (implies (mismatch-listp x)
           (iff (consp (assoc-equal key x))
                (assoc-equal key x))))

(defconst *record-keys*
  '(:id :name :word :gap-key :error-class :mismatches :unknown))

(defun report-recordp (x)
  (declare (xargs :guard t))
  (and (keyword-value-listp x)
       (subsetp-eq (evens x) *record-keys*)
       (no-duplicatesp-equal (evens x))
       (natp (report-get :word x nil))
       (let ((class (report-get :error-class x nil)))
         (or (null class)
             (member-eq class *error-classes*)))
       (mismatch-listp (report-get :mismatches x nil))
       (true-listp (report-get :unknown x nil))))

;; A record built with list, as a model's harness builds them, satisfies
;; report-recordp if its values do.
(defthm report-recordp-of-list
  (equal (report-recordp (list :id id :name name :word word :gap-key gap-key
                               :error-class error-class :mismatches mismatches
                               :unknown unknown))
         (and (natp word)
              (or (null error-class)
                  (member-eq error-class *error-classes*))
              (mismatch-listp mismatches)
              (true-listp unknown)))
  :hints (("Goal" :in-theory (enable report-get))))

(defun report-record-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (report-recordp (car x))
         (report-record-listp (cdr x)))))

(defconst *waiver-keys* '(:name :mask :value :field :bits :reason :cite :note))

(defconst *waiver-reasons*
  '(:unknown :implementation-defined :oracle-limitation :model-feature-absent))

(defun waiverp (x)
  (declare (xargs :guard t))
  (and (keyword-value-listp x)
       (subsetp-eq (evens x) *waiver-keys*)
       (no-duplicatesp-equal (evens x))
       (if (report-get :name x nil)
           (and (not (report-get :mask x nil))
                (not (report-get :value x nil)))
         (and (natp (report-get :mask x nil))
              (natp (report-get :value x nil))))
       (report-get :field x nil)
       (let ((bits (report-get :bits x nil)))
         (or (null bits) (natp bits)))
       (member-eq (report-get :reason x nil) *waiver-reasons*)
       (let ((cite (report-get :cite x nil)))
         (and (stringp cite)
              (not (equal cite ""))))
       (stringp (report-get :note x ""))))

(defun waiver-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (waiverp (car x))
         (waiver-listp (cdr x)))))

(defthm true-listp-when-waiver-listp
  (implies (waiver-listp x)
           (true-listp x))
  :rule-classes :forward-chaining)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Applying waivers.

;; Whether WAIVER excuses MISMATCH, of the instruction with NAME and WORD.
(defun waiver-applies-p (waiver name word mismatch)
  (declare (xargs :guard (and (waiverp waiver)
                              (natp word)
                              (mismatchp mismatch))))
  (b* ((field (car mismatch))
       (waiver-field (report-get :field waiver nil))
       (waiver-name (report-get :name waiver nil))
       (bits (report-get :bits waiver nil))
       (expected (report-get :expected (cdr mismatch) nil))
       (actual (report-get :actual (cdr mismatch) nil)))
    (and (if waiver-name
             (equal waiver-name name)
           (equal (logand (report-get :mask waiver nil) word)
                  (report-get :value waiver nil)))
         (or (equal waiver-field field)
             (and (consp field)
                  (equal waiver-field (car field))))
         (or (null bits)
             (and (integerp expected)
                  (integerp actual)
                  (equal 0 (logand (lognot bits) (logxor expected actual))))))))

;; The first of WAIVERS that excuses MISMATCH, or nil.
(defun find-waiver (waivers name word mismatch)
  (declare (xargs :guard (and (waiver-listp waivers)
                              (natp word)
                              (mismatchp mismatch))))
  (if (endp waivers)
      nil
    (if (waiver-applies-p (car waivers) name word mismatch)
        (car waivers)
      (find-waiver (cdr waivers) name word mismatch))))

(defthm waiverp-of-find-waiver
  (implies (and (waiver-listp waivers)
                (find-waiver waivers name word mismatch))
           (waiverp (find-waiver waivers name word mismatch)))
  :hints (("Goal" :in-theory (disable waiverp waiver-applies-p))))

;; Splits MISMATCHES, of the instruction with NAME and WORD, into those no
;; waiver excuses and those some waiver does.  Returns (mv unwaived waived
;; used), where each element of WAIVED is (MISMATCH REASON CITE), and USED is
;; USED with the waivers that applied added.
(defund apply-waivers (mismatches name word waivers used)
  (declare (xargs :guard (and (mismatch-listp mismatches)
                              (natp word)
                              (waiver-listp waivers)
                              (true-listp used))))
  (if (endp mismatches)
      (mv nil nil used)
    (b* ((mismatch (car mismatches))
         (waiver (find-waiver waivers name word mismatch))
         ((mv unwaived waived used)
          (apply-waivers (cdr mismatches) name word waivers
                         (if waiver (add-to-set-equal waiver used) used))))
      (if waiver
          (mv unwaived
              (cons (list mismatch
                          (report-get :reason waiver nil)
                          (report-get :cite waiver nil))
                    waived)
              used)
        (mv (cons mismatch unwaived) waived used)))))

(defthm true-listp-of-mv-nth-2-of-apply-waivers
  (implies (true-listp used)
           (true-listp (mv-nth 2 (apply-waivers mismatches name word waivers used))))
  :hints (("Goal" :in-theory (e/d (apply-waivers) (find-waiver)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tallies.

;; An alist from keys to counts.
(defun count-alistp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (consp (car x))
         (natp (cdar x))
         (count-alistp (cdr x)))))

(defthm alistp-when-count-alistp
  (implies (count-alistp x)
           (alistp x)))

;; Adds N to the count of KEY in COUNTS.  A new key goes at the end.
(defun add-count (key n counts)
  (declare (xargs :guard (and (natp n) (count-alistp counts))))
  (if (endp counts)
      (list (cons key n))
    (if (equal key (caar counts))
        (cons (cons key (+ n (cdar counts))) (cdr counts))
      (cons (car counts) (add-count key n (cdr counts))))))

(defthm count-alistp-of-add-count
  (implies (and (natp n) (count-alistp counts))
           (count-alistp (add-count key n counts))))

;; Adds each count in COUNTS2 to COUNTS.
(defun add-counts (counts2 counts)
  (declare (xargs :guard (and (count-alistp counts2) (count-alistp counts))))
  (if (endp counts2)
      counts
    (add-counts (cdr counts2)
                (add-count (caar counts2) (cdar counts2) counts))))

(defthm count-alistp-of-add-counts
  (implies (and (count-alistp counts2) (count-alistp counts))
           (count-alistp (add-counts counts2 counts))))

;; An alist from instruction names to count alists.
(defun by-name-alistp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (consp (car x))
         (count-alistp (cdar x))
         (by-name-alistp (cdr x)))))

(defthm alistp-when-by-name-alistp
  (implies (by-name-alistp x)
           (alistp x)))

;; Adds the counts in COUNTS to those of NAME in BY-NAME.
(defun add-name-counts (name counts by-name)
  (declare (xargs :guard (and (count-alistp counts) (by-name-alistp by-name))))
  (if (endp by-name)
      (list (cons name counts))
    (if (equal name (caar by-name))
        (cons (cons name (add-counts counts (cdar by-name))) (cdr by-name))
      (cons (car by-name) (add-name-counts name counts (cdr by-name))))))

(defthm by-name-alistp-of-add-name-counts
  (implies (and (count-alistp counts) (by-name-alistp by-name))
           (by-name-alistp (add-name-counts name counts by-name))))

;; Adds each entry of BY-NAME2 to BY-NAME.
(defun add-by-name (by-name2 by-name)
  (declare (xargs :guard (and (by-name-alistp by-name2) (by-name-alistp by-name))))
  (if (endp by-name2)
      by-name
    (add-by-name (cdr by-name2)
                 (add-name-counts (caar by-name2) (cdar by-name2) by-name))))

(defthm by-name-alistp-of-add-by-name
  (implies (and (by-name-alistp by-name2) (by-name-alistp by-name))
           (by-name-alistp (add-by-name by-name2 by-name))))

;; Inserts the pair (KEY . COUNT) into the sorted count alist COUNTS, which has
;; larger counts first, and equal counts in lexorder of their keys.
(defun insert-count (pair counts)
  (declare (xargs :guard (and (consp pair)
                              (natp (cdr pair))
                              (count-alistp counts))))
  (if (or (endp counts)
          (> (cdr pair) (cdar counts))
          (and (= (cdr pair) (cdar counts))
               (lexorder (car pair) (caar counts))))
      (cons pair counts)
    (cons (car counts) (insert-count pair (cdr counts)))))

(defthm count-alistp-of-insert-count
  (implies (and (consp pair)
                (natp (cdr pair))
                (count-alistp counts))
           (count-alistp (insert-count pair counts))))

;; Sorts COUNTS, larger counts first.
(defun sort-counts (counts)
  (declare (xargs :guard (count-alistp counts)))
  (if (endp counts)
      nil
    (insert-count (car counts) (sort-counts (cdr counts)))))

(defthm count-alistp-of-sort-counts
  (implies (count-alistp counts)
           (count-alistp (sort-counts counts))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Summarizing.

;; Applies WAIVERS to RECORD and gives it its outcome class.  Returns (mv class
;; unwaived waived used), where UNWAIVED and WAIVED are as for apply-waivers
;; (nil if the record has an :error-class), and USED is USED with the waivers
;; that applied added.
(defund classify-record (record waivers used)
  (declare (xargs :guard (and (report-recordp record)
                              (waiver-listp waivers)
                              (true-listp used))))
  (b* ((error-class (report-get :error-class record nil))
       ((when error-class)
        (mv error-class nil nil used))
       ((mv unwaived waived used)
        (apply-waivers (report-get :mismatches record nil)
                       (report-get :name record nil)
                       (report-get :word record nil)
                       waivers used)))
    (mv (cond (unwaived :mismatch)
              (waived :waived)
              ((report-get :unknown record nil) :unknown-dependent)
              (t :pass))
        unwaived waived used)))

(defthm true-listp-of-mv-nth-3-of-classify-record
  (implies (true-listp used)
           (true-listp (mv-nth 3 (classify-record record waivers used))))
  :hints (("Goal" :in-theory (enable classify-record))))

;; Adds RECORD to the summary that summarize-records accumulates.  Returns (mv
;; counts by-name gaps mismatches waived unknown used).
(defund summarize-record (record waivers
                                 counts by-name gaps mismatches waived unknown used)
  (declare (xargs :guard (and (report-recordp record)
                              (waiver-listp waivers)
                              (count-alistp counts)
                              (by-name-alistp by-name)
                              (count-alistp gaps)
                              (true-listp used))))
  (b* ((id (report-get :id record nil))
       (name (report-get :name record nil))
       (word (report-get :word record nil))
       (fields (report-get :unknown record nil))
       ((mv class unwaived waived-here used)
        (classify-record record waivers used)))
    (mv (add-count class 1 counts)
        (if name
            (add-name-counts name (list (cons class 1)) by-name)
          by-name)
        (if (eq class :coverage-gap)
            (add-count (report-get :gap-key record nil) 1 gaps)
          gaps)
        (if unwaived
            (cons (list* id name word unwaived) mismatches)
          mismatches)
        (if waived-here
            (cons (list* id name word waived-here) waived)
          waived)
        (if fields
            (cons (cons id fields) unknown)
          unknown)
        used)))

(defthm summarize-record-return-types
  (implies (and (count-alistp counts)
                (by-name-alistp by-name)
                (count-alistp gaps)
                (true-listp mismatches)
                (true-listp waived)
                (true-listp unknown)
                (true-listp used))
           (and (count-alistp (mv-nth 0 (summarize-record record waivers counts by-name gaps mismatches waived unknown used)))
                (by-name-alistp (mv-nth 1 (summarize-record record waivers counts by-name gaps mismatches waived unknown used)))
                (count-alistp (mv-nth 2 (summarize-record record waivers counts by-name gaps mismatches waived unknown used)))
                (true-listp (mv-nth 3 (summarize-record record waivers counts by-name gaps mismatches waived unknown used)))
                (true-listp (mv-nth 4 (summarize-record record waivers counts by-name gaps mismatches waived unknown used)))
                (true-listp (mv-nth 5 (summarize-record record waivers counts by-name gaps mismatches waived unknown used)))
                (true-listp (mv-nth 6 (summarize-record record waivers counts by-name gaps mismatches waived unknown used)))))
  :hints (("Goal" :in-theory (enable summarize-record))))

;; Accumulates the summary of RECORDS.  Returns (mv counts by-name gaps
;; mismatches waived unknown used), with the lists of vectors in the order of
;; RECORDS.
(defun summarize-records (records waivers
                                  counts by-name gaps mismatches waived unknown used)
  (declare (xargs :guard (and (report-record-listp records)
                              (waiver-listp waivers)
                              (count-alistp counts)
                              (by-name-alistp by-name)
                              (count-alistp gaps)
                              (true-listp mismatches)
                              (true-listp waived)
                              (true-listp unknown)
                              (true-listp used))))
  (if (endp records)
      (mv counts by-name gaps
          (reverse mismatches) (reverse waived) (reverse unknown)
          used)
    (b* (((mv counts by-name gaps mismatches waived unknown used)
          (summarize-record (car records) waivers
                            counts by-name gaps mismatches waived unknown used)))
      (summarize-records (cdr records) waivers
                         counts by-name gaps mismatches waived unknown used))))

(defthm summarize-records-return-types
  (implies (and (count-alistp counts)
                (by-name-alistp by-name)
                (count-alistp gaps)
                (true-listp mismatches)
                (true-listp waived)
                (true-listp unknown)
                (true-listp used))
           (and (count-alistp (mv-nth 0 (summarize-records records waivers counts by-name gaps mismatches waived unknown used)))
                (by-name-alistp (mv-nth 1 (summarize-records records waivers counts by-name gaps mismatches waived unknown used)))
                (count-alistp (mv-nth 2 (summarize-records records waivers counts by-name gaps mismatches waived unknown used)))
                (true-listp (mv-nth 6 (summarize-records records waivers counts by-name gaps mismatches waived unknown used))))))

;; Summarizes RECORDS under the name NAME.  NAMES lists the names of all the
;; instructions of the model, WAIVERS are the waivers to apply, and NOT-RUN is
;; the alist for the summary's :not-run.
(defun summarize-results (name records names waivers not-run)
  (declare (xargs :guard (and (stringp name)
                              (report-record-listp records)
                              (true-listp names)
                              (waiver-listp waivers)
                              (count-alistp not-run))))
  (b* (((mv counts by-name gaps mismatches waived unknown used)
        (summarize-records records waivers
                           (pairlis$ *outcome-classes* '(0 0 0 0 0 0 0 0))
                           nil nil nil nil nil nil)))
    (list :name name
          :vectors (len records)
          :not-run not-run
          :counts counts
          :by-name by-name
          :gaps (sort-counts gaps)
          :mismatches mismatches
          :waived waived
          :unknown unknown
          :unexercised (set-difference-equal names (strip-cars by-name))
          :unused-waivers (set-difference-equal waivers used))))

(defun summaryp (x)
  (declare (xargs :guard t))
  (and (keyword-value-listp x)
       (stringp (report-get :name x ""))
       (natp (report-get :vectors x 0))
       (count-alistp (report-get :not-run x nil))
       (count-alistp (report-get :counts x nil))
       (by-name-alistp (report-get :by-name x nil))
       (count-alistp (report-get :gaps x nil))
       (true-list-listp (report-get :mismatches x nil))
       (true-list-listp (report-get :waived x nil))
       (true-listp (report-get :unknown x nil))
       (true-listp (report-get :unexercised x nil))
       (true-listp (report-get :unused-waivers x nil))))

(defun summary-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (summaryp (car x))
         (summary-listp (cdr x)))))

;; Whether SUMMARY has no mismatch that a waiver did not excuse.
(defun check-summary (summary)
  (declare (xargs :guard (summaryp summary)))
  (null (report-get :mismatches summary nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Merging summaries, such as those of the files of a corpus.

(defun sum-vectors (summaries)
  (declare (xargs :guard (summary-listp summaries)))
  (if (endp summaries)
      0
    (+ (report-get :vectors (car summaries) 0)
       (sum-vectors (cdr summaries)))))

;; Adds up the count alists under KEY in SUMMARIES, onto COUNTS.
(defun merge-counts (key summaries counts)
  (declare (xargs :guard (and (member-eq key '(:not-run :counts :gaps))
                              (summary-listp summaries)
                              (count-alistp counts))))
  (if (endp summaries)
      counts
    (merge-counts key (cdr summaries)
                  (add-counts (report-get key (car summaries) nil) counts))))

(defthm count-alistp-of-merge-counts
  (implies (and (member-eq key '(:not-run :counts :gaps))
                (summary-listp summaries)
                (count-alistp counts))
           (count-alistp (merge-counts key summaries counts))))

(defun merge-by-name (summaries by-name)
  (declare (xargs :guard (and (summary-listp summaries)
                              (by-name-alistp by-name))))
  (if (endp summaries)
      by-name
    (merge-by-name (cdr summaries)
                   (add-by-name (report-get :by-name (car summaries) nil) by-name))))

;; Appends the lists under KEY in SUMMARIES.
(defun append-lists (key summaries)
  (declare (xargs :guard (and (member-eq key '(:mismatches :waived :unknown))
                              (summary-listp summaries))))
  (if (endp summaries)
      nil
    (append (report-get key (car summaries) nil)
            (append-lists key (cdr summaries)))))

;; Intersects the lists under KEY in SUMMARIES, which must not be empty.
(defun intersect-lists (key summaries)
  (declare (xargs :guard (and (member-eq key '(:unexercised :unused-waivers))
                              (summary-listp summaries)
                              (consp summaries))))
  (if (endp (cdr summaries))
      (report-get key (car summaries) nil)
    (intersection-equal (report-get key (car summaries) nil)
                        (intersect-lists key (cdr summaries)))))

;; Combines SUMMARIES, which must not be empty, into one summary named NAME.
;; An instruction is unexercised, and a waiver unused, if it is so in every
;; summary.
(defun merge-summaries (name summaries)
  (declare (xargs :guard (and (stringp name)
                              (summary-listp summaries)
                              (consp summaries))))
  (list :name name
        :vectors (sum-vectors summaries)
        :not-run (merge-counts :not-run summaries nil)
        :counts (merge-counts :counts summaries nil)
        :by-name (merge-by-name summaries nil)
        :gaps (sort-counts (merge-counts :gaps summaries nil))
        :mismatches (append-lists :mismatches summaries)
        :waived (append-lists :waived summaries)
        :unknown (append-lists :unknown summaries)
        :unexercised (intersect-lists :unexercised summaries)
        :unused-waivers (intersect-lists :unused-waivers summaries)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Printing and writing summaries.

;; Prints ", COUNT CLASS" for each entry of COUNTS that is nonzero or is for
;; :mismatch.
(defun print-class-counts (counts)
  (declare (xargs :guard (count-alistp counts)))
  (if (endp counts)
      nil
    (b* ((class (caar counts))
         (count (cdar counts))
         (label (cdr (assoc-equal class *outcome-class-labels*))))
      (prog2$ (if (or (< 0 count) (eq class :mismatch))
                  (if (stringp label)
                      (cw ", ~x0 ~s1" count label)
                    (cw ", ~x0 ~x1" count class))
                nil)
              (print-class-counts (cdr counts))))))

;; Whether some count in COUNTS is nonzero.
(defun some-count-p (counts)
  (declare (xargs :guard (count-alistp counts)))
  (and (consp counts)
       (or (< 0 (cdar counts))
           (some-count-p (cdr counts)))))

;; Prints "COUNT KEY" for each nonzero entry of COUNTS, the first preceded by
;; SEP and the others by a comma.
(defun print-counts (counts sep)
  (declare (xargs :guard (and (count-alistp counts) (stringp sep))))
  (if (endp counts)
      nil
    (if (< 0 (cdar counts))
        (prog2$ (cw "~s0~x1 ~x2" sep (cdar counts) (caar counts))
                (print-counts (cdr counts) ", "))
      (print-counts (cdr counts) sep))))

;; Prints the first N entries of COUNTS, each on a line of its own.
(defun print-count-lines (counts n)
  (declare (xargs :guard (and (count-alistp counts) (natp n))))
  (if (or (endp counts) (zp n))
      nil
    (prog2$ (cw "    ~c0  ~x1~%" (cons (cdar counts) 7) (caar counts))
            (print-count-lines (cdr counts) (+ -1 n)))))

;; Prints the first N of ENTRIES, the :mismatches of a summary, with the
;; instruction word and the numbers in the mismatches in hexadecimal.  (The id
;; and name are printed in decimal, where a name such as :add does not need
;; escaping.)
(defun print-mismatch-entries (entries n)
  (declare (xargs :guard (and (true-list-listp entries) (natp n))))
  (if (or (endp entries) (zp n))
      nil
    (b* ((entry (car entries)))
      (prog2$ (cw "    ~x0 ~x1 " (first entry) (second entry))
              (prog2$ (cw-print-base-radix '(16 . t) "~x0~%~*1"
                                           (third entry)
                                           (list "" "      ~x*~%" "      ~x*~%"
                                                 "      ~x*~%" (nthcdr 3 entry)))
                      (print-mismatch-entries (cdr entries) (+ -1 n)))))))

;; Prints each of WAIVERS on a line of its own: what it selects, its field,
;; and its citation.
(defun print-waivers (waivers)
  (declare (xargs :guard (true-listp waivers)))
  (if (endp waivers)
      nil
    (b* ((waiver (car waivers)))
      (prog2$ (cond ((not (waiverp waiver))
                     (cw "    ~x0~%" waiver))
                    ((report-get :name waiver nil)
                     (cw "    ~x0 ~x1 (~s2)~%"
                         (report-get :name waiver nil)
                         (report-get :field waiver nil)
                         (report-get :cite waiver nil)))
                    (t
                     (cw-print-base-radix '(16 . t)
                                          "    (:mask ~x0 :value ~x1) ~x2 (~s3)~%"
                                          (report-get :mask waiver nil)
                                          (report-get :value waiver nil)
                                          (report-get :field waiver nil)
                                          (report-get :cite waiver nil))))
              (print-waivers (cdr waivers))))))

;; Prints ITEMS, N to a line.
(defun print-items (items n i)
  (declare (xargs :guard (and (true-listp items) (posp n) (natp i))))
  (if (endp items)
      (if (zp i) nil (cw "~%"))
    (prog2$ (cw (if (zp i) "    ~x0" " ~x0") (car items))
            (if (<= n (+ 1 i))
                (prog2$ (cw "~%")
                        (print-items (cdr items) n 0))
              (print-items (cdr items) n (+ 1 i))))))

;; Prints SUMMARY, listing at most MAX mismatches and gap keys.  If COVERAGEP,
;; also lists the unused waivers and the unexercised instructions, which are
;; meaningful for a whole corpus rather than for part of one.
(defun print-summary (summary max coveragep)
  (declare (xargs :guard (and (summaryp summary)
                              (natp max))))
  (b* ((not-run (report-get :not-run summary nil))
       (gaps (report-get :gaps summary nil))
       (mismatches (report-get :mismatches summary nil))
       (unused (report-get :unused-waivers summary nil))
       (unexercised (report-get :unexercised summary nil))
       (- (cw "~s0: ~x1 vectors" (report-get :name summary "")
              (report-get :vectors summary 0)))
       (- (print-class-counts (report-get :counts summary nil)))
       (- (cw "~%"))
       (- (if (some-count-p not-run)
              (prog2$ (cw "  Not run")
                      (prog2$ (print-counts not-run ": ") (cw "~%")))
            nil))
       (- (if (consp gaps)
              (prog2$ (cw "  Coverage gaps by key, ~x0 of ~x1 keys:~%"
                          (min max (len gaps)) (len gaps))
                      (print-count-lines gaps max))
            nil))
       (- (if (consp mismatches)
              (prog2$ (cw "  First ~x0 of ~x1 mismatches:~%"
                          (min max (len mismatches)) (len mismatches))
                      (print-mismatch-entries mismatches max))
            nil)))
    (if coveragep
        (prog2$
         (if (consp unused)
             (prog2$ (cw "  Unused waivers:~%")
                     (print-waivers unused))
           (cw "  Unused waivers: none~%"))
         (prog2$ (cw "  Unexercised instructions: ~x0~%" (len unexercised))
                 (print-items unexercised 4 0)))
      nil)))

;; Writes SUMMARY to the file FILENAME, for tools and for comparing runs.  It
;; is pretty-printed, so that a list too long for one line, such as the
;; mismatches, has an element per line.  Returns (mv erp state).
(defun write-summary (summary filename state)
  (declare (xargs :guard (and (summaryp summary)
                              (stringp filename))
                  :stobjs state
                  :guard-hints (("Goal" :in-theory (enable open-output-channel-p)))))
  (mv-let (channel state)
    (open-output-channel filename :object state)
    (if (not channel)
        (mv (list :could-not-open filename) state)
      (let* ((state (print-object$+ summary channel
                                    :header nil
                                    :print-pretty t
                                    :print-right-margin 100))
             (state (close-output-channel channel state)))
        (mv nil state)))))
