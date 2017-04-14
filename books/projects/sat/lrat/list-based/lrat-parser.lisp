; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See ../README.

; This file was originally created by Nathan Wetzler, but now is being
; modified by Warren Hunt and Matt Kaufmannn so as to produce a faster,
; lrat proof checker.

; We read two files: a formula file and a proof file.  A proof step in the
; proof file is either a deletion step

;  d i1 ... ik 0

; or else an addition step

;  j l1 l2 ... lk 0 d1 d2 ... dm -e1 f11 ... f1{m_1} -e2 f21 ... f2{m_2} ... 0

; where:

; - j is the index of a clause C = {l1, l2, ..., lk} to be added redundantly;
; - d1 ... dm are indices of unit clauses for RUP from the negation of C;
; - e1 < e2 < ... are indices of existing (non-deleted) clauses; and
; - ei is a RAT clause Ci, and fi1 ... fi{m_i} are indices of unit clauses for
;   RUP from the union of the negation of C with the negation of Ci \ {-l1}.

; Note that each index j must exceed all preceding clause indices.

(in-package "LRAT")

(include-book "std/util/bstar" :dir :system)
(include-book "lrat-checker")
(program) ; because of (er soft ...), which calls the fmt functions
(set-state-ok t)

(defun read-to-0 (channel lst ctx state)

; Extends lst by pushing values read until 0 is encountered.  However, if we
; get end-of-file when lst is nil, then return :eof.  Closes channel if there
; is an error.

  (b* (((mv eof val state)
        (read-object channel state))
       ((when eof)
        (if (null lst)
            (value :eof)
          (pprogn
           (close-input-channel channel state)
           (er soft ctx
               "Reached end-of-file before finding a terminating 0."))))
       ((when (eql val 0))
        (value lst)))
    (read-to-0 channel (cons val lst) ctx state)))

(defun equal-symbol-name (sym name)
  (and (symbolp sym)
       (equal (symbol-name sym) name)))

(defun parse-cnf-channel-first-line (channel ctx state)

; E.g., the first line could be: p cnf 4 8.

  (flet ((eof-error (channel ctx state)
                    (pprogn
                     (close-input-channel channel state)
                     (er soft ctx
                         "End of file encountered.")))
         (expected-error (channel index expected-string val ctx state)
                         (pprogn
                          (close-input-channel channel state)
                          (er soft ctx
                              "Expected ~n0 object to be ~s1, but ~
                              it was: ~x2."
                              (list index) expected-string val))))
    (b* (((mv eof val state)
          (read-object channel state))
         ((when eof)
          (eof-error channel ctx state))
         ((unless (equal-symbol-name val "P"))
          (expected-error channel 1 "`p'" val ctx state))
         ((mv eof val state)
          (read-object channel state))
         ((when eof)
          (eof-error channel ctx state))
         ((unless (equal-symbol-name val "CNF"))
          (expected-error channel 2 "`cnf'" val ctx state))
         ((mv eof val state)
          (read-object channel state))
         ((when eof)
          (eof-error channel ctx state))
         ((unless (posp val))
          (expected-error channel 3 "a positive integer" val ctx state))
         ((mv eof val state)
          (read-object channel state))
         ((when eof)
          (eof-error channel ctx state))
         ((unless (posp val))
          (expected-error channel 4 "a positive integer" val ctx state)))
      (value nil))))

(defun parse-cnf-channel-formula (channel index fal ctx state)

; Warning: This function is responsible for closing the given input channel.

  (b* (((er val)
        (read-to-0 channel nil ctx state))
       ((when (eq val :eof))
        (pprogn
         (close-input-channel channel state)
         (value fal)))
       (index (1+ index)))
    (parse-cnf-channel-formula channel index
                               (hons-acons index (reverse val) fal)
                               ctx state)))

(defun parse-cnf-channel (channel ctx state)

; Warning: This function is responsible for closing the given input channel.

  (er-progn (parse-cnf-channel-first-line channel ctx state)
            (parse-cnf-channel-formula channel 0 nil ctx state)))

(defun parse-cnf-file (cnf-file state)
  (b* ((ctx (cons 'parse-cnf-file cnf-file))
       ((mv channel state)
        (open-input-channel cnf-file :object state))
       ((when (null channel))
        (er soft ctx
            "Unable to open file ~x0 for input."
            cnf-file)))
    (parse-cnf-channel channel ctx state)))

(defun split-to-negp (lst acc)
  (cond ((endp lst) (mv nil acc nil))
        ((< (car lst) 0)
         (mv (car lst) acc (cdr lst)))
        (t (split-to-negp (cdr lst) (cons (car lst) acc)))))

(defun make-add-step-1 (lst drat-hints)
  (cond ((endp lst) (mv nil (reverse drat-hints)))
        (t (mv-let (minus-e indices rest)
             (split-to-negp lst nil)
             (cond ((null minus-e)
                    (assert$ (null rest)
                             (mv indices (reverse drat-hints))))
                   (t (make-add-step-1 rest
                                       (cons (cons (- minus-e) indices)
                                             drat-hints))))))))

(defun make-add-step (j clause val2)

; We want to make an add step for the given clause index, j, after having
; parsed this line:

;  j l1 l2 ... lk 0 d1 d2 ... dm -e1 f11 ... f1{m_1} -e2 f21 ... f2{m_2} ... 0

; Val is the list (l1 ... lk), and val2 is the reverse of the items between the
; two zeros.  Recall that drat-hints needs to be in order of decreasing clause
; index.

  (mv-let (rup-indices drat-hints)
    (make-add-step-1 val2 nil)
    (make add-step
          :index j
          :clause clause
          :rup-indices rup-indices
          :drat-hints drat-hints)))

(defun parse-lrat-line (channel ctx state)

; Returns a proof-entry-p.

  (b* (((er val0)
        (read-to-0 channel nil ctx state))
       ((when (eq val0 :eof))
        (value :eof))
       ((when (null val0))
        (pprogn
         (close-input-channel channel state)
         (er soft ctx
             "Found empty first part of addition step.")))
       (val (reverse val0))
       ((when (equal-symbol-name (cadr val) "D"))
        (value (cons t ; flag the deletion
                     (cddr val))))
       ((cons j clause) val)
       ((er val2)
        (read-to-0 channel nil ctx state))
       ((when (eq val2 :eof))
        (pprogn
         (close-input-channel channel state)
         (er soft ctx
             "Missing the second part of addition step for index #~x0."
             j))))
    (value (make-add-step j clause val2))))

(defun parse-lrat-channel (channel ctx state step-lst)

; Warning: This function is responsible for closing the given input channel.

  (b* (((er step)
        (parse-lrat-line channel ctx state))
       ((when (eq step :eof))
        (pprogn
         (close-input-channel channel state)
         (value (reverse step-lst)))))
    (parse-lrat-channel channel ctx state (cons step step-lst))))

(defun parse-lrat-file (lrat-file state)
  (b* ((ctx (cons 'parse-lrat-file lrat-file))
       ((mv channel state)
        (open-input-channel lrat-file :object state))
       ((when (null channel))
        (er soft ctx
            "Unable to open input file ~x0 for input."
            lrat-file)))
    (parse-lrat-channel channel ctx state nil)))

(defun verify-lrat-proof-fn (cnf-file lrat-file incomplete-okp state)
  (b* (((er formula) (time$ (parse-cnf-file cnf-file state)))
       ((er proof) (time$ (parse-lrat-file lrat-file state))))
    (value (mv-let (v c)
             (time$ (valid-proofp formula proof))
             (and v
                  (or incomplete-okp
                      c))))))

(defmacro verify-lrat-proof (cnf-file lrat-file
                                      &optional (incomplete-okp 'nil))
  `(verify-lrat-proof-fn ,cnf-file ,lrat-file ,incomplete-okp state))

; Example:
; (verify-lrat-proof "tests/example-4-vars.cnf" "tests/example-4-vars.lrat")

; Some debugging tools.

(defun show-proof-entry (entry)
  (cond ((proof-entry-deletion-p entry)
         (cons 'deletion (cdr entry)))
        (t (list :index (access add-step entry :index)
                 :clause (access add-step entry :clause)
                 :rup-indices (access add-step entry :rup-indices)
                 :drat-hints (access add-step entry :drat-hints)))))

(defun show-lrat-proof (proof acc)
  (cond ((endp proof) (reverse acc))
        (t (show-lrat-proof (cdr proof)
                            (cons (show-proof-entry (car proof)) acc)))))

(defun show-lrat-parse (lrat-file state)
  (er-let* ((proof (parse-lrat-file lrat-file state)))
    (value (show-lrat-proof proof nil))))

(defun show-drat-hints-raw (drat-hints acc)
  (cond ((endp drat-hints) acc)
        (t (show-drat-hints-raw (cdr drat-hints)
                                (cons (- (caar drat-hints))
                                      (append (cdar drat-hints) acc))))))

(defun show-proof-entry-raw (index entry)
  (cond ((proof-entry-deletion-p entry)
         (list* index 'd (cdr entry)))
        (t (cons (access add-step entry :index)
                 (append (access add-step entry :clause)
                         (cons 0
                               (append (access add-step entry :rup-indices)
                                       (show-drat-hints-raw
                                        (access add-step entry :drat-hints)
                                        nil))))))))

(defun show-lrat-proof-raw (index proof acc)
  (cond ((endp proof) (reverse acc))
        (t (let ((entry-raw (show-proof-entry-raw index (car proof))))
             (show-lrat-proof-raw (car entry-raw)
                                  (cdr proof)
                                  (cons entry-raw acc))))))

(defun show-lrat-parse-raw (lrat-file state)
  (er-let* ((proof (parse-lrat-file lrat-file state)))
    (pprogn (acl2::print-on-separate-lines
             (show-lrat-proof-raw nil proof nil)
             nil *standard-co* state)
            (value :invisible))))

; Test driver

(defun lrat-test-fn (doublets dir okp chan state)
  (cond
   ((endp doublets)
    (pprogn (fms "OVERALL RESULT: ~s0~|~%"
                 (list (cons #\0 (if okp "success" "FAILURE")))
                 chan state nil)
            (value okp)))
   (t (let* ((d (car doublets))
             (cnf (concatenate 'string dir (car d)))
             (lrat (concatenate 'string dir (cadr d)))
             (incomplete-okp (caddr d)))
        (pprogn
         (fms "Starting ~x0.~|"
              (list (cons #\0 `(verify-lrat-proof ,cnf
                                                  ,lrat
                                                  ,@(cddr d))))
              chan state nil)
         (er-let* ((val (verify-lrat-proof cnf lrat incomplete-okp)))
           (pprogn
            (princ$ "Result: " chan state)
            (princ$ (if val "success" "FAILURE") chan state)
            (newline chan state)
            (lrat-test-fn (cdr doublets) dir (and val okp) chan state))))))))

(defmacro lrat-test (doublets &optional (dir '""))

; This should be run in the tests/ directory, or else in the directory dir
; relative to the current directory (e.g., "../tests" or "../tests/").

  (declare (xargs :guard (stringp dir))) ; partial guard
  (let ((dir (if (and (not (equal dir ""))
                      (not (eql (char dir (1- (length dir)))
                                #\/)))
                 (concatenate 'string dir "/")
               dir)))
    `(lrat-test-fn ',doublets ',dir t (standard-co state) state)))
