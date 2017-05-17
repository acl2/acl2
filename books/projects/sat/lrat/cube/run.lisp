; Copyright (C) 2017, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See README.

(in-package "LRAT")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Preliminaries
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "transform")
(include-book "verify-for-cube-soundness")
(include-book "../incremental/print-formula")
(include-book "../incremental/soundness")

(program)
(set-state-ok t)

(defun my-getenv (string state)
  (mv-let (erp s state)
    (getenv$ string state)
    (mv (and (not erp)
             (let ((s1 (string-upcase s)))
               (cond ((equal s1 "T")
                      t)
                     ((equal s1 "NIL")
                      nil)
                     (t s))))
        state)))

(defun get-defaults (chunk-size debug timep exitp state)
  (mv-let (chunk-size state)
    (cond
     ((eq chunk-size :none)
      (mv-let (s state)
        (my-getenv "LRAT_CHUNK_SIZE" state)
        (mv (if (stringp s)
                (acl2::decimal-string-to-number s (length s) 0)
              1000000)
            state)))
     (t (mv chunk-size state)))
    (mv-let (debug state)
      (cond ((eq debug :none)
             (my-getenv "LRAT_DEBUG" state))
            (t (mv debug state)))
      (mv-let (timep state)
        (cond ((eq timep :none)
               (my-getenv "LRAT_TIMEP" state))
              (t (mv timep state)))
        (mv-let (exitp state)
          (cond ((eq exitp :none)
                 (my-getenv "LRAT_EXITP" state))
                (t (mv exitp state)))
          (mv chunk-size debug timep exitp state))))))

(defun maybe-print-success-and-exit (exitp state)
  (cond ((null exitp) (value nil))
        (t (pprogn (princ$ "s VERIFIED" (standard-co state) state)
                   (newline (standard-co state) state)
                   (prog2$ (exit 0)
                           (value nil))))))

(defun maybe-print-failure-and-exit (exitp state)
  (cond ((null exitp) (value nil))
        (t (pprogn (princ$ "FAILED" (standard-co state) state)
                   (prog2$ (exit 1)
                           (value nil))))))

(defmacro maybe-time$ (timep form)
  `(cond (,timep (time$ ,form))
         (t ,form)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Transform
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; See (1) in README.

(defun transform-check-fn (cnf-file clrat-file chunk-size
                                    debug
                                    old-formula-outfile
                                    new-formula-outfile
                                    timep
                                    exitp
                                    ctx
                                    state)
  (declare (xargs :stobjs state :mode :program))
  (mv-let (chunk-size debug timep exitp state)
    (get-defaults chunk-size debug timep exitp state)
    (mv-let (erp result state)
      (maybe-time$ timep (transform cnf-file clrat-file chunk-size debug state))
      (cond
       ((and (null erp)
             result)
        (let ((old-formula (car result))
              (new-formula (cdr result)))
          (er-progn
           (cond ((null old-formula-outfile) (value nil))
                 (t (pprogn (cond ((eq old-formula-outfile t)
                                   (fms "~s0 Input formula ~s0~|"
                                        (list (cons #\0 "==============="))
                                        (standard-co state) state nil))
                                  (t state))
                            (print-formula (reverse old-formula)
                                           :filename old-formula-outfile))))
           (cond ((null new-formula-outfile) (value nil))
                 (t (pprogn (cond ((eq new-formula-outfile t)
                                   (fms "~s0 Output formula ~s0~|"
                                        (list (cons #\0 "==============="))
                                        (standard-co state) state nil))
                                  (t state))
                            (print-formula new-formula
                                           :filename new-formula-outfile))))
           (maybe-print-success-and-exit exitp state)
           (value `(:SUCCESS
                    ,@(and (stringp old-formula-outfile)
                           (list :input-formula-printed-to
                                 old-formula-outfile))
                    ,@(and (stringp new-formula-outfile)
                           (list :output-formula-printed-to
                                 new-formula-outfile)))))))
       (t (er-progn (maybe-print-failure-and-exit exitp state)
                    (er soft ctx "Transform FAILED.")))))))

(defmacro transform-check (cnf-file clrat-file
                                    &key
                                    old-formula-outfile
                                    new-formula-outfile
                                    (chunk-size ':none)
                                    (debug ':none)
                                    (timep ':none)
                                    (exitp ':none))
  `(transform-check-fn ,cnf-file ,clrat-file
                       ,chunk-size ,debug
                       ,old-formula-outfile ,new-formula-outfile ,timep ,exitp
                       'transform-check state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Verify-for-cube
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; See (2) in README.

(defun verify-for-cube-check-fn (cnf-file clrat-file cube-file chunk-size debug
                                          old-formula-outfile new-clause-outfile
                                          timep exitp ctx state)
  (declare (xargs :stobjs state :mode :program))
  (mv-let (chunk-size debug timep exitp state)
    (get-defaults chunk-size debug timep exitp state)
    (mv-let (erp formula/clause state)
      (maybe-time$ timep
                   (verify-for-cube cnf-file clrat-file cube-file chunk-size
                                    debug ctx state))
      (assert$
       (null erp)
       (cond
        (formula/clause
         (let ((formula (reverse (car formula/clause)))
               (clause (cdr formula/clause)))
           (er-progn
            (cond ((null old-formula-outfile) (value nil))
                  (t (pprogn (cond ((eq old-formula-outfile t)
                                    (fms "~s0 Formula ~s0~|"
                                         (list (cons #\0 "==============="))
                                         (standard-co state) state nil))
                                   (t state))
                             (print-formula formula
                                            :filename old-formula-outfile))))
            (cond ((null new-clause-outfile) (value nil))
                  (t (pprogn (cond ((eq new-clause-outfile t)
                                    (fms "~s0 Clause ~s0~|"
                                         (list (cons #\0 "==============="))
                                         (standard-co state) state nil))
                                   (t state))
                             (print-formula ; turn clause into a formula
                              (list (cons 1 clause))
                              :filename new-clause-outfile
                              :header-p nil))))
            (maybe-print-success-and-exit exitp state)
            (value `(:SUCCESS
                     ,@(and (stringp old-formula-outfile)
                            (list :formula-printed-to old-formula-outfile))
                     ,@(and (stringp new-clause-outfile)
                            (list :clause-printed-to new-clause-outfile)))))))
        (t (er-progn (maybe-print-failure-and-exit exitp state)
                     (er soft ctx "Verify-for-cube FAILED."))))))))

(defmacro verify-for-cube-check (cnf-file clrat-file cube-file
                                          &key
                                          old-formula-outfile
                                          new-clause-outfile
                                          (chunk-size ':none)
                                          (debug ':none)
                                          (timep ':none)
                                          (exitp ':none))
  `(verify-for-cube-check-fn ,cnf-file ,clrat-file ,cube-file
                             ,chunk-size ,debug
                             ,old-formula-outfile ,new-clause-outfile ,timep
                             ,exitp 'verify-for-cube-check state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Cubes-unsat-check
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; See (3) in README.

(defun cubes-unsat-check-fn (cnf-file clrat-file chunk-size debug outfile
                                      timep exitp ctx state)
  (mv-let (chunk-size debug timep exitp state)
    (get-defaults chunk-size debug timep exitp state)
    (mv-let (erp formula state)
      (maybe-time$ timep
                   (proved-formula cnf-file clrat-file
                                   chunk-size
                                   debug
                                   nil ; incomplete-okp
                                   'cubes-unsat-check state))
      (cond ((and (null erp) ; always true
                  formula)
             (pprogn (cond ((eq outfile t)
                            (fms "~s0 Input formula ~s0~|"
                                 (list (cons #\0 "==============="))
                                 (standard-co state) state nil))
                           (t state))
                     (er-progn
                      (cond (outfile (print-formula formula
                                                    :filename outfile))
                            (t (value nil)))
                      (maybe-print-success-and-exit exitp state)
                      (value `(:SUCCESS
                               ,@(and (stringp outfile)
                                      (list :input-formula-printed-to
                                            outfile)))))))
            (t
             (er-progn (maybe-print-failure-and-exit exitp state)
                       (er soft ctx "Cubes-unsat-check FAILED.")))))))

(defmacro cubes-unsat-check (cnf-file clrat-file
                                      &key
                                      outfile
                                      (chunk-size ':none)
                                      (debug ':none)
                                      (timep ':none)
                                      (exitp ':none))
  `(cubes-unsat-check-fn ,cnf-file ,clrat-file ,chunk-size ,debug ,outfile
                         ,timep ,exitp 'cubes-unsat-check state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Single interface
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro cube-check (cnf-infile clrat-infile cnf-outfile
                                 &optional cube-infile produced-outfile)
  (cond (cube-infile ; (2)
         `(verify-for-cube-check ,cnf-infile ,clrat-infile ,cube-infile
                                 :old-formula-outfile ,cnf-outfile
                                 :new-clause-outfile ,produced-outfile))
        (produced-outfile ; (1)
         `(transform-check ,cnf-infile ,clrat-infile
                           :old-formula-outfile ,cnf-outfile
                           :new-formula-outfile ,produced-outfile))
        (t ; (3)
         `(cubes-unsat-check ,cnf-infile ,clrat-infile
                             :outfile ,cnf-outfile))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Some environment variable settings to try:
; (setenv$ "LRAT_TIMEP" "t")
; (setenv$ "LRAT_TIMEP" "nil")
; (setenv$ "LRAT_CHUNK_SIZE" "200")

#||

(transform-check "../tests/uuf-100-5.cnf" "../tests/uuf-100-5-partial.clrat"
                 :old-formula-outfile "my-old"
                 :new-formula-outfile "my-new")
% diff ../tests/uuf-100-5.cnf my-old
; equivalently
(cube-check "../tests/uuf-100-5.cnf" "../tests/uuf-100-5-partial.clrat"
            "my-old2" nil "my-new2")
; equivalently
./run.sh ../tests/uuf-100-5.cnf ../tests/uuf-100-5-partial.clrat my-old2 nil my-new2

% diff my-old my-old2
% diff my-new my-new2

(let ((cnf-file "../tests/uuf-30-1.cnf")
      (clrat-file "../tests/uuf-30-1-cube.clrat")
      (cube-file "../tests/uuf-30-1.cube"))
  (verify-for-cube-check cnf-file clrat-file cube-file
                         :old-formula-outfile "my-old"
                         :new-clause-outfile "my-new"))
% diff ../tests/uuf-30-1.cnf my-old
% # should be just -25 0:
% cat my-new
; equivalently
(cube-check "../tests/uuf-30-1.cnf" "../tests/uuf-30-1-cube.clrat"
            "my-old2" "../tests/uuf-30-1.cube" "my-new2")
% diff my-old my-old2
% diff my-new my-new2
; equivalently
./run.sh ../tests/uuf-30-1.cnf ../tests/uuf-30-1-cube.clrat my-old2 \
          ../tests/uuf-30-1.cube my-new2

(let ((cnf-file "../tests/uuf-30-1.cnf")
      (clrat-file "../tests/uuf-30-1.clrat"))
  (cubes-unsat-check cnf-file clrat-file
                     :outfile t))
; equivalently:
(cube-check "../tests/uuf-30-1.cnf" "../tests/uuf-30-1.clrat" t)
; File version:
(let ((cnf-file "../tests/uuf-30-1.cnf")
      (clrat-file "../tests/uuf-30-1.clrat"))
  (cubes-unsat-check cnf-file clrat-file
                     :outfile "my-old"))
; equivalently:
./run.sh ../tests/uuf-30-1.cnf ../tests/uuf-30-1.clrat my-old2
% diff my-old my-old2

||#
