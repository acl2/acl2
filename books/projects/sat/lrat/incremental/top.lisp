; Copyright (C) 2017, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See ../README.

(in-package "LRAT")

(local (include-book "incremental"))
(include-book "../sorted/lrat-checker")
(include-book "clrat-parser")

(defun incl-verify-proof$-rec (ncls ndel formula proof a$)
  (declare (xargs :stobjs a$
                  :guard (and (a$p a$)
; See the comment in verify-clause$ about perhaps eliminating the next
; conjunct (which is perhaps not necessary).
                              (= (a$ptr a$) 0)
                              (integerp ncls) ; really natp; see comment below
                              (natp ndel)
                              (formula-p$ formula a$)
                              (proofp$ proof a$))
                  :guard-hints
                  (("Goal" :use ((:guard-theorem verify-proof$-rec))))))
  (cond
   ((atom proof) (mv t formula a$))
   (t
    (let* ((entry (car proof))
           (delete-flg (proof-entry-deletion-p entry)))
      (cond
       (delete-flg
        (let* ((indices (proof-entry-deletion-indices entry))
               (new-formula (delete-clauses indices formula))
               (len (length indices))
               (ncls

; We expect that (<= len ncls).  It is tempting to assert that here (with
; assert$), but it's not necessary so we avoid the overhead (mostly in proof,
; but perhaps also a bit in execution).

                (- ncls len))
               (ndel (+ ndel len)))
          (incl-verify-proof$-rec ncls ndel new-formula (cdr proof) a$)))
       (t ; addition
        (mv-let (ncls ndel new-formula a$)
          (verify-clause$ formula entry ncls ndel a$)
          (cond (ncls ; success
                 (incl-verify-proof$-rec
                  (1+ ncls)
                  ndel
                  (add-proof-clause (access add-step entry :index)
                                    (access add-step entry :clause)
                                    new-formula)
                  (cdr proof)
                  a$))
                (t (mv nil formula a$))))))))))

(defun incl-verify-proof$ (formula proof a$)
  (declare (xargs :stobjs a$
                  :guard (and (a$p a$)
; See the comment in verify-clause$ about perhaps eliminating the next
; conjunct (which is perhaps not necessary).
                              (= (a$ptr a$) 0)
                              (formula-p$ formula a$)
                              (proofp$ proof a$))))
  (incl-verify-proof$-rec (fast-alist-len formula)
                          0
                          formula
                          proof
                          a$))

(defun incl-initialize-a$ (max-var a$)
  (declare (xargs :stobjs a$
                  :guard (and (a$p a$)
                              (equal (a$ptr a$) 0)
                              (natp max-var))))
  (cond ((<= max-var (a$stk-length a$))
         a$)
        (t (let* ((new-max-var (* 2 max-var)))
             (initialize-a$ new-max-var a$)))))

(defun check-proofp (proof) ; primitive

; This variant of proofp causes an error when false, printing the offending
; entry.

  (declare (xargs :guard t))
  (if (atom proof)
      (null proof)
    (and (or (lrat-proof-entry-p (car proof))
             (er hard? 'check-proof
                 "Illegal proof entry: ~X01"
                 (car proof)
                 nil))
         (check-proofp (cdr proof)))))

(defun incl-valid-proofp$ (formula proof old-max-var a$)
  (declare (xargs :stobjs a$
                  :guard (and (a$p a$)
                              (eql (a$ptr a$) 0)
                              (formula-p formula)
                              (natp old-max-var)
                              (<= (formula-max-var formula 0)
                                  old-max-var))
                  :guard-hints (("Goal"
                                 :use ((:guard-theorem valid-proofp$))))))
  (let* ((formula (shrink-formula formula))
         (max-var (and (check-proofp proof)
                       (proof-max-var proof old-max-var))))
    (cond ((natp max-var)
           (let ((a$ (incl-initialize-a$ max-var a$)))
             (mv-let (v new-formula a$)
               (incl-verify-proof$ formula proof a$)
               (mv v
                   new-formula
                   (proof-contradiction-p proof)
                   max-var
                   a$))))
          (t (mv nil formula nil old-max-var a$)))))

(defun incl-valid-proofp$-top-rec (formula clrat-file posn chunk-size
                                           clrat-file-length old-suffix debug
                                           old-max-var a$ ctx state)
  (declare (xargs :guard (and (a$p a$)
                              (eql (a$ptr a$) 0)
                              (formula-p formula)
                              (stringp clrat-file)
                              (natp posn)
                              (< posn *2^56*)
                              (posp chunk-size)
                              (posp clrat-file-length)
                              (stringp old-suffix)
                              (natp old-max-var)
                              (<= (formula-max-var formula 0)
                                  old-max-var))
                  :ruler-extenders (:lambdas mv-list return-last) ; ugly bug work-around
                  :measure (nfix (- clrat-file-length posn))
                  :stobjs (state a$)))
  (cond
   ((and (mbt (natp posn))
         (mbt (posp clrat-file-length))
         (mbt (posp chunk-size))
         (<= posn clrat-file-length))
    (prog2$
     (and debug
          (cw "; Note: Reading from position ~x0~|" posn))
     (mv-let (proof suffix new-posn)
       (clrat-read-next clrat-file posn chunk-size old-suffix
                        clrat-file-length state)
       (cond
        ((null suffix) ; error (normally a string, possibly even "")
         (mv (er hard? ctx "Implementation error: Null suffix!")
             a$))
        ((null proof)
         (mv :incomplete a$))
        ((stringp proof) ; impossible
         (mv (er hard? ctx
                 "Implementation error: ~x0 returned a string for its proof, ~
                  which we thought was impossible!"
                 'clrat-read-next)
             a$))
        (t
         (mv-let (v new-formula c new-max-var a$)
           (prog2$
            (cw "; Note: Checking next proof segment.~|")
            (incl-valid-proofp$ formula proof old-max-var a$))
           (cond
            ((>= new-posn *2^56*)
             (mv (er hard? ctx
                     "Attempted to read at position ~x0, but the maximum ~
                      legal such position is 2^56 = ~x1."
                     new-posn *2^56*)
                 a$))
            ((not v) (mv nil a$))
            (c
             (mv :complete a$))
            ((> new-posn clrat-file-length)

; If new-posn is exactly clrat-file-length, then as per the discussion of the
; "truncation case"in :doc read-file-into-string, we need to iterate.  But if
; new-posn exceeds clrat-file-length, then we're done.

             (mv :incomplete a$))
            (t
             (incl-valid-proofp$-top-rec new-formula clrat-file new-posn
                                         chunk-size clrat-file-length suffix
                                         debug new-max-var a$ ctx
                                         state)))))))))
   (t ; impossible
    (mv nil a$))))

(defun incl-valid-proofp$-top-aux (formula clrat-file incomplete-okp chunk-size
                                           clrat-file-length debug a$ ctx state)
  (declare (xargs :stobjs (a$ state)
                  :guard (and (a$p a$)
                              (eql (a$ptr a$) 0)
                              (formula-p formula)
                              (stringp clrat-file)
                              (posp chunk-size)
                              (posp clrat-file-length))))
  (mv-let (val a$)
    (incl-valid-proofp$-top-rec formula clrat-file 0 chunk-size
                                clrat-file-length "" debug
                                (formula-max-var formula 0)
                                a$ ctx state)
    (case val
      (:complete (mv t a$))
      (:incomplete (mv (or incomplete-okp
                           (er hard? ctx
                               "Incomplete proof!"))
                       a$))
      (t (mv (er hard? ctx
                 "Invalid proof!")
             a$)))))

; Verify-termination doesn't work here because of how ACL2 handles make-event
; during certification.  Hopefully this will be fixed.
; (verify-termination acl2::world-evisceration-alist
;   (declare (xargs :verify-guards t)))
#!acl2
(encapsulate
  ()
  (set-state-ok t)
  (defun world-evisceration-alist (state alist)
    (declare (xargs :verify-guards t))
    (let ((wrld (w state)))
      (cond ((null wrld) ; loading during the build
             alist)
            (t (cons (cons wrld *evisceration-world-mark*)
                     alist))))))

#!acl2
(defun abbrev-evisc-tuple-logic (state)

; This is modified from ACL2 source function abbrev-evisc-tuple.

  (declare (xargs :stobjs state))
  (let ((evisc-tuple (if (f-boundp-global 'abbrev-evisc-tuple state)
                         (f-get-global 'abbrev-evisc-tuple state)
                       :default)))
    (cond
     ((eq evisc-tuple :default)
      (cons (world-evisceration-alist state nil)
            '(5 7 nil)))
     (t evisc-tuple))))

#!acl2
(defun error-fms-soft-logic (ctx str alist state)

; This is modified from ACL2 source function error-fms.

  (declare (xargs :stobjs state))
  (fmt-to-comment-window "~%~%ACL2 Error in ~x0:  ~@1~%~%"
                         (list (cons #\0 ctx)
                               (cons #\1 (cons str alist)))
                         0
                         (acl2::abbrev-evisc-tuple-logic state)))

#!acl2
(defun error1-logic (ctx str alist state)

; This is modified from ACL2 source function error1.

  (declare (xargs :stobjs state))
  (prog2$ (error-fms-soft-logic ctx str alist state)
          (mv t nil state)))

(defmacro er-soft-logic (ctx str &rest str-args)
  (let ((alist (acl2::make-fmt-bindings '(#\0 #\1 #\2 #\3 #\4
                                          #\5 #\6 #\7 #\8 #\9)
                                        str-args)))
    (list 'acl2::error1-logic ctx str alist 'state)))

(defun ordered-formula-p1 (formula index)
  (declare (xargs :guard (posp index)))
  (if (atom formula)
      (null formula)
    (let ((pair (car formula)))
      (and (consp pair)
           (posp (car pair))
           (clause-or-assignment-p (cdr pair))
           (< (car pair) index)
           (ordered-formula-p1 (cdr formula) (car pair))))))

(defund ordered-formula-p (formula)

; It is important that the formula produced by the cnf parser does not have
; duplicate indices, since otherwise the first call of shrink-formula will
; change its semantics.  Fortunately, the cnf parser presents the formula in
; reverse order; so we can check for duplicate-free indices in linear time.

  (declare (xargs :guard t))
  (if (atom formula)
      (null formula)
    (let ((pair (car formula)))
      (and (consp pair)
           (posp (car pair))
           (clause-or-assignment-p (cdr pair))
           (ordered-formula-p1 (cdr formula) (car pair))))))

(defun incl-valid-proofp$-top (cnf-file clrat-file incomplete-okp chunk-size
                                        debug ctx state)
  (declare (xargs :guard t :stobjs state))
  (let ((formula (time$ (ec-call (cnf-read-file cnf-file state)))))
    (cond
     ((not (stringp clrat-file))
      (er-soft-logic
       ctx
       "The filename argument is not a string:~|~x0"
       clrat-file))
     ((not (posp chunk-size))
      (er-soft-logic
       ctx
       "The supplied :chunk-size must be a positive integer, but ~x0 is ~
        not.~|~x0"
       clrat-file))
     ((not (ordered-formula-p formula))
      (er-soft-logic ctx "An invalid formula was supplied by the parser!"))
     (t
      (mv-let (clrat-file-length state)
        (file-length$ clrat-file state)
        (cond
         ((posp clrat-file-length)
          (prog2$
           (and debug
                (cw "Length of file ~x0: ~x1~|" clrat-file clrat-file-length))
           (value
            (with-fast-alist
              formula
              (with-local-stobj a$
                (mv-let
                  (val a$)
                  (let ((a$ (resize-a$arr 2 a$))) ; to get a$p to hold
                    (incl-valid-proofp$-top-aux formula
                                                clrat-file
                                                incomplete-okp chunk-size
                                                clrat-file-length debug a$
                                                ctx state))
                  (cons val formula)))))))
         ((eql clrat-file-length 0)
          (er-soft-logic
           ctx
           "Zero-length file: ~x0."
           clrat-file))
         (t (er-soft-logic
             ctx
             "Sorry, Lisp cannot determine the file-length of file ~x0."
             clrat-file))))))))

(defun incl-verify-proof-fn (cnf-file clrat-file incomplete-okp chunk-size
                                      debug state)

; This is just a little interface to incl-valid-proofp$-top.

  (declare (xargs :guard t
                  :guard-hints (("Goal"
                                 :in-theory
                                 (disable incl-valid-proofp$-top-aux
                                          cnf-read-file
                                          file-length$)))
                  :stobjs state))
  (er-let* ((val/formula
             (time$ (incl-valid-proofp$-top cnf-file clrat-file incomplete-okp
                                            chunk-size debug 'incl-verify-proof
                                            state))))
    (value (car val/formula))))

(defconst *256mb*
  (expt 2 28))

(defconst *default-chunk-size*
  *256mb*)

(defmacro incl-verify-proof (cnf-file clrat-file
                                      &key
                                      incomplete-okp
                                      chunk-size
                                      (debug 't))
  `(incl-verify-proof-fn ,cnf-file ,clrat-file ,incomplete-okp
                         ,(or chunk-size *default-chunk-size*)
                         ,debug
                         state))
