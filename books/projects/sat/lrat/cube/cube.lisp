; Copyright (C) 2017, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See README.

(in-package "LRAT")

(include-book "../incremental/incremental")

(defun parse-cube-file2 (channel acc ctx state n)
  (declare (xargs :stobjs state
                  :guard (and (symbolp channel)
                              (open-input-channel-p channel :object state)
                              (true-listp acc)
                              (natp n))
                  :measure (nfix n)))
  (cond
   ((zp n)
    (er-soft-logic ctx
                   "Read zillions of literals and gave up!  We thought this ~
                    was impossible."))
   (t (mv-let (eof obj state)
        (read-object channel state)
        (cond (eof (value (reverse acc)))
              (t (parse-cube-file2 channel (cons obj acc) ctx state
                                   (1- n))))))))

(defun parse-cube-file1 (channel ctx state)
  (declare (xargs :stobjs state
                  :guard (open-input-channel-p channel :object state)
                  :verify-guards nil))
  (er-let* ((ans (parse-cube-file2 channel nil ctx state
                                   100000000)))
    (pprogn (close-input-channel channel state)
            (value ans))))

(defthm true-listp-reverse
  (implies (not (stringp x))
           (true-listp (reverse x)))
  :hints (("Goal" :in-theory (enable reverse)))
  :rule-classes :type-prescription)

(defthm true-listp-mv-nth-1-parse-cube-file2
  (implies (true-listp acc)
           (true-listp (mv-nth 1 (parse-cube-file2 channel acc ctx state n))))
  :hints (("Goal" :in-theory (enable acl2::error1-logic))))

(defthm true-listp-mv-nth-1-parse-cube-file
  (true-listp (mv-nth 1 (parse-cube-file1 cube-file ctx state)))
  :rule-classes :type-prescription)

(in-theory (disable parse-cube-file1))

(defun parse-cube-file (cube-file ctx state)

; Returns an error triple whose value (in the non-error case) is the contents
; of cube-file after the initial "a".

  (declare (xargs :stobjs state
                  :guard (stringp cube-file)))
  (mv-let (channel state)
    (open-input-channel cube-file :object state)
    (cond
     ((null channel)
      (er-soft-logic ctx
                     "Cube file not found: ~x0."
                     cube-file))
     (t
      (mv-let (eofp obj state)

; GCL versions before approximately 2017 do not support read-object-with-case,
; because system::set-readtable-case is not defined.  If we want to support GCL
; here, the simplest solution is to call read-object instead of
; read-object-with-case channel :preserve state) (perhaps conditional on (@
; host-lisp) = :GCL) and then test for symbol-name "A" instead of "a".

        (acl2::read-object-with-case channel :preserve state)
        (cond
         (eofp (er-soft-logic ctx
                              "End-of-file encountered before completing read ~
                               for one form in cube file ~x0."
                              cube-file))
         ((not (and (symbolp obj)
                    (equal (symbol-name obj) "a")))
          (er-soft-logic
           ctx
           "Cube file ~x0 starts with ~x1, not with the letter a ."
           cube-file obj))
         (t (er-let* ((lst (ec-call (parse-cube-file1 channel ctx state))))
              (cond
               ((not (eql (car (last lst)) 0))
                (er-soft-logic
                 ctx
                 "Cube input file ~x0 does not end with 0."
                 cube-file))
               (t (value (butlast lst 1))))))))))))

(defun extend-formula-with-cube1 (formula cube next-index)
  (declare (xargs :guard (and (formula-p formula)
                              (literal-listp cube)
                              (posp next-index))
                  :guard-hints (("Goal"
                                 :in-theory (enable formula-p clausep
                                                    conflicting-literalsp
                                                    literal-listp
                                                    literalp
                                                    unique-literalsp)))))
  (cond ((endp cube) formula)
        (t (extend-formula-with-cube1
            (acons next-index (list (car cube)) formula)
            (cdr cube)
            (1+ next-index)))))

(defun formula-max-index (formula)
  (declare (xargs :guard (ordered-formula-p formula)
                  :guard-hints (("Goal" :in-theory (enable ordered-formula-p)))))
  (cond ((endp formula) 1) ; probably don't care, so return posp
        (t (caar formula))))

(defthm posp-formula-max-index
  (implies (force (formula-p formula))
           (posp (formula-max-index formula)))
  :rule-classes :type-prescription)

(defun extend-formula-with-cube (formula cube)
  (declare (xargs :guard (and (ordered-formula-p formula)
                              (literal-listp cube))
                  :guard-hints (("Goal"
                                 :in-theory
                                 (e/d (formula-p)
                                      (ordered-formula-p-implies-formula-p))
                                 :use ordered-formula-p-implies-formula-p))))
  (let ((next-index (1+ (formula-max-index formula))))
    (extend-formula-with-cube1 formula cube next-index)))

(defun negate-cube (cube)
  (declare (xargs :guard (literal-listp cube)
                  :guard-hints (("Goal" :in-theory (enable literal-listp)))))
  (cond ((endp cube) nil)
        (t (cons (negate (car cube))
                 (negate-cube (cdr cube))))))

(in-theory (disable extend-formula-with-cube parse-cube-file))

(defthm formula-p-extend-formula-with-cube1
  (implies (and (formula-p formula)
                (literal-listp cube)
                (posp next-index))
           (formula-p (extend-formula-with-cube1 formula cube next-index)))
  :hints (("Goal" :in-theory (enable literal-listp
                                     formula-p
                                     extend-formula-with-cube1
                                     clausep
                                     conflicting-literalsp
                                     literal-listp
                                     literalp
                                     unique-literalsp))))

(defthm formula-p-extend-formula-with-cube
  (implies (and (formula-p formula)
                (literal-listp cube))
           (formula-p (extend-formula-with-cube formula cube)))
  :hints (("Goal" :in-theory (enable extend-formula-with-cube formula-p))))

(defun cube-valid-proofp$-top (cnf-file clrat-file cube-file incomplete-okp
                                        chunk-size debug ctx state)

; Keep in sync with incl-valid-proofp$-top.

  (declare (xargs :stobjs state
                  :guard-hints (("Goal"
                                 :in-theory (enable formula-p
                                                    clausep
                                                    acl2::error1-logic
                                                    conflicting-literalsp
                                                    literal-listp
                                                    literalp
                                                    unique-literalsp)))))
  (let ((input-formula (ec-call (cnf-read-file cnf-file state))))
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
     ((not (ordered-formula-p input-formula))
      (er-soft-logic ctx "An invalid formula was read by the parser!"))
     ((not (stringp cube-file))
      (er-soft-logic ctx
                     "The cube-file argument must be a strong.  Hence the ~
                      argument ~x0 is illegal."
                     cube-file))
     (t
      (mv-let (clrat-file-length state)
        (file-length$ clrat-file state)
        (er-let* ((cube (parse-cube-file cube-file ctx state)))
          (cond
           ((not (clausep cube))
            (er-soft-logic
             ctx
             "Cube input file ~x0 is illegal: it begins with `a' and ends ~
              with 0, but there is a non-literal in the middle."
             cube-file))
           (t
            (let ((formula0 (extend-formula-with-cube input-formula cube)))
              (cond
               ((posp clrat-file-length)
                (prog2$
                 (and debug
                      (cw "Length of file ~x0: ~x1~|"
                          clrat-file clrat-file-length))
                 (value
                  (with-fast-alist
                    formula0
                    (with-local-stobj a$
                      (mv-let
                        (val a$)
                        (let ((a$ (resize-a$arr 2 a$))) ; to get a$p to hold
                          (incl-valid-proofp$-top-aux formula0
                                                      clrat-file
                                                      incomplete-okp chunk-size
                                                      clrat-file-length debug a$
                                                      ctx state))
                        (list* val input-formula cube)))))))
               ((eql clrat-file-length 0)
                (er-soft-logic
                 ctx
                 "Zero-length file: ~x0."
                 clrat-file))
               (t (er-soft-logic
                   ctx
                   "Sorry, Lisp cannot determine the file-length of file ~x0."
                   clrat-file))))))))))))

; Lemma for guard proof for verify-for-cube:
(defthm alistp-extend-formula-with-cube
  (implies (and (formula-p formula)
                (literal-listp cube))
           (alistp (extend-formula-with-cube formula cube)))
  :hints (("Goal" :in-theory (enable extend-formula-with-cube formula-p))))

(defthm true-listp-extend-formula-with-cube
  (implies (and (formula-p formula)
                (literal-listp cube))
           (true-listp (extend-formula-with-cube formula cube)))
  :hints (("Goal" :in-theory (enable extend-formula-with-cube formula-p))))

(defthm alistp-revappend
  (implies (and (alistp x)
                (alistp y))
           (alistp (revappend x y))))

(defthm alistp-reverse
  (implies (alistp x)
           (alistp (reverse x)))
  :hints (("Goal" :in-theory (enable reverse))))

(defun verify-for-cube (cnf-file clrat-file cube-file chunk-size debug ctx
                                 state)

; This function is somewhat based on proved-formula (defined in
; ../incremental/soundness.lisp).  Here we return an error triple whose
; component, in the non-error case, is (cons cl-list cl) where cl-list is the
; list of clauses read from cnf-file, cl is the negation of the cube read from
; cube-file, and cl-list U {cl} is unsatisfiable.

  (declare (xargs :stobjs state
                  :guard-hints (("Goal"
                                 :in-theory (disable reverse file-length$
                                                     incl-valid-proofp$-top-aux
                                                     cnf-read-file)))))
  (mv-let (erp val/formula/cube state)
    (cube-valid-proofp$-top cnf-file clrat-file cube-file
                            nil ; incomplete-okp
                            chunk-size debug ctx state)
    (value (and (null erp)
                (consp val/formula/cube)
                (eq (car val/formula/cube) t)

; Notice that the formula is returned as an ordered-formula-p.  We can print
; it back out in its original (reverse) order.

                (cons (cadr val/formula/cube)
                      (negate-cube (cddr val/formula/cube)))))))

; A little test:
(local
 (encapsulate
   ()
   (local (include-book "std/testing/assert-bang-stobj" :dir :system))
   (local (acl2::assert!-stobj
           #+gcl

; Versions of GCL predating 2017 or so do not define
; system::set-readtable-case, which makes read-object-with-case cause an error.
; If we want to be able to use verify-for-cube with GCL, simply change the call
; of read-object-with-case as indicated above.

           (mv t state)
           #-gcl
           (mv-let
             (erp formula/cube state)
             (let ((cnf-file "../tests/uuf-30-1.cnf")
                   (clrat-file "../tests/uuf-30-1-cube.clrat")
                   (cube-file "../tests/uuf-30-1.cube")
                   (chunk-size 1000000)
                   (debug t)
                   (ctx 'top))
               (verify-for-cube cnf-file clrat-file cube-file chunk-size debug ctx
                                state))
             (let ((cnf (reverse (strip-cdrs (car formula/cube))))
                   (cube (cdr formula/cube)))
               (mv (and (not erp)
                        (equal cnf
                               '((-7 23 15)
                                 (-25 -5 21)
                                 (4 29 30)
                                 (17 3 11)
                                 (25 28 6)
                                 (27 -29 20)
                                 (-4 28 13)
                                 (9 28 -6)
                                 (16 -19 18)
                                 (-9 -25 -20)
                                 (-26 21 -23)
                                 (24 -19 30)
                                 (24 19 15)
                                 (11 -22 -6)
                                 (-2 9 -16)
                                 (4 -30 -22)
                                 (-26 -28 3)
                                 (-17 25 4)
                                 (-10 18 -20)
                                 (-27 20 -16)
                                 (-26 -28 12)
                                 (-4 20 -13)
                                 (-9 24 4)
                                 (-21 5 6)
                                 (-2 29 -16)
                                 (17 -19 21)
                                 (19 11 -22)
                                 (24 10 6)
                                 (26 23 -8)
                                 (9 30 -23)
                                 (-26 27 3)
                                 (-2 10 3)
                                 (9 -11 26)
                                 (-1 22 -16)
                                 (-1 27 -16)
                                 (-10 -24 -16)
                                 (-26 4 13)
                                 (-18 4 6)
                                 (19 4 -30)
                                 (11 4 -22)
                                 (-12 -14 -8)
                                 (-26 -21 30)
                                 (10 27 11)
                                 (-27 -29 30)
                                 (2 -28 -24)
                                 (16 -29 15)
                                 (-3 18 29)
                                 (-3 18 30)
                                 (-2 -3 -22)
                                 (1 18 29)
                                 (17 -28 -30)
                                 (24 -16 -8)
                                 (18 5 30)
                                 (-17 12 7)
                                 (-12 -14 23)
                                 (-19 3 13)
                                 (1 -12 5)
                                 (4 -13 -23)
                                 (16 9 -12)
                                 (9 -20 -7)
                                 (25 30 -8)
                                 (-1 -25 23)
                                 (26 19 -7)
                                 (3 -13 -15)
                                 (-17 -1 18)
                                 (8 -19 -13)
                                 (11 -15 -16)
                                 (-5 20 -15)
                                 (-11 27 3)
                                 (-9 20 -13)
                                 (2 3 -16)
                                 (18 -27 4)
                                 (8 9 -13)
                                 (19 13 30)
                                 (-26 -18 1)
                                 (9 11 29)
                                 (18 -4 23)
                                 (24 -1 26)
                                 (1 18 12)
                                 (-17 -12 -30)
                                 (10 -4 23)
                                 (-11 -13 -24)
                                 (13 -23 14)
                                 (-10 -22 23)
                                 (-18 -21 -24)
                                 (16 -26 -30)
                                 (-25 13 -24)
                                 (-10 -19 -27)
                                 (-25 23 -16)
                                 (-3 -27 11)
                                 (28 -30 7)
                                 (-3 12 -23)
                                 (17 20 29)
                                 (18 -3 5)
                                 (19 4 28)
                                 (-1 25 -6)
                                 (-27 14 30)
                                 (29 13 21)
                                 (16 28 -22)
                                 (25 6 7)
                                 (2 11 -13)
                                 (10 4 -8)
                                 (25 -11 14)
                                 (-26 2 -27)
                                 (8 -10 -15)
                                 (24 4 -16)
                                 (-10 18 -23)
                                 (-26 -6 -7)
                                 (8 9 6)
                                 (-17 -29 -21)
                                 (-1 -27 2)
                                 (-26 11 -24)
                                 (2 27 -13)
                                 (-25 9 3)
                                 (16 10 23)
                                 (17 11 -21)
                                 (25 -20 -12)
                                 (-26 -3 -15)
                                 (24 25 18)
                                 (-17 -13 -8)
                                 (-1 11 -23)
                                 (17 -14 23)
                                 (8 28 6)
                                 (3 -13 12)
                                 (-11 -28 14)
                                 (25 -6 29)
                                 (28 -23 7)))
                        (equal cube
                               '(-25)))
                   state)))
           state))))
