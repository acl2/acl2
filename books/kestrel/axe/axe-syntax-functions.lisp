; General-purpose syntactic tests
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book contains general-purpose functions that support Axe rules
;; that call axe-syntaxp and axe-bind-free.

;; TODO: Some of these are not needed any more; we could remove them from the base-evaluator...

(include-book "misc/total-order" :dir :system) ;to get <<
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "axe-syntax")
(include-book "dag-arrays")
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(defund axe-quotep (item)
  (declare (xargs :guard (dargp item)))
  (consp item) ;; means that it is a quotep, not a nodenum
  )

;; might be better to check not consp, if we know the thing is a dag-item
;todo: deprecate now that things can be negated
(defun not-quotep (item)
  (declare (xargs :guard (dargp item)))
  (not (quotep item)))

;;TODO: Change these to never compare nodenums (can cause simplification to loop if things keep getting commuted due to different nodenums?)

;move these?

;; (defun arg1-safe (fn expr)
;;   (declare (xargs :guard (true-listp expr))) ;think about this
;;   (if (equal fn (ffn-symb expr))
;;       (farg1 expr)
;;     (hard-error 'arg1-safe "Found an unexpected expr: ~x0.  We expected one that started with ~x1" (acons #\0 expr (acons #\1 fn nil)))))

;; (defun arg2-safe (fn expr)
;;   (declare (xargs :guard (true-listp expr))) ;think about this
;;   (if (equal fn (ffn-symb expr))
;;       (farg2 expr)
;;     (hard-error 'arg2-safe "Found an unexpected expr: ~x0.  We expected one that started with ~x1" (acons #\0 expr (acons #\1 fn nil)))))

;; (defun arg3-safe (fn expr)
;;   (declare (xargs :guard (true-listp expr))) ;think about this
;;   (if (equal fn (ffn-symb expr))
;;       (farg3 expr)
;;     (hard-error 'arg3-safe "Found an unexpected expr: ~x0.  We expected one that started with ~x1" (acons #\0 expr (acons #\1 fn nil)))))


; Check whether x is 'heavier' than y.  Helps us decide when to reorder terms
; (e.g., to put 'light terms first).  x and y are either quoteps or nodenums.
(defund heavier-dag-term (x y)
  (declare (xargs :guard (and (dargp x)
                              (dargp y))))
  (if (quotep x)
      (if (quotep y)
          (<< (unquote y) (unquote x))
        nil)
    (if (quotep y)
        t
      ;;both are nodenums
      (< y x))))

(defun get-expr (nodenum-or-quotep dag-array)
  (declare (xargs :guard (or (myquotep nodenum-or-quotep)
                             (and (array1p 'dag-array dag-array) ;could pull out as a top-level conjunct
                                  (valid-array-indexp nodenum-or-quotep 'DAG-ARRAY DAG-ARRAY)))))
  (if (integerp nodenum-or-quotep)
      (aref1 'dag-array dag-array nodenum-or-quotep)
    nodenum-or-quotep))

;; (skip- proofs
;;  (mutual-recursion
;;   (defun print-objs (objs)
;;     (if (atom objs)
;;         (if objs
;;             (cw " . ~y0" objs)
;;           nil)
;;       (prog2$ (print-obj (car objs))
;;               (print-objs (cdr objs)))))

;;   (defun print-obj (obj)
;;     (declare (xargs :measure (make-ord 1 (len obj) nil)))
;;     (if (atom obj)
;;         (cw "~y0 " obj)
;;       (prog2$ (cw "(") ;print the first element separately to avoid a space before it
;;               (prog2$ (print-objs obj)
;;                       (cw ")~%")))))))

;; (skip- proofs (verify-guards print-obj))

;;decides whether to reverse the equality of x and y, which are nodenums or quoteps
;recall that we substitute the left value for the right value, so the left value should be the "nicer" of the two.
;fixme considering redoing substitution
(defund should-reverse-equality (x y dag-array)
  (declare (xargs :guard (and (or (myquotep x)
                                  (and (natp x)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 x))))
                              (or (myquotep y)
                                  (and (natp y)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 y)))))
                  :guard-hints (("Goal" :in-theory (enable array1p))))
           (ignore dag-array))
  (if (quotep x)
      nil
    (if (quotep y)
        t

      ;;recent change... if we put this back, add a check that the prefered term isn't a superterm of the other term..


      (if nil ;(and (BV-TERM-SYNTAXP y dag-array) ;store in variable!
          ;;(not (BV-TERM-SYNTAXP x dag-array)))
          t
        (if nil ;(and (not (BV-TERM-SYNTAXP y dag-array))
            ;; (BV-TERM-SYNTAXP x dag-array))
            nil
          ;;compare the nodenums - yuck?!  i've seen loops where this put in a gross term for a nice term
          (< y x))))))

;(skip- proofs (verify-guards should-reverse-equality))

(defund syntactic-call-of (quoted-fn nodenum-or-quotep dag-array)
  (declare (xargs :guard (or (myquotep nodenum-or-quotep)
                             (and (natp nodenum-or-quotep)
                                  (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nodenum-or-quotep))))))
  (and (not (consp nodenum-or-quotep))
       (if (not (and (myquotep quoted-fn)
                     (symbolp (unquote quoted-fn))))
           (er hard? 'syntactic-call-of "Bad fn argument: ~x0." quoted-fn)
         (let ((fn (unquote quoted-fn)))
           (call-of fn (aref1 'dag-array dag-array nodenum-or-quotep))))))

(defund syntactic-constantp (nodenum-or-quotep dag-array)
  (declare (xargs :guard (or (myquotep nodenum-or-quotep)
                             (and (natp nodenum-or-quotep)
                                  (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nodenum-or-quotep))))))
  (if (consp nodenum-or-quotep) ;check for quotep
      t
    (let ((expr (aref1 'dag-array dag-array nodenum-or-quotep)))
      (and (consp expr)
           (eq 'quote (car expr))))))

(defund syntactic-variablep (nodenum-or-quotep dag-array)
  (declare (xargs :guard (or (myquotep nodenum-or-quotep)
                             (and (natp nodenum-or-quotep)
                                  (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nodenum-or-quotep))))))
  (if (consp nodenum-or-quotep) ;check for quotep
      nil
    (let ((expr (aref1 'dag-array dag-array nodenum-or-quotep)))
      (atom expr))))

(defund is-the-variablep (quoted-var nodenum-or-quotep dag-array)
  (declare (xargs :guard (and ;; (symbolp (unquote quoted-var)) ; causes problems for caller but should be true
                          (or (myquotep nodenum-or-quotep)
                              (and (natp nodenum-or-quotep)
                                   (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nodenum-or-quotep)))))))
  (if (consp nodenum-or-quotep) ;check for quotep
      nil
    (if (not (and (myquotep quoted-var)
                  (symbolp (unquote quoted-var))))
        (er hard? 'is-the-variablep "Bad fn argument: ~x0." quoted-var)
      (let ((expr (aref1 'dag-array dag-array nodenum-or-quotep)))
        (equal (unquote quoted-var) expr)))))

;bozo make this a real table?
;args are numbered from 1
;make this a constant?
(defconst *axe-invisible-fns-table*
  ;for bvplus, consider the second argument to bvminus, not the bvminus itself:
  (acons 'bvplus (acons 'bvuminus 2 nil)
         ;ffixme other boolean ops?
         (acons 'bvand
                (acons 'bvnot 2 (acons 'bvxor  ;bvxor is new! to handle xoring with ones, which is the same as bvnot (fffixme restrict to that case?)
                                       3 nil))
                nil)))

;either returns a new term or nil if nothing was stripped -ffixme just return the same term if nothing was stripped?
;BOZO this should not return a quoted constant
(defund strip-invisible-fns (fn expr)
  (declare (xargs :guard (dag-exprp0 expr)
                  :guard-hints (("Goal" :in-theory (enable LOOKUP-EQUAL-OF-CONS)))))
  (if (or (symbolp expr) ;was atom, which was wrong for vars
          (quotep expr))
      nil ;rare?
    (let* ((table-for-fn (lookup-eq fn *axe-invisible-fns-table*))
           (expr-fn (ffn-symb expr))
           (arg-for-expr-fn (lookup-eq expr-fn table-for-fn))) ;is an arg number
      (if (and arg-for-expr-fn
               (posp arg-for-expr-fn)
               (< arg-for-expr-fn (len expr)))
          (let ((arg (nth (+ -1 arg-for-expr-fn) (dargs expr))))
            (if (quotep arg)
                nil
              arg))
        ;;nothing to strip:
        nil))))

;move
(defthm integerp-of-nth-when-all-dargp-less-than
  (implies (and (all-dargp-less-than args bound)
                (not (consp (nth n args)))
                (natp n)
                (< n (len args)))
           (integerp (nth n args)))
  :hints (("Goal" :in-theory (e/d (all-dargp-less-than nth) (NTH-OF-CDR)))))

(defthm integerp-of-nth-when-all-dargp-less-than-special
  (implies (and (all-dargp-less-than (cdr expr) bound)
                (not (consp (nth n expr)))
                (posp n)
                (< n (len expr)))
           (integerp (nth n expr)))
  :hints (("Goal" :in-theory (e/d (all-dargp-less-than nth) (NTH-OF-CDR)))))

(defthm natp-of-strip-invisible-fns
  (implies (and (bounded-dag-exprp nodenum expr)
                (strip-invisible-fns fn expr))
           (natp (strip-invisible-fns fn expr)))
  :hints (("Goal" :in-theory (e/d (strip-invisible-fns LOOKUP-EQUAL-OF-CONS) (len true-listp)))))

(defthm rationalp-of-strip-invisible-fns
  (implies (and (bounded-dag-exprp nodenum expr)
                (strip-invisible-fns fn expr))
           (rationalp (strip-invisible-fns fn expr)))
  :hints (("Goal" :use (:instance natp-of-strip-invisible-fns)
           :in-theory (disable natp-of-strip-invisible-fns))))

(defthm rationalp-of-strip-invisible-fns-2
  (implies (and (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nodenum))
                (strip-invisible-fns fn (aref1 'dag-array dag-array nodenum))
                (natp nodenum))
           (rationalp (strip-invisible-fns fn (aref1 'dag-array dag-array nodenum))))
  :hints (("Goal" :use (:instance natp-of-strip-invisible-fns
                                  (expr (aref1 'dag-array dag-array nodenum)))
           :in-theory (e/d (pseudo-dag-arrayp-aux)
                           (natp-of-strip-invisible-fns
                             bounded-dag-exprp)))))

;; we really only want this to fire at the leafmost bitxor in a nest??

;move?
;BBOZO rethink this?
;; Determines whether we should we bring TERM2 in front of TERM1.
;; FN is the function whose nests we are rewriting (e.g., BVXOR, BVPLUS, etc.).
;; DAG-ARRAY is the entire DAG
;; If term2 is a call of FN, it should not be commuted (that would mess up associativity)
;; Also, TERM1 should not be a call to FN?
;example of use: (axe-syntaxp (should-commute-args-dag 'bvxor x y dag-array)) <- note that the FN is quoted
;bozo should we check that a bvuminus has the same size as the enclosing bvplus before ignoring the bvuminus?
(defund should-commute-args-dag (quoted-fn term1 term2 dag-array)
  (declare (xargs :guard (and (or (myquotep term1)
                                  (and (natp term1)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 term1))))
                              (or (myquotep term2)
                                  (and (natp term2)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 term2)))))))
  (if (quotep term2)
      (if (quotep term1)
          ;;both are constants:
          ;;we sort constants by numeric value
          ;;or we could just not swap them, at least for operators which have the combine-constants rule..
          (and (rationalp term1)
               (rationalp term2)
               (< (unquote term2) (unquote term1)))
        ;;TERM2 is a quoted constant but TERM1 isn't, so TERM2 should come first
        t)
    (if (quotep term1) ;Otherwise, if TERM1 is a quoted constant, we shouldn't commute TERM2 in front of it
        nil
      ;; both are nodenums:
      ;; first look up the expression for TERM2 in the DAG
      (let ((expr2 (aref1 'dag-array dag-array term2)))
        (if (not (and (myquotep quoted-fn)
                      (symbolp (unquote quoted-fn))))
            (er hard? 'should-commute-args-dag "Bad fn argument: ~x0." quoted-fn)
          (let ((fn (unquote quoted-fn)))
            (if (call-of fn expr2)
                nil ;IF TERM2 is a call to FN, commuting it forward will mess up the associativity, so refrain. (FFIXME check the size too?  otherwise, this will not apply to a bvplus 64 nest when an argument is a bvplus 32, even though associativity would not apply when one size is 32 and the other is 64)
              ;; If term2 isn't a call to FN (TERM1 shouldn't be one because of associativity), then just compare the nodenums (but first strip off invisible fns)
              ;; fffixme could putting bigger nodenums first help with sharing? it's what simplify-bitxors does
              (let* ((expr1 (aref1 'dag-array dag-array term1))
                     (stripped1 (strip-invisible-fns fn expr1))
                     (term1 (if stripped1 stripped1 term1))
                     (stripped2 (strip-invisible-fns fn expr2))
                     (term2 (if stripped2 stripped2 term2)))
                (< term2 term1)))))))))

;move?
;same as should-commute-args-dag except it puts bigger nodenums first (matches what simplify-bitxors does)
;ffixme maybe we should always put bigger nodenums first and so always just use this?
(defund should-commute-args-increasing-dag (quoted-fn term1 term2 dag-array)
  (declare (xargs :guard (and (or (myquotep term1)
                                  (and (natp term1)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 term1))))
                              (or (myquotep term2)
                                  (and (natp term2)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 term2)))))
                  ;;:guard-hints (("Goal" :in-theory (enable PSEUDO-DAG-ARRAYP-AUX)))
                  ))
  (if (quotep term2)
      (if (quotep term1)
          ;;both are constants:
          ;;we sort constants by numeric value
          ;;or we could just not swap them, at least for operators which have the combine-constants rule..
          (and (rationalp (unquote term1))
               (rationalp (unquote term2))
               (< (unquote term2) (unquote term1)))
        ;;TERM2 is a quoted constant but TERM1 isn't, so TERM2 should come first
        t)
    (if (quotep term1) ;Otherwise, if TERM1 is a quoted constant, we shouldn't commute TERM2 in front of it
        nil
      ;; both are nodenums:
      ;; first look up the expression for TERM2 in the DAG
      (let ((expr2 (aref1 'dag-array dag-array term2)))
        (if (not (and (myquotep quoted-fn)
                      (symbolp (unquote quoted-fn))))
            (er hard? 'should-commute-args-increasing-dag "Bad fn argument: ~x0." quoted-fn)
          (let ((fn (unquote quoted-fn)))

            (if (call-of fn expr2)
                nil ;IF TERM2 is a call to FN, commuting it forward will mess up the associativity, so refrain.
              ;; If term2 isn't a call to FN (TERM1 shouldn't be one because of associativity), then just compare the nodenums (but first strip off invisible fns)
              ;; fffixme could putting bigger nodenums first help with sharing? it's what simplify-bitxors does
              (let* ((expr1 (aref1 'dag-array dag-array term1))
                     (stripped1 (strip-invisible-fns fn expr1))
                     (term1 (if stripped1 stripped1 term1))
                     (stripped2 (strip-invisible-fns fn expr2))
                     (term2 (if stripped2 stripped2 term2)))
                ;;bring larger nodenums to the front!
                (< term1 term2)))))))))

;; ;maybe the measure is the size of the terms at the give nodenums in the dag...
;; (mutual-recursion
;;  ;;the exprs can be dag-exprs?? or quoteps or nodenums or variables??
;;  (defun dag-exprs-equal (expr1 expr2 dag-array count)
;; ;    (declare (xargs :measure (make-ord 1 (if (consp expr1) 0 (nfix expr1)) 0)))
;;    (declare (xargs :measure (nfix count)
;;                    :guard (and (natp count)  ;todo: repetitive
;;                                (or (myquotep expr1)
;;                                    (and (natp expr1)
;;                                         (pseudo-dag-arrayp 'dag-array dag-array (+ 1 expr1))))
;;                                (or (myquotep expr2)
;;                                    (and (natp expr2)
;;                                         (pseudo-dag-arrayp 'dag-array dag-array (+ 1 expr2)))))
;;                    :guard-hints (("Goal" :in-theory (enable PSEUDO-DAG-ARRAYP-LIST)))))
;;    ;;lookup any that are nodenums:
;;    (if (zp count)
;;        nil
;;      (let ((expr1 (get-expr expr1 dag-array))
;;            (expr2 (get-expr expr2 dag-array)))
;;        (if (quotep expr1)
;;            (equal expr1 expr2)
;;          (if (symbolp expr1)
;;              (equal expr1 expr2)
;;            ;;otherwise expr1 is a function call:
;;            (and (consp expr2)
;;                 (equal (ffn-symb expr1) (ffn-symb expr2))
;;                 (eql (len (dargs expr1))
;;                      (len (dargs expr2)))
;;                 (dag-exprs-equal-lst (dargs expr1) (dargs expr2) dag-array (+ -1 count))))))))

;;  (defun dag-exprs-equal-lst (expr1-lst expr2-lst dag-array count)
;; ;   (declare (xargs :measure (make-ord 1 (if (consp (first expr1-lst)) 0 (first expr1-lst)) 1)))
;;    (declare (xargs :measure (nfix count)
;;                    :guard (and (natp count)
;;                                (true-listp expr1-lst)
;;                                (true-listp expr2-lst)
;;                                (eql (len expr1-lst) (len expr2-lst))
;;                                (pseudo-dag-arrayp-list expr1-lst 'dag-array dag-array)
;;                                (pseudo-dag-arrayp-list expr2-lst 'dag-array dag-array))))
;;    (if (zp count)
;;        nil
;;      (if (endp expr1-lst)
;;          (endp expr2-lst)
;;        (and (dag-exprs-equal (car expr1-lst) (car expr2-lst) dag-array (+ -1 count))
;;             (dag-exprs-equal-lst (cdr expr1-lst) (cdr expr2-lst) dag-array (+ -1 count)))))))

(local (in-theory (enable car-becomes-nth-of-0
                          integerp-of-nth-when-all-dargp
                          not-cddr-of-nth-when-all-dargp
                          consp-of-cdr-of-nth-when-all-dargp
                          equal-of-quote-and-nth-0-of-nth-when-all-dargp
                          symbolp-of-nth-0-when-dag-exprp0
                          )))

;returns the number of branches
(defun count-myif-branches (nest dag-array)
  (declare (xargs :measure (if (quotep nest) 0 (+ 1 (nfix nest)))
                  :guard (or (myquotep nest)
                             (and (natp nest)
                                  (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nest))))
                  :verify-guards nil ;done below
                  ))
  (if (or (consp nest) ;check for quotep
          (not (mbt (natp nest))))
      1
    (let ((expr (aref1 'dag-array dag-array nest)))
      (if (or (atom expr)
              (quotep expr))
          1
        (if (not (and (eq 'myif (car expr))
                      (eql 3 (len (dargs expr)))))
            1
          (b* (;; Uncomment this to print the test:
               ;; (- (cw "(Test:~%") ;todo: check for a constant test?
               ;;    (print-dag-only-supporters 'dag-array dag-array (darg1 expr))
               ;;    (cw ")~%"))
               (then-branch (darg2 expr))
               ;; Uncomment this to print the then-branch:
               ;; (- (cw "(Then branch:~%") ;todo: check for a constant test?
               ;;    (if (quotep then-branch) (cw "~x0~%" then-branch) (print-dag-only-supporters 'dag-array dag-array then-branch))
               ;;    (cw ")~%"))
               (else-branch (darg3 expr))
               ;; Uncomment this to print the else-branch:
               ;; (- (cw "(Else branch:~%") ;todo: check for a constant test?
               ;;    (if (quotep else-branch) (cw "~x0~%" else-branch) (print-dag-only-supporters 'dag-array dag-array else-branch))
               ;;    (cw ")~%"))
               )
            (if (mbt (and (or (myquotep then-branch) ;for termination
                              (and (natp then-branch)
                                   (< then-branch nest)))
                          (or (myquotep else-branch)
                              (and (natp else-branch)
                                   (< else-branch nest)))))
                (let ((then-branch-count (count-myif-branches then-branch dag-array))
                      (else-branch-count (count-myif-branches else-branch dag-array)))
                  (+ then-branch-count else-branch-count))
              1)))))))

(defthm natp-of-count-myif-branches
  (natp (count-myif-branches nest dag-array)))

(verify-guards count-myif-branches
                    :hints (("Goal" :in-theory (e/d (car-becomes-nth-of-0)
                                                    (len)))))

;; ;; vars should be a symbol-list.
;; (defun nodenums-are-vars (nodenums-or-quoteps vars dag-array)
;;   (declare (xargs :guard (and (true-listp nodenums-or-quoteps)
;;                               (pseudo-dag-arrayp-list nodenums-or-quoteps 'dag-array dag-array))
;;                   :guard-hints (("Goal" :in-theory (enable pseudo-dag-arrayp-list)))))
;;   (if (atom nodenums-or-quoteps)
;;       t
;;     (and (atom (car nodenums-or-quoteps)) ;tests for nodenum
;;          ;; using equal instead of eq here because I don't want a guard  on vars:
;;          (equal (car vars) (aref1 'dag-array dag-array (car nodenums-or-quoteps)))
;;          (nodenums-are-vars (cdr nodenums-or-quoteps) (cdr vars) dag-array))))

;; (defund nodenums-are-not-vars (nodenums-or-quoteps vars dag-array)
;;   (declare (xargs :guard (and (true-listp nodenums-or-quoteps)
;;                               ;; (symbol-listp vars)
;;                               (pseudo-dag-arrayp-list nodenums-or-quoteps 'dag-array dag-array))))
;;   (not (nodenums-are-vars nodenums-or-quoteps vars dag-array)))

;just call syntactic-call-of?
(defund is-a-myif (arg dag-array)
  (declare (xargs :guard (or (myquotep arg)
                             (and (natp arg)
                                  (pseudo-dag-arrayp 'dag-array dag-array (+ 1 arg))))))
  (and (integerp arg)
       (let ((expr (aref1 'dag-array dag-array arg)))
         (and (consp expr)
              (or (eq 'myif (car expr))
                  ;(eq 'bvif (car expr))
                  )))))

;just call not-syntactic-call-of?
(defund not-is-a-myif (arg dag-array)
  (declare (xargs :guard (or (myquotep arg)
                             (and (natp arg)
                                  (pseudo-dag-arrayp 'dag-array dag-array (+ 1 arg))))))
  (not (is-a-myif arg dag-array)))
