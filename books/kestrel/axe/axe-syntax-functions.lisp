; General-purpose syntactic tests
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
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

(include-book "std/util/bstar" :dir :system)
(include-book "misc/total-order" :dir :system) ;to get <<
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "axe-syntax")
(include-book "dag-arrays")
(local (include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;; quotep gets converted this this
(defund-inline axe-quotep (darg)
  (declare (xargs :guard (dargp darg)))
  (consp darg) ;; means that it is a quotep, not a nodenum
  )

;;TODO: Change these to never compare nodenums (can cause simplification to loop if things keep getting commuted due to different nodenums?)

; Check whether x is 'lighter' than y.  Helps us decide when to reorder terms
; (e.g., to put 'light' terms first).  x and y are either quoteps or nodenums.
(defund lighter-dargp (x y)
  (declare (xargs :guard (and (dargp x)
                              (dargp y))))
  (if (consp x) ; checks for quotep
      (if (consp y) ; checks for quotep
          (<< (unquote x) (unquote y))
        t ; x is a constant but y isn't, so x is "lighter"
        )
    (if (consp y)
        nil ; x is not a constant but y is, so x is not "lighter"
      ;; both are nodenums:
      (< x y))))

;drop?
;; (defun valid-array-indexp (index array-name array)
;;   (declare (xargs :guard (array1p array-name array)))
;;   (and (natp index)
;;        (< index (alen1 array-name array))))

;; (defun get-expr (nodenum-or-quotep dag-array)
;;   (declare (xargs :guard (or (myquotep nodenum-or-quotep)
;;                              (and (array1p 'dag-array dag-array) ;could pull out as a top-level conjunct
;;                                   (valid-array-indexp nodenum-or-quotep 'DAG-ARRAY DAG-ARRAY)))))
;;   (if (integerp nodenum-or-quotep)
;;       (aref1 'dag-array dag-array nodenum-or-quotep)
;;     nodenum-or-quotep))

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
  (if (consp x) ; checks for quotep
      nil
    (if (consp y) ; checks for quotep
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

;; We expect quoted-fn to always be a quoted symbol, but we cannot require that in the guard.
(defund syntactic-call-of (quoted-fn darg dag-array)
  (declare (xargs :guard (and (or (myquotep quoted-fn)
                                  (and (natp quoted-fn)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 quoted-fn))))
                              (or (myquotep darg)
                                  (and (natp darg)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg)))))))
  (and (not (consp darg)) ; checks for nodenum
       (consp quoted-fn) ; checks for quotep
       (let ((fn (unquote quoted-fn)))
         (if (not (symbolp fn)) ; can we skip this check?
             (er hard? 'syntactic-call-of "Bad fn argument: ~x0." quoted-fn)
           (call-of fn (aref1 'dag-array dag-array darg))))))

;; We expect quoted-var to always be a quoted symbol, but we cannot require that in the guard.
(defund is-the-variablep (quoted-var darg dag-array)
  (declare (xargs :guard (and (or (myquotep quoted-var)
                                  (and (natp quoted-var)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 quoted-var))))
                              (or (myquotep darg)
                                  (and (natp darg)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg)))))))
  (and (not (consp darg)) ; checks for nodenum
       (consp quoted-var) ; checks for quotep
       (let ((var (unquote quoted-var)))
         (if (not (symbolp var)) ; drop this check?
             (er hard? 'is-the-variablep "Bad fn argument: ~x0." quoted-var)
           (equal var (aref1 'dag-array dag-array darg))))))

;; ;deprecate?  allows an expr to be constant, but that should be very rare
;; (defund syntactic-constantp (darg dag-array)
;;   (declare (xargs :guard (or (myquotep darg)
;;                              (and (natp darg)
;;                                   (pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg))))))
;;   (if (consp darg) ;checks for quotep
;;       t
;;     (let ((expr (aref1 'dag-array dag-array darg)))
;;       (and (consp expr)
;;            (eq 'quote (car expr))))))

(defund syntactic-variablep (darg dag-array)
  (declare (xargs :guard (or (myquotep darg)
                             (and (natp darg)
                                  (pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg))))))
  (if (consp darg) ;checks for quotep
      nil
    (let ((expr (aref1 'dag-array dag-array darg)))
      (atom expr))))



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
  (declare (xargs :guard (dag-exprp expr)
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

;BBOZO rethink this?
;; Determines whether we should we bring TERM2 in front of TERM1.
;; QUOTED-FN is the function whose arguments we are considering (e.g., BVXOR, BVPLUS, etc.).
;; DAG-ARRAY is the entire DAG
;; If term2 is a call of FN, it should not be commuted (that would mess up associativity)
;; Also, TERM1 should not be a call to FN?
;example of use: (axe-syntaxp (should-commute-axe-argsp 'bvxor x y dag-array)) <- note that the FN is quoted
;bozo should we check that a bvuminus has the same size as the enclosing bvplus before ignoring the bvuminus?
(defund should-commute-axe-argsp (quoted-fn darg1 darg2 dag-array)
  (declare (xargs :guard (and (or (myquotep darg1)
                                  (and (natp darg1)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg1))))
                              (or (myquotep darg2)
                                  (and (natp darg2)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg2)))))))
  (if (quotep darg2)
      (if (quotep darg1)
          ;;both are constants:
          ;;we sort constants by numeric value
          ;;or we could just not swap them, at least for operators which have the combine-constants rule..
          (and (rationalp darg1)
               (rationalp darg2)
               (< (unquote darg2) (unquote darg1)))
        ;;DARG2 is a quoted constant but DARG1 isn't, so DARG2 should come first
        t)
    (if (quotep darg1) ;Otherwise, if DARG1 is a quoted constant, we shouldn't commute DARG2 in front of it
        nil
      ;; both are nodenums:
      ;; first look up the expression for DARG2 in the DAG
      (let ((expr2 (aref1 'dag-array dag-array darg2)))
        (if (not (and (myquotep quoted-fn)
                      (symbolp (unquote quoted-fn))))
            (er hard? 'should-commute-axe-argsp "Bad fn argument to should-commute-axe-argsp: ~x0." quoted-fn)
          (let ((fn (unquote quoted-fn)))
            (if (call-of fn expr2)
                nil ;IF DARG2 is a call to FN, commuting it forward will mess up the associativity, so refrain. (FFIXME check the size too?  otherwise, this will not apply to a bvplus 64 nest when an argument is a bvplus 32, even though associativity would not apply when one size is 32 and the other is 64)
              ;; If darg2 isn't a call to FN (DARG1 shouldn't be one because of associativity), then just compare the nodenums (but first strip off invisible fns)
              ;; fffixme could putting bigger nodenums first help with sharing? it's what simplify-bitxors does
              (let* ((expr1 (aref1 'dag-array dag-array darg1))
                     (stripped1 (strip-invisible-fns fn expr1))
                     (darg1 (if stripped1 stripped1 darg1))
                     (stripped2 (strip-invisible-fns fn expr2))
                     (darg2 (if stripped2 stripped2 darg2)))
                (< darg2 darg1)))))))))

;same as should-commute-axe-argsp except it puts bigger nodenums first (matches what simplify-bitxors does)
;ffixme maybe we should always put bigger nodenums first and so always just use this?
(defund should-commute-axe-args-increasingp (quoted-fn darg1 darg2 dag-array)
  (declare (xargs :guard (and (or (myquotep darg1)
                                  (and (natp darg1)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg1))))
                              (or (myquotep darg2)
                                  (and (natp darg2)
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 darg2)))))
                  ;;:guard-hints (("Goal" :in-theory (enable PSEUDO-DAG-ARRAYP-AUX)))
                  ))
  (if (quotep darg2)
      (if (quotep darg1)
          ;;both are constants:
          ;;we sort constants by numeric value
          ;;or we could just not swap them, at least for operators which have the combine-constants rule..
          (and (rationalp (unquote darg1))
               (rationalp (unquote darg2))
               (< (unquote darg2) (unquote darg1)))
        ;;DARG2 is a quoted constant but DARG1 isn't, so DARG2 should come first
        t)
    (if (quotep darg1) ;Otherwise, if DARG1 is a quoted constant, we shouldn't commute DARG2 in front of it
        nil
      ;; both are nodenums:
      ;; first look up the expression for DARG2 in the DAG
      (let ((expr2 (aref1 'dag-array dag-array darg2)))
        (if (not (and (myquotep quoted-fn)
                      (symbolp (unquote quoted-fn))))
            (er hard? 'should-commute-axe-args-increasingp "Bad fn argument: ~x0." quoted-fn)
          (let ((fn (unquote quoted-fn)))
            (if (call-of fn expr2)
                nil ;IF DARG2 is a call to FN, commuting it forward will mess up the associativity, so refrain.
              ;; If darg2 isn't a call to FN (DARG1 shouldn't be one because of associativity), then just compare the nodenums (but first strip off invisible fns)
              ;; fffixme could putting bigger nodenums first help with sharing? it's what simplify-bitxors does
              (let* ((expr1 (aref1 'dag-array dag-array darg1))
                     (stripped1 (strip-invisible-fns fn expr1))
                     (darg1 (if stripped1 stripped1 darg1))
                     (stripped2 (strip-invisible-fns fn expr2))
                     (darg2 (if stripped2 stripped2 darg2)))
                ;;bring larger nodenums to the front!
                (< darg1 darg2)))))))))

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
                          integerp-of-nth-when-darg-listp
                          not-cddr-of-nth-when-darg-listp
                          consp-of-cdr-of-nth-when-darg-listp
                          equal-of-quote-and-nth-0-of-nth-when-darg-listp
                          symbolp-of-nth-0-when-dag-exprp
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
               ;;    (print-dag-array-node-and-supporters 'dag-array dag-array (darg1 expr))
               ;;    (cw ")~%"))
               (then-branch (darg2 expr))
               ;; Uncomment this to print the then-branch:
               ;; (- (cw "(Then branch:~%") ;todo: check for a constant test?
               ;;    (if (quotep then-branch) (cw "~x0~%" then-branch) (print-dag-array-node-and-supporters 'dag-array dag-array then-branch))
               ;;    (cw ")~%"))
               (else-branch (darg3 expr))
               ;; Uncomment this to print the else-branch:
               ;; (- (cw "(Else branch:~%") ;todo: check for a constant test?
               ;;    (if (quotep else-branch) (cw "~x0~%" else-branch) (print-dag-array-node-and-supporters 'dag-array dag-array else-branch))
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
