; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book separates out some functions called in termination-database.lisp
; that are also called elsewhere.

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)

(defconst *td-stub-name-max*

; After building td (during development, 6/18/2018) I found the maximum number
; of formals to be 16:

#||
? (loop for i from 0 to (next-index *the-live-td*)
        maximize
        (let ((entry (td-entry-ari i *the-live-td*)))
          (cond ((null entry) 0)
                (t (length (formals (access td-entry entry :root)
                                    (w *the-live-state*)))))))
16
? (loop for i from 0 to (next-index *the-live-td*)
        maximize
        (let ((entry (td-entry-ari i *the-live-td*)))
          (cond ((null entry) 0)
                (t (loop for pair in (access td-entry entry :alt-alist)
                         maximize
                         (length (formals (car pair)
                                          (w *the-live-state*))))))))
14
?
||#

; So 20 would seem to be plenty; we use the value below to be safe.  We cause
; an error in td-stub-name if we exceed the bound.

  64)

(defun td-stub-name (n fn)
  (declare (type (integer 0 *) n)
           (type symbol fn))
  (if (<= n *td-stub-name-max*)
      (packn (list 'td-stub- n))
    (er hard? 'td-stub-name
        "The function ~x0 has more than ~x1 formals.  The value of constant ~
         ~x2 needs to be increased in the book ~x3 to more than ~x1."
        fn *td-stub-name-max* '*td-stub-name-max*
        "termination-database.lisp")))

(defun td-stub-lst (n defs sigs)
  (declare (type (integer 0 *) n)
           (xargs :guard (and (true-listp defs)
                              (true-listp sigs))))
  (cond ((zp n) (mv (reverse defs) (reverse sigs)))
        (t (let* ((n (1- n))
                  (name (td-stub-name n nil))
                  (formals (make-var-lst 'x n)))
             (td-stub-lst
               n
               (cons `(local (defun ,name ,formals
                               (list ,@formals)))
                     defs)
               (cons `(,name ,formals t)
                     sigs))))))

(defun td-stub-lst-event (n)

; It may be tempting to make the new names untouchable, so that others can't
; use them.  But that won't help if a new name is used before this book is
; included, and anyhow, we will actually need to use those names in the events
; we generate on behalf of defunt calls.

  (mv-let (local-defuns sigs)
    (td-stub-lst n nil nil)
    (let ((names (strip-cars sigs)))
      `(progn
         (defconst *td-stub-names* ',names)
         (encapsulate
           ,sigs
           ,@local-defuns)))))

(make-event

; Create stubs TD-STUB-0, ..., TD-STUB-64, with zero through 64 formals.

 (td-stub-lst-event (1+ *td-stub-name-max*)))

(mutual-recursion

; This is based loosely on the all-ffn-symbs nest in the ACL2 sources.
; It explores lambdas.

(defun fn-symb-occur (fn term)
  (declare (xargs :guard (and (symbolp fn)
                              (pseudo-termp term))
                  :mode :logic))
  (cond ((variablep term) nil)
        ((fquotep term) nil)
        ((flambdap (ffn-symb term))
         (or (fn-symb-occur fn (lambda-body (ffn-symb term)))
             (fn-symb-occur-lst fn (fargs term))))
        ((eq fn (ffn-symb term))
         t)
        (t (fn-symb-occur-lst fn (fargs term)))))

(defun fn-symb-occur-lst (fn lst)
  (declare (xargs :guard (and (symbolp fn)
                              (pseudo-term-listp lst))))
  (cond ((endp lst) nil)
        (t (or (fn-symb-occur fn (car lst))
               (fn-symb-occur-lst fn (cdr lst))))))

)

(defun fn-symb-occur-lst-lst (fn lst)
  (declare (xargs :guard (and (symbolp fn)
                              (pseudo-term-list-listp lst))
                  :mode :logic))
  (cond ((endp lst) nil)
        (t (or (fn-symb-occur-lst fn (car lst))
               (fn-symb-occur-lst-lst fn (cdr lst))))))

(program)

(mutual-recursion

(defun sublis-fn-trivial (alist term)

; This is just an efficient version of sublis-fn, which is defined in the ACL2
; sources.  Here, alist is assumed to map symbols to symbols; no lambdas should
; be involved in alist.

; See also sublis-fn-lst-lst-trivial, below.

  (cond ((variablep term) (mv nil term))
        ((fquotep term) (mv nil term))
        (t (mv-let (changedp args)
             (sublis-fn-lst-trivial alist (fargs term))
             (let ((fn (ffn-symb term)))
               (cond
                ((flambdap fn)
                 (mv-let (changedp2 body)
                   (sublis-fn-trivial alist (lambda-body fn))
                   (cond
                    (changedp2
                     (mv t (fcons-term (make-lambda (lambda-formals fn)
                                                    body)
                                       args)))
                    (changedp
                     (mv t (fcons-term fn args)))
                    (t (mv nil term)))))
                (t (let ((pair (assoc-eq fn alist)))
                     (cond (pair (mv t (fcons-term (cdr pair) args)))
                           (changedp (mv t (fcons-term fn args)))
                           (t (mv nil term)))))))))))

(defun sublis-fn-lst-trivial (alist lst)
  (cond ((endp lst) (mv nil nil))
        (t (mv-let (c1 x1)
             (sublis-fn-trivial alist (car lst))
             (mv-let (c2 x2)
               (sublis-fn-lst-trivial alist (cdr lst))
               (cond ((or c1 c2) (mv t (cons x1 x2)))
                     (t (mv nil lst))))))))
)

(defun sublis-fn-lst-lst-trivial (alist cl-lst)

; Returns (mv changedp new-cl-lst), where new-cl-lst is the result of
; functionally substituting alist into cl-lst; and if changedp is nil, then
; new-cl-lst is EQ to cl-lst, else cl-lst and new-cl-lst differ.  Unlike
; sublis-fn and sublis-fn-lst, there is no attention paid to capture, so use
; with caution, e.g., when alist has no lambdas or only closed lambdas in its
; range.

; By using the changedp flag we got improved performance without full GC being
; invoked, and we probably also saved a lot of conses.

;;; Profiling result without using changedp flag:
; Calls                                                                      135
; Time of all outermost calls                                               0.36
; Time per call                                                          2.66E-3

;;; Profiling result WITH using changedp flag:
; Calls                                                                      135
; Time of all outermost calls                                               0.22
; Time per call                                                          1.65E-3

  (cond ((endp cl-lst) (mv nil nil))
        (t (mv-let (c1 x1)
             (sublis-fn-lst-trivial alist (car cl-lst))
             (mv-let (c2 x2)
               (sublis-fn-lst-lst-trivial alist (cdr cl-lst))
               (cond ((or c1 c2) (mv t (cons x1 x2)))
                     (t (mv nil cl-lst))))))))

(defun td-replace-fn-cl-lst (fn cl-lst wrld)

; Replacement doesn't go into lambdas bodies (though it easily could).  So we
; assume that lambdas have been expanded away (more precisely, that there are
; no lambdas) in cl-lst.

  (declare (xargs :guard (and (symbolp fn)
                              (pseudo-term-list-listp cl-lst)
                              (plist-worldp wrld))))
  (cond ((not (fn-symb-occur-lst-lst fn cl-lst)) ; optimize for common case
         cl-lst)
        (t (let* ((len ; call formals, so it's an error if fn isn't defined
                   (len (formals fn wrld)))
                  (fn2 (td-stub-name len fn)))
             (mv-let (changedp new-cl-lst)
               (sublis-fn-lst-lst-trivial
                (acons fn fn2 nil)
                cl-lst)
               (declare (ignore changedp))
               new-cl-lst)))))

(defun pair-with-formals-and-body (fns wrld)
  (cond ((endp fns) nil)
        (t (acons (car fns)
                  (cons (formals (car fns) wrld)
                        (body (car fns) t wrld))
                  (pair-with-formals-and-body (cdr fns) wrld)))))

(defconst *auto-termination-fns*

; These are trivial "abbreviation" functions that we want to expand, so that
; subsumption can take place more often for normalized termination clause-sets.

  (union-equal '(zp natp posp zip)
               (remove1-eq 'mv-nth *definition-minimal-theory*)))

(make-event
 `(defconst *auto-termination-fn-alist*
    ',(pair-with-formals-and-body *auto-termination-fns* (w state))))

(defun negated-p (x y)
  (cond ((ffn-symb-p y 'not)
         (equal x (fargn y 1)))
        ((ffn-symb-p x 'not)
         (equal y (fargn x 1)))
        ((ffn-symb-p x 'if)
         (and (ffn-symb-p y 'if)
              (equal (fargn x 1) (fargn y 1))
              (negated-p (fargn x 2) (fargn y 2))
              (negated-p (fargn x 3) (fargn y 3))))
        ((ffn-symb-p y 'if)
         nil)
        ((variablep x)
         nil)
        ((variablep y)
         nil)
        ((fquotep x)
         (if (equal x *nil*)
             (equal y *t*)
           (equal y *nil*)))
        (t nil)))

(defun my-negate-lit (x)
  (cond ((ffn-symb-p x 'if)
         (fcons-term* 'if
                      (fargn x 1)
                      (my-negate-lit (fargn x 2))
                      (my-negate-lit (fargn x 3))))
        (t (dumb-negate-lit x))))

(mutual-recursion

(defun norm-lit (lit not-flg iff-flg)
  (cond ((variablep lit) (if not-flg (dumb-negate-lit lit) lit))
        ((fquotep lit) (if not-flg
                           (if (equal lit *nil*) *t* *nil*)
                         lit))
        ((eq (ffn-symb lit) 'not)
         (norm-lit (fargn lit 1) (not not-flg) t))
        ((eq (ffn-symb lit) 'if)
         (mv-let
           (tst tbr fbr)
           (if (ffn-symb-p (fargn lit 1) 'not)
               (mv (fargn (fargn lit 1) 1)
                   (fargn lit 3)
                   (fargn lit 2))
             (mv (fargn lit 1) (fargn lit 2) (fargn lit 3)))
           (let ((tst (norm-lit tst nil t))
                 (tbr (norm-lit tbr not-flg iff-flg))
                 (fbr (norm-lit fbr not-flg iff-flg)))
             (mv-let
               (tst tbr fbr)
               (if (ffn-symb-p tst 'not)
                   (mv (my-negate-lit tst) fbr tbr)
                 (mv tst tbr fbr))
               (fcons-term*
                'if
                tst
                (cond ((and (equal tst tbr) iff-flg)
                       *t*)
                      ((negated-p tst tbr)
                       *nil*)
                      (t tbr))
                (cond ((equal tst fbr)
                       *nil*)
                      ((negated-p tst fbr)
                       *t*)
                      (t fbr)))))))
        ((member-eq (ffn-symb lit) *auto-termination-fns*)
         (let* ((pair (cdr (assoc-eq (ffn-symb lit) *auto-termination-fn-alist*)))
                (formals (car pair))
                (body (cdr pair)))
           (norm-lit (subcor-var formals (fargs lit) body) not-flg iff-flg)))
        (t (let ((x (cons-term (ffn-symb lit)
                               (norm-lit-lst (fargs lit)))))
             (if not-flg (dumb-negate-lit x) x)))))

(defun norm-lit-lst (lst)
  (cond ((endp lst) nil)
        (t (cons (norm-lit (car lst) nil nil)
                 (norm-lit-lst (cdr lst))))))
)

(defun add-lit-and-flatten (lit cl)
  (case-match lit
    (*nil* cl)
    (*t* (list *t*))
    (('if tst tst fbr) ; (or tst fbr)
     (add-lit-and-flatten tst
                          (add-lit-and-flatten fbr cl)))
    (('if tst *t* fbr) ; (or tst fbr)
     (add-lit-and-flatten tst
                          (add-lit-and-flatten fbr cl)))
    (('if tst tbr *t*) ; (or (not tst) tbr)
     (add-lit-and-flatten (dumb-negate-lit tst)
                          (add-lit-and-flatten tbr cl)))
    (('not ('if tst tbr *nil*)) ; (not (and tst tbr))
     (add-lit-and-flatten (dumb-negate-lit tst)
                          (add-lit-and-flatten (dumb-negate-lit tbr) cl)))
    (('not ('if tst *nil* fbr)) ; (not (and (not tst) tbr))
     (add-lit-and-flatten tst
                          (add-lit-and-flatten (dumb-negate-lit fbr) cl)))
    (& (add-to-set-equal lit cl))))

(defun norm-clause (clause)

; Perform some basic simplifications and flatten ORs.

  (cond ((endp clause) nil)
        (t (add-lit-and-flatten (norm-lit (car clause) nil nil)
                                (norm-clause (cdr clause))))))

(defun extend-clause-lst (cl cl-lst acc)
  (cond ((endp cl-lst) (cons cl (reverse acc)))
        ((subsumes nil cl (car cl-lst) nil)
         (extend-clause-lst cl (cdr cl-lst) acc))
        ((subsumes nil (car cl-lst) cl nil)
         (revappend acc cl-lst))
        (t (extend-clause-lst cl (cdr cl-lst) (cons (car cl-lst) acc)))))

(defun norm-clause-lst-1 (cl-lst)
  (cond ((endp cl-lst) nil)
        (t
         (extend-clause-lst (norm-clause (car cl-lst))
                            (norm-clause-lst-1 (cdr cl-lst))
                            nil))))

(defun norm-clause-lst (cl-lst)
  (norm-clause-lst-1
   (subsumption-replacement-loop (merge-sort-length cl-lst) nil nil)))

(defun td-remove-lambdas-cl-lst (cl-lst)
  (cond ((endp cl-lst) nil)
        (t (cons (mv-let (changedp cl)
                   (remove-lambdas-lst (car cl-lst))
                   (declare (ignore changedp))
                   cl)
                 (td-remove-lambdas-cl-lst (cdr cl-lst))))))

(defun td-cl-lst (names bodies ruler-extenders-lst measure-alist mp rel
                        clause-size-limit wrld)

; This is the top-level "normalization" routine for termination clause-sets, to
; increase subsumption.

  (let ((clause-set
         (termination-theorem-clauses
          names
          bodies ; (get-unnormalized-bodies names wrld)
          measure-alist mp rel
          ruler-extenders-lst ; (ruler-extenders-lst names wrld)
          wrld)))
    (cond ((and clause-size-limit
                (= (cons-count-bounded-ac clause-set 0 clause-size-limit)
                   clause-size-limit))
           :failed)
          (t (norm-clause-lst
              (td-remove-lambdas-cl-lst
               (td-replace-fn-cl-lst (car names) clause-set wrld)))))))

(defrec roots-alist-entry

; Warning: Keep root as the car, since we may use assoc to find its entry.

; Root is a symbol, intended to be a function symbol (in a suitable world) with
; the indicated arity.  Book can be nil, or else a "book representation", which
; is either a string or else is a sysfile (:system . <relative-filename>) that
; represents a community book.

  (root arity . book)
  t)

(defrec td-candidate

; Let C be a td-candidate record.  The :roots-alist field of C is a a list of
; roots-alist-entry records.  For each such record, R, when its :book field is
; included then its :root has as its 'justification property the one stored in
; the :justification field of C, up to alpha-equivalence (see
; alpha-variant-p-justification).  Each such :root has a normalized termination
; clause-set that is subsumption-equivalent to the one stored in the
; :clause-list field.  Finally, the first record R in the :roots-alist is
; special: the :justification and :clause-list of C correspond exactly to the
; :root of R (not merely alpha-equivalence or subsumption-equivalent).

  (justification
   clause-list
   .
   roots-alist)
  t)

(defun alpha-variant-p (term1 term2)
  (and (one-way-unify-p term1 term2)
       (one-way-unify-p term2 term1)))

(defun alpha-variant-p-justification (j1 j2)

; The :subset is just the variables of the :measure.  So we don't compare the
; two :subset fields.

  (and (eq (access justification j1 :subversive-p)
           (access justification j2 :subversive-p)) ; both are nil here
       (eq (access justification j1 :mp)
           (access justification j2 :mp))
       (eq (access justification j1 :rel)
           (access justification j2 :rel))
       (let ((re1 (access justification j1 :ruler-extenders))
             (re2 (access justification j2 :ruler-extenders)))
         (or (equal re1 re2)
             (and (symbol-listp re1)
                  (symbol-listp re2)
                  (set-equalp-eq re1 re2))))
       (alpha-variant-p (access justification j1 :measure)
                        (access justification j2 :measure))))

(defun td-cands-alist-1 (td-cand just alist acc)

; See td-cands-alist.

  (cond ((endp alist)
         (acons just (list td-cand) acc))
        ((alpha-variant-p-justification just (caar alist))
         (revappend (cdr alist)
                    (acons (caar alist)
                           (cons td-cand (cdar alist))
                           acc)))
        (t
         (td-cands-alist-1 td-cand just (cdr alist) (cons (car alist) acc)))))

(defun td-cands-alist (td-cands acc)

; Organizes the candidates into equivalence classes, by accumulating into the
; alist, acc.  Each key, which is a justification record, is associated with
; candidates whose justification agrees with key except that its measure need
; only be an alpha-variant of the :measure of key.

; Since these are accumulated into acc, it may be desirable to reverse td-cands
; so that the order of candidates associated with a given key in the result
; respects the original order of candidates in td-cands.  Note that we make no
; claim about the order of elements in the resulting alist, only within the cdr
; of any member of alist.

  (cond ((endp td-cands) acc)
        (t
         (td-cands-alist (cdr td-cands)
                         (td-cands-alist-1 (car td-cands)
                                           (access td-candidate (car td-cands)
                                                   :justification)
                                           acc
                                           nil)))))
