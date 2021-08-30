; ACL2 Version 8.4 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2021, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

; Table of contents.
;
; 0.    PRELIMINARY MACROS
; I.    INTRODUCTION AND DATA TYPES
; II.   OP-ALIST
; III.  HASH OPERATIONS
; IV.   HASH OPERATIONS: QUOTEPS
; V.    BDD RULES AND ONE-WAY UNIFIER
; VI.   SOME INTERFACE UTILITIES
; VII.  MAIN ALGORITHM
; VIII. TOP-LEVEL (INTERFACE) ROUTINES
; IX.   COMPILING THIS FILE AND OTHER HELPFUL TIPS
;

; Mx-id-bound is currently 438619, perhaps too low.  We could perhaps fix this
; by changing how we deal with close to 16 args in op-hash-index1, and by
; changing 131 in if-hash-index.

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; 0. PRELIMINARY MACROS ;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro mvf (x &rest rest)

; We often wish to pass back a multiple value such that the first value is a
; fixnum.  Efficiency is apparently improved in GCL when that fixnum is not
; "boxed," but instead is treated as a raw C integer.  Currently ACL2 provides
; mechanisms for this, but they require that an appropriate THE expression
; surround such a value when it is the first value passed back by MV.  (Note
; that there seems to be no way to keep GCL from boxing fixnums in other than
; the first argument position of MV.)

  `(mv (the-fixnum ,x) ,@rest))

(defmacro logandf (&rest args)
  (xxxjoin-fixnum 'logand args -1))

(defmacro logxorf (&rest args)
  (xxxjoin-fixnum 'logxor args 0))

(defmacro logiorf (&rest args)
  (xxxjoin-fixnum 'logior args 0))

(defmacro ashf (x y)
  (list 'the-fixnum
        (list 'ash (list 'the-fixnum x) (list 'the-fixnum y))))

(defmacro mx-id-bound ()

; This bound on mx-id must be such that our calls of +f and *f involving mx-id
; produce fixnums.  At this writing the most severe such test is in
; op-hash-index1; see the comment there.

  (1- (floor (fixnum-bound) 153)))

(defmacro 1+mx-id (x)

; DILEMMA:  Do we let this macro box (1+ x) or not, and if so, when?  Here are
; some thoughts on the issue.

; Use this macro to increment mx-id,in order to guarantee that mx-id remains a
; fixnum.  X is known to be a nonnegative fixnum; this macro checks that we
; keep it a fixnum by adding 1 to it.  It actually checks even more, namely,
; that

  `(the-fixnum
    (let ((x ,x))
      (declare (type (signed-byte 30) x))

; Should we really include the declaration above?  The main reason seems to be
; in order for the incrementing operation below to run fast, but in fact we
; have done several experiments and it seems that the current version of this
; code is optimal for performance.  That's a bit surprising, since each mx-id
; gets consed into a list anyhow (a cst), and hence is boxed in GCL (which is
; the only list we are talking about here).  So, there wouldn't appear to be
; any particular advantage in wrapping the-fixnum around this form.  At any
; rate, the performance issues here seem to be quite minor.

; A typical use of this macro is of the form

;  (let ((new-mx-id (1+mx-id mx-id)))
;    (declare (type (signed-byte 30) new-mx-id))
;    (let ((new-cst (make-leaf-cst
;                    new-mx-id
;                    term
;                    nil)))
;      (mvf new-mx-id
;           ...)))

; Note that make-leaf-cst will box new-mx-id -- after all, it is consing
; new-mx-id into a list.  The present approach delays this boxing until that
; time, so that we don't have to unbox new-mx-id in the mvf form above.  The
; unboxed new-mx-id may actually never benefit from being unboxed, and in fact
; we may want to rework our entire bdd code so that mx-ids are always boxed.

      (cond ((< x ,(mx-id-bound))
             (1+f x))
            (t (the-fixnum ; the-fixnum call may help with proclaiming
                (er-hard-val 0 'bdd
                    "Maximum id for bdds exceeded.  Current maximum id is ~x0."
                    x)))))))

(defmacro bdd-error (mx-id fmt-string fmt-alist bad-cst ttree)

; Perhaps it would be more "natural" to define this macro to return

; `(mvf ,mx-id ,(cons fmt-string ,fmt-alist) ,bad-cst <nil-call-stack> ,ttree)

; since then we can view the result as

; `(mvf ,mx-id ,<msg> ,bad-cst ,call-stack ,ttree)

; However, we would like to have a very fast test for whether the tuple
; returned designates an error.  The present approach allows us to test with
; stringp on the second value returned.  We take advantage of that in the
; definition of bdd-mv-let.

; Note that the order of the first two values should not be changed:  we
; declare mx-id to be a fixnum at some point, and we we want the second
; position to be tested by stringp to see if we have an "error" situation.

; Keep this in sync with bdd-mv-let.

  `(mvf ,mx-id ,fmt-string (cons ,fmt-alist ,bad-cst)

; The following nil is really an initial value of the bdd-call-stack that is
; ultimately to be placed in a bddnote.  At the time of this writing,
; bdd-mv-let is the only place where we update this stack.

        nil
        ,ttree))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; I. INTRODUCTION AND DATA TYPES ;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; In this work we represent terms in what we call the cheap syntax.  Such a
; "term" is called a "csterm".  Bryant would call it a "node."

; We are interested in normalized IF expressions corresponding to ACL2 terms.
; If x is not itself an IF term, then (IF x y z) is represented by

; `(k ,x ,boolp ,y . ,z)

; where k is a natural number that is uniquely associated with <x,y,z> and
; boolp is t if the term is known to be Boolean.  The association between k and
; <x,y,z> is arranged via a "hash table" discussed below.  The objective is
; that two canonicalized IF expressions are equal (and therefore represent the
; same term) iff their unique identifiers (cars) are =.

; We also represent "leaf" ACL2 terms, which are generally IF-free, as csts of
; a slightly different sort; see below.  (Note that these may have IFs in them
; because certain function symbols are "blocked" -- see bdd-constructors.)

; The list of "leaf" csts arising from variables in the input term, which we
; typically call leaf-cst-list, is passed around unchanged by various of our
; functions.  We rely on the op-ht to find csts for other leaves, and to avoid
; re-consing up leaf csts.

; The shapes of csts are as follows.  Note that two csts are equal iff their
; cars are =.

; Non-leaf:
; (unique-id tst boolp tbr . fbr) ; informally, represents (if tst tbr fbr)

; Leaf:
; (unique-id term boolp)
; where term is of one of the following forms:
;   variable
;   quotep
;   application of function symbol other than IF to a list of csts

; WARNING:  The definition of leafp below relies on the fact that leaf csts are
; exactly those whose final cdr is nil.  Do not succumb to the temptation to
; add a new field as the final cdr without taking this into account.

; Note:  It is tempting to replace the "term" in the last case by an ACL2 term,
; rather than an application of a function symbol to a list of csts.  However,
; the list of csts has presumably already been consed up, so we save the
; re-consing, awaiting the final decoding to build the actual ACL2 term if
; necessary.

; Macros for accessing canonicalized IFs:

(defmacro unique-id (x) `(the-fixnum (car ,x)))

(defmacro tst (x) `(cadr ,x)) ;a cst, not a number; but beware since tst=trm
                              ;and trm is a sort of term

; Note:  We found that 95% of the time on one test was being spent inside
; cst-boolp, when we used to keep this information directly in leaf nodes only.

(defmacro cst-boolp (x) `(caddr ,x))

(defmacro tbr (x) `(cadddr ,x))
(defmacro fbr (x) `(cddddr ,x))

(defmacro leafp (x)
  `(null (cdddr ,x)))

(defmacro trm (x) `(cadr ,x))

(defun bdd-constructors (wrld)
  (declare (xargs :guard
                  (and (plist-worldp wrld)
                       (alistp (table-alist 'acl2-defaults-table wrld)))))
  (let ((pair (assoc-eq :bdd-constructors (table-alist
                                           'acl2-defaults-table wrld))))
    (if pair
        (cdr pair)
      '(cons))))

(defun make-leaf-cst (unique-id trm boolp)

; We write the definition this way, rather than simply as something like (list*
; unique-id trm boolp ), in order to avoid repeatedly consing up '(t . nil) and
; '(nil . nil).

  (if boolp
      (list* unique-id trm '(t))
    (list* unique-id trm '(nil))))

(defun evg-fn-symb (x)

; This function takes the view that every explicit value can be constructed
; from 0.  It returns nil on 0, but, in principle, returns an appropriate
; function symbol otherwise.  At this point we choose not to support this idea
; in full, but instead we view cons as the only constructor.  We leave the full
; code in place as a comment, in case we choose to support this idea in the
; future.

;   (cond ((consp x) 'cons)
;         ((symbolp x) 'intern-in-package-of-symbol)
;         ((integerp x)
;          (cond ((< x 0) 'unary--)
;                ((< 0 x) 'binary-+)
;                (t nil)))
;         ((rationalp x)
;          (if (equal (numerator x) 1)
;              'unary-/
;            'binary-*))
;         ((complex-rationalp x)
;          'complex)
;         ((stringp x) 'coerce)
;         ((characterp x) 'char-code)
;         (t (er hard 'fn-symb "Unexpected object, ~x0."
;                x)))

  (cond ((consp x) 'cons)
        (t nil)))

(defun bdd-constructor-trm-p (trm bdd-constructors)
  (and (consp trm)
       (if (fquotep trm)
           (member-eq (evg-fn-symb (cadr trm)) bdd-constructors)
         (member-eq (car trm) bdd-constructors))))

(defun evg-type (x)

; This function takes the view that every explicit value can be constructed
; from 0.  It returns nil on 0, but, in principle, returns an appropriate
; function symbol otherwise.  See also evg-fn-symb.

  (cond ((consp x) 'consp)
        ((symbolp x) 'symbol)
        ((integerp x) 'integer)
        ((rationalp x) 'rational)
        ((complex-rationalp x) 'complex-rational)
        ((stringp x) 'string)
        ((characterp x) 'character)
        (t (er hard 'fn-symb "Unexpected object, ~x0."
               x))))

(defun make-if-cst (unique-id tst tbr fbr bdd-constructors)

; The second value returned is always a new cst.  The first value is non-nil
; when there is an "error", in which case that value is of the form (fmt-string
; . alist).

  (let* ((boolp (and (cst-boolp tbr)
                     (cst-boolp fbr)))
         (new-cst (list* unique-id tst boolp tbr fbr)))
    (cond
     ((or (and (leafp tbr)
               (bdd-constructor-trm-p (trm tbr) bdd-constructors))
          (and (leafp fbr)
               (bdd-constructor-trm-p (trm fbr) bdd-constructors)))
      (mv (msg "Attempted to create IF node during BDD processing with ~@0, ~
                which would produce a non-BDD term (as defined in :DOC ~
                bdd-algorithm).  See :DOC show-bdd."
               (let ((true-fn (trm tbr))
                     (false-fn (trm fbr)))
                 (cond
                  ((and (leafp tbr)
                        (bdd-constructor-trm-p (trm tbr) bdd-constructors))
                   (cond
                    ((and (leafp fbr)
                          (bdd-constructor-trm-p (trm fbr) bdd-constructors))
                     (msg "true branch with ~#0~[function symbol ~x1~/explicit ~
                         value of type ~x2~] and false branch with ~
                         ~#3~[function symbol ~x4~/explicit value  of type ~
                         ~x5~]"
                          (if (eq (car true-fn) 'quote) 1 0)
                          (car true-fn)
                          (and (eq (car true-fn) 'quote)
                               (evg-type (cadr true-fn)))
                          (if (eq (car false-fn) 'quote) 1 0)
                          (car false-fn)
                          (and (eq (car false-fn) 'quote)
                               (evg-type (cadr false-fn)))))
                    (t (msg "true branch with ~#0~[function symbol ~x1~/explicit ~
                           value of type ~x2~]"
                            (if (eq (car true-fn) 'quote) 1 0)
                            (car true-fn)
                            (and (eq (car true-fn) 'quote)
                                 (evg-type (cadr true-fn)))))))
                  (t (msg "false branch with ~#0~[function symbol ~x1~/explicit ~
                           value of type ~x2~]"
                          (if (eq (car false-fn) 'quote) 1 0)
                          (car false-fn)
                          (and (eq (car false-fn) 'quote)
                               (evg-type (cadr false-fn))))))))
          new-cst))
     (t (mv nil new-cst)))))

; We will always represent nil and t as described above.  To make this work, we
; must set the initial mx-id to 2, so the next unique id generated is 3.

; It is nearly inconsequential which of t or nil has the smaller id, but we
; find it handy to give t the smaller id, as noted in a comment in the
; definition of combine-op-csts-comm.

(defconst *cst-t*   (make-leaf-cst 1 *t* t))
(defconst *cst-nil* (make-leaf-cst 2 *nil* t))

(defmacro cst= (cst1 cst2)
  `(= (unique-id ,cst1)
      (unique-id ,cst2)))

(defmacro cst-tp (cst)
  `(= (unique-id ,cst) 1))

(defmacro cst-nilp (cst)
  `(= (unique-id ,cst) 2))

(defmacro cst-varp (cst)
  `(< 2 (unique-id ,cst)))

(defun cst-nonnilp (cst)
  (and (leafp cst)
       (if (quotep (trm cst))
           (not (cst-nilp cst))

; Consider other types here besides cons, e.g., that of numbers.  We may want
; to pass in a list of functions that have been checked to have type-sets that
; are disjoint from *ts-nil* and variable-free.  We would use a member-eq test
; below against such a list.  This list of function symbols could be determined
; easily from the list of all function symbols in op-alist.

         (ffn-symb-p (trm cst) 'cons))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; II. OP-ALIST ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The goal of this section is to define functions op-alist and op-alist-info.
; See those definitions below for more details.  Briefly, these functions
; respectively build and do lookup in a so-called op-alist, which is a list of
; entries that describe function symbols occurring in the term for which we
; want to build a bdd.

(defun bool-mask1 (formals vars rune)

; Formals is the list of formals of a function symbol, and vars is a list of
; variables contained in formals such that every call of that function returns
; either t or nil, assuming that each var in vars is of boolean type.  This
; function returns a list in one-one correspondence with formals (but see
; below), replacing a formal by t if it belongs to vars (thus indicating that
; this position's actual might be returned) and nil if not.  Rune is a
; type-prescription record, used simply for the final cdr of the list returned
; (after all the t's and nil's have been listed as indicated above).

  (cond
   ((endp formals) rune)
   ((member-eq (car formals) vars)
    (cons t (bool-mask1 (cdr formals) vars rune)))
   (t (cons nil (bool-mask1 (cdr formals) vars rune)))))

(defun boolean-term-var (x)

; X is a term.  If x is of the form (booleanp v) or something "clearly"
; equivalent to it, return v.  Otherwise return nil.

  (and (not (variablep x))
       (not (fquotep x))
       (cond
        ((and (eq (ffn-symb x) 'booleanp)
              (variablep (fargn x 1)))
         (fargn x 1))
        ((eq (ffn-symb x) 'if)

; Check for translated version of (or (equal v t) (equal v nil)) or
; (or (equal v nil) (equal v t)).

         (let ((test (fargn x 1))
               (tbr (fargn x 2))
               (fbr (fargn x 3)))
           (and (ffn-symb-p test 'equal)
                (let ((v (fargn test 1)))
                  (and (variablep v)
                       (let ((b (fargn test 2)))
                         (and (or (equal b *t*) (equal b *nil*))
                              (let ((c (if (equal b *t*) *nil* *t*)))
                                (if (and (equal test tbr)
                                         (equal fbr (fcons-term* 'equal v c)))
                                    v
                                  nil)))))))))
        (t nil))))

(defun boolean-hyps-vars (hyps)

; If hyps consists of terms of the form (booleanp v), or perhaps the
; equivalent, then we return a list indices of such v.

  (if (endp hyps)
      nil
    (let ((rst (boolean-hyps-vars (cdr hyps))))
      (if (eq rst t)
          t
        (let ((v (boolean-term-var (car hyps))))
          (if v
              (cons v rst)
            t))))))

(defun first-boolean-type-prescription (type-prescription-list ens formals)

; This function finds the most recent enabled type-prescription rule from the
; given list whose :basic-ts is boolean and :hyps are all of the form (booleanp
; v) or a "clearly" equivalent form, where the :term is of the form (fn ... v
; ...).  It returns two values.  The first is the :rune of the rule, which is
; non-nil if and only if such a rule is found.  If the first value is non-nil,
; then the second value is a "mask" as described in the comment in bool-mask.

  (cond
   ((endp type-prescription-list)
    (mv nil nil))
   ((and (enabled-numep
          (access type-prescription (car type-prescription-list) :nume)
          ens)
         (ts-subsetp
          (access type-prescription (car type-prescription-list) :basic-ts)
          *ts-boolean*))
    (let* ((tp (car type-prescription-list))
           (hyps (access type-prescription tp :hyps))
           (vars (access type-prescription tp :vars)))
      (if hyps
          (let ((more-vars (boolean-hyps-vars hyps)))
            (if (or (eq more-vars t)
                    (not (subsetp-eq more-vars formals)))
                (first-boolean-type-prescription (cdr type-prescription-list)
                                                 ens
                                                 formals)
              (mv (access type-prescription tp :rune)
                  (union-eq vars more-vars))))
        (mv (access type-prescription tp :rune)
            vars))))
   (t (first-boolean-type-prescription
       (cdr type-prescription-list) ens formals))))

(defun recognizer-rune (recognizer-alist wrld ens)
  (cond
   ((endp recognizer-alist) nil)
   ((enabled-runep (access recognizer-tuple (car recognizer-alist) :rune)
                   ens
                   wrld)
    (access recognizer-tuple (car recognizer-alist) :rune))
   (t (recognizer-rune (cdr recognizer-alist) wrld ens))))

(defun bool-mask (fn wrld ens)

; Returns a "mask" that is a suitable argument to bool-flg.  Thus, this
; function returns either nil or else a mask of the form

; (list* b1 b2 ... bn rune)

; where rune is a type prescription rune and each bi is either t or nil.  The
; function bool-flg will check that a given call of fn is boolean, returning
; rune if it can confirm this fact.  A bi must be marked t if the conclusion
; that the call of fn is boolean requires a check that the formal corresponding
; to bi is boolean.

; We give special treatment not only to compound recognizers, but also to
; Boolean-valued primitives, since these will not generally have built-in
; type-prescription rules.

  (cond
   ((or (eq fn 'equal) (eq fn '<))
    (list* nil nil *fake-rune-for-type-set*))
   ((eq fn 'not)

; `Not' is so basic that we could probably skip this case, but we might as well
; handle it appropriately.

    (list* nil *fake-rune-for-type-set*))
   (t
    (let ((rune (recognizer-rune (getpropc fn 'recognizer-alist nil wrld)
                                 wrld
                                 ens))
          (formals (formals fn wrld)))
      (if rune
          (bool-mask1 formals nil rune)
        (mv-let (rune vars)

; We only consider the most recent type prescription with Boolean base type.
; Some day we might consider somehow combining all such type prescription
; rules.

                (first-boolean-type-prescription
                 (getpropc fn 'type-prescriptions nil wrld)
                 ens
                 formals)
                (and rune
                     (bool-mask1 formals vars rune))))))))

(defun commutative-p1 (fn lemmas ens)

; Fn is assumed to have arity 2 in the current ACL2 world.

  (cond
   ((endp lemmas) nil)
   (t (if (and (member-eq (access rewrite-rule (car lemmas) :subclass)
                          '(backchain abbreviation))
               (equal (access rewrite-rule (car lemmas) :equiv) 'equal)
               (enabled-numep (access rewrite-rule (car lemmas) :nume) ens)
               (null (access rewrite-rule (car lemmas) :hyps))
               (let ((lhs (access rewrite-rule (car lemmas) :lhs))
                     (rhs (access rewrite-rule (car lemmas) :rhs)))
                 (and (or (eq (ffn-symb lhs) fn)
                          (er hard 'commutative-p1
                              "We had thought we had a rewrite rule with :lhs ~
                               being a call of ~x0, but the :lhs is ~x1."
                              fn lhs))
                      (ffn-symb-p rhs fn)
                      (variablep (fargn lhs 1))
                      (variablep (fargn lhs 2))
                      (not (eq (fargn lhs 1) (fargn lhs 2)))
                      (equal (fargn lhs 1) (fargn rhs 2))
                      (equal (fargn lhs 2) (fargn rhs 1)))))
          (access rewrite-rule (car lemmas) :rune)
        (commutative-p1 fn (cdr lemmas) ens)))))

(defun find-equivalence-rune (fn rules)
  (cond
   ((endp rules)
    nil)
   ((eq (access congruence-rule (car rules) :equiv) fn)
    (let ((rune (access congruence-rule (car rules) :rune)))
         (if (eq (car rune) :equivalence)
             rune
           (find-equivalence-rune fn (cdr rules)))))
   (t (find-equivalence-rune fn (cdr rules)))))

(defun equivalence-rune1 (fn congruences)

; For example, if fn is 'iff then congruences may contain:

; (EQUAL ((126 IFF :EQUIVALENCE IFF-IS-AN-EQUIVALENCE))
;        ((126 IFF :EQUIVALENCE IFF-IS-AN-EQUIVALENCE)))

; But the two singleton lists above can contain other members too.  See the
; Essay on Equivalence, Refinements, and Congruence-based Rewriting.

; See add-equivalence-rule.

  (cond
   ((endp congruences)
    (er hard 'equivalence-rune
        "Failed to find an equivalence rune for function symbol ~x0."
        fn))
   (t (let ((x (car congruences)))
        (case-match x
                    (('equal rules1 rules2)
                     (let ((rune (find-equivalence-rune fn rules1)))
                       (if (and rune
                                (equal rune (find-equivalence-rune fn rules2)))
                           rune
                         (equivalence-rune1 fn (cdr congruences)))))
                    (& (equivalence-rune1 fn (cdr congruences))))))))

(defun equivalence-rune (fn wrld)
  (declare (xargs :guard (equivalence-relationp fn wrld)))
  (cond
   ((eq fn 'equal)
    (fn-rune-nume 'equal nil nil wrld))
   (t (equivalence-rune1 fn
                         (getpropc fn 'congruences
                                   '(:error "See equivalence-rune.")
                                   wrld)))))

(defun commutative-p (fn ens wrld)

; Note that if the value is non-nil, it is a rune justifying the commutativity
; of the given function.

  (and (= (arity fn wrld) 2)
       (if (equivalence-relationp fn wrld)
           (equivalence-rune fn wrld)
           (commutative-p1 fn
                           (getpropc fn 'lemmas nil wrld)
                           ens))))

; To memoize the various merging operations we will hash on the opcodes.
; Increasing each by a factor of 3 was intended to make it spread out a little
; more, but (at least this has been true at one time) it doesn't have much of
; an effect.

(defun op-alist (fns acc i ens wrld)

; Build a list of entries (op opcode comm-p enabled-executable-counterpartp
; mask).  The next index to use is i.  Call this as in (op-alist (remove1-eq
; 'if (all-fnnames term)) nil 6 (ens state) (w state)).  Keep this in sync with
; op-alist-info.

; Note that if comm-p is non-nil, it is a rune justifying the commutativity of
; the given function.  Similarly, if enabled-executable-counterpartp is non-nil
; then it is an :executable-counterpart rune.

  (cond
   ((endp fns) acc)
   ((> i (mx-id-bound))
    (er hard 'bdd
        "We are very surprised to see that, apparently, your problem for bdd ~
         processing involves ~x0 function symbols!  We cannot handle this many ~
         function symbols."
        (/ i 3)))
   (t (op-alist (cdr fns)
                (cons (list* (car fns)
                             i
                             (commutative-p (car fns) ens wrld)
                             (and (not (getpropc (car fns) 'constrainedp nil
                                                 wrld))
                                  (enabled-xfnp (car fns) ens wrld)
                                  (fn-rune-nume (car fns) nil t wrld))
                             (bool-mask (car fns) wrld ens))
                      acc)
                (+ 3 i)
                ens
                wrld))))

(defun op-alist-info (fn op-alist)

; Returns (mv opcode comm-p enabled-exec-p mask).  Keep this in sync with
; op-alist.

  (cond
   ((endp op-alist)
    (mv (er hard 'op-alist-info
            "Function not found:  ~x0"
            fn)
        nil nil nil))
   ((eq fn (caar op-alist))
    (let ((info (cdar op-alist)))
      (mv (car info)
          (cadr info)
          (caddr info)
          (cdddr info))))
   (t (op-alist-info fn (cdr op-alist)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; III. HASH OPERATIONS ;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro if-op-code () 3)

(defmacro hash-size ()

; Do not quote the body of this definition.  We want it computed at
; definition/compile time!

; At one time we used a defconst here, but then we realized that we would
; (apparently, at least, in GCL) have to pay the price both of looking up the
; value of that variable and also unboxing it for fixnum operations.  Although
; a little experimentation did not yield meaningful evidence that there is
; really an impact on performance, we proceed with a macro.

; WARNING:  Do not increase this size too close to (fixnum-bound).  See the
; warning in op-hash-index-evg.

  (1- (expt 2 15)))

; We have two hash arrays, 'if-ht for assigning unique-ids to csts, and 'op-ht
; for memo-izing the merge operators.  In each case the array assigns "buckets"
; to indices.

; Buckets in an if-ht are lists of non-leaf csts.

; Buckets in an op-ht are lists of entries of the form (cst op . args), where
; args is a list of csts.  The length of the list is the arity of op.
; Exception:  op can be quote, in which case args is a list containing a single
; evg.

(defmacro if-hash-index (x y z)

; Note that (+ 131 2 1) does not exceed 153.  See the comment about mx-id-bound
; in op-hash-index1.  There is probably nothing sacred about the choices of
; these three numbers 131, 2, and 1, although it seems good that they are
; relatively prime.

  `(logandf (+f (*f 131 (unique-id ,x))
                (*f 2 (unique-id ,y))
                (unique-id ,z))
            (hash-size)))

(defun op-hash-index1 (args i acc)

; There should be no more than 16 args before we "turn around", so that the
; multiplier on unique-ids is no more than (1+ (+ 2 3 ... 17)) = 153.  (The
; `1+' is because in op-hash-index we add in the op-code as well.  Op-codes are
; also bounded by mx-id-bound -- see op-alist -- as are of course unique-ids.)
; See the comment in mx-id-bound.

; If we want to increase the (mx-id-bound), we believe that we could start the
; "turnaround" here earlier.  But we have not yet checked this claim carefully.

  (declare (type (signed-byte 30) i acc)
           (xargs :measure (acl2-count args)))
  (the-fixnum
   (cond
    ((endp args) (if (< acc 0) (- acc) acc))
    ((or (= (the-fixnum i) 18)
         (= (the-fixnum i) -1))
     (if (> acc 0)
         (op-hash-index1 args -17 acc)
       (op-hash-index1 args 2 acc)))
    (t (op-hash-index1 (cdr args)
                       (1+f i)
                       (+f acc
                           (*f i
                               (unique-id (car args)))))))))

(defmacro op-hash-index (op-code args)
  `(logandf (+f ,op-code
                (op-hash-index1 ,args 2 1))
            (hash-size)))

(defmacro op-hash-index-2 (op-code arg1 arg2)

; This special case of op-hash-index is used for commutative operators in
; chk-memo-2.

  `(logandf (+f ,op-code
                (*f 2 (unique-id ,arg1))
                (*f 3 (unique-id ,arg2)))
            (hash-size)))

(defmacro op-hash-index-if (arg1 arg2 arg3)
  `(logandf (+f (if-op-code)
                (*f 2 (unique-id ,arg1))
                (*f 3 (unique-id ,arg2))
                (*f 4 (unique-id ,arg3)))
            (hash-size)))

; Having found the bucket associated with the hash-index, here is how
; we search it.

(defun if-search-bucket (x y z lst)

; Here lst is a list of non-leaf csts.

  (cond ((null lst) nil)
        ((and (cst= x (tst (car lst)))
              (cst= y (tbr (car lst)))
              (cst= z (fbr (car lst))))
         (car lst))
        (t (if-search-bucket x y z (cdr lst)))))

(defun cst=-lst (x y)
  (cond
   ((endp x) t)
   (t (and (cst= (car x) (car y))
           (cst=-lst (cdr x) (cdr y))))))

(defmacro eq-op (x y)

; This test must change if we start allowing LAMBDAs as operators.

  `(eq ,x ,y))

(defun op-search-bucket (op args lst)

; Here op is a function symbol and lst is a tail of a bucket from an op-ht.
; Thus, lst is a list of elements of the form (cst op0 . args0), where args0 is
; a list of csts unless op0 is 'quote, which it is not if op0 is op.

  (cond ((null lst) nil)
        ((and (eq-op op
                     (cadr (car lst)))
              (cst=-lst args (cddr (car lst))))
         (car (car lst)))
        (t (op-search-bucket op args (cdr lst)))))

(defun op-search-bucket-2 (op arg1 arg2 lst)

; This is a version of op-search-bucket for binary functions.  This is merely
; an optimization we use for commutative operators, since we know that they are
; binary.  We could of course use this for all binary operators, but the point
; here is that for commutative operators we delay consing up the commuted
; argument list until it is necessary.  See combine-op-csts-comm.

  (cond ((null lst) nil)
        ((and (eq-op op
                     (cadr (car lst)))
              (let ((args (cddr (car lst))))
                (and (cst= arg1 (car args))
                     (cst= arg2 (cadr args)))))
         (car (car lst)))
        (t (op-search-bucket-2 op arg1 arg2 (cdr lst)))))

(defun op-search-bucket-if (arg1 arg2 arg3 lst)

; This is a version of op-search-bucket that does not require us to cons up the
; arguments into a list, used in chk-memo-if.  This is merely an optimization
; we use since IF is such a common operation.

  (cond ((null lst) nil)
        ((and (eq-op 'if
                     (cadr (car lst)))
              (let ((args (cddr (car lst))))
                (and (cst= arg1 (car args))
                     (cst= arg2 (cadr args))
                     (cst= arg3 (caddr args)))))
         (car (car lst)))
        (t (op-search-bucket-if arg1 arg2 arg3 (cdr lst)))))

(defun chk-memo (op-code op args op-ht)

; If <op,arg1,arg2,...> has an entry in op-ht, return 0 and the entry.
; Otherwise, return the hash index for <op-code,arg1,arg2,...> (simply to avoid
; its recomputation) and NIL.  Entries are of the form (result op . args).  We
; return the hash index as the first value so that we can avoid boxing up a
; fixnum for it in GCL.

  (declare (type (signed-byte 30) op-code))
  (the-mv
   2
   (signed-byte 30)
   (let ((n (op-hash-index op-code args)))
     (declare (type (signed-byte 30) n))
     (let ((ans (op-search-bucket op args (aref1 'op-ht op-ht n))))
       (cond (ans (mvf 0 ans))
             (t (mvf n nil)))))))

(defun chk-memo-2 (op-code op arg1 arg2 op-ht)

; This is merely an optimization of chk-memo for the case where the operator is
; binary, in particularly for commutative operators; see the comment in
; op-search-bucket-2.

  (declare (type (signed-byte 30) op-code))
  (the-mv
   2
   (signed-byte 30)
   (let ((n (op-hash-index-2 op-code arg1 arg2)))
     (declare (type (signed-byte 30) n))
     (let ((ans (op-search-bucket-2 op arg1 arg2 (aref1 'op-ht op-ht n))))
       (cond (ans (mvf 0 ans))
             (t (mvf n nil)))))))

(defun chk-memo-if (arg1 arg2 arg3 op-ht)

; This is merely an optimization of chk-memo for the case where the operator is
; if, which is likely very common.  Note that by treating this special case as
; we do, we avoid consing up the list of arguments in some cases; see
; combine-if-csts.

  (the-mv
   2
   (signed-byte 30)
   (let ((n (op-hash-index-if arg1 arg2 arg3)))
     (declare (type (signed-byte 30) n))
     (let ((ans (op-search-bucket-if arg1 arg2 arg3 (aref1 'op-ht op-ht n))))
       (cond (ans (mvf 0 ans))
             (t (mvf n nil)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; IV. HASH OPERATIONS: QUOTEPS ;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro half-hash-size ()
  (floor (hash-size) 2))

(defmacro fourth-hash-size ()
  (floor (hash-size) 4))

(defun op-hash-index-string (index acc string)
  (declare (type (signed-byte 30) index acc))
  (the-fixnum
   (cond
    ((= index 0) acc)
    (t (let ((index (1- (the-fixnum index))))
         (declare (type (signed-byte 30) index))
         (op-hash-index-string
          index
          (logandf (hash-size)
                   (+f acc (char-code (char string index))))
          string))))))

(defun op-hash-index-evg (evg)
  (the-fixnum
   (cond
    ((integerp evg)
     (logandf (hash-size) evg))
    ((rationalp evg)
     (logandf (hash-size)
              (+ (numerator evg)
                 (* 17 (denominator evg)))))
    ((acl2-numberp evg)
     (logandf (hash-size)
              (+f (op-hash-index-evg (realpart evg))
                  (op-hash-index-evg (imagpart evg)))))
    ((characterp evg)
     (+f (fourth-hash-size)
         (char-code evg)))
    ((symbolp evg)
     (logandf (hash-size)

; WARNING:  Here we assume that (* 19 (hash-size)) is a fixnum.  We know it is
; because the hash index is at most (hash-size), which is well under
; (fixnum-bound).

              (*f 19 (op-hash-index-evg (symbol-name evg)))))
    ((stringp evg)
     (the-fixnum
      (op-hash-index-string (the-fixnum! (length evg) 'bdd)
                            (half-hash-size) evg)))
    (t ;cons
     (logandf (hash-size)
              (+f (op-hash-index-evg (car evg))
                  (*f 2 (op-hash-index-evg (cdr evg)))))))))

(defun op-search-bucket-quote (evg bucket)
  (cond ((null bucket) nil)
        ((and (eq-op 'quote
                     (cadr (car bucket)))
              (equal evg (caddr (car bucket))))
         (car (car bucket)))
        (t (op-search-bucket-quote evg (cdr bucket)))))

(defun chk-memo-quotep (term op-ht)
  (the-mv
   2
   (signed-byte 30)
   (let ((n (op-hash-index-evg (cadr term))))
     (declare (type (signed-byte 30) n))
     (let ((ans (op-search-bucket-quote
                 (cadr term)
                 (aref1 'op-ht op-ht n))))

; One might think that the calls of the-fixnum just below are not necessary,
; but in fact they do appear to produce better compiled code in GCL.

       (cond (ans (mvf 0 ans))
             (t (mvf n nil)))))))

(defun bdd-quotep (term op-ht mx-id)
  (declare (type (signed-byte 30) mx-id))
  (the-mv
   3
   (signed-byte 30)
   (cond
    ((equal term *t*)
     (mvf mx-id *cst-t* op-ht))
    ((equal term *nil*)
     (mvf mx-id *cst-nil* op-ht))
    (t
     (mv-let (hash-index ans)
             (chk-memo-quotep term op-ht)
             (declare (type (signed-byte 30) hash-index))
             (cond
              (ans (mvf mx-id ans op-ht))
              (t (let ((new-mx-id (1+mx-id mx-id)))
                   (declare (type (signed-byte 30) new-mx-id))
                   (let ((new-cst (make-leaf-cst
                                   new-mx-id
                                   term
                                   nil)))
                     (mvf new-mx-id
                          new-cst
                          (aset1-trusted 'op-ht op-ht hash-index
                                         (cons

; The following is the same as (list new-cst 'quote (cadr term)), but saves a
; cons.

                                          (cons new-cst term)
                                          (aref1 'op-ht op-ht
                                                 hash-index)))))))))))))

(defmacro bdd-quotep+ (term op-ht if-ht mx-id ttree)
  `(mv-let (mx-id cst op-ht)
           (bdd-quotep ,term ,op-ht ,mx-id)
           (declare (type (signed-byte 30) mx-id))
           (mvf mx-id cst op-ht ,if-ht ,ttree)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; V. BDD RULES AND ONE-WAY UNIFIER ;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We could just use the rewrite-rule data structures already existing in the
; ACL2 world.  However, we suspect that it is a good idea, in order to support
; computationally intensive bdd computations, to avoid having to look at the
; enabled structure or dig deep into a rewrite rule in order to find the
; various fields we need.  In fact, we want to have the lhs available as
; quickly as possible, since that field is used the most.

(defrec bdd-rule
  (lhs rhs . rune)
  t)

(defun rewrite-rule-to-bdd-rule (lemma)
  (make bdd-rule
        :lhs  (access rewrite-rule lemma :lhs)
        :rhs  (access rewrite-rule lemma :rhs)
        :rune (access rewrite-rule lemma :rune)))

(defun bdd-rules-alist1
  (recp lemmas ens all-fns nondef-rules def-rules new-fns)

; This function returns lists of definitional and non-definitional bdd-rules
; corresponding to the lemmas of a given function symbol.  The arguments are as
; follows.

; recp:    True when the top-level function symbol for the lemmas is recursive
; lemmas:  The rewrite-rule structures that we want to convert to bdd-rules
; ens:     The current enabled structure
; all-fns: List of all function symbols already encountered in bdd rules built
; nondef-rules:  Bdd-rules accumulated so far not from definition rules
; def-rules:     Bdd-rules accumulated so far from definition rules
; new-fns: List of function symbols to be added to all-fns (an accumulator)

; At this point, we do not support backchaining:  that is, we assume that each
; rule has :hyps field of NIL.  We also do not allow free variables in the
; :rhs, and we require :lhs to be a function symbol call.  We also require a
; null loop-stopper (:heuristic-info for subclass 'backchain), rather than
; attempting to control looping during the bdd computation.  Perhaps some of
; these restrictions can be removed after some thought and additional
; implementation work.

; We require that the :rhs only contain function symbols that are known in the
; op-alist.  In order to enforce this requirement, we simply pass back two
; values:  a list of new function symbols to consider (i.e., ones not in
; all-fns that occur in :rhs fields) and the list of bdd-rules.

; As noted in a comment in bdd-rules-alist, the lists of lemmas returned by
; this function need to be reversed, because they have the oldest rules at the
; front.  That could easily be changed, though the natural way to do this would
; presumably render this function non-tail recursive.  At this point the issue
; seems sufficiently minor that we are satisfied to leave things this way.

  (cond
   ((endp lemmas) (mv new-fns nondef-rules def-rules))
   (t (let ((subclass (access rewrite-rule (car lemmas) :subclass)))
        (cond
         ((and (eq (access rewrite-rule (car lemmas) :equiv) 'equal)
               (enabled-numep (access rewrite-rule (car lemmas) :nume) ens)
               (case subclass
                     (definition
                       (and (null recp)
                            (null (access rewrite-rule (car lemmas) :hyps))
                            (subsetp-eq
                             (all-vars (access rewrite-rule (car lemmas)
                                               :rhs))
                             (all-vars (access rewrite-rule (car lemmas)
                                               :lhs)))))
                     (abbreviation
                      (subsetp-eq
                       (all-vars (access rewrite-rule (car lemmas) :rhs))
                       (all-vars (access rewrite-rule (car lemmas) :lhs))))
                     (backchain
                      (and (null (access rewrite-rule (car lemmas)
                                         :hyps))
                           (null (access rewrite-rule (car lemmas)
                                         :heuristic-info))
                           (subsetp-eq
                            (all-vars (access rewrite-rule (car lemmas)
                                              :rhs))
                            (all-vars (access rewrite-rule (car lemmas)
                                              :lhs)))))
                     (otherwise nil)))
          (bdd-rules-alist1 recp (cdr lemmas) ens all-fns
            (if (eq subclass 'definition)
                nondef-rules
              (cons (rewrite-rule-to-bdd-rule (car lemmas)) nondef-rules))
            (if (eq subclass 'definition)
                (cons (rewrite-rule-to-bdd-rule (car lemmas)) def-rules)
              def-rules)
            (union-eq (set-difference-eq
                       (all-fnnames (access rewrite-rule (car lemmas) :rhs))
                       all-fns)
                      new-fns)))
         (t (bdd-rules-alist1 recp (cdr lemmas) ens all-fns
              nondef-rules def-rules new-fns)))))))

(defun extra-rules-for-bdds (fn wrld)

; We include certain trivial rewrite rules regardless of whether there are
; explicit rewrite rules that correspond to them.

  (cond
   ((eq fn 'equal)
    (list (make rewrite-rule
                :nume nil :hyps nil :equiv 'equal

; Rockwell Addition:  I have totally stripped out all vestiges of the
; aborted attempt to implement :OUTSIDE-IN rewrite rules.  I won't comment
; on subsequent differences of this sort.

                :subclass 'backchain
                :heuristic-info nil
                :backchain-limit-lst *initial-default-backchain-limit*
                :rune *fake-rune-for-anonymous-enabled-rule*
                :lhs (fcons-term* 'equal *nil* 'x)
                :var-info t
                :rhs (fcons-term* 'if 'x *nil* *t*))
          (make rewrite-rule
                :nume nil :hyps nil :equiv 'equal
                :subclass 'backchain
                :heuristic-info nil
                :backchain-limit-lst *initial-default-backchain-limit*
                :rune *fake-rune-for-anonymous-enabled-rule*
                :lhs (fcons-term* 'equal 'x *nil*)
                :var-info t
                :rhs (fcons-term* 'if 'x *nil* *t*))))
   ((eq fn 'consp)

; (defthm consp-cons (consp (cons x y)))

    (list (make rewrite-rule
                :nume nil :hyps nil :equiv 'equal
                :subclass 'backchain
                :heuristic-info nil
                :backchain-limit-lst *initial-default-backchain-limit*
                :rune *fake-rune-for-anonymous-enabled-rule*
                :lhs (fcons-term* 'consp (fcons-term* 'cons 'x 'y))
                :var-info t
                :rhs *t*)))
   ((equivalence-relationp fn wrld)

; We do not need to include reflexivity when fn is 'equal, because it is
; hardwired into the definition of combine-op-csts.

    (list (make rewrite-rule
                :nume nil :hyps nil :equiv 'equal
                :subclass 'abbreviation
                :heuristic-info nil
                :backchain-limit-lst *initial-default-backchain-limit*
                :rune (equivalence-rune fn wrld)
                :lhs (fcons-term* fn 'x 'x)
                :var-info t
                :rhs *t*)))
   ((eq fn 'mv-nth)
    (list (make rewrite-rule
                :nume nil :hyps nil :equiv 'equal
                :subclass 'backchain
                :heuristic-info nil
                :backchain-limit-lst *initial-default-backchain-limit*
                :rune (fn-rune-nume 'mv-nth nil nil wrld)
                :lhs (fcons-term* 'mv-nth 'n (fcons-term* 'cons 'x 'y))
                :var-info t

; (if (zp n) x (mv-nth (- n 1) y))

                :rhs (fcons-term* 'if
                                  (fcons-term* 'zp 'n)
                                  'x
                                  (fcons-term* 'mv-nth
                                               (fcons-term* 'binary-+
                                                            'n
                                                            (kwote -1))
                                               'y)))))

   (t nil)))

(defun bdd-rules-alist (fns all-fns bdd-rules-alist ens wrld)

; Call this with a list fns of function symbols that does not include 'if, and
; all-fns the result of adding 'if to that list.  The parameter bdd-rules-alist
; is the accumulator, initially nil.

; WARNING:  Be sure to modify this function to account for hypotheses if we
; implement conditional rewriting with BDDs.

; Invariant:  fns is a subset of all-fns.  This is important for not just
; termination, but in fact to guarantee that the same function (car fns) is
; never processed twice by bdd-rules-alist1.

; NOTE:  Do we store entries when there are no rules, or not?  Not.  Suppose
; there are p elements of fns with a non-nil set of rules and q elements of fns
; with a nil set of rules.  Then the average number of CDRs required for lookup
; (assuming each function symbol is looked up the same number of times) is
; roughly (p+q)/2 if we store entries for nil sets of rules; and if we don't,
; it's:  [1/(p+q)]*(p*p/2 + q*p), which equals [p/2(p+q)]*(p + 2q).
; Now we can see that we're better off the second way, not storing nil entries:

; p+q >= [p/(p+q)]*(p + 2q) ?
; (p+q)^2 >= p^2 + 2pq ?
; q^2 >= 0 !
; Yes, in fact the inequality is strict if q > 0.

  (cond
   ((endp fns) (mv all-fns bdd-rules-alist))
   (t (mv-let (new-fns nondef-rules def-rules)
              (bdd-rules-alist1
               (recursivep (car fns) t wrld)
               (append (getpropc (car fns) 'lemmas nil wrld)
                       (extra-rules-for-bdds (car fns) wrld))
               ens
               (cons (car fns) all-fns)
               nil
               nil
               nil)
              (cond ((or def-rules nondef-rules)
                     (bdd-rules-alist
                       (append new-fns (cdr fns))
                       (append new-fns all-fns)
                       (cons (cons (car fns)

; The calls of reverse below ensure that rules will be tried in the appropriate
; order, i.e., most recent ones first.  See the comment in bdd-rules-alist1.

                                   (cons (reverse nondef-rules)
                                         (reverse def-rules)))
                             bdd-rules-alist)
                       ens
                       wrld))

; Otherwise do not store an entry for (car fns) in bdd-rules-alist, as argued
; in the comment above.

                    (t (bdd-rules-alist (cdr fns) all-fns bdd-rules-alist ens
                                        wrld)))))))

; We now adapt ACL2's one-way-unifier for terms to the realms of csts.

(defmacro one-way-unify1-cst-2 (mx-id p1 p2 cst1 cst2 alist op-ht)
  `(mv-let (mx-id ans alist1 op-ht)
           (one-way-unify1-cst ,mx-id ,p1 ,cst1 ,alist ,op-ht)
           (declare (type (signed-byte 30) mx-id))
           (cond
            (ans
             (mv-let (mx-id ans alist2 op-ht)
                     (one-way-unify1-cst mx-id ,p2 ,cst2 alist1 op-ht)
                     (declare (type (signed-byte 30) mx-id))
                     (cond
                      (ans (mvf mx-id t alist2 op-ht))
                      (t (mvf mx-id nil ,alist op-ht)))))
            (t (mvf mx-id nil ,alist op-ht)))))

(defmacro one-way-unify1-cst-3 (mx-id p1 p2 p3 cst1 cst2 cst3 alist op-ht)
  `(mv-let (mx-id ans alist2 op-ht)
           (one-way-unify1-cst-2 ,mx-id ,p1 ,p2 ,cst1 ,cst2 ,alist ,op-ht)
           (declare (type (signed-byte 30) mx-id))
           (cond
            (ans
             (mv-let (mx-id ans alist3 op-ht)
                     (one-way-unify1-cst mx-id ,p3 ,cst3 alist2 op-ht)
                     (declare (type (signed-byte 30) mx-id))
                     (cond
                      (ans (mvf mx-id t alist3 op-ht))
                      (t (mvf mx-id nil ,alist op-ht)))))
            (t (mvf mx-id nil ,alist op-ht)))))

(mutual-recursion

; The following functions are adapted from one-way-unify1 and the like.

(defun one-way-unify1-cst (mx-id pat cst alist op-ht)
  (declare (type (signed-byte 30) mx-id))
  (the-mv
   4
   (signed-byte 30)
   (cond ((variablep pat)
          (let ((pair (assoc-eq pat alist)))
            (cond (pair (cond ((cst= (cdr pair) cst)
                               (mvf mx-id t alist op-ht))
                              (t (mvf mx-id nil alist op-ht))))
                  (t (mvf mx-id t (cons (cons pat cst) alist) op-ht)))))
         ((not (leafp cst))
          (cond
           ((fquotep pat)
            (mvf mx-id nil alist op-ht))
           ((eq (ffn-symb pat) 'if)
            (one-way-unify1-cst-3 mx-id
                                  (fargn pat 1) (fargn pat 2) (fargn pat 3)
                                  (tst cst) (tbr cst) (fbr cst)
                                  alist op-ht))
           (t
            (mvf mx-id nil alist op-ht))))
         (t (let ((term (trm cst)))
              (cond
               ((fquotep pat)
                (cond ((equal pat term) (mvf mx-id t alist op-ht))
                      (t (mvf mx-id nil alist op-ht))))
               ((variablep term) (mvf mx-id nil alist op-ht))
               ((fquotep term) ;term is not a term, but fquotep is ok here
                (cond ((acl2-numberp (cadr term))
                       (let ((ffn-symb (ffn-symb pat)))
                         (case ffn-symb
                               (binary-+
                                (cond ((quotep (fargn pat 1))
                                       (mv-let (mx-id cst op-ht)
                                               (bdd-quotep
                                                (kwote (- (cadr term)
                                                          (fix (cadr (fargn pat
                                                                            1)))))
                                                op-ht mx-id)
                                               (declare (type (signed-byte 30)
                                                              mx-id))
                                               (one-way-unify1-cst
                                                mx-id (fargn pat 2)
                                                cst alist op-ht)))
                                      ((quotep (fargn pat 2))
                                       (mv-let (mx-id cst op-ht)
                                               (bdd-quotep
                                                (kwote (- (cadr term)
                                                          (fix (cadr (fargn pat
                                                                            2)))))
                                                op-ht mx-id)
                                               (declare (type (signed-byte 30)
                                                              mx-id))
                                               (one-way-unify1-cst
                                                mx-id (fargn pat 1)
                                                cst alist op-ht)))
                                      (t (mvf mx-id nil alist op-ht))))
                               (binary-*
                                (cond ((and (quotep (fargn pat 1))
                                            (integerp (cadr (fargn pat 1)))
                                            (> (abs (cadr (fargn pat 1))) 1))
                                       (mv-let (mx-id cst op-ht)
                                               (bdd-quotep
                                                (kwote (/ (cadr term)
                                                          (cadr (fargn pat 1))))
                                                op-ht mx-id)
                                               (declare (type (signed-byte 30)
                                                              mx-id))
                                               (one-way-unify1-cst
                                                mx-id (fargn pat 2)
                                                cst alist op-ht)))
                                      ((and (quotep (fargn pat 2))
                                            (integerp (cadr (fargn pat 2)))
                                            (> (abs (cadr (fargn pat 2))) 1))
                                       (mv-let (mx-id cst op-ht)
                                               (bdd-quotep
                                                (kwote (/ (cadr term)
                                                          (cadr (fargn pat 2))))
                                                op-ht mx-id)
                                               (declare (type (signed-byte 30)
                                                              mx-id))
                                               (one-way-unify1-cst
                                                mx-id (fargn pat 1)
                                                cst alist op-ht)))
                                      (t (mvf mx-id nil alist op-ht))))
                               (unary-- (cond ((>= (+ (realpart (cadr term))
                                                      (imagpart (cadr term)))
                                                   0)
                                               (mvf mx-id nil alist op-ht))
                                              (t (mv-let (mx-id cst op-ht)
                                                         (bdd-quotep
                                                          (kwote (- (cadr term)))
                                                          op-ht mx-id)
                                                         (declare (type
                                                                   (signed-byte
                                                                    30)
                                                                   mx-id))
                                                         (one-way-unify1-cst
                                                          mx-id (fargn pat 1)
                                                          cst alist
                                                          op-ht)))))
                               (unary-/ (cond ((or (>= (* (cadr term)
                                                          (conjugate (cadr term)))
                                                       1)
                                                   (eql 0 (cadr term)))
                                               (mvf mx-id nil alist op-ht))
                                              (t (mv-let (mx-id cst op-ht)
                                                         (bdd-quotep
                                                          (kwote (/ (cadr term)))
                                                          op-ht mx-id)
                                                         (declare (type
                                                                   (signed-byte
                                                                    30)
                                                                   mx-id))
                                                         (one-way-unify1-cst
                                                          mx-id (fargn pat 1)
                                                          cst alist op-ht)))))
                               (otherwise (mvf mx-id nil alist op-ht)))))

; We try to avoid some complications by avoiding intern-in-package-of-symbol
; and coerce for now.  We are not aware of any reason why they should present
; undue difficulties, however.

                      ((consp (cadr term))
                       (cond ((eq (ffn-symb pat) 'cons)

; We have to be careful with alist below so we are a no change loser.

                              (mv-let
                               (mx-id cst1 op-ht)
                               (bdd-quotep
                                (kwote (car (cadr term)))
                                op-ht mx-id)
                               (declare (type (signed-byte 30) mx-id))
                               (mv-let
                                (mx-id ans alist1 op-ht)
                                (one-way-unify1-cst
                                 mx-id (fargn pat 1) cst1 alist op-ht)
                                (declare (type (signed-byte 30) mx-id))
                                (cond
                                 (ans
                                  (mv-let
                                   (mx-id cst2 op-ht)
                                   (bdd-quotep
                                    (kwote (cdr (cadr term)))
                                    op-ht mx-id)
                                   (declare (type (signed-byte 30) mx-id))
                                   (mv-let (mx-id ans alist2 op-ht)
                                           (one-way-unify1-cst
                                            mx-id (fargn pat 2) cst2 alist1
                                            op-ht)
                                           (declare (type (signed-byte 30)
                                                          mx-id))
                                           (cond (ans (mvf mx-id t alist2
                                                           op-ht))
                                                 (t (mvf mx-id nil alist
                                                         op-ht))))))
                                 (t (mvf mx-id nil alist op-ht))))))
                             (t (mvf mx-id nil alist op-ht))))
                      (t (mvf mx-id nil alist op-ht))))
               ((eq (ffn-symb pat) (ffn-symb term))

; Note:  We do not allow lambda expressions at this point.  If that changes,
; then we should consider that case too.

                (cond ((eq (ffn-symb pat) 'equal)
                       (one-way-unify1-cst-equal mx-id
                                                 (fargn pat 1) (fargn pat 2)
                                                 (fargn term 1) (fargn term 2)
                                                 alist op-ht))
                      (t (mv-let (mx-id ans alist1 op-ht)
                                 (one-way-unify1-cst-lst mx-id
                                                         (fargs pat)
                                                         (fargs term)
                                                         alist op-ht)
                                 (declare (type (signed-byte 30) mx-id))
                                 (cond (ans (mvf mx-id t alist1 op-ht))
                                       (t (mvf mx-id nil alist op-ht)))))))
               (t (mvf mx-id nil alist op-ht))))))))

(defun one-way-unify1-cst-lst (mx-id pl cstl alist op-ht)

; This function is NOT a No Change Loser.

  (declare (type (signed-byte 30) mx-id))
  (the-mv
   4
   (signed-byte 30)
   (cond ((null pl) (mvf mx-id t alist op-ht))
         (t (mv-let (mx-id ans alist op-ht)
                    (one-way-unify1-cst mx-id (car pl) (car cstl) alist op-ht)
                    (declare (type (signed-byte 30) mx-id))
                    (cond
                     (ans
                      (one-way-unify1-cst-lst mx-id (cdr pl) (cdr cstl) alist
                                              op-ht))
                     (t (mvf mx-id nil alist op-ht))))))))

(defun one-way-unify1-cst-equal (mx-id pat1 pat2 cst1 cst2 alist op-ht)
  (declare (type (signed-byte 30) mx-id))
  (the-mv
   4
   (signed-byte 30)
   (mv-let (mx-id ans alist op-ht)
           (one-way-unify1-cst-2 mx-id pat1 pat2 cst1 cst2 alist op-ht)
           (declare (type (signed-byte 30) mx-id))
           (cond
            (ans (mvf mx-id t alist op-ht))
            (t (one-way-unify1-cst-2 mx-id pat2 pat1 cst1 cst2 alist
                                     op-ht))))))
)

(defun some-one-way-unify-cst-lst (cst-lst rules op-ht mx-id ttree)
  (declare (type (signed-byte 30) mx-id))
  (the-mv
   6
   (signed-byte 30)
   (cond
    ((endp rules)
     (mvf mx-id nil nil nil op-ht ttree))
    (t (mv-let (mx-id ans alist op-ht)
               (one-way-unify1-cst-lst
                mx-id (fargs (access bdd-rule (car rules) :lhs))
                cst-lst nil op-ht)
               (declare (type (signed-byte 30) mx-id))
               (cond
                (ans (mvf mx-id t
                          (access bdd-rule (car rules) :rhs)
                          alist op-ht
                         (push-lemma (access bdd-rule (car rules) :rune)
                                     ttree)))
                (t (some-one-way-unify-cst-lst cst-lst (cdr rules)
                                               op-ht mx-id ttree))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; VI. SOME INTERFACE UTILITIES
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We will ignore declaration opportunities in this section, especially for
; declaring mx-id to be a fixnum, because efficiency is a minor issue here.

(defun leaf-cst-list (lst bool-vars acc mx-id)

; Here lst is a list of variables from the input term.  Returns a list of leaf
; csts for those variables, i.e., elements of the form (unique-id variable
; bool), where if bool is t then variable is known to be Boolean.

  (cond
   ((endp lst) (mv mx-id acc))
   (t (mv-let (mx-id acc)
              (cond ((assoc-eq (car lst) acc)
                     (mv mx-id acc))
                    (t (let ((new-mx-id (1+mx-id mx-id)))
                         (mv new-mx-id
                             (cons (make-leaf-cst
                                    new-mx-id
                                    (car lst)
                                    (member-eq (car lst) bool-vars))
                                   acc)))))
              (leaf-cst-list (cdr lst) bool-vars acc mx-id)))))

(mutual-recursion

(defun decode-cst (cst cst-array)

; This takes a cst and returns a term and an updated cst-array, whose nth entry
; is the decoding of the cst with unique id n.

  (let ((term (aref1 'cst-array cst-array (unique-id cst))))
    (cond
     (term (mv term cst-array))
     ((leafp cst)
      (cond
       ((or (variablep (trm cst))
            (fquotep (trm cst)))
        (mv (trm cst) cst-array))
       (t (mv-let (args cst-array)
                  (decode-cst-lst (fargs (trm cst)) cst-array)
                  (let ((x (cons-term (ffn-symb (trm cst))
                                      args)))
                    (mv x
                        (aset1-trusted 'cst-array
                                       cst-array
                                       (unique-id cst)
                                       x)))))))
     (t (mv-let
         (tst cst-array)
         (decode-cst (tst cst) cst-array)
         (mv-let
          (tbr cst-array)
          (decode-cst (tbr cst) cst-array)
          (mv-let
           (fbr cst-array)
           (decode-cst (fbr cst) cst-array)
           (let ((x (mcons-term* 'if tst tbr fbr)))
             (mv x
                 (aset1-trusted 'cst-array
                                cst-array
                                (unique-id cst)
                                x))))))))))

(defun decode-cst-lst (cst-lst cst-array)
  (cond
   ((endp cst-lst)
    (mv nil cst-array))
   (t (mv-let (first cst-array)
              (decode-cst (car cst-lst) cst-array)
              (mv-let (rest cst-array)
                      (decode-cst-lst (cdr cst-lst) cst-array)
                      (mv (cons first rest)
                          cst-array))))))
)

(defun decode-cst-alist1 (alist cst-array)
  (cond
   ((endp alist) (mv nil cst-array))
   (t (mv-let (term cst-array)
              (decode-cst (cdar alist) cst-array)
              (mv-let (rest cst-array)
                      (decode-cst-alist1 (cdr alist) cst-array)
                      (mv (cons (list (caar alist)
                                      term)
                                rest)
                          cst-array))))))

(defun decode-cst-alist (cst-alist cst-array)
  (mv-let (alist cst-array)
          (decode-cst-alist1 cst-alist cst-array)
          (declare (ignore cst-array))
          alist))

(defun leaf-cst-list-array (mx-id)
  (let ((dim (1+ mx-id)))
    (compress1 'cst-array
               `((:header :dimensions (,dim)
                          :maximum-length ,(+ 10 dim)
                          :default nil)))))

(defconst *some-non-nil-value* "Some non-nil value")

(defun falsifying-assignment1 (cst acc cst-array)

; Returns a list of doublets (var bool) that provide an environment for
; falsifying the given cst.  Also returns a new cst-array; we have to do that
; so that we always pass in the "current" cst-array, in order to avoid slow
; array access.

  (cond
   ((cst-nilp cst)
    (mv acc cst-array))
   ((quotep (trm cst))
    (mv (er hard 'falsifying-assignment1
            "Tried to falsify ~x0!"
            (trm cst))
        cst-array))
   ((leafp cst)
    (mv-let (term cst-array)
            (decode-cst cst cst-array)
            (mv (cons (list term nil) acc)
                cst-array)))
   ((cst-nonnilp (tbr cst))
    (mv-let (term cst-array)
            (decode-cst (tst cst) cst-array)
            (falsifying-assignment1 (fbr cst)
                                    (cons (list term nil)
                                          acc)
                                    cst-array)))
   (t
    (mv-let (term cst-array)
            (decode-cst (tst cst) cst-array)
            (falsifying-assignment1 (tbr cst)
                                    (cons (list term (if (cst-boolp (tst cst))
                                                         t
                                                       *some-non-nil-value*))
                                          acc)
                                    cst-array)))))

(defun falsifying-assignment (cst mx-id)
  (mv-let (asst cst-array)
          (falsifying-assignment1 cst nil (leaf-cst-list-array mx-id))
          (declare (ignore cst-array))
          (reverse asst)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; VII. MAIN ALGORITHM ;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-if (mx-id n op args x y z op-ht if-ht bdd-constructors)

; This function returns either

; (mvf mx-id cst op-ht if-ht)

; or (culling this from an "erroneous" return of make-if-cst below)

; (mvf mx-id fmt-string fmt-alist bad-cst)

; Intuitively, this function makes a cst representing (IF x y z).  But
; we know that this is the answer to the merge op(args) and we
; know that n is the hash index of <op,arg1,...>.  We know
; <op,arg1,...> is not in the op-ht.  We first look in the if-ht to
; see if (IF x y z) is there.  If so, we return it.  If not, we build
; an appropriate one, assigning the next unique id, which is (1+
; mx-id), and add it to the if-ht.  In any case, before returning, we
; store the returned cst as the answer for op(arg1,...) in op-ht.  We
; thus have to return four results: the new mx-id, the cst, and the
; two hash arrays.

  (declare (type (signed-byte 30) n mx-id))
  (the-mv
   4
   (signed-byte 30)
   (cond ((cst= y z) (mvf mx-id
                          y

; The following aset1 was added after Moore's first presentation of this
; work.  Its absence was discovered during a code-walk with Jim
; Bitner.  The times improved slightly on most examples, except mul08
; where we lost a few more seconds.  The times shown in
; ~moore/text/pc-hacking.mss -- the most recent version of a talk on
; this work -- have been updated to show the performance of this
; version of the code.

                          (aset1-trusted 'op-ht op-ht n
                                         (cons (list* y op args)
                                               (aref1 'op-ht op-ht n)))
                          if-ht))
         (t (let ((m (if-hash-index x y z)))
              (declare (type (signed-byte 30) m))
              (let* ((bucket (aref1 'if-ht if-ht m))
                     (old-if (if-search-bucket x y z bucket)))
                (cond (old-if (mvf mx-id
                                   old-if
                                   (aset1-trusted 'op-ht op-ht n
                                                  (cons (list* old-if op args)
                                                        (aref1 'op-ht op-ht
                                                               n)))
                                   if-ht))
                      ((and (cst-tp y)
                            (cst-nilp z)
                            (cst-boolp x))
                       (mvf mx-id
                            x
                            (aset1-trusted 'op-ht op-ht n
                                           (cons (list* x op args)
                                                 (aref1 'op-ht op-ht n)))
                            if-ht))
                      (t (let ((mx-id (1+mx-id mx-id)))
                           (declare (type (signed-byte 30) mx-id))
                           (mv-let
                            (erp new-if)
                            (make-if-cst mx-id x y z bdd-constructors)
                            (cond
                             (erp (mvf mx-id
                                       (car erp) ;fmt-string
                                       (cdr erp) ;fmt-alist
                                       new-if ;bad cst
                                       ))
                             (t
                              (mvf mx-id
                                   new-if
                                   (aset1-trusted 'op-ht op-ht n
                                                  (cons (list* new-if op args)
                                                        (aref1 'op-ht op-ht
                                                               n)))
                                   (aset1-trusted 'if-ht if-ht m
                                                  (cons new-if
                                                        bucket)))))))))))))))

(defun make-if-no-memo (mx-id x y z op-ht if-ht bdd-constructors)

; Same as make-if, except that we do not change op-ht, and we assume that y and
; z are already known to be distinct.

  (declare (type (signed-byte 30) mx-id))
  (the-mv
   4
   (signed-byte 30)
   (let ((m (if-hash-index x y z)))
     (declare (type (signed-byte 30) m))
     (let* ((bucket (aref1 'if-ht if-ht m))
            (old-if (if-search-bucket x y z bucket)))
       (cond (old-if (mvf mx-id old-if op-ht if-ht))
             ((and (cst-tp y)
                   (cst-nilp z)
                   (cst-boolp x))
              (mvf mx-id x op-ht if-ht))
             (t (let ((mx-id (1+mx-id mx-id)))
                  (declare (type (signed-byte 30) mx-id))
                  (mv-let
                   (erp new-if)
                   (make-if-cst mx-id x y z bdd-constructors)
                   (cond
                    (erp (mvf mx-id
                              (car erp) ;fmt-string
                              (cdr erp) ;fmt-alist
                              new-if ;bad cst
                              ))
                    (t
                     (mvf mx-id new-if op-ht
                          (aset1-trusted 'if-ht if-ht m
                                         (cons new-if bucket)))))))))))))

(defmacro split-var (cst)

; The variable to split on from cst.  If cst is a leaf, then we only split on
; it if it is a cst-varp (i.e., not the representation of T or NIL) and is
; known to be Boolean.

  `(if (leafp ,cst)
       (if (and (cst-varp ,cst)
                (cst-boolp ,cst))
           ,cst
         nil)
     (tst ,cst)))

(defun min-var (acc args)

; Args is a list of csts.  We return nil if there is no variable to split on.
; Otherwise, we return the leaf cst with the smallest unique-id.  Call this
; with acc = nil.

  (declare (xargs :measure (acl2-count args)))
  (if (endp args)
      acc
    (let ((var (split-var (car args))))
      (if (null var)
          (min-var acc (cdr args))
        (min-var (cond
                  ((null acc)
                   var)
                  ((< (unique-id var) (unique-id acc))
                   var)
                  (t acc))
                 (cdr args))))))

(defun combine-op-csts1 (var-id args)

; Args is a list of csts, and var-id is the unique-id of a term that is not
; necessarily Boolean-valued.  We return (mv true-branch-args
; false-branch-args), where under the assumption that var-id is the unique id
; of a term that is not (semantically) nil, args represents the same list of
; terms as true-branch-args; and under the assumption that var-id is the unique
; id of a term that (semantically) equals nil, args represents the same list of
; terms as false-branch-args.

  (declare (type (signed-byte 30) var-id))
  (if (endp args)
      (mv nil nil)
    (mv-let (x y)
            (combine-op-csts1 var-id (cdr args))
            (cond
             ((leafp (car args))
              (if (and (= (the-fixnum var-id) (unique-id (car args)))

; Even though we are splitting on var-id, we need to know that it is the unique
; id of a boolean variable in order to simplify as shown below.  Note that
; var-id need only be the unique-id of a Boolean cst when split-var returns it
; by virtue of its being a leaf; it could be non-Boolean if split-var
; encounters it as a test.

                       (cst-boolp (car args)))
                  (mv (cons *cst-t* x) (cons *cst-nil* y))
                (mv (cons (car args) x) (cons (car args) y))))
             (t
              (if (= (the-fixnum var-id) (unique-id (tst (car args))))
                  (mv (cons (tbr (car args)) x) (cons (fbr (car args)) y))
                (mv (cons (car args) x) (cons (car args) y))))))))

(defun bool-flg (args mask)

; Checks that for each "bit" set in mask, the corresponding arg in args is
; known to be Boolean.  In the case that mask is (typically) from a type
; prescription, this allows us to conclude, assuming that the given function
; symbol's base type is Boolean, then the application of that function to args
; is Boolean.

; If this function returns a non-nil value, then that value is a type
; prescription rune.

  (cond
   ((endp args)

; Then mask is a type prescription rune.

    mask)
   ((car mask)
    (and (cst-boolp (car args))
         (bool-flg (cdr args) (cdr mask))))
   (t (bool-flg (cdr args) (cdr mask)))))

(defun some-bdd-constructorp (args bdd-constructors)
  (cond
   ((endp args) nil)
   (t (or (and (leafp (car args))
               (bdd-constructor-trm-p (trm (car args)) bdd-constructors))
          (some-bdd-constructorp (cdr args) bdd-constructors)))))

(defun combine-op-csts-simple
  (hash-index op mask args op-ht if-ht mx-id bdd-constructors ttree)

; Make a new leaf-cst for (op . args).  Note:  this function returns an "error"
; in the sense described in the bdd nest if the call attempts to build a
; non-bdd-constructor node when some argument is a bdd-constructor.  Pass in
; bdd-constructors = nil if no such attempt is possible; otherwise, we know
; that op is not a member of bdd-constructors.

  (declare (type (signed-byte 30) hash-index mx-id))
  (the-mv
   5
   (signed-byte 30)
   (let ((new-mx-id (1+mx-id mx-id))
         (rune (and mask

; If mask is non-nil, we guarantee that op corresponds to a function whose type
; is Boolean modulo that mask (for its type prescription).

                    (bool-flg args mask))))
     (declare (type (signed-byte 30) new-mx-id))
     (let ((new-cst (make-leaf-cst
                     new-mx-id
                     (cons op args)
                     rune)))
       (cond
        ((and bdd-constructors

; We presumably know that (not (member-eq op bdd-constructors)).

              (some-bdd-constructorp args bdd-constructors))
         (bdd-error
          new-mx-id
          "Attempted to create ~x0 node during BDD processing with an argument ~
           that is a call of ~#1~[a bdd-constructor~/CONS~], which would ~
           produce a non-BDD term (as defined in :DOC bdd-algorithm).  See ~
           :DOC show-bdd."
          (list (cons #\0 op)
                (cons #\1 (if (equal bdd-constructors '(cons))
                              1
                            0)))
          new-cst
          ttree))
        (t
         (mvf new-mx-id
              new-cst
              (aset1-trusted 'op-ht op-ht hash-index
                             (cons (list* new-cst op args)
                                   (aref1 'op-ht op-ht hash-index)))
              if-ht
              (if rune (push-lemma rune ttree) ttree))))))))

(defmacro bdd-mv-let (vars form body)

; The idea here is that we want to allow functions in the bdd nest to return
; multiple values of the sort returned by the macro bdd-error.
; Combine-if-csts+ gets special treatment.

; This macro should only be used when the first var has a fixnum value.  We go
; even further by requiring that the first var be mx-id.  Whenever we write

; (bdd-mv-let vars form body)

; we assume that body returns the same number of values as does form.

; Keep this in sync with bdd-error, as indicated in a comment below.  The code
; below is the only place, as of this writing, where we update the
; bdd-call-stack.

  (declare (xargs :guard
                  (and (true-listp vars)
                       (eq (car vars) 'mx-id)
                       (< 2 (length vars))
                       (consp form)
                       (true-listp form)
                       (member-eq
                        (car form)
                        '(combine-if-csts+
                          combine-op-csts combine-op-csts+
                          combine-op-csts-guts combine-op-csts-comm
                          bdd bdd-alist bdd-list)))))
  `(mv-let ,vars
           ,form
           (declare (type (signed-byte 30) mx-id))
           (if (stringp ,(cadr vars))
               ,(cond
                 ((eq (car form) 'bdd)

; Vars is of the form returned by bdd-error:
; (mv mx-id fmt-string (cons fmt-alist bad-cst) call-stack ttree).
; We want to push the current term onto the call-stack.

                 (list 'mvf
                       (car vars)
                       (cadr vars)
                       (caddr vars)
                       (list 'cons

; Keep this in sync with the definition of bdd.  Here, (cadr form) is really
; the first argument of bdd, which should be a term, and (caddr form) is the
; second argument, which should be an alist.  The cons we generate here is the
; new value of the call-stack.

                             (list 'cons (cadr form) (caddr form))
                             (cadddr vars))
                       (cadddr (cdr vars))))
                 (t

; Then vars represents an "error", and we want to return an error of the same
; sort.  This sort will be different for combine-if-csts+ than for the other
; allowable functions (from the guard expression above), but no matter.

                  (cons 'mvf vars)))
             ,body)))

(defmacro combine-if-csts+ (cst1 cst2 cst3 op-ht if-ht mx-id bdd-constructors)
  `(cond
    ((cst-nilp ,cst1)
     (mvf ,mx-id ,cst3 ,op-ht ,if-ht))
    ((cst-nonnilp ,cst1)
     (mvf ,mx-id ,cst2 ,op-ht ,if-ht))
    (t (combine-if-csts ,cst1 ,cst2 ,cst3 ,op-ht ,if-ht ,mx-id
                        ,bdd-constructors))))

(defun combine-if-csts1 (var-id args)

; This function is identical to combine-op-csts1, except that the op is
; assumed to be IF.

  (declare (type (signed-byte 30) var-id))
  (mv-let (x y)
          (combine-op-csts1 var-id (cdr args))
          (cond
           ((leafp (car args))
            (if (= (the-fixnum var-id) (unique-id (car args)))
                (mv (cons *cst-t* x)
                    (cons *cst-nil* y))
              (mv (cons (car args) x)
                  (cons (car args) y))))
           (t
            (if (= (the-fixnum var-id) (unique-id (tst (car args))))
                (mv (cons (tbr (car args)) x) (cons (fbr (car args)) y))
              (mv (cons (car args) x) (cons (car args) y)))))))

(defun combine-if-csts
  (test-cst true-cst false-cst op-ht if-ht mx-id bdd-constructors)

; Similarly to the bdd nest, this function returns either

; (mvf mx-id cst op-ht if-ht)

; or

; (mvf mx-id fmt-string (cons fmt-alist bad-cst) nil).

; We assume here that test-cst is not the cst of a quotep, and that the input
; csts are really all csts (not error strings).

  (declare (type (signed-byte 30) mx-id))
  (the-mv
   4
   (signed-byte 30)
   (cond
    ((cst= true-cst false-cst)
     (mvf mx-id true-cst op-ht if-ht))
    ((cst= test-cst false-cst)
     (combine-if-csts test-cst true-cst *cst-nil* op-ht if-ht mx-id
                      bdd-constructors))
    ((and (cst= test-cst true-cst)
          (cst-boolp true-cst))
     (combine-if-csts test-cst *cst-t* false-cst op-ht if-ht mx-id
                      bdd-constructors))
    ((and (cst-nilp false-cst)
          (if (cst-tp true-cst)
              (cst-boolp test-cst)
            (cst= test-cst true-cst)))
     (mvf mx-id test-cst op-ht if-ht))
    (t (let ((true-var (split-var true-cst))
             (false-var (split-var false-cst)))
         (cond
          ((and (leafp test-cst)
                (or (null true-var)
                    (< (unique-id test-cst) (unique-id true-var)))
                (or (null false-var)
                    (< (unique-id test-cst) (unique-id false-var))))

; Then the test is the appropriate variable to split on for building a bdd, so
; we proceed to build a bdd.  Some test data suggests that it is more efficient
; to avoid op-ht memoization in this case; it makes sense anyhow that if-ht
; memoization would suffice here.  After all, very little work would be done
; inbetween looking in the op-ht and looking in the if-ht.  So, we neither
; consult nor use the op-ht when the test-cst is already in the right position.

           (make-if-no-memo mx-id test-cst true-cst false-cst op-ht if-ht
                            bdd-constructors))
          (t
           (mv-let
            (hash-index ans)
            (chk-memo-if test-cst true-cst false-cst op-ht)
            (declare (type (signed-byte 30) hash-index))
            (cond
             (ans (mvf mx-id ans op-ht if-ht))
             (t (let* ((args (list test-cst true-cst false-cst))
                       (min-var (min-var nil args)))

; Note that min-var is non-nil; otherwise split-var returns nil for each arg,
; and the previous case would apply.

                  (mv-let
                   (args1 args2)
                   (combine-if-csts1 (unique-id min-var) args)
                   (bdd-mv-let
                    (mx-id cst1 op-ht if-ht)
                    (combine-if-csts+ (car args1) (cadr args1) (caddr args1)
                                      op-ht if-ht mx-id bdd-constructors)
                    (bdd-mv-let
                     (mx-id cst2 op-ht if-ht)
                     (combine-if-csts+ (car args2) (cadr args2) (caddr args2)
                                       op-ht if-ht mx-id bdd-constructors)
                     (make-if mx-id hash-index 'if args min-var cst1 cst2
                              op-ht if-ht bdd-constructors)))))))))))))))

(defun cst-list-to-evg-list (cst-lst)
  (cond
   ((endp cst-lst) nil)
   (t (cons (cadr (trm (car cst-lst)))
            (cst-list-to-evg-list (cdr cst-lst))))))

(defun cst-quote-listp (cst-lst)
  (cond
   ((endp cst-lst) t)
   ((and (leafp (car cst-lst))
         (quotep (trm (car cst-lst))))
    (cst-quote-listp (cdr cst-lst)))
   (t nil)))

(defrec bddspv

; Bddspv stands for "BDD special variables", in analogy to pspv.  We simply
; prefer not to pass around such long argument lists.  In addition, we expect
; the code to be easier to modify this way; for example, the addition of
; bdd-constructors as a field in the bddspv avoids the need to massive
; modification of function calls.

  (op-alist bdd-rules-alist . bdd-constructors)
  t)

(defun bdd-ev-fncall
  (mx-id hash-index op mask args op-ht if-ht bdd-constructors rune ttree state)
  (declare (type (signed-byte 30) hash-index mx-id))
  (the-mv
   5
   (signed-byte 30)
   (mv-let (erp val latches)
           (ev-fncall op (cst-list-to-evg-list args)
                      nil ; irrelevant arg-exprs (as latches is nil)
                      state nil nil nil)
           (declare (ignore latches))
           (cond
            (erp

; How can this case happen?  Ev-fncall can only "return an error" if there is a
; guard violation (not possible in this context) or a call of a constrained
; function (introduced locally in an encapsulate or introduced by defchoose).
; Although we have guaranteed that op is not constrained (see the code for
; op-alist), still the body of op could contain calls of constrained functions.

             (combine-op-csts-simple
              hash-index op mask args op-ht if-ht mx-id
              (and (not (member-eq op bdd-constructors))

; See the comment in combine-op-csts-simple.  The idea is that if op is in
; bdd-constructors, then we may suppress a certain check.

                   bdd-constructors)
              ttree))
            (t (bdd-quotep+ (list 'quote val) op-ht if-ht mx-id
                            (push-lemma rune ttree)))))))

(defmacro combine-op-csts+ (mx-id comm-p enabled-exec-p op-code op mask args op-ht
                                  if-ht op-bdd-rules ttree bddspv)

; In combine-op-csts-guts we want to call either combine-op-csts or
; combine-op-csts-comm, depending on the comm-p argument.  It would be slightly
; more efficient if we simply had two versions of combine-op-csts-guts:  one
; that calls combine-op-csts and one that calls combine-op-csts-comm.  But the
; savings seems quite trivial, so we devise this macro to call the appropriate
; function.

  `(if ,comm-p
       (combine-op-csts-comm ,mx-id ,comm-p ,enabled-exec-p ,op-code ,op ,mask
                             (car ,args) (cadr ,args) ,args ,op-ht ,if-ht
                             ,op-bdd-rules ,ttree ,bddspv state)
     (combine-op-csts ,mx-id ,enabled-exec-p ,op-code ,op ,mask
                      ,args ,op-ht ,if-ht ,op-bdd-rules
                      ,ttree ,bddspv state)))

(defun make-if-for-op
  (mx-id hash-index op args test-cst true-cst false-cst
         op-ht if-ht bdd-constructors)
  (declare (type (signed-byte 30) hash-index mx-id))
  (the-mv
   4
   (signed-byte 30)
   (cond
    ((cst= true-cst false-cst)

; Keep this case in sync with make-if.

     (mvf mx-id true-cst
          (aset1-trusted 'op-ht op-ht hash-index
                         (cons (list* true-cst op args)
                               (aref1 'op-ht op-ht hash-index)))
          if-ht))
    ((let ((true-split-var (split-var true-cst))
           (false-split-var (split-var false-cst))
           (test-id (unique-id test-cst)))
       (declare (type (signed-byte 30) test-id))
       (and (or (null true-split-var)
                (< test-id (unique-id true-split-var)))
            (or (null false-split-var)
                (< test-id (unique-id false-split-var)))))
     (make-if
      mx-id hash-index op args test-cst true-cst false-cst
      op-ht if-ht bdd-constructors))
    (t
     (bdd-mv-let
      (mx-id cst op-ht if-ht)
      (combine-if-csts+
       test-cst true-cst false-cst op-ht if-ht mx-id bdd-constructors)
      (mvf mx-id
           cst
           (aset1-trusted 'op-ht op-ht hash-index
                          (cons (list* cst op args)
                                (aref1 'op-ht op-ht hash-index)))
           if-ht))))))

(mutual-recursion

; All functions in this nest return either

; (mvf mx-id cst op-ht if-ht ttree)

; or (as returned by bdd-error)

; (mvf mx-id fmt-string (fmt-alist . bad-cst) call-stack ttree)

(defun combine-op-csts (mx-id enabled-exec-p op-code op mask args op-ht
                              if-ht op-bdd-rules ttree bddspv state)

; Returns a cst for (op . args).  For special treatment of the case where the
; operator is commutative, in order to avoid some consing, use
; combine-op-csts-comm.

  (declare (type (signed-byte 30) op-code mx-id))
  (the-mv
   5
   (signed-byte 30)
   (mv-let
    (hash-index ans)
    (chk-memo op-code op args op-ht)
    (declare (type (signed-byte 30) hash-index))
    (cond
     (ans (mvf mx-id ans op-ht if-ht ttree))
     ((and enabled-exec-p
           (cst-quote-listp args))
      (bdd-ev-fncall mx-id hash-index op mask args op-ht if-ht
                     (access bddspv bddspv :bdd-constructors)
                     enabled-exec-p ttree state))
     ((and (eq op 'booleanp)
           (cst-boolp (car args)))
      (mvf mx-id *cst-t* op-ht if-ht
           (push-lemma (fn-rune-nume 'booleanp nil nil (w state)) ttree)))
     (t (combine-op-csts-guts
         mx-id nil hash-index enabled-exec-p op-code op mask args op-ht
         if-ht op-bdd-rules ttree bddspv state))))))

(defun combine-op-csts-comm (mx-id comm-p enabled-exec-p op-code op mask arg1
                                   arg2 args op-ht if-ht op-bdd-rules ttree
                                   bddspv state)

; Returns a cst for (op arg1 arg2) where op is commutative and comm-p is a rune
; justifying commutativity of op.

; When args is non-nil, it is (list arg1 arg2).  The idea is to avoid making a
; cons when possible.

  (declare (type (signed-byte 30) op-code mx-id))
  (the-mv
   5
   (signed-byte 30)
   (cond
    ((and (eq op 'equal)
          (cst= arg1 arg2))

; Alternatively, we could wait until after the chk-memo-2 test below.  But in
; that case, we should make the appropriate entry in the op-ht so that we don't
; waste our time the next time the same call of 'equal arises, looking for an
; entry in op-ht that has not been (and will never be) put there.  But we
; prefer to avoid the op-ht entirely in this trivial case, and also avoid the
; computations having to do with commutativity.

; Actually, a few experiments suggest that we should have left this branch
; where it was, jut before the next branch involving 'equal.  But that makes no
; sense!  Since the performance degradation seemed to be at most a couple of
; percent, we'll leave it this way for now.

     (mvf mx-id *cst-t* op-ht if-ht
          (push-lemma (fn-rune-nume 'equal nil nil (w state)) ttree)))
    (t
     (mv-let
      (arg1 arg2 args ttree)
      (cond ((and (quotep arg2)
                  (not (quotep arg1)))
             (mv arg2 arg1 nil (push-lemma comm-p ttree)))
            ((< (unique-id arg2)
                (unique-id arg1))
             (mv arg2 arg1 nil (push-lemma comm-p ttree)))
            (t (mv arg1 arg2 args ttree)))
      (mv-let
       (hash-index ans)
       (chk-memo-2 op-code op arg1 arg2 op-ht)
       (declare (type (signed-byte 30) hash-index))
       (cond
        (ans (mvf mx-id ans op-ht if-ht ttree))
        ((and (eq op 'equal)
              (cst-tp arg1)
              (cst-boolp arg2))

; Note:  We are tempted to worry about the term (equal 'nil 't), which would
; not get caught by this case and hence, we fret, could fall through to a call
; of bdd-ev-fncall (which may be rather slower than we wish).  However, since
; the unique id is 1 for T and 2 for NIL, and we have already commuted the args
; if necessary, then there is nothing to worry about.

         (mvf mx-id arg2 op-ht if-ht
              (push-lemma (fn-rune-nume 'equal nil nil (w state)) ttree)))
        ((and enabled-exec-p
              (quotep (trm arg1))
              (quotep (trm arg2)))
         (bdd-ev-fncall mx-id hash-index op mask (or args (list arg1 arg2)) op-ht
                        if-ht
                        (access bddspv bddspv :bdd-constructors)
                        enabled-exec-p ttree state))
        (t (combine-op-csts-guts
            mx-id comm-p hash-index enabled-exec-p op-code op mask

; It is tempting to avoid consing up the following list, just in case it will
; be torn apart again.  However, this list is the one that is ultimately
; memoized, so we need it anyhow.

            (or args (list arg1 arg2))
            op-ht if-ht op-bdd-rules ttree bddspv state)))))))))

(defun combine-op-csts-guts
  (mx-id comm-p hash-index enabled-exec-p op-code op mask args op-ht if-ht
         op-bdd-rules ttree bddspv state)

; Note that op-bdd-rules is a pair of the form (bdd-lemmas . bdd-defs).  These
; are all the bdd rules that rewrite calls of the function symbol op.

  (declare (type (signed-byte 30) op-code mx-id hash-index))
  (the-mv
   5
   (signed-byte 30)
   (mv-let
    (mx-id ans rhs alist op-ht ttree)
    (some-one-way-unify-cst-lst args (car op-bdd-rules)
                                op-ht mx-id ttree)
    (declare (type (signed-byte 30) mx-id))
    (cond
     (ans
      (bdd-mv-let
       (mx-id cst op-ht if-ht ttree)
       (bdd rhs alist op-ht if-ht mx-id ttree bddspv state)

; We could consider avoiding the following memoization for the application of
; lemmas.  The "be" benchmarks suggest mixed results.

       (mvf mx-id cst
            (aset1-trusted 'op-ht op-ht hash-index
                           (cons (list* cst op args)
                                 (aref1 'op-ht op-ht hash-index)))
            if-ht
            ttree)))
     (t (let ((bdd-constructors (access bddspv bddspv :bdd-constructors)))
          (cond
           ((member-eq op bdd-constructors)

; Then build a leaf node.  We do not distribute IF through calls of
; bdd-constructors.

            (combine-op-csts-simple
             hash-index op mask args op-ht if-ht mx-id nil ttree))
           (t (mv-let
               (mx-id ans rhs alist op-ht ttree)
               (some-one-way-unify-cst-lst args (cdr op-bdd-rules)
                                           op-ht mx-id ttree)
               (declare (type (signed-byte 30) mx-id))
               (cond
                (ans
                 (bdd-mv-let
                  (mx-id cst op-ht if-ht ttree)
                  (bdd rhs alist op-ht if-ht mx-id ttree bddspv state)

; We could consider avoiding the following memoization for the application of
; definitions.  The "be" benchmarks suggest mixed results.

                  (mvf mx-id cst
                       (aset1-trusted 'op-ht op-ht hash-index
                                      (cons (list* cst op args)
                                            (aref1 'op-ht op-ht hash-index)))
                       if-ht ttree)))
                (t
                 (let ((min-var (min-var nil args)))

; There is certainly a potential here for more case splitting than me might
; desire.  For, notice that min-var could be non-nil even though all of the
; args are leaves, because split-var (called by min-var) is happy to return a
; leaf that is known to be Boolean (and not t or nil).  However, our current
; model of how OBDDs will be used suggests that we rarely get to this part of
; the code anyhow, because operators not belonging to bdd-constructors will
; have been expanded away using rewrite rules or definitions.  So, we see no
; need at this point to take pains to avoid case splitting.  Instead, we prefer
; to err on the side of "completeness".

                   (cond
                    ((null min-var)
                     (combine-op-csts-simple
                      hash-index op mask args op-ht if-ht mx-id

; At this point we know that op is a not a member of bdd-constructors.  So we
; must pass in bdd-constructors here rather than nil.  See the comment in
; combine-op-csts-simple.

                      bdd-constructors ttree))
                    (t (mv-let
                        (args1 args2)
                        (combine-op-csts1 (unique-id min-var) args)

; Collect args1 for the true branch and args2 for the false branch.  For
; example, (foo x0 (if min-var x1 x2) (if min-var x3 x4)) yields
; (mv (list x0 x1 x3) (list x0 x2 x4)).  More reifically:

; (combine-op-csts1 3 '((4 x0 t)
;                       (9  (3 y t) t (5 x1 t) . (6 x2 t))
;                       (10 (3 y t) t (7 x3 t) . (8 x4 t))))

; is equal to

; (mv ((4 X0 T) (5 X1 T) (7 X3 T))
;     ((4 X0 T) (6 X2 T) (8 X4 T)))

                        (bdd-mv-let
                         (mx-id cst1 op-ht if-ht ttree)
                         (combine-op-csts+ mx-id comm-p enabled-exec-p
                                           op-code op mask args1 op-ht
                                           if-ht op-bdd-rules ttree bddspv)
                         (bdd-mv-let
                          (mx-id cst2 op-ht if-ht ttree)
                          (combine-op-csts+ mx-id comm-p enabled-exec-p
                                            op-code op mask args2 op-ht
                                            if-ht op-bdd-rules ttree bddspv)
                          (mv-let
                           (mx-id ans op-ht if-ht)
                           (make-if-for-op
                            mx-id hash-index op args min-var cst1 cst2
                            op-ht if-ht bdd-constructors)
                           (declare (type (signed-byte 30) mx-id))
                           (cond ((stringp ans)
                                  (bdd-error mx-id ans op-ht if-ht ttree))
                                 (t
                                  (mvf mx-id ans op-ht if-ht
                                       ttree)))))))))))))))))))))

(defun bdd (term alist op-ht if-ht mx-id ttree bddspv state)
  (declare (xargs :measure (acl2-count term)
                  :guard (pseudo-termp term))
           (type (signed-byte 30) mx-id))
  (the-mv
   5
   (signed-byte 30)
   (cond
    ((variablep term)
     (mvf mx-id
          (or (cdr (assoc-eq term alist))
              (er hard 'bdd
                  "Didn't find variable ~x0!"
                  term))
          op-ht if-ht ttree))
    ((fquotep term)
     (cond
      ((eq (cadr term) t)
       (mvf mx-id *cst-t* op-ht if-ht ttree))
      ((eq (cadr term) nil)
       (mvf mx-id *cst-nil* op-ht if-ht ttree))
      (t (bdd-quotep+ term op-ht if-ht mx-id ttree))))
    ((or (eq (ffn-symb term) 'if)
         (eq (ffn-symb term) 'if*))
     (bdd-mv-let
      (mx-id test-cst op-ht if-ht ttree)
      (bdd (fargn term 1) alist op-ht if-ht
           mx-id

; We will need to note the use of if* eventually, so for simplicity we do it
; now.

           (if (eq (ffn-symb term) 'if)
               ttree
             (push-lemma (fn-rune-nume 'if* nil nil (w state)) ttree))
           bddspv state)

; Note that we don't simply call combine-if-csts+, because we want to avoid
; applying bdd to one of the branches if the test already decides the issue.

      (cond
       ((cst-nilp test-cst)
        (bdd (fargn term 3) alist op-ht if-ht mx-id ttree bddspv state))
       ((cst-nonnilp test-cst)
        (bdd (fargn term 2) alist op-ht if-ht mx-id ttree bddspv state))
       ((eq (ffn-symb term) 'if*)
        (bdd-error
         mx-id
         "Unable to resolve test of IF* for term~|~%~p0~|~%under the ~
          bindings~|~%~x1~|~%-- use SHOW-BDD to see a backtrace."
         (list (cons #\0 (untranslate term nil (w state)))
               (cons #\1
                     (decode-cst-alist alist
                                       (leaf-cst-list-array mx-id))))

; We need a cst next, though we don't care about it.

         *cst-t*
         ttree))
       (t
        (bdd-mv-let
         (mx-id true-cst op-ht if-ht ttree)
         (bdd (fargn term 2) alist op-ht if-ht mx-id ttree bddspv state)
         (bdd-mv-let
          (mx-id false-cst op-ht if-ht ttree)
          (bdd (fargn term 3) alist op-ht if-ht mx-id ttree bddspv state)
          (mv-let
           (mx-id cst op-ht if-ht)
           (combine-if-csts test-cst true-cst false-cst op-ht if-ht mx-id
                            (access bddspv bddspv :bdd-constructors))
           (declare (type (signed-byte 30) mx-id))
           (cond
            ((stringp cst)
             (bdd-error mx-id cst op-ht if-ht ttree))
            (t
             (mvf mx-id cst op-ht if-ht ttree))))))))))
    ((flambdap (ffn-symb term))
     (bdd-mv-let
      (mx-id alist op-ht if-ht ttree)
      (bdd-alist (lambda-formals (ffn-symb term))
                 (fargs term)
                 alist op-ht if-ht
                 mx-id ttree bddspv state)
      (bdd (lambda-body (ffn-symb term))
           alist op-ht if-ht mx-id ttree bddspv state)))
    (t (mv-let
        (opcode comm-p enabled-exec-p mask)
        (op-alist-info (ffn-symb term)
                       (access bddspv bddspv :op-alist))
        (declare (type (signed-byte 30) opcode))
        (cond
         (comm-p
          (bdd-mv-let
           (mx-id arg1 op-ht if-ht ttree)
           (bdd (fargn term 1) alist op-ht if-ht mx-id ttree bddspv state)
           (bdd-mv-let
            (mx-id arg2 op-ht if-ht ttree)
            (bdd (fargn term 2) alist op-ht if-ht mx-id ttree bddspv state)
            (combine-op-csts-comm mx-id comm-p enabled-exec-p opcode
                                  (ffn-symb term) mask
                                  arg1 arg2 nil op-ht if-ht
                                  (cdr (assoc-eq (ffn-symb term)
                                                 (access bddspv bddspv
                                                         :bdd-rules-alist)))
                                  ttree bddspv state))))
         (t
          (bdd-mv-let (mx-id lst op-ht if-ht ttree)
                   (bdd-list (fargs term) alist op-ht if-ht mx-id ttree bddspv
                             state)
                   (combine-op-csts mx-id enabled-exec-p opcode
                                    (ffn-symb term) mask

; For a first cut I'll keep this simple.  Later, we may want to avoid consing
; up lst in the first place if we're only going to mess with it.

                                    lst op-ht if-ht
                                    (cdr (assoc-eq (ffn-symb term)
                                                   (access bddspv bddspv
                                                           :bdd-rules-alist)))
                                    ttree bddspv state)))))))))

(defun bdd-alist (formals actuals alist op-ht if-ht mx-id ttree bddspv state)
  (declare (type (signed-byte 30) mx-id))
  (the-mv
   5
   (signed-byte 30)
   (cond
    ((endp formals)
     (mvf mx-id nil op-ht if-ht ttree))
    (t (bdd-mv-let
        (mx-id bdd op-ht if-ht ttree)
        (bdd (car actuals) alist op-ht if-ht mx-id ttree bddspv state)
        (bdd-mv-let (mx-id rest-alist op-ht if-ht ttree)
                    (bdd-alist (cdr formals) (cdr actuals)
                               alist op-ht if-ht mx-id ttree bddspv state)
                    (mvf mx-id
                         (cons (cons (car formals) bdd)
                               rest-alist)
                         op-ht if-ht ttree)))))))

(defun bdd-list (lst alist op-ht if-ht mx-id ttree bddspv state)
  (declare (type (signed-byte 30) mx-id))
  (the-mv
   5
   (signed-byte 30)
   (cond
    ((endp lst)
     (mvf mx-id nil op-ht if-ht ttree))
    (t (bdd-mv-let
        (mx-id bdd op-ht if-ht ttree)
        (bdd (car lst) alist op-ht if-ht mx-id ttree bddspv state)
        (bdd-mv-let (mx-id rest op-ht if-ht ttree)
                    (bdd-list (cdr lst) alist op-ht if-ht mx-id ttree
                              bddspv state)
                    (mvf mx-id (cons bdd rest) op-ht if-ht ttree)))))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; VIII. TOP-LEVEL (INTERFACE) ROUTINES     ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We will ignore declaration opportunities in this section, especially for
; declaring mx-id to be a fixnum, because efficiency is a minor issue at this
; level.

; See axioms.lisp for the definition of if*.

(defun if-ht-max-length (state)
  (if (f-boundp-global 'if-ht-max-length state)
      (f-get-global 'if-ht-max-length state)
    (+ 100000 (hash-size))))

(defun op-ht-max-length (state)
  (if (f-boundp-global 'op-ht-max-length state)
      (f-get-global 'op-ht-max-length state)
    (+ 100000 (hash-size))))

(defun leaf-cst-list-to-alist (leaf-cst-list)

; Leaf-cst-list is a list of leaf csts of the form (unique-id var bool-flg).
; We return a corresponding alist in which each variable is paired with its
; cst.

  (cond
   ((endp leaf-cst-list)
    nil)
   (t (cons (cons (trm (car leaf-cst-list))
                  (car leaf-cst-list))
            (leaf-cst-list-to-alist (cdr leaf-cst-list))))))

#+(and gcl (not acl2-loop-only))
(defvar *request-bigger-fixnum-table*
  (fboundp 'system::allocate-bigger-fixnum-range))

(defun bdd-top (term input-vars bool-vars bdd-constructors cl-id ens state)

; This function returns a bddnote, where if an "error" occurs then the cst is
; nil.  This bddnote has an empty :term field.

; Input-vars should be the list of all variables, with the highest priority
; variables (those which will have the lowest unique-ids) listed first.  At any
; rate, all variables in bool-vars are to be considered Boolean-valued.

; This function is allowed to assume that we are in a context where only
; propositional equivalence need be maintained.

  (let* ((fns (all-fnnames term))
         (wrld (w state)))
    (mv-let (fns bdd-rules-alist)
            (bdd-rules-alist (remove1-eq 'if fns)
                             (add-to-set-eq 'if fns)
                             nil
                             ens
                             wrld)
            (let ((op-alist (op-alist fns nil 6 ens wrld))
                  (if-ht (compress1 'if-ht
                                    `((:header :dimensions
                                               (,(1+ (hash-size)))
                                               :maximum-length
                                               ,(if-ht-max-length state)
                                               :default nil))))
                  (op-ht (compress1 'op-ht
                                    `((:header :dimensions
                                               (,(1+ (hash-size)))
                                               :maximum-length
                                               ,(op-ht-max-length state)
                                               :default nil))))
                  (all-vars (let ((term-vars (reverse (all-vars term))))

; So, term-vars has the variables in print order of first occurrence, a very
; unsatisfying but very simple heuristic.

                              (cond ((not (symbol-listp input-vars))
                                     (er hard 'bdd-top
                                         "The second argument of BDD-TOP must ~
                                          be a list of variables, but ~x0 is ~
                                          not."
                                         input-vars))
                                    ((subsetp-eq term-vars input-vars)
                                     input-vars)
                                    (t (er hard 'bdd-top
                                           "The following variables are free ~
                                            in the input term, ~x0, but not do ~
                                            not occur in the specified input ~
                                            variables, ~x1:  ~x2."
                                           term input-vars
                                           (set-difference-eq term-vars
                                                              input-vars)))))))
              #+(and (not acl2-loop-only) akcl)
              (cond ((and (not *gcl-large-maxpages*)
                          (fboundp 'si::sgc-on)
                          (funcall 'si::sgc-on))
                     (fms "NOTE: Turning off SGC.  If you wish to turn SGC ~
                           back on again, execute (SI::SGC-ON T) in raw Lisp.~|"
                          nil (standard-co *the-live-state*)
                          *the-live-state* nil)
                     (funcall 'si::sgc-on nil)))
              #+(and gcl (not acl2-loop-only))
              (cond (*request-bigger-fixnum-table*
                     (allocate-fixnum-range 0 (hash-size))
                     (setq *request-bigger-fixnum-table* nil)))
              (mv-let (mx-id leaf-cst-list)
                      (leaf-cst-list all-vars
                                     bool-vars
                                     nil
                                     (max (unique-id *cst-nil*)
                                          (unique-id *cst-t*)))
                      (mv-let (mx-id cst op-ht if-ht ttree)
                              (bdd term (leaf-cst-list-to-alist leaf-cst-list)
                                   op-ht if-ht mx-id nil
                                   (make bddspv
                                         :op-alist op-alist
                                         :bdd-rules-alist bdd-rules-alist
                                         :bdd-constructors bdd-constructors)
                                   state)
                              (cond
                               ((stringp cst)

; Then we actually have
; (mv mx-id fmt-string (cons fmt-alist bad-cst) call-stack ttree).

                                (make bddnote
                                      :cl-id cl-id
                                      :goal-term term
                                      :mx-id mx-id
                                      :err-string cst
                                      :fmt-alist (car op-ht)
                                      :cst (cdr op-ht)
                                      :term nil
                                      :bdd-call-stack if-ht
                                      :ttree ttree))
                               (t
                                (make bddnote
                                      :cl-id cl-id
                                      :goal-term term
                                      :mx-id mx-id
                                      :err-string nil
                                      :fmt-alist nil
                                      :cst cst
                                      :term nil
                                      :bdd-call-stack nil
                                      :ttree ttree)))))))))

(defun get-bool-vars (vars type-alist ttree acc)
  (cond
   ((endp vars) (mv acc ttree))
   (t (let ((entry

; We use the low-level function assoc-eq here so that it is clear we are not
; depending on the ACL2 world.

             (assoc-eq (car vars) type-alist)))
        (cond
         ((and entry
               (ts-subsetp (cadr entry) *ts-boolean*))
          (get-bool-vars (cdr vars)
                         type-alist
                         (cons-tag-trees (cddr entry) ttree)
                         (cons (car vars) acc)))
         (t (get-bool-vars (cdr vars) type-alist ttree acc)))))))

(defun bdd-clause1 (hint-alist type-alist cl position ttree0 cl-id ens wrld
                               state)

; Returns (mv hitp x y), where:

; if hitp is 'error then x is a msg and y is nil or a bddnote;
; if hitp is 'miss then x is nil and y is a bddnote;
; else hitp is 'hit, in which case x is a list of clauses and y is a ttree.

  (let* ((term (case position
                     (:conc (mcons-term* 'if (car (last cl)) *t* *nil*))
                     (:all (mcons-term* 'if (disjoin cl) *t* *nil*))
                     (otherwise
                      (let ((lit (nth position cl)))
                        (case-match
                         lit
                         (('not x)
                          (mcons-term* 'if x *t* *nil*))
                         (& (mcons-term* 'not lit)))))))
         (all-vars (all-vars term))
         (vars-hint (cdr (assoc-eq :vars hint-alist)))
         (prove-hint (if (assoc-eq :prove hint-alist)
                         (cdr (assoc-eq :prove hint-alist))
                       t))
         (bdd-constructors-hint
          (if (assoc-eq :bdd-constructors hint-alist)
              (cdr (assoc-eq :bdd-constructors hint-alist))
            (bdd-constructors wrld))))
    (mv-let
     (bool-vars ttree1)
     (get-bool-vars all-vars type-alist ttree0 nil)
     (cond
      ((not (subsetp-eq (if (eq vars-hint t) all-vars vars-hint)
                        bool-vars))
       (let ((bad-vars
              (set-difference-eq (if (eq vars-hint t) all-vars vars-hint)
                                 bool-vars)))
         (mv 'error
             (msg "The following variable~#0~[ is~/s are~] not known to be ~
                   Boolean by trivial (type set) reasoning:  ~&0.  Perhaps you ~
                   need to add hypotheses to that effect.  Alternatively, you ~
                   may want to prove :type-prescription rules (see :DOC ~
                   type-prescription) or :forward-chaining (see :DOC ~
                   forward-chaining) rules to help with the situation, or ~
                   perhaps to start with the hint ~x1."
                  bad-vars
                  (list :cases
                        (if (consp (cdr bad-vars))
                            (list (cons 'and
                                        (pairlis$
                                         (make-list (length bad-vars)
                                                    :initial-element 'booleanp)
                                         (pairlis$ bad-vars nil))))
                          `((booleanp ,(car bad-vars))))))
             nil)))
      (t
       (let* ((real-vars-hint (if (eq vars-hint t) nil vars-hint))
              (bddnote (bdd-top term
                                (append real-vars-hint
                                        (set-difference-eq
                                         (reverse all-vars)
                                         real-vars-hint))
                                bool-vars
                                bdd-constructors-hint
                                cl-id
                                ens
                                state))
              (cst (access bddnote bddnote :cst))
              (err-string (access bddnote bddnote :err-string))
              (ttree (access bddnote bddnote :ttree)))
         (cond
          (err-string

; An error occurred; we aborted the bdd computation.

           (if prove-hint
               (mv 'error
                   (cons (access bddnote bddnote :err-string)
                         (access bddnote bddnote :fmt-alist))
                   bddnote)
             (mv 'miss nil bddnote)))
          ((cst-tp cst)
           (mv 'hit
               nil
               (add-to-tag-tree
                'bddnote
                bddnote
                (cons-tag-trees ttree ttree1))))
          (prove-hint
           (mv 'error
               (list "The :BDD hint for the current goal has ~
                      successfully simplified this goal, but has ~
                      failed to prove it.  Consider using (SHOW-BDD) ~
                      to suggest a counterexample; see :DOC show-bdd.")
               bddnote))
          (t (mv-let
              (new-term cst-array)
              (decode-cst
               cst
               (leaf-cst-list-array
                (access bddnote bddnote :mx-id)))
              (declare (ignore cst-array))
              (let* ((bddnote (change bddnote bddnote
                                      :term new-term))
                     (ttree (add-to-tag-tree
                             'bddnote
                             bddnote
                             (cons-tag-trees ttree ttree1))))
                (cond
                 ((eq position :conc)
                  (mv 'hit
                      (list (add-literal new-term
                                         (butlast cl 1)
                                         t))
                      ttree))
                 ((eq position :all)
                  (mv 'hit
                      (list (add-literal new-term nil nil))
                      ttree))
                 (t ; hypothesis
                  (mv 'hit
                      (list (subst-for-nth-arg (dumb-negate-lit new-term)
                                               position
                                               cl))
                      ttree)))))))))))))

(defmacro expand-and-or-simple+
  (term bool fns-to-be-ignored-by-rewrite wrld ttree)

; Unlike expand-and-or-simple, the list of terms (second value) returned by
; this macro is always ``correct,'' and the hitp value is always non-nil.

  `(mv-let (hitp lst ttree1)
           (expand-and-or-simple
            ,term ,bool ,fns-to-be-ignored-by-rewrite ,wrld ,ttree)
           (cond (hitp (mv hitp lst ttree1))
                 (t (mv t (list ,term) ,ttree)))))

(defun expand-and-or-simple
  (term bool fns-to-be-ignored-by-rewrite wrld ttree)

; See the comment in expand-clause.  This is a simple version of expand-and-or
; that does not expand abbreviations or, in fact, use lemmas at all (just the
; definitions of NOT, IF, and IMPLIES).  We expand the top-level fn symbol of
; term provided the expansion produces a conjunction -- when bool is nil -- or
; a disjunction -- when bool is t.  We return three values:  a hitp flag
; denoting success, the resulting list of terms (to be conjoined or disjoined
; to produce a term equivalent to term), and a new ttree.  If the hitp flag is
; nil then we make no guarantees about the ``resulting list of terms,'' which
; in fact (for efficiency) is typically nil.

; Note that this function only guarantees propositional (iff) equivalence of
; term with the resulting conjunction or disjunction.

  (cond ((variablep term)
         (mv nil nil ttree))
        ((fquotep term)
         (cond
          ((equal term *nil*)
           (if bool (mv t nil ttree) (mv nil nil ttree)))
          ((equal term *t*)
           (if bool (mv nil nil ttree) (mv t nil ttree)))
          (t
           (if bool (mv t (list *t*) ttree) (mv t nil ttree)))))
        ((member-equal (ffn-symb term) fns-to-be-ignored-by-rewrite)
         (mv nil nil ttree))
        ((flambda-applicationp term)

; Legacy comment, before adding lambda-okp argument to and-orp after v8-0 (the ACL2
; bdd package is used so rarely that we don't rethink this):

;   We don't use (and-orp (lambda-body (ffn-symb term)) bool) here because that
;   approach ignores nested lambdas.

         (mv-let (hitp lst ttree0)
                 (expand-and-or-simple
                  (lambda-body (ffn-symb term))
                  bool fns-to-be-ignored-by-rewrite wrld ttree)
                 (cond
                  (hitp (mv hitp
                            (subcor-var-lst
                             (lambda-formals (ffn-symb term))
                             (fargs term)
                             lst)
                            ttree0))
                  (t (mv nil nil ttree)))))
        ((eq (ffn-symb term) 'not)
         (mv-let (hitp lst ttree0)
                 (expand-and-or-simple (fargn term 1) (not bool)
                                       fns-to-be-ignored-by-rewrite wrld ttree)
                 (cond (hitp
                        (mv hitp
                            (dumb-negate-lit-lst lst)
                            (push-lemma (fn-rune-nume 'not nil nil wrld)
                                        ttree0)))
                       (t (mv nil nil ttree)))))
        ((and (eq (ffn-symb term) 'implies)
              bool)
         (expand-and-or-simple
          (subcor-var (formals 'implies wrld)
                      (fargs term)
                      (bbody 'implies))
          bool fns-to-be-ignored-by-rewrite wrld
          (push-lemma (fn-rune-nume 'implies nil nil wrld)
                      ttree)))
        ((eq (ffn-symb term) 'if)
         (let ((t1 (fargn term 1))
               (t2 (fargn term 2))
               (t3 (fargn term 3)))
           (cond
            ((or (equal t1 *nil*)
                 (equal t2 t3))
             (expand-and-or-simple+ t3 bool fns-to-be-ignored-by-rewrite
                                    wrld ttree))
            ((quotep t1)
             (expand-and-or-simple+ t2 bool fns-to-be-ignored-by-rewrite
                                    wrld ttree))
            ((and (quotep t2) (quotep t3))
             (cond
              ((equal t2 *nil*)

; We already know t2 is not t3, so we have t3 = *t* up to iff-equivalence, and
; hence we are looking at (not t1) up to iff-equivalence.

               (mv-let (hitp lst ttree)
                       (expand-and-or-simple t1 (not bool)
                                             fns-to-be-ignored-by-rewrite
                                             wrld ttree)
                       (mv t
                           (if hitp
                               (dumb-negate-lit-lst lst)
                             (list (dumb-negate-lit t1)))
                           ttree)))
              ((equal t3 *nil*)
               (expand-and-or-simple+ t1 bool
                                      fns-to-be-ignored-by-rewrite
                                      wrld ttree))
              (t
               (expand-and-or-simple *t* bool
                                     fns-to-be-ignored-by-rewrite
                                     wrld ttree))))
            ((and (quotep t3)
                  (eq (not bool) (equal t3 *nil*)))

; We combine the cases (or (not t1) t2) [bool = t] and (and t1 t2) [bool =
; nil].

             (mv-let (hitp lst1 ttree)
                     (expand-and-or-simple+ t1 nil
                                            fns-to-be-ignored-by-rewrite
                                            wrld ttree)
                     (declare (ignore hitp))
                     (mv-let (hitp lst2 ttree)
                             (expand-and-or-simple+
                              t2 bool
                              fns-to-be-ignored-by-rewrite wrld ttree)
                             (declare (ignore hitp))
                             (if bool
                                 (mv t
                                     (union-equal (dumb-negate-lit-lst lst1)
                                                  lst2)
                                     ttree)
                               (mv t (union-equal lst1 lst2) ttree)))))
            ((and (quotep t2)
                  (eq (not bool) (equal t2 *nil*)))

; We combine the cases (or t1 t3) [bool = t] and (and (not t1) t3)
; [bool = nil].

             (mv-let (hitp lst1 ttree)
                     (expand-and-or-simple+ t1 t
                                            fns-to-be-ignored-by-rewrite
                                            wrld ttree)
                     (declare (ignore hitp))
                     (mv-let (hitp lst2 ttree)
                             (expand-and-or-simple+
                              t3 bool
                              fns-to-be-ignored-by-rewrite wrld ttree)
                             (declare (ignore hitp))
                             (if bool
                                 (mv t (union-equal lst1 lst2) ttree)
                               (mv t
                                   (union-equal (dumb-negate-lit-lst lst1)
                                                lst2)
                                   ttree)))))
            (t (mv nil nil ttree)))))
        (t (mv nil nil ttree))))

(defun expand-clause
  (cl fns-to-be-ignored-by-rewrite wrld ttree acc)

; A classic form for a bdd problem is something like the following.

; (let ((x (list x0 x1 ...))
;   (implies (boolean-listp x)
;            ...)

; How do we let the bdd package know that x0, x1, ... are Boolean?  It needs to
; know that x really is (list x0 x1 ...), and then it needs to forward-chain
; from (boolean-listp (list x0 x1 ...)) to the conjunction of (booleanp xi).
; However, the clause handed to bdd-clause may be a one-element clause with the
; literal displayed above, so here we "flatten" this literal into a clause that
; is more amenable to forward-chaining.

  (cond
   ((endp cl) (mv acc ttree))
   (t (mv-let (hitp lst ttree)
              (expand-and-or-simple+
               (car cl) t fns-to-be-ignored-by-rewrite wrld ttree)
              (declare (ignore hitp))
              (expand-clause (cdr cl) fns-to-be-ignored-by-rewrite wrld
                             ttree (union-equal lst acc))))))

(defun bdd-clause (bdd-hint cl-id top-clause pspv wrld state)

; This function is analogous to simplify-clause (except that bdd-hint is passed
; in here), and shares much code with simplify-clause1.  It is separated out
; from apply-top-hints-clause for readability.  We return 4 values, as required
; by apply-top-hints-clause.

; Unlike simplify-clause1, we do not call ok-to-force, but instead we do not
; force during forward-chaining.  We may want to revisit that decision, but
; for now, we prefer to minimize forcing during bdd processing.

  (let ((rcnst (access prove-spec-var pspv :rewrite-constant))
        (literal-hint (or (cdr (assoc-eq :literal bdd-hint))
                          :all)))
    (cond
     ((and (integerp literal-hint)

; Note that literal-hint is a 0-based index; see translate-bdd-hint1.  We know
; that literal-hint is non-negative, translate-bdd-hint1 never returns a
; negative literal-hint.

           (not (< literal-hint (1- (length top-clause)))))
      (mv 'error
          (msg "There ~#0~[are no hypotheses~/is only one hypothesis~/are only ~
                ~n0 hypotheses~] in this goal, but your :BDD hint suggested ~
                that there would be at least ~x1 ~
                ~#1~[~/hypothesis~/hypotheses]."
               (1- (length top-clause))
               (1+ literal-hint))
          nil
          pspv))
     (t
      (mv-let (hitp current-clause current-clause-pts
                    remove-trivial-equivalences-ttree)
              (remove-trivial-equivalences top-clause
                                           (enumerate-elements top-clause 0)
                                           t
                                           (access rewrite-constant rcnst
                                                   :current-enabled-structure)
                                           wrld state nil)
              (declare (ignore hitp))
              (let ((position (cond ((integerp literal-hint)
                                     (position literal-hint
                                               current-clause-pts))
                                    (t literal-hint))))
                (cond
                 ((or (null position)
                      (and (eq literal-hint :conc)
                           (not (member (1- (length top-clause))
                                        current-clause-pts))))
                  (mv 'error
                      (msg "The attempt to use a :BDD hint for the goal named ~
                            \"~@0\" has failed.  The problem is that the hint ~
                            specified that BDD processing was to be used on ~
                            the ~#1~[~n2 hypothesis~/conclusion~], which has ~
                            somehow disappeared.  One possibility is that this ~
                            literal is an equivalence that has disappeared ~
                            after being used for substitution into the rest of ~
                            the goal.  Another possibility is that this ~
                            literal has merged with another.  We suspect, ~
                            therefore, that you would benefit by reconsidering ~
                            this :BDD hint, possibly attaching it to a ~
                            subsequent goal instead."
                           (tilde-@-clause-id-phrase cl-id)
                           (if (null position) 0 1)
                           (if (null position) (1+ literal-hint) 0))
                      nil
                      pspv))
                 (t
                  (let ((ens (access rewrite-constant rcnst
                                     :current-enabled-structure)))
                    (mv-let (expanded-clause ttree)
                            (expand-clause
                             current-clause
                             (access rewrite-constant
                                     rcnst
                                     :fns-to-be-ignored-by-rewrite)
                             wrld remove-trivial-equivalences-ttree nil)
                            (mv-let
                             (contradictionp type-alist fc-pair-lst)
                             (forward-chain-top 'bdd-clause
                                                expanded-clause
                                                nil
                                                nil ; Let's not force
                                                t ; do-not-reconsiderp
                                                wrld
                                                ens
                                                (match-free-override wrld)
                                                state)
                             (cond
                              (contradictionp

; Note: When forward-chain returns with contradictionp = t, then the
; "fc-pair-lst" is really a ttree.  We must add the remove-trivial-
; equivalences ttree to the ttree returned by forward-chain and we must
; remember our earlier case splits.

                               (mv 'hit
                                   nil
                                   (cons-tag-trees ttree fc-pair-lst)
                                   pspv))
                              (t (mv-let (changedp clauses ttree)

; Ttree is either nil or a bddnote if changedp is 'miss or 'error.  See
; waterfall-step.

                                         (bdd-clause1 bdd-hint type-alist
                                                      current-clause position
                                                      ttree
                                                      cl-id ens wrld state)
                                         (mv changedp clauses ttree
                                             pspv)))))))))))))))

; See show-bdd and successive definitions for code used to inspect the
; results of using OBDDs.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;; IX.   COMPILING THIS FILE AND OTHER HELPFUL TIPS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; In order to check for slow code, you can execute the following from ACL2 built
; on GCL, inside raw Lisp.
;
; (compile-file "bdd.lisp" :c-file t)
;
; Then, search the file bdd.c for make_fixnum and number_ for slow stuff.  Note
; that you'll find a lot of these, but you only need to worry about them in the
; workhorse functions, and you don't need to worry about CMPmake_fixnum when it
; is used for an error or for a new mx-id.
;
; When you find one of these, search upward for `local entry' to see which
; function or macro you are in.  Don't worry, for example, about commutative-p,
; which is a database kind of function rather than a workhorse function.
;
; You'll see things like the following (from local entry to BDD).  The idea here
; is that we are boxing a fixnum and pushing it on a stack, but why?  LnkLI253
; appears to be a function call, which is found near the end of the file to
; correspond to leaf-cst-list-array.  If we're still not clear on what's going
; on, we can look up 273 as well.  When we do this, we find that we are probably
; in the part of the BDD code shown at the end, which is not a problem.
;
;         V1570 = CMPmake_fixnum(V1549);
;         V1571= (*(LnkLI253))(/* INLINE-ARGS */V1569,V1570);
;         V1572= (*(LnkLI273))((V1525),/* INLINE-ARGS */V1571);
;
; ....
;
; static object  LnkTLI273(va_alist)va_dcl{va_list ap;va_start(ap);
;  return(object )call_proc(VV[273],&LnkLI273,2,ap);} /* DECODE-CST-ALIST */
;
; static object  LnkTLI253(va_alist)va_dcl{va_list ap;va_start(ap);
;  return(object )call_proc(VV[253],&LnkLI253,2,ap);} /* LEAF-CST-LIST-ARRAY */
;
; ; Source code from (defun bdd ...) [an earlier version]:
;
;         (bdd-error
;          mx-id
;          "Unable to resolve test of IF* for term~|~%~p0~|~%under the ~
;           bindings~|~%~x1~|~%-- use SHOW-BDD to see a backtrace."
;          (list (cons #\0 (untranslate term nil))
;                (cons #\1
;                      (decode-cst-alist alist
;                                        (leaf-cst-list-array
;                                         (strip-cdrs alist)
;                                         mx-id))))
;
; ; We need a cst next, though we don't care about it.
;
;          *cst-t*
;          ttree)
