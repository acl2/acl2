; Copyright (C) 2014, Regents of the University of Texas
; Contributed by Matt Kaufmann (original date October, 2012)
; based on earlier work by Sol Swords.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; (certify-book "meta-extract-simple-test" 0 t :ttags :all)

; This example is based on the first one in
; clause-processors/meta-extract-user.lisp, but is simpler -- in particular, it
; does not include that book.

; For a more interesting tutorial example on meta-extract hypotheses, see
; community book
; /projects/acl2/acl2/books/demos/nth-update-nth-meta-extract.lisp.

(in-package "ACL2")

; The following is only needed for developer builds (using ACL2_DEVEL), which
; put some meta-extract functions in :program mode.
(include-book "system/meta-extract" :dir :system)
(include-book "misc/without-waterfall-parallelism" :dir :system)

(encapsulate
 ((bar (x) t))
 (local (defun bar (x) (declare (ignore x)) 1))
 (defthm bar-posp
   (posp (bar u))
   :rule-classes nil))

(defevaluator nthmeta-ev nthmeta-ev-lst
  ((typespec-check ts x)
   (if a b c)
   (equal a b)
   (not a)
   (iff a b)
   (implies a b)
   (nth n x)
   (car x)
   (binary-+ x y)
   (fix x)
   (posp x)
   (bar x)))

; Here is a trivial test of the use of meta-extract-global-fact in
; clause-processor rules.

(defun bar-posp-cl-proc (cl hint state)
  (declare (xargs :guard t
                  :stobjs state)
           (ignore hint))
  (if (equal (meta-extract-formula 'bar-posp state)
             '(POSP (BAR U)))
      (value (list (cons '(not (posp (bar u))) cl)))
    (value (list cl))))

(defthm correctness-of-bar-posp-cl-proc
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (nthmeta-ev (meta-extract-global-fact '(:formula bar-posp)
                                                      state)
                            a)
                (nthmeta-ev (conjoin-clauses
                             (clauses-result
                              (bar-posp-cl-proc cl hint state)))
                            a))
           (nthmeta-ev (disjoin cl) a))
  :rule-classes :clause-processor)

(without-waterfall-parallelism
(defthm bar-posp-cl-proc-test
  (integerp (bar u))
  :hints (("Goal"
           :clause-processor
           (bar-posp-cl-proc clause nil state)))))

; Our first example for :meta rules is based on one in
; books/clause-processors/meta-extract-user.lisp.

; First we develop a meta rule that implements the following fact.  (We do not
; need this event.)
(defthm nth-when-symbolp
  (implies (symbolp n)
           (equal (nth n x) (car x)))
  :rule-classes nil)

(defun nth-symbolp-metafn (term mfc state)
  (declare (xargs :stobjs state))
  (case-match term
    (('nth n x)
     (if (equal (mfc-ts n mfc state :forcep nil) *ts-symbol*)
         `(car ,x)
       (prog2$ (cw "Oops, the typeset of n is ~x0~%"
                   (mfc-ts n mfc state :forcep nil))
               term)))
    (& term)))

(defthm nth-symbolp-meta
    (implies (nthmeta-ev (meta-extract-contextual-fact
                          `(:typeset ,(cadr term))
                          mfc
                          state)
                         a)
             (equal (nthmeta-ev term a)
                    (nthmeta-ev (nth-symbolp-metafn term mfc state) a)))
    :rule-classes ((:meta :trigger-fns (nth))))

(defstub foo (x) t)

(defthm foo-test
  (implies (symbolp (foo x))
           (equal (nth (foo x) y)
                  (car y)))
  :hints (("Goal" :in-theory '(nth-symbolp-meta))))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defun nth-symbolp-metafn-alt (term mfc state)
   (declare (xargs :stobjs state))
   (case-match term
     (('nth n x)
      (if (let ((ts-n (mfc-ts n mfc state :forcep nil)))
            (and (integerp ts-n)          ; for guard verification
                 (<= *min-type-set* ts-n) ; for guard verification
                 (<= ts-n *max-type-set*) ; for guard verification
                 (ts-subsetp ts-n *ts-symbol*)))
          `(car ,x)
        (prog2$ (cw "Oops, the typeset of n is ~x0~%"
                    (mfc-ts n mfc state :forcep nil))
                term)))
     (& term)))

 (defthm nth-symbolp-meta-alt
   (implies (nthmeta-ev (meta-extract-contextual-fact
                         `(:typeset ,(cadr term)) mfc state)
                        a)
            (equal (nthmeta-ev term a)
                   (nthmeta-ev (nth-symbolp-metafn-alt term mfc state) a)))
   :rule-classes ((:meta :trigger-fns (nth)))))

(defthm foo-test-alt
  (implies (symbolp (foo x))
           (equal (nth (foo x) y)
                  (car y)))
  :hints (("Goal" :in-theory '(nth-symbolp-meta-alt))))

; Now, a slight variant involving subtypes, implementing this fact: (We do not
; need this event.)
(defthm plus-identity
  (implies (and (acl2-numberp n)
                (not (acl2-numberp x)))
           (equal (+ n x)
                  n))
  :rule-classes nil)

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defun plus-identity-metafn (term mfc state)
   (declare (xargs :stobjs state))
   (case-match term
     (('binary-+ n x)
      (let ((ts-n (mfc-ts n mfc state :forcep nil))
            (ts-x (mfc-ts x mfc state :forcep nil)))
        (if (and (integerp ts-n)         ; for guard verification
                 (integerp ts-x)         ; for guard verification
                 (<= *min-type-set* ts-n) ; for guard verification
                 (<= *min-type-set* ts-x) ; for guard verification
                 (<= ts-n *max-type-set*) ; for guard verification
                 (<= ts-x *max-type-set*) ; for guard verification
                 (ts= ts-n *ts-positive-integer*)
                 (ts= ts-x *ts-character*))
            n
          (prog2$ (cw "Oops, the typesets of n and x are ~x0 and ~x1~%"
                      (mfc-ts n mfc state :forcep nil)
                      (mfc-ts x mfc state :forcep nil))
                  term))))
     (& term))))

(defthm plus-identity-meta
    (implies (and (nthmeta-ev (meta-extract-contextual-fact
                               `(:typeset ,(cadr term)) mfc state)
                              a)
                  (nthmeta-ev (meta-extract-contextual-fact
                               `(:typeset ,(caddr term)) mfc state)
                              a))
             (equal (nthmeta-ev term a)
                    (nthmeta-ev (plus-identity-metafn term mfc state) a)))
    :rule-classes ((:meta :trigger-fns (binary-+))))

(defthm plus-identity-test
  (implies (and (posp (foo x))
                (characterp (foo y)))
           (equal (+ (foo x) (foo y))
                  (foo x)))
  :hints (("Goal" :in-theory '(posp plus-identity-meta))))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defun plus-identity-2-metafn (term mfc state)
   (declare (xargs :stobjs state))
   (case-match term
     (('binary-+ ('bar n) y)
      (cond
       ((equal (meta-extract-formula 'bar-posp state)
               '(POSP (BAR U)))
        (let ((ts-y (mfc-ts y mfc state :forcep nil)))
          (if (and (integerp ts-y)        ; for guard verification
                   (<= *min-type-set* ts-y) ; for guard verification
                   (<= ts-y *max-type-set*) ; for guard verification
                   (ts= ts-y *ts-character*))
              (cadr term)
            (prog2$ (cw "Oops, the typesets of n and y are ~x0 and ~x1~%"
                        (mfc-ts n mfc state :forcep nil)
                        (mfc-ts y mfc state :forcep nil))
                    term))))
       (t term)))
     (& term))))

(defthm plus-identity-2-meta
    (implies (and (nthmeta-ev (meta-extract-global-fact '(:formula bar-posp)
                                                      state)
                              (list (cons 'u
                                          (nthmeta-ev (cadr (cadr term))
                                                      a))))
                  (nthmeta-ev (meta-extract-contextual-fact
                               `(:typeset ,(caddr term)) mfc state)
                              a))
             (equal (nthmeta-ev term a)
                    (nthmeta-ev (plus-identity-2-metafn term mfc state) a)))
    :rule-classes ((:meta :trigger-fns (binary-+))))

(defthm plus-identity-2-test
  (implies (and (posp (bar x))
                (characterp (foo y)))
           (equal (+ (bar x) (foo y))
                  (bar x)))
  :hints (("Goal" :in-theory '(plus-identity-2-meta))))
