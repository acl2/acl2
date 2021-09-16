; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>


(in-package "ACL2")

;; Have you ever wanted a clause processor to help you prove the
;; correctness of other clause processors?  If so, you might be beyond
;; help.  However, this book defines several functions and theorems
;; that might aid in proving claims about evaluator functions as
;; defined with defevaluator or defevaluator-fast.  See defapply.lisp
;; for an example of how they may be used.  The functions can be used
;; as-is; the theorems will need to be functionally instantiated so as
;; to be usable with the evaluator of your choice, unless the
;; evaluator defined in this book suits your needs.




(include-book "std/util/define" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "tools/match-tree" :dir :system)
(local (in-theory (disable mv-nth)))


(defevaluator evmeta-ev evmeta-ev-lst
  ((eql a b)
   (equal a b)
   (implies a b)
   (if a b c)
   (not a)
   (car x)
   (cdr x)
   (nth n x)
   (cons a b)
   (consp x)
   (cons-with-hint x y hint)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced assoc-eq by assoc-equal).]
   (assoc-equal x a)
   (kwote-lst lst)
   (symbolp x)
   (pairlis$ a b)
   (return-last fn x y)
   (hide a)
   (mv-nth n x)
   (mv-list n x)

   (typespec-check ts x)
   (iff a b)
   (binary-+ a b)
   (unary-- a)
   (len x)

   (synp vars form term)
   )
  :namedp t)





(def-meta-extract evmeta-ev evmeta-ev-lst)


(local (defthm meta-extract-formula-w-elim
         (equal (meta-extract-formula-w name (w st))
                (meta-extract-formula name st))
         :hints(("Goal" :in-theory (enable meta-extract-formula
                                           meta-extract-formula-w)))))


(local (in-theory (disable w)))

;; (define check-synp-is-true ((world plist-worldp))
;;   (equal (meta-extract-formula-w 'synp world)
;;          '(equal (synp vars form term) 't))
;;   ///
;;   (defthm check-synp-is-true-correct
;;     (implies (and (evmeta-ev-meta-extract-global-facts)
;;                   (check-synp-is-true (w state)))
;;              (equal (evmeta-ev (list 'synp x y z) a) t))
;;     :hints (("goal" :use ((:instance evmeta-ev-meta-extract-formula
;;                            (name 'synp) (st state)
;;                            (a `((vars . ,(evmeta-ev x a))
;;                                 (form . ,(evmeta-ev y a))
;;                                 (term . ,(evmeta-ev z a))))))
;;              :in-theory (e/d (evmeta-ev-of-fncall-args)
;;                              (evmeta-ev-meta-extract-formula))))))
  

(defthmd evmeta-ev-of-match-tree
  (b* (((mv ok alist) (match-tree pat x alist)))
    (implies ok
             (equal (evmeta-ev x a)
                    (evmeta-ev (subst-tree pat alist) a))))
  :hints(("Goal" :in-theory (enable match-tree-is-subst-tree))))

(local (in-theory (enable evmeta-ev-of-match-tree)))

;; Constraint 0.
(define check-ev-of-fncall-args ((evfn symbolp)
                                 (evfn-lst symbolp)
                                 (name symbolp)
                                 (world plist-worldp))
  (b* ((form (meta-extract-formula-w name world))
       ((unless-match form
                      (IMPLIES (IF (CONSP X)
                                   (IF (SYNP 'NIL
                                             '(SYNTAXP (NOT (EQUAL A ''NIL)))
                                             '(IF (NOT (EQUAL A ''NIL)) 'T 'NIL))
                                       (NOT (EQUAL (CAR X) 'QUOTE))
                                       'NIL)
                                   'NIL)
                               (EQUAL ((:! evfn) X A)
                                      ((:! evfn) (CONS (CAR X)
                                                       (KWOTE-LST ((:! evfn-lst) (CDR X) A)))
                                       'NIL))))
        nil))
    t)
  ///
  (local (def-match-tree-rewrites
           (IMPLIES (IF (CONSP X)
                        (IF (SYNP 'NIL
                                  '(SYNTAXP (NOT (EQUAL A ''NIL)))
                                  '(IF (NOT (EQUAL A ''NIL)) 'T 'NIL))
                            (NOT (EQUAL (CAR X) 'QUOTE))
                            'NIL)
                        'NIL)
                    (EQUAL ((:! evfn) X A)
                           ((:! evfn) (CONS (CAR X)
                                            (KWOTE-LST ((:! evfn-lst) (CDR X) A)))
                            'NIL)))))

  (defthm check-ev-of-fncall-args-correct
    (implies (and (consp (evmeta-ev x1 a))
                  (not (equal (car (evmeta-ev x1 a)) 'quote))
                  (evmeta-ev-meta-extract-global-facts)
                  (check-ev-of-fncall-args evfn evfn-lst name (w state))
                  (not (eq evfn 'quote))
                  (not (eq evfn-lst 'quote)))
             (equal (evmeta-ev (list evfn x1 a1) a)
                    (evmeta-ev `(,evfn
                                 (cons (car ,x1)
                                       (kwote-lst
                                        (,evfn-lst (cdr ,x1) ,a1)))
                                 'nil)
                               a)))
    :hints (("goal" :use ((:instance evmeta-ev-meta-extract-formula
                           (name name)
                           (st state)
                           (a `((x . ,(evmeta-ev x1 a))
                                (a . ,(evmeta-ev a1 a))))))
             :in-theory (e/d (evmeta-ev-of-fncall-args)
                             (evmeta-ev-meta-extract-formula)))))

  (assert-event (check-ev-of-fncall-args 'evmeta-ev 'evmeta-ev-lst
                                         'evmeta-ev-of-fncall-args
                                         (w state))))

;; Constraint 1.
(define check-ev-of-variable ((evfn symbolp)
                              (name symbolp)
                              (world plist-worldp))
  (b* ((form (meta-extract-formula-w name world))
       ((unless-match form
                      (IMPLIES (SYMBOLP X)
                               (EQUAL ((:! evfn) X A)
                                      (IF X (CDR (ASSOC-EQUAL X A)) 'NIL))))
        nil))
    t)
  ///
  (defthm check-ev-of-variable-correct
    (implies (and (symbolp (evmeta-ev x1 a))
                  (evmeta-ev-meta-extract-global-facts)
                  (check-ev-of-variable evfn name (w state))
                  (not (eq evfn 'quote)))
             (equal (evmeta-ev (list evfn x1 a1) a)
                    (evmeta-ev `(if ,x1
                                    (cdr (assoc-equal ,x1 ,a1))
                                  'nil)
                               a)))
    :hints (("goal" :use ((:instance evmeta-ev-meta-extract-formula
                           (name name)
                           (st state)
                           (a `((x . ,(evmeta-ev x1 a))
                                (a . ,(evmeta-ev a1 a))))))
             :in-theory (e/d (evmeta-ev-of-fncall-args)
                             (evmeta-ev-meta-extract-formula)))))

  (assert-event (check-ev-of-variable 'evmeta-ev 'evmeta-ev-of-variable (w state))))


(define check-ev-of-quote ((evfn symbolp)
                           (name symbolp)
                           (world plist-worldp))
  (b* ((form (meta-extract-formula-w name world))
       ((unless-match form
                      (IMPLIES (IF (CONSP X)
                                   (EQUAL (CAR X) 'QUOTE)
                                   'NIL)
                               (EQUAL ((:! evfn) X A) (CAR (CDR X)))))
        nil))
    t)
  ///
  (defthm check-ev-of-quote-correct
    (implies (and (consp (evmeta-ev x1 a))
                  (equal (car (evmeta-ev x1 a)) 'quote)
                  (evmeta-ev-meta-extract-global-facts)
                  (check-ev-of-quote evfn name (w state))
                  (not (eq evfn 'quote)))
             (equal (evmeta-ev (list evfn x1 a1) a)
                    (evmeta-ev `(car (cdr ,x1))
                               a)))
    :hints (("goal" :use ((:instance evmeta-ev-meta-extract-formula
                           (name name)
                           (st state)
                           (a `((x . ,(evmeta-ev x1 a))
                                (a . ,(evmeta-ev a1 a))))))
             :in-theory (e/d (evmeta-ev-of-fncall-args)
                             (evmeta-ev-meta-extract-formula)))))

  (assert-event (check-ev-of-quote 'evmeta-ev 'evmeta-ev-of-quote (w state))))

(define check-ev-of-lambda ((evfn symbolp)
                            (evfn-lst symbolp)
                            (name symbolp)
                           (world plist-worldp))
  (b* ((form (meta-extract-formula-w name world))
       ((unless-match form
                      (IMPLIES (IF (CONSP X) (CONSP (CAR X)) 'NIL)
                               (EQUAL ((:! evfn) X A)
                                      ((:! evfn) (CAR (CDR (CDR (CAR X))))
                                                 (PAIRLIS$ (CAR (CDR (CAR X)))
                                                           ((:! evfn-lst) (CDR X) A))))))
        nil))
    t)
  ///
  (defthm check-ev-of-lambda-correct
    (implies (and (consp (evmeta-ev x1 a))
                  (consp (car (evmeta-ev x1 a)))
                  (evmeta-ev-meta-extract-global-facts)
                  (check-ev-of-lambda evfn evfn-lst name (w state))
                  (not (eq evfn 'quote))
                  (not (eq evfn-lst 'quote)))
             (equal (evmeta-ev (list evfn x1 a1) a)
                    (evmeta-ev `(,evfn (car (cdr (cdr (car ,x1))))
                                       (pairlis$ (car (cdr (car ,x1)))
                                                 (,evfn-lst (cdr ,x1) ,a1)))
                               a)))
    :hints (("goal" :use ((:instance evmeta-ev-meta-extract-formula
                           (name name)
                           (st state)
                           (a `((x . ,(evmeta-ev x1 a))
                                (a . ,(evmeta-ev a1 a))))))
             :in-theory (e/d (evmeta-ev-of-fncall-args)
                             (evmeta-ev-meta-extract-formula)))))

  (assert-event (check-ev-of-lambda 'evmeta-ev 'evmeta-ev-lst 'evmeta-ev-of-lambda (w state))))

(define check-ev-of-nonsymbol-atom ((evfn symbolp)
                            (name symbolp)
                           (world plist-worldp))
  (b* ((form (meta-extract-formula-w name world))
       ((unless-match form
                      (IMPLIES (IF (NOT (CONSP X))
                                   (NOT (SYMBOLP X))
                                   'NIL)
                               (EQUAL ((:! evfn) X A) 'NIL)))
        nil))
    t)
  ///
  (defthm check-ev-of-nonsymbol-atom-correct
    (implies (and (not (evmeta-ev x1 a))
                  (not (symbolp (evmeta-ev x1 a)))
                  (evmeta-ev-meta-extract-global-facts)
                  (check-ev-of-nonsymbol-atom evfn name (w state))
                  (not (eq evfn 'quote)))
             (equal (evmeta-ev (list evfn x1 a1) a)
                    nil))
    :hints (("goal" :use ((:instance evmeta-ev-meta-extract-formula
                           (name name)
                           (st state)
                           (a `((x . ,(evmeta-ev x1 a))
                                (a . ,(evmeta-ev a1 a))))))
             :in-theory (e/d (evmeta-ev-of-fncall-args)
                             (evmeta-ev-meta-extract-formula)))))

  (assert-event (check-ev-of-nonsymbol-atom 'evmeta-ev 'evmeta-ev-of-nonsymbol-atom (w state))))


(define check-ev-of-bad-fncall ((evfn symbolp)
                            (name symbolp)
                           (world plist-worldp))
  (b* ((form (meta-extract-formula-w name world))
       ((unless-match form
                      (IMPLIES (IF (CONSP X)
                                   (IF (NOT (CONSP (CAR X)))
                                       (NOT (SYMBOLP (CAR X)))
                                       'NIL)
                                   'NIL)
                               (EQUAL ((:! evfn) X A) 'NIL)))
        nil))
    t)
  ///
  (defthm check-ev-of-bad-fncall-correct
    (implies (and (consp (evmeta-ev x1 a))
                  (not (consp (car (evmeta-ev x1 a))))
                  (not (symbolp (car (evmeta-ev x1 a))))
                  (evmeta-ev-meta-extract-global-facts)
                  (check-ev-of-bad-fncall evfn name (w state))
                  (not (eq evfn 'quote)))
             (equal (evmeta-ev (list evfn x1 a1) a)
                    nil))
    :hints (("goal" :use ((:instance evmeta-ev-meta-extract-formula
                           (name name)
                           (st state)
                           (a `((x . ,(evmeta-ev x1 a))
                                (a . ,(evmeta-ev a1 a))))))
             :in-theory (e/d (evmeta-ev-of-fncall-args)
                             (evmeta-ev-meta-extract-formula)))))

  (assert-event (check-ev-of-bad-fncall 'evmeta-ev 'evmeta-ev-of-bad-fncall (w state))))


(define ev-of-arglist ((n natp)
                       (evfn symbolp)
                       arglist-obj alist-obj)
  (if (zp n)
      nil
    (cons `(,evfn ',(ec-call (car arglist-obj)) ',alist-obj)
          (ev-of-arglist (1- n) evfn
                         (ec-call (cdr arglist-obj)) alist-obj)))
  ///
  (defthm ev-of-arglist-is-ground
    (implies (and (syntaxp (not (equal a ''nil)))
                  (not (equal evfn 'quote)))
             (equal (evmeta-ev-lst (ev-of-arglist n evfn arglist alist) a)
                    (evmeta-ev-lst (ev-of-arglist n evfn arglist alist) nil)))
    :hints(("Goal" :in-theory (enable evmeta-ev-of-fncall-args)))))

(define ev-of-arglist-symb ((n natp)
                            (evfn symbolp)
                            arglist-term alist-term)
  (if (zp n)
      nil
    (cons `(,evfn (car ,arglist-term) ,alist-term)
          (ev-of-arglist-symb (1- n) evfn
                              `(cdr ,arglist-term) alist-term)))
  ///
  (defthm evmeta-ev-lst-of-ev-of-arglist-symb
    (implies (not (equal evfn 'quote))
             (equal (evmeta-ev-lst (ev-of-arglist-symb n evfn arglist-term alist-term) a)
                    (evmeta-ev-lst (ev-of-arglist n evfn (evmeta-ev arglist-term a) (evmeta-ev alist-term a))
                                   nil)))
    :hints(("Goal" :in-theory (enable evmeta-ev-of-fncall-args ev-of-arglist)))))

(define ev-of-call-check-args (args
                               (evfn symbolp)
                               (arglist-term pseudo-termp)
                               (alist-var pseudo-termp))
  (b* (((when (atom args)) t)
       (form1 (car args))
       ((unless-match form1
                      ((:! evfn) (car (:! arglist-term)) (:! alist-var)))
        nil))
    (ev-of-call-check-args (cdr args) evfn `(cdr ,arglist-term) alist-var))
  ///
  (defthm ev-of-call-check-args-correct
    (implies (and (ev-of-call-check-args args evfn arglist-term alist-var)
                  (not (equal evfn 'quote)))
             (equal (evmeta-ev-lst args a)
                    (evmeta-ev-lst (ev-of-arglist
                                    (len args)
                                    evfn
                                    (evmeta-ev arglist-term a)
                                    (evmeta-ev alist-var a))
                                   nil)))
    :hints(("Goal" :in-theory (enable ev-of-arglist evmeta-ev-of-fncall-args)))))
         

(define check-ev-of-call ((evfn symbolp)
                          (fn symbolp)
                          (arity natp)
                          (name symbolp)
                          (world plist-worldp))
  (b* ((form (meta-extract-formula-w name world))
       ((unless-match form
                      (IMPLIES (IF (CONSP X)
                                   (EQUAL (CAR X) '(:! fn))
                                   'NIL)
                               (EQUAL ((:! evfn) X A)
                                      ((:! fn) . (:? args)))))
        nil))
    (and (eql (mbe :logic (nfix arity) :exec arity)
              (len args))
         (ev-of-call-check-args args evfn '(cdr x) 'a)))
  ///
  (defthm check-ev-of-call-correct
    (implies (and (check-ev-of-call evfn fn arity name (w state))
                  (consp (evmeta-ev x1 a))
                  (equal (car (evmeta-ev x1 a)) fn)
                  (not (equal fn 'quote))
                  (evmeta-ev-meta-extract-global-facts)
                  (not (equal evfn 'quote)))
             (equal (evmeta-ev (list evfn x1 a1) a)
                    (evmeta-ev (cons fn
                                     (ev-of-arglist (nfix arity) evfn
                                                    (cdr (evmeta-ev x1 a))
                                                    (evmeta-ev a1 a)))
                               a)))
    :hints (("goal" :use ((:instance evmeta-ev-meta-extract-formula
                           (name name)
                           (st state)
                           (a `((x . ,(evmeta-ev x1 a))
                                (a . ,(evmeta-ev a1 a))))))
             :in-theory (e/d (evmeta-ev-of-fncall-args)
                             (evmeta-ev-meta-extract-formula)))))

  (assert-event (check-ev-of-call 'evmeta-ev 'synp 3 'evmeta-ev-of-synp-call (w state))))

(define check-ev-of-call-weak ((evfn symbolp)
                               (fn symbolp)
                               (name symbolp)
                               (world plist-worldp))
  (b* ((form (meta-extract-formula-w name world))
       ((unless-match form
                      (IMPLIES (IF (CONSP X)
                                   (EQUAL (CAR X) '(:! fn))
                                   'NIL)
                               (EQUAL ((:! evfn) X A)
                                      (:? rhs))))
        nil))
    rhs)
  ///
  (defthm check-ev-of-call-weak-correct
    (implies (and (check-ev-of-call-weak evfn fn name (w state))
                  (consp (evmeta-ev x1 a))
                  (equal (car (evmeta-ev x1 a)) fn)
                  (not (equal fn 'quote))
                  (evmeta-ev-meta-extract-global-facts)
                  (not (equal evfn 'quote)))
             (equal (evmeta-ev (list evfn x1 a1) a)
                    (evmeta-ev `((lambda (x a) ,(check-ev-of-call-weak evfn fn name (w state)))
                                 ,x1 ,a1) a)))
    :hints (("goal" :use ((:instance evmeta-ev-meta-extract-formula
                           (name name)
                           (st state)
                           (a `((x . ,(evmeta-ev x1 a))
                                (a . ,(evmeta-ev a1 a))))))
             :in-theory (e/d (evmeta-ev-of-fncall-args)
                             (evmeta-ev-meta-extract-formula)))))

  (assert-event (check-ev-of-call-weak 'evmeta-ev 'cons-with-hint 'evmeta-ev-of-cons-with-hint-call (w state))))





(defun is-n-cdrs-of-x (n term x)
  (if (zp n)
      (eq term x)
    (case-match term
      (('cdr inner)
       (is-n-cdrs-of-x (1- n) inner x)))))

(defun list-of-ev-apps-p (lst evfn index x)
  (if (atom lst)
      (eq lst nil)
    (let ((first (car lst)))
      (case-match first
        ((!evfn ('car n-cdrs-of-x) 'a)
         (and (is-n-cdrs-of-x (1+ index) n-cdrs-of-x x)
              (list-of-ev-apps-p (cdr lst) evfn (1+ index) x)))))))

(defun ev-collect-apply-lemmas1 (lemmas evfn evlstfn)
  (if (atom lemmas)
      nil
    (b* ((rule (car lemmas))
         (hyps (access rewrite-rule rule :hyps))
         (equiv (access rewrite-rule rule :equiv))
         (lhs (access rewrite-rule rule :lhs))
         (rhs (access rewrite-rule rule :rhs))
         (rune (access rewrite-rule rule :rune))
         (aggregate (list hyps rhs))
         (rest (ev-collect-apply-lemmas1 (cdr lemmas) evfn evlstfn)))
      (if (eq equiv 'equal)
          (case-match lhs
            ((!evfn . '(x a))
             (case-match aggregate
               ;; constraint 0: ev-expand-fncall
               (('((consp  x)
                   (synp 'nil '(syntaxp (not (equal a ''nil)))
                         '(if (not (equal a ''nil)) 't 'nil))
                   (not (equal (car x) 'quote)))
                 (!evfn ('cons '(car x)
                               ('kwote-lst (!evlstfn . '((cdr x) a))))
                        ''nil))
                (hons-acons :expand-fncall rune rest))

               ;; constraint 1: ev-lookup-var
               (('((symbolp x))
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced assoc-eq by assoc-equal).]
                 '(if x (cdr (assoc-equal x a)) 'nil))
                (hons-acons :lookup-var rune rest))

               ;; constraint 2: ev-quote
               (('((consp x) (equal (car x) 'quote))
                 '(car (cdr x)))
                (hons-acons :quote rune rest))

               ;; constraint 3: ev-lambda
               (('((consp x) (consp (car x)))
                 (!evfn '(car (cdr (cdr (car x))))
                        ('pairlis$ '(car (cdr (car x)))
                                   (!evlstfn . '((cdr x) a)))))
                (hons-acons :lambda rune rest))

               ;; constraints 6+: ev-function
               ;; special case 1: return-last
               (((('consp 'x) ('equal ('car 'x) ''return-last))
                 (!evfn . '((car (cdr (cdr (cdr x)))) a)))
                (hons-acons 'return-last (cons 3 rune)
                            rest))

               ;; special case 2: mv-list
               (((('consp 'x) ('equal ('car 'x) ''mv-list))
                 (!evfn . '((car (cdr (cdr x))) a)))
                (hons-acons 'mv-list (cons 2 rune)
                            rest))

               ;; special case 3: cons-with-hint
               (((('consp 'x) ('equal ('car 'x) ''cons-with-hint))
                 ('cons (!evfn . '((car (cdr x)) a))
                       (!evfn . '((car (cdr (cdr x))) a))))
                (hons-acons 'cons-with-hint (cons 2 rune)
                            rest))

               (((('consp 'x) ('equal ('car 'x) ('quote fn)))
                 (fn . list-of-ev-apps))
                (if (list-of-ev-apps-p list-of-ev-apps evfn 0 'x)
                    (hons-acons fn (cons (len list-of-ev-apps) rune)
                                rest)
                  rest))

               (& rest)))

            ;; constraint 4: evlst-atom
            ((!evlstfn . '(x-lst a))
             (case-match aggregate
               (('((not (consp x-lst)))
                 ''nil)
                (hons-acons :lst-atom rune rest))
               (('((consp x-lst))
                 ('cons (!evfn . '((car x-lst) a))
                        (!evlstfn . '((cdr x-lst) a))))
                (hons-acons :lst-cons rune rest))
               (& rest)))

            (& rest))
        rest))))

(defun ev-collect-apply-lemmas (evfn evlstfn world)
  (ev-collect-apply-lemmas1
   (append (fgetprop evfn 'lemmas nil world)
           (fgetprop evlstfn 'lemmas nil world))
   evfn evlstfn))



(defthmd evmeta-ev-of-fncall-args-even-if-alist-is-nil
  (implies (and (syntaxp (not (and (consp args) (eq (car args) 'kwote-lst))))
                (not (equal fn 'quote)))
           (equal (evmeta-ev (cons fn args) a)
                  (evmeta-ev (cons fn (kwote-lst (evmeta-ev-lst args a))) nil)))
  :hints(("Goal" :in-theory (enable evmeta-ev-of-fncall-args))))


(defthmd kwote-lst-of-cons
  (equal (kwote-lst (cons a b))
         (cons (kwote a) (kwote-lst b))))

(defconst *def-evaluator-expander-theory*
  '((:DEFINITION KWOTE)
    (:DEFINITION NFIX)
    (:DEFINITION SYNP)
    (:DEFINITION subst-tree)
    (:EXECUTABLE-COUNTERPART EQUAL)
    (:EXECUTABLE-COUNTERPART KWOTE-LST)
    (:executable-counterpart match-tree-binder-p)
    (:REWRITE CAR-CONS)
    (:REWRITE CDR-CONS)
    (:REWRITE CHECK-EV-OF-CALL-CORRECT)
    (:REWRITE CHECK-EV-OF-CALL-WEAK-CORRECT)
    (:REWRITE EVMETA-EV-LST-OF-ATOM)
    (:REWRITE EVMETA-EV-LST-OF-CONS)
    (:REWRITE EVMETA-EV-LST-OF-EV-OF-ARGLIST-SYMB)
    (:REWRITE EVMETA-EV-OF-CONS-CALL)
    (:rewrite evmeta-ev-of-match-tree)
    (:rewrite evmeta-ev-of-lambda)
    (:REWRITE EVMETA-EV-OF-FNCALL-ARGS)
    (:REWRITE EVMETA-EV-OF-QUOTE)
    (:REWRITE KWOTE-LST-OF-CONS)
    (:rewrite not-quote-by-match-tree-restrictions)
    (:executable-counterpart intersectp-equal)
    (:executable-counterpart match-tree-restrictions)
    (:TYPE-PRESCRIPTION CHECK-EV-OF-CALL)
    (:TYPE-PRESCRIPTION EV-OF-ARGLIST-SYMB)
    (:TYPE-PRESCRIPTION LEN)))

(defconst *def-evaluator-expander-guard-theory*
  '((:COMPOUND-RECOGNIZER NATP-COMPOUND-RECOGNIZER)
    (:DEFINITION EQ)
    (:DEFINITION HONS-GET)
    (:DEFINITION KWOTE)
    (:DEFINITION STATE-P)
    (:EXECUTABLE-COUNTERPART EQUAL)
    (:EXECUTABLE-COUNTERPART CAR)
        (:EXECUTABLE-COUNTERPART CDR)
        (:EXECUTABLE-COUNTERPART CONSP)
        (:EXECUTABLE-COUNTERPART EQLABLEP)
        (:EXECUTABLE-COUNTERPART IF)
        (:EXECUTABLE-COUNTERPART MATCH-TREE-BINDERS)
        (:EXECUTABLE-COUNTERPART MEMBER-EQUAL)
        (:executable-counterpart intersectp-equal)
        (:executable-counterpart match-tree-restrictions)
        (:EXECUTABLE-COUNTERPART NOT)
        (:EXECUTABLE-COUNTERPART SYMBOL-ALISTP)
        (:REWRITE MATCH-TREE-BINDERS-BOUND)
        (:REWRITE SYMBOL-ALISTP-MATCH-TREE)
        (:rewrite symbolp-by-match-tree-restrictions)
    (:rewrite assoc-eql-exec-is-assoc-equal)
    (:REWRITE PLIST-WORLDP-W-STATE)
    (:TYPE-PRESCRIPTION EV-OF-ARGLIST-SYMB)
    (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL)
    (:TYPE-PRESCRIPTION LEN)
    (:TYPE-PRESCRIPTION STATE-P1)))



(defconst *def-evaluator-expander-form*
  '(progn
     (make-event
      `(defconst thm-alist-const
         ',(ev-collect-apply-lemmas 'evfn nil (w state))))



     (define metafn (x mfc state)
       (declare (ignorable mfc))
       :guard-hints (("goal" :in-theory *def-evaluator-expander-guard-theory*)
                     ;; (and stable-under-simplificationp
                     ;;      '(:in-theory (Enable)))
                     )
       (b* (((unless-match x (evfn (:? form) (:? a))) x)
            ((mv fn ?args)
             (b* (((when-match form
                               (cons '(:?F fn) (:? args)))
                   (mv fn args))
                  ((when-match form '((:?F fn) . (:? args)))
                   (mv fn (kwote args))))
               (mv nil nil))
             
                               
             ;; (case-match x
             ;;   (('evfn ('cons ('quote fn) args) a)
             ;;    (mv fn args a))
             ;;   (('evfn ('quote (fn . args)) a)
             ;;    (mv fn (kwote args) a))
             ;;   (& (mv nil nil nil)))
             )
            ((unless fn) x)
            ;; ((unless (and fn (symbolp fn) (not (eq fn 'quote)))) x)
            (pair (hons-get fn thm-alist-const))
            ((unless (and pair
                          (consp (cdr pair))
                          (consp (cddr pair))
                          (consp (cdddr pair))
                          (symbolp (caddr (cdr pair)))))
             x)
            (arity (len (getpropc fn 'formals t (w state))))
            ((unless (check-ev-of-call 'evfn fn arity (caddr (cdr pair)) (w state)))
             (b* ((rhs (check-ev-of-call-weak 'evfn fn (caddr (cdr pair)) (w state)))
                  ((unless rhs) x))
               `((lambda (x a) ,rhs) ,form ,a))))
         (cons fn (ev-of-arglist-symb arity 'evfn args a)))
       ///
       (defthm metafn-correct
         (implies (evmeta-ev-meta-extract-global-facts)
                  (equal (evmeta-ev x a)
                         (evmeta-ev (metafn x mfc state) a)))
         :hints (("goal" :do-not-induct t
                  :in-theory (cons 'metafn *def-evaluator-expander-theory*))
                 (and stable-under-simplificationp
                      '(:in-theory (cons 'evmeta-ev-of-fncall-args-even-if-alist-is-nil
                                         (set-difference-equal *def-evaluator-expander-theory*
                                                               '((:definition kwote-lst)
                                                                 (:rewrite kwote-lst-of-cons)))))))
         :rule-classes ((:meta :trigger-fns (evfn)))
         :otf-flg t))))

(defun def-evaluator-expander-fn (evfn metafn metafn-correct thm-alist-const)
  (b* ((metafn (or metafn
                   (intern-in-package-of-symbol
                    (concatenate 'string (symbol-name evfn) "-EXPANDER")
                    evfn)))
       (metafn-correct (or metafn-correct
                           (intern-in-package-of-symbol
                            (concatenate 'string (symbol-name metafn) "-CORRECT")
                            metafn)))
       (thm-alist-const (or thm-alist-const
                            (intern-in-package-of-symbol
                             (concatenate 'string "*" (symbol-name evfn) "-THM-ALIST*")
                             evfn))))
    (sublis `((evfn . ,evfn)
              (metafn . ,metafn)
              (metafn-correct . ,metafn-correct)
              (thm-alist-const . ,thm-alist-const))
            *def-evaluator-expander-form*)))

(defmacro def-evaluator-expander (evfn &key metafn metafn-correct thm-alist-const)
  (def-evaluator-expander-fn evfn metafn metafn-correct thm-alist-const))

(local
 (progn
   (defevaluator test-ev test-ev-lst
     ((if a b c)
      (equal p q)
      (cons-with-hint x y hint))
     :namedp t)
   (encapsulate nil
     (local (in-theory nil)) ;; test whether the included hints are enough
     (def-evaluator-expander test-ev))
     
   (defthm test-ev-of-equal
     (equal (test-ev (list 'equal x y) a)
            (equal (test-ev x a) (test-ev y a)))
     :hints(("Goal" :in-theory (disable test-ev-of-equal-call))))

   (defthm test-ev-of-cons-with-hint
     (equal (test-ev (list 'cons-with-hint x y z) a)
            (cons-with-hint (test-ev x a) (test-ev y a) (test-ev z a)))
     :hints(("Goal" :in-theory (disable test-ev-of-cons-with-hint-call))))))
