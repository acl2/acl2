; Copyright (C) 2013, Regents of the University of Texas
; Written by J Moore, 6/13/01
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; All the "terms" encountered in this work are untranslated.  We nevertheless
; explore them.  We will always check that they are "deft terms" which means
; they are
; <dterm> ::= <atom> -- variables, constants, unquoted evgs like 3 and "abc" |
;             (quote x) |
;             (sym <dterm> ... <dterm>)

(include-book "xdoc/top" :dir :system)
(defxdoc dft
  :parents (defthm events)
  :short "Provide an explicit proof, for example chaining equalities"
  :long "<p>@('Dft') is a proof-checking-like macro that allows you to chain
 together equalities.  The name @('\"dft\"') is short for @('\"defthm\"').  In
 the @(see community-books) see @('books/misc/dft-ex.lisp') for some
 examples.</p>

 <p>This tool has not been used in big proofs and probably can be improved
 quite a bit.  The author encourages users to build improved versions.</p>")

(defmacro enable-disable (a b)
  `(set-difference-theories (enable ,@a) ',b))

(mutual-recursion

(defun undeft-termp (x)
  (declare (xargs :mode :program))
  (cond
   ((atom x) nil)
   ((not (true-listp x))
    `(er soft 'deft
         "Untranslated terms encountered by DEFT must be true-lists, but ~p0 ~
          is not."
         ',x))
   ((eq (car x) 'quote)
    (cond ((= (length x) 2) nil)
          (t `(er soft 'deft
                  "QUOTEd terms such as ~p0 must have length 2."
                  ',x))))
   ((or (not (symbolp (car x)))
        (member-eq (car x) '(cond let let*)))

; We list above some commonly used macros that violate the syntax of
; <dterm> above.

    `(er soft 'deft
         "We do not permit ~p0 as a function symbol."
         ',(car x)))
   (t (undeft-termp-lst (cdr x)))))

(defun undeft-termp-lst (lst)
  (declare (xargs :mode :program))
  (cond
   ((atom lst) t)
   (t (or (undeft-termp (car lst))
          (undeft-termp-lst (cdr lst)))))))

(mutual-recursion

(defun dterm-all-vars (dterm vars)
  (declare (xargs :mode :program))
  (cond
   ((atom dterm)
    (cond ((and (symbolp dterm)
                (eq (legal-variable-or-constant-namep dterm) 'variable))
           (add-to-set-eq dterm vars))
          (t vars)))
   ((eq (car dterm) 'quote) vars)
   (t (dterm-all-vars-lst (cdr dterm) vars))))

(defun dterm-all-vars-lst (lst vars)
  (declare (xargs :mode :program))
  (cond ((atom lst) vars)
        (t (dterm-all-vars-lst (cdr lst)
                               (dterm-all-vars (car lst) vars))))))

(mutual-recursion

(defun dterm-sublis (alist dterm)

; This function knows how to substitute both for vars and exprs.

  (declare (xargs :mode :program))
  (let ((pair (assoc-equal dterm alist)))
    (cond
     (pair (cdr pair))
     ((atom dterm) dterm)
     ((eq (car dterm) 'quote) dterm)
     (t (cons (car dterm) (dterm-sublis-lst alist (cdr dterm)))))))

(defun dterm-sublis-lst (alist lst)
  (declare (xargs :mode :program))
  (cond ((null lst) nil)
        (t (cons (dterm-sublis alist (car lst))
                 (dterm-sublis-lst alist (cdr lst)))))))

(defun dterm-sublis-subst-to-alist (alist subst)
  (declare (xargs :mode :program))
  (cond ((null subst) nil)
        (t (cons (cons (caar subst) (dterm-sublis alist (cadr (car subst))))
                 (dterm-sublis-subst-to-alist alist (cdr subst))))))

(defun dterm-sublis-subst (alist subst)
  (declare (xargs :mode :program))
  (let ((alist2 (dterm-sublis-subst-to-alist alist subst)))
    (pairlis$ (strip-cars alist2)
              (pairlis$ (strip-cdrs alist2) nil))))

(defun assoc-keys-other-than (lst alist)
  (declare (xargs :mode :program))
  (cond ((null alist) nil)
        ((member-eq (caar alist) lst) (assoc-keys-other-than lst (cdr alist)))
        (t (cons (caar alist) (assoc-keys-other-than lst (cdr alist))))))

(defun dterm-sublis-into-lmi (alist lmi)
  (declare (xargs :mode :program))
  (cond
   ((atom lmi) lmi)
   ((eq (car lmi) :instance)
    (list* :instance (dterm-sublis-into-lmi alist (cadr lmi))
           (dterm-sublis-subst alist (cddr lmi))))
   (t lmi)))


(defun dterm-sublis-into-use-hint (alist lst)
  (declare (xargs :mode :program))
  (cond
   ((null lst) nil)
   (t
    (cons (dterm-sublis-into-lmi alist (car lst))
          (dterm-sublis-into-use-hint alist (cdr lst))))))

(defun convert-keyword-alist-to-alist (bindings keyword-alist)
  (declare (xargs :mode :program))
  (cond ((atom keyword-alist) nil)
        (t (cons (cons (car keyword-alist)
                       (cond ((eq (car keyword-alist) :use)
                              (cond ((and (consp (cadr keyword-alist))
                                          (eq (car (cadr keyword-alist)) :instance))
                                     (dterm-sublis-into-lmi bindings (cadr keyword-alist)))
                                    (t (dterm-sublis-into-use-hint bindings
                                                                   (cadr keyword-alist)))))
                             (t (cadr keyword-alist))))
                 (convert-keyword-alist-to-alist bindings (cddr keyword-alist))))))

(defun negate-dterm (dterm)
  (declare (xargs :mode :program))
  (cond ((equal dterm t) nil)
        ((equal dterm nil) t)
        ((and (consp dterm)
              (eq (car dterm) 'not))
         (cadr dterm))
        (t (list 'not dterm))))

(defun conjoin-dterms (dterm1 dterm2)
  (declare (xargs :mode :program))
  (cond ((equal dterm1 nil) nil)
        ((equal dterm2 nil) nil)
        ((equal dterm1 t) dterm2)
        ((equal dterm2 t) dterm1)
        (t (let ((lst1 (case-match dterm1
                                   (('and . terms)
                                    terms)
                                   (& (list dterm1))))
                 (lst2 (case-match dterm2
                                   (('and . terms)
                                    terms)
                                   (& (list dterm2)))))
             (cons 'and (append lst1 lst2))))))

(defun implicate-dterms (dhyp dconcl)
  (declare (xargs :mode :program))
  (cond ((eq dhyp t) dconcl)
        (t (case-match dconcl
                       (('implies hyps concl)
                        (list 'implies
                              (conjoin-dterms hyps dhyp)
                              concl))
                       (& (list 'implies dhyp dconcl))))))

(defun dterm-hyp (dterm)
  (declare (xargs :mode :program))
  (case-match dterm
              (('implies hyp &) hyp)
              (& t)))

(defun dterm-concl (dterm)
  (declare (xargs :mode :program))
  (case-match dterm
              (('implies & concl) concl)
              (& dterm)))

(defun apply-proof-step (dhyp1 dterm)
  (declare (xargs :mode :program))
  (let ((dhyp2 (dterm-hyp dterm))
        (dconcl (dterm-concl dterm)))
    (case-match dhyp1
                (('equal lhs rhs)
                 (let ((dconcl2 (dterm-sublis (list (cons lhs rhs)) dconcl)))
                   (cond ((equal dconcl2 dconcl)
                          (implicate-dterms (conjoin-dterms dhyp2 dhyp1) dconcl))
                         (t (implicate-dterms dhyp2 dconcl2)))))
                (& (implicate-dterms (conjoin-dterms dhyp2 dhyp1) dconcl)))))

(defun pairlis1 (x1 lst)

; Make an alist pairing x1 with each element of lst.

  (declare (xargs :mode :program))
  (cond ((null lst) nil)
        (t (cons (cons x1 (car lst))
                 (pairlis1 x1 (cdr lst))))))

(defun generalization-phrasep (all-vars bindings phrase new-hyps alist)

; We parse phrase into repetitions of
; `expr TO var'
; `expr TO var WHERE hyp' ;;; hyp is `about' var but must be proved of `expr'
; possibly separated by `and'.

; We return (mv er-form new-hyps alist), where new-hyps is a list of hyps
; (about the exprs, not the vars) to be proved and alist is a substitution
; mapping the vars to the exprs.

  (declare (xargs :mode :program))
  (cond
   ((atom phrase)
    (mv nil
        (dterm-sublis-lst alist (reverse new-hyps))
        (reverse alist)))
   ((keywordp (car phrase))
    (mv `(er soft 'deft
             "It is illegal to put a hint inside a generalization step.  The ~
              usual intent is to aid the proof of a restriction on some ~
              variable, as in (GENERALIZE expr TO var WHERE (p var) ~p0...).  ~
              The proper way to achieve this is to OBSERVE that expr has the ~
              desired property before its generalization to var, as in ~
              (OBSERVE (p expr) ~p0 ...) (GENERALIZE expr TO ar)."
             ',(car phrase))
        nil nil))
   ((eq (car phrase) 'and)
    (generalization-phrasep all-vars bindings (cdr phrase) new-hyps alist))
   ((and (consp (cdr phrase))
         (eq (cadr phrase) 'to)
         (consp (cddr phrase))
         (symbolp (caddr phrase))
         (not (member-eq (caddr phrase) all-vars)))
    (let* ((expr (dterm-sublis bindings (car phrase)))
           (var (caddr phrase))
           (hyp (if (and (consp (cdddr phrase))
                         (eq (cadddr phrase) 'where)
                         (car (cddddr phrase)))
                    (dterm-sublis bindings (car (cddddr phrase)))
                  nil))
           (phrase1 (if hyp (cdr (cddddr phrase)) (cdddr phrase))))
      (generalization-phrasep (cons var all-vars) bindings phrase1
                              (if hyp (cons hyp new-hyps) new-hyps)
                              (cons (cons var expr) alist))))
   (t (mv `(er soft 'deft
               "Illegal GENERALIZATION step.  We expected to see repetitions ~
                of the phrases `expr TO var' or `expr TO var WHERE ~
                restriction', possibly separated by `and', where var is a ~
                variable not previously involved in the problem; ~p0 cannot be ~
                parsed that way."
               ',phrase)
          nil nil))))

(mutual-recursion

(defun translate-proof1 (dname dterm proof addr bindings
                               revents otherwise-term xhyp cnames
                               use-hint consider-dterm thm-pair)
  (declare (xargs :mode :program))
  (cond
   ((null proof)
    (mv-let (er-form event addr1)
            (deft-fn dname
              dterm
              addr
              bindings
              `((:use . ,(revappend cnames (reverse use-hint)))
                (:in-theory . 'nil))
              nil
              :default
              nil)
            (cond
             (er-form (mv er-form nil nil))
             (t (mv nil
                    (cons event revents)
                    addr1)))))
   (t
    (let ((proof-step (car proof)))
      (case-match
       proof-step
       (('case test . subproof)
        (let* ((case-name (packn `(* ,addr)))
               (test (if (eq test 'otherwise)
                         otherwise-term
                       (dterm-sublis bindings test)))
               (case-dterm (implicate-dterms test dterm)))
          (mv-let
           (er-form revents1 addr1)
           (translate-proof1
            case-name
            case-dterm
            (if (member-equal subproof '((easy)(trivial)))
                nil
              subproof)
            (1+ addr)
            bindings
            revents t
            (dterm-hyp case-dterm)
            nil use-hint nil nil)
           (cond
            (er-form (mv er-form nil nil))
            (t (translate-proof1
                dname
                dterm
                (cdr proof)
                addr1
                bindings
                revents1
                (conjoin-dterms
                 otherwise-term
                 (negate-dterm test))
                xhyp
                (cons case-name cnames)
                use-hint nil nil))))))
       (('let var & expr)
        (translate-proof1
         dname dterm (cdr proof) addr
         (cons (cons var (dterm-sublis bindings expr)) bindings)
         revents otherwise-term xhyp cnames use-hint consider-dterm
         thm-pair))
       (('Theorem dthm . h-alist)
        (let* ((theorem-name (packn `(* ,addr)))
               (pass-bindings-downp (and (consp h-alist)
                                         (eq (car h-alist) :pass-bindings-downp)))
               (h-alist (if pass-bindings-downp (cdr h-alist) h-alist)))
          (mv-let
           (er-form event addr1)
           (deft-fn theorem-name dthm (1+ addr)
             (if pass-bindings-downp bindings nil)
             (convert-keyword-alist-to-alist bindings h-alist)
             nil
             :default
             nil)
           (cond
            (er-form (mv er-form nil nil))
            (t (translate-proof1
                dname
                dterm
                (cdr proof)
                addr1
                bindings
                (cons event revents)
                otherwise-term
                xhyp
                cnames
                use-hint
                nil
                (cons theorem-name dthm)))))))
       (('Instantiate-just-proved-theorem . rest)
        (translate-proof1 dname dterm
                          (cons (cons 'Instantiate rest) (cdr proof))
                          addr bindings revents otherwise-term xhyp cnames use-hint
                          consider-dterm thm-pair))
       (('Instantiate . subst)
        (cond
         (thm-pair
          (let* ((alist (dterm-sublis-subst-to-alist bindings subst))
                 (subst (pairlis$ (strip-cars alist)
                                  (pairlis$ (strip-cdrs alist) nil)))
                 (dthm-inst (dterm-sublis alist (cdr thm-pair))))
            (translate-proof1
             dname
             dterm
             (cdr proof)
             addr
             bindings
             revents
             otherwise-term
             (conjoin-dterms xhyp dthm-inst)
             cnames
             (cons `(:instance ,(car thm-pair)
                               ,@subst)
                   use-hint)
             nil
             thm-pair)))
         (t (mv `(er soft 'deft
                     "It is illegal to use INSTANTIATE except when it ~
                      immediately follows THEOREM or another INSTANTIATE.")
                 nil nil))))
       (('Generalize . generalization-phrase)
        (mv-let
         (er-form new-hyps alist)
         (generalization-phrasep
          (dterm-all-vars dterm nil)
          bindings generalization-phrase nil nil)
         (cond
          (er-form (mv er-form nil nil))
          (t
           (translate-proof1
            dname dterm
            `(,@(pairlis1 'Observe (pairlis-x2 new-hyps nil))
              (Theorem
               ,(dterm-sublis
                 (pairlis$ (strip-cdrs alist) (strip-cars alist))
                 (implicate-dterms
                  (cond ((null new-hyps) xhyp)
                        ((null (cdr new-hyps))
                         (conjoin-dterms xhyp (car new-hyps)))
                        (t (conjoin-dterms xhyp (cons 'and new-hyps))))
                  (dterm-concl dterm)))
               :pass-bindings-downp
               :proof ,(cdr proof))
              (Instantiate
               ,@(pairlis$ (strip-cars alist)
                           (pairlis-x2 (strip-cdrs alist) nil))))
            addr bindings revents otherwise-term xhyp cnames use-hint
            consider-dterm thm-pair)))))
       (('So-it-suffices-to-prove . rest)
        (translate-proof1 dname dterm
                          (cons (cons 'so rest) (cdr proof))
                          addr bindings revents otherwise-term xhyp cnames use-hint
                          consider-dterm thm-pair))
       (('So new-dterm)
        (let ((new-dterm (dterm-sublis bindings new-dterm))
              (goal-name-suff (packn `(* ,addr -sufficient)))
              (goal-name (packn `(* ,addr))))
          (mv-let (er-form event addr1)
                  (deft-fn goal-name-suff
                    (implicate-dterms new-dterm dterm)
                    (+ 2 addr)
                    bindings
                    `((:use . ,(revappend cnames (reverse use-hint)))
                      (:in-theory . 'nil))
                    nil
                    :default
                    nil)
                  (cond
                   (er-form (mv er-form nil nil))
                   (t (mv-let
                       (er-form revents addr2)
                       (translate-proof1
                        goal-name
                        new-dterm
                        (cdr proof)
                        addr1
                        bindings
                        (cons event revents)
                        otherwise-term
                        (dterm-hyp new-dterm)
                        nil nil nil nil)
                       (cond
                        (er-form (mv er-form nil nil))
                        (t
                         (mv-let (er-form event addr3)
                                 (deft-fn dname
                                   dterm
                                   addr2
                                   bindings
                                   `((:use . (,goal-name-suff
                                              ,goal-name))
                                     (:in-theory . 'nil))
                                   nil
                                   :default
                                   nil)
                                 (cond
                                  (er-form (mv er-form nil nil))
                                  (t (mv nil
                                         (cons event revents)
                                         addr3))))))))))))
       (('Observe obs-dterm . h-alist)
        (let* ((obs-dterm (dterm-sublis bindings obs-dterm))
               (step-name (packn `(* ,addr)))
; See translate-proof2 for an explanation of this next part.
               (pass-consider-dtermp
                (and (consp h-alist)
                     (eq (car h-alist) :pass-consider-dtermp)))
               (h-alist (if pass-consider-dtermp (cdr h-alist) h-alist)))
          (mv-let
           (er-form event addr1)
           (deft-fn step-name
             (implicate-dterms xhyp obs-dterm)
             (1+ addr)
             bindings
             (convert-keyword-alist-to-alist bindings h-alist)
             nil
             :default
             nil)
           (cond
            (er-form (mv er-form nil nil))
            (t (translate-proof1
                dname dterm
                (cdr proof)
                addr1
                bindings
                (cons event revents)
                otherwise-term
                (conjoin-dterms xhyp obs-dterm)
                cnames
                (cons step-name use-hint)
                (if pass-consider-dtermp consider-dterm nil)
                nil))))))
       (('consider dterm1)
        (translate-proof1
         dname dterm (cdr proof) addr bindings
         revents otherwise-term xhyp cnames use-hint
         (dterm-sublis bindings dterm1)
         nil))
       (('= dterm1 . h-alist)
        (translate-proof2 '= 'equal dterm1 h-alist
                          dname dterm proof addr bindings revents
                          otherwise-term xhyp cnames use-hint
                          consider-dterm thm-pair))
       (('<-> dterm1 . h-alist)
        (translate-proof2 '<-> 'iff dterm1 h-alist
                          dname dterm proof addr bindings revents
                          otherwise-term xhyp cnames use-hint
                          consider-dterm thm-pair))
       (('-> dterm1 . h-alist)
        (translate-proof2 '-> 'implies dterm1 h-alist
                          dname dterm proof addr bindings revents
                          otherwise-term xhyp cnames use-hint
                          consider-dterm thm-pair))
       (('< dterm1 . h-alist)
        (translate-proof2 '< '< dterm1 h-alist
                          dname dterm proof addr bindings revents
                          otherwise-term xhyp cnames use-hint
                          consider-dterm thm-pair))
       (('<= dterm1 . h-alist)
        (translate-proof2 '<= '<= dterm1 h-alist
                          dname dterm proof addr bindings revents
                          otherwise-term xhyp cnames use-hint
                          consider-dterm thm-pair))
       (('> dterm1 . h-alist)
        (translate-proof2 '> '> dterm1 h-alist
                          dname dterm proof addr bindings revents
                          otherwise-term xhyp cnames use-hint
                          consider-dterm thm-pair))
       (('>= dterm1 . h-alist)
        (translate-proof2 '>= '>= dterm1 h-alist
                          dname dterm proof addr bindings revents
                          otherwise-term xhyp cnames use-hint
                          consider-dterm thm-pair))
       (& (mv `(er soft 'deft
                   "Unrecognized proof step, ~p0."
                   ',proof-step)
              nil nil)))))))

(defun translate-proof2 (symbol fn dterm1 h-alist
                                dname dterm proof addr bindings revents
                                otherwise-term xhyp cnames use-hint
                                consider-dterm thm-pair)
  (declare (xargs :mode :program))
  (declare (ignore thm-pair))
  (cond
   (consider-dterm
    (let ((dterm1 (dterm-sublis bindings dterm1)))
      (translate-proof1
       dname dterm

; The :pass-consider-dtermp hack allows us to invoke Observe but tell it to pass
; the consider-dterm unchanged.  Normally, Observe nulls out the
; consider-dterm.  We pass in the instantiated dterm1 as the new consider-dterm
; and arrange for it to be passed on.

       (cons `(Observe (,fn ,consider-dterm ,dterm1)
                       :pass-consider-dtermp . ,h-alist)
             (cdr proof))
       addr
       bindings revents otherwise-term xhyp cnames use-hint
       dterm1
       nil)))
   (t (mv `(er soft 'deft
               "The ~p0 relation, as in (~p0 ~p1 ...), may be used only immediately after CONSIDER ~
                or another ~p0 or similar relation."
               ',symbol
               ',dterm1)
          nil nil))))

(defun translate-proof
  (name dterm proof addr bindings rule-classes otf-flg doc)
  (declare (xargs :mode :program))
  (mv-let (er-form revents addr)
          (translate-proof1 name
                            dterm
                            proof
                            addr
                            bindings
                            nil t
                            (dterm-hyp dterm)
                            nil nil nil nil)
          (cond
           (er-form (mv er-form nil nil))
           (t (let* (

; The first element of revents -- the last to be generated -- is
; of the form (defthm name dterm :rule-classes nil :hints hints ...)
; and we are merely interested in the hints.

                     (hints (cadr (assoc-keyword :hints (cdddr (car revents)))))
                     (main
                      `(defthm ,name ,dterm
                         ,@(and doc `(:doc ,doc))
                         ,@(and (not (eq otf-flg :default))
                                `(:otf-flg ,otf-flg))
                         ,@(and (not (eq rule-classes :default))
                                `(:rule-classes ,rule-classes))
                         ,@(and hints
                                `(:hints ,hints))))
                     (local-events (reverse (cdr revents))))
                (cond
                 ((null local-events)
                  (mv nil main addr))
                 ((null (cdr local-events))
                  (mv nil
                      `(encapsulate nil (local ,(car local-events)) ,main)
                      addr))
                 (t (mv nil
                        `(encapsulate nil
                                      (local (encapsulate nil ,@local-events))
                                      ,main)
                        addr))))))))

(defun deft-fn (name term addr bindings h-alist rule-classes otf-flg doc)
  (declare (xargs :mode :program))
  (let ((proof (cdr (assoc-eq :proof h-alist))))
    (cond
     (proof
      (let ((bad (assoc-keys-other-than '(:proof) h-alist)))
        (cond
         (bad
          (mv `(er soft 'deft
                   "It is illegal to supply both a :PROOF hint and any other ~
                    proof-time advice.  You supplied ~&1."
                   ',bad)
              nil nil))
         (t (translate-proof name term
                             proof
                             addr
                             bindings
                             rule-classes otf-flg doc)))))
     (t (let ((bad (assoc-keys-other-than
                    '(:proof     ;;; if it was provided, it was nil
                      :in-theory
                      :enable
                      :disable
                      :use
                      :expand
                      :cases
                      :induct
                      :by
                      :restrict
                      :do-not
                      :do-not-induct
                      :hints)
                    h-alist))
              (in-theory (cdr (assoc :in-theory h-alist)))
              (enable (cdr (assoc :enable h-alist)))
              (disable (cdr (assoc :disable h-alist)))
              (use (cdr (assoc :use h-alist)))
              (expand (cdr (assoc :expand h-alist)))
              (cases (cdr (assoc :cases h-alist)))
              (induct (cdr (assoc :induct h-alist)))
              (by (cdr (assoc :by h-alist)))
              (restrict (cdr (assoc :restrict h-alist)))
              (do-not (cdr (assoc :do-not h-alist)))
              (do-not-induct (cdr (assoc :do-not-induct h-alist)))
              (hints (cdr (assoc :hints h-alist))))
          (cond
           (bad
            (mv `(er soft 'deft
                     "Unrecognized keyword argument~#0~[~/s~], ~&0."
                     ',(reverse bad))
                nil nil))
           ((and (or (assoc-equal "Goal" hints)
                     (assoc-equal "goal" hints))
                 (or in-theory enable disable use expand cases induct by
                     restrict do-not do-not-induct))
            (mv '(er soft 'deft
                     "It is not permitted to supply both a :HINTS argument for ~
                      \"Goal\" and any of :IN-THEORY, :ENABLE, :DISABLE, :USE, ~
                      :EXPAND, :CASES, :INDUCT, :RESTRICT, :BY, :DO-NOT, or ~
                      :DO-NOT-INDUCT (which are implicitly for \"Goal\") ~
                      because DEFT does not know how to combine hints.")
                nil nil))
           ((and in-theory
                 (or enable disable))
            (mv '(er soft 'deft
                     "It is not permitted to supply both an :IN-THEORY ~
                      argument and either of :ENABLE or :DISABLE, because DEFT ~
                      does not know how to combine theory hints.")
                nil nil))
           (t (mv
               nil
               `(defthm ,name ,term
                  ,@(and doc `(:doc ,doc))
                  ,@(and (not (eq otf-flg :default)) `(:otf-flg ,otf-flg))
                  ,@(and (not (eq rule-classes :default))
                         `(:rule-classes ,rule-classes))
                  ,@(and hints
                         (not (or in-theory enable disable
                                  use expand cases restrict
                                  induct by do-not do-not-induct))
                         `(:hints ,hints))
                  ,@(and (or in-theory enable disable use expand cases
                             restrict induct by do-not do-not-induct)
                         `(:hints
                           (("Goal"
                             ,@(and in-theory `(:in-theory ,in-theory))
                             ,@(and (or enable disable)
                                    `(:in-theory
                                      (enable-disable
                                       (,@(cond
                                           ((null enable) nil)
                                           ((or (atom enable)
                                                (keywordp (car enable)))
                                            (list enable))
                                           (t enable)))
                                       (,@(cond
                                           ((null disable) nil)
                                           ((or (atom disable)
                                                (keywordp (car disable)))
                                            (list disable))
                                           (t disable))))))
                             ,@(and use `(:use ,use))
                             ,@(and expand `(:expand ,expand))
                             ,@(and cases `(:cases ,cases))
                             ,@(and restrict `(:restrict ,restrict))
                             ,@(and induct `(:induct ,induct))
                             ,@(and by `(:by ,by))
                             ,@(and do-not `(:do-not ,do-not))
                             ,@(and do-not-induct
                                    `(:do-not-induct ,do-not-induct)))
                            ,@hints))))
               addr))))))))

)

(defun delete-null-cdrs (alist)
  (declare (xargs :mode :program))
  (cond ((atom alist) nil)
        ((null (cdar alist)) (delete-null-cdrs (cdr alist)))
        (t (cons (car alist) (delete-null-cdrs (cdr alist))))))

(defmacro dft (&whole event-form name term
                     &key proof
                     doc
                     (rule-classes ':default)
                     (otf-flg ':default)
                     in-theory enable disable
                     use expand cases induct by restrict
                     do-not do-not-induct hints)
  (declare (ignore event-form))
  (mv-let (er-form event addr)
          (deft-fn name term
            1
            nil
            (delete-null-cdrs
             `((:proof . ,proof)
               (:in-theory . ,in-theory)
               (:enable . ,enable)
               (:disable . ,disable)
               (:use . ,use)
               (:expand . ,expand)
               (:cases . ,cases)
               (:induct . ,induct)
               (:by . ,by)
               (:restrict . ,restrict)
               (:do-not . ,do-not)
               (:do-not-induct . ,do-not-induct)
               (:hints . ,hints)))
            rule-classes
            otf-flg
            doc)
          (declare (ignore addr))
          (cond (er-form er-form)
                (t event))))
