

(in-package "ACL2")



(defttag meta-cheat)

;; EXPERIMENTAL, LIKELY UNSOUND (though not intentionally).

;; NOTE:  Yes, this IS UNSOUND -- for example, mfc- functions may force
;; hypotheses, in which case we will suppose that they were satisfied, but they
;; won't be actually relieved later as they should be.  Hopefully this can be
;; corrected.


;; The "cheat" is that you're allowed to assume some extra things when proving
;; the correcthess theorem for a :meta rule.  (We intend to extend this to
;; clause-processors, but have not yet.)  For :meta,
;; there are two extra optional hypotheses we allow, making the most generic
;; form of the theorem as follows:
;; (implies (and (pseudo-termp x)
;;               (alistp a)
;;               (evl (hyp-metafunction x mfc state) a)
;;               ;; meta-cheat additions:
;;               (evl (meta-cheat-contextual-fact obj1 mfc state) a)
;;               (evl (meta-cheat-global-fact obj2 state) aa))
;;          (equiv (evl x a)
;;                 (evl (metafunction x mfc state) a)))
;; Here obj1, obj2, and aa may be arbitrary terms.  Note that this means, in
;; particular, they may be "bad-guy" defchoose functions, so that we
;; effectively may assume those hyps to be true of any obj1, obj2, and aa.

;; Explanation:  Meta-cheat-contextual-fact and meta-cheat-global-fact
;; represent various modes of access to the ACL2 prover and its database of
;; stored facts.  For example,
;;    (meta-cheat-contextual-fact :type-alist mfc state)
;; is equal to
;;    (type-alist-ok-term (mfc-type-alist mfc)).
;; Then, for example, the following is provable if the evaluator EVL supports
;; the right functions:
;; (implies (and (evl (type-alist-ok-term type-alist) a)
;;               (equal (cdr (assoc term type-alist)) *ts-negative-integer*))
;;          (and (integerp (evl term a))
;;               (< 0 (evl term a))))
;; (and other theorems for other type-specs.)  So this hypothesis allows the
;; metafunction to assume that facts looked up from the mfc-type-alist are
;; true.

;; The difference between the meta-cheat-contextual- and -global-fact functions
;; is that -contextual- is designed to return terms that are true under the
;; current rewriting context (hyps and rulers), whereas -global- returns terms
;; that are theorems, true independent of the context.  Therefore we only
;; assume -contextual-fact terms are true under the alist A, whereas for
;; -global-fact terms we may assume them true under any alist.  Both are
;; available for meta rules, whereas only the global functions will be
;; available for clause-processor rules when this addition is implemented.




;; These two functions are used by our redefinition of
;; meta-rule-hypothesis-function below.  They recognize certain hypotheses and
;; remove them so they won't cause the rule to be rejected.
(defun remove-meta-cheat-contextual-hyp (hyps ev mfc-symbol a)
  (declare (xargs :mode :program))
  (if (atom hyps)
      nil
    (let ((hyp (car hyps)))
      (case-match hyp
        ((!ev ('meta-cheat-contextual-fact & !mfc-symbol 'state) !a)
         (cdr hyps))
        (& (cons hyp
                 (remove-meta-cheat-contextual-hyp (cdr hyps) ev
                                                   mfc-symbol a)))))))

(defun remove-meta-cheat-global-hyp (hyps ev)
  (declare (xargs :mode :program))
  (if (atom hyps)
      nil
    (let ((hyp (car hyps)))
      (case-match hyp
        ((!ev ('meta-cheat-global-fact & 'state) &)
         (cdr hyps))
        (& (cons hyp
                 (remove-meta-cheat-global-hyp (cdr hyps) ev)))))))




;; NOTE: We are about to redefine the system function
;; META-RULE-HYPOTHESIS-FUNCTION from defthm.lisp in order to allow our extra
;; hyps to be used in :meta rules.  We must keep our redefinition in sync with
;; the system function.  The following make-event checks that we are up to
;; date and the system definition is the one we expect.

(local
 (progn
   (include-book "tools/bstar" :dir :system)
   ;; NOTE: We are going to redefine the system function
   ;; META-RULE-HYPOTHESIS-FUNCTION.  This form checks that the installed
   ;; system function is the one we expect.
   (make-event
    (b* ((fn 'meta-rule-hypothesis-function)
         (wrld (w state))
         (ev-wrld (decode-logical-name fn wrld))
         ((unless (and ev-wrld
                       (eq (caar ev-wrld) 'event-landmark)))
          (er soft 'meta-cheat "Checking meta-rule-hypothesis-function: no ~
                             definition found!~%"))
         (expected-definition
          '(DEFUN META-RULE-HYPOTHESIS-FUNCTION (HYP EV X A MFC-SYMBOL)
             (LET ((HYPS (FLATTEN-ANDS-IN-LIT HYP)))
                  (LET* ((REST-HYPS (REMOVE1-EQUAL (FCONS-TERM* 'PSEUDO-TERMP X)
                                                   (REMOVE1-EQUAL (FCONS-TERM* 'ALISTP A)
                                                                  HYPS)))
                         (HYP3 (CAR REST-HYPS))
                         (EXTENDED-ARGS (IF MFC-SYMBOL (CONS MFC-SYMBOL '(STATE))
                                            NIL)))
                        (COND ((NULL REST-HYPS) T)
                              (T (AND (NULL (CDR REST-HYPS))
                                      (CASE-MATCH HYP3
                                                  ((!EV (FN !X . !EXTENDED-ARGS) !A) FN)
                                                  (& NIL)))))))))
         ((when (equal (nthcdr 3 (car ev-wrld)) expected-definition))
          ;; The definition is as expected, so do nothing.
          (value '(value-triple
                   :definition-check-ok-for-meta-rule-hypothesis-function))))
      (er soft 'meta-cheat
          "Checking meta-rule-hypothesis-function: the definition appears to ~
        have changed!  Keep in sync.~%")))))

(redef+)
(defun meta-rule-hypothesis-function (hyp ev x a mfc-symbol)

; Here hyp is the hypothesis of the proposed meta rule (or, *t* if
; there is none).  We want to identify the hypothesis metafunction
; (see :DOC meta) of that rule.  We return nil if the hyp is
; unacceptable, t if there is no extra hypothesis, and otherwise the
; hypothesis function.  Note that we allow, but do not require, the
; hypotheses (pseudo-termp x) and (alistp a) to be among the
; hypotheses, in which case we delete them before returning the
; result.

; If mfc-symbol is non-nil, this is an extended metafunction and we
; insist that the hyp function be extended also.  All extended
; functions take three arguments, the term, the context, and STATE, in
; that order.  The value of mfc-symbol is the variable symbol used to
; denote the context.

  (let ((hyps (flatten-ands-in-lit hyp)))
    (let* ((rest-hyps (remove1-equal
                       (fcons-term* 'pseudo-termp x)
                       (remove1-equal (fcons-term* 'alistp a) hyps)))
;; --------- BEGIN META-CHEAT ADDITION --------------
           (rest-hyps (if mfc-symbol
                          (remove-meta-cheat-contextual-hyp rest-hyps ev mfc-symbol a)
                        rest-hyps))
           (rest-hyps (remove-meta-cheat-global-hyp rest-hyps ev))
;; ---------- END META-CHEAT ADDITION ---------------
           (hyp3 (car rest-hyps))
           (extended-args
            (if mfc-symbol (cons mfc-symbol '(STATE)) nil)))
      (cond
       ((null rest-hyps)
        t)
       (t
        (and (null (cdr rest-hyps))
             (case-match
               hyp3
               ((!ev (fn !x . !extended-args) !a)
                fn)
               (& nil))))))))

(redef-)


;; Now we define the functions META-CHEAT-CONTEXTUAL-FACT and
;; META-CHEAT-GLOBAL-FACT.


;; Meta-cheat-formula -- look up a fact by name from the state.
(verify-termination latest-body)
(verify-termination def-body)
(verify-termination body)

(defthm plist-worldp-when-state-p1
  (implies (state-p1 state)
           (plist-worldp (w state))))

(in-theory (disable state-p1 w))

(defun def-body-to-formula (fn def-body)
  (latest-body
   (fcons-term fn (access def-body def-body :formals))
   (access def-body def-body :hyp)
   (access def-body def-body :concl)))

;; kind of like FORMULA, but without the corollary support, and returns *t* if
;; none is found, and guard-verified (though uses ec-call to call
;; def-body-to-formula).
(defund meta-cheat-formula (name normalp state)
  (declare (xargs :stobjs state
                  :guard (symbolp name)))
  (let* ((wrld (w state))
         (functionp (not (eq (getprop name 'formals t 'current-acl2-world wrld)
                             t))))
    (if functionp
        (or (getprop name 'defchoose-axiom nil 'current-acl2-world wrld)
            (if normalp
                (let* ((bodies (getprop name 'def-bodies nil
                                        'current-acl2-world wrld)))
                  (and (consp bodies)
                       (ec-call (def-body-to-formula name (car bodies)))))
              (getprop name 'unnormalized-body nil 'current-acl2-world wrld))
            (er hard? 'meta-cheat-formula "Failed to look up function: ~x0 ~
                                           (normalp: ~x1)" name normalp)
            *t*)
      (or (getprop name 'theorem nil 'current-acl2-world wrld)
          *t*))))


;; Typeset-related functions.  Typespec-check checks whether X is of the given
;; typespec.  Type-alist-ok-term creates a term that says the type-alist is ok,
;; i.e. the evaluation of each term bound in the type-alist matches the typeset
;; that is claimed.

(verify-termination type-set-quote)
(verify-guards type-set-quote)

(defun typespec-check (ts x)
  (declare (xargs :guard (integerp ts)))
  (if (bad-atom x)
      (< ts 0)
    (/= 0 (logand (type-set-quote x) ts))))

;; type alist entries are of the form (term ts . ttree)
(defun type-alist-ok-term (x)
  (declare (xargs :guard t))
  (if (atom x)
      *t*
    (if (and (consp (car x))
             (consp (cdar x)))
        `(if (typespec-check ',(cadar x) ,(caar x))
             ,(type-alist-ok-term (cdr x))
           'nil)
      *nil*)))


;; Rewrite-related functions:
;; Term-subst applies a sigma to a term.

(mutual-recursion
 (defun term-subst (x al)
   (declare (xargs :guard (and (pseudo-termp x)
                               (alistp al))))
   (cond ((null x) nil)
         ((atom x)
          (let ((look (assoc-eq x al)))
            (if look
                (cdr look)
              x)))
         ((eq (car x) 'quote) x)
         (t (cons (car x) (termlist-subst (cdr x) al)))))

 (defun termlist-subst (x al)
   (declare (xargS :guard (and (pseudo-term-listp x)
                               (alistp al))))
   (if (atom x)
       x
     (cons (term-subst (car x) al)
           (termlist-subst (cdr x) al)))))



(encapsulate
  nil
  (local (defun term-ind (x list-flg)
           (declare (xargs :guard (and (if list-flg
                                           (pseudo-term-listp x)
                                         (pseudo-termp x)))))
           (if list-flg
               (if (atom x)
                   x
                 (cons (term-ind (car x) nil)
                       (term-ind (cdr x) t)))
             (if (or (atom x)
                     (eq (car x) 'quote))
                 x
               (cons (car x) (term-ind (cdr x) t))))))

  (local (defthm term-subst-identity-lemma
           (implies (atom al)
                    (if list-flg
                        (equal (termlist-subst x al) x)
                      (equal (term-subst x al) x)))
           :hints (("goal" :induct (term-ind x list-flg)))
           :rule-classes nil))

  (defthm term-subst-identity
    (implies (atom al)
             (equal (term-subst x al) x))
    :hints (("goal" :use ((:instance term-subst-identity-lemma
                           (list-flg nil))))))

  (defthm termlist-subst-identity
    (implies (atom al)
             (equal (termlist-subst x al) x))
    :hints (("goal" :use ((:instance term-subst-identity-lemma
                           (list-flg t)))))))

;; Meta-cheat-rw+-term creates a term claiming that term under alist is equiv
;; to rhs.  We have not yet implemented geneqv support so we return *t*,
;; meaning that nothing is assumed about the operation of mfc-rw+/mfc-rw when
;; equiv-info is not t, nil, or an equivalence relation.
(defun-nx meta-cheat-rw+-term (term alist equiv-info rhs state)
  (declare (xargs :stobjs state
                  :verify-guards nil))
  (let ((lhs (term-subst term alist)))
    (case equiv-info
      ((nil) `(equal ,lhs ,rhs))
      ((t)   `(iff ,lhs ,rhs))
      (otherwise
       ;; Check equivalence-relationp
       (if (symbolp equiv-info)
           (if (equivalence-relationp equiv-info (w state))
               `(,equiv-info ,lhs ,rhs)
             ;; Bad equivalence relation?
             *t*)
         ;; BOZO deal with geneqvs somehow.
         *t*)))))

;; Meta-cheat-contextual-fact: Our hack above allows us to hypothesize while
;; proving meta rules that this function always produces a term that evaluates
;; non-nil under the rewriting context where the metafunction is operating,
;; i.e. under the specific alist A for which we're proving (evl x a) = (evl
;; (metafn x) a).  The terms it produces reflect the correctness of certain
;; prover operations -- currently, accessing type-alist and typeset
;; information, rewriting, and linear arithmetic.

(defun-nx meta-cheat-contextual-fact (obj mfc state)
  (declare (xargs :stobjs state :verify-guards nil))
  (case-match obj
    (':type-alist
     ;; The assumptions in the type-alist (as accessed by mfc-type-alist) hold.
     (type-alist-ok-term (mfc-type-alist mfc)))
    ((':typeset term . &)
     ;; MFC-TS produces correct results according to typespec-check.
     `(typespec-check ',(mfc-ts term mfc state) ,term))
    ((':rw+ term alist obj equiv-info . &)
     ;; MFC-RW+ produces a term equivalent to (term \ alist).
     (meta-cheat-rw+-term term alist equiv-info
                          (mfc-rw+ term alist obj equiv-info mfc state)
                          state))
    ((':rw term obj equiv-info . &)
     ;; MFC-RW produces a term equivalent to (term \ nil)
     ;; (which is the same as term).
     (meta-cheat-rw+-term term nil equiv-info
                          (mfc-rw term obj equiv-info mfc state)
                          state))
    ((':ap term . &)
     ;; mfc-ap returns t or nil according to whether linear arithmetic can
     ;; falsify term
     (if (mfc-ap term mfc state)
         `(not ,term)
       *t*))
    ((':relieve-hyp hyp alist rune target bkptr . &)
     ;; relieve-hyp returns true if (hyp \ alist) was proved
     (if (mfc-relieve-hyp hyp alist rune target bkptr mfc state)
         (term-subst hyp alist)
       *t*))
    (& *t*)))



;; Turn a rewrite-rule record into a term
(defun rewrite-rule-term (x)
  `(implies ,(conjoin (access rewrite-rule x :hyps))
            (,(access rewrite-rule x :equiv)
             ,(access rewrite-rule x :lhs)
             ,(access rewrite-rule x :rhs))))

;; Meta-cheat-global-fact: Our hack above allows us to hypothesize while
;; proving meta rules that this function always produces a term that always
;; evaluates non-nil, i.e. under any alist.  At the moment, the terms it
;; produces reflect the correctess of certain facts stored in the world --
;; namely, facts accessed by meta-cheat-formula (which is similar to FORMULA
;; but does not support runes/corollaries), and rewrite-rules stored in the
;; LEMMAS properties of function symbols.

(defun-nx meta-cheat-global-fact (obj state)
  (declare (xargs :stobjs state :verify-guards nil))
  (case-match obj
    ((':formula name . normalp?)
     (let ((normalp (and (consp normalp?) (car normalp?))))
       ;; meta-cheat-formula produces a term that is a theorem, or *t* if there
       ;; was an error
       (meta-cheat-formula name normalp state)))
    ((':lemma fn n)
     (let* ((lemmas (getprop fn 'lemmas nil 'current-acl2-world (w state)))
            (rule (nth n lemmas)))
       ;; This assumes that the LEMMAS property of any symbol in the ACL2 world
       ;; is a list of rewrite-rule records which reflect known facts.
       (if (< (nfix n) (len lemmas))
           (rewrite-rule-term rule)
         *t*))) ;; fn doesn't exist or n too big
    (& *t*)))


;; At this point the user may use the supported prover facilities in meta rules
;; and it is possible to prove them correct.  However, it's not terribly
;; convenient yet.  In meta-cheat-user we prove theorems about
;; meta-cheat-global-fact and meta-cheat-contextual-fact that make it much more
;; convenient to do so, and define a macro that instantiates these theorems for
;; user-defined evaluators.
