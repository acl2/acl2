

(in-package "ACL2")

;; This book builds on meta-cheat-ttag and defines theorems and tools to enable
;; the user to more easily use the supported system functions in their meta
;; rules (and, not yet implemented, clause processors).

(include-book "meta-cheat-ttag")
(include-book "tools/defevaluator-fast" :dir :system)
(include-book "clause-processors/ev-theoremp" :dir :system)
(include-book "tools/def-functional-instance" :dir :system)           

;; The functions listed in this evaluator are the ones necessary to use all
;; meta-cheat facilities, i.e. to prove the theorems that follow.  We provide a
;; macro def-meta-cheat below which proves these theorems for an extension of
;; this evaluator.
(defevaluator-fast mcheat-ev mcheat-ev-lst
  ((typespec-check ts x)
   (if a b c)
   (equal a b)
   (not a)
   (iff a b)
   (implies a b))
  :namedp t)

;; This introduces a bad-guy function MCHEAT-EV-FALSIFY and a macro
;; (MCHEAT-EV-THEOREMP x) --> (mcheat-ev x (mcheat-ev-falsify x))
;; along with theorems for reasoning about falsify and
;; disjoin/conjoin/conjoin-clauses.
(def-ev-theoremp mcheat-ev)

;; Badguy for contextual terms.
(defchoose mcheat-contextual-badguy obj (a mfc state)
  (not (mcheat-ev (meta-cheat-contextual-fact obj mfc state) a)))

;; (mcheat-ev-contextual-facts a) can be used as a hyp in a :meta rule, and
;; allows us to assume the correctness of any result (correctly) derived from
;; the supported contextual prover facilities with respect to mcheat-ev.
(defmacro mcheat-ev-contextual-facts (a)
  `(mcheat-ev
    (meta-cheat-contextual-fact
     (mcheat-contextual-badguy a mfc state) mfc state)
    ,a))


(defthmd mcheat-contextual-badguy-sufficient
  (implies (mcheat-ev-contextual-facts a)
           (mcheat-ev (meta-cheat-contextual-fact obj mfc state) a))
  :hints (("goal" :use mcheat-contextual-badguy
           :in-theory (disable meta-cheat-contextual-fact))))

;; Badguy for global terms.
(defchoose mcheat-global-badguy obj (state)
  (not (mcheat-ev-theoremp (meta-cheat-global-fact obj state))))

;; (mcheat-ev-global-facts) can be used as a hyp in a :meta rule, and
;; allows us to assume the correctness of any result (correctly) derived from
;; the supported global prover facilities with respect to mcheat-ev.
(defmacro mcheat-ev-global-facts ()
  '(mcheat-ev
    (meta-cheat-global-fact
     (mcheat-global-badguy state) state)
    (mcheat-ev-falsify
     (meta-cheat-global-fact
      (mcheat-global-badguy state) state))))

(defthmd mcheat-global-badguy-sufficient
  (implies (mcheat-ev-global-facts)
           (mcheat-ev (meta-cheat-global-fact obj state) a))
  :hints (("goal" :use ((:instance mcheat-global-badguy)
                        (:instance mcheat-ev-falsify
                         (x (meta-cheat-global-fact obj state))))
           :in-theory (disable meta-cheat-global-fact))))


;; lemma: if the type-alist is ok, then any term bound in it
;; typespec-checks with its (cadr (assoc term type-alist)).
(defthm type-alist-lookup-when-type-alist-ok-term
  (implies (and (mcheat-ev (type-alist-ok-term type-alist) a)
                (assoc term type-alist))
           (typespec-check (cadr (assoc term type-alist))
                           (mcheat-ev term a)))
  :hints(("Goal" :in-theory (disable typespec-check))))

;; Assuming (mcheat-ev-contextual-facts a), we know type-alist lookups in
;; mfc-type-alist work as expected.
(defthm mcheat-type-alist-lookup
  (implies (and (mcheat-ev-contextual-facts a)
                (assoc-equal term (mfc-type-alist mfc)))
           (typespec-check (cadr (assoc-equal term (mfc-type-alist mfc)))
                           (mcheat-ev term a)))
  :hints (("goal" :use ((:instance mcheat-contextual-badguy
                         (obj :type-alist)))
           :in-theory (disable typespec-check))))

;; Assuming (mcheat-ev-contextual-facts a), we know mfc-ts works as expected.
(defthm mcheat-typeset
  (implies (mcheat-ev-contextual-facts a)
           (typespec-check (mfc-ts term mfc state)
                           (mcheat-ev term a)))
  :hints (("goal" :use ((:instance mcheat-contextual-badguy
                         (obj `(:typeset ,term))))
           :in-theory (disable typespec-check))))

;; Assuming (mcheat-ev-contextual-facts a), mfc-rw+ works as expected
;; for equal, iff, and equiv-relation calls (note: no geneqvs yet).
(defthm mcheat-rw+-equal
  (implies (mcheat-ev-contextual-facts a)
           (equal (mcheat-ev
                   (mfc-rw+ term alist obj nil mfc state)
                   a)
                  (mcheat-ev (term-subst term alist) a)))
  :hints(("Goal" :use ((:instance mcheat-contextual-badguy
                        (obj (list :rw+ term alist obj nil)))))))

(defthm mcheat-rw+-iff
  (implies (mcheat-ev-contextual-facts a)
           (iff (mcheat-ev
                 (mfc-rw+ term alist obj t mfc state)
                 a)
                (mcheat-ev (term-subst term alist) a)))
  :hints(("Goal" :use ((:instance mcheat-contextual-badguy
                        (obj (list :rw+ term alist obj t)))))))

(defthm mcheat-rw+-equiv
  (implies (and (mcheat-ev-contextual-facts a)
                equiv
                (not (equal equiv t))
                (symbolp equiv)
                (getprop equiv 'coarsenings nil 'current-acl2-world (w state)))
           (mcheat-ev
            `(,equiv ,(term-subst term alist)
                    ,(mfc-rw+ term alist obj equiv mfc state))
            a))
  :hints(("Goal" :use ((:instance mcheat-contextual-badguy
                        (obj (list :rw+ term alist obj equiv)))))))



;; To show that mfc-rw works as expected, we first show that term-subst with an
;; empty substitution is the identity.
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


;; Assuming (mcheat-ev-contextual-facts a), mfc-rw works as expected
;; for equal, iff, and equiv-relation calls (note: no geneqvs yet).
(defthm mcheat-rw-equal
  (implies (mcheat-ev-contextual-facts a)
           (equal (mcheat-ev
                   (mfc-rw term obj nil mfc state)
                   a)
                  (mcheat-ev term a)))
  :hints(("Goal" :use ((:instance mcheat-contextual-badguy
                        (obj (list :rw term obj nil)))))))

(defthm mcheat-rw-iff
  (implies (mcheat-ev-contextual-facts a)
           (iff (mcheat-ev
                 (mfc-rw term obj t mfc state)
                 a)
                (mcheat-ev term a)))
  :hints(("Goal" :use ((:instance mcheat-contextual-badguy
                        (obj (list :rw term obj t)))))))

(defthm mcheat-rw-equiv
  (implies (and (mcheat-ev-contextual-facts a)
                equiv
                (not (equal equiv t))
                (symbolp equiv)
                (getprop equiv 'coarsenings nil 'current-acl2-world (w state)))
           (mcheat-ev
            `(,equiv ,term
                    ,(mfc-rw term obj equiv mfc state))
            a))
  :hints(("Goal" :use ((:instance mcheat-contextual-badguy
                        (obj (list :rw term obj equiv)))))))

;; Assuming (mcheat-ev-contextual-facts a), mfc-ap works as expected.
(defthm mcheat-mfc-ap
  (implies (and (mfc-ap term mfc state)
                (mcheat-ev-contextual-facts a))
           (not (mcheat-ev term a)))
  :hints(("Goal" :use ((:instance mcheat-contextual-badguy
                        (obj (list :ap term)))))))

;; Assuming (mcheat-ev-contextual-facts a), mfc-relieve-hyp works as expected.
(defthm mcheat-relieve-hyp
  (implies (and (mfc-relieve-hyp hyp alist rune target bkptr mfc state)
                (mcheat-ev-contextual-facts a))
           (mcheat-ev (term-subst hyp alist) a))
  :hints(("Goal" :use ((:instance mcheat-contextual-badguy
                        (obj (list :relieve-hyp hyp alist rune target bkptr)))))))
                
;; Assuming (mcheat-ev-global-facts), meta-cheat-formula produces a theorem
(defthm mcheat-formula
  (implies (mcheat-ev-global-facts)
           (mcheat-ev (meta-cheat-formula name normalp state) a))
  :hints(("Goal" :use ((:instance mcheat-global-badguy-sufficient
                        (obj (list :formula name normalp)))))))

;; The following is used to show that any member of a list may be accessed by
;; nth, which is needed for mcheat-lemma below
(local
 (encapsulate nil
   (local (defthm minus-over-plus
            (equal (- (+ a b))
                   (+ (- a) (- b)))))
   (local (defthm plus-move-constant
            (implies (syntaxp (quotep b))
                     (equal (+ a b c)
                            (+ b a c)))))
   (local (defthm nth-plus-1
            (implies (natp b)
                     (equal (nth (+ 1 b) x)
                            (nth b (cdr x))))))

   (defthm len-member-equal
     (<= (len (member-equal x y)) (len y))
     :rule-classes :linear)

   (defthm len-member-equal-pos
     (implies (member-equal x y)
              (< 0 (len (member-equal x y))))
     :rule-classes :linear)

   (defthm nth-by-member-equal
     (implies (member x y)
              (equal (nth (+ (len y) (- (len (member x y)))) y)
                     x)))))

;; Assuming (mcheat-ev-global-facts), each element of the lemmas property of a
;; symbol in the world is a correct rewrite rule.
(defthm mcheat-lemma
  (implies (and (member rule (getprop fn 'lemmas nil 'current-acl2-world (w state)))
                (mcheat-ev (conjoin (access rewrite-rule rule :hyps)) a)
                (mcheat-ev-global-facts))
           (mcheat-ev `(,(access rewrite-rule rule :equiv)
                        ,(access rewrite-rule rule :lhs)
                        ,(access rewrite-rule rule :rhs))
                      a))
  :hints(("Goal"
          :use ((:instance mcheat-global-badguy-sufficient
                 (obj (list :lemma fn
                            (let ((lemmas
                                   (getprop fn 'lemmas nil
                                            'current-acl2-world (w state))))
                              (- (len lemmas)
                                 (len (member rule lemmas)))))))))))



;; Macro def-meta-cheat proves the above theorems for any evaluator that
;; extends mcheat-ev.
(defconst *def-meta-cheat-events*
  '(encapsulate nil
     
     (def-ev-theoremp evfn)

     (defchoose evfn-meta-cheat-contextual-badguy obj (a mfc state)
       (not (evfn (meta-cheat-contextual-fact obj mfc state) a)))

     (defchoose evfn-meta-cheat-global-badguy obj (state)
       (not (evfn (meta-cheat-global-fact obj state)
                  (evfn-falsify (meta-cheat-global-fact obj state)))))

     (defthmd evfn-falsify-sufficient
       (implies (evfn x (evfn-falsify x))
                (evfn x a))
       :hints (("goal" :use evfn-falsify)))

     (defmacro evfn-meta-cheat-contextual-facts (a)
       `(evfn
         (meta-cheat-contextual-fact
          (evfn-meta-cheat-contextual-badguy a mfc state) mfc state)
         ,a))

     (defthmd evfn-meta-cheat-contextual-badguy-sufficient
       (implies (evfn-meta-cheat-contextual-facts a)
                (evfn (meta-cheat-contextual-fact obj mfc state) a))
       :hints (("goal" :use evfn-meta-cheat-contextual-badguy
                :in-theory (disable meta-cheat-contextual-fact))))

     (defmacro evfn-meta-cheat-global-facts ()
       '(evfn
         (meta-cheat-global-fact
          (evfn-meta-cheat-global-badguy state) state)
         (evfn-falsify
          (meta-cheat-global-fact
           (evfn-meta-cheat-global-badguy state) state))))

     (defthmd evfn-meta-cheat-global-badguy-sufficient
       (implies (evfn-meta-cheat-global-facts)
                (evfn (meta-cheat-global-fact obj state) a))
       :hints (("goal" :use ((:instance evfn-meta-cheat-global-badguy)
                             (:instance evfn-falsify
                              (x (meta-cheat-global-fact obj state))))
                :in-theory (disable meta-cheat-global-fact))))

     (local (in-theory (enable evfn-meta-cheat-global-badguy-sufficient
                               evfn-meta-cheat-contextual-badguy-sufficient)))

     (local (in-theory (disable meta-cheat-global-fact
                                meta-cheat-contextual-fact)))

     (local
      (make-event
       (let ((rule (find-matching-rule
                    nil nil nil '(evfn (CONS (CAR X)
                                             (KWOTE-LST (evlst-fn (CDR X) A)))
                                       'NIL)
                    (getprop 'evfn 'lemmas nil 'current-acl2-world (w
                                                                    state)))))
         (prog2$
          (or rule
              (er hard? 'def-meta-cheat
                  "Couldn't find fncall on args rule for ~x0~%" 'evfn))
          `(add-default-hints
            '((and stable-under-simplificationp
                   '(:in-theory (enable ,rule
                                        evfn-falsify-sufficient)))))))))

     (def-functional-instance
       evfn-type-alist-lookup-when-type-alist-ok-term
       type-alist-lookup-when-type-alist-ok-term
       ((mcheat-ev evfn)
        (mcheat-ev-lst evlst-fn)))

     (def-functional-instance
       evfn-meta-cheat-type-alist-lookup
       mcheat-type-alist-lookup
       ((mcheat-ev evfn)
        (mcheat-ev-lst evlst-fn)
        (mcheat-contextual-badguy evfn-meta-cheat-contextual-badguy)))

     (def-functional-instance
       evfn-meta-cheat-typeset
       mcheat-typeset
       ((mcheat-ev evfn)
        (mcheat-ev-lst evlst-fn)
        (mcheat-contextual-badguy evfn-meta-cheat-contextual-badguy)))

     (def-functional-instance
       evfn-meta-cheat-rw+-equal
       mcheat-rw+-equal
       ((mcheat-ev evfn)
        (mcheat-ev-lst evlst-fn)
        (mcheat-contextual-badguy evfn-meta-cheat-contextual-badguy)))

     (def-functional-instance
       evfn-meta-cheat-rw+-iff
       mcheat-rw+-iff
       ((mcheat-ev evfn)
        (mcheat-ev-lst evlst-fn)
        (mcheat-contextual-badguy evfn-meta-cheat-contextual-badguy)))

     (def-functional-instance
       evfn-meta-cheat-rw+-equiv
       mcheat-rw+-equiv
       ((mcheat-ev evfn)
        (mcheat-ev-lst evlst-fn)
        (mcheat-contextual-badguy evfn-meta-cheat-contextual-badguy)))

     (def-functional-instance
       evfn-meta-cheat-rw-equal
       mcheat-rw-equal
       ((mcheat-ev evfn)
        (mcheat-ev-lst evlst-fn)
        (mcheat-contextual-badguy evfn-meta-cheat-contextual-badguy)))

     (def-functional-instance
       evfn-meta-cheat-rw-iff
       mcheat-rw-iff
       ((mcheat-ev evfn)
        (mcheat-ev-lst evlst-fn)
        (mcheat-contextual-badguy evfn-meta-cheat-contextual-badguy)))

     (def-functional-instance
       evfn-meta-cheat-rw-equiv
       mcheat-rw-equiv
       ((mcheat-ev evfn)
        (mcheat-ev-lst evlst-fn)
        (mcheat-contextual-badguy evfn-meta-cheat-contextual-badguy)))

     (def-functional-instance
       evfn-meta-cheat-mfc-ap
       mcheat-mfc-ap
       ((mcheat-ev evfn)
        (mcheat-ev-lst evlst-fn)
        (mcheat-contextual-badguy evfn-meta-cheat-contextual-badguy)))

     (def-functional-instance
       evfn-meta-cheat-relieve-hyp
       mcheat-relieve-hyp
       ((mcheat-ev evfn)
        (mcheat-ev-lst evlst-fn)
        (mcheat-contextual-badguy evfn-meta-cheat-contextual-badguy)))

     (def-functional-instance
       evfn-meta-cheat-formula
       mcheat-formula
       ((mcheat-ev evfn)
        (mcheat-ev-lst evlst-fn)
        (mcheat-ev-falsify evfn-falsify)
        (mcheat-global-badguy evfn-meta-cheat-global-badguy)))

     (def-functional-instance
       evfn-meta-cheat-lemma
       mcheat-lemma
       ((mcheat-ev evfn)
        (mcheat-ev-lst evlst-fn)
        (mcheat-ev-falsify evfn-falsify)
        (mcheat-global-badguy evfn-meta-cheat-global-badguy)))))

(defun meta-cheat-replace-sym (from to x)
  (let* ((name (symbol-name x))
         (pos (search from name)))
    (if pos
        (let* ((pre (subseq name 0 pos))
               (post (subseq name (+ pos (length from)) nil)))
          (intern-in-package-of-symbol
           (concatenate 'string pre (symbol-name to) post)
           to))
      x)))

(mutual-recursion
 (defun meta-cheat-replace-evfn (evfn evlst-fn x)
   (declare (xargs :mode :program))
   (if (atom x)
       (if (symbolp x)
           (meta-cheat-replace-sym
            "EVLST-FN" evlst-fn
            (meta-cheat-replace-sym
             "EVFN" evfn x))
         x)
     (meta-cheat-replace-evfn-list evfn evlst-fn x)))
 (defun meta-cheat-replace-evfn-list (evfn evlst-fn x)
   (if (atom x)
       nil
     (cons (meta-cheat-replace-evfn evfn evlst-fn (car x))
           (meta-cheat-replace-evfn-list evfn evlst-fn (cdr x))))))


(defmacro def-meta-cheat (evfn evlst-fn)
  (meta-cheat-replace-evfn evfn evlst-fn *def-meta-cheat-events*))


(in-theory (disable meta-cheat-contextual-fact
                    meta-cheat-global-fact))



;; Now a couple of examples.


(local
 ;; This just localizes all the events in events and allows a name to be given
 (defmacro localize-example (name &rest events)
   `(encapsulate nil
      (value-triple ',name)
      (local
       (progn . ,events))
      (value-triple ',name))))




(local
 (localize-example
  using-typeset-and-type-alist
  
  (defthm nth-when-symbolp
    (implies (symbolp n)
             (equal (nth n x)
                    (car x)))
    :rule-classes nil)

  (defevaluator-fast nthmeta-ev nthmeta-ev-lst
    ((typespec-check ts x)
     (if a b c)
     (equal a b)
     (not a)
     (iff a b)
     (implies a b)
     (nth n x)
     (car x))
    :namedp t)

  (def-meta-cheat nthmeta-ev nthmeta-ev-lst)

  (defun nth-symbolp-metafn (term mfc state)
    (declare (xargs :stobjs state))
    (case-match term
      (('nth n x)
       (if (equal (mfc-ts n mfc state) *ts-symbol*)
           `(car ,x)
         (prog2$ (cw "Oops, the typeset of n is ~x0~%"
                     (mfc-ts n mfc state))
                 term)))
      (& term)))



  (defthm nth-symbolp-meta
    (implies (nthmeta-ev-meta-cheat-contextual-facts a)
             (equal (nthmeta-ev term a)
                    (nthmeta-ev (nth-symbolp-metafn term mfc state) a)))
    :hints (("goal" :use ((:instance nthmeta-ev-meta-cheat-typeset
                           (term (cadr term))))
             :in-theory (disable nthmeta-ev-meta-cheat-typeset)))
    :rule-classes ((:meta :trigger-fns (nth))))

  (defmacro nth-symbolp-test (n)
    `(encapsulate nil
       (local (progn

                (encapsulate
                  (((foo *) => *)
                   ((bar *) => *)
                   ((baz *) => *))


                  (local (defun foo (x) (declare (ignore x)) t))
                  (local (defun bar (x) (symbolp x)))
                  (local (defun baz (x) (symbolp x)))

                  (defthm foo-type
                    (symbolp (foo x))
                    :rule-classes :type-prescription)

                  (defthm bar-booleanp
                    (booleanp (bar x))
                    :rule-classes :type-prescription)

                  (defthm bar-implies-symbolp
                    (implies (bar x)
                             (symbolp x))
                    :rule-classes :compound-recognizer)

                  (defthm baz-implies-symbolp
                    (implies (baz x)
                             (symbolp x))
                    :rule-classes :forward-chaining))

                (make-event
                 (mv-let (erp val state)
                   (defthm nth-foo
                     (equal (nth (foo x) y)
                            (car y)))
                   (declare (ignore val))
                   (if erp
                       (prog2$ (cw "FOO failed~%")
                               (value '(value-triple ':foo-failed)))
                     (prog2$ (cw "FOO passed~%")
                             (value '(value-triple ':foo-passed))))))

                (make-event
                 (mv-let (erp val state)
                   (defthm nth-when-bar
                     (implies (Bar x)
                              (equal (nth x y)
                                     (car y))))
                   (declare (ignore val))
                   (if erp
                       (prog2$ (cw "BAR failed~%")
                               (value '(value-triple ':bar-failed)))
                     (prog2$ (cw "BAR passed~%")
                             (value '(value-triple ':bar-passed))))))


                (make-event
                 (mv-let (erp val state)
                   (defthm nth-when-baz
                     (implies (Baz x)
                              (equal (nth x y)
                                     (car y))))
                   (declare (ignore val))
                   (if erp
                       (prog2$ (cw "BAZ failed~%")
                               (value '(value-triple ':baz-failed)))
                     (prog2$ (cw "BAZ passed~%")
                             (value '(value-triple ':baz-passed))))))))
       (value-triple '(nth-symbol-test ,n))))

  (nth-symbolp-test 1)



  (defthm type-alistp-of-mfc-type-alist
    (type-alistp (mfc-type-alist mfc)))

  (in-theory (disable mfc-type-alist))

  (encapsulate nil
    (local (defthm alistp-when-type-alistp
             (implies (type-alistp x)
                      (alistp x))))
    (defthm alistp-of-mfc-type-alist
      (alistp (mfc-type-alist mfc))))

  (local (defthm assoc-equal-when-alistp
           (implies (alistp x)
                    (iff (consp (Assoc-equal a x))
                         (assoc-equal a x)))))

  (defthm cdr-assoc-equal-when-type-alistp
    (implies (type-alistp x)
             (iff (consp (cdr (assoc-equal a x)))
                  (assoc-equal a x))))


  (defun nth-symbolp-weaker-metafn (term mfc state)
    (declare (xargs :stobjs state)
             (ignorable state))
    (case-match term
      (('nth n x)
       (prog2$ (cw "type-alist: ~x0~%" (mfc-type-alist mfc))
               (if (equal (cadr (assoc-equal n (mfc-type-alist mfc)))
                          *ts-symbol*)
                   `(car ,x)
                 (prog2$ (cw "Oops, type-alist entry for n is ~x0~%"
                             (cadr (assoc-equal n (mfc-type-alist mfc))))
                         term))))
      (& term)))



  (defthm nth-symbolp-weaker-meta
    (implies (nthmeta-ev-meta-cheat-contextual-facts a)
             (equal (nthmeta-ev term a)
                    (nthmeta-ev (nth-symbolp-weaker-metafn term mfc state) a)))
    :hints (("goal" :use ((:instance nthmeta-ev-meta-cheat-type-alist-lookup
                           (term (cadr term))))
             :in-theory (disable nthmeta-ev-meta-cheat-type-alist-lookup)))
    :rule-classes ((:meta :trigger-fns (nth))))

  (in-theory (disable nth nth-symbolp-meta))

  (nth-symbolp-test 2)))


(local
 (localize-example
  using-mfc-rw+

  (encapsulate
    (((foo *) => *)
     ((bar *) => *)
     ((baz *) => *))

    (set-ignore-ok t)
    (set-irrelevant-formals-ok t)
    (local (defun foo (x) nil))
    (local (defun bar (x) nil))
    (local (defun baz (x) nil))

    ;; Under (bar ...) context, (foo x) is equivalent to x.
    (defthm bar-of-foo
      (equal (bar (foo x))
             (bar x)))

    ;; Under (foo ...) context, (baz x) is equivalent to x.
    (defthm foo-of-baz
      (equal (foo (baz x))
             (foo x))))

  ;; The above constraints imply that under BAR context, (baz x) is equivalent
  ;; to x, since:
  ;; (bar (baz x))       => (bar (foo (baz x))) by bar-of-foo (reversed)
  ;; (bar (foo (baz x))) => (bar (foo x))       by foo-of-baz
  ;; (bar (foo x))       => (bar x)             by bar-of-foo.
  ;; But because the top one uses bar-of-foo reversed, ACL2 can't prove this:
  (make-event
   (b* (((mv erp & state)
         (defthm bar-of-baz-fails
           (equal (bar (baz x))
                  (bar x)))))
     (if erp
         (value '(value-triple :failed))
       (er soft 'bar-of-baz-fails "Proof unexpectedly succeeded"))))

  (defevaluator-fast foobar-ev foobar-ev-lst
    ((typespec-check ts x)
     (if a b c)
     (equal a b)
     (not a)
     (iff a b)
     (implies a b)
     (foo x)
     (bar x))
    :namedp t)

  (def-meta-cheat foobar-ev foobar-ev-lst)

  ;; This meta rule only knows basically that a BAR context induces a FOO
  ;; context, because (bar (foo x)) = (bar x).  In particular it cares nothing
  ;; about baz.
  (defun reduce-bar-with-foo (x mfc state)
    (declare (xargs :stobjs state))
    (case-match x
      (('bar xx . &)
       (let* ((xxx (case-match xx
                     (('foo xxx . &)
                      (prog2$ (cw "note: reduce-bar-with-foo caught xx not in ~
                                 normal form: ~x0~%" xx)
                              xxx))
                     (& xx)))
              (foo-xxx-rw (mfc-rw+ '(foo xxx)
                                   `((xxx . ,xxx))
                                   '? nil mfc state))
              (y (case-match foo-xxx-rw
                   (('foo y . &) y)
                   (& foo-xxx-rw))))
         `(bar ,y)))
      (& x)))

  (encapsulate nil
    (local (defthm bar-of-foo-free
             (implies (equal x (foo y))
                      (equal (bar x)
                             (bar y)))))

    ;; Note: even with bar-of-foo-free, this isn't proved
    (make-event
     (b* (((mv erp & state)
           (defthm bar-of-baz-fails
             (equal (bar (baz x))
                    (bar x)))))
       (if erp
           (value '(value-triple :failed))
         (er soft 'bar-of-baz-fails "Proof unexpectedly succeeded"))))

    (defthm reduce-bar-with-foo-meta
      (implies (foobar-ev-meta-cheat-contextual-facts a)
               (equal (foobar-ev x a)
                      (foobar-ev (reduce-bar-with-foo x mfc state) a)))
      :hints (("goal" :use ((:instance FOOBAR-EV-META-CHEAT-RW+-EQUAL
                             (term '(foo xxx))
                             (alist (let ((xx (cadr x)))
                                      `((xxx . ,(case-match xx
                                                  (('foo xxx . &) xxx)
                                                  (& xx))))))
                             (obj '?))
                            (:instance bar-of-foo
                             (x (foobar-ev (let ((xx (cadr x)))
                                             (case-match xx
                                               (('foo xxx . &) xxx)
                                               (& xx)))
                                           a))))
               :in-theory (disable foobar-ev-meta-cheat-rw+-equal
                                   bar-of-foo)))
      :rule-classes ((:meta :trigger-fns (bar)))))

  (defthm bar-of-baz
    (equal (bar (baz x))
           (bar x)))))
