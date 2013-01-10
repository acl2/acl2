(in-package "ACL2")

;; This book builds on meta-extract-ttag and defines theorems and tools to enable
;; the user to more easily use the supported system functions in their meta
;; rules (and, not yet implemented, clause processors).

;(include-book "meta-extract-ttag")
(include-book "tools/defevaluator-fast" :dir :system)
(include-book "ev-theoremp")
(include-book "tools/def-functional-instance" :dir :system)           

; The following are necessary for developer builds, in which sublis-var and
; other supporting functions for meta-extract are not in :logic mode.
(include-book "system/sublis-var" :dir :system)
(include-book "system/meta-extract" :dir :system)

;; The functions listed in this evaluator are the ones necessary to use all
;; meta-extract facilities, i.e. to prove the theorems that follow.  We provide a
;; macro def-meta-extract below which proves these theorems for an extension of
;; this evaluator.
(defevaluator-fast mextract-ev mextract-ev-lst
  ((typespec-check ts x)
   (if a b c)
   (equal a b)
   (not a)
   (iff a b)
   (implies a b))
  :namedp t)

;; This introduces a bad-guy function MEXTRACT-EV-FALSIFY and a macro
;; (MEXTRACT-EV-THEOREMP x) --> (mextract-ev x (mextract-ev-falsify x))
;; along with theorems for reasoning about falsify and
;; disjoin/conjoin/conjoin-clauses.
(def-ev-theoremp mextract-ev)

;; Badguy for contextual terms.
(defchoose mextract-contextual-badguy obj (a mfc state)
  (not (mextract-ev (meta-extract-contextual-fact obj mfc state) a)))

;; (mextract-ev-contextual-facts a) can be used as a hyp in a :meta rule, and
;; allows us to assume the correctness of any result (correctly) derived from
;; the supported contextual prover facilities with respect to mextract-ev.
(defmacro mextract-ev-contextual-facts (a)
  `(mextract-ev
    (meta-extract-contextual-fact
     (mextract-contextual-badguy a mfc state) mfc state)
    ,a))


(defthmd mextract-contextual-badguy-sufficient
  (implies (mextract-ev-contextual-facts a)
           (mextract-ev (meta-extract-contextual-fact obj mfc state) a))
  :hints (("goal" :use mextract-contextual-badguy
           :in-theory (disable meta-extract-contextual-fact))))

;; Badguy for global terms.
(defchoose mextract-global-badguy obj (state)
  (not (mextract-ev-theoremp (meta-extract-global-fact obj state))))

;; (mextract-ev-global-facts) can be used as a hyp in a :meta rule, and
;; allows us to assume the correctness of any result (correctly) derived from
;; the supported global prover facilities with respect to mextract-ev.
(defmacro mextract-ev-global-facts ()
  '(mextract-ev
    (meta-extract-global-fact
     (mextract-global-badguy state) state)
    (mextract-ev-falsify
     (meta-extract-global-fact
      (mextract-global-badguy state) state))))

(defthmd mextract-global-badguy-sufficient
  (implies (mextract-ev-global-facts)
           (mextract-ev (meta-extract-global-fact obj state) a))
  :hints (("goal" :use ((:instance mextract-global-badguy)
                        (:instance mextract-ev-falsify
                         (x (meta-extract-global-fact obj state))))
           :in-theory (disable meta-extract-global-fact))))

;; Assuming (mextract-ev-contextual-facts a), we know mfc-ts works as expected.
(defthm mextract-typeset
  (implies (mextract-ev-contextual-facts a)
           (typespec-check (mfc-ts term mfc state :forcep nil)
                           (mextract-ev term a)))
  :hints (("goal" :use ((:instance mextract-contextual-badguy
                         (obj `(:typeset ,term))))
           :in-theory (disable typespec-check))))

;; Assuming (mextract-ev-contextual-facts a), mfc-rw+ works as expected
;; for equal, iff, and equiv-relation calls (note: no geneqvs yet).
(defthm mextract-rw+-equal
  (implies (mextract-ev-contextual-facts a)
           (equal (mextract-ev
                   (mfc-rw+ term alist obj nil mfc state
                            :forcep nil)
                   a)
                  (mextract-ev (sublis-var alist term) a)))
  :hints(("Goal" :use ((:instance mextract-contextual-badguy
                        (obj (list :rw+ term alist obj nil)))))))

(defthm mextract-rw+-iff
  (implies (mextract-ev-contextual-facts a)
           (iff (mextract-ev
                 (mfc-rw+ term alist obj t mfc state
                          :forcep nil)
                 a)
                (mextract-ev (sublis-var alist term) a)))
  :hints(("Goal" :use ((:instance mextract-contextual-badguy
                        (obj (list :rw+ term alist obj t)))))))

(defthm mextract-rw+-equiv
  (implies (and (mextract-ev-contextual-facts a)
                equiv
                (not (equal equiv t))
                (symbolp equiv)
                (getprop equiv 'coarsenings nil 'current-acl2-world (w state)))
           (mextract-ev
            `(,equiv ,(sublis-var alist term)
                    ,(mfc-rw+ term alist obj equiv mfc state
                              :forcep nil))
            a))
  :hints(("Goal" :use ((:instance mextract-contextual-badguy
                        (obj (list :rw+ term alist obj equiv)))))))

;; Assuming (mextract-ev-contextual-facts a), mfc-rw works as expected
;; for equal, iff, and equiv-relation calls (note: no geneqvs yet).
(defthm mextract-rw-equal
  (implies (mextract-ev-contextual-facts a)
           (equal (mextract-ev
                   (mfc-rw term obj nil mfc state
                           :forcep nil)
                   a)
                  (mextract-ev (sublis-var nil term) a)))
  :hints(("Goal" :use ((:instance mextract-contextual-badguy
                        (obj (list :rw term obj nil)))))))

(defthm mextract-rw-iff
  (implies (mextract-ev-contextual-facts a)
           (iff (mextract-ev
                 (mfc-rw term obj t mfc state
                         :forcep nil)
                 a)
                (mextract-ev (sublis-var nil term) a)))
  :hints(("Goal" :use ((:instance mextract-contextual-badguy
                        (obj (list :rw term obj t)))))))

(defthm mextract-rw-equiv
  (implies (and (mextract-ev-contextual-facts a)
                equiv
                (not (equal equiv t))
                (symbolp equiv)
                (getprop equiv 'coarsenings nil 'current-acl2-world (w state)))
           (mextract-ev
            `(,equiv ,(sublis-var nil term)
                    ,(mfc-rw term obj equiv mfc state
                             :forcep nil))
            a))
  :hints(("Goal" :use ((:instance mextract-contextual-badguy
                        (obj (list :rw term obj equiv)))))))

;; Assuming (mextract-ev-contextual-facts a), mfc-ap works as expected.
(defthm mextract-mfc-ap
  (implies (and (mfc-ap term mfc state :forcep nil)
                (mextract-ev-contextual-facts a))
           (not (mextract-ev term a)))
  :hints(("Goal" :use ((:instance mextract-contextual-badguy
                        (obj (list :ap term)))))))

;; Assuming (mextract-ev-contextual-facts a), mfc-relieve-hyp works as expected.
(defthm mextract-relieve-hyp
  (implies (and (mfc-relieve-hyp hyp alist rune target bkptr mfc state
                                 :forcep nil)
                (mextract-ev-contextual-facts a))
           (mextract-ev (sublis-var alist hyp) a))
  :hints(("Goal" :use ((:instance mextract-contextual-badguy
                        (obj (list :relieve-hyp hyp alist rune target bkptr)))))))
                
;; Assuming (mextract-ev-global-facts), meta-extract-formula produces a theorem
(defthm mextract-formula
  (implies (mextract-ev-global-facts)
           (mextract-ev (meta-extract-formula name state) a))
  :hints(("Goal" :use ((:instance mextract-global-badguy-sufficient
                        (obj (list :formula name)))))))

;; The following is used to show that any member of a list may be accessed by
;; nth, which is needed for mextract-lemma below
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

(defthm mextract-lemma-term
  (implies (and (member rule (getprop fn 'lemmas nil 'current-acl2-world (w state)))
                (mextract-ev-global-facts))
           (mextract-ev (rewrite-rule-term rule)
                      a))
  :hints(("Goal"
          :use ((:instance mextract-global-badguy-sufficient
                 (obj (list :lemma fn
                            (let ((lemmas
                                   (getprop fn 'lemmas nil
                                            'current-acl2-world (w state))))
                              (- (len lemmas)
                                 (len (member rule lemmas)))))))))))

;; Assuming (mextract-ev-global-facts), each element of the lemmas property of a
;; symbol in the world is a correct rewrite rule.
(defthm mextract-lemma
  (implies (and (member rule (getprop fn 'lemmas nil 'current-acl2-world (w state)))
                (not (eq (access rewrite-rule rule :subclass) 'meta))
                (mextract-ev (conjoin (access rewrite-rule rule :hyps)) a)
                (mextract-ev-global-facts))
           (mextract-ev `(,(access rewrite-rule rule :equiv)
                        ,(access rewrite-rule rule :lhs)
                        ,(access rewrite-rule rule :rhs))
                      a))
  :hints(("Goal"
          :use ((:instance mextract-global-badguy-sufficient
                 (obj (list :lemma fn
                            (let ((lemmas
                                   (getprop fn 'lemmas nil
                                            'current-acl2-world (w state))))
                              (- (len lemmas)
                                 (len (member rule lemmas)))))))))))



;; Macro def-meta-extract proves the above theorems for any evaluator that
;; extends mextract-ev.
(defconst *def-meta-extract-events*
  '(encapsulate nil
     
     (def-ev-theoremp evfn)

     (defchoose evfn-meta-extract-contextual-badguy obj (a mfc state)
       (not (evfn (meta-extract-contextual-fact obj mfc state) a)))

     (defchoose evfn-meta-extract-global-badguy obj (state)
       (not (evfn (meta-extract-global-fact obj state)
                  (evfn-falsify (meta-extract-global-fact obj state)))))

     (defthmd evfn-falsify-sufficient
       (implies (evfn x (evfn-falsify x))
                (evfn x a))
       :hints (("goal" :use evfn-falsify)))

     (defmacro evfn-meta-extract-contextual-facts (a)
       `(evfn
         (meta-extract-contextual-fact
          (evfn-meta-extract-contextual-badguy a mfc state) mfc state)
         ,a))

     (defthmd evfn-meta-extract-contextual-badguy-sufficient
       (implies (evfn-meta-extract-contextual-facts a)
                (evfn (meta-extract-contextual-fact obj mfc state) a))
       :hints (("goal" :use evfn-meta-extract-contextual-badguy
                :in-theory (disable meta-extract-contextual-fact))))

     (defmacro evfn-meta-extract-global-facts ()
       '(evfn
         (meta-extract-global-fact
          (evfn-meta-extract-global-badguy state) state)
         (evfn-falsify
          (meta-extract-global-fact
           (evfn-meta-extract-global-badguy state) state))))

     (defthmd evfn-meta-extract-global-badguy-sufficient
       (implies (evfn-meta-extract-global-facts)
                (evfn (meta-extract-global-fact obj state) a))
       :hints (("goal" :use ((:instance evfn-meta-extract-global-badguy)
                             (:instance evfn-falsify
                              (x (meta-extract-global-fact obj state))))
                :in-theory (disable meta-extract-global-fact))))

     (local (in-theory (enable evfn-meta-extract-global-badguy-sufficient
                               evfn-meta-extract-contextual-badguy-sufficient)))

     (local (in-theory (disable meta-extract-global-fact
                                meta-extract-contextual-fact)))

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
              (er hard? 'def-meta-extract
                  "Couldn't find fncall on args rule for ~x0~%" 'evfn))
          `(add-default-hints
            '((and stable-under-simplificationp
                   '(:in-theory (enable ,rule
                                        evfn-falsify-sufficient)))))))))

     (def-functional-instance
       evfn-meta-extract-typeset
       mextract-typeset
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-contextual-badguy evfn-meta-extract-contextual-badguy)))

     (def-functional-instance
       evfn-meta-extract-rw+-equal
       mextract-rw+-equal
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-contextual-badguy evfn-meta-extract-contextual-badguy)))

     (def-functional-instance
       evfn-meta-extract-rw+-iff
       mextract-rw+-iff
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-contextual-badguy evfn-meta-extract-contextual-badguy)))

     (def-functional-instance
       evfn-meta-extract-rw+-equiv
       mextract-rw+-equiv
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-contextual-badguy evfn-meta-extract-contextual-badguy)))

     (def-functional-instance
       evfn-meta-extract-rw-equal
       mextract-rw-equal
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-contextual-badguy evfn-meta-extract-contextual-badguy)))

     (def-functional-instance
       evfn-meta-extract-rw-iff
       mextract-rw-iff
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-contextual-badguy evfn-meta-extract-contextual-badguy)))

     (def-functional-instance
       evfn-meta-extract-rw-equiv
       mextract-rw-equiv
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-contextual-badguy evfn-meta-extract-contextual-badguy)))

     (def-functional-instance
       evfn-meta-extract-mfc-ap
       mextract-mfc-ap
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-contextual-badguy evfn-meta-extract-contextual-badguy)))

     (def-functional-instance
       evfn-meta-extract-relieve-hyp
       mextract-relieve-hyp
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-contextual-badguy evfn-meta-extract-contextual-badguy)))

     (def-functional-instance
       evfn-meta-extract-formula
       mextract-formula
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-ev-falsify evfn-falsify)
        (mextract-global-badguy evfn-meta-extract-global-badguy)))

     (def-functional-instance
       evfn-meta-extract-lemma-term
       mextract-lemma-term
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-ev-falsify evfn-falsify)
        (mextract-global-badguy evfn-meta-extract-global-badguy)))

     (def-functional-instance
       evfn-meta-extract-lemma
       mextract-lemma
       ((mextract-ev evfn)
        (mextract-ev-lst evlst-fn)
        (mextract-ev-falsify evfn-falsify)
        (mextract-global-badguy evfn-meta-extract-global-badguy)))))

(defun meta-extract-replace-sym (from to x)
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
 (defun meta-extract-replace-evfn (evfn evlst-fn x)
   (declare (xargs :mode :program))
   (if (atom x)
       (if (symbolp x)
           (meta-extract-replace-sym
            "EVLST-FN" evlst-fn
            (meta-extract-replace-sym
             "EVFN" evfn x))
         x)
     (meta-extract-replace-evfn-list evfn evlst-fn x)))
 (defun meta-extract-replace-evfn-list (evfn evlst-fn x)
   (if (atom x)
       nil
     (cons (meta-extract-replace-evfn evfn evlst-fn (car x))
           (meta-extract-replace-evfn-list evfn evlst-fn (cdr x))))))


(defmacro def-meta-extract (evfn evlst-fn)
  (meta-extract-replace-evfn evfn evlst-fn *def-meta-extract-events*))


(in-theory (disable meta-extract-contextual-fact
                    meta-extract-global-fact))



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

  (def-meta-extract nthmeta-ev nthmeta-ev-lst)

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
    (implies (nthmeta-ev-meta-extract-contextual-facts a)
             (equal (nthmeta-ev term a)
                    (nthmeta-ev (nth-symbolp-metafn term mfc state) a)))
    :hints (("goal" :use ((:instance nthmeta-ev-meta-extract-typeset
                           (term (cadr term))))
             :in-theory (disable nthmeta-ev-meta-extract-typeset)))
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

  (def-meta-extract foobar-ev foobar-ev-lst)

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
                                   '? nil mfc state :forcep nil))
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
      (implies (foobar-ev-meta-extract-contextual-facts a)
               (equal (foobar-ev x a)
                      (foobar-ev (reduce-bar-with-foo x mfc state) a)))
      :hints (("goal" :use ((:instance FOOBAR-EV-META-EXTRACT-RW+-EQUAL
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
               :in-theory (disable foobar-ev-meta-extract-rw+-equal
                                   bar-of-foo)))
      :rule-classes ((:meta :trigger-fns (bar)))))

  (defthm bar-of-baz
    (equal (bar (baz x))
           (bar x)))))
