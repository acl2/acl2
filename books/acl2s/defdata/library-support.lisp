#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

;record implementation
(include-book "acl2s/defdata/records" :dir :system)
(defconst *tag* :0tag)

;(include-book "finite-set-theory/osets/sets" :dir :system)
;; (include-book "std/osets/top" :dir :system)

;GETTING RECORDS TO behave nicely here are some
;;RECORDS THMS proven

#|

 s-diff-s1/2 are rules that replaces acl2::s-diff-s,
 acl2::s-diff-s is a rule that has a loop-stopper and the
 behavior of loop-stoppers makes it hard to determine how ss are
 rewritten, so the only point of defdata-s-diff-s is to get rid
 of that loop stopper and add more predictable behavior.

 For example, with s-diff-s

 (acl2s-defaults :set testing-enabled nil)

 (thm
   (equal x
          (s :p 'a (s :ab 'b nil))))

 Doesn't do any rewriting, but

 (s :p 'a (s :ab 'b nil)) is ((:AB . B) (:P . A))

 So there is a discrepancy between evaluation and theorem proving
 that just makes it painful when debugging.

 Now after looking at the documentation, it isn't really

 (term-order ':ab ':p)

 which is used to determine whether to apply the rule; if it was, then
 the rule would be applied; it is:

 (term-order '':ab '':p)

 but that is based on pseudo-function application stuff described in
 the documentation, which is complicated and then which uses lexorder,
 so I want more predicable behavior.

|#

; If a and b are quoted objects, check the term-order by unquoting
; them. This is the only rule we should see in ACL2s/defdata since
; record fields are keywords.
(defthm s-diff-s1
  (implies (and
            (syntaxp (quotep a))
            (syntaxp (quotep b))
            (syntaxp (term-order (unquote a) (unquote b)))
            (not (equal a b)))
           (equal (s b y (s a x r))
                  (s a x (s b y r))))
  :rule-classes ((:rewrite :loop-stopper nil)))

; This rule is here so that we get the s-diff-s behavior in all
; other cases.
(defthm s-diff-s2
  (implies (and
            (syntaxp (or (not (quotep a)) (not (quotep b))))
            (not (equal a b)))
           (equal (s b y (s a x r))
                  (s a x (s b y r))))
  :rule-classes ((:rewrite :loop-stopper ((a b s)))))

(in-theory (disable s-diff-s))

#|

(defthm records-lemma-acl2-count
  (implies (and (ifmp v)
                (well-formed-map v)
                )
           (< (acl2-count (g-wf x v))
              (acl2-count v)))
  :hints (("goal" :in-theory (enable g-wf)))
  :rule-classes :linear)

(defun non-empty-good-map (x)
  (declare (xargs :guard t))
  (and (consp x)
       (good-map x)))

|#

(defthm records-lemma-acl2-count
  (implies (and (ifrp v)
                (rcdp v))
           (< (acl2-count (g-aux x v))
              (acl2-count v)))
  :hints (("goal" :in-theory (enable g-aux ifrp)))
  :rule-classes :linear)

(defun good-map (x)
  (rcdp x))

(defun non-empty-good-map (x)
  (declare (xargs :guard t))
  (and (consp x)
       (rcdp x)))

(defthm records-acl2-count-linear-arith-<=
  (<= (acl2-count (g k v))
      (acl2-count v))
  :hints (("goal" :in-theory (enable rcdp g g-aux ifrp acl2->rcd)))
  :rule-classes :linear)

(defthm records-acl2-count-linear-arith-<
  (implies (and k
                (g k v))
           (< (acl2-count (g k v))
              (acl2-count v)))
  :hints (("goal" :in-theory (enable rcdp g g-aux ifrp acl2->rcd)))
  :rule-classes :linear)

(defthm records-acl2-count
  (implies (and x
                (consp v))
           (< (acl2-count (g x v))
              (acl2-count v)))
  :hints (("goal" :induct (g-aux x v)
           :in-theory (enable rcdp g g-aux ifrp acl2->rcd)))
  :rule-classes :linear)


;shifted from base.lisp to here.

;; (defun map-identity (x) 
;;   "for map elim rules -- dummy destructor"
;;   x)

(defun map-identity2 (a x) 
  "for map elim rule -- dummy destructor"
  (declare (ignore a))
  x)

(defthmd map-elim-rule 
;(implies (rcdp x)
  (equal (s a (g a x) (map-identity2 a x))
         x)
  :rule-classes :elim)

(defun list-identity2 (a x) 
  "for list elim rule -- dummy destructor"
  (declare (ignore a))
  x)

(defthmd list-elim-rule 
  (implies (and (true-listp x)
                (natp i)
                (< i (len x)))
           (equal (update-nth i (nth i x) (list-identity2 i x))
                  x))
  :hints (("Goal" :in-theory (e/d (update-nth len nth) (true-listp (tau-system)))))
  :rule-classes :elim)

(defun put-assoc-equal-elim-rule-version (e x)
  "put entry e=(key . value) in its rightful place in alist x"
  (put-assoc-equal (car e) (cdr e) x))

(defun alist-identity2 (a x) 
  "for alist elim rule -- dummy destructor"
  (declare (ignore a))
  x)

(defthm assoc-eq-answer-car 
  (implies (assoc-equal k x) 
           (equal (car (assoc-equal k x)) k)))

(defthmd alist-elim-rule 
  (implies (and (alistp x)
                (assoc-equal k x))
           (equal (put-assoc-equal-elim-rule-version (assoc-equal k x) (alist-identity2 k x))
                  x))
  :rule-classes :elim)

;Following lemmas are needed for record modifier theorems

(defthm s-aux-consp
  (implies v
           (consp (s-aux a v r)))
  :hints (("goal" :in-theory (enable rcdp s-aux)))
  :rule-classes ((:forward-chaining :trigger-terms ((s-aux a v r)))
                 (:rewrite :backchain-limit-lst 1)))

(defthm s-preserves-rcdp-nil
  (implies (and (syntaxp (quotep a))
                a)
           (rcdp (s a v nil)))
  :hints (("goal" :in-theory (enable s ifrp rcdp s-aux acl2->rcd rcd->acl2)))
  :rule-classes ((:forward-chaining :trigger-terms ((s a v nil)))
                 (:rewrite)))

(defthmd s-preserves-rcdp
  (implies (and a v (rcdp r))
           (rcdp (s a v r)))
  :hints (("goal" :in-theory
           (enable s ifrp rcdp s-aux acl2->rcd rcd->acl2)))
  :rule-classes ((:forward-chaining :trigger-terms ((s a v r)))
                 (:rewrite)))

(defthm s-nil-no-op
  (implies (and (rcdp r) (not (g a r)))
           (equal (s a nil r) r))
  :hints (("goal" :in-theory
           (enable s ifrp rcdp s-aux acl2->rcd rcd->acl2
                   g g-aux)))
  :rule-classes ((:forward-chaining :trigger-terms ((s a nil r)))
                 (:rewrite)))

(defthm s-preserves-rcdp2
  (implies (and a (rcdp r) (not (g a r)))
           (rcdp (s a v r)))
  :hints (("goal" :in-theory
           (enable s ifrp rcdp s-aux acl2->rcd rcd->acl2
                   g g-aux)))
  :rule-classes ((:forward-chaining :trigger-terms ((s a v r)))
                 (:rewrite)))

(defthm rcd->acl2-preserves-rcdp-tag
  (implies (not (ifrp r))
           (and (rcdp (rcd->acl2 r))
                (not (ifrp (rcd->acl2 r)))))
  :hints (("goal" :in-theory (enable ifrp rcdp acl2->rcd rcd->acl2)))
  :rule-classes ((:forward-chaining :trigger-terms ((rcd->acl2 r)))
                 (:rewrite :backchain-limit-lst 1)))

(defthm s-aux-preserves-not-ifrp
  (implies (and a
                v
                (not (ifrp r)))
           (not (ifrp (s-aux a v r))))
  :hints (("goal" :in-theory (enable s ifrp s-aux rcdp rcd->acl2 acl2->rcd))))


(defthm g-aux-ifrp 
  (implies (and (g-aux *tag* r) (rcdp r))
           (not (ifrp r)))
  :hints (("goal" :in-theory (enable g g-aux s ifrp s-aux rcdp rcd->acl2 acl2->rcd)))
  :rule-classes ((:forward-chaining :trigger-terms ((g-aux *tag* r)))
                 (:rewrite :backchain-limit-lst 1)))

(defthm s-aux-preserves-not-ifrp-tag
  (implies (and (not (equal a *tag*))
                (rcdp r)
                (or (g *tag* (s-aux a v r))
                    (g *tag* r)))
           (and (not (ifrp (s-aux a v r)))
                (rcdp (s-aux a v r))))
  :hints (("goal" :in-theory (enable g g-aux s ifrp s-aux rcdp rcd->acl2 acl2->rcd)))
  :rule-classes ((:forward-chaining :trigger-terms ((s-aux a v r)))
                 (:rewrite :backchain-limit-lst 1)))

(defthm s-preserves-rcdp-tag
  (implies (and (not (equal a *tag*))
                (rcdp r)
                (or (g *tag* (s a v r))
                    (g *tag* r)))
           (and (not (ifrp (s a v r)))
                (rcdp (s a v r))))
  :hints (("goal" :in-theory (enable g g-aux s ifrp rcdp s-aux acl2->rcd
                                     rcd->acl2)))
  :rule-classes ((:forward-chaining :trigger-terms ((rcdp (s a v r))))
                 (:rewrite :backchain-limit-lst 2)))

(defthm s-non-nil-val-is-consp
  (implies (and a v (rcdp r))
           (consp (s a v r)))
  :rule-classes ((:forward-chaining :trigger-terms ((s a v r)))
                 (:rewrite :backchain-limit-lst 1))
  :hints (("goal" :in-theory (enable s ifrp s-aux rcdp rcd->acl2 acl2->rcd))))

(defthm field-not-empty-implies-record-not-empty1
  (implies (and (g a x) a)
           (consp x))
  :hints (("goal" :in-theory (enable s g g-aux s-aux acl2->rcd)))
  :rule-classes (:forward-chaining))

(defthm tag-not-empty-implies-record-not-empty1
  (implies (g *tag* x)
           (consp x))
  :hints (("goal" :in-theory (enable s g g-aux s-aux acl2->rcd)))
  :rule-classes ((:forward-chaining)))

#|
(defthm establish-g-s
  (implies (and (syntaxp (quotep a))
                a)
           (g *tag* (s *tag* a r)))
  :rule-classes ((:forward-chaining :trigger-terms ((s *tag* a r)))))
|#

(defthmd s-diff-entry-non-empty-good-map-is-consp1
  (implies (and a
                (g a (s b v r)))
           (consp (s b v r)))
  :hints (("goal" :use ((:instance field-not-empty-implies-record-not-empty1
                                   (x (s b v r))))
           :in-theory (enable s g g-aux s-aux rcd->acl2 acl2->rcd rcdp ifrp)))
  :rule-classes ((:forward-chaining :trigger-terms ((s b v r)))
                 (:rewrite :backchain-limit-lst 1)))

(defthm s-diff-entry-non-empty-tag-is-consp1
  (implies (g *tag* (s b v r))
           (consp (s b v r)))
  :rule-classes ((:forward-chaining)
                 (:rewrite :backchain-limit-lst 1)))

(defthmd s-diff-entry-non-empty-good-map-is-consp2
  (implies (and a
                (not (equal a b))
                (g a r))
           (consp (s b v r)))
  :hints (("goal" :use ((:instance field-not-empty-implies-record-not-empty1
                                   (x (s b v r))))))
  :rule-classes ((:forward-chaining :trigger-terms ((s b v r)))
                 (:rewrite :backchain-limit-lst 1)))

(defthmd s-diff-entry-tag-is-consp
  (implies (and (g *tag* r)
                (or (not (equal b *tag*))
                    v))
           (consp (s b v r)))
  :hints (("goal"
           :use ((:instance s-diff-entry-non-empty-good-map-is-consp2
                            (a *tag*)))
           :in-theory (enable s g g-aux s-aux rcd->acl2 acl2->rcd)))
  :rule-classes ((:forward-chaining :trigger-terms ((s b v r)))
                 (:rewrite :backchain-limit-lst 1)))

(defthmd s-diff-entry-non-empty-good-map-is-non-nil
  (implies (and (g a r)
                a
                (not (equal a b))) 
           (s b v r))
  :hints (("goal" :use ((:instance s-diff-entry-non-empty-good-map-is-consp2))))
  :rule-classes ((:forward-chaining :trigger-terms ((s b v r)))
                 (:rewrite :backchain-limit-lst 1)))

(defthmd s-diff-entry-tag-is-non-nil
  (implies (and (g *tag* r)
                (not (equal b *tag*))) 
           (s b v r))
  :hints (("goal" :use ((:instance s-diff-entry-non-empty-good-map-is-consp2))))
  :rule-classes ((:forward-chaining :trigger-terms ((s b v r)))
                 (:rewrite :backchain-limit-lst 1)))

(defthm non-empty-good-map-fc
  (implies (rcdp v1)
           (and (implies v1 (consp v1))
                (implies (car v1) (consp (car v1)))))
  :hints (("goal" :in-theory (enable rcdp)))
  :rule-classes :forward-chaining)

(in-theory (disable rcdp))
