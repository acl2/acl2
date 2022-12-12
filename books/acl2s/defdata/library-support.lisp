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

 mset-diff-mset1/2 are rules that replaces acl2::mset-diff-mset,
 acl2::mset-diff-mset is a rule that has a loop-stopper and the
 behavior of loop-stoppers makes it hard to determine how ss are
 rewritten, so the only point of defdata-mset-diff-mset is to get rid
 of that loop stopper and add more predictable behavior.

 For example, with mset-diff-mset

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
  (<= (acl2-count (mget k r))
      (acl2-count r))
  :hints (("goal" :in-theory
           (enable minimal-records-theory)))
  :rule-classes :linear)

(defun good-map (x)
  (recordp x))

(defun non-empty-good-map (x)
  (declare (xargs :guard t))
  (and (consp x)
       (recordp x)))

(defthm records-acl2-count-linear-arith-<
  (implies (mget k r)
           (< (acl2-count (mget k r))
              (acl2-count r)))
  :hints (("goal" :in-theory 
           (enable minimal-records-theory)))
  :rule-classes :linear)

(defthm records-acl2-count
  (implies (consp r)
           (< (acl2-count (mget k r))
              (acl2-count r)))
  :hints (("goal" :in-theory
           (enable minimal-records-theory)))
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
  (implies (recordp r)
           (equal (mset k (mget k r) (map-identity2 k r))
                  r))
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

(defthm mset-aux-consp
  (implies v
           (consp (mset a v r)))
  :hints (("goal" :in-theory
           (enable minimal-records-theory)))
  :rule-classes ((:forward-chaining :trigger-terms ((mset a v r)))
                 (:rewrite :backchain-limit-lst 1)))

(defthm s-nil-no-op
  (implies (and (force (recordp r)) (not (mget a r)))
           (equal (mset a nil r) r))
  :hints (("goal" :in-theory
           (enable minimal-records-theory)))
  :rule-classes ((:forward-chaining :trigger-terms ((mset a nil r)))
                 (:rewrite :backchain-limit-lst 1)))

(defthm field-not-empty-implies-record-not-empty1
  (implies (mget a r)
           (consp r))
  :hints (("goal" :in-theory
           (enable minimal-records-theory)))
  :rule-classes ((:forward-chaining)
                 (:rewrite :backchain-limit-lst 0)))

(defthmd s-diff-entry-non-empty-good-map-is-consp2
  (implies (and (not (equal a b))
                (mget a r))
           (consp (mset b v r)))
  :hints (("goal"
           :in-theory
           (enable mset mget recordp no-nil-val-alistp
                   ordered-unique-key-alistp)))
  :rule-classes ((:forward-chaining :trigger-terms ((mset b v r)))
                 (:rewrite :backchain-limit-lst 1)))

(defthmd s-diff-entry-non-empty-good-map-is-consp-tag
  (implies (and (not (equal *tag* b))
                (mget *tag* r))
           (consp (mset b v r)))
  :hints (("goal"
           :in-theory
           (enable mset mget recordp no-nil-val-alistp
                   ordered-unique-key-alistp)))
  :rule-classes ((:forward-chaining :trigger-terms ((mset b v r)))
                 (:rewrite :backchain-limit-lst 1)))

(defthmd s-diff-entry-non-empty-good-map-is-non-nil
  (implies (and (mget a r)
                (not (equal a b))) 
           (mset b v r))
  :hints (("goal" :use
           ((:instance s-diff-entry-non-empty-good-map-is-consp2))))
  :rule-classes ((:forward-chaining :trigger-terms ((mset b v r)))
                 (:rewrite :backchain-limit-lst 1)))

(defthmd s-diff-entry-tag-is-non-nil
  (implies (and (mget *tag* r)
                (not (equal b *tag*))) 
           (mset b v r))
  :rule-classes ((:forward-chaining :trigger-terms ((mset b v r)))
                 (:rewrite :backchain-limit-lst 1)))

(defthm non-empty-record-consp
  (implies (and (recordp r) r)
           (consp r))
  :hints (("goal" :in-theory (enable recordp)))
  :rule-classes ((:forward-chaining)))

(defthm non-empty-record-consp-car
  (implies (and (recordp r) (car r))
           (consp (car r)))
  :hints (("goal" :in-theory (enable recordp)))
  :rule-classes ((:forward-chaining)))

