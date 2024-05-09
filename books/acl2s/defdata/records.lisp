#|


|#


(in-package "ACL2")
(include-book "misc/total-order" :dir :system)
(include-book "tools/flag" :dir :system)

; Basic definitions
(defun ordered-unique-key-alistp (a)
  (declare (xargs :guard (alistp a)))
  (or (null (cdr a))
      (and (<< (caar a) (caadr a))
           (ordered-unique-key-alistp (cdr a)))))

(defun no-nil-val-alistp (a)
  (declare (xargs :guard (alistp a)))
  (or (null a)
      (and (not (null (cdar a)))
           (no-nil-val-alistp (cdr a)))))

(defun recordp (r)
  (declare (xargs :guard t))
  (and (alistp r)
       (no-nil-val-alistp r)
       (ordered-unique-key-alistp r)))
        
(defun mget (a r)
  (declare (xargs :guard (recordp r)))
  (cond ((or (atom r)
             (<< a (caar r)))
         nil)
        ((equal a (caar r))
         (cdar r))
        (t (mget a (cdr r)))))

(defun mset-cons (a v r)
  (declare (xargs :guard (recordp r)))
  (if v (acons a v r) r))

(defun mset (a v r) 
  (declare (xargs :guard (recordp r)))
  (cond ((atom r) (mset-cons a v r))
        ((<< a (caar r)) (mset-cons a v r))
        ((equal a (caar r))
         (mset-cons a v (cdr r)))
        (t (cons (car r) (mset a v (cdr r))))))

; Rules about recordp, no-nil-val-alistp and ordered-unique-key-alistp
(defthm recordp-implies-true-listp
  (implies (recordp x)
           (true-listp x))
  :rule-classes ((:forward-chaining) (:compound-recognizer)))

(defthm recordp-implies-alistp
  (implies (recordp x)
           (alistp x))
  :rule-classes ((:forward-chaining)))

(defthm recordp-implies-no-nil-val-alistp
  (implies (recordp x)
           (no-nil-val-alistp x))
  :rule-classes ((:forward-chaining)))

(defthm mset-preserves-no-nil-val-alistp
  (implies (and (alistp r)
                (no-nil-val-alistp r))
           (no-nil-val-alistp (mset a v r)))
  :hints (("goal" :in-theory (enable <<))))

(defthm recordp-implies-ordered-unique-key-alistp
  (implies (recordp x)
           (ordered-unique-key-alistp x))
  :rule-classes ((:forward-chaining)))

(defthm mset-preserves-ordered-unique-key-alistp
  (implies (and (alistp r)
                (ordered-unique-key-alistp r))
           (ordered-unique-key-alistp (mset a v r)))
  :hints (("goal" :in-theory (enable <<))))

(defthm mset-preserves-recordp
  (implies (force (recordp r))
           (recordp (mset a v r))))

(defthm mset-preserves-record-nil
  (recordp (mset a v nil)))

(defthm record-<<-of-caar
  (implies (and (force (recordp r))
                (<< k a)
                (<< k (caar r))
                (mset a v r))
           (<< k (caar (mset a v r)))))

(defthm recordp-of-cons
  (implies (and (consp (double-rewrite e))
                (cdr e)
                (recordp s)
                (<< (car (double-rewrite e)) (caar (double-rewrite s))))
           (recordp (cons e s))))

; Rules about (mget ...)

(defthm mget-is-nil-for-<<
  (implies (<< a (caar r))
           (equal (mget a r) nil))
  :rule-classes :forward-chaining)

(defthm non-nil-if-mget-non-nil
  (implies (mget a r) r)
  :rule-classes :forward-chaining)

; To avoid if introduction we leave this disabled and hope that the
; other rules are enough. Turn this on if you find that they aren't.
(defthm mget-of-mset-expand
  (implies (force (recordp r))
           (equal (mget a (mset b v r))
                  (if (equal a b) v (mget a r)))))

(in-theory (disable mget-of-mset-expand))

(defthm mget-diff-mset
  (implies (and (force (recordp r))
                (not (equal a b)))
           (equal (mget a (mset b v r))
                  (mget a r))))

(defthm mget-same-mset
  (implies (force (recordp r))
           (equal (mget a (mset a v r))
                  v)))

(defthm mget-of-nil-is-nil
  (not (mget a nil)))

; Rules about (mset ...)

(defthm mset-non-nil-cannot-be-nil
  (implies v (mset a v r))
  :rule-classes ((:forward-chaining :trigger-terms ((mset a v r)))
                 (:rewrite :backchain-limit-lst 1)))

(defthm mset-same-mget
  (implies (force (recordp r))
           (equal (mset a (mget a r) r)
                  r)))

;; Instead of mset-diff-mset, I have the two following rules.

(defthm mset-diff-mset
  (implies (and (force (recordp r))
                (not (equal a b)))
           (equal (mset b y (mset a x r))
                  (mset a x (mset b y r))))
  :rule-classes nil)
; The rule classes to use if you really wanted the above rule
; :rule-classes ((:rewrite :loop-stopper ((b a mset)))))


; This rule is here so that we get the mset-diff-mset behavior in all
; cases, where mset-diff-mset1 does not apply.
(defthm mset-diff-mset2
  (implies (and
            (syntaxp (or (not (quotep a)) (not (quotep b))))
            (force (recordp r))
            (not (equal a b)))
           (equal (mset b y (mset a x r))
                  (mset a x (mset b y r))))
  :rule-classes ((:rewrite :loop-stopper ((a b mset)))))

; If a and b are quoted objects, check the term-order by unquoting
; them. This is the only rule we should see in ACL2s/defdata since
; record fields are keywords.
(defthm mset-diff-mset1
  (implies (and
            (syntaxp (quotep a))
            (syntaxp (quotep b))
            (syntaxp (term-order (unquote a) (unquote b)))
            (force (recordp r))
            (not (equal a b)))
           (equal (mset b y (mset a x r))
                  (mset a x (mset b y r))))
  :rule-classes ((:rewrite :loop-stopper nil)))

(defthm mset-same-mset
  (implies (force (recordp r))
           (equal (mset a y (mset a x r))
                  (mset a y r))))

(defun msets-macro (r msets)
  (declare (xargs :guard (and (true-listp msets)
                              (evenp (len msets)))))
  (if (endp msets)
      r
    (msets-macro `(mset ,(car msets) ,(cadr msets) ,r)
                 (cddr msets))))

(defmacro msets (r &rest msets)
  (declare (xargs :guard (and (true-listp msets)
                              (evenp (len msets)))))
  (msets-macro r msets))

#|

;; Experimented with the following idea, which was to expand the
;; definition of recordp while still keeping around that the argument
;; is a record, using hide so that it doesn't continue to
;; expand. Something like that should be possible, but this seems to
;; not work.
(defthm recordp-def
  (equal (recordp x)
         (and (hide (recordp x))
              (alistp x)
              (no-nil-val-alistp x)
              (ordered-unique-key-alistp x)))
  :hints (("goal" :in-theory (e/d (flag::expand-all-hides) ())))
  :rule-classes ((:definition :controller-alist ((recordp t))
                              :install-body :normalize)))

(in-theory (disable recordp recordp-def))
|#

(in-theory (disable mset mget recordp ordered-unique-key-alistp
                    no-nil-val-alistp))

(deftheory minimal-records-theory
  '(recordp
    ordered-unique-key-alistp
    no-nil-val-alistp
    mset
    mget
    ))

(deftheory maximal-records-theory
  '(minimal-records-theory
    <<
    ))
