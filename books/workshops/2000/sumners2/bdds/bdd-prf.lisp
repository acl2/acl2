(in-package "ACL2")

(include-book "bdd-spec")

#|

    bdd-prf.lisp
    ~~~~~~~~~~~~

we now prove the bdd manager defined in the bdd-mgr.lisp book is
correct. We will show that a certain invariant is preserved by any
sequence of calls,

    (free-bdd;(ite-bdd + var-bdd)*)*

used to build bdds within the context of determining the equivalence
of two propositional formulae using the constant-time test eql-bdd.
We will show how this invariant (in conjunction with some lemmas about
reduced-ordered BDDs) will be sufficient to verify the correctness of
the function bdd-sat?. while this actually just shows that a particular
application of the bdd-mgr is correct, i can't imagine how the bdd-sat?
function could "hide" an error in the bdd-mgr.

   free-bdd (keep bmr) --> (lst bmr)
   ite-bdd (f g h bmr) --> (bdd bmr)
   var-bdd (n bmr) --> (bdd bmr)

   bdd-0 --> bdd
   bdd-1 --> bdd

   eql-bdd (f g) --> boolean

|#

;;;; this book only contains definitions used for proving theorems
;;;; about the "executable" functions in bdd-mr.lisp. Thus, we do not
;;;; expect to execute the functions in this book and as such, we will
;;;; not go through the overhead of verifying their guards.

(set-verify-guards-eagerness 0)

#|----------------------------------------------------------------------------|#

;;;; some simple theorems relating nth and update-nth. these theorems
;;;; are essentially the same as those used by Wilding, et.al. very handy!

(in-theory (enable nth update-nth))

(defthm nth-update-nth-diff
  (implies (not (equal (nfix n) (nfix m)))
           (equal (nth n (update-nth m v l)) (nth n l))))

(defthm nth-update-nth-same
  (implies (equal (nfix n) (nfix m))
           (equal (nth n (update-nth m v l)) v)))

(defthm update-nth-update-nth-same
  (equal (update-nth n v (update-nth n x l))
         (update-nth n v l)))

(defthm update-nth-update-nth-diff
  (implies (not (equal (nfix n) (nfix m)))
           (equal (update-nth n v (update-nth m x l))
                  (update-nth m x (update-nth n v l))))
  :rule-classes ((:rewrite :loop-stopper ((n m)))))

(in-theory (disable nth update-nth))


;;;; we also will prove some simple theorems about mv-nth and lists
;;;; and then turn off the definition of mv-nth (mainly for readability
;;;; and to keep from rewriting (mv-nth 0 x) to (car x) which then
;;;; doesn't match an existing rule).

(defthm mv-nth-0-reduce
  (equal (mv-nth 0 (list x y)) x))

(defthm mv-nth-1-reduce
  (equal (mv-nth 1 (list x y)) y))

(in-theory (disable mv-nth))



(defmacro uniq-tbl (x) `(nth 0 ,x))

(defmacro rslt-tbl (x) `(nth 1 ,x))

(defmacro new-id (x) `(nth 2 ,x))

#|----------------------------------------------------------------------------|#

;;;; BEGIN bdd-mgr invariant definition ;;;;

(defun flatten (tbl)
  (if (endp tbl) ()
    (append (first tbl)
            (flatten (rest tbl)))))

(defun in-tbl (e tbl)
  (and (consp tbl)
       (or (equal e (first tbl))
           (in-tbl e (rest tbl)))))

(defun consesp (lst)
  (or (atom lst)
      (and (consp (first lst))
           (consesp (rest lst)))))

(defun embedded (b tbl)
  (or (atom b)
      (and (in-tbl b tbl)
           (embedded (b-then b) tbl)
           (embedded (b-else b) tbl))))

(defun in-uniq-tbl (b bmr)
  (embedded b (flatten (uniq-tbl bmr))))

(defun contained (lst tbl)
  (or (endp lst)
      (and (embedded (first lst) tbl)
           (contained (rest lst) tbl))))

(defun no-match (id lst)
  (or (endp lst)
      (and (not (equal id (b-id (first lst))))
           (no-match id (rest lst)))))

(defun no-dup-ids (lst)
  (or (endp lst)
      (and (no-match (b-id (first lst)) (rest lst))
           (no-dup-ids (rest lst)))))

(defun no-node= (node lst)
  (or (endp lst)
      (and (not (bdd= node (first lst)))
           (no-node= node (rest lst)))))

(defun no-dup-nodes (lst)
  (or (endp lst)
      (and (no-node= (first lst) (rest lst))
           (no-dup-nodes (rest lst)))))

(defun ids-bounded (lst N)
  (or (endp lst)
      (and (< (b-id (first lst)) N)
           (ids-bounded (rest lst) N))))

(defun is-a-result (rslt)
  (bdd= (ite-rslt rslt)
        (ite-spec (ite-f rslt)
                  (ite-g rslt)
                  (ite-h rslt))))

(defun ite-results (lst)
  (or (endp lst)
      (and (or (not (first lst))
               (is-a-result (first lst)))
           (ite-results (rest lst)))))

(defun rslt-contained (rslt tbl)
  (and (embedded (ite-f rslt) tbl)
       (embedded (ite-g rslt) tbl)
       (embedded (ite-h rslt) tbl)
       (embedded (ite-rslt rslt) tbl)))

(defun rslts-contained (lst tbl)
  (or (endp lst)
      (and (or (not (first lst))
               (rslt-contained (first lst) tbl))
           (rslts-contained (rest lst) tbl))))

(defun bdd-code (bdd)
  (id-hash (b-test bdd)
           (bdd-id (b-then bdd))
           (bdd-id (b-else bdd))))

(defthm bdd-code-is-natp
  (natp (bdd-code bdd))
  :rule-classes :type-prescription)

(defun each-has-code (lst n)
  (or (endp lst)
      (and (equal (bdd-code (first lst)) n)
           (each-has-code (rest lst) n))))

(defun codes-match (tbl n)
  (or (endp tbl)
      (and (each-has-code (first tbl) n)
           (codes-match (rest tbl) (1+ n)))))

(defpred uniq-tbl-inv (bmr)
  (let ((uniq-lst (flatten (uniq-tbl bmr)))
        (rslt-lst (rslt-tbl bmr)))
    (and (integerp (new-id bmr))
         (consesp uniq-lst)
         (codes-match (uniq-tbl bmr) 0)
         (no-dup-ids uniq-lst)
         (no-dup-nodes uniq-lst)
         (contained uniq-lst uniq-lst)
         (ids-bounded uniq-lst (new-id bmr))
         (rslts-contained rslt-lst uniq-lst))))

(defpred bdd-mgr-inv (bmr)
  (and (uniq-tbl-inv bmr)
       (ite-results (rslt-tbl bmr))))

;;;; END bdd-mgr invariant definition ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN "eql-bdd" function ;;;;

(in-theory (enable eql-bdd))

(defthm no-dup-ids-membership
  (implies (and (no-dup-ids lst)
                (in-tbl f lst)
                (in-tbl g lst)
                (equal (b-id f) (b-id g)))
           (equal f g))
  :rule-classes nil)

(defthm no-dup-nodes-implies-not-bdd=
  (implies (and (no-dup-nodes lst)
                (in-tbl f lst)
                (in-tbl g lst)
                (not (equal f g)))
           (not (bdd= f g)))
  :rule-classes nil)

(in-theory (enable bdd=))

(defthm eql-bdd-is-correct
  (implies (and (uniq-tbl-inv bmr)
                (in-uniq-tbl f bmr)
                (in-uniq-tbl g bmr))
           (equal (eql-bdd f g) (bdd= f g)))
  :hints (("Goal"
           :in-theory (disable flatten)
           :use ((:instance no-dup-ids-membership
                            (lst (flatten (uniq-tbl bmr))))
                 (:instance no-dup-nodes-implies-not-bdd=
                            (lst (flatten (uniq-tbl bmr))))))))

(in-theory (disable bdd=))

(in-theory (disable eql-bdd))

;;;; END "eql-bdd" function ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN unique-tbl functions ;;;;

(in-theory (enable get-unique))

;;;; lemmas needed for the case where we find a match in unique table

(defthm in-tbl-append-skip-over
  (implies (in-tbl e y)
           (in-tbl e (append x y))))

(defthm in-tbl-append-pop-top
  (implies (in-tbl e x)
           (in-tbl e (append x y))))

(defthm in-tbl-bdd-match
  (implies (bdd-match v l r x)
           (in-tbl (bdd-match v l r x) x)))

(defthm in-tbl-consesp-implies-consp
  (implies (and (consesp x)
                (in-tbl e x))
           (consp e)))

(defthm bdd-match-is-in-flattened-tbl
  (implies (bdd-match v l r (nth n x))
           (in-tbl (bdd-match v l r (nth n x))
                   (flatten x)))
  :hints (("Goal"
           :in-theory (enable (:induction nth))
           :induct (nth n x)
           :expand (nth n x))))

(defthm contained-and-in-tbl-embedded-free
  (implies (and (contained x y)
                (in-tbl e x))
           (embedded e y))
  :rule-classes nil)

(defthm contained-and-in-tbl-implies-embedded
  (implies (and (contained x x)
                (in-tbl e x))
           (embedded e x))
  :hints (("Goal" :use
           (:instance contained-and-in-tbl-embedded-free
                      (y x)))))

(defthm embedded-bdd-match-uniq-tbl-inv
  (let ((bdd (bdd-match v l r (nth n (uniq-tbl bmr)))))
    (implies (and (uniq-tbl-inv bmr)
                  bdd)
             (embedded bdd (flatten (uniq-tbl bmr))))))

(defthm embedded-implies-embedded-then-else
  (implies (embedded b x)
           (and (embedded (b-then b) x)
                (embedded (b-else b) x))))

(defthm bdd-match-returns-equivalent-bdd
  (let ((bdd (bdd-match v g h lst)))
    (implies bdd
             (and (equal (b-test bdd) v)
                  (eql-bdd (b-then bdd) g)
                  (eql-bdd (b-else bdd) h))))
  :hints (("Goal" :in-theory (enable eql-bdd)))
  :rule-classes nil)

(defthm bdd-match-returns-in-uniq-tbl
  (let ((bdd (bdd-match v g h (nth n (uniq-tbl bmr)))))
    (implies (and (uniq-tbl-inv bmr)
                  bdd)
             (and (in-uniq-tbl (b-then bdd) bmr)
                  (in-uniq-tbl (b-else bdd) bmr))))
  :hints (("Goal" :in-theory (disable embedded))))

(defthm bdd-match-is-bdd=-vgh
  (implies (and (uniq-tbl-inv bmr)
                (in-uniq-tbl g bmr)
                (in-uniq-tbl h bmr)
                (bdd-match v g h (nth n (uniq-tbl bmr))))
           (bdd= (bdd-match v g h (nth n (uniq-tbl bmr)))
                 (b-node 'if v g h)))
  :hints (("Goal" :in-theory (enable bdd= b-node)
           :use (:instance bdd-match-returns-equivalent-bdd
                           (lst (nth n (uniq-tbl bmr)))))))

;;;; lemmas needed for case where we don't find a match in the unique tbl

(defun len-count (n tbl)
  (if (zp n) 0
    (+ (len (first tbl))
       (len-count (1- n) (rest tbl)))))

(defun inject-at (n e lst)
  (if (zp n) (cons e lst)
    (cons (first lst)
          (inject-at (1- n) e (rest lst)))))

(defthm trivial-factoid1
  (implies (and (integerp n)
                (integerp k)
                (integerp m))
           (equal (+ (- k) m k n) (+ m n))))

(defthm inject-at-skip-over-1
  (implies (and (integerp n) (>= n 0)
                (integerp m) (>= m 0))
           (equal (inject-at (+ m 1 n) e (cons x y))
                  (cons x (inject-at (+ m n) e y)))))

(defthm inject-at-append-reduce
  (implies (and (integerp n) (>= n 0))
           (equal (inject-at (+ (len x) n) e (append x y))
                  (append x (inject-at n e y)))))

(defthm update-nth-cons-nth-reduction
  (equal (flatten (update-nth n (cons e (nth n x)) x))
         (inject-at (len-count n x) e (flatten x)))
  :hints (("Goal" :in-theory (enable update-nth nth))))

(defthm len-count<=len-flatten
  (<= (len-count n x) (len (flatten x)))
  :rule-classes :linear)

(defthm in-tbl-unaffected-by-injection
  (implies (in-tbl e x)
           (in-tbl e (inject-at n b x))))

(defthm embedded-unaffected-by-injection
  (implies (embedded e x)
           (embedded e (inject-at n b x))))

(defthm contained-unaffected-by-injection
  (implies (contained x y)
           (contained x (inject-at n b y))))

(defthm inject-at-preserves-containment
  (implies (and (contained x y)
                (embedded b y)
                (<= n (len x)))
           (contained (inject-at n b x) y)))

(defthm in-tbl-inject-at-n
  (in-tbl b (inject-at n b x)))

(defun inject-induct (n x)
  (if (endp x) n (inject-induct (1- n) (cdr x))))

(defthm inject-at-preserves-ids-bounded
  (implies (and (ids-bounded x id)
                (<= n (len x))
                (integerp id))
           (ids-bounded (inject-at n (b-node id v g h) x)
                        (1+ id)))
  :hints (("Goal" :induct (inject-induct n x)
           :in-theory (enable b-node))))

(defthm ids-bounded-implies-no-match
  (implies (ids-bounded x id)
           (no-match id x)))

(defthm no-match-implies-no-match-inject-at
  (implies (and (no-match a x)
                (not (equal a id))
                (<= n (len x)))
           (no-match a (inject-at n (b-node id v g h) x)))
  :hints (("Goal" :induct (inject-induct n x)
           :in-theory (enable b-node))))

(defthm inject-at-preserves-no-dup-ids
  (implies (and (ids-bounded x id)
                (integerp id)
                (no-dup-ids x)
                (<= n (len x)))
           (no-dup-ids (inject-at n (b-node id v g h) x)))
  :hints (("Subgoal *1/1" :in-theory (enable b-node))))

(defthm inject-at-preserves-results-contained
  (implies (rslts-contained lst tbl)
           (rslts-contained lst (inject-at n (b-node id v g h) tbl))))

(defthm inject-at-preserves-consesp
  (implies (and (consesp tbl)
                (<= n (len tbl)))
           (consesp (inject-at n (b-node id v g h) tbl))))

(defthm no-node=-implies-no-node=-inject-at
  (implies (and (no-node= a x)
                (not (bdd= a b))
                (<= n (len x)))
           (no-node= a (inject-at n b x)))
  :hints (("Goal" :induct (inject-induct n x))))

(defthm inject-at-preserves-no-dup-nodes
  (implies (and (no-node= b x)
                (no-dup-nodes x)
                (<= n (len x)))
           (no-dup-nodes (inject-at n b x))))

(defthm trivial-factoid3
  (implies (and (integerp m) (integerp n) (integerp k))
           (equal (+ k m (- k) n) (+ m n))))

(defun codes-match-induct (tbl m n)
  (cond ((zp n) m)
        ((endp tbl) (codes-match-induct tbl (1+ m) (1- n)))
        (t (codes-match-induct (rest tbl) (1+ m) (1- n)))))

(in-theory (disable bdd-code))

(defthm codes-match-update-nth-free
  (implies (and (codes-match tbl m)
                (natp m) (natp n)
                (each-has-code lst (+ m n)))
           (codes-match (update-nth n lst tbl) m))
  :hints (("Goal" :in-theory (enable update-nth)
           :induct (codes-match-induct tbl m n)))
  :rule-classes nil)

(defthm codes-match-update-nth
  (implies (and (codes-match tbl 0) (natp n)
                (each-has-code lst n))
           (codes-match (update-nth n lst tbl) 0))
  :hints (("Goal" :use
           (:instance codes-match-update-nth-free
                      (m 0)))))

(defthm nth-codes-match-each-has-code-free
  (implies (and (codes-match tbl m)
                (natp m) (natp n))
           (each-has-code (nth n tbl) (+ m n)))
  :hints (("Goal" :in-theory (enable nth)
           :induct (codes-match-induct tbl m n)))
  :rule-classes nil)

(defthm nth-codes-match-each-has-code
  (implies (and (codes-match tbl 0) (natp n))
           (each-has-code (nth n tbl) n))
  :hints (("Goal" :use
           (:instance nth-codes-match-each-has-code-free
                      (m 0)))))

(defun no-node-eql (v l r lst)
  (or (endp lst)
      (and (not (node-eql v l r (first lst)))
           (no-node-eql v l r (rest lst)))))

(defthm each-has-code-implies-no-match
  (let ((code (bdd-code (b-node 'if v l r))))
    (implies (and (each-has-code lst n)
                  (not (equal n code)))
             (no-node-eql v l r lst)))
  :hints (("Goal"
           :induct (no-node-eql v l r lst)
           :in-theory (enable eql-bdd bdd-code bdd-id b-node))))

(defthm no-node-eql-append-reduce
  (equal (no-node-eql v l r (append x y))
         (and (no-node-eql v l r x)
              (no-node-eql v l r y))))

(in-theory (disable node-eql b-node))

(defthm codes-match-doesnt-change-no-node-eql
  (let ((code (bdd-code (b-node 'if v l r))))
    (implies (and (codes-match tbl m) (natp m)
                  (> m code))
             (no-node-eql v l r (flatten tbl)))))

(defthm trivial-factoid4
  (implies (and (integerp m) (integerp n) (integerp k))
           (equal (+ (- (+ k m)) n) (+ (- k) (- m) n))))

(defun fixed-match-induct (m code tbl)
  (declare (xargs :measure (acl2-count tbl)))
  (cond ((endp tbl) tbl)
        ((equal code m) tbl)
        ((zp (- code m)) tbl)
        (t (fixed-match-induct (1+ m) code (cdr tbl)))))

(defthm codes-match-no-node-eql-to-nth-free
  (let ((code (bdd-code (b-node 'if v l r))))
    (implies (and (codes-match tbl m) (natp m))
             (equal (no-node-eql v l r (flatten tbl))
                    (no-node-eql v l r (nth (- code m) tbl)))))
  :hints (("Goal" :in-theory (enable nth)
           :induct (fixed-match-induct m (bdd-code (b-node 'if v l r)) tbl)))
  :rule-classes nil)

(defthm codes-match-no-node-eql-to-nth
  (let ((code (bdd-code (b-node 'if v l r))))
    (implies (codes-match tbl 0)
             (equal (no-node-eql v l r (flatten tbl))
                    (no-node-eql v l r (nth code tbl)))))
  :hints (("Goal" :use
           (:instance codes-match-no-node-eql-to-nth-free
                      (m 0)))))

(defthm bdd=-b-node-node-eql-under-uniq-tbl
  (implies (and (uniq-tbl-inv bmr)
                (in-uniq-tbl l bmr)
                (in-uniq-tbl r bmr)
                (in-uniq-tbl x bmr)
                (consp x))
           (equal (bdd= (b-node 'if v l r) x)
                  (node-eql v l r x)))
  :hints (("Goal" :in-theory
           (enable node-eql b-node bdd=))))

(defthm in-uniq-tbl-definition-forward-chain
  (implies (embedded x (flatten (uniq-tbl bmr)))
           (in-uniq-tbl x bmr))
  :rule-classes :forward-chaining)

(in-theory (disable in-uniq-tbl))

(defthm uniq-tbl-inv-no-node=-no-node-eql
  (implies (and (uniq-tbl-inv bmr)
                (in-uniq-tbl l bmr)
                (in-uniq-tbl r bmr)
                (consesp lst)
                (contained lst (flatten (uniq-tbl bmr))))
           (equal (no-node= (b-node 'if v l r) lst)
                  (no-node-eql v l r lst)))
  :hints (("Goal" :in-theory (disable b-node embedded node-eql))))

(defthm implies-not-bdd-match-no-node-eql
  (implies (and (consesp lst)
                (not (bdd-match v l r lst)))
           (no-node-eql v l r lst)))

(defthm consesp-append-distribute
  (equal (consesp (append x y))
         (and (consesp x) (consesp y))))

(defthm consesp-flatten-x-implies-consesp-nth
  (implies (consesp (flatten tbl))
           (consesp (nth n tbl)))
  :hints (("Goal" :induct (nth n tbl)
           :in-theory (enable nth))))

(defthm bdd-code-nth-2-bdd-code
  (equal (bdd-code (b-node (nth 2 bmr) v g h))
         (bdd-code (b-node 'if v g h)))
  :hints (("Goal" :in-theory (enable bdd-code b-node))))

(defthm bdd=-for-equivalent-b-nodes
  (bdd= (b-node (nth 2 bmr) v g h)
        (b-node 'if v g h))
  :hints (("Goal" :in-theory (enable bdd= b-node))))

(defcong bdd= equal (no-node= x y) 1)

(defthm uniq-tbl-inv-and-not-bdd-match-implies-no-node=
  (let* ((node (b-node (nth 2 bmr) v l r))
         (code (bdd-code node)))
    (implies (and (uniq-tbl-inv bmr)
                  (in-uniq-tbl l bmr)
                  (in-uniq-tbl r bmr)
                  (not (bdd-match v l r (nth code (uniq-tbl bmr)))))
             (no-node= node (flatten (uniq-tbl bmr))))))

(defthm bdd-hash-code-into-b-node
  (equal (bdd-hash-code v (bdd-id g) (bdd-id h) (table-size))
         (bdd-code (b-node 'if v g h)))
  :hints (("Goal" :in-theory (enable bdd-code b-node))))

(defthm consp-forward-chain-embedded
  (implies (not (consp x)) (equal (embedded x y) t))
  :hints (("Goal" :in-theory (enable in-uniq-tbl embedded)))
  :rule-classes :type-prescription)

(defthm embedded-b-node-back-chain
  (implies (and (embedded g y) (embedded h y)
                (in-tbl (b-node id v g h) y))
           (embedded (b-node id v g h) y))
  :hints (("Goal" :in-theory (enable embedded b-node))))

(defthm get-unique-preserves-uniq-tbl-inv
  (implies (and (uniq-tbl-inv bmr)
                (in-uniq-tbl g bmr)
                (in-uniq-tbl h bmr))
           (mv-let (b nbm)
               (get-unique v g h bmr)
             (and (uniq-tbl-inv nbm)
                  (in-uniq-tbl b nbm)
                  (bdd= b (b-node 'if v g h)))))
  :hints (("Goal" :in-theory (enable in-uniq-tbl uniq-tbl-inv)))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((get-unique v g h bmr)))
                 :rewrite))

(defthm get-unique-preserves-ite-results
  (implies (ite-results (rslt-tbl bmr))
           (ite-results (rslt-tbl (mv-nth 1 (get-unique v g h bmr)))))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((get-unique v g h bmr)))
                 :rewrite))

(defthm get-unique-preserves-in-uniq-tbl
  (implies (in-uniq-tbl b bmr)
           (in-uniq-tbl b (mv-nth 1 (get-unique v g h bmr))))
  :hints (("Goal" :in-theory (enable in-uniq-tbl)))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((mv-nth 1 (get-unique v g h bmr))))
                 :rewrite))

(in-theory (disable get-unique))

;;;; END unique-tbl function ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN "var-bdd" function ;;;;

(in-theory (enable var-bdd))

(in-theory (enable in-uniq-tbl))

(defthm in-uniq-tbl-t (in-uniq-tbl t bmr))
(defthm in-uniq-tbl-nil (in-uniq-tbl nil bmr))

(in-theory (disable in-uniq-tbl))

(defthm var-bdd-is-correct
  (implies (bdd-mgr-inv bmr)
           (mv-let (f nbm)
               (var-bdd n bmr)
             (and (bdd-mgr-inv nbm)
                  (in-uniq-tbl f nbm)
                  (bdd= f (b-node 'if n t nil)))))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((var-bdd n bmr)))
                 :rewrite))

(defthm var-bdd-preserves-in-uniq-tbl
  (implies (in-uniq-tbl b bmr)
           (in-uniq-tbl b (mv-nth 1 (var-bdd n bmr))))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((mv-nth 1 (var-bdd n bmr))))
                 :rewrite))

(in-theory (disable var-bdd))

;;;; END "var-bdd" function ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN result-tbl functions ;;;;

(in-theory (enable find-result set-result))

(in-theory (enable nth))

(defthm nth-ite-results-is-a-result
  (implies (and (ite-results lst) (nth n lst))
           (is-a-result (nth n lst)))
  :hints (("Goal" :in-theory (disable is-a-result)))
  :rule-classes nil)

(defthm nth-results-contained-is-contained
  (implies (and (nth n lst) (rslts-contained lst tbl))
           (rslt-contained (nth n lst) tbl))
  :hints (("Goal" :in-theory (disable rslt-contained)))
  :rule-classes nil)

(in-theory (disable nth embedded))

(defthm find-result-returns-in-uniq-tbl
  (implies (and (uniq-tbl-inv bmr)
                (find-result f g h bmr))
           (in-uniq-tbl (ite-rslt (find-result f g h bmr)) bmr))
  :hints (("Goal" :in-theory (enable in-uniq-tbl)
           :use (:instance nth-results-contained-is-contained
                           (n (bdd-hash f g h))
                           (lst (rslt-tbl bmr))
                           (tbl (flatten (uniq-tbl bmr))))))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((find-result f g h bmr)))
                 :rewrite))

(in-theory (disable in-uniq-tbl))

(defthm find-result-returns-correct-result
  (implies (and (ite-results (rslt-tbl bmr))
                (uniq-tbl-inv bmr)
                (in-uniq-tbl f bmr)
                (in-uniq-tbl g bmr)
                (in-uniq-tbl h bmr)
                (find-result f g h bmr))
           (bdd= (ite-rslt (find-result f g h bmr))
                 (ite-spec f g h)))
  :hints (("Goal"
           :use ((:instance nth-ite-results-is-a-result
                            (n (bdd-hash f g h))
                            (lst (rslt-tbl bmr)))
                 (:instance nth-results-contained-is-contained
                            (n (bdd-hash f g h))
                            (lst (rslt-tbl bmr))
                            (tbl (flatten (uniq-tbl bmr)))))))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((find-result f g h bmr)))
                 :rewrite))

(in-theory (enable update-nth))

(defthm update-nth-is-a-result-ite-results
  (implies (ite-results lst)
           (equal (ite-results (update-nth n entry lst))
                  (is-a-result entry)))
  :hints (("Goal" :in-theory (disable is-a-result)))
  :rule-classes nil)

(defthm update-nth-rslt-contained-rslts-contained
  (implies (and (rslt-contained entry tbl)
                (rslts-contained lst tbl))
           (rslts-contained (update-nth n entry lst) tbl))
  :hints (("Goal" :in-theory (disable rslt-contained)))
  :rule-classes nil)

(in-theory (disable update-nth))

(in-theory (enable rslt-entry))

(defthm set-result-preserves-uniq-tbl-inv
  (implies (and (uniq-tbl-inv bmr)
                (in-uniq-tbl f bmr)
                (in-uniq-tbl g bmr)
                (in-uniq-tbl h bmr)
                (in-uniq-tbl rslt bmr))
           (uniq-tbl-inv (set-result f g h rslt bmr)))
  :hints (("Goal" :in-theory (enable in-uniq-tbl)
           :use (:instance update-nth-rslt-contained-rslts-contained
                           (n (bdd-hash f g h))
                           (lst (rslt-tbl bmr))
                           (tbl (flatten (uniq-tbl bmr)))
                           (entry (rslt-entry f g h rslt)))))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((set-result f g h rslt bmr)))
                 :rewrite))

(defthm set-result-preserves-ite-results
  (implies (ite-results (rslt-tbl bmr))
           (equal (ite-results (rslt-tbl (set-result f g h rslt bmr)))
                  (if (cacheable-resultp f g h)
                      (bdd= rslt (ite-spec f g h))
                    t)))
  :hints (("Goal" :in-theory (enable in-uniq-tbl)
           :use (:instance update-nth-is-a-result-ite-results
                           (n (bdd-hash f g h))
                           (lst (rslt-tbl bmr))
                           (entry (rslt-entry f g h rslt)))))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((set-result f g h rslt bmr)))
                 :rewrite))

(defthm set-result-preserves-in-uniq-tbl
  (implies (in-uniq-tbl b bmr)
           (in-uniq-tbl b (set-result f g h rslt bmr)))
  :hints (("Goal" :in-theory (enable in-uniq-tbl)))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((set-result f g h rslt bmr)))
                 :rewrite))

(in-theory (disable find-result set-result))

;;;; END result-tbl functions ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN "ite-bdd" functions ;;;;

(in-theory (enable ite-bdd then-node else-node in-uniq-tbl yes-no?))

(defthm then-node-forward-chain-in-uniq-tbl
  (implies (in-uniq-tbl x bmr)
           (in-uniq-tbl (then-node x v) bmr))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((then-node x v)))))

(defthm else-node-forward-chain-in-uniq-tbl
  (implies (in-uniq-tbl x bmr)
           (in-uniq-tbl (else-node x v) bmr))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((else-node x v)))))

(defthm yes-no?-forward-chain
  (implies (yes-no? g h)
           (and (equal g t) (not h)))
  :rule-classes :forward-chaining)

(in-theory (disable top-var then-node else-node in-uniq-tbl yes-no?))

(defthm ite-bdd-preserves-in-uniq-tbl
  (implies (in-uniq-tbl b bmr)
           (in-uniq-tbl b (mv-nth 1 (ite-bdd f g h bmr))))
  :hints (("Goal" :induct (ite-bdd f g h bmr)
           :expand (ite-bdd f g h bmr))))

(defthm ite-bdd-in-uniq-tbl-forward-chain
  (implies (and (in-uniq-tbl b bmr)
                (uniq-tbl-inv (mv-nth 1 (ite-bdd f g h bmr))))
           (in-uniq-tbl b (mv-nth 1 (ite-bdd f g h bmr))))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((in-uniq-tbl b bmr)))))

(defthm ite-bdd-preserves-uniq-tbl-inv
  (implies (and (uniq-tbl-inv bmr)
                (in-uniq-tbl f bmr)
                (in-uniq-tbl g bmr)
                (in-uniq-tbl h bmr))
           (mv-let (r nbm)
               (ite-bdd f g h bmr)
             (and (uniq-tbl-inv nbm)
                  (in-uniq-tbl r nbm))))
  :hints (("Goal" :induct (ite-bdd f g h bmr)))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((ite-bdd f g h bmr)))
                 :rewrite))

(defcong bdd= bdd= (b-node i v g h) 3
  :hints (("Goal" :in-theory (enable bdd= b-node))))

(defcong bdd= bdd= (b-node i v g h) 4
  :hints (("Goal" :in-theory (enable bdd= b-node))))

(defthm robdd-then-node-forward-chain
  (implies (robdd x) (robdd (then-node x u)))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((then-node x u)))))

(defthm robdd-else-node-forward-chain
  (implies (robdd x) (robdd (else-node x u)))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((else-node x u)))))

(defthm ite-spec-reduction-2-rewrite
  (implies (and (robdd f) (robdd g) (robdd h)
                (bdd= f g))
           (bdd= (ite-spec f g h)
                 (ite-spec f (bdd-1) h)))
  :hints (("Goal" :use (:instance ite-spec-reduction-2))))

(in-theory (disable eql-bdd-is-correct))

(defthm ite-bdd-returns-correct-result
  (implies (and (uniq-tbl-inv bmr)
                (ite-results (rslt-tbl bmr))
                (in-uniq-tbl f bmr)
                (in-uniq-tbl g bmr)
                (in-uniq-tbl h bmr)
                (robdd f) (robdd g) (robdd h))
           (mv-let (r nbm)
               (ite-bdd f g h bmr)
             (and (ite-results (rslt-tbl nbm))
                  (bdd= r (ite-spec f g h)))))
  :hints (("Goal" :induct (ite-bdd f g h bmr)
           :in-theory (enable ite-spec)
           :do-not '(generalize eliminate-destructors
                     fertilize eliminate-irrelevance))
          ("Subgoal *1/8"
           :use ((:instance
                  eql-bdd-is-correct
                  (f (mv-nth 0
                             (ite-bdd (then-node f (top-var f g h))
                                      (then-node g (top-var f g h))
                                      (then-node h (top-var f g h))
                                      bmr)))
                  (g (mv-nth 0
                             (ite-bdd (else-node f (top-var f g h))
                                      (else-node g (top-var f g h))
                                      (else-node h (top-var f g h))
                                      (mv-nth 1
                                              (ite-bdd (then-node f (top-var f g h))
                                                       (then-node g (top-var f g h))
                                                       (then-node h (top-var f g h))
                                                       bmr)))))
                  (bmr (mv-nth 1
                               (ite-bdd (else-node f (top-var f g h))
                                        (else-node g (top-var f g h))
                                        (else-node h (top-var f g h))
                                        (mv-nth 1
                                                (ite-bdd (then-node f (top-var f g h))
                                                         (then-node g (top-var f g h))
                                                         (then-node h (top-var f g h))
                                                         bmr))))))))
          ("Subgoal *1/6" :in-theory (enable eql-bdd-is-correct))
          ("Subgoal *1/5" :in-theory (enable eql-bdd-is-correct))
          ("Subgoal *1/4" :in-theory (enable eql-bdd-is-correct))))

(defthm ite-bdd-is-correct
  (implies (and (bdd-mgr-inv bmr)
                (in-uniq-tbl f bmr)
                (in-uniq-tbl g bmr)
                (in-uniq-tbl h bmr)
                (robdd f) (robdd g) (robdd h))
           (mv-let (r nbm)
               (ite-bdd f g h bmr)
             (and (bdd-mgr-inv nbm)
                  (in-uniq-tbl r nbm)
                  (bdd= r (ite-spec f g h))
                  (robdd r))))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((ite-bdd f g h bmr)))
                 :rewrite))

(in-theory (disable ite-bdd))

;;;; END "ite-bdd" functions ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN "init-bdd" functions ;;;;

(defun cleared-from (x n)
  (declare (xargs :measure (nfix (- (len x) n))))
  (or (zp (- (len x) n))
      (and (null (nth n x))
           (cleared-from x (1+ n)))))

(defthm trivial-factoid2
  (implies (and (integerp n)
                (integerp k))
           (equal (+ (- k) k n) n)))

(defthm reduce-nthcdr->=-len-x
  (implies (and (true-listp x)
                (natp n)
                (>= n (len x)))
           (equal (nthcdr n x) ())))

(defthm nthcdr-cdr-permute
  (equal (nthcdr n (cdr x))
         (cdr (nthcdr n x))))

(defthm equal-car-nthcdr-nth
  (equal (car (nthcdr n x))
         (nth n x))
  :hints (("Goal" :in-theory (enable nth))))

(defthm cleared-from-flatten-nthcdr-is-nil
  (implies (and (natp n)
                (true-listp x)
                (cleared-from x n))
           (equal (flatten (nthcdr n x)) ()))
  :rule-classes nil)

(defthm cleared-from-ite-results-nthcdr
  (implies (and (natp n)
                (true-listp x)
                (cleared-from x n))
           (ite-results (nthcdr n x)))
  :rule-classes nil)

(defthm cleared-from-rslts-contained-nthcdr
  (implies (and (natp n)
                (true-listp x)
                (cleared-from x n))
           (rslts-contained (nthcdr n x) u))
  :rule-classes nil)

(defthm cleared-from-codes-match-nthcdr
  (implies (and (natp n)
                (true-listp x)
                (cleared-from x n))
           (codes-match (nthcdr n x) n))
  :rule-classes nil)

(defthm init-uniq-tbl-update-nth-<
  (implies (and (natp m) (natp n) (< n m))
           (equal (nth n (uniq-tbl (init-uniq-tbl m bmr)))
                  (nth n (uniq-tbl bmr)))))

(defthm init-uniq-tbl-update-nth-reduce
  (implies (and (natp m) (natp n)
                (<= m n) (< n (table-size)))
           (not (nth n (uniq-tbl (init-uniq-tbl m bmr))))))

(defthm len-update-nth-redux
  (implies (and (natp n) (< n (len x)))
           (equal (len (update-nth n v x))
                  (len x))))

(defthm len-init-uniq-tbl-reduce
  (implies (and (natp n)
                (equal (len (uniq-tbl bmr)) (table-size)))
           (equal (len (uniq-tbl (init-uniq-tbl n bmr)))
                  (table-size))))

(defthm cleared-from-init-uniq-tbl-n
  (implies (and (bdd-mgrp bmr) (natp n)
                (< n (table-size)))
           (cleared-from (uniq-tbl (init-uniq-tbl 0 bmr)) n))
  :hints (("Goal" :in-theory (enable bdd-mgrp)))
  :rule-classes nil)

(defthm uniq-tblp-implies-true-listp
  (implies (uniq-tblp x) (true-listp x)))

(defthm bdd-mgrp-uniq-tbl-is-true-listp
  (implies (bdd-mgrp bmr)
           (true-listp (uniq-tbl bmr)))
  :hints (("Goal" :in-theory (enable bdd-mgrp))))

(defthm init-uniq-tbl-clears-flattened-tbl
  (implies (bdd-mgrp bmr)
           (equal (flatten (uniq-tbl (init-uniq-tbl 0 bmr))) ()))
  :hints (("Goal"
           :use ((:instance cleared-from-init-uniq-tbl-n (n 0))
                 (:instance cleared-from-flatten-nthcdr-is-nil
                            (x (uniq-tbl (init-uniq-tbl 0 bmr)))
                            (n 0))))))


(defthm init-rslt-tbl-update-nth-<
  (implies (and (natp m) (natp n) (< n m))
           (equal (nth n (rslt-tbl (init-rslt-tbl m bmr)))
                  (nth n (rslt-tbl bmr)))))

(defthm init-rslt-tbl-update-nth-reduce
  (implies (and (natp m) (natp n)
                (<= m n) (< n (table-size)))
           (not (nth n (rslt-tbl (init-rslt-tbl m bmr))))))

(defthm len-init-rslt-tbl-reduce
  (implies (and (natp n)
                (equal (len (rslt-tbl bmr)) (table-size)))
           (equal (len (rslt-tbl (init-rslt-tbl n bmr)))
                  (table-size))))

(defthm cleared-from-init-rslt-tbl-n
  (implies (and (bdd-mgrp bmr) (natp n)
                (< n (table-size)))
           (cleared-from (rslt-tbl (init-rslt-tbl 0 bmr)) n))
  :hints (("Goal" :in-theory (enable bdd-mgrp)))
  :rule-classes nil)

(defthm rslt-tblp-implies-true-listp
  (implies (rslt-tblp x) (true-listp x)))

(defthm bdd-mgrp-rslt-tbl-is-true-listp
  (implies (bdd-mgrp bmr)
           (true-listp (rslt-tbl bmr)))
  :hints (("Goal" :in-theory (enable bdd-mgrp))))
#|
(defthm implies-len-<=0-atom
  (implies (<= (len x) 0)
           (not (consp x)))
  :rule-classes :forward-chaining)
|#
(defthm implies-len-equal-0-atom
  (implies (equal (len x) 0)
           (not (consp x)))
  :rule-classes :forward-chaining)

(defthm init-rslt-tbl-has-ite-results
  (implies (bdd-mgrp bmr)
           (ite-results (rslt-tbl (init-rslt-tbl 0 bmr))))
  :hints (("Goal"
           :use ((:instance cleared-from-init-rslt-tbl-n (n 0))
                 (:instance cleared-from-ite-results-nthcdr
                            (x (rslt-tbl (init-rslt-tbl 0 bmr)))
                            (n 0))))))

(defthm init-rslt-tbl-has-rslts-contained
  (implies (bdd-mgrp bmr)
           (rslts-contained (rslt-tbl (init-rslt-tbl 0 bmr)) u))
  :hints (("Goal"
           :use ((:instance cleared-from-init-rslt-tbl-n (n 0))
                 (:instance cleared-from-rslts-contained-nthcdr
                            (x (rslt-tbl (init-rslt-tbl 0 bmr)))
                            (n 0))))))

(defthm init-uniq-tbl-has-codes-match
  (implies (bdd-mgrp bmr)
           (codes-match (uniq-tbl (init-uniq-tbl 0 bmr)) 0))
  :hints (("Goal"
           :use ((:instance cleared-from-init-uniq-tbl-n (n 0))
                 (:instance cleared-from-codes-match-nthcdr
                            (x (uniq-tbl (init-uniq-tbl 0 bmr)))
                            (n 0))))))

(defthm init-rslt-tbl-does-not-affect-uniq-tbl
  (equal (uniq-tbl (init-rslt-tbl n bmr))
         (uniq-tbl bmr)))

(defthm init-bdd-is-correct
  (implies (bdd-mgrp bmr)
           (bdd-mgr-inv (init-bdd bmr)))
  :hints (("Goal" :in-theory
           (enable init-bdd bdd-mgr-inv uniq-tbl-inv))))

(in-theory (disable init-bdd))

;;;; END "init-bdd" functions ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN "free-bdd" functions ;;;;

(defun each-in-uniq (lst bmr)
  (or (endp lst)
      (and (in-uniq-tbl (first lst) bmr)
           (each-in-uniq (rest lst) bmr))))

(defun pairwise-bdd= (x y)
  (if (endp x) (endp y)
    (and (not (endp y))
         (bdd= (first x) (first y))
         (pairwise-bdd= (rest x) (rest y)))))

(defthm rebuild-bdd-maintains-in-uniq-tbl
  (implies (in-uniq-tbl f bmr)
           (in-uniq-tbl f (mv-nth 1 (rebuild-bdd g bmr)))))

(defthm rebuild-bdd-is-correct
  (implies (bdd-mgr-inv bmr)
           (mv-let (g nbm)
               (rebuild-bdd f bmr)
             (and (in-uniq-tbl g nbm)
                  (bdd= g f)
                  (bdd-mgr-inv nbm))))
  :hints (("Goal" :in-theory
           (enable bdd-mgr-inv bdd= b-node))
          ("Subgoal *1/1" :in-theory
           (enable in-uniq-tbl))))

(defthm rebuild-bdds-maintains-in-uniq-tbl
  (implies (in-uniq-tbl f bmr)
           (in-uniq-tbl f (mv-nth 1 (rebuild-bdds keep bmr)))))

(defthm rebuild-bdds-is-correct
  (implies (bdd-mgr-inv bmr)
           (mv-let (copy nbm)
               (rebuild-bdds keep bmr)
             (and (each-in-uniq copy nbm)
                  (pairwise-bdd= keep copy)
                  (bdd-mgr-inv nbm)))))

(defthm free-bdd-is-correct
  (implies (bdd-mgrp bmr)
           (mv-let (rslt nbm)
               (free-bdd keep bmr)
             (and (each-in-uniq rslt nbm)
                  (pairwise-bdd= keep rslt)
                  (bdd-mgr-inv nbm)))))

;;;; END "free-bdd" functions ;;;;

#|----------------------------------------------------------------------------|#

;;;; BEGIN final verification ;;;;

;;;; We now define a satisfiability checker using the bdd-mgr implementation.
;;;; we will use the above theory to prove the correctness of the sat checker
;;;; while keeping the

(defun prop-formula (x)
  (or (atom x)
      (and (true-listp x)
           (prop-formula (second x))
           (prop-formula (third x))
           (prop-formula (fourth x)))))

(defun prop-ev (x a)
  (cond ((pnatp x) (prop-look x a))
        ((atom x) (bool x))
        (t (prop-if (prop-ev (second x) a)
                    (prop-ev (third x) a)
                    (prop-ev (fourth x) a)))))

(defun formulap (x)
  (declare (xargs :guard t
                  :verify-guards t))
  (or (atom x)
      (and (true-listp x)
           (formulap (car x))
           (formulap (cdr x)))))

;;;; using the bdd manager to answer if an ite-formula is satisfiable

(defun formula->bdd (formula bdd-mgr)
  (declare (xargs :guard (formulap formula)
                  :stobjs bdd-mgr
                  :verify-guards nil)) ;; we defer the guard check.
  (cond ((pnatp formula)
         (var-bdd formula bdd-mgr))
        ((atom formula)
         (mv (if formula (bdd-1) (bdd-0)) bdd-mgr))
        (t
         (seq (((f-bdd bdd-mgr)
                (formula->bdd (second formula) bdd-mgr))
               ((g-bdd bdd-mgr)
                (formula->bdd (third formula) bdd-mgr))
               ((h-bdd bdd-mgr)
                (formula->bdd (fourth formula) bdd-mgr)))
              (ite-bdd f-bdd g-bdd h-bdd bdd-mgr)))))

(defthm formula->bdd-type-correct
  (implies (bdd-mgrp x)
	   (and (bddp (mv-nth 0 (formula->bdd f x)))
		(bdd-mgrp (mv-nth 1 (formula->bdd f x))))))

(verify-guards formula->bdd)

(defthm formula->bdd-preserves-in-uniq-tbl
  (implies (in-uniq-tbl b bmr)
           (in-uniq-tbl b (mv-nth 1 (formula->bdd f bmr)))))

(defthm formula->bdd-preserves-invariant
  (implies (bdd-mgr-inv bmr)
           (mv-let (r nbm)
               (formula->bdd f bmr)
             (and (in-uniq-tbl r nbm)
                  (bdd-mgr-inv nbm)
                  (robdd r))))
  :hints (("Goal" :induct (formula->bdd f bmr)
           :do-not '(generalize eliminate-destructors
                     fertilize eliminate-irrelevance))
          ("Subgoal *1/1" :in-theory (enable b-node robdd))))

(in-theory (disable prop-if))

(defthm prop-look-reduction
  (equal (prop-if (prop-look v a) t nil)
         (prop-look v a)))

(defthm formula->bdd-is-correct
  (implies (bdd-mgr-inv bmr)
           (equal (bdd-ev (mv-nth 0 (formula->bdd f bmr)) a)
                  (prop-ev f a)))
  :hints (("Goal" :induct (formula->bdd f bmr)
           :in-theory (enable bdd-ev)
           :do-not '(generalize eliminate-destructors
                     fertilize eliminate-irrelevance))
          ("Subgoal *1/1" :in-theory (enable b-node bdd-ev)))
  :rule-classes nil)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; FINALLY, we prove our statement of correctness, namely that for
;;;; any ite formula f, the function (bdd-sat? f bdd-mgr) will return
;;;; a NON-NIL value iff there exists a satisfying assignment a such
;;;; that (prop-ev f a) is T.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun clear-bdd (bdd-mgr)
  (declare (xargs :stobjs bdd-mgr
                  :verify-guards t))
  (mv-let (dummy bdd-mgr)
      (free-bdd () bdd-mgr)
    (declare (ignore dummy))
    bdd-mgr))

(defthm clear-bdd-is-exactly-init-bdd
  (equal (clear-bdd bmr) (init-bdd bmr)))

(in-theory (disable clear-bdd))

(defun bdd-sat? (formula bdd-mgr)
  (declare (xargs :guard (formulap formula)
                  :stobjs bdd-mgr
                  :verify-guards t))
  (seq ((bdd-mgr (clear-bdd bdd-mgr))
        ((f-bdd bdd-mgr) (formula->bdd formula bdd-mgr)))
       (mv (not (eql-bdd f-bdd (bdd-0))) bdd-mgr)))

(in-theory (enable bdd-ev))

(defthm bdd-sat?-is-correct-part-1
  (implies (and (bdd-mgrp bmr)
                (not (mv-nth 0 (bdd-sat? f bmr))))
           (not (prop-ev f a)))
  :hints (("Goal"
           :in-theory (disable formula->bdd-preserves-invariant)
           :use ((:instance formula->bdd-is-correct
                            (bmr (init-bdd bmr)))
                 (:instance eql-bdd-is-correct
                            (bmr (mv-nth 1 (formula->bdd f (init-bdd bmr))))
                            (g (bdd-0))
                            (f (mv-nth 0 (formula->bdd f (init-bdd bmr)))))
                 (:instance formula->bdd-preserves-invariant
                            (bmr (init-bdd bmr)))))))

(defun sat-witness (f bdd-mgr)
  (declare (xargs :stobjs (bdd-mgr)))
  (seq ((bdd-mgr (clear-bdd bdd-mgr))
        ((f-bdd bdd-mgr) (formula->bdd f bdd-mgr)))
       (mv (robdd-witness f-bdd (bdd-0)) bdd-mgr)))

(defthm bdd-sat?-is-correct-part-2
  (implies (and (bdd-mgrp bmr)
                (mv-nth 0 (bdd-sat? f bmr)))
           (prop-ev f (mv-nth 0 (sat-witness f bmr))))
  :hints (("Goal"
           :in-theory (disable formula->bdd-preserves-invariant
                               robdd-bdd=-saturates-bdd-ev-=)
           :use ((:instance formula->bdd-is-correct
                            (bmr (init-bdd bmr))
                            (a (robdd-witness
                                (mv-nth 0 (formula->bdd f (init-bdd bmr)))
                                (bdd-0))))
                 (:instance eql-bdd-is-correct
                            (bmr (mv-nth 1 (formula->bdd f (init-bdd bmr))))
                            (g (bdd-0))
                            (f (mv-nth 0 (formula->bdd f (init-bdd bmr)))))
                 (:instance formula->bdd-preserves-invariant
                            (bmr (init-bdd bmr)))
                 (:instance robdd-bdd=-saturates-bdd-ev-=
                            (x (mv-nth 0 (formula->bdd f (init-bdd bmr))))
                            (y (bdd-0)))))))

;;;; END final verification ;;;;
