; This book develops a metafunction that ``relinks'' calls of fancy loop$
; scions by eliminating unused globals and sorting the others into term order,
; reexpressing the references to the global var in the body as necessary.

; The need for this arises because of lemmas or metafunctions that rewrite
; loop$ scion calls.  For example, when the following lambda objects are used
; with the given gvars, they are equivalent, even though they are different.

; fancy lambda object                                    gvars

; (lambda (x y) (f (car x) (cadr x) y))              (list a b)
; =
; (lambda (x y) (f (cadr x) (car x) y))              (list b a)

; Note: in the lambda objects generated for loop$s, we use LOOP$-GVARS and
; LOOP$-IVARS where we use x and y above.  Here we are imagining that the given
; lambda objects and gvars appear in a form like (COLLECT$ '<lambda-obj> gvars
; (LOOP$-AS (LIST target1 ...)))  but we don't need to know anything about the
; targets to sort the gvars and relink the lambda object.

; For example:
; (RELINK-FANCY-SCION '(COLLECT$+ '(LAMBDA (LOOP$-GVARS LOOP$-IVARS)
;                            (F (CAR (CDR LOOP$-GVARS))
;                               (CAR LOOP$-GVARS)
;                               (CAR LOOP$-IVARS)))
;                         (CONS B (CONS A 'NIL))
;                         targets))
;  produces
; (COLLECT$+ '(LAMBDA (LOOP$-GVARS LOOP$-IVARS)
;                     (F (CAR LOOP$-GVARS)
;                        (CAR (CDR LOOP$-GVARS))
;                        (CAR LOOP$-IVARS)))
;            (CONS A (CONS B 'NIL))
;            TARGETS)

; This book is meant as a warmup exercise for the more ambitious goal of
; composing fancy lambdas.  That composition involves combining two sets of
; gvars, flattening them into a simple list of actual global values, and
; expressing the composition with respect to the positions of the actuals in
; that flattened list.  This seems like a good toy version of the problem.

; Terminology: In this book we use ``gvar'' as the name of lambda formal that
; takes as its value the package of globals.  Typically, gvar will be
; LOOP$-GVAR.  In the body it is assumed that gvar is always referenced in
; ``extractor'' nests, which are arbitrarily deep CAR/CDR-nests around gvar.
; If there is an occurrence of gvar not in such a nest, we don't do anything!
; The term occupying the second argument of a fancy loop$ scion is called the
; ``globals term'' and it is typically the translation of (LIST g1 ... gk).
; The components of the globals term that are actually referenced in the body
; are called the ``actuals.''  They are typically a subset of the gi in the
; globals term.  We use ``old'' and ``new'' to distinguish the globals term and
; body we start with versus the ones we finish with.

(in-package "ACL2")

(include-book "base")
(include-book "sorting/perm" :dir :system)
(include-book "sorting/term-ordered-perms" :dir :system)
(include-book "sorting/convert-perm-to-how-many" :dir :system)
(include-book "sorting/merge-sort-term-order" :dir :system)

(defun true-car/cdr-nestp (term var)
; This function checks that term is a well-formed car/cdr nest on var.
; Car/cdr-nestp of definductor.lisp does not check well-formedness.

; WARNING: (true-car/cdr-nestp 'V 'V)!  That is, the variable var is considered
; a true car/cdr nest!  If you mean to require that term starts with a CAR or
; CDR and is a true car/cdr nest, require (consp term)!

  (declare (xargs :guard (symbolp var)))
  (cond ((variablep term) (eq term var))
        ((fquotep term) nil)
        ((and (or (eq (ffn-symb term) 'car)
                  (eq (ffn-symb term) 'cdr)))
         (and (consp (cdr term))
              (null (cddr term))
              (true-car/cdr-nestp (fargn term 1) var)))
        (t nil)))

(defun true-car/cdr-nestp-on-a-var (term)
; This function checks that term is a well-formed car/cdr nest on some symbol.
  (declare (xargs :guard t))
  (cond ((variablep term)
         (symbolp term))
        ((fquotep term) nil)
        ((and (or (eq (ffn-symb term) 'car)
                  (eq (ffn-symb term) 'cdr)))
         (and (consp (cdr term))
              (null (cddr term))
              (true-car/cdr-nestp-on-a-var (fargn term 1))))
        (t nil)))

(defconst *bad* "BAD")

(defun car/cdr-val (term actual)

; Term is a car/cdr-term around a variable, say var.  Actual is (presumably) a
; cons-term (or a quoted constant).  We determine the symbolic value of term
; assuming var is bound to actual.  We return *bad* or the corresponding
; subterm of actual.  For example, let actual be (CONS (CONS A B) C).  Then if
; term is (CDR (CAR var)) we return B, but if term is (CAR (CDR var)) we
; return *bad*.  This function can return a quoted constant as the value, e.g.,
; if term is (CAR gver) and actual is '77 we return NIL and if actual is '("Hi"
; "there") we return '"Hi".

  (declare (xargs :guard (and (true-car/cdr-nestp-on-a-var term)
                              (pseudo-termp actual))
                  :verify-guards nil))

  (cond ((variablep term) actual)
        ((eq (ffn-symb term) 'car)
         (let ((arg-val (car/cdr-val (fargn term 1) actual)))
           (cond
            ((equal arg-val *bad*) *bad*)
            ((variablep arg-val) *bad*)
            ((fquotep arg-val)
             (if (atom (unquote arg-val))
                 *nil*
                 (kwote (car (unquote arg-val)))))
            ((eq (ffn-symb arg-val) 'cons)
             (fargn arg-val 1))
            (t *bad*))))
        ((eq (ffn-symb term) 'cdr)
         (let ((arg-val (car/cdr-val (fargn term 1) actual)))
           (cond
            ((equal arg-val *bad*) *bad*)
            ((variablep arg-val) *bad*)
            ((fquotep arg-val)
             (if (atom (unquote arg-val))
                 *nil*
                 (kwote (cdr (unquote arg-val)))))
            ((eq (ffn-symb arg-val) 'cons)
             (fargn arg-val 2))
            (t *bad*))))
        (t *bad*)))

(defthm pseudo-termp-car/cdr-val
; This theorem recognizes that even the *bad* answer is a tame term!  But I
; don't think that's important except to eliminate a hyp.
  (implies (and (pseudo-termp actual)
                (not (equal (car/cdr-val term actual) *bad*)))
           (pseudo-termp (car/cdr-val term actual))))

(verify-guards car/cdr-val
  :hints (("Subgoal *1/1" :in-theory (disable pseudo-termp-car/cdr-val)
                          :use ((:instance pseudo-termp-car/cdr-val
                                           (term (CADR (CADR TERM)))
                                           (actual ACTUAL))))))

(mutual-recursion
 (defun car/cdr-to-val-alist (term var actual)

; This function either returns *bad* or an alist binding each extractor in term
; to its value (assuming var were bound to actual.  It returns *bad* when it
; finds an occurrence of var not in an extractor.

   (declare (xargs :guard (and (pseudo-termp term)
                               (symbolp var)
                               (pseudo-termp actual))
                   :verify-guards nil))
   (cond
    ((variablep term)
     (if (eq term var)
         *bad*
         nil))
    ((fquotep term) nil)
    ((true-car/cdr-nestp term var) ; (consp term) is true
     (let ((val (car/cdr-val term actual)))
       (if (equal val *bad*)
           *bad*
           (list (cons term val)))))
    (t (car/cdr-to-val-alist-list (fargs term) var actual))))

 (defun car/cdr-to-val-alist-list (terms var actual)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (symbolp var)
                               (pseudo-termp actual))))
   (cond
    ((endp terms) nil)
    (t (let ((temp1 (car/cdr-to-val-alist (car terms) var actual)))
         (cond ((equal temp1 *bad*) *bad*)
               (t (let ((temp2 (car/cdr-to-val-alist-list (cdr terms) var actual)))
                    (cond ((equal temp2 *bad*) *bad*)
                          (t (union-equal temp1 temp2)))))))))))

(defun tree-induction (x)
  (cond ((atom x) x)
        (t (list (tree-induction (car x))
                 (tree-induction (cdr x))))))

(defthm alistp-car/cdr-to-val-alist
  (and (implies (not (equal (car/cdr-to-val-alist term var actuals) *bad*))
                (alistp (car/cdr-to-val-alist term var actuals)))
       (implies (not (equal (car/cdr-to-val-alist-list term var actuals) *bad*))
                (alistp (car/cdr-to-val-alist-list term var actuals))))
  :hints (("Goal" :induct (tree-induction term)))
  :rule-classes
  ((:forward-chaining
    :corollary
    (implies (not (equal (car/cdr-to-val-alist term var actuals) *bad*))
             (alistp (car/cdr-to-val-alist term var actuals))))
   (:forward-chaining
    :corollary
    (implies (not (equal (car/cdr-to-val-alist-list term var actuals) *bad*))
             (alistp (car/cdr-to-val-alist-list term var actuals))))))

(verify-guards car/cdr-to-val-alist)

(defun make-cdr-nest (n term)
  (declare (xargs :guard (natp n)))
  (cond ((zp n) term)
        (t (list 'cdr (make-cdr-nest (- n 1) term)))))

(defun make-nth (n gvar)
  (declare (xargs :guard (natp n)))
  (list 'car (make-cdr-nest n gvar)))

(defthm nth-position-equal-ac
  (implies (and (natp n)
                (member-equal e lst))
           (equal (nth (- (position-equal-ac e lst n) n) lst) e))
  :rule-classes nil)

(defthm nth-position
  (implies (member-equal e lst)
           (equal (nth (position-equal e lst) lst) e))
  :hints (("Goal" :use (:instance nth-position-equal-ac
                                  (e e)
                                  (lst lst)
                                  (n 0)))))

(defthm integerp-position-equal-ac
  (implies (and (natp n)
                (member-equal e lst))
           (integerp (position-equal-ac e lst n))))

(defthm integerp-position-equal
  (implies (member-equal e lst)
           (integerp (position-equal e lst))))

(defthm bounds-position-equal-ac
  (implies (and (natp n)
                (member-equal e lst))
           (and (<= 0 (position-equal-ac e lst n))
                (< (position-equal-ac e lst n) (+ n (len lst)))))
  :rule-classes :linear)

(defthm bounds-position-equal
  (implies (member-equal e lst)
           (and (<= 0 (position-equal e lst))
                (< (position-equal e lst) (len lst))))
  :rule-classes :linear)

(in-theory (disable position-equal))

(defun all-true-car/cdr-nests (flg x var)
  (declare (xargs :guard (and (if flg (pseudo-termp x) (pseudo-term-listp x))
                              (symbolp var))
                  :verify-guards nil))
; We compute the list of all true-car/cdr-nests on var in x.  This is just used
; in guards and theorems.

  (if flg
      (cond ((variablep x) nil)
            ((quotep x) nil)
            ((or (eq (ffn-symb x) 'car) ; This might be a car/cdr-nest on gvar
                 (eq (ffn-symb x) 'cdr))
             (cond
              ((true-car/cdr-nestp x var) ; (consp x) is true.
               (list x))
              (t (all-true-car/cdr-nests nil (fargs x) var))))
            (t (all-true-car/cdr-nests nil (fargs x) var)))
      (cond ((endp x) nil)
            (t (union-equal (all-true-car/cdr-nests t (car x) var)
                            (all-true-car/cdr-nests nil (cdr x) var))))))

(defthm true-car/cdr-nestp-implies-pseudo-termp
  (implies (and (true-car/cdr-nestp x var)
                (symbolp var))
           (pseudo-termp x))
  :rule-classes :forward-chaining)

(defthm pseudo-term-listp-all-true-car/cdr-nests
  (implies (symbolp var)
           (pseudo-term-listp (all-true-car/cdr-nests flg x var))))

(verify-guards all-true-car/cdr-nests)

(defthm perm-merge-sort-term-order
  (perm (merge-sort-term-order x) x))

(defcong perm equal (subsetp a b) 1
  :hints (("Goal" :in-theory (disable convert-perm-to-how-many))))

(defthm subsetp-reflexive-lemma
  (implies (subsetp a (cdr b))
           (subsetp a b)))

(defthm subsetp-reflexive
  (subsetp a a))

(defthm perm-implies-subsetp-1
  (implies (perm a b)
           (subsetp a b))
  :rule-classes nil)

(defthm perm-implies-subsetp-2
  (implies (perm a b)
           (subsetp b a))
  :rule-classes nil)

(defthm subsetp-implies-member
  (implies (and (subsetp a b)
                (member-equal e a))
           (member-equal e b)))

(defcong perm iff (member-equal e a) 2
  :hints (("Goal" :in-theory (disable PERM-IMPLIES-EQUAL-SUBSETP-1
                                      convert-perm-to-how-many
                                      PERM-IS-AN-EQUIVALENCE)
           :use ((:instance perm-implies-subsetp-1
                            (a a)
                            (b a-equiv))
                 (:instance perm-implies-subsetp-2
                            (a a)
                            (b a-equiv)))
           :do-not-induct t)))

(defcong perm equal (subsetp a b) 2
  :hints (("Goal" :in-theory (disable convert-perm-to-how-many))))

(defthm member-equal-strip-cars-assoc-equal
  (implies (and (alistp alist)
                (member-equal e (strip-cars alist)))
           (assoc-equal e alist)))

(defthm member-equal-cdr-assoc-equal
  (implies (and (assoc-equal term alist)
                (SUBSETP-EQUAL (STRIP-CDRS ALIST) RELEVANT-VALS))
           (member-equal (cdr (assoc-equal term alist)) relevant-vals)))



(encapsulate
  nil
  (local
   (defthm subsetp-equal-union-equal-1-lemma
     (implies (and (subsetp-equal (union-equal a b) c)
                   (member-equal e b))
              (member-equal e c))))

  (defthm subsetp-equal-union-equal-1
    (equal (subsetp-equal (union-equal a b) c)
           (and (subsetp-equal a c)
                (subsetp-equal b c)))))

(mutual-recursion
 (defun relink-term (old-alist gvar relevant-vals term)

; Term is the body of some lambda object.  Old-alist maps the car/cdr-nests (of
; gvar) occuring in term to their values relative to the old globals term that
; was passed to the lambda object.  Relevent-vals is the sorted strip-cdrs of
; the alist.  As such, it contains the values actually referenced in the lambda
; body, listed in term order.  We copy term and replace each old car/cdr-nest
; by the new car/cdr-nest referencing the same value in relevant-vals.

   (declare (xargs :guard (and (alistp old-alist)
                               (symbolp gvar)
                               (true-listp relevant-vals)
                               (pseudo-termp term)
                               (subsetp-equal
                                (all-true-car/cdr-nests t term gvar)
                                (strip-cars old-alist))
                               (subsetp-equal (strip-cdrs old-alist)
                                              relevant-vals))))

   (cond
    ((variablep term) term)
    ((fquotep term) term)
    ((or (eq (ffn-symb term) 'car) ; This might be a car/cdr-nest on gvar
         (eq (ffn-symb term) 'cdr))
     (cond
      ((true-car/cdr-nestp term gvar) ; (consp term) is true

; We know that old-alist maps every true-car/cdr-nest on gvar to the
; corresponding actual expression.  So the assoc-equal below is non-nil.

       (make-nth (position (cdr (assoc-equal term old-alist))
                           relevant-vals
                           :test 'equal)
                 gvar))
      (t (list (ffn-symb term)
               (relink-term old-alist gvar relevant-vals (cadr term))))))
    (t (cons (ffn-symb term)
             (relink-term-list old-alist gvar relevant-vals (fargs term))))))

 (defun relink-term-list (old-alist gvar relevant-vals terms)
   (declare (xargs :guard (and (alistp old-alist)
                               (symbolp gvar)
                               (true-listp relevant-vals)
                               (pseudo-term-listp terms)
                               (subsetp-equal
                                (all-true-car/cdr-nests nil terms gvar)
                                (strip-cars old-alist))
                               (subsetp-equal (strip-cdrs old-alist)
                                              relevant-vals))))
   (cond ((endp terms) nil)
         (t (cons (relink-term old-alist gvar relevant-vals (car terms))
                  (relink-term-list old-alist gvar relevant-vals (cdr terms))))))
 )

; Test
; (relink-term
;  '(((car (cdr (cdr loop$-gvars))) . C)
;    ((car (cdr (cdr (cdr loop$-gvars)))) . A))
;  'loop$-gvars
;  '(A C)
;  '(binary-append (car (cdr (cdr loop$-gvars)))
;                  (car (cdr (cdr (cdr loop$-gvars))))))
; ==>
; (BINARY-APPEND (CAR (CDR LOOP$-GVARS))
;                (CAR LOOP$-GVARS))

(defconst *fancy-loop$-scions*
  (strip-caddrs *for-loop$-keyword-info*))

(defun make-true-cons-nest (terms)
  (declare (xargs :guard (true-listp terms)))
  (if (consp terms)
      (xxxjoin 'cons (append terms '('nil)))
      *nil*))

(defthm pseudo-term-listp-strip-cdrs-car/cdr-to-val-alist
  (and (implies (and (pseudo-termp actuals)
                     (not (equal (car/cdr-to-val-alist term var actuals) *bad*)))
                (pseudo-term-listp (strip-cdrs (car/cdr-to-val-alist term var actuals))))
       (implies (and (pseudo-termp actuals)
                     (not (equal (car/cdr-to-val-alist-list term var actuals) *bad*)))
                (pseudo-term-listp (strip-cdrs (car/cdr-to-val-alist-list term var actuals)))))
  :hints (("Goal" :induct (tree-induction term))))

(defthm member-strip-cdrs
  (implies (member-equal e b)
           (member-equal (cdr e) (strip-cdrs b))))

(defthm member-strip-cdrs-union-equal
  (implies (member-equal e b)
           (member-equal (cdr e) (strip-cdrs (union-equal a b)))))

(defthm member-strip-cars-union-equal
  (implies (member-equal e b)
           (member-equal (car e) (strip-cars (union-equal a b)))))

(defthm strip-cdrs-union-equal-1
  (subsetp-equal (strip-cdrs a)
                 (strip-cdrs (union-equal a b))))

(defthm strip-cdrs-union-equal-2
  (subsetp-equal (strip-cdrs b)
                 (strip-cdrs (union-equal a b))))

(defthm transitivity-of-subsetp-equal
  (implies (and (subsetp-equal a b) (subsetp-equal b c))
           (subsetp-equal a c)))

(defthm transitivity-corollary-1
  (implies (subsetp-equal (strip-cdrs (union-equal a b)) c)
           (subsetp-equal (strip-cdrs a) c)))

(defthm transitivity-corollary-2
  (implies (subsetp-equal (strip-cdrs (union-equal a b)) c)
           (subsetp-equal (strip-cdrs b) c)))

(defthm member-union-equal
  (iff (member-equal e (union-equal a b))
       (or (member-equal e a)
           (member-equal e b))))

; By the way, I actually know strip-cdrs distributes over union-equal
; preserving set equality (subsetp-equal in both directions).  But I
; don't think I need that.

(defun set-equalp (x y)
  (and (subsetp-equal x y)
       (subsetp-equal y x)))

(defequiv set-equalp)

(defthm equal-subsetp-equal
  (equal (equal (subsetp-equal a b) (subsetp-equal c d))
         (iff (subsetp-equal a b) (subsetp-equal c d))))

(defcong set-equalp equal (subsetp-equal x y) 1)
(defcong set-equalp equal (subsetp-equal x y) 2)

(encapsulate
  nil
  (local
   (defthm strip-cdrs-union-equal-distributivity-1
     (subsetp-equal (strip-cdrs (union-equal a b))
                    (union-equal (strip-cdrs a) (strip-cdrs b)))
     :rule-classes nil))

  (defthm strip-cdrs-union-equal-distributivity
    (set-equalp (strip-cdrs (union-equal a b))
                (union-equal (strip-cdrs a)
                             (strip-cdrs b)))))

(encapsulate
  nil
  (local
   (defthm strip-cars-union-equal-distributivity-1
     (subsetp-equal (strip-cars (union-equal a b))
                    (union-equal (strip-cars a) (strip-cars b)))
     :rule-classes nil))

  (defthm strip-cars-union-equal-distributivity
    (set-equalp (strip-cars (union-equal a b))
                (union-equal (strip-cars a)
                             (strip-cars b)))))

(defthm subsetp-equal-union-equal-2
  (implies (subsetp-equal a c)
           (subsetp-equal a (union-equal b c))))

(defthm relink-term-reqmt-on-alist-general
  (implies (not (equal (if flg
                        (CAR/CDR-TO-VAL-ALIST x var old-global-actual)
                        (CAR/CDR-TO-VAL-ALIST-LIST x var old-global-actual))
                    *bad*))
           (SUBSETP-EQUAL (ALL-TRUE-CAR/CDR-NESTS flg x var)
                          (STRIP-CARS (if flg
                                          (CAR/CDR-TO-VAL-ALIST x var old-global-actual)
                                          (CAR/CDR-TO-VAL-ALIST-LIST x var old-global-actual)))))
  :rule-classes nil)

(defthm relink-term-reqmt-on-alist
  (and (implies (not (equal (CAR/CDR-TO-VAL-ALIST x var old-global-actual) *bad*))
                (SUBSETP-EQUAL (ALL-TRUE-CAR/CDR-NESTS t x var)
                               (STRIP-CARS (CAR/CDR-TO-VAL-ALIST x var old-global-actual))))
       (implies (not (equal (CAR/CDR-TO-VAL-ALIST-list x var old-global-actual) *bad*))
                (SUBSETP-EQUAL (ALL-TRUE-CAR/CDR-NESTS nil x var)
                               (STRIP-CARS (CAR/CDR-TO-VAL-ALIST-list x var old-global-actual)))))
  :hints (("Goal" :use ((:instance relink-term-reqmt-on-alist-general
                                   (flg t))
                        (:instance relink-term-reqmt-on-alist-general
                                   (flg nil))))))

(defthm pseudo-term-listp-remove-duplicates-equal
  (implies (true-listp x)
           (equal (pseudo-term-listp (remove-duplicates-equal x))
                  (pseudo-term-listp x))))

(defthm member-equal-remove-duplicates-equal
  (iff (member-equal x (remove-duplicates-equal l))
       (member-equal x l)))

(defthm subsetp-equal-remove-duplicates-equal
  (subsetp-equal (remove-duplicates-equal x) x))

(defthm subsetp-equal-remove-duplicates-equal-corollary
  (equal (subsetp-equal x (remove-duplicates-equal y))
         (subsetp-equal x y))
  :hints (("Goal" :induct (remove-duplicates-equal y))))

(defun relink-fancy-scion (term)
  (declare (xargs :guard (pseudo-termp term)))
  (case-match term
    ((scion ('QUOTE ('LAMBDA (gvar ivar) body))
            old-global-actual
            target-tuples)
     (cond
      ((and (member-eq scion *fancy-loop$-scions*)
            (symbolp gvar)
            (symbolp ivar)
            (not (eq gvar ivar))
            (pseudo-termp body)) ; this is necessary for guard verification!
       (let ((old-alist (car/cdr-to-val-alist body gvar old-global-actual)))
         (cond
          ((equal old-alist *bad*) term)
          (t (let* ((new-actuals (merge-sort-term-order
                                  (remove-duplicates-equal
                                   (strip-cdrs old-alist))))
                    (new-body (relink-term old-alist gvar new-actuals body))
                    (new-global-actual (make-true-cons-nest new-actuals)))
               (cond
                ((equal body new-body)

; If body is new-body, then the global actual can have the same value as
; before.  But the global actual as computed above might be a different term,
; e.g., the old-global-actual might be '(0) and new be (cons '0 'nil), causing
; an infinite loop.

                 term)
                (t `(,scion '(lambda (,gvar ,ivar)
                               ,new-body)
                            ,new-global-actual
                            ,target-tuples))))))))
      (t term)))
    (& term)))

; Test
; (relink-fancy-scion '(thereis$+ '(lambda (loop$-gvars loop$-ivars)
;                              (foo (car (cdr (cdr loop$-gvars)))
;                                   (car (cdr (cdr (cdr loop$-gvars))))))
;                           (cons c (cons b (cons c (cons a 'nil))))
;                           target-tuples))
; =
; (THEREIS$+ '(LAMBDA (LOOP$-GVARS LOOP$-IVARS)
;                     (FOO (CAR (CDR LOOP$-GVARS))
;                          (CAR LOOP$-GVARS)))
;            (CONS A (CONS C 'NIL))
;            TARGET-TUPLES)

(defun relink-fancy-scion-hypfn (term)

; This function doesn't have to check that term is an actionable call of a
; fancy loop$ scion.  If it isn't, the conclusion of the metafunction
; correctness theorem is trivially valid.

  (declare (xargs :guard (pseudo-termp term)))
  (cond ((consp term)
         `(tamep-functionp ,(fargn term 1)))
        (t *nil*)))

(defun tamep-listp (terms)
  (cond ((endp terms) t)
        (t (and (tamep (car terms))
                (tamep-listp (cdr terms))))))

(defthm cdr-append-list-nil
  (iff (CDR (APPEND lst '('NIL)))
       (consp lst)))

(defthm tamep-xxxjoin-cons
  (implies (and (consp lst)
                (tamep-listp lst))
           (tamep (xxxjoin 'cons (append lst '('nil))))))

(defthm ev$-make-true-cons-nest
  (implies (tamep-listp terms)
           (equal (ev$ (make-true-cons-nest terms) a)
                  (ev$-list terms a))))

(in-theory (disable make-true-cons-nest))

(defthm tamep-make-cdr-nest
  (implies (symbolp var)
           (tamep (make-cdr-nest n var))))

(defthm ev$-car
  (implies (tamep x)
           (equal (ev$ (list 'car x) a)
                  (car (ev$ x a)))))

(defthm ev$-cdr
  (implies (tamep x)
           (equal (ev$ (list 'cdr x) a)
                  (cdr (ev$ x a)))))

(defthm ev$-cons
  (implies (and (tamep x)
                (tamep y))
           (equal (ev$ (list 'cons x y) a)
                  (cons (ev$ x a)
                        (ev$ y a)))))

(local ; avoid name conflict with existing lemmas
 (defthm cdr-nthcdr
   (implies (natp n)
            (equal (cdr (nthcdr n lst))
                   (nthcdr (+ 1 n) lst)))))

(defthm ev$-make-cdr-nest
  (implies (and (natp n)
                (symbolp var))
           (equal (ev$ (make-cdr-nest n var) a)
                  (nthcdr n (cdr (assoc-eq var a)))))
  :hints (("Goal" :induct (make-cdr-nest n var))))

(defthm ev$-make-nth
  (implies (and (natp n)
                (symbolp var))
           (equal (ev$ (make-nth n var) a)
                  (nth n (cdr (assoc-eq var a))))))

(defthm tamep-make-nth
  (implies (and (natp n)
                (symbolp var))
           (tamep (make-nth n var))))

(in-theory (disable make-nth))

(defun flagged-tamep-hint (flg n flags x)
  (if flg
      (cond
       ((variablep x) (list n flags x))
       ((fquotep x) x)
       ((symbolp (ffn-symb x))
        (flagged-tamep-hint
         nil
         (access apply$-badge (badge (ffn-symb x)) :arity)
         (if (eq (access apply$-badge (badge (ffn-symb x)) :ilks) t)
             nil
             (access apply$-badge (badge (ffn-symb x)) :ilks))
         (fargs x)))
       ((consp (ffn-symb x))
        (flagged-tamep-hint nil (len (fargs x)) nil (fargs x)))
       (t x))
      (cond
       ((endp x) nil)
       (t (cons (flagged-tamep-hint t n flags (car x))
                (flagged-tamep-hint nil (- n 1) (cdr flags) (cdr x)))))))

(defun suitably-tamep-listp-hint (n flags x)
  (if (zp n)
      (list flags x)
      (suitably-tamep-listp-hint (- n 1) (cdr flags) (cdr x))))

(defthm suitably-tamep-listp-implies-len
  (implies (suitably-tamep-listp n nil args)
           (suitably-tamep-listp (len args) NIL args))
  :hints (("Goal" :induct (suitably-tamep-listp-hint n nil args))))

; Note the subsetp-equal hypotheses below.  In fact, the cdrs of old-alist are
; set-equal to relevant-vals, but we just need this direction here.  The
; stronger perm relationship is unsuitable for our application (even though the
; theorem can be proved for perm) because the relevant-vals will included only
; one occurrence of any actual value, whereas the alist may contain multiple
; occurrences.

(defthm tamep-relink-term-general
  (if flg
      (implies (and (tamep x)
                    (symbolp gvar)
                    (alistp old-alist)
                    (subsetp-equal
                     (all-true-car/cdr-nests t x gvar)
                     (strip-cars old-alist))
                    (subsetp-equal (strip-cdrs old-alist) relevant-vals))
               (tamep (relink-term old-alist gvar relevant-vals x)))
      (implies (and (suitably-tamep-listp n flags x)
                    (symbolp gvar)
                    (alistp old-alist)
                    (subsetp-equal
                     (all-true-car/cdr-nests nil x gvar)
                     (strip-cars old-alist))
                    (subsetp-equal (strip-cdrs old-alist) relevant-vals))
               (suitably-tamep-listp n flags (relink-term-list old-alist gvar relevant-vals x))))
  :hints (("Goal"
           :induct (flagged-tamep-hint flg n flags x)
           :expand ((suitably-tamep-listp n flags x)
                    (tamep x)
                    (relink-term old-alist gvar relevant-vals x))))
  :rule-classes nil)

(defthm tamep-relink-term
  (and (implies (and (tamep x)
                     (symbolp gvar)
                     (alistp old-alist)
                     (subsetp-equal
                      (all-true-car/cdr-nests t x gvar)
                      (strip-cars old-alist))
                     (subsetp-equal (strip-cdrs old-alist) relevant-vals))
                (tamep (relink-term old-alist gvar relevant-vals x)))
       (implies (and (suitably-tamep-listp n flags x)
                     (symbolp gvar)
                     (alistp old-alist)
                     (subsetp-equal
                      (all-true-car/cdr-nests nil x gvar)
                      (strip-cars old-alist))
                     (subsetp-equal (strip-cdrs old-alist) relevant-vals))
                (suitably-tamep-listp n flags (relink-term-list old-alist gvar relevant-vals x))))
  :hints (("Goal" :use ((:instance tamep-relink-term-general (flg t))
                        (:instance tamep-relink-term-general (flg nil))))))

(defevaluator evalator evalator-list
  ((car x)
   (cdr x)
   (cons x y)
   (tamep-functionp fn)
   (sum$+ fn globals lst)
   (always$+ fn globals lst)
   (thereis$+ fn globals lst)
   (collect$+ fn globals lst)
   (append$+ fn globals lst)
   (until$+ fn globals lst)
   (when$+ fn globals lst)))

(defthm len-relink-term-list
  (equal (len (relink-term-list old-alist gvar new-actuals x))
         (len x)))

(defun strong-alist-propertyp (alist gvar actual)
  (cond ((endp alist) (equal alist nil))
        ((and (consp (car alist))
              (consp (car (car alist)))
              (true-car/cdr-nestp (car (car alist)) gvar)
              (equal (car/cdr-val (car (car alist)) actual)
                     (cdr (car alist)))
              (pseudo-termp (cdr (car alist))))
         (strong-alist-propertyp (cdr alist) gvar actual))
        (t nil)))

(defthm strong-alist-propertyp-union-equal
  (implies (and (strong-alist-propertyp a gvar actual)
                (strong-alist-propertyp b gvar actual))
           (strong-alist-propertyp (union-equal a b) gvar actual)))

(defun term-induction (flg x)
  (if flg
      (cond ((variablep x) x)
            ((fquotep x) x)
            (t (term-induction nil (cdr x))))
      (cond ((endp x) x)
            (t (list (term-induction t (car x))
                     (term-induction nil (cdr x)))))))

(defthm strong-alist-propertyp-car/cdr-to-val-alist-general
  (if flg
      (implies (and (pseudo-termp actual)
                    (not (equal (car/cdr-to-val-alist x gvar actual) *bad*)))
               (strong-alist-propertyp (car/cdr-to-val-alist x gvar actual) gvar actual))
      (implies (and (pseudo-termp actual)
                    (not (equal (car/cdr-to-val-alist-list x gvar actual) *bad*)))
               (strong-alist-propertyp (car/cdr-to-val-alist-list x gvar actual) gvar actual)))
  :hints (("Goal" :induct (term-induction flg x)))
  :rule-classes nil)

(defthm strong-alist-propertyp-car/cdr-to-val-alist
  (and (implies (and (pseudo-termp actual)
                     (not (equal (car/cdr-to-val-alist x gvar actual) *bad*)))
                (strong-alist-propertyp (car/cdr-to-val-alist x gvar actual) gvar actual))
       (implies (and (pseudo-termp actual)
                     (not (equal (car/cdr-to-val-alist-list x gvar actual) *bad*)))
                (strong-alist-propertyp (car/cdr-to-val-alist-list x gvar actual) gvar actual)))
  :hints (("Goal" :use ((:instance strong-alist-propertyp-car/cdr-to-val-alist-general
                                   (flg t))
                        (:instance strong-alist-propertyp-car/cdr-to-val-alist-general
                                   (flg nil))))))

(defthm assoc-equal-put-assoc-equal
  (equal (assoc-equal key (put-assoc-equal key val a))
         (cons key val)))

(defthm len-evalator-list
  (equal (len (evalator-list x a))
         (len x)))

(defthm nth-evalator-list
  (equal (nth n (evalator-list x a))
         (evalator (nth n x) a)))

(defthm tamep-true-car/cdr-nestp
  (implies (and (true-car/cdr-nestp x var)
                (symbolp var))
           (tamep x)))

(defthm ev$-true-car/cdr-nest
  (implies (and (symbolp gvar)
                (true-car/cdr-nestp x gvar)
                (not (equal (car/cdr-val x actual) *bad*)))
           (equal (ev$ x (put-assoc-equal gvar (evalator actual a1) a2))
                  (evalator (car/cdr-val x actual) a1)))
  :hints (("Goal"
           :induct (true-car/cdr-nestp x gvar)
           :do-not-induct t
           :expand ((ev$ x (put-assoc-equal gvar (evalator actual a1) a2))))))

(defthm strong-alist-property-cdr-assoc-equal-1
  (implies (and (strong-alist-propertyp old-alist gvar global-actual)
                (assoc-equal x old-alist))
           (equal (cdr (assoc-equal x old-alist))
                  (car/cdr-val x global-actual))))
(in-theory (disable strong-alist-property-cdr-assoc-equal-1))

(defthm strong-alist-property-cdr-assoc-equal-2
  (implies (and (strong-alist-propertyp old-alist gvar global-actual)
                (assoc-equal x old-alist))
           (not (equal (car/cdr-val x global-actual) *bad*))))

(in-theory (disable strong-alist-property-cdr-assoc-equal-2))

(defthm strong-alist-property-implies-cadr-not-bad
  (implies (and (STRONG-ALIST-PROPERTYP OLD-ALIST GVAR GLOBAL-ACTUAL)
                (symbolp gvar)
                (true-car/cdr-nestp x gvar)
                (assoc-equal x old-alist))
           (and (CONSP (CAR/CDR-VAL (CADR X) GLOBAL-ACTUAL))
                (or (eq (car (CAR/CDR-VAL (CADR X) GLOBAL-ACTUAL)) 'CONS)
                    (eq (car (CAR/CDR-VAL (CADR X) GLOBAL-ACTUAL)) 'quote)))) 
  :rule-classes nil)

(defthm strong-alist-propertyp-implies-alistp
  (implies (strong-alist-propertyp alist gvar global-actual)
           (alistp alist))
  :rule-classes :forward-chaining)

(defthm ev$-relink-term-general
  (if flg
      (implies (and (tamep x)
                    (not (equal (car/cdr-to-val-alist x gvar global-actual) *bad*))
                    (pseudo-termp global-actual)
                    (symbolp gvar)
                    (subsetp-equal
                     (all-true-car/cdr-nests t x gvar)
                     (strip-cars old-alist))
                    (strong-alist-propertyp old-alist gvar global-actual)
                    (set-equalp (strip-cdrs old-alist) relevant-vals))
               (equal (ev$ (relink-term
                            old-alist
                            gvar
                            relevant-vals
                            x)
                           (put-assoc-equal gvar (evalator-list relevant-vals a1) a2))
                      (ev$ x
                           (put-assoc-equal gvar (evalator global-actual a1) a2))))
      (implies (and (suitably-tamep-listp n flags x)
                    (not (equal (car/cdr-to-val-alist-list x gvar global-actual) *bad*))
                    (pseudo-termp global-actual)
                    (symbolp gvar)
                    (subsetp-equal
                     (all-true-car/cdr-nests nil x gvar)
                     (strip-cars old-alist))
                    (strong-alist-propertyp old-alist gvar global-actual)
                    (set-equalp (strip-cdrs old-alist) relevant-vals))
               (equal (ev$-list (relink-term-list
                                 old-alist
                                 gvar
                                 relevant-vals
                                 x)
                                (put-assoc-equal gvar (evalator-list relevant-vals a1) a2))
                      (ev$-list x
                                (put-assoc-equal gvar (evalator global-actual a1) a2)))))
  :rule-classes nil
  :hints (("Goal" :induct (flagged-tamep-hint flg n flags x)
           :expand ((SUITABLY-TAMEP-LISTP N FLAGS X)
                    (SUITABLY-TAMEP-LISTP 1 NIL (CDR X))
                    (tamep x)
                    (ev$ x a2)
                    (RELINK-TERM OLD-ALIST GVAR RELEVANT-VALS X)
                    (EV$ (CONS (CAR X)
                               (RELINK-TERM-LIST OLD-ALIST GVAR RELEVANT-VALS (CDR X)))
                         (PUT-ASSOC-EQUAL GVAR (EVALATOR-LIST RELEVANT-VALS A1)
                                          A2))
                    (EV$ X
                         (PUT-ASSOC-EQUAL GVAR (EVALATOR GLOBAL-ACTUAL A1)
                                          A2))))
          ("Subgoal *1/3" ; "Subgoal *1/3.22'''"
           :use (:instance strong-alist-property-implies-cadr-not-bad))
          ("Subgoal *1/3.38'" :in-theory (enable strong-alist-property-cdr-assoc-equal-1))
          ("Subgoal *1/3.37'" :in-theory (enable strong-alist-property-cdr-assoc-equal-1))
          ("Subgoal *1/3.35''" :in-theory (enable strong-alist-property-cdr-assoc-equal-1))
          ("Subgoal *1/3.34''" :in-theory (enable strong-alist-property-cdr-assoc-equal-1))
          ("Subgoal *1/3.33'" :in-theory (enable strong-alist-property-cdr-assoc-equal-1))
          ("Subgoal *1/3.32'" :in-theory (enable strong-alist-property-cdr-assoc-equal-1))
          ("Subgoal *1/3.30'" :in-theory (enable strong-alist-property-cdr-assoc-equal-1))
          ("Subgoal *1/3.28'''" :in-theory (enable strong-alist-property-cdr-assoc-equal-1))
          ("Subgoal *1/3.27'" :in-theory (enable strong-alist-property-cdr-assoc-equal-1))
          ("Subgoal *1/3.13'" :in-theory (enable strong-alist-property-cdr-assoc-equal-1))
          ("Subgoal *1/3.11.2'" :in-theory (enable strong-alist-property-cdr-assoc-equal-1))
          ("Subgoal *1/3.11.1'" :in-theory (enable strong-alist-property-cdr-assoc-equal-1))
          ("Subgoal *1/3.10'" :in-theory (enable strong-alist-property-cdr-assoc-equal-1))
          ("Subgoal *1/3.8'" :in-theory (enable strong-alist-property-cdr-assoc-equal-1))
          ("Subgoal *1/3.7'" :in-theory (enable strong-alist-property-cdr-assoc-equal-1))
          ("Subgoal *1/3.5''" :in-theory (enable strong-alist-property-cdr-assoc-equal-1))
          ("Subgoal *1/3.4''" :in-theory (enable strong-alist-property-cdr-assoc-equal-1))
          ("Subgoal *1/3.3'" :in-theory (enable strong-alist-property-cdr-assoc-equal-1))
          ("Subgoal *1/3.2'" :in-theory (enable strong-alist-property-cdr-assoc-equal-1))))

(defthm ev$-relink-term
  (implies (and (tamep x)
                (not (equal (car/cdr-to-val-alist x gvar global-actual) *bad*))
                (pseudo-termp global-actual)
                (symbolp gvar))
           (equal (ev$ (relink-term
                        (car/cdr-to-val-alist x gvar global-actual)
                        gvar
                        (merge-sort-term-order
                         (remove-duplicates-equal
                          (strip-cdrs
                           (car/cdr-to-val-alist x gvar global-actual))))
                        x)
                       (list
                        (cons gvar (evalator-list (merge-sort-term-order
                                                   (remove-duplicates-equal
                                                    (strip-cdrs
                                                     (car/cdr-to-val-alist
                                                      x gvar global-actual))))
                                                  a1))
                        (cons ivar target-tuple)))
                  (ev$ x
                       (list
                        (cons gvar (evalator global-actual
                                             a1))
                        (cons ivar target-tuple))
                       )))
  :hints (("Goal" :use (:instance ev$-relink-term-general
                                  (flg t)
                                  (old-alist
                                   (car/cdr-to-val-alist x gvar global-actual))
                                  (relevant-vals
                                   (merge-sort-term-order
                                    (remove-duplicates-equal
                                     (strip-cdrs
                                      (car/cdr-to-val-alist x gvar global-actual)))))
                                  (a2 (list (cons gvar any)
                                            (cons ivar target-tuple)))))))

(defthm relink-fancy-scion-lemma-sum$+
  (implies
   (and (tamep-functionp `(lambda (,gvar ,ivar) ,body))
        (symbolp gvar)
        (symbolp ivar)
        (not (eq gvar ivar))
        (pseudo-termp global-actual)
        (not (equal (car/cdr-to-val-alist body gvar global-actual) *bad*)))
   (equal
    (sum$+
     (list 'lambda (list gvar ivar)
           (relink-term
            (car/cdr-to-val-alist body gvar global-actual)
            gvar
            (merge-sort-term-order
             (remove-duplicates-equal
              (strip-cdrs
               (car/cdr-to-val-alist body gvar global-actual))))
            body))
     (evalator-list
      (merge-sort-term-order
       (remove-duplicates-equal
        (strip-cdrs
         (car/cdr-to-val-alist body gvar global-actual))))
      a)
     targets)
    (sum$+ `(lambda (,gvar ,ivar) ,body)
           (evalator global-actual a)
           targets)))
  :hints (("Goal" :induct (sum$+ `(lambda (,gvar ,ivar) ,body)
                                 (evalator global-actual a)
                                 targets))))

(defthm relink-fancy-scion-lemma-always$+
  (implies
   (and (tamep-functionp `(lambda (,gvar ,ivar) ,body))
        (symbolp gvar)
        (symbolp ivar)
        (not (eq gvar ivar))
        (pseudo-termp global-actual)
        (not (equal (car/cdr-to-val-alist body gvar global-actual) *bad*)))
   (equal
    (always$+
     (list 'lambda (list gvar ivar)
           (relink-term
            (car/cdr-to-val-alist body gvar global-actual)
            gvar
            (merge-sort-term-order
             (remove-duplicates-equal
              (strip-cdrs
               (car/cdr-to-val-alist body gvar global-actual))))
            body))
     (evalator-list
      (merge-sort-term-order
       (remove-duplicates-equal
        (strip-cdrs
         (car/cdr-to-val-alist body gvar global-actual))))
      a)
     targets)
    (always$+ `(lambda (,gvar ,ivar) ,body)
           (evalator global-actual a)
           targets)))
  :hints (("Goal" :induct (always$+ `(lambda (,gvar ,ivar) ,body)
                                 (evalator global-actual a)
                                 targets))))
(defthm relink-fancy-scion-lemma-thereis$+
  (implies
   (and (tamep-functionp `(lambda (,gvar ,ivar) ,body))
        (symbolp gvar)
        (symbolp ivar)
        (not (eq gvar ivar))
        (pseudo-termp global-actual)
        (not (equal (car/cdr-to-val-alist body gvar global-actual) *bad*)))
   (equal
    (thereis$+
     (list 'lambda (list gvar ivar)
           (relink-term
            (car/cdr-to-val-alist body gvar global-actual)
            gvar
            (merge-sort-term-order
             (remove-duplicates-equal
              (strip-cdrs
               (car/cdr-to-val-alist body gvar global-actual))))
            body))
     (evalator-list
      (merge-sort-term-order
       (remove-duplicates-equal
        (strip-cdrs
         (car/cdr-to-val-alist body gvar global-actual))))
      a)
     targets)
    (thereis$+ `(lambda (,gvar ,ivar) ,body)
           (evalator global-actual a)
           targets)))
  :hints (("Goal" :induct (thereis$+ `(lambda (,gvar ,ivar) ,body)
                                 (evalator global-actual a)
                                 targets))))
(defthm relink-fancy-scion-lemma-collect$+
  (implies
   (and (tamep-functionp `(lambda (,gvar ,ivar) ,body))
        (symbolp gvar)
        (symbolp ivar)
        (not (eq gvar ivar))
        (pseudo-termp global-actual)
        (not (equal (car/cdr-to-val-alist body gvar global-actual) *bad*)))
   (equal
    (collect$+
     (list 'lambda (list gvar ivar)
           (relink-term
            (car/cdr-to-val-alist body gvar global-actual)
            gvar
            (merge-sort-term-order
             (remove-duplicates-equal
              (strip-cdrs
               (car/cdr-to-val-alist body gvar global-actual))))
            body))
     (evalator-list
      (merge-sort-term-order
       (remove-duplicates-equal
        (strip-cdrs
         (car/cdr-to-val-alist body gvar global-actual))))
      a)
     targets)
    (collect$+ `(lambda (,gvar ,ivar) ,body)
           (evalator global-actual a)
           targets)))
  :hints (("Goal" :induct (collect$+ `(lambda (,gvar ,ivar) ,body)
                                 (evalator global-actual a)
                                 targets))))
(defthm relink-fancy-scion-lemma-append$+
  (implies
   (and (tamep-functionp `(lambda (,gvar ,ivar) ,body))
        (symbolp gvar)
        (symbolp ivar)
        (not (eq gvar ivar))
        (pseudo-termp global-actual)
        (not (equal (car/cdr-to-val-alist body gvar global-actual) *bad*)))
   (equal
    (append$+
     (list 'lambda (list gvar ivar)
           (relink-term
            (car/cdr-to-val-alist body gvar global-actual)
            gvar
            (merge-sort-term-order
             (remove-duplicates-equal
              (strip-cdrs
               (car/cdr-to-val-alist body gvar global-actual))))
            body))
     (evalator-list
      (merge-sort-term-order
       (remove-duplicates-equal
        (strip-cdrs
         (car/cdr-to-val-alist body gvar global-actual))))
      a)
     targets)
    (append$+ `(lambda (,gvar ,ivar) ,body)
           (evalator global-actual a)
           targets)))
  :hints (("Goal" :induct (append$+ `(lambda (,gvar ,ivar) ,body)
                                 (evalator global-actual a)
                                 targets))))
(defthm relink-fancy-scion-lemma-until$+
  (implies
   (and (tamep-functionp `(lambda (,gvar ,ivar) ,body))
        (symbolp gvar)
        (symbolp ivar)
        (not (eq gvar ivar))
        (pseudo-termp global-actual)
        (not (equal (car/cdr-to-val-alist body gvar global-actual) *bad*)))
   (equal
    (until$+
     (list 'lambda (list gvar ivar)
           (relink-term
            (car/cdr-to-val-alist body gvar global-actual)
            gvar
            (merge-sort-term-order
             (remove-duplicates-equal
              (strip-cdrs
               (car/cdr-to-val-alist body gvar global-actual))))
            body))
     (evalator-list
      (merge-sort-term-order
       (remove-duplicates-equal
        (strip-cdrs
         (car/cdr-to-val-alist body gvar global-actual))))
      a)
     targets)
    (until$+ `(lambda (,gvar ,ivar) ,body)
           (evalator global-actual a)
           targets)))
  :hints (("Goal" :induct (until$+ `(lambda (,gvar ,ivar) ,body)
                                 (evalator global-actual a)
                                 targets))))
(defthm relink-fancy-scion-lemma-when$+
  (implies
   (and (tamep-functionp `(lambda (,gvar ,ivar) ,body))
        (symbolp gvar)
        (symbolp ivar)
        (not (eq gvar ivar))
        (pseudo-termp global-actual)
        (not (equal (car/cdr-to-val-alist body gvar global-actual) *bad*)))
   (equal
    (when$+
     (list 'lambda (list gvar ivar)
           (relink-term
            (car/cdr-to-val-alist body gvar global-actual)
            gvar
            (merge-sort-term-order
             (remove-duplicates-equal
              (strip-cdrs
               (car/cdr-to-val-alist body gvar global-actual))))
            body))
     (evalator-list
      (merge-sort-term-order
       (remove-duplicates-equal
        (strip-cdrs
         (car/cdr-to-val-alist body gvar global-actual))))
      a)
     targets)
    (when$+ `(lambda (,gvar ,ivar) ,body)
           (evalator global-actual a)
           targets)))
  :hints (("Goal" :induct (when$+ `(lambda (,gvar ,ivar) ,body)
                                 (evalator global-actual a)
                                 targets))))

; TODO: The simplifier loops on some xxxjoin proofs.  If you try to prove
; evalator-make-true-cons-nest without the following two prior events it loops
; forever, expanding xxxjoin as each expansion introduces a term allowing the
; next expansion.  So I prove a nice version of make-true-cons-nest that
; behaves and prevent the introduction of xxxjoin.

(defthm make-true-cons-nest-opener
  (and (implies (atom tail)
                (equal (make-true-cons-nest tail)
                       ''nil))
       (equal (make-true-cons-nest (cons a tail))
              `(cons ,a ,(make-true-cons-nest tail))))
  :hints (("Goal" :in-theory (enable make-true-cons-nest))))

(defthm evalator-make-true-cons-nest
  (equal (evalator (make-true-cons-nest lst) a)
         (evalator-list lst a))
  :hints (("Goal" :induct (len lst))))

(defthm relink-fancy-scion-correct
  (implies (and (pseudo-termp x)
                (evalator (relink-fancy-scion-hypfn x) a))
           (equal (evalator x a)
                  (evalator (relink-fancy-scion x) a)))
  :hints (("Goal" :in-theory (disable lambda-object-formals lambda-object-body)))
  :rule-classes ((:meta
                  :trigger-fns (sum$+
                                always$+
                                thereis$+
                                collect$+
                                append$+
                                until$+
                                when$+))))

