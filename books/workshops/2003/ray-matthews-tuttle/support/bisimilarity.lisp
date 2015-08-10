(in-package "ACL2")

;; The following two lines are added for portability to v2-7.


#|

  bisimilarity.lisp
  ~~~~~~~~~~~~~~~~~

We take a step back now, and define the concepts of bisimilarity inside
ACL2. The text-book definition of bisimilarity is as follows. A relation B
between states of two Kripke Structures m and n is a bisimilarity relation if
for every initial state of m there is an initial state in n such that B holds,
and for every pair of states in which B holds, there is a next state for which
B holds. Two models are said to be bisimulation equivalent if such a relation
exists between the two models.

The theory of bisimulation, frankly, is a higher order theory and, ACL2 (my
apologies to Matt and J) cannot deal with it. However, we do what feeble
efforts we can possibly master, and try to do as much work as possible with the
encapsulations in ACL2. However, I strongly believe that treatment like this in
ACL2 is nothing more than a hack.

As an afterthought, we implement bisimilarity here, with respect to a given
collection of variables. What this means is that two states will be called
bisimilar if they have the same value for the given set of variables in the
label, and for every next state of these states, the next states are bisimilar
wrt the same set of variables. This is useful for reduction algorithms for
model-checking that we are interested in, and will let us do away with
hand-waving statements of the form that two states are bisimilar with labelling
restricted to C.

|#

;; Since we do not want to see ACL2 reduce mv-nth 0 to car etc. we do the
;; following tricks. I should ask Matt to have these as macro's or as a syntaxp
;; hypothesis and disable mv-nth.

(defthm mv-nth-0-reduce
  (equal (mv-nth 0 (mv x y z)) x))

(defthm mv-nth-1-reduce
  (equal (mv-nth 1 (mv x y z)) y))

(defthm mv-nth-2-reduce
  (equal (mv-nth 2 (mv x y z)) z))

(in-theory (disable mv-nth)) ;; We do not need to disable mv since mv is a
                             ;; macro.

;; End of macros for mv-nth.

;; The book ltl is included here since I will use the Kripke Structures there
;; to define my bisimilarity.

(include-book "ltl")

;; These two rules are found to be expensive, which is obvious given what these
;; rules are. I disable them here and in cone-of-influence.lisp and the proof
;; is much much faster.

(in-theory (disable subset-of-empty-is-empty
                    subset-of-nil-is-nil))

;; Now we encapsulate the property of bisimilarity for two states. Briefly, two
;; states are bisimilar if they have labels equal within vars, and for every
;; next state of one, there exists a next state of another that is bisimilar.

(encapsulate
 (((bisimilar * * * * *) => *)
  ((bisimilar-transition-witness-m->n * * * * * *) => *)
  ((bisimilar-initial-state-witness-m->n * * * *) => *)
  ((bisimilar-transition-witness-n->m * * * * * *) => *)
  ((bisimilar-initial-state-witness-n->m * * * *) => *)
  ((bisimilar-equiv * * *) => *))

 (local
  (defun bisimilar (p m q n vars)
    (declare (ignore vars))
    (and (equal p q)
         (equal m n)))
  )

 (local
  (defun bisimilar-transition-witness-m->n (p r m q n vars)
    (declare (ignore p m q n vars))
    r)
  )

 (local
  (defun bisimilar-initial-state-witness-m->n (s m n vars)
    (declare (ignore m n vars))
    s)
  )


 (local
  (defun bisimilar-transition-witness-n->m (p m q r n vars)
    (declare (ignore p m q n vars))
    r)
  )

 (local
  (defun bisimilar-initial-state-witness-n->m (m s n vars)
    (declare (ignore m n vars))
    s)
  )

 (local
  (defun bisimilar-equiv (m n vars)
    (declare (ignore vars))
    (equal m n))
  )


 ;; If two Kripke Structures m and n are equivalent with respect to a bisimilar
 ;; relation B, then for every initial-state of m there is a initial-state of n
 ;; that is bisimilar.

 (defthm bisimilar-equiv-implies-init->init-m->n
   (implies (and (bisimilar-equiv m n vars)
                 (memberp s (initial-states m)))
            (memberp (bisimilar-initial-state-witness-m->n s m n vars)
                     (initial-states n))))

 (defthm bisimilar-equiv-implies-bisimilar-initial-states-m->n
   (implies (and (bisimilar-equiv m n vars)
                 (memberp s (initial-states m)))
            (bisimilar s m
                       (bisimilar-initial-state-witness-m->n s m n vars)
                       n vars)))

 ;; And the same result holds for n to m

 (defthm bisimilar-equiv-implies-init->init-n->m
   (implies (and (bisimilar-equiv m n vars)
                 (memberp s (initial-states n)))
            (memberp (bisimilar-initial-state-witness-n->m m s n vars)
                     (initial-states m))))

 (defthm bisimilar-equiv-implies-bisimilar-initial-states-n->m
   (implies (and (bisimilar-equiv m n vars)
                 (memberp s (initial-states n)))
            (bisimilar (bisimilar-initial-state-witness-n->m m s n vars)
                       m s n vars)))

 ;; Bisimilar states have the same label with respect to vars. I just use
 ;; set-equality because they might not have "equal" labels. BTW, I might not
 ;; need the modelp hypothesis here. But I plug it in, just so that I can keep
 ;; the (functional instance of) bisimilarity relation as simple as possible.

 (defthm bisimilar-states-have-labels-equal
   (implies (and (bisimilar p m q n vars)
                 (modelp m)
                 (modelp n))
            (set-equal (set-intersect (label-of p m) vars)
                       (set-intersect (label-of q n) vars))))



 ;; Of course bisimilarity witness is a member of states of the corresponding model.

 (defthm bisimilar-witness-member-of-states-m->n
   (implies (and (bisimilar p m q n vars)
                 (next-statep p r m)
                 (memberp r (states m)))
            (memberp (bisimilar-transition-witness-m->n p r m q n vars)
                     (states n))))

 ;; Again this part may not be required.

 (defthm bisimilar-witness-member-of-states-n->m
   (implies (and (bisimilar p m q n vars)
                 (next-statep q r n)
                 (memberp r (states n)))
            (memberp  (bisimilar-transition-witness-n->m p m q r n vars)
                      (states m))))

 ;; And if two states are bisimilar, then for every next state of one, there is
 ;; a next state of another which is bisimilar.

 (defthm bisimilar-witness-matches-transition-m->n
   (implies (and (bisimilar p m q n vars)
                 (next-statep p r m))
            (next-statep q (bisimilar-transition-witness-m->n p r m q n vars)
                         n)))

 (defthm bisimilar-witness-produces-bisimilar-states-m->n
   (implies (and (bisimilar p m q n vars)
                 (next-statep p r m))
            (bisimilar r m
                       (bisimilar-transition-witness-m->n p r m q n vars)
                       n vars)))

 ;; Again this part may not be required.

 (defthm bisimilar-witness-matches-transition-n->m
   (implies (and (bisimilar p m q n vars)
                  (next-statep q r n))
            (next-statep p (bisimilar-transition-witness-n->m p m q r n vars)
                         m)))



 (defthm bisimilar-witness-produces-bisimilar-states-n->m
   (implies (and (bisimilar p m q n vars)
                 (next-statep q r n))
            (bisimilar (bisimilar-transition-witness-n->m p m q r n vars)
                       m r n vars)))

)

;; The next phase of the book is to show that if two Kripke Structures are
;; bisim-equiv, then for each periodic path of one, there exists a periodic
;; path of another that has the same labels within vars. This finally will show
;; that for any LTL formula restricted to the variable set in vars, the
;; evaluation of the formula wrt bisimilar structures is identical.


;; In find-matching-path-for-path, we create a finite path in n that is
;; bisimilar to a (finite) path in m.

(defun find-matching-path-for-path-m->n (path m q n vars)
  (cond ((endp path) nil)
        ((endp (rest path)) (list q))
        (t (cons q (find-matching-path-for-path-m->n
                    (rest path) m
                    (bisimilar-transition-witness-m->n
                     (first path) (second path) m q n vars)
                    n vars)))))

;; And a similar function from n to m. This is really unfortunate. We could
;; have gotten rid of this duplication if we could rely on symmetry. But I want
;; the encapsulation to provide me with as little constraint as possible.

(defun find-matching-path-for-path-n->m (p m path n vars)
  (cond ((endp path) nil)
        ((endp (rest path)) (list p))
        (t (cons p (find-matching-path-for-path-n->m
                    (bisimilar-transition-witness-n->m
                     p m (first path) (second path) n vars)
                    m (rest path)
                    n vars)))))


;; The function to handle periodic paths is rather complicated, and needs to be
;; decomposed. Here is our solution.

(defun snoc (x e)
  (if (endp x) (list e)
    (cons (first x) (snoc (rest x) e))))

(defun del-last (x)
  (if (endp x) nil
    (if (endp (rest x)) nil
      (cons (first x) (del-last (rest x))))))

(defthm del-last-snoc-reduction
  (implies (true-listp x)
           (equal (del-last (snoc x e)) x)))


(defun find-prefix (cycle seen witness path)
  (cond ((endp path) nil)
        ((endp seen) path) ;; should not arise
        ((equal witness (first seen)) nil)
        (t (append (first-n (len cycle) path) (find-prefix
                                               cycle (rest seen) witness
                                               (last-n (len cycle) path))))))

(defun find-cycle (cycle seen witness path)
  (cond ((endp seen) nil) ;; should not arise
        ((endp path) nil)
        ((equal witness (first seen)) path)
        (t (find-cycle cycle (rest seen) witness (last-n (len cycle) path)))))

;; ACL2 is really stupid in arithmetic. I just add Robert's collection of
;; arithmetic books to get it thru with what I want. I need arithmetic really for
;; very weird reasons, but well, what the heck, I dont want to deal with
;; arithmetic myself any ways.

(local
(include-book "../../../../arithmetic-2/meta/top")
)

(local
(defthm len-of-snoc-is-more
  (< (len x) (len (snoc x e)))
  :rule-classes :linear)
)

;; The following function determines a weird path in n, when given a cycle in
;; m. The weird path is a finite path compatible with n, and can be thought of
;; as the append of the prefix and cycle.

(defun find-matching-prefix-and-cycle-for-cycle-m->n (cycle m seen q states n vars path)
  (declare (xargs :measure (nfix (- (1+ (len states)) (len seen)))))
  ;; for termination using Pigeon-hole arguments
  (if (< (len states) (len seen)) (mv seen q path)
    (let* ((path-produced (find-matching-path-for-path-m->n
                           cycle m q n vars))
           (node-witness (bisimilar-transition-witness-m->n
                          (last-val cycle) (first cycle) m
                          (last-val path-produced) n vars)))
      (if (memberp node-witness seen)
          (mv (snoc seen node-witness) node-witness (append path path-produced))
        (find-matching-prefix-and-cycle-for-cycle-m->n cycle m (snoc seen node-witness)
                                                       node-witness states n
                                                       vars (append path
                                                                    path-produced))))))

(defun find-matching-prefix-and-cycle-for-cycle-n->m (seen q states m cycle n vars path)
  (declare (xargs :measure (nfix (- (1+ (len states)) (len seen)))))
  ;; for termination using Pigeon-hole arguments
  (if (< (len states) (len seen)) (mv seen q path)
    (let* ((path-produced (find-matching-path-for-path-n->m
                           q m cycle n vars))
           (node-witness (bisimilar-transition-witness-n->m
                          (last-val path-produced)  m
                          (last-val cycle) (first cycle)  n vars)))
      (if (memberp node-witness seen)
          (mv (snoc seen node-witness) node-witness (append path path-produced))
        (find-matching-prefix-and-cycle-for-cycle-n->m (snoc seen node-witness)
                                                       node-witness states m
                                                       cycle n
                                                       vars (append path
                                                                    path-produced))))))


;; And we pick up the prefix from the weird path

(defun find-matching-prefix-for-cycle-m->n (cycle m q n vars)
  (mv-let (seen witness path)
          (find-matching-prefix-and-cycle-for-cycle-m->n
           cycle m (list q) q (states n) n vars nil)
          (find-prefix cycle (del-last seen) witness path)))

(defun find-matching-prefix-for-cycle-n->m (q m cycle n vars)
  (mv-let (seen witness path)
          (find-matching-prefix-and-cycle-for-cycle-n->m
           (list q) q (states m) m cycle n vars nil)
          (find-prefix cycle (del-last seen) witness path)))


;; and also the cycle.

(defun find-matching-cycle-for-cycle-m->n (cycle m q n vars)
  (mv-let (seen witness path)
          (find-matching-prefix-and-cycle-for-cycle-m->n
           cycle m (list q) q (states n) n vars nil)
          (find-cycle cycle (del-last seen) witness path)))

(defun find-matching-cycle-for-cycle-n->m (q m cycle n vars)
  (mv-let (seen witness path)
          (find-matching-prefix-and-cycle-for-cycle-n->m
           (list q) q (states m) m cycle n vars nil)
          (find-cycle cycle (del-last seen) witness path)))

;; So we can now produce the matching periodic path by appending the prefix
;; after the matching path for the prefix and the cycle as we obtained.

(defun find-matching-periodic-path-m->n (ppath m n vars)
  (let* ((init-p (initial-state ppath))
         (prefix-p (prefix ppath))
         (first-p (first prefix-p))
         (cycle-p (cycle ppath))
         (init-q (bisimilar-initial-state-witness-m->n init-p m n vars))
         (first-q (bisimilar-transition-witness-m->n init-p first-p m init-q n
                                                     vars))
         (match-path (find-matching-path-for-path-m->n prefix-p m first-q n
                                                       vars))
         (last-p (last-val prefix-p))
         (last-q (last-val match-path))
         (first-cp (first cycle-p))
         (first-cq (bisimilar-transition-witness-m->n last-p first-cp m last-q
                                                      n vars))
         (match-prefix (find-matching-prefix-for-cycle-m->n
                        cycle-p m first-cq n vars))
         (match-cycle (find-matching-cycle-for-cycle-m->n
                       cycle-p m first-cq n vars)))
    (>_ :initial-state init-q
        :prefix (append match-path match-prefix)
        :cycle match-cycle)))

(defun find-matching-periodic-path-n->m (m ppath n vars)
  (let* ((init-q (initial-state ppath))
         (prefix-q (prefix ppath))
         (first-q (first prefix-q))
         (cycle-q (cycle ppath))
         (init-p (bisimilar-initial-state-witness-n->m m init-q n vars))
         (first-p (bisimilar-transition-witness-n->m init-p m init-q first-q n
                                                     vars))
         (match-path (find-matching-path-for-path-n->m first-p m prefix-q n
                                                       vars))
         (last-q (last-val prefix-q))
         (last-p (last-val match-path))
         (first-cq (first cycle-q))
         (first-cp (bisimilar-transition-witness-n->m last-p m last-q first-cq
                                                      n vars))
         (match-prefix (find-matching-prefix-for-cycle-n->m
                        first-cp m cycle-q n vars))
         (match-cycle (find-matching-cycle-for-cycle-n->m
                       first-cp m cycle-q n vars)))
    (>_ :initial-state init-p
        :prefix (append match-path match-prefix)
        :cycle match-cycle)))


;; Now we bite the bullet and start showing that this dirty bad function suits
;; our purpose. Any suggestions for improvement will be greatly appreciated.

;; Let us define the general concept of what we mean by two paths (or segments
;; being bisimilar.


(local
(defun bisimilar-segments-p (p m q n vars)
  (if (endp p) (endp q)
    (and (consp q)
         (bisimilar (first p) m (first q) n vars)
         (bisimilar-segments-p (rest p) m (rest q) n vars))))
)

;; And of course we can then define when a sequence of segments appended
;; together is bisimilar.


(local
(defun bisimilar-segments-sequence-p (p m q n vars)
  (declare (xargs :measure (len q)))
  (if (endp q) T
    (if (or (endp p) (< (len q) (len p))) nil
      (and (bisimilar-segments-p p m (first-n (len p) q) n vars)
           (bisimilar-segments-sequence-p p m (last-n (len p) q)  n vars)))))
)

(local
(defun bisimilar-segments-sequence-p-2 (p m q n vars)
  (declare (xargs :measure (len p)))
  (if (endp p) T
    (if (or (endp q) (< (len p) (len q))) nil
      (and (bisimilar-segments-p (first-n (len q) p) m q n vars)
           (bisimilar-segments-sequence-p-2 (last-n (len q) p) m q n vars)))))
)


;; Of course now, we know that find-matching-path produces a bisimilar path.

(local
(defthm find-matching-path-produces-bisimilar-segments
  (implies (and (compatible-path-p p m)
                (bisimilar (first p) m q n vars))
           (bisimilar-segments-p
            p m
            (find-matching-path-for-path-m->n p m q n vars)
            n vars)))
)

(local
(defthm find-matching-path-produces-bisimilar-segments-2
  (implies (and (compatible-path-p q n)
                (bisimilar p m (first q) n vars))
           (bisimilar-segments-p
            (find-matching-path-for-path-n->m p m q n vars)
            m q
            n vars)))
)

;; and bisimilar paths have the same length.

(local
(defthm bisimilar-to-length
  (implies (bisimilar-segments-p p m q n vars)
           (equal (len p) (len q)))
  :rule-classes :forward-chaining)
)

(local
(defthm len-of-append
  (equal (len (append x y))
         (+ (len x) (len y))))
)

(local
(defthm last-n-is-true-listp
  (implies (true-listp p)
           (true-listp (last-n i p))))
)

(local
(defthm first-last-append-reduction-2
  (implies (<= i (len x))
           (equal (append x y)
                  (append (first-n i x) (append (last-n i x) y)))))
)

(local
(defthm first-n-reduced
  (implies (and (equal (len x) i)
                (true-listp x))
           (equal (first-n i x) x)))
)

(local
(defthm last-n-reduced
  (implies (and (<= (len x) i)
                (integerp i)
                (true-listp x))
           (equal (last-n i x) nil)))
)

;; and bisimilar segements would also be bisimilar-segments-sequence.

(local
(defthm bisimilar-segments-are-bisimilar-segment-sequences
  (implies (and (bisimilar-segments-p p m q n vars)
                (true-listp p)
                (true-listp q)
                (consp p))
           (bisimilar-segments-sequence-p p m q n vars))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize)
           :induct (bisimilar-segments-sequence-p p m q n vars)
           :do-not-induct t)))
)

(local
(defthm bisimilar-segments-are-bisimilar-segment-sequences-2
  (implies (and (bisimilar-segments-p p m q n vars)
                (true-listp p)
                (true-listp q)
                (consp q))
           (bisimilar-segments-sequence-p-2 p m q n vars))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize)
           :induct (bisimilar-segments-sequence-p-2 p m q n vars)
           :do-not-induct t)))
)

;; which when appended will produce bisimilar segments sequence.

(local
(defthm append-of-bisimilar-segments-produces-bisimilar-segment-list
  (implies (and (bisimilar-segments-p p m r n vars)
                (consp p)
                (true-listp r)
                (true-listp p)
                (true-listp q)
                (bisimilar-segments-sequence-p p m q n vars))
           (bisimilar-segments-sequence-p p m (append q r) n vars))
  :hints (("Goal"
           :do-not '(generalize eliminate-destructors)
           :do-not-induct t
           :induct (bisimilar-segments-sequence-p p m q n vars))))
)

(local
(defthm append-of-bisimilar-segments-produces-bisimilar-segment-list-2
  (implies (and (bisimilar-segments-p r m q n vars)
                (consp q)
                (true-listp r)
                (true-listp p)
                (true-listp q)
                (bisimilar-segments-sequence-p-2 p m q n vars))
           (bisimilar-segments-sequence-p-2 (append p r) m q n vars))
  :hints (("Goal"
           :do-not '(generalize eliminate-destructors)
           :do-not-induct t
           :induct (bisimilar-segments-sequence-p-2 p m q n vars))))
)

;; and the prefix of bisimilar segements sequence is a
;; bisimialr-segments-sequence

(local
(defthm prefix-produces-bisimilar-segment-list
  (implies (bisimilar-segments-sequence-p p m q n vars)
           (bisimilar-segments-sequence-p p m (find-prefix p seen witness q) n
                                          vars)))
)

(local
(defthm prefix-produces-bisimilar-segment-list-2
  (implies (bisimilar-segments-sequence-p-2 p m q n vars)
           (bisimilar-segments-sequence-p-2 (find-prefix q seen witness p) m q n
                                          vars)))

)

;; and so is the cycle.

(local
(defthm cycle-produces-bisimilar-segment-list
  (implies (bisimilar-segments-sequence-p p m q n vars)
           (bisimilar-segments-sequence-p p m (find-cycle p seen witness q) n
                                          vars)))
)

(local
(defthm cycle-produces-bisimilar-segment-list-2
  (implies (bisimilar-segments-sequence-p-2 p m q n vars)
           (bisimilar-segments-sequence-p-2  (find-cycle q seen witness p) m q n
                                          vars)))
)

;; Also the last-vals of compatible paths is bisimilar.

(local
(defthm last-vals-are-bisimilar
  (implies (and (compatible-path-p path m)
                (consp path)
                (bisimilar (first path) m q n vars))
           (bisimilar (last-val path) m
                      (last-val (find-matching-path-for-path-m->n path m q n
                                                                  vars))
                      n vars)))
)

(local
(defthm last-vals-are-bisimilar-2
  (implies (and (compatible-path-p path n)
                (consp path)
                (bisimilar p m (first path) n vars))
           (bisimilar (last-val (find-matching-path-for-path-n->m p m path n
                                                                  vars))
                      m (last-val path)
                      n vars)))
)



(local
(defthm true-listp-append-reduction
  (implies (true-listp y)
           (true-listp (append x y))))
)

;; and therefore, finally, the segment produced by find-prefix-and-cycle is
;; bisimilar segments sequence-p

(local
(defthm matching-prefix-and-cycle-produces-bisimilar-segment-list
  (implies (and (consp cycle)
                (true-listp path)
                (bisimilar-segments-sequence-p cycle m path n vars)
                (compatible-path-p cycle m)
                (next-statep (last-val cycle) (first cycle) m)
                (bisimilar (first cycle) m q n vars))
           (bisimilar-segments-sequence-p
            cycle m
            (mv-nth
             2
             (find-matching-prefix-and-cycle-for-cycle-m->n
              cycle m seen q
              states n vars path))
            n vars)))
)

(local
(defthm matching-prefix-and-cycle-produces-bisimilar-segment-list-2
  (implies (and (consp cycle)
                (true-listp path)
                (bisimilar-segments-sequence-p-2 path m cycle n vars)
                (compatible-path-p cycle n)
                (next-statep (last-val cycle) (first cycle) n)
                (bisimilar q m (first cycle) n vars))
           (bisimilar-segments-sequence-p-2
            (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-n->m
                       seen q states m cycle n vars path))
            m cycle
            n vars))
  :hints (("Goal"
           :induct (find-matching-prefix-and-cycle-for-cycle-n->m
                                                      seen q states m cycle n
                                                      vars path)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t)))
)


;; which means that the prefix is bisimilar segments sequence

(local
(defthm find-matching-prefix-is-bisimilar-segments-p
  (implies (and (consp cycle)
                (compatible-path-p cycle m)
                (next-statep (last-val cycle) (car cycle) m)
                (bisimilar (first cycle) m q n vars))
           (bisimilar-segments-sequence-p
            cycle m (find-matching-prefix-for-cycle-m->n cycle m q n vars) n
            vars)))
)

(local
(defthm find-matching-prefix-is-bisimilar-segments-p-2
  (implies (and (consp cycle)
                (compatible-path-p cycle n)
                (next-statep (last-val cycle) (car cycle) n)
                (bisimilar q m (first cycle) n vars))
           (bisimilar-segments-sequence-p-2
            (find-matching-prefix-for-cycle-n->m q m cycle n vars) m cycle n
            vars)))
)

;; and so is the cycle.

(local
(defthm find-matching-cycle-is-bisimilar-segments-p
  (implies (and (consp cycle)
                (compatible-path-p cycle m)
                (next-statep (last-val cycle) (car cycle) m)
                (bisimilar (first cycle) m q n vars))
           (bisimilar-segments-sequence-p
            cycle m (find-matching-cycle-for-cycle-m->n cycle m q n vars) n
            vars)))

)

(local
(defthm find-matching-cycle-is-bisimilar-segments-p-2
  (implies (and (consp cycle)
                (compatible-path-p cycle n)
                (next-statep (last-val cycle) (car cycle) n)
                (bisimilar q m (first cycle) n vars))
           (bisimilar-segments-sequence-p-2
            (find-matching-cycle-for-cycle-n->m q m cycle n vars) m cycle n
            vars)))

)

;; Now of course, a periodic path is bisimilar to another if the following
;; holds.

(local
(defun bisimilar-periodic-paths-p (p m q n vars)
  (and (bisimilar (initial-state p) m (initial-state q) n vars)
       (or (and (bisimilar-segments-p (prefix p) m
                                      (first-n (len (prefix p)) (prefix q))
                                      n vars)
                (bisimilar-segments-sequence-p
                 (cycle p) m
                 (last-n (len (prefix p)) (prefix q)) n vars)
                (bisimilar-segments-sequence-p (cycle p) m (cycle q) n vars))
           (and (bisimilar-segments-p (first-n (len (prefix q)) (prefix p)) m
                                      (prefix q) n vars)
                (bisimilar-segments-sequence-p-2 (last-n (len (prefix q))
                                                         (prefix p))
                                                 m (cycle q) n vars)
                (bisimilar-segments-sequence-p-2
                 (cycle p) m (cycle q) n vars)))))

)

;; We need to show that find-matching-periodic-path-m->ns produce
;; bisimilar-periodic-paths-p.


;; And we need to append things the other way around to get it through.

(local
(in-theory (disable find-matching-prefix-for-cycle-m->n
                    find-matching-cycle-for-cycle-m->n
                    find-matching-prefix-for-cycle-n->m
                    find-matching-cycle-for-cycle-n->m))
)

(local
(defthm find-matching-path-for-path-has-same-len
  (equal (len (find-matching-path-for-path-m->n p m q n vars))
         (len p)))
)

(local
(defthm find-matching-path-for-path-has-same-len-2
  (equal (len (find-matching-path-for-path-n->m p m q n vars))
         (len q)))
)

(local
(defthm find-matching-periodic-path-m->n-produces-bisimilar-periodic-paths
  (implies (and (compatible-ppath-p ppath m)
                (bisimilar-equiv m n vars))
           (bisimilar-periodic-paths-p ppath m
                                       (find-matching-periodic-path-m->n
                                        ppath m n
                                        vars)
                                       n vars))
  :hints (("Goal"
           :do-not-induct t)))
)

(local
(defthm find-matching-periodic-path-m->n-produces-bisimilar-periodic-paths-2
  (implies (and (compatible-ppath-p ppath n)
                (bisimilar-equiv m n vars))
           (bisimilar-periodic-paths-p
            (find-matching-periodic-path-n->m m ppath n
                                              vars)
            m ppath
            n vars))
  :hints (("Goal"
           :do-not-induct t)))
)

;; Now let us prove that bisimilar periodic paths have labels equal.


(local
 (in-theory (disable set-equal set-intersect))
 )

(local
(defthm bisimilar-segments-have-equal-labels
  (implies (and (bisimilar-segments-p p m q n vars)
                (modelp m)
                (modelp n))
           (equal-label-segments-p p m q n vars)))
)

(local
(defthm bisimilar-segments-sequence-p-have-equal-labels
  (implies (and (bisimilar-segments-sequence-p p m q n vars)
                (modelp m)
                (modelp n))
           (equal-label-segments-sequence-p-small-p p m q n vars)))
)

(local
(defthm bisimilar-segments-sequence-p-have-equal-labels-2
  (implies (and (bisimilar-segments-sequence-p-2 p m q n vars)
                (modelp m)
                (modelp n))
           (equal-label-segments-sequence-p-large-p p m q n vars)))
)

(local
(defthm bisimilar-periodic-paths-have-equal-labels
  (implies (and (bisimilar-periodic-paths-p p m q n vars)
                (modelp m)
                (modelp n))
           (equal-labels-periodic-path-p p m q n vars)))
)

(local
(in-theory (disable bisimilar-periodic-paths-p equal-labels-periodic-path-p))
)

(local
(defthm ppath-and-its-matching-ppath-have-same-labels
  (implies (and (compatible-ppath-p ppath m)
                (bisimilar-equiv m n vars)
                (modelp m)
                (modelp n))
           (equal-labels-periodic-path-p
            ppath m (find-matching-periodic-path-m->n ppath m n vars) n vars))
  :hints (("Goal"
           :in-theory (disable compatible-ppath-p
                               find-matching-periodic-path-m->n))))

)

(local
(defthm ppath-and-its-matching-ppath-have-same-labels-2
  (implies (and (compatible-ppath-p ppath n)
                (bisimilar-equiv m n vars)
                (modelp m)
                (modelp n))
           (equal-labels-periodic-path-p
            (find-matching-periodic-path-n->m m ppath n vars) m ppath n vars))
  :hints (("Goal"
           :in-theory (disable compatible-ppath-p
                               find-matching-periodic-path-n->m))))

)


;; OK let us now think over what I proved so far. Briefly I have proved that if
;; P is a periodic path in m, and m and n are bisimilar-equivalent, then there
;; is a periodic path which has the same labels. Now what do we need to
;; prove? We need to prove that the periodic path we have proved to have the
;; same label must be a path of n. That is it is compatible with n. If we do
;; that, then we would know that for every path in m there is a path in n that
;; has the same labels. hence we will know that ltl-semantics of m and n for a
;; restricted formula f is same.


;; Unfortunately, this property (though trivial intuitively) is not an easy
;; property for a theorem-proving exercise. It needs a lot of work showing (for
;; example) pigeon-hole principle. I will discuss the issues as we get
;; there. For now, let us start proving each of the constraints of
;; compatible-ppath-p separately. There is no real mystery here, --- I took a
;; printout of ltl.lisp, and decided to prove each of the constraints
;; separately.

;; To prove these constraints separately, I will bear in mind that in the final
;; theorem compatible-ppath-p is going to be enabled. This being a recursive
;; function, we will have to be careful that in the lemmas, we do not have
;; compatible-ppath-p as a hypothesis.

;; The first theorem in our agenda is to show that initial-state of matching
;; ppath is a member of initial states. That is obvious, from the constraints
;; of bisimilar-initial-state-witness.


;; The next theorem is to show that the prefix is a consp. This is because we
;; start with a matching-path of a consp prefix and append of a consp with
;; something is a consp. This is established by the next two theorems.

(local
(defthm prefix-is-a-consp
  (equal (consp (find-matching-path-for-path-m->n path m q n vars))
         (consp path)))
)

(local
(defthm prefix-is-a-consp-2
  (equal (consp (find-matching-path-for-path-n->m q m path n vars))
         (consp path)))
)


(local
(defthm append-expands-to-consp
  (equal (consp (append x y))
         (if (consp x) T (consp y))))
)

;; The next constraint says that the first of the prefix is next state of
;; init. This is trivial from property of bisimilar-transition-witness and the
;; fact that inits of the two models are bisimilar.



;; The next constraint is to show that the cycle is a consp. In other words, we
;; have to show the consp property for find-matching-cycle-for-cyle.  Now why
;; is the cycle consp. Roughly, the reason is as follows. The length of the
;; path produced by prefix and cycle is (len seen) * (len cycle). And the
;; witness is a member of path. seen. Hence the cycle produced is a consp by
;; the next two theorems.

(local
(defthm last-n-len-reduction
  (implies (and (equal (len path) (+ i j))
                (integerp i)
                (integerp j)
                (<= 0 i)
                (<= 0 j))
           (equal (len (last-n i path))
                  j)))
)

(local
(defthm witness-member-of-seen-implies-consp
  (implies (and (memberp witness seen)
                (consp cycle)
                (force (equal (len path) (* (len cycle) (len seen)))))
           (consp (find-cycle cycle seen witness path))))
)

;; However, this leads us to two more proof requirements. Why should the
;; witness be a member of seen, and why should the length of the big path be
;; the product of the length of seen and cycle. We address these two issues
;; below.

(local
(defthm snoc-produces-memberp
  (memberp e (snoc x e)))
)

(local
(defthm snoc-len-reduction
  (equal (len (snoc x e))
         (1+ (len x))))
)

;; We show that the value returned as the seen list has 1 less than what we
;; need, and this will just be figured out by deducting 1 again from the seen
;; list since we remove the last guy.

(local
(defthm len-of-path-is-product-of-two
  (implies (equal (len path) (* (len cycle) (1- (len seen))))
           (equal (len (mv-nth
                        2 (find-matching-prefix-and-cycle-for-cycle-m->n
                           cycle m seen q states n vars path)))
                  (* (len cycle)
                     (1- (len (mv-nth
                               0 (find-matching-prefix-and-cycle-for-cycle-m->n
                                  cycle m seen q states n vars
                                  path))))))))

)

(local
(defthm len-of-path-is-product-of-two-2
  (implies (equal (len path) (* (len cycle) (1- (len seen))))
           (equal (len (mv-nth
                        2 (find-matching-prefix-and-cycle-for-cycle-n->m
                            seen q states m cycle n vars path)))
                  (* (len cycle)
                     (1- (len (mv-nth
                               0
                               (find-matching-prefix-and-cycle-for-cycle-n->m
                                seen q states m cycle n vars
                                path))))))))

)


(local
(defthm del-last-len-reduction
  (implies (consp x)
           (equal (len (del-last x))
                  (1- (len x)))))
)

;; And finally that the seen list is consp

(local
(defthm seen-list-is-consp
  (implies (memberp q seen)
           (consp (mv-nth 0 (find-matching-prefix-and-cycle-for-cycle-m->n
                             cycle m seen q states n vars path))))
  :hints (("Goal"
           :induct (find-matching-prefix-and-cycle-for-cycle-m->n cycle m seen
                                                                  q states n
                                                                  vars path))))

)

(local
(defthm seen-list-is-consp-2
  (implies (memberp q seen)
           (consp (mv-nth 0 (find-matching-prefix-and-cycle-for-cycle-n->m
                             seen q states m cycle n vars path))))
  :hints (("Goal"
           :induct (find-matching-prefix-and-cycle-for-cycle-n->m seen
                                                                  q states m
                                                                  cycle n
                                                                  vars path))))

)

;; Now why should the witness be a member of the seen? The reason is kind of a
;; pigeon-hole argument. The high-level argument is that witness is producing a
;; a member of states all the time, and a new guy every time it produces a
;; non-member of seen so it will exhaust out eventually.


;; First a few reductions using snoc and uniquep. I am lucky that uniquep is
;; already in records which helps a lot.

(local
(defthm snoc-member-reduction
  (equal (memberp a (snoc x e))
         (or (memberp a x)
             (equal a e))))
)

(local
(defthm uniquep-snoc-reduction
  (implies (and (uniquep seen)
                (not (memberp e seen)))
           (uniquep (snoc seen e))))
)

(local
(defthm memberp-del-last-reduction
  (equal (memberp a (del-last (snoc x e)))
         (memberp a x)))
)

(local
(defthm uniquep-dellast-reduction
  (implies (uniquep x)
           (uniquep (del-last (snoc x e)))))
)

(local
(defthm not-memberp-del-reduction
  (implies (not (memberp e x))
           (not (memberp e (del-last x)))))
)

(local
(defthm uniquep-del-last-true
  (implies (uniquep x)
           (uniquep (del-last x))))
)

;; So now, we can show that the seen list is uniquep.

(local
(defthm del-last-seen-is-unique-p
  (implies (uniquep seen)
           (uniquep (del-last (mv-nth 0 (find-matching-prefix-and-cycle-for-cycle-m->n
                                         cycle m seen q states n vars path)))))
  :hints (("Goal"
           :induct (find-matching-prefix-and-cycle-for-cycle-m->n
                               cycle m seen q states n vars path)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t)))
)

(local
(defthm del-last-seen-is-unique-p-2
  (implies (uniquep seen)
           (uniquep (del-last (mv-nth 0 (find-matching-prefix-and-cycle-for-cycle-n->m
                                         seen q states m cycle n vars path)))))
  :hints (("Goal"
           :induct (find-matching-prefix-and-cycle-for-cycle-n->m
                               seen q states m cycle n vars path)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t)))
)

(local
(defthm len-<-states-implies-<witness-memberp
  (implies (case-split (<= (len (mv-nth 0 (find-matching-prefix-and-cycle-for-cycle-m->n
                                           cycle m seen q states n vars path)))
                           (len states)))
           (memberp (mv-nth 1 (find-matching-prefix-and-cycle-for-cycle-m->n
                               cycle m seen q states n vars path))
                    (del-last (mv-nth 0 (find-matching-prefix-and-cycle-for-cycle-m->n
                                         cycle m seen q states n vars path))))))
)

(local
(defthm len-<-states-implies-<witness-memberp-2
  (implies (case-split (<= (len (mv-nth 0 (find-matching-prefix-and-cycle-for-cycle-n->m
                                           seen q states m cycle n vars path)))
                           (len states)))
           (memberp (mv-nth 1 (find-matching-prefix-and-cycle-for-cycle-n->m
                               seen q states m cycle n vars path))
                    (del-last (mv-nth 0 (find-matching-prefix-and-cycle-for-cycle-n->m
                                         seen q states m cycle n vars path))))))
)

(local
(in-theory (enable subset))
)

;; Again, we need to define del. This is because it will be used in the
;; induction hint. I am rpetty sure this is not the shortest path to the proof,
;; but this is how I would have reasoned without ACL2.

(local
(defun del (e x)
  (if (endp x) nil
    (if (equal e (car x)) (cdr x)
      (cons (car x) (del e (cdr x))))))
)

(local
(defthm uniquep-to-not-member
  (implies (uniquep x)
           (not (memberp e (del e x)))))
)

(local
(defthm member-del-reduction
  (implies (not (equal a e))
           (equal (memberp a (del e y))
                  (memberp a y))))
)

(local
(defthm del-subset-reduction
  (implies (and (uniquep x)
                (subset x y))
           (subset (del e x) (del e y))))
)

(local
(defthm len-del-reduction
  (implies (memberp e x)
           (equal (len (del e x))
                  (1- (len x)))))
)

(local
(defun induction-hint (x y)
  (if (endp x) y
    (induction-hint (rest x) (del (first x) y))))
)

(local
(defthm not-memberp-del-reduction-2
  (implies (not (memberp e x))
           (subset x (del e x))))
)

(local
(defthm unique-p-del-subset-reduction
  (implies (and (uniquep x)
                (not (memberp e x))
                (subset x y))
           (subset x (del e y)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance subset-is-transitive
                            (y (del e x))
                            (z (del e y)))))))
)

(local
(defthm uniquep-subset-reduction
  (implies (and (uniquep x)
                (subset x y))
           (<= (len x) (len y)))
  :hints (("Goal"
           :induct (induction-hint x y))))
)

(local
(defthm car-append-reduction
  (equal (car (append x y))
         (if (consp x) (car x) (car y))))
)

(local
(defthm consp-to-car-find-matching-path
  (implies (consp path)
           (equal (car (find-matching-path-for-path-m->n path m q n vars))
                  q)))
)

(local
(defthm consp-to-car-find-matching-path-2
  (implies (consp path)
           (equal (car (find-matching-path-for-path-n->m q m path n vars))
                  q)))
)

(local
(defthm last-val-append-reduction
  (equal (last-val (append x y))
         (if (consp y) (last-val y) (last-val x))))
)

(local
(defthm subset-snoc-reduction
  (implies (and (subset x y)
                (memberp e y))
           (subset (snoc x e) y)))
)

(local
(defthm last-val-bisimilar-reduction
  (implies (and (bisimilar (first cycle) m q n vars)
                (consp cycle)
                (compatible-path-p cycle m))
           (bisimilar (last-val cycle) m (last-val
                                          (find-matching-path-for-path-m->n
                                           cycle m q n vars))
                      n vars)))
)

(local
(defthm last-val-bisimilar-reduction-2
  (implies (and (bisimilar q m (first cycle) n vars)
                (consp cycle)
                (compatible-path-p cycle n))
           (bisimilar (last-val (find-matching-path-for-path-n->m q m cycle n
                                                                  vars))
                      m
                      (last-val cycle)
                      n vars)))
)

(local
(defthm find-matching-path-produces-compatible-path
  (implies (and (compatible-path-p cycle m)
                (consp cycle)
                (memberp q (states n))
                (bisimilar (first cycle) m q n vars))
           (compatible-path-p (find-matching-path-for-path-m->n
                               cycle m q n vars)
                              n)))
)

(local
(defthm find-matching-path-produces-compatible-path-2
  (implies (and (compatible-path-p cycle n)
                (consp cycle)
                (memberp q (states m))
                (bisimilar q m (first cycle) n vars))
           (compatible-path-p (find-matching-path-for-path-n->m
                               q m cycle n vars)
                              m)))
)

;; And finally, I am saying that seen list is a subset of states. (Basically a
;; slightly stronger thing, but that is ok.)


(local
(defthm seen-list-subset-of-states
  (implies (and (subset seen (states n))
                (bisimilar (first cycle) m q n vars)
                (consp cycle)
                (next-statep (last-val cycle) (first cycle) m)
                (compatible-path-p cycle m))
           (subset  (mv-nth 0 (find-matching-prefix-and-cycle-for-cycle-m->n
                                        cycle m seen q states n vars path))
                   (states n)))
  :hints (("Goal"
           :induct  (find-matching-prefix-and-cycle-for-cycle-m->n
                     cycle m seen q states n vars path)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t)))
)

(local
(defthm seen-list-subset-of-states-2
  (implies (and (subset seen (states m))
                (bisimilar q m (first cycle) n vars)
                (consp cycle)
                (next-statep (last-val cycle) (first cycle) n)
                (compatible-path-p cycle n))
           (subset  (mv-nth 0 (find-matching-prefix-and-cycle-for-cycle-n->m
                               seen q states m cycle n vars path))
                   (states m)))
  :hints (("Goal"
           :induct  (find-matching-prefix-and-cycle-for-cycle-n->m
                     seen q states m cycle n vars path)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t)))
)

;; And also that witness is a member of states.

(local
(defthm witness-member-of-states
  (implies (and (memberp q (states n))
                (bisimilar (first cycle) m q n vars)
                (consp cycle)
                (next-statep (last-val cycle) (first cycle) m)
                (compatible-path-p cycle m))
           (memberp  (mv-nth 1 (find-matching-prefix-and-cycle-for-cycle-m->n
                                        cycle m seen q states n vars path))
                   (states n)))
  :hints (("Goal"
           :induct  (find-matching-prefix-and-cycle-for-cycle-m->n
                     cycle m seen q states n vars path)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t)))
)

(local
(defthm witness-member-of-states-2
  (implies (and (memberp q (states m))
                (bisimilar q m (first cycle) n vars)
                (consp cycle)
                (next-statep (last-val cycle) (first cycle) n)
                (compatible-path-p cycle n))
           (memberp  (mv-nth 1 (find-matching-prefix-and-cycle-for-cycle-n->m
                                        seen q states m cycle n vars path))
                   (states m)))
  :hints (("Goal"
           :induct  (find-matching-prefix-and-cycle-for-cycle-n->m
                     seen q states m cycle n vars path)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t)))
)

(local
(defthm subset-remains-for-del
  (implies (subset x y)
           (subset (del-last x) y)))
)

(local
(defthm del-creates-subset
  (subset (del-last x) x))
)

(local
(defthm memberp-to-subset
  (implies (memberp q states)
           (subset (list q) states))
  :rule-classes nil)
)

(local
(defthm uniquep-and-=-and-implies-member
  (implies (and (uniquep x)
                (equal (len x) (len y))
                (subset x y)
                (memberp e y))
           (memberp e x))
  :hints (("Goal"
           :induct (induction-hint x y))))
)

;; Then finally, I am done. I am saying here that the matching cycle is a
;; consp. Matt might just not like the use hints I force, but there seems to be
;; no simpler route. I would be interested to know if someone can simplify this
;; proof.

(local
(defthm find-matching-cycle-for-cycle-is-consp
  (implies (and (memberp q (states n))
                (consp cycle)
                (compatible-path-p cycle m)
                (bisimilar (first cycle) m q n vars)
                (next-statep (last-val cycle) (first cycle) m))
           (consp (find-matching-cycle-for-cycle-m->n cycle m q n vars)))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize)
           :expand (find-matching-cycle-for-cycle-m->n cycle m q n vars)
           :do-not-induct t
           :in-theory (disable witness-member-of-seen-implies-consp)
           :use ((:instance  witness-member-of-seen-implies-consp
                             (witness (mv-nth 1 (find-matching-prefix-and-cycle-for-cycle-m->n
                                                 cycle m (list q) q (states n)
                                                 n vars nil)))
                             (seen (del-last (mv-nth 0
                                                     (find-matching-prefix-and-cycle-for-cycle-m->n
                                                      cycle m (list q) q (states n) n
                                                      vars nil))))
                             (path (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-m->n
                                              cycle m (list q) q (states n) n
                                              vars nil))))
                 (:instance  uniquep-subset-reduction
                             (x (del-last (mv-nth 0 (find-matching-prefix-and-cycle-for-cycle-m->n
                                                     cycle m (list q) q (states n) n vars nil))))
                             (y (states n)))
                 (:instance uniquep-and-=-and-implies-member
                            (x (del-last (mv-nth 0 (find-matching-prefix-and-cycle-for-cycle-m->n
                                                    cycle m (list q) q (states n)
                                                    n vars nil))))
                            (y (states n))
                            (e (mv-nth 1 (find-matching-prefix-and-cycle-for-cycle-m->n
                                                    cycle m (list q) q (states n)
                                                    n vars nil))))))))
)


(local
(defthm find-matching-cycle-for-cycle-is-consp-2
  (implies (and (memberp q (states m))
                (consp cycle)
                (compatible-path-p cycle n)
                (bisimilar q m (first cycle) n vars)
                (next-statep (last-val cycle) (first cycle) n))
           (consp (find-matching-cycle-for-cycle-n->m q m cycle n vars)))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize)
           :expand (find-matching-cycle-for-cycle-n->m q m cycle n vars)
           :do-not-induct t
           :in-theory (disable witness-member-of-seen-implies-consp)
           :use ((:instance  witness-member-of-seen-implies-consp
                             (witness (mv-nth 1 (find-matching-prefix-and-cycle-for-cycle-n->m
                                                 (list q) q (states m) m cycle
                                                 n vars nil)))
                             (seen (del-last (mv-nth 0
                                                     (find-matching-prefix-and-cycle-for-cycle-n->m
                                                      (list q) q (states m) m
                                                      cycle n
                                                      vars nil))))
                             (path (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-n->m
                                              (list q) q (states m) m
                                              cycle n
                                              vars nil))))
                 (:instance  uniquep-subset-reduction
                             (x (del-last (mv-nth 0 (find-matching-prefix-and-cycle-for-cycle-n->m
                                                     (list q) q (states m) m
                                                     cycle n
                                                     vars nil))))
                             (y (states m)))
                 (:instance uniquep-and-=-and-implies-member
                            (x (del-last (mv-nth 0 (find-matching-prefix-and-cycle-for-cycle-n->m
                                                    (list q) q (states m) m
                                                    cycle
                                                    n vars nil))))
                            (y (states m))
                            (e (mv-nth 1 (find-matching-prefix-and-cycle-for-cycle-n->m
                                                     (list q) q (states m) m
                                                     cycle n vars nil))))))))
)

;; The next theorem in our agenda is to prove that the prefix of the matching
;; path is compatible-path-p. Notice we have already proved that
;; find-matching-path produces a compatible-path-p. So we need to prove that
;; prefix-and-cycle produces the same, and then say that append of two "good"
;; compatible paths is a compatible path.

(local
(defthm compatible-path-append-reduction
  (implies (force (and (true-listp x)
                       (true-listp y)))
  (equal (compatible-path-p (append x y) m)
         (if (not (consp x)) (compatible-path-p y m)
           (if (not (consp y)) (compatible-path-p x m)
             (and (compatible-path-p x m)
                  (compatible-path-p y m)
                  (next-statep (last-val x) (first y) m)))))))
)


;; While we are at it, let us show that the first-n and last-n are
;; compatible-paths

(local
(defthm consp-and-i>=-first-n-reduction
  (implies (and (consp p)
                (integerp i)
                (< 0 i))
           (equal (car (first-n i p))
                  (car p))))
)

(local
(defthm compatible-path-first-n-reduction
  (implies (and (compatible-path-p p m)
                (integerp i)
                (<= 0 i)
                (<= i (len p)))
           (compatible-path-p (first-n i p) m))
  :hints (("Goal"
           :induct (first-n i p)
           :in-theory (enable zp)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t)
          ("Subgoal *1/2"
           :cases ((zp (1- i))))))
)

(local
(defthm compatible-path-last-n-reduction
  (implies (and (compatible-path-p p m)
                (integerp i)
                (<= 0 i)
                (<= i (len p)))
           (compatible-path-p (last-n i p) m))
  :hints (("Goal"
           :induct (last-n i p)
           :in-theory (enable zp)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t)
          ("Subgoal *1/2"
           :cases ((zp (1- i))))))
)

;; The theorems above just say that if we could (somehow) prove that
;; find-prefix-and-cycle produces a compatible path then I would immediately
;; know that the prefix and cycle are both compatible.

;; Now why should find-prefix-and-cycle produce a compatible path? For
;; something to be a compatible path, what we need is that every state in the
;; path is a member of states and the next state is a next-statep.  So let us
;; prove these properties separately.

;; Informally here is what happens. I know that the last-val of
;; find-matching-path is bisimilar to last-val of cycle. and is a member of
;; states. Hence, the bisimilar witness it produces with the first of cycle is
;; a next-statep (Notice that next-statep is true for last-val and car of
;; cycle.) Hence the paths produced by recursive calls can be appended together
;; to produce a compatible path if path (the initial segment of the accumulator
;; is known to be a compatible path.


(local
(defthm last-val-of-find-matching-prefix-is-member-of-states
  (implies (and (bisimilar (first cycle) m q n vars)
                (consp cycle)
                (compatible-path-p cycle m)
                (memberp q (states n)))
           (memberp (last-val (find-matching-path-for-path-m->n
                               cycle m q n vars))
                    (states n))))
)

(local
(defthm find-prefix-and-cycle-produces-compatible-path
  (implies (and (bisimilar (first cycle) m q n vars)
                (compatible-path-p path n)
                (compatible-path-p (append path
                                           (find-matching-path-for-path-m->n
                                            cycle m q n vars))
                                   n)
                (consp cycle)
                (memberp q (states n))
                (next-statep (last-val cycle) (car cycle) m)
                (compatible-path-p cycle m))
           (compatible-path-p (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-m->n
                                         cycle m seen q (states n) n vars path))
                                      n))
  :hints (("Goal"
           :induct (find-matching-prefix-and-cycle-for-cycle-m->n
                    cycle m seen q (states n) n vars path)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t)))
)

(local
(defthm find-prefix-and-cycle-produces-compatible-path-2
  (implies (and (bisimilar q m (first cycle) n vars)
                (compatible-path-p path m)
                (compatible-path-p (append path
                                           (find-matching-path-for-path-n->m
                                            q m cycle n vars))
                                   m)
                (consp cycle)
                (memberp q (states m))
                (next-statep (last-val cycle) (car cycle) n)
                (compatible-path-p cycle n))
           (compatible-path-p (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-n->m
                                         seen q (states m) m cycle n vars path))
                                      m))
  :hints (("Goal"
           :induct (find-matching-prefix-and-cycle-for-cycle-n->m
                    seen q (states m) m cycle n vars path)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t)))
)

;; Now that we know that find-prefix-and-cycle-is-a-compatible-path-p, and also
;; that first-n of a compatible path is a compatible path, and also append
;; produces compatible paths, we should be able to prove that
;; find-matching-prefix and find-matching-cycle produce compatible paths.

;; Well, it does not seem to be as simple as it looks. The problem is in
;; getting the induction working right.

;; To do work with find-matching-prefix we define the index such that
;; find-prefix produces that index.


(local
(defun find-prefix-index (cycle seen witness path)
  (cond ((endp path) 0)
        ((endp seen) (len path))
        ((equal witness (first seen)) 0)
        (t (+ (len cycle)
              (find-prefix-index cycle (rest seen) witness (last-n (len cycle) path))))))
)

(local
(defthm first-n+-reduction
  (implies (and (integerp i)
                (integerp j)
                (<= 0 i)
                (<= 0 j))
           (equal (first-n (+ i j) x)
                  (append (first-n i x) (first-n j (last-n i x))))))
)

(local
(defthm last-n+-reduction
  (implies (and (integerp i)
                (integerp j)
                (<= 0 i)
                (<= 0 j))
           (equal (last-n (+ i j) x)
                  (last-n j (last-n i x)))))
)

(local
(defthm find-prefix-with-index
  (implies (and (true-listp path)
                (equal (len path) (* (len cycle) (len seen))))
           (equal (find-prefix cycle seen witness path)
                  (first-n (find-prefix-index cycle seen witness path) path))))
)

(local
(defthm find-cycle-with-index
  (implies (and (equal (len path) (* (len cycle) (len seen)))
                (true-listp path))
           (equal (find-cycle cycle seen witness path)
                  (last-n (find-prefix-index cycle seen witness path) path))))
)

(local
(defthm index-is-an-integer->=0
  (and (integerp (find-prefix-index cycle seen witness path))
       (<= 0 (find-prefix-index cycle seen witness path)))
  :rule-classes :type-prescription)
)

(local
(defthm prefix-and-cycle-produces-true-listp
  (implies (true-listp path)
           (true-listp (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-m->n
                                  cycle m q seen states n vars path)))))
)

(local
(defthm prefix-and-cycle-produces-true-listp-2
  (implies (true-listp path)
           (true-listp (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-n->m
                                   q seen states m cycle n vars path)))))
)

(local
(in-theory (enable find-matching-cycle-for-cycle-m->n
                   find-matching-prefix-for-cycle-m->n))
)

(local
(defthm last-consp-implies-first-<=len
  (implies (and (consp (last-n i x))
                (integerp i))
           (<= i (len x)))
  :rule-classes :linear)
)

(local
(defthm find-matching-prefix-is-a-compatible-path
  (implies (and (compatible-path-p cycle m)
                (bisimilar (first cycle) m q n vars)
                (consp cycle)
                (memberp q (states n))
                (next-statep (last-val cycle) (car cycle) m))
           (compatible-path-p (find-matching-prefix-for-cycle-m->n cycle m q n
                                                                   vars)
                              n))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(eliminate-destructors generalize)
           :in-theory (disable compatible-path-first-n-reduction
                               find-matching-cycle-for-cycle-is-consp)
           :use ((:instance compatible-path-first-n-reduction
                            (i (find-prefix-index  cycle
                                                   (del-last (mv-nth 0
                                                                     (find-matching-prefix-and-cycle-for-cycle-m->n
                                                                      cycle m (list q) q (states n) n
                                                                      vars
                                                                      nil)))

                                                   (mv-nth 1
                                                           (find-matching-prefix-and-cycle-for-cycle-m->n
                                                            cycle m (list q) q (states n) n
                                                            vars nil))
                                                    (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-m->n
                                                               cycle m (list q) q (states n) n
                                                               vars nil))))
                            (m n)
                            (p (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-m->n
                                          cycle m (list q) q (states n) n
                                          vars nil))))
                 (:instance find-matching-cycle-for-cycle-is-consp)))))
)

(local
(defthm find-matching-cycle-is-a-compatible-path
  (implies (and (compatible-path-p cycle m)
                (bisimilar (first cycle) m q n vars)
                (consp cycle)
                (memberp q (states n))
                (next-statep (last-val cycle) (car cycle) m))
           (compatible-path-p (find-matching-cycle-for-cycle-m->n cycle m q n
                                                                   vars)
                              n))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(eliminate-destructors generalize)
           :in-theory (disable compatible-path-first-n-reduction
                               find-matching-cycle-for-cycle-is-consp)
           :use ((:instance compatible-path-last-n-reduction
                            (i (find-prefix-index  cycle
                                                   (del-last (mv-nth 0
                                                                     (find-matching-prefix-and-cycle-for-cycle-m->n
                                                                      cycle m (list q) q (states n) n
                                                                      vars
                                                                      nil)))

                                                   (mv-nth 1
                                                           (find-matching-prefix-and-cycle-for-cycle-m->n
                                                            cycle m (list q) q (states n) n
                                                            vars nil))
                                                    (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-m->n
                                                               cycle m (list q) q (states n) n
                                                               vars nil))))
                            (m n)
                            (p (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-m->n
                                          cycle m (list q) q (states n) n
                                          vars nil))))
                 (:instance find-matching-cycle-for-cycle-is-consp)))))
)

(local
(in-theory (enable find-matching-prefix-for-cycle-n->m
                   find-matching-cycle-for-cycle-n->m))
)

(local
(defthm find-matching-prefix-is-a-compatible-path-2
  (implies (and (compatible-path-p cycle n)
                (bisimilar q m (first cycle) n vars)
                (consp cycle)
                (memberp q (states m))
                (next-statep (last-val cycle) (car cycle) n))
           (compatible-path-p (find-matching-prefix-for-cycle-n->m q m cycle n
                                                                   vars)
                              m))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(eliminate-destructors generalize)
           :in-theory (disable compatible-path-first-n-reduction
                               find-matching-cycle-for-cycle-is-consp-2)
           :use ((:instance compatible-path-first-n-reduction
                            (i (find-prefix-index  cycle
                                                   (del-last (mv-nth 0
                                                                     (find-matching-prefix-and-cycle-for-cycle-n->m
                                                                       (list q)
                                                                       q
                                                                       (states
                                                                        m) m
                                                                        cycle n
                                                                      vars
                                                                      nil)))

                                                   (mv-nth 1
                                                           (find-matching-prefix-and-cycle-for-cycle-n->m
                                                            (list q) q (states
                                                                        m)
                                                            m
                                                            cycle n
                                                            vars nil))
                                                    (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-n->m
                                                               (list q) q
                                                               (states m) m
                                                               cycle n
                                                               vars nil))))
                            (p (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-n->m
                                          (list q) q (states m) m
                                          cycle n
                                          vars nil))))
                 (:instance find-matching-cycle-for-cycle-is-consp-2)))))
)


(local
(defthm find-matching-cycle-is-a-compatible-path-2
  (implies (and (compatible-path-p cycle n)
                (bisimilar q m (first cycle) n vars)
                (consp cycle)
                (memberp q (states m))
                (next-statep (last-val cycle) (car cycle) n))
           (compatible-path-p (find-matching-cycle-for-cycle-n->m q m cycle n
                                                                   vars)
                              m))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(eliminate-destructors generalize)
           :in-theory (disable compatible-path-last-n-reduction
                               find-matching-cycle-for-cycle-is-consp-2)
           :use ((:instance compatible-path-last-n-reduction
                            (i (find-prefix-index
                                cycle
                                (del-last (mv-nth 0
                                                  (find-matching-prefix-and-cycle-for-cycle-n->m
                                                   (list q)
                                                   q
                                                   (states
                                                    m) m
                                                    cycle n
                                                    vars
                                                    nil)))

                                (mv-nth 1
                                        (find-matching-prefix-and-cycle-for-cycle-n->m
                                         (list q) q (states
                                                     m)
                                         m
                                         cycle n
                                         vars nil))
                                (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-n->m
                                           (list q) q
                                           (states m) m
                                           cycle n
                                           vars nil))))
                            (p (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-n->m
                                          (list q) q (states m) m
                                          cycle n
                                          vars nil))))
                 (:instance find-matching-cycle-for-cycle-is-consp-2)))))
)

(local
(defthm consp-last-next-state-p-reduction
  (implies (and (compatible-path-p (append p q) m)
                (true-listp p)
                (true-listp q)
                (consp p)
                (consp q))
           (next-statep (last-val p) (first q) m))
  :rule-classes nil)
)

(local
(defthm append-of-prefix-and-cycle-is-weird-path
  (implies (and (compatible-path-p cycle m)
                (next-statep (last-val cycle) (first cycle) m)
                (bisimilar (first cycle) m q n vars)
                (consp cycle)
                (true-listp cycle)
                (memberp q (states n)))
           (equal (append (find-matching-prefix-for-cycle-m->n cycle m q n
                                                               vars)
                          (find-matching-cycle-for-cycle-m->n cycle m q n
                                                                vars))
                  (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-m->n cycle m
                                                                           (list q)
                                                                           q
                                                                           (states n) n
                                                                           vars nil))))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t
           :in-theory (disable find-matching-cycle-for-cycle-is-consp)
           :use ((:instance first-last-append-reduction
                            (n (find-prefix-index cycle
                                                  (del-last (mv-nth 0
                                                                    (find-matching-prefix-and-cycle-for-cycle-m->n
                                                                     cycle m (list q) q (states n) n
                                                                     vars
                                                                     nil)))

                                                  (mv-nth 1
                                                          (find-matching-prefix-and-cycle-for-cycle-m->n
                                                           cycle m (list q) q (states n) n
                                                           vars nil))
                                                    (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-m->n
                                                               cycle m (list q) q (states n) n
                                                               vars nil))))
                            (x  (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-m->n
                                           cycle m (list q) q (states n) n
                                           vars nil))))
                 (:instance find-matching-cycle-for-cycle-is-consp)))))
)

(local
(defthm append-of-prefix-and-cycle-is-weird-path-2
  (implies (and (compatible-path-p cycle n)
                (next-statep (last-val cycle) (first cycle) n)
                (bisimilar q m (first cycle) n vars)
                (consp cycle)
                (true-listp cycle)
                (memberp q (states m)))
           (equal (append (find-matching-prefix-for-cycle-n->m q m cycle n
                                                               vars)
                          (find-matching-cycle-for-cycle-n->m q m cycle n
                                                                vars))
                  (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-n->m (list q)
                                                                           q
                                                                           (states m) m
                                                                           cycle n
                                                                           vars nil))))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t
           :in-theory (disable find-matching-cycle-for-cycle-is-consp-2)
           :use ((:instance first-last-append-reduction
                            (n (find-prefix-index cycle
                                                  (del-last (mv-nth 0
                                                                    (find-matching-prefix-and-cycle-for-cycle-n->m
                                                                     (list q) q
                                                                     (states m)
                                                                     m
                                                                     cycle n
                                                                     vars
                                                                     nil)))

                                                  (mv-nth 1
                                                          (find-matching-prefix-and-cycle-for-cycle-n->m
                                                           (list q) q (states
                                                                       m)
                                                           m
                                                           cycle n
                                                           vars nil))
                                                    (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-n->m
                                                               (list q) q
                                                               (states m) m
                                                               cycle n
                                                               vars nil))))
                            (x  (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-n->m
                                           (list q) q (states m) m
                                           cycle n
                                           vars nil))))
                 (:instance find-matching-cycle-for-cycle-is-consp-2)))))
)

(local
(in-theory (disable append-of-prefix-and-cycle-is-weird-path
                    append-of-prefix-and-cycle-is-weird-path-2))
)

(local
(defthm matching-cycle-is-true-listp
  (true-listp (find-matching-cycle-for-cycle-m->n cycle m q n vars)))
)

(local
(defthm matching-cycle-is-true-listp-2
  (true-listp (find-matching-cycle-for-cycle-n->m q m cycle n vars)))
)

(local
(defthm matching-prefix-is-true-listp
  (true-listp (find-matching-prefix-for-cycle-m->n cycle m q n vars)))
)

(local
(defthm matching-prefix-is-true-listp-2
  (true-listp (find-matching-prefix-for-cycle-n->m q m cycle n vars)))
)

(local
(defthm next-state-of-prefix-is-first-cycle
  (implies (and (compatible-path-p cycle m)
                (next-statep (last-val cycle) (first cycle) m)
                (bisimilar (first cycle) m q n vars)
                (consp cycle)
                (true-listp cycle)
                (memberp q (states n)))
           (implies (consp (find-matching-prefix-for-cycle-m->n cycle m q n
                                                                vars))
                    (next-statep (last-val (find-matching-prefix-for-cycle-m->n
                                            cycle m q n vars))
                                 (first (find-matching-cycle-for-cycle-m->n
                                         cycle m q n vars))
                                 n)))
  :otf-flg t
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t
           :in-theory (disable find-prefix-with-index
                               find-prefix-and-cycle-produces-compatible-path
                               find-matching-prefix-for-cycle-m->n
                               find-matching-cycle-for-cycle-m->n
                               find-cycle-with-index
                               find-matching-cycle-for-cycle-is-consp
                               find-matching-prefix-and-cycle-for-cycle-m->n)
           :use ((:instance append-of-prefix-and-cycle-is-weird-path)
                 (:instance find-matching-cycle-for-cycle-is-consp)
                 (:instance find-prefix-and-cycle-produces-compatible-path
                            (seen (list q))
                            (path nil))
                 (:instance consp-last-next-state-p-reduction
                            (m n)
                            (p (find-matching-prefix-for-cycle-m->n
                                cycle m q n vars))
                            (q (find-matching-cycle-for-cycle-m->n
                                cycle m q n vars)))))))
)

(local
(defthm next-state-of-prefix-is-first-cycle-2
  (implies (and (compatible-path-p cycle n)
                (next-statep (last-val cycle) (first cycle) n)
                (bisimilar q m (first cycle) n vars)
                (consp cycle)
                (true-listp cycle)
                (memberp q (states m)))
           (implies (consp (find-matching-prefix-for-cycle-n->m q m cycle n
                                                                vars))
                    (next-statep (last-val (find-matching-prefix-for-cycle-n->m
                                            q m cycle n vars))
                                 (first (find-matching-cycle-for-cycle-n->m
                                         q m cycle n vars))
                                 m)))
  :otf-flg t
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t
           :in-theory (disable find-prefix-with-index
                               find-prefix-and-cycle-produces-compatible-path-2
                               find-matching-prefix-for-cycle-n->m
                               find-matching-cycle-for-cycle-n->m
                               find-cycle-with-index
                               find-matching-cycle-for-cycle-is-consp-2
                               find-matching-prefix-and-cycle-for-cycle-n->m)
           :use ((:instance append-of-prefix-and-cycle-is-weird-path-2)
                 (:instance find-matching-cycle-for-cycle-is-consp-2)
                 (:instance find-prefix-and-cycle-produces-compatible-path-2
                            (seen (list q))
                            (path nil))
                 (:instance consp-last-next-state-p-reduction
;;                            (m n)
                            (p (find-matching-prefix-for-cycle-n->m
                                q m cycle n vars))
                            (q (find-matching-cycle-for-cycle-n->m
                                q m cycle n vars)))))))
)

;; So we have proved that matching-path is consp and that find-matching-prefix
;; is compatible. Now we need to prove that last-val of matching-path and first
;; of find-matching-prefix are next-states. Why is that? This is because
;; last-val of find-matching-prefix is bisimilar to last-val of prefix, and we
;; know that car of find-matching-prefix is the bisimilar witness.


(local
(defthm car-of-prefix-and-cycle
  (implies (and (bisimilar (first cycle) m q n vars)
                (force (<= (len seen) (len (states n))))
                (compatible-path-p path n)
                (compatible-path-p (append path
                                           (find-matching-path-for-path-m->n
                                            cycle m q n vars))
                                   n)
                (consp cycle)
                (memberp q (states n))
                (next-statep (last-val cycle) (car cycle) m)
                (compatible-path-p cycle m))
           (equal (car (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-m->n
                                  cycle m seen q (states n) n vars path)))
                  (if (consp path) (car path) q)))
  :otf-flg t
  :hints (("Goal"
           :induct (find-matching-prefix-and-cycle-for-cycle-m->n cycle m seen q (states
                                                                         n) n
                                                                         vars
                                                                         path)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t)))
)

(local
(defthm car-of-prefix-and-cycle-2
  (implies (and (bisimilar q m (first cycle) n vars)
                (force (<= (len seen) (len (states m))))
                (compatible-path-p path m)
                (compatible-path-p (append path
                                           (find-matching-path-for-path-n->m
                                            q m cycle n vars))
                                   m)
                (consp cycle)
                (memberp q (states m))
                (next-statep (last-val cycle) (car cycle) n)
                (compatible-path-p cycle n))
           (equal (car (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-n->m
                                  seen q (states m) m cycle n vars path)))
                  (if (consp path) (car path) q)))
  :otf-flg t
  :hints (("Goal"
           :induct (find-matching-prefix-and-cycle-for-cycle-n->m  seen q (states
                                                                           m)
                                                                   m
                                                                   cycle n
                                                                   vars
                                                                   path)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t)))
)

(local
(in-theory (disable find-matching-prefix-for-cycle-m->n
                    find-matching-cycle-for-cycle-m->n
                    find-matching-prefix-for-cycle-n->m
                    find-matching-cycle-for-cycle-n->m))
)

(local
(defthm matching-prefix-consp
  (implies (and (compatible-path-p cycle m)
                (next-statep (last-val cycle) (first cycle) m)
                (bisimilar (first cycle) m q n vars)
                (true-listp cycle)
                (consp cycle)
                (memberp q (states n))
                (consp (find-matching-prefix-for-cycle-m->n cycle m q n vars)))
           (equal (car (find-matching-prefix-for-cycle-m->n cycle m q n vars))
                  (car (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-m->n
                                  cycle m (list q) q (states n) n vars nil)))))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t
           :in-theory (disable car-of-prefix-and-cycle
                               car-append-reduction
                               find-prefix-with-index find-cycle-with-index)
           :use ((:instance append-of-prefix-and-cycle-is-weird-path)
                 (:instance car-append-reduction
                            (x (find-matching-prefix-for-cycle-m->n
                                cycle m q n vars))
                            (y (find-matching-cycle-for-cycle-m->n
                                cycle m q n vars)))))))

)

(local
(defthm matching-prefix-consp-2
  (implies (and (compatible-path-p cycle n)
                (next-statep (last-val cycle) (first cycle) n)
                (bisimilar q m (first cycle) n vars)
                (true-listp cycle)
                (consp cycle)
                (memberp q (states m))
                (consp (find-matching-prefix-for-cycle-n->m q m cycle n vars)))
           (equal (car (find-matching-prefix-for-cycle-n->m q m cycle n vars))
                  (car (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-n->m
                                  (list q) q (states m) m cycle n vars nil)))))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t
           :in-theory (disable car-of-prefix-and-cycle-2
                               car-append-reduction
                               find-prefix-with-index find-cycle-with-index)
           :use ((:instance append-of-prefix-and-cycle-is-weird-path-2)
                 (:instance car-append-reduction
                            (x (find-matching-prefix-for-cycle-n->m
                                q m cycle n vars))
                            (y (find-matching-cycle-for-cycle-n->m
                                q m cycle n vars)))))))

)

(local
(defthm matching-prefix-not-consp
  (implies (and (compatible-path-p cycle m)
                (next-statep (last-val cycle) (first cycle) m)
                (bisimilar (first cycle) m q n vars)
                (consp cycle)
                (true-listp cycle)
                (memberp q (states n))
                (not (consp (find-matching-prefix-for-cycle-m->n cycle m q n
                                                                 vars))))
           (equal (find-matching-cycle-for-cycle-m->n cycle m q n vars)
                  (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-m->n
                             cycle m (list q) q (states n) n vars nil))))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t
           :use append-of-prefix-and-cycle-is-weird-path)))
)

(local
(defthm matching-prefix-not-consp-2
  (implies (and (compatible-path-p cycle n)
                (next-statep (last-val cycle) (first cycle) n)
                (bisimilar q m (first cycle) n vars)
                (consp cycle)
                (true-listp cycle)
                (memberp q (states m))
                (not (consp (find-matching-prefix-for-cycle-n->m q m cycle n
                                                                 vars))))
           (equal (find-matching-cycle-for-cycle-n->m q m cycle n vars)
                  (mv-nth 2 (find-matching-prefix-and-cycle-for-cycle-n->m
                             (list q) q (states m) m cycle n vars nil))))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t
           :use append-of-prefix-and-cycle-is-weird-path-2)))
)

;; The next and final property should be that the next state of the last of the
;; cycle is the first of the cycle. Once I do that, I would go home-free with
;; the final theorems.


(local
(defthm witness-is-next-state-of-last-val
  (implies (and (consp cycle)
                (true-listp cycle)
                (subset seen (states n))
                (uniquep seen)
                (compatible-path-p cycle m)
                (memberp q (states n))
                (bisimilar (first cycle) m q n vars)
                (next-statep (last-val cycle) (first cycle) m))
           (next-statep (last-val
                         (mv-nth 2
                                 (find-matching-prefix-and-cycle-for-cycle-m->n
                                  cycle m seen q (states n) n vars path)))
                        (mv-nth 1
                                (find-matching-prefix-and-cycle-for-cycle-m->n
                                 cycle m seen q (states n) n vars path))
                        n)))
)

(local
(defthm witness-is-next-state-of-last-val-2
  (implies (and (consp cycle)
                (true-listp cycle)
                (subset seen (states m))
                (uniquep seen)
                (compatible-path-p cycle n)
                (memberp q (states m))
                (bisimilar q m (first cycle) n vars)
                (next-statep (last-val cycle) (first cycle) n))
           (next-statep (last-val
                         (mv-nth 2
                                 (find-matching-prefix-and-cycle-for-cycle-n->m
                                  seen q (states m) m cycle n vars path)))
                        (mv-nth 1
                                (find-matching-prefix-and-cycle-for-cycle-n->m
                                 seen q (states m) m cycle n vars path))
                        m)))
)

;; OK, so we have proved that the witness is the next state of the
;; last-val. Now of course, we have to know that the witness is the first thing
;; that is picked up by find-cycle.


(local
(defun seen-compatible-with-path (cycle seen path)
  (if (endp seen) (endp path)
    (and (equal (car path) (car seen))
         (seen-compatible-with-path cycle (rest seen) (last-n (len cycle) path)))))
)

(local
(defthm consp-len-consp
  (implies (and (consp cycle)
                (<= (len cycle) (len q)))
           (consp q))
  :rule-classes nil)
)

(local
(defthm consp-last-n-append-reduction
  (implies (and (consp q)
                (consp p))
           (consp (last-n (len q) (append p q)))))
)

(local
(defthm car-to-car-for-append
  (implies (and (seen-compatible-with-path cycle seen (append p q))
                (consp seen)
                (force (consp p)))
           (equal (car p) (car seen))))
)

(local
(defthm snoc-car
  (equal (car (snoc x e))
         (if (consp x) (car x) e)))
)

(local
(defthm last-n-not-consp
  (not (consp (last-n (len p) p))))
)

(local
(defthm last-append-reduction
  (implies (and (integerp i)
                (<= 0 i)
                (<= i (len p)))
           (equal (last-n i (append p q))
                  (append (last-n i p) q))))
)

(local
(defthm len-<-1=>not-consp
  (implies (< (len x) 1)
           (not (consp x))))
)

(local
(defthm snoc-append-compatible-reduction
  (implies (and (seen-compatible-with-path cycle seen path)
                (equal e (car q))
                (consp q)
                (force (equal (len path) (* (len cycle) (len seen))))
                (force (<= (len cycle) (len path)))
                (equal (len cycle) (len q)))
           (seen-compatible-with-path cycle (snoc seen e) (append path q)))
  :otf-flg t
  :hints (("Goal"
           :induct (seen-compatible-with-path cycle seen path)
           :in-theory (disable first-last-append-reduction-2)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t)))
)

(local
(defthm find-prefix-and-cycle-has-seen-compatible
  (implies (and (consp cycle)
                (memberp q seen)
                (true-listp seen)
                (equal (len path) (* (len cycle) (1- (len seen))))
                (seen-compatible-with-path cycle seen (append path
                                                              (find-matching-path-for-path-m->n
                                                               cycle m q n vars)))
                (bisimilar (first cycle) m q n vars)
                (<= (len seen) (len (states n)))
                (next-statep (last-val cycle) (first cycle) m)
                (compatible-path-p cycle m))
           (seen-compatible-with-path cycle
                                      (del-last (mv-nth 0
                                                        (find-matching-prefix-and-cycle-for-cycle-m->n
                                                         cycle m seen q (states n) n vars
                                                         path)))
                                      (mv-nth 2  (find-matching-prefix-and-cycle-for-cycle-m->n
                                                         cycle m seen q (states n) n vars
                                                         path))))
  :hints (("Goal"
           :induct (find-matching-prefix-and-cycle-for-cycle-m->n
                    cycle m seen q (states n) n vars path)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t)))
)

(local
(defthm find-prefix-and-cycle-has-seen-compatible-2
  (implies (and (consp cycle)
                (memberp q seen)
                (true-listp seen)
                (equal (len path) (* (len cycle) (1- (len seen))))
                (seen-compatible-with-path cycle seen (append path
                                                              (find-matching-path-for-path-n->m
                                                               q m cycle n vars)))
                (bisimilar q m (first cycle) n vars)
                (<= (len seen) (len (states m)))
                (next-statep (last-val cycle) (first cycle) n)
                (compatible-path-p cycle n))
           (seen-compatible-with-path cycle
                                      (del-last (mv-nth 0
                                                        (find-matching-prefix-and-cycle-for-cycle-n->m
                                                         seen q (states m) m
                                                         cycle n vars
                                                         path)))
                                      (mv-nth 2  (find-matching-prefix-and-cycle-for-cycle-n->m
                                                         seen q (states m) m
                                                         cycle n vars
                                                         path))))
  :hints (("Goal"
           :induct (find-matching-prefix-and-cycle-for-cycle-n->m
                    seen q (states m) m cycle n vars path)
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t)))
)


(local
(defthm car-is-witness
  (implies (and (consp (find-cycle cycle seen witness path))
                (seen-compatible-with-path cycle seen path))
           (equal (car (find-cycle cycle seen witness path))
                  witness)))
)

(local
(defthm last-val-of-cycle-is-last-val-of-prefix-and-cycle
  (implies (and (compatible-path-p cycle m)
                (bisimilar (first cycle) m q n vars)
                (consp cycle)
                (next-statep (last-val cycle) (first cycle) m)
                (true-listp cycle)
                (memberp q (states n)))
           (equal (last-val (find-matching-cycle-for-cycle-m->n
                             cycle m q n vars))
                  (last-val (mv-nth 2
                                    (find-matching-prefix-and-cycle-for-cycle-m->n
                                     cycle m (list q) q (states n) n vars
                                     nil)))))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t
           :in-theory (disable find-matching-prefix-and-cycle-for-cycle-m->n)
           :use ((:instance append-of-prefix-and-cycle-is-weird-path)
                 (:instance find-matching-cycle-for-cycle-is-consp)
                 (:instance last-val-append-reduction
                            (x (find-matching-prefix-for-cycle-m->n
                                cycle m q n vars))
                            (y (find-matching-cycle-for-cycle-m->n
                                cycle m q n vars)))))))
)

(local
(defthm last-val-of-cycle-is-last-val-of-prefix-and-cycle-2
  (implies (and (compatible-path-p cycle n)
                (bisimilar q m (first cycle) n vars)
                (consp cycle)
                (next-statep (last-val cycle) (first cycle) n)
                (true-listp cycle)
                (memberp q (states m)))
           (equal (last-val (find-matching-cycle-for-cycle-n->m
                             q m cycle n vars))
                  (last-val (mv-nth 2
                                    (find-matching-prefix-and-cycle-for-cycle-n->m
                                     (list q) q (states m) m cycle n vars
                                     nil)))))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t
           :in-theory (disable find-matching-prefix-and-cycle-for-cycle-n->m)
           :use ((:instance append-of-prefix-and-cycle-is-weird-path-2)
                 (:instance find-matching-cycle-for-cycle-is-consp-2)
                 (:instance last-val-append-reduction
                            (x (find-matching-prefix-for-cycle-n->m
                                q m cycle n vars))
                            (y (find-matching-cycle-for-cycle-n->m
                                q m cycle n vars)))))))
)

(local
(in-theory (disable find-prefix-with-index find-cycle-with-index))
)

(local
(defthm del-last-has-len-<=-states
  (implies (and (compatible-path-p cycle m)
                (bisimilar (first cycle) m q n vars)
                (consp cycle)
                (next-statep (last-val cycle) (first cycle) m)
                (true-listp cycle)
                (memberp q (states n)))
           (<= (len (del-last
                     (mv-nth 0 (find-matching-prefix-and-cycle-for-cycle-m->n
                                cycle m (list q) q (states n) n vars nil))))
               (len (states n))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(eliminate-destructors generalize)
           :in-theory (disable  uniquep-subset-reduction
                                del-last-seen-is-unique-p)
           :use ((:instance uniquep-subset-reduction
                            (x (del-last
                                (mv-nth 0
                                        (find-matching-prefix-and-cycle-for-cycle-m->n
                                         cycle m (list q) q (states n) n vars
                                         nil))))
                            (y (states n)))
                 (:instance del-last-seen-is-unique-p
                            (seen (list q))
                            (states (states n))
                            (path nil)))))
  :rule-classes :linear)
)

(local
(defthm next-state-of-last-of-find-cycle-is-first-of-find-cycle
  (implies (and (compatible-path-p cycle m)
                (bisimilar (first cycle) m q n vars)
                (consp cycle)
                (next-statep (last-val cycle) (first cycle) m)
                (true-listp cycle)
                (memberp q (states n)))
           (next-statep (last-val (find-matching-cycle-for-cycle-m->n
                                   cycle m q n vars))
                        (first (find-matching-cycle-for-cycle-m->n
                                cycle m q n vars))
                        n))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize)
           :in-theory (disable find-matching-cycle-for-cycle-is-consp
                               uniquep-subset-reduction
                               last-val-of-cycle-is-last-val-of-prefix-and-cycle
                               car-is-witness
                               witness-is-next-state-of-last-val)
           :do-not-induct t
           :expand (find-matching-cycle-for-cycle-m->n cycle m q n vars)
           :use ((:instance find-matching-cycle-for-cycle-is-consp)
                 (:instance witness-is-next-state-of-last-val
                            (path nil)
                            (seen (del-last
                                   (mv-nth 0
                                           (find-matching-prefix-and-cycle-for-cycle-m->n
                                            cycle m (list q) q (states n) n
                                            vars nil)))))
                 (:instance car-is-witness
                            (seen (del-last
                                   (mv-nth 0
                                           (find-matching-prefix-and-cycle-for-cycle-m->n
                                            cycle m (list q) q (states n) n
                                            vars nil))))
                            (witness (mv-nth 1
                                             (find-matching-prefix-and-cycle-for-cycle-m->n
                                              cycle m (list q) q (states n) n
                                              vars nil)))
                            (path (mv-nth 2
                                          (find-matching-prefix-and-cycle-for-cycle-m->n
                                           cycle m (list q) q (states n) n
                                           vars nil))))
                 (:instance
                  last-val-of-cycle-is-last-val-of-prefix-and-cycle)))
          ("Subgoal 2.2"
           :in-theory (disable find-prefix-and-cycle-has-seen-compatible)
           :use ((:instance  find-prefix-and-cycle-has-seen-compatible
                             (seen (list q))
                             (path nil))))
          ("Subgoal 1"
           :in-theory (enable  find-matching-cycle-for-cycle-m->n))))
)

(local
(defthm next-state-of-last-of-find-cycle-is-first-of-find-cycle-2
  (implies (and (compatible-path-p cycle n)
                (bisimilar q m (first cycle) n vars)
                (consp cycle)
                (next-statep (last-val cycle) (first cycle) n)
                (true-listp cycle)
                (memberp q (states m)))
           (next-statep (last-val (find-matching-cycle-for-cycle-n->m
                                   q m cycle n vars))
                        (first (find-matching-cycle-for-cycle-n->m
                                q m cycle n vars))
                        m))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize)
           :in-theory (disable find-matching-cycle-for-cycle-is-consp-2
                               uniquep-subset-reduction
                               last-val-of-cycle-is-last-val-of-prefix-and-cycle-2
                               car-is-witness
                               witness-is-next-state-of-last-val-2)
           :do-not-induct t
           :expand (find-matching-cycle-for-cycle-n->m q m cycle n vars)
           :use ((:instance find-matching-cycle-for-cycle-is-consp-2)
                 (:instance witness-is-next-state-of-last-val-2
                            (path nil)
                            (seen (del-last
                                   (mv-nth 0
                                           (find-matching-prefix-and-cycle-for-cycle-n->m
                                             (list q) q (states m) m
                                             cycle n
                                            vars nil)))))
                 (:instance car-is-witness
                            (seen (del-last
                                   (mv-nth 0
                                           (find-matching-prefix-and-cycle-for-cycle-n->m
                                            (list q) q (states m) m
                                            cycle n
                                            vars nil))))
                            (witness (mv-nth 1
                                             (find-matching-prefix-and-cycle-for-cycle-n->m
                                              (list q) q (states m) m
                                              cycle n
                                              vars nil)))
                            (path (mv-nth 2
                                          (find-matching-prefix-and-cycle-for-cycle-n->m
                                           (list q) q (states m) m
                                           cycle n
                                           vars nil))))
                 (:instance
                  last-val-of-cycle-is-last-val-of-prefix-and-cycle-2)))
          ("Subgoal 2.2"
           :in-theory (disable find-prefix-and-cycle-has-seen-compatible-2)
           :use ((:instance  find-prefix-and-cycle-has-seen-compatible-2
                             (seen (list q))
                             (path nil))))
          ("Subgoal 1"
           :in-theory (enable  find-matching-cycle-for-cycle-n->m))))
)

(local
(in-theory (disable witness-is-next-state-of-last-val
                    witness-is-next-state-of-last-val-2
                    consp-last-n-append-reduction
                    car-to-car-for-append
                    snoc-car
                    last-n-not-consp
                    last-n-append-reduction
                    len-<-1=>not-consp
                    snoc-append-compatible-reduction
                    find-prefix-and-cycle-has-seen-compatible
                    find-prefix-and-cycle-has-seen-compatible-2
                    car-is-witness
                    last-val-of-cycle-is-last-val-of-prefix-and-cycle
                    last-val-of-cycle-is-last-val-of-prefix-and-cycle-2))
)

(local
(defthm matching-ppath-is-compatible
  (implies (and (compatible-ppath-p p m)
                (modelp m)
                (modelp n)
                (bisimilar-equiv m n vars))
           (compatible-ppath-p (find-matching-periodic-path-m->n p m n vars)
                               n))
  :hints (("Goal"
           :in-theory (disable modelp-characterization)
           :use ((:instance modelp-characterization)
                 (:instance modelp-characterization (m n))))))

)

(local
(defthm matching-ppath-is-compatible-2
  (implies (and (compatible-ppath-p p n)
                (modelp n)
                (modelp m)
                (bisimilar-equiv m n vars))
           (compatible-ppath-p (find-matching-periodic-path-n->m m p n vars)
                               m))
  :hints (("Goal"
           :in-theory (disable modelp-characterization)
           :use ((:instance modelp-characterization)
                 (:instance modelp-characterization (m n))))))
)

(local
(in-theory (disable compatible-ppath-p find-matching-periodic-path-m->n
                    modelp-characterization restricted-formulap
                    find-matching-periodic-path-n->m))
)

(local
(defthm bisimilar-models-have-same-ltl-semantics-1
  (implies (and (bisimilar-equiv m n vars)
                (modelp m)
                (modelp n)
                (subset vars (variables m))
                (subset vars (variables n))
                (restricted-formulap f vars))
           (implies (ltl-semantics f m)
                    (ltl-semantics f n)))
  :hints (("Goal"
           :cases ((compatible-ppath-p (ltl-semantics-witness f n) n)))
          ("Subgoal 1"
           :in-theory (disable ltl-semantics-necc ltl-semantics-necc-expanded
                               ltl-ppath-semantics-cannot-distinguish-between-equal-labels
                               matching-ppath-is-compatible-2
                               ppath-and-its-matching-ppath-have-same-labels-2)
           :use ((:instance ppath-and-its-matching-ppath-have-same-labels-2
                            (ppath (ltl-semantics-witness f n)))
                 (:instance ltl-semantics-necc-expanded
                            (ppath (find-matching-periodic-path-n->m
                                     m (ltl-semantics-witness f n) n vars)))
                 (:instance matching-ppath-is-compatible-2
                            (p (ltl-semantics-witness f n)))
                 (:instance
                  ltl-ppath-semantics-cannot-distinguish-between-equal-labels
                  (p (find-matching-periodic-path-n->m
                      m (ltl-semantics-witness f n) n vars))
                  (q (ltl-semantics-witness f n)))))))
)

(local
(defthm bisimilar-models-have-same-ltl-semantics-2
  (implies (and (bisimilar-equiv m n vars)
                (modelp m)
                (modelp n)
                (subset vars (variables m))
                (subset vars (variables n))
                (restricted-formulap f vars))
           (implies (ltl-semantics f n)
                    (ltl-semantics f m)))
  :hints (("Goal"
           :cases ((compatible-ppath-p (ltl-semantics-witness f m) m)))
          ("Subgoal 1"
           :in-theory (disable ltl-semantics-necc ltl-semantics-necc-expanded
                               ltl-ppath-semantics-cannot-distinguish-between-equal-labels
                               matching-ppath-is-compatible
                               ppath-and-its-matching-ppath-have-same-labels)
           :use ((:instance ppath-and-its-matching-ppath-have-same-labels
                            (ppath (ltl-semantics-witness f m)))
                 (:instance ltl-semantics-necc-expanded
                            (m n)
                            (ppath (find-matching-periodic-path-m->n
                                     (ltl-semantics-witness f m) m n vars)))
                 (:instance matching-ppath-is-compatible
                            (p (ltl-semantics-witness f m)))
                 (:instance
                  ltl-ppath-semantics-cannot-distinguish-between-equal-labels
                  (q (find-matching-periodic-path-m->n
                      (ltl-semantics-witness f m) m n vars))
                  (p (ltl-semantics-witness f m)))))))
)

(local
(in-theory (disable ltl-semantics ltl-semantics-necc ltl-semantics-necc-expanded))
)

(DEFTHM bisimilar-models-have-same-ltl-semantics
  (implies (and (bisimilar-equiv m n vars)
                (restricted-formulap f vars)
                (subset vars (variables m))
                (subset vars (variables n))
                (modelp m)
                (modelp n))
           (equal (ltl-semantics f m)
                  (ltl-semantics f n)))
  :hints (("Goal"
           :use ((:instance bisimilar-models-have-same-ltl-semantics-1)
                 (:instance bisimilar-models-have-same-ltl-semantics-2))))
  :rule-classes nil)





