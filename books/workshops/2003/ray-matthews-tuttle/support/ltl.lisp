(in-package "ACL2")

;; The following two lines are added for portability to v2-7....


#|

  ltl.lisp
  ~~~~~~~~

In this book, we discuss the syntax of LTL formula and its semantics with
respect to a Kripke Structure. The standard semantics of LTL involve operations
with respect to an inifinitary object, namely the path. However, ACL2 does not
allow such objects. Thus, we need to define the semantics of LTL with respect
to a Kripke Structure directly. However, this requires a tableau construction
which is easy to get wrong and harder to prove theorems about, even if
specified correctly.

We have chosen to take a middle ground based on (John Matthews's)
discussions with Ernie Cohen. The idea is to define the semantics of LTL with
respect to eventually periodic paths. (We defer the proof now that any
verification of semantics over eventually periodic paths corresponds to a
verification over infinite paths and this might not be possible to do in
ACL2.) However, for the moment the semantics are with respect to eventually
periodic paths and the semantics for a Kripke Structure are given by
quantifying over all compatible paths.

The current book is produced to prove compositional reductions for
model-checking. The goal is to verify that the composition reductions are
correct given that the underlying model-checking routines are correct. Given
this assumption, we take further liberties and encapsulate the ltl semantics
over periodic paths as an underlying model-checking routine, exporting theorems
that are required to verify the reductions. The point in the case is that if
for a real LTL semantics function these constraints are not satisfied for
periodic paths, then the functions (and not the theorems) need to be changed,
making encapsulate a viable option in order to not get bogged down in
implementation of a model-checking routine for ltl.

Questions and comments are welcome. -- Sandip.

|#

(set-match-free-default :once)

(include-book "sets")




;; We now define the syntax of an LTL formula. For purpose of reductions, we
;; also define a restricted formula over a subset of variables.

(defun ltl-constantp (f)
  (or (equal f 'true)
      (equal f 'false)))

(defun ltl-variablep (f)
  (and (symbolp f)
       (not (memberp f '(+ & U W X F G)))))

;; So an LTL formula is either (i) a constant 'True or 'False, (ii) a variable
;; which is a quote or a symbol other than the LTL operator symbol, or of the
;; form (P + Q), (P & Q), (P U Q), (P W Q), (~ P), (F P), (G P), (X P), where P
;; and Q are LTL formulas.


(defun ltl-formulap (f)
  (cond ((atom f) (or (ltl-constantp f)
                      (ltl-variablep f)))
        ((equal (len f) 3)
         (and (memberp (second f) '(+ & U W))
              (ltl-formulap (first f))
              (ltl-formulap (third f))))
        ((equal (len f) 2)
         (and (memberp (first f) '(~ X F G))
              (ltl-formulap (second f))))
        (t nil)))

;; A formula is called resctricted with respect to a collection vars of
;; variables if it mentions no variable other than those in vars. Here is the
;; recursive definition.

(defun restricted-formulap (f v-list)
  (cond ((atom f) (or (ltl-constantp f)
                      (and (ltl-variablep f)
                           (memberp f v-list))))
        ((equal (len f) 3) (and (memberp (second f) '(& + U W))
                                (restricted-formulap (first f) v-list)
                                (restricted-formulap (third f) v-list)))
        ((equal (len f) 2) (and (memberp (first f) '(~ X F G))
                                (restricted-formulap (second f) v-list)))
        (t nil)))

;; Now we show the obvious thing that a restricted formula is also an ltl
;; formula.

(defthm restricted-formula-is-an-ltl-formula
  (implies (restricted-formulap f v-list)
           (ltl-formulap f))
  :rule-classes :forward-chaining)

;; Given an LTL formula, can we create a v-list such that the LTL-formula is a
;; restricted formula over the variables in v-list? The function
;; create-restricted-var-set attempts that.

(defun create-restricted-var-set (f)
  (cond ((atom f) (if (ltl-constantp f) nil (list f)))
        ((equal (len f) 3) (set-union (create-restricted-var-set (first f))
                                      (create-restricted-var-set (third f))))
        ((equal (len f) 2) (create-restricted-var-set (second f)))
        (t nil)))

;; And show that we have been successful

(local
(defthm restricted-formulap-append-reduction
  (implies (restricted-formulap f vars)
           (restricted-formulap f (set-union vars vars-prime)))
  :hints (("Goal"
           :in-theory (enable set-union))))
)

(local
(defthm restricted-formulap-append-reduction-2
  (implies (restricted-formulap f vars)
           (restricted-formulap f (set-union vars-prime vars)))
  :hints (("Goal"
           :in-theory (enable set-union))))
)

(defthm ltl-formula-is-a-restricted-formula
  (implies (ltl-formulap f)
           (restricted-formulap f (create-restricted-var-set f)))
  :rule-classes :forward-chaining)

;; OK, so we are done with syntax of LTL for mow. We will revisit this section
;; and add different restricted models when we do proofs of different
;; reductions.

;; We turn our attention to models.

;; First this handy collection of functions that might help us.
;; NOTE TO MYSELF: I should write some utilities in ACL2 that will allow me to
;; load the accessor and updater macros easily. I will have to think about it
;; at aome point.

;; Here are the accessors and updaters as macros. A Kripke structure is a
;; record of states, initial-states, transition and label-fn.

(defmacro initial-states (m) `(<- ,m :initial-states))
(defmacro transition     (m) `(<- ,m :transition))
(defmacro label-fn       (m) `(<- ,m :label-fn))
(defmacro states         (m) `(<- ,m :states))
(defmacro variables      (m) `(<- ,m :variables))

;; A periodic path is a record of initial-state, (finite) prefix, and (finite)
;; cycle.

;; NOTE TO MYSELF: The initial state might not be required. It is difficult to
;; estimate what is considered standard for Kripke structures. I have heard
;; Professor Emerson talk about Kripke Structures with initial states and
;; Kripke Structures without initial states (and so in Dr. Clarke's Book). I
;; follow the "with initial states" in that jargon, though I do believe that we
;; can modify the theorems for Kripke Structures "without initial states". The
;; reason for this choice is that I think the stronger requirements of "without
;; initial states" should not bother us at this time.

(defmacro initial-state  (p) `(<- ,p :initial-state))
(defmacro cycle          (p) `(<- ,p :cycle))
(defmacro prefix         (p) `(<- ,p :prefix))

(defmacro >_ (&rest upds) `(update nil ,@upds))

(defun next-statep (p q m)
  (memberp q (<- (transition m) p)))

(defun initial-statep (p m)
  (memberp p (initial-states m)))

(defun label-of (s m)
  (<- (label-fn m) s))

(in-theory (disable next-statep initial-statep label-of))

;; The predicate modelp here precisely describes what we expect a Kripke
;; Structure to look like.

(defun next-states-in-states (m states)
  (if (endp states) T
    (and (subset (<- (transition m) (first states))
                 (states m))
         (next-states-in-states m (rest states)))))

(defthm next-states-in-states-clarified-aux
  (implies (and (memberp p states)
                (next-states-in-states m states)
                (next-statep p q m))
           (memberp q (states m)))
  :hints (("Goal"
           :in-theory (enable next-statep))))

(defthm next-states-in-states-clarified
  (implies (and (next-states-in-states m (states m))
                (memberp p (states m))
                (next-statep p q m))
           (memberp q (states m))))

(in-theory (disable next-states-in-states-clarified-aux
                    next-states-in-states))

(encapsulate
 (((modelp *) => *))

 (local
  (defun modelp (m)
    (and (subset (initial-states m) (states m))
         (consp (states m))
         (next-states-in-states m (states m)))))

 (defthm modelp-characterization
   (implies (modelp m)
            (and (subset (initial-states m) (states m))
                 (consp (states m))
                 (next-states-in-states m (states m)))))
)


;; We define a periodic path to be compatible with a model if (a) its initial
;; state is in the initial states of the model, (b) its prefix is a compatible
;; path wrt the model, and (c) its cycle is a compatible cycle with respect to
;; the prefix.

(defun last-val (x)
  (cond ((endp x) nil)
        ((endp (rest x)) (first x))
        (t (last-val (rest x)))))

(defun compatible-path-p (path model)
  (cond ((endp path) (null path))
        ((endp (rest path)) (and (memberp (first path) (states model))
                                 (null (rest path))))
        (t (and (next-statep (first path) (second path) model)
                (memberp (first path) (states model))
                (compatible-path-p (rest path) model)))))

(defthm compatible-path-is-true-listp
  (implies (compatible-path-p path model)
           (true-listp path)))

(defthm compatible-paths-have-only-states
  (implies (and (compatible-path-p path m)
                (memberp s path))
           (memberp s (states m))))

(defun compatible-ppath-p (ppath model)
  (let ((init (initial-state ppath))
        (prefix (prefix ppath))
        (cycle (cycle ppath)))
    (and (memberp init (initial-states model))
         (consp prefix)
         (next-statep init (first prefix) model)
         (consp cycle)
         (next-statep (last-val prefix) (first cycle) model)
         (compatible-path-p prefix model)
         (compatible-path-p cycle model)
         (next-statep (last-val cycle) (first cycle) model))))

(defun labels-equal-along-paths (p m q n vars)
  (if (endp p) T
    (and (set-equal (set-intersect (label-of (first p) m) vars)
                    (set-intersect (label-of (first q) n) vars))
         (labels-equal-along-paths (rest p) m (rest q) n vars))))

(defun state-at-aux (n cycle)
  (declare (xargs :measure (nfix n)))
  (cond ((endp cycle) nil) ;; for termination
        ((< (nfix n) (len cycle)) (nth n cycle))
        (t (state-at-aux (- n (len cycle)) cycle))))

(defun state-at (n ppath)
  (let ((init (initial-state ppath))
        (prefix (prefix ppath))
        (cycle (cycle ppath)))
  (cond ((zp n) init)
        ((< (1- n) (len prefix)) (nth (1- n) prefix))
        (t (state-at-aux (- n (1+ (len prefix))) cycle)))))


;; Now we are ready to define ltl semantics. We will define LTL semantics as an
;; encapsulated function with the properties we need exported out.


(defun labels-equal-for-paths (p m q n vars)
  (if (endp p) (endp q)
    (and (equal (set-intersect (label-of (first p) m) vars)
                (set-intersect (label-of (first q) n) vars))
         (labels-equal-for-paths (rest p) m (rest q) n vars))))


(defun first-n (n lst)
  (if (zp n) nil
    (cons (first lst) (first-n (1- n) (rest lst)))))

(defun last-n (n lst)
  (if (zp n) lst
    (last-n (1- n) (rest lst))))

(defthm first-last-append-reduction
  (implies (<= n (len x))
           (equal (append (first-n n x)
                          (last-n n x))
                  x)))

(defthm len-of-last-n-is-len-minus-n
  (implies (and (not (zp n))
                (<= n (len x)))
           (equal (len (last-n n x)) (- (len x) n))))

(defthm append-of-nil-is-x
  (implies (true-listp x)
           (equal (append x nil) x)))


(local
(include-book "../../../../arithmetic-2/meta/top")
)

(defthm first-n-append-reduction
  (implies (and (equal i (len y))
                (true-listp y))
           (equal (first-n i (append y z))
                  y)))


(defthm last-n-append-reduction
  (implies (equal i (len x))
           (equal (last-n i (append x y))
                  y)))

(defun equal-label-segments-p (p m q n vars)
  (if (endp p) (endp q)
    (and (consp q)
         (set-equal (set-intersect (label-of (first p) m) vars)
                    (set-intersect (label-of (first q) n) vars))
         (equal-label-segments-p (rest p) m (rest q) n vars))))

(defthm len-of-last-n-expanded
  (implies (and (integerp i)
                (< 0 i)
                (<= i (len x)))
           (< (len (last-n i x))
              (len x)))
  :rule-classes :linear)

(defthm consp-to-len-expanded
  (implies (consp x)
           (< 0 (len x)))
  :rule-classes :linear)

(defun equal-label-segments-sequence-p-small-p (p m q n vars)
  (declare (xargs :measure (len q)))
  (if (endp q) T
    (if (or (endp p) (< (len q) (len p))) nil
      (and (equal-label-segments-p p m (first-n (len p) q) n vars)
           (equal-label-segments-sequence-p-small-p
            p m
            (last-n (len p) q) n vars)))))

(defun equal-label-segments-sequence-p-large-p (p m q n vars)
  (declare (xargs :measure (len p)))
  (if (endp p) T
    (if (or (endp q) (< (len p) (len q))) nil
      (and (equal-label-segments-p (first-n (len q) p) m q n vars)
           (equal-label-segments-sequence-p-large-p
            (last-n (len q) p) m q  n vars)))))

(defun equal-labels-periodic-path-p (p m q n vars)
  (and (set-equal (set-intersect (label-of (initial-state p) m) vars)
                  (set-intersect (label-of (initial-state q) n) vars))
       (or (and (equal-label-segments-p (prefix p) m
                                        (first-n (len (prefix p)) (prefix q))
                                        n vars)
                (equal-label-segments-sequence-p-small-p
                 (cycle p) m
                 (last-n (len (prefix p)) (prefix q))
                 n vars)
                (equal-label-segments-sequence-p-small-p
                 (cycle p) m (cycle q)
                 n vars))
            (and (equal-label-segments-p
                  (first-n (len (prefix q)) (prefix p))
                  m (prefix q) n vars)
                (equal-label-segments-sequence-p-large-p
                 (last-n
                  (len (prefix q))
                  (prefix p)) m
                  (cycle q) n vars)
                (equal-label-segments-sequence-p-large-p
                 (cycle p) m (cycle q) n vars)))))


;; Now we define the semantics of ltl. The semantics function is the
;; concrete-ltl-semantics provided below. And I need not emphasize that the
;; function is a mess.

;; We have decided to snip out part of this book from here. I have actually
;; proved that concrete-ltl-semantics satisfies the theorem
;; ltl-ppath-semantics-cannot-distinguish-between-equal-labels. Actually we
;; proved a more general version of the theorem, and equal-labels-periodic-path-p
;; is too restrictive. However, as we will see in the sequel, that is all that we
;; would need. The proof simply is to induct with the structure of the formula
;; f. However, it turned out that the proof in this case became extremely
;; cluttered, mainly because to prove a theorem about mutually recursive
;; function, we need to prove a theorem about all the functions in the
;; clique. (The corresponding statements for the different other functions are not
;; very elegant in our case.) To see how bad theorems can become look at the
;; file bisimilarity.lisp. Further, we note that we will never actually
;; execute the function ltl-ppath-semantics. (Indeed the function we would have
;; hoped to execute would be the model checking function ltl-semantics, but
;; that is defined using defun-sk and hence we have lost all hopes of executing
;; it. The reason for our going to such lengths to define
;; concrete-ltl-semantics is to justify that we can indeed do what we want with
;; eventually periodic paths. Henceforth, however, we will simply use the
;; following encapsulated function ltl-ppath-semantcs, where we assume the
;; version of ltl-ppath-semantics-cannot-distinguish-between-equal-labels, that
;; we export from the encapsulate. If a reader of the script feels unsatisfied,
;; we can provide the actual theorems about concrete-ltl-semantics.


(encapsulate
 (((ltl-ppath-semantics * * *) => *))

 (local
  (defun ltl-ppath-semantics (f ppath m)
    (declare (ignore f ppath m))
    T)
  )

 (defthm ltl-ppath-semantics-returns-boolean
   (or (equal (ltl-ppath-semantics f ppath m) T)
       (equal (ltl-ppath-semantics f ppath m) nil))
   :rule-classes :type-prescription)

  (defthm ltl-ppath-semantics-cannot-distinguish-between-equal-labels
   (implies (and (equal-labels-periodic-path-p p m q n vars)
                 (subset vars (variables m))
                 (subset vars (variables n))
                 (compatible-ppath-p p m)
                 (compatible-ppath-p q n)
                 (restricted-formulap f vars))
            (equal (ltl-ppath-semantics f p m)
                   (ltl-ppath-semantics f q n))))

 (defthm ltl-ppath-semantics-can-be-decomposed-over-conjunctions
   (implies (and (ltl-formulap f)
                 (equal (len f) 3)
                 (equal (second f) '&)
                 (compatible-ppath-p p m))
            (equal (ltl-ppath-semantics f p m)
                   (and (ltl-ppath-semantics (first f) p m)
                        (ltl-ppath-semantics (third f) p m)))))


)

(defun-sk ltl-semantics (f m)
  (forall ppath
          (implies (compatible-ppath-p ppath m)
                   (ltl-ppath-semantics f ppath m))))

(defthm ltl-semantics-necc-expanded
  (implies (and (ltl-semantics f m)
                (compatible-ppath-p ppath m))
           (ltl-ppath-semantics f ppath m))
  :hints (("Goal"
           :use ltl-semantics-necc)))

(in-theory (disable ltl-semantics-necc))

