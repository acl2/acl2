(in-package "ACL2")
(include-book "hons-help2")

; Courtesy of Bob Boyer and Warren Hunt:

(defun fib (x)
  (declare (xargs :guard (and (integerp x)
                              (<= 0 x))))
  (mbe
   :logic
   (cond ((zp x) 0)
         ((= x 1) 1)
         (t (+ (fib (- x 1)) (fib (- x 2)))))
   :exec
   (if (< x 2)
       x
     (+ (fib (- x 1)) (fib (- x 2))))))

(comp t) ; for other than CCL and SBCL

#+hons
(memoize 'fib)

#+hons
(defthm fib-test0

; SBCL 1.03 has given the following error for fib-test, below, when not
; including fib-test0 first:

; Error:  Control stack exhausted (no more space for function call frames).

; Since fib is not tail-recursive, the problem presumably is that even with
; memoization, we need a control stack of size about 10000 for fib-test.  By
; putting fib-test0 first, we presumably stay within SBCL's stack size limit.

  (equal (integer-length (fib 5000)) 3471))

#+hons
(defthm fib-test
  (equal (integer-length (fib 10000)) 6942))

(defn tree-depth (x)

  ; This is the same as max-depth, but we want to
  ; hack with it so we give it another name.

  (if (atom x)
      0
    (1+ (max (tree-depth (car x))
             (tree-depth (cdr x))))))

(defun build-tree (n)
  (declare (xargs :guard t))
  (if (posp n)
      (hons (build-tree (1- n)) (build-tree (1- n)))
    nil))

#+hons
(memoize 'build-tree)

#+hons
(memoize 'tree-depth)

#+hons
(defthm build-tree-test
  (let ((n 1000))
    (equal (tree-depth (build-tree n)) n)))

(defn make-list-of-numbers (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (list n)
    (hons n (make-list-of-numbers (1- n)))))

(comp 'make-list-of-numbers)

(defun lots (n)
  (declare (xargs :guard (posp n)))
  (let* ((lots-of-numbers (make-list-of-numbers n)))
    (equal (+ (len (hons-intersection lots-of-numbers
                                      lots-of-numbers))
              (len (hons-union        lots-of-numbers
                                      lots-of-numbers))
              (len (hons-set-diff     lots-of-numbers
                                      lots-of-numbers)))
           (+ 2 (* 2 n)))))

(defthm lots-thm (lots 6000))


;; Previous stuff from qi.lisp ---------------------------



; ubdd operations.  ubdd-based set operations.  Reachability.

; ubdd stands for 'unlabeled bdd', and means a cons-tree in T and NIL
; without any subtree that is '(t . t) or '(nil . nil).

; By 'cons-tree in T and NIL' we mean the intersection of all sets S
; such that:
;
;    1.  T is a member of S,
;    2.  NIL is a member of S, and
;    3.  for all x and y, if x and y are in S, then (CONS x y) is in S.

; Legend:
;  A function whose name begins "q-"  returns an ubdd.
;  A function whose name beqins "qv-" returns a list of ubdds.
;  A function whose name begins "qs-" is a set operation on ubdds.

; If, especially in the name of a function, we write 'bdd', we mean
; 'ubdd'.

; This paragraph sucks because it refers to variables, which are
; nowhere in sight.  This file defines a number of ubdd-related
; operations.  ubdds generally have three characteristics: each path
; from the root to a tip encounters each variable at most once, every
; path encounters variables in pre-specified order, and no pair of
; outgoing edges point to the same node (reduced).  Our ubdd
; definition does not reduce internal nodes unless both outgoing edges
; of a ubdd node point to the same constant.  As a result, we do not
; need to store the variable name in the ubdd nodes.  We do reduce our
; ubdds in the sense that constant values terminate any path.

(defabbrev qcar (x) (if (consp x) (car x) x))

(defabbrev qcdr (x) (if (consp x) (cdr x) x))

(defabbrev qcons (x y)
  (if (if (eq x t)
          (eq y t)
        (and (eq x nil) (eq y nil)))
      x
    (hons x y)))

; The three abbreviations above along with the two functions below
; provide the complete definition of our ubdd system.  The order of
; the ubdd variables is implicit -- there are no names, just the depth
; from the root.  Thus, an ubdd with only one variable can be either
; the reduced values T or NIL, or it can be, (HONS T NIL), or (HONS
; NIL T); (HONS T T) and (HONS NIL NIL) are not permitted, but reduced
; to T and NIL, respectively (see the definition of NORMP below).

(defn q-not (x)
  (if (atom x)
      (if x nil t)
    (hons (q-not (car x))
          (q-not (cdr x)))))

(defn q-ite (x y z)

;;; This legacy doc string was replaced Nov. 2014 by the corresponding
;;; auto-generated defxdoc form in the last part of this file.

; ":Doc-section Hons-and-Memoization

; if-then-else for ubdds.~/

; (Q-ITE x y z) expects three ubdds, which are to be interpreted at
; the same level.  Informally speaking. Q-ITE returns a single ubdd,
; also at the same level, that is 'equivalent' to (IF x y z).  The two
; theorems Q-ITE-CORRECT and NORMP-Q-ITE express formally what Q-ITE
; returns.~/~/"

  (cond
   ((null x) z)
   ((atom x) y)
   (t (let ((y (if (hqual x y) t y))
            (z (if (hqual x z) nil z)))
        (cond ((hqual y z) y)
              ((and (eq y t) (eq z nil)) x)
              ((and (eq y nil) (eq z t)) (q-not x))
              ;; ((eq z nil) (q-and x y))
              ;; ((eq z t)   (q-implies x y))
              ;; ((eq y t)   (q-or x y))
              ;; ((eq y nil) (q-and-c1 x y))
              (t (qcons (q-ite (car x) (qcar y) (qcar z))
                        (q-ite (cdr x) (qcdr y) (qcdr z)))))))))

; For these definitions to serve as an effective ubdd system, we
; memoize the functions Q-NOT and Q-ITE.


(defn normp (x)

;;; This legacy doc string was replaced Nov. 2014 by the corresponding
;;; auto-generated defxdoc form in the last part of this file.

;":Doc-section Hons-and-Memoization

; Recognizer of ubdds.~/
; (NORMP x) returns T or NIL according to whether X is a well-formed
; ubdd, i.e., a rooted, binary tree, in T and NIL, with no node equal
; to '(T . T) or '(NIL . NIL).~/~/"

  (mbe :logic
       (if (atom x)
           (booleanp x)
         (and (normp (car x))
              (normp (cdr x))
              (if (atom (car x))
                  (not (equal (car x) (cdr x)))
                t)))

       :exec
       (cond ((eq x t) t)
             ((eq x nil) t)
             ((atom x) nil)
             (t (let ((a (car x))
                      (d (cdr x)))
                  (cond ((eq a t)
                         (cond ((eq d nil) t)
                               ((eq d t) nil)
                               (t (normp d))))
                        ((eq a nil)
                         (cond ((eq d nil) nil)
                               ((eq d t) t)
                               (t (normp d))))
                        (t (and (normp a) (normp d)))))))))

(defn normp-list (x)
  (if (atom x) t (and (normp (car x)) (normp-list (cdr x)))))

(defn eval-bdd (x values)

  "(EVAL-bdd x values) is the 'value' of X with respect to VALUES.

   X is normally a CONS tree of Booleans and VALUES is normally a
   TRUE-LISTP of Booleans, i.e., Ts and NILs.  (Typically, X is T,
   NIL, or a 'HONSP' NORMP.)  Of course, since EVAL-BDD's guard is T,
   it can be given any two ACL2 objects as arguments.

   If X is an atom, then X is its own 'value'; otherwise, we use the
   CAR and CDR of VALUES, say A and D, to guide us further through X.
   (If VALUES is an atom, we use NIL for both A and D.)  If A is NIL
   the answer is the value of (CDR X) with respect to D; otherwise the
   answer is the value of (CAR X) with respect to D.

   One can think of the VALUES argument to EVAL-BDD as having its last
   atom replaced with an infinite list of NILs."

  (if (atom x)
      x
    (if (atom values)
        (eval-bdd (cdr x) nil)
      (if (car values)
          (eval-bdd (car x) (cdr values))
        (eval-bdd (cdr x) (cdr values))))))

(defthm normp-implies-eval-bdd-blp
  (implies (normp x)
           (booleanp (eval-bdd x vals))))

(defn eval-bdd-list (bdds values)
  (if (atom bdds)
      nil
    (hons (eval-bdd (car bdds) values)
          (eval-bdd-list (cdr bdds) values))))

; Assuming variable names are ordered by their location in a list,
; LOCN returns the location of a variable in a list.  (QVAR-N i)
; creates the ith ubdd variable.  Variable names are a mere
; convenience.  We have tried not to impose any unnecessary
; restriction on variables names; however, since we usually only use
; symbols and natural numbers for variable names we have sometimes
; used the EQLABLEP guard on variables.

(defn locn-acc (v vs acc)
  (declare (xargs :guard (integerp acc)))
  (cond ((atom vs) acc)
        ((equal v (car vs)) acc)
        (t (locn-acc v (cdr vs) (1+ acc)))))

(defn locn (v vs)
  (declare (xargs :guard t
                  :verify-guards nil))
  (mbe
   :logic
   (cond ((atom vs) 0)
         ((equal v (car vs)) 0)
         (t (1+ (locn v (cdr vs)))))
   :exec
   (locn-acc v vs 0)))

(defthm locn-is-locn-acc
  (implies (natp acc)
           (equal (locn-acc v vars acc)
                  (+ acc (locn v vars)))))

(verify-guards locn)

(defn qvar-n (n)
  (declare (xargs :guard (natp n)))
  (mbe
   :logic
   (cond ((not (natp n)) nil)
         ((= n 0) (hons t nil))
         (t (let ((x (qvar-n (1- n))))
              (hons x x))))
   :exec
   (cond ((int= n 0) (hons t nil))
         (t (let ((x (qvar-n (1- n))))
              (hons x x))))))

(defthm consp-qvar-n
  (implies (and (integerp n)
                (<= 0 n))
           (consp (qvar-n n))))

(defthm normp-qvar-n
  (normp (qvar-n n)))

(in-theory (disable qvar-n))

(defn var-to-tree (var vars) (qvar-n (locn var vars)))

(defthm normp-var-to-tree
  (normp (var-to-tree var vars)))

(in-theory (disable var-to-tree))

(defn var-to-tree-list (variables vars)
  (if (atom variables) nil
    (hons (var-to-tree (car variables) vars)
          (var-to-tree-list (cdr variables) vars))))

;                      *B0* and *B1*

(defconst *b1* t

; Matt K. mod: Comment out doc string (disallowed after ACL2 8.3).
#|
  "The constant *B1*, which has value T, plays at least four roles:

     (a) *B1* represents 'true'.

     (b) *B1* represents 'bit 1' in bit vectors.

     (c) *B1* represents 'negative' as an arithmetic sign in a general
         integer.

     (d) *B1* refers to the the CAR side of a CONSP NORMP."
|#)

(defconst *b0* nil

; Matt K. mod: Comment out doc string (disallowed after ACL2 8.3).
#|
  "The constant *B0*, which always has value NIL, represents 'false',
  'bit 0', 'positive as an arithmetic sign', 'CDR side', and, of
  course, the empty list."
|#)

(defconst *list-b1* (hist *b1*))

(defconst *list-b0* (hist *b0*))

(defmacro is-b1 (x) `(eq ,x t))

(defmacro is-b0 (x) `(eq ,x nil))

(defmacro if-bbb (x y z)

  "(IF-BBB x y z) is equal to (Q-ITE x y z).  IF-BBB is a
  'short-circuit' or 'lazy' version of Q-ITE that avoids evaluating y
  if x evaluates to *B0* and avoids evaluating z if x evaluates to
  *B1*."

; A possible improvement to IF-BBB: macroexpansion of IF-BBB terms
; could result in less code.  The double appearances of y and z could
; be eliminated with an FLET of two functions.  But currently, ACL2
; does support not FLET unless all the free vars in the body are among
; the args.

  `(let ((if-bbb-x-do-not-use-elsewhere ,x))
     (cond
      ((is-b1 if-bbb-x-do-not-use-elsewhere) ,y)
      ((is-b0 if-bbb-x-do-not-use-elsewhere) ,z)
      (t (let* ((if-bbb-y-do-not-use-elsewhere ,y)
                (if-bbb-z-do-not-use-elsewhere ,z))
           (q-ite if-bbb-x-do-not-use-elsewhere
                  if-bbb-y-do-not-use-elsewhere
                  if-bbb-z-do-not-use-elsewhere))))))


(defmacro and-bb (x y) `(if-bbb ,x ,y *b0*))

(defn iff-bb (x y) (if-bbb x y (q-not y)))

(defn xor-bb (x y) (if-bbb x (q-not y) y))

(defn not-b (x) (q-not x))

(defmacro or-bb (x y) `(if-bbb ,x *b1* ,y))

(defabbrev maj-bbb (c a b) (if-bbb c (or-bb a b) (and-bb a b)))


; We define additional ubdd-operations that can sometime provide
; better efficiency than only using Q-ITE through the use of specific
; function memoization.

(defn q-not-ite (x)
  (q-ite x nil t))

(defn q-and (x y)
  (if (atom x)
      (if x y nil)
    (if (atom y)
        (if y x nil)
      (if (hqual x y)
          x
        (let ((l (q-and (car x) (car y)))
              (r (q-and (cdr x) (cdr y))))
          (qcons l r))))))

(defn q-and-ite (x y)
  (q-ite x y nil))

; It would be nice here to have:
;    (thm (equal (q-and x y) (q-and-ite x y))).

(defn q-or (x y)
  (if (atom x)
      (if x t y)
    (if (atom y)
        (if y t x)
      (if (hqual x y)
          x
        (let ((l (q-or (car x) (car y)))
              (r (q-or (cdr x) (cdr y))))
          (qcons l r))))))

(defn q-or-ite (x y)
  (q-ite x t y))

(defn q-implies (x y)
  ;; aka q-or-c1
  (if (atom x)
      (if x y t)
    (if (atom y)
        (if y t (q-not x))
      (if (hqual x y)
          t
        (let ((l (q-implies (car x) (car y)))
              (r (q-implies (cdr x) (cdr y))))
          (qcons l r))))))

(defn q-implies-ite (x y)
  ;; aka q-or-c1
  (q-ite x y t))

(defn q-or-c2 (x y)
  (if (atom y) ; y tested for to emulate q-or-c2-ite
      (if y x t)
    (if (atom x)
        (if x t (q-not y))
      (if (hqual x y)
          t
        (let ((l (q-or-c2 (car x) (car y)))
              (r (q-or-c2 (cdr x) (cdr y))))
          (qcons l r))))))

(defn q-or-c2-ite (x y)
  ;; aka y->x
  (q-ite y x t))

(defn q-and-c1 (x y)
  (if (atom x)
      (if x nil y)
    (if (atom y)
        (if y (q-not x) nil)
      (if (hqual x y)
          nil
        (let ((l (q-and-c1 (car x) (car y)))
              (r (q-and-c1 (cdr x) (cdr y))))
          (qcons l r))))))

(defn q-and-c1-ite (x y)
  (q-ite x nil y))

(defn q-and-c2 (x y)
  (if (atom x)
      (if x (q-not y) nil)
    (if (atom y)
        (if y nil x)
      (if (hqual x y)
          nil
        (let ((l (q-and-c2 (car x) (car y)))
              (r (q-and-c2 (cdr x) (cdr y))))
          (qcons l r))))))

(defn q-and-c2-ite (x y)
  (q-ite y nil x))

(defn q-iff (x y)
  (if (atom x)
      (if x y (q-not y))
    (if (atom y)
        (if y x (q-not x))
      (if (hqual x y)
          t
        (let ((l (q-iff (car x) (car y)))
              (r (q-iff (cdr x) (cdr y))))
          (qcons l r))))))

(defn q-iff-ite (x y)   ; why call q-not rather than q-ite?
  (if-bbb x y (q-not y)))

(defn q-nand (x y)
  (if (atom x)
      (if x (q-not y) t)
    (if (atom y)
        (if y (q-not x) t)
      (if (hqual x y)
          (q-not x)
        (let ((l (q-nand (car x) (car y)))
              (r (q-nand (cdr x) (cdr y))))
          (qcons l r))))))

(defn q-nand-ite (x y)
  (if-bbb x (q-not y) t))

(defn q-nor (x y)
  (if (atom x)
      (if x nil (q-not y))
    (if (atom y)
        (if y nil (q-not x))
      (if (hqual x y)
          (q-not x)
        (let ((l (q-nor (car x) (car y)))
              (r (q-nor (cdr x) (cdr y))))
          (qcons l r))))))

(defn q-nor-ite (x y)
  (if-bbb x nil (q-not y)))

(defn q-xor (x y)
  (if (atom x)
      (if x (q-not y) y)
    (if (atom y)
        (if y (q-not x) x)
      (if (hqual x y)
          nil
        (let ((l (q-xor (car x) (car y)))
              (r (q-xor (cdr x) (cdr y))))
          (qcons l r))))))

(defn q-xor-ite (x y)

; why call atom, q-not, and hqual rather than q-ite?

  (if (atom x)
      (if x (q-not y) y)
    (if (atom y)
        (if y (q-not x) x)
      (if (hqual x y)
          nil
        (if-bbb x (q-not y) y)))))

; End of the 10 q-functions of two arguments.


(defn q-buf (x)         x)

(defn q-or3   (w x y)   (q-or  w (q-or  x y)))

(defn q-and3  (w x y)   (q-and w (q-and x y)))

(defn q-or4   (w x y z) (q-or  w (q-or  x (q-or  y z))))

(defn q-and4  (w x y z) (q-and w (q-and x (q-and y z))))

(defn q-nor3  (w x y)   (q-not (q-or3  w x y)))

(defn q-nand3 (w x y)   (q-not (q-and3 w x y)))

(defn q-nor4  (w x y z) (q-not (q-or4  w x y z)))

(defn q-nand4 (w x y z) (q-not (q-and4 w x y z)))


; (defn qs-complement (x full-set) (q-and-c1 x full-set))

; Conjecture:  (qs-subset x y) is an efficient implementation of
; (eq t (q-implies x y)).

(defn qs-subset (x y)
  (cond ((atom x)
         (if x (eq y t) t))
        ((atom y) y)
        ((hqual x y) t)
        (t (and (qs-subset (car x) (car y))
                (qs-subset (cdr x) (cdr y))))))

;; Composes the Boolean function represented by ubdd X with those
;; represented by ubdds in the list L.

(defn q-compose (x l)
  (if (atom x)
      x
    (if (atom l)
        (q-compose (cdr x) nil)
      (if-bbb (car l)
              (q-compose (car x) (cdr l))
              (q-compose (cdr x) (cdr l))))))

(defn q-compose-list (xs l)
  (if (atom xs)
      nil
    (cons (q-compose (car xs) l)
          (q-compose-list (cdr xs) l))))

(defn q-restrict (x n v vars)

  ;; Needs to be memoized.  Q-RESTRICT takes an ubdd X, a value N (T
  ;; or NIL), a variable V, which is a member of the list of variables
  ;; VARS with respect to which X is an ubdd.  Q-RESTRICT returns the
  ;; ubdd corresponding to the formula that one obtains by simplifying
  ;; every internal node in X corresponding to variable V to N.  Thus,
  ;; if an ubdd with variables '(A B C) has variable B restricted to
  ;; NIL, then both outgoing edges from every internal node Y at
  ;; "level" B will point to the (CDR Y).

  ;; This like forming (LET ((V N)) X) and simplifying the resulting
  ;; expression.

  (declare (xargs :guard (and (eqlablep v)
                              (eqlable-listp vars))))
  (if (atom x)
      x
    (if (eql v (car vars))
        (if n
            (qcons (car x) (car x))
          (qcons (cdr x) (cdr x)))
      (qcons (q-restrict (car x) n v (cdr vars))
             (q-restrict (cdr x) n v (cdr vars))))))

(defn q-restrict-shrink (x n v vars)

  ;; Q-RESTRICT-SHRINK should to be memoized.  Q-RESTRICT-SHRINK takes
  ;; an ubdd X, a value N (t or nil), a variable V, which is a member
  ;; of the list of variables VARS with respect to which X is an ubdd.
  ;; q-RESTRICT-SHRINK returns the ubdd corresponding to the formula
  ;; that one obtains by substituting N for X in the formula to which
  ;; X corresponds.

  ;; Suttle point: the var V is eliminated.  Always know which VARS
  ;; list you are using!

  (declare (xargs :guard (and (eqlablep v)
                              (eqlable-listp vars))))
  (if (atom x)
      x
    (if (eql v (car vars))
        (if n (car x) (cdr x))
      (qcons (q-restrict-shrink (car x) n v (cdr vars))
             (q-restrict-shrink (cdr x) n v (cdr vars))))))

; Q-REORDER is an ubdd variable reorder function.  DELETE-HQL is
; defined to return a unique (HONSP) object.  For the memoization of
; Q-REORDER to work best, it should be called as (Q-REORDER x
; (HONS-COPY vars) (HONS-COPY nvars)) which will ensure that unique
; objects are supplied.

(defn delete-hql (x l)
  (declare (xargs :guard (eqlablep x)))
  (cond ((atom l) nil)
        ((eql x (car l))
         (cdr l))
        (t (hons (car l) (delete-hql x (cdr l))))))

(defthm symbol-listp-delete-hql
  (implies (eqlable-listp l)
           (eqlable-listp (delete-hql x l))))

(defn q-reorder (x vars nvars)

  ;; Needs to be memoized.  VARS and NVARS should be of the same
  ;; length.  X is an ubdd.  Q-REORDER returns the ubdd whose meaning
  ;; with respect to NVARS is equivalent to to the meaning of X with
  ;; respect to VARS.

  (declare (xargs :guard (and (eqlable-listp vars)
                              (eqlable-listp nvars))
                  :measure (acl2-count nvars)))
  (if (or (atom x)
          (atom nvars)) ;; could be eliminated
      x
    (if (eql (car vars) (car nvars))
        ;; It may be possible to simplify the QCONS function calls
        ;; here to HONS function calls.
        (qcons (q-reorder (car x) (cdr vars) (cdr nvars))
               (q-reorder (cdr x) (cdr vars) (cdr nvars)))
      (qcons (q-reorder (q-restrict-shrink x t (car nvars) vars)
                        (delete-hql (car nvars) vars)
                        (cdr nvars))
             (q-reorder (q-restrict-shrink x nil (car nvars) vars)
                        (delete-hql (car nvars) vars)
                        (cdr nvars))))))

(defun q-restrict-alist (x bindings vars)

  ;; See also Q-RESTRICT.

  ;; (Q-RESTRICT-ALIST x bindings vars) is somewhat similar to forming
  ;; (let bindings x) and simplifying the resulting expression.

  ;; Should this be re-written to use Q-ITE and obviate the need to
  ;; memoize this function?  Probably not.

  (declare (xargs :guard (eqlable-alistp bindings)))
  (if (atom x)
      x
    (if (atom vars)
        x
      (let ((pair (assoc (car vars) bindings)))
        (if pair
            (let ((x-below (q-restrict-alist
                            (if (cdr pair) (car x) (cdr x))
                            bindings (cdr vars))))
              (qcons x-below x-below))
          (qcons (q-restrict-alist (car x) bindings (cdr vars))
                 (q-restrict-alist (cdr x) bindings (cdr vars))))))))

(defun q-restrict-alist-list (x-lst bindings vars)
  (declare (xargs :guard (eqlable-alistp bindings)))
  (if (atom x-lst)
      nil
    (cons (q-restrict-alist (car x-lst) bindings vars)
          (q-restrict-alist-list (cdr x-lst) bindings vars))))


(defn q-reorder-down-one (x var vars)
  ;; This function "swaps" variable VAR with the variable just below
  ;; it in the variable order.
  (declare (xargs :guard (eqlablep var)))
  (if (atom x)
      x
    (if (atom vars)
        x
      (if (eql (car vars) var)
          ;; Perform the swap.
          (qcons (qcons (qcar (qcar x))
                        (qcar (qcdr x)))
                 (qcons (qcdr (qcar x))
                        (qcdr (qcdr x))))
        (hons (q-reorder-down-one (car x) var (cdr vars))
              (q-reorder-down-one (cdr x) var (cdr vars)))))))


#||

(defn find-best-position-helper (bdd var max-var)
  (loop for

(defn find-best-position (bdd var)
  (let ((max-var (max-depth bdd)))
    (if (< max-var var)
        bdd
      (find-best-position-helper bdd var max-var)

||#

(defn q-exists-shrink (x E-vars vars)

  ;; E-vars must be a subset of VARS and its variables must appear in
  ;; the same order as they do in VARS.  Q-EXISTS-SHRINK returns an
  ;; answer that has meaning with respect to the deletion of the
  ;; members of E-vars from VARS.

  (declare (xargs :guard (and (eqlable-listp E-vars)
                              (eqlable-listp vars))))
  (if (or (atom x)
          (atom E-vars))
      x
    (if (eql (car E-vars) (car vars))
        (q-or (q-exists-shrink (car x) (cdr E-vars) (cdr vars))
              (q-exists-shrink (cdr x) (cdr E-vars) (cdr vars)))
      (qcons (q-exists-shrink (car x) E-vars (cdr vars))
             (q-exists-shrink (cdr x) E-vars (cdr vars))))))

(defn q-exists (x E-vars vars)

  ;; E-vars must be a subset of VARS and its variables must appear in
  ;; the same order as they do in VARS.  Q-EXISTS returns an answer
  ;; that has meaning with respect to VARS.

  (declare (xargs :guard (and (eqlable-listp E-vars)
                              (eqlable-listp vars))))
  (if (or (atom x)
          (atom E-vars))
      x
    (if (eql (car E-vars) (car vars))
        (let ((below
               (q-or (q-exists (car x) (cdr E-vars) (cdr vars))
                     (q-exists (cdr x) (cdr E-vars) (cdr vars)))))
          (qcons below below))
      (qcons (q-exists (car x) E-vars (cdr vars))
             (q-exists (cdr x) E-vars (cdr vars))))))

(defn q-for-all-shrink (x E-vars vars)

  ;; E-vars must be a subset of VARS and its variables must appear in
  ;; the same order as they do in VARS.  Q-FOR-ALL-SHRINK returns an
  ;; answer that has meaning with respect to the deletion of the
  ;; members of E-vars from VARS.

  (declare (xargs :guard (and (eqlable-listp E-vars)
                              (eqlable-listp vars))))
  (if (or (atom x)
          (atom E-vars))
      x
    (if (eql (car E-vars) (car vars))
        (q-and (q-for-all-shrink (car x) (cdr E-vars) (cdr vars))
               (q-for-all-shrink (cdr x) (cdr E-vars) (cdr vars)))
      (qcons (q-for-all-shrink (car x) E-vars (cdr vars))
             (q-for-all-shrink (cdr x) E-vars (cdr vars))))))

(defn q-for-all (x E-vars vars)

  ;; E-vars must be a subset of VARS and its variables must appear in
  ;; the same order as they do in VARS.  Q-FOR-ALL returns an answer
  ;; that has meaning with respect to VARS.

  (declare (xargs :guard (and (eqlable-listp E-vars)
                              (eqlable-listp vars))))
  (if (or (atom x)
          (atom E-vars))
      x
    (if (eql (car E-vars) (car vars))
        (let ((below
               (q-and (q-for-all (car x) (cdr E-vars) (cdr vars))
                      (q-for-all (cdr x) (cdr E-vars) (cdr vars)))))
          (qcons below below))
      (qcons (q-for-all (car x) E-vars (cdr vars))
             (q-for-all (cdr x) E-vars (cdr vars))))))

(defn q-exists-one-var (x v vars)
  (declare (xargs :guard (and (eqlablep v)
                              (eqlable-listp vars))))
  (q-or (q-restrict x  t  v vars)
        (q-restrict x nil v vars)))

(defn q-for-all-one-var (x v vars)
  (declare (xargs :guard (and (eqlablep v)
                              (eqlable-listp vars))))
  (q-and (q-restrict x  t  v vars)
         (q-restrict x nil v vars)))

(defn q-exists-one-var-shrink (x v vars)
  (declare (xargs :guard (and (eqlablep v)
                              (eqlable-listp vars))))
  (q-or (q-restrict-shrink x  t  v vars)
        (q-restrict-shrink x nil v vars)))

(defn q-for-all-one-var-shrink (x v vars)
  (declare (xargs :guard (and (eqlablep v)
                              (eqlable-listp vars))))
  (q-and (q-restrict-shrink x  t  v vars)
         (q-restrict-shrink x nil v vars)))


; To ease the use of our ubdd system, we have defined some functions
; that let a user write expressions in a typical Lisp style.  Such
; expressions are then converted into IF-expressions, before they are
; converted into ubdds.

(defn good-to-if-p (x)
  ;; GOOD-TO-IF-P recognizes a well-formed IF-expression.
  (if (atom x)
      (eqlablep x)
    (let ((fn (car x))
          (args (cdr x)))
      (case fn
        (if (and (consp args)
                 (consp (cdr args))
                 (consp (cddr args))
                 (null (cdddr args))
                 (good-to-if-p (car args))
                 (good-to-if-p (cadr args))
                 (good-to-if-p (caddr args))))
        (otherwise nil)))))

(defn nmake-if (test true false)
  (declare (xargs :guard (and (good-to-if-p test)
                              (good-to-if-p true)
                              (good-to-if-p false))))
  (cond ((eq test t)
         true)
        ((eq test nil)
         false)
        ((and (consp test) (eq 'if (car test))
              (null (caddr test)) (eq t (cadddr test)))
         (nmake-if (cadr test) false true))
        (t (let* ((true (if (hqual test true) t true))
                  (true (if (and (consp true)
                                 (hqual test (cadr true)))
                            (caddr true)
                          true))
                  (false (if (hqual test false) nil false))
                  (false (if (and (consp false)
                                  (hqual test (cadr false)))
                             (cadddr false)
                           false)))
             (cond ((hqual true false) true)
                   ((and (eq true t) (eq false nil))
                    test)
                   (t (hist 'if test true false)))))))

(defn to-if-error-p (x)
  (and (consp x)
       (stringp (car x))))

(defthm good-to-if-nmake-if
  (implies (and (good-to-if-p x)
                (good-to-if-p y)
                (good-to-if-p z))
           (good-to-if-p (nmake-if x y z))))

(defthm eqlablep-of-nmake-if
  (implies (and (good-to-if-p x)
                (good-to-if-p y)
                (good-to-if-p z)
                (not (consp (nmake-if x y z))))
           (eqlablep (nmake-if x y z))))

(defthm consp-of-nmake-if
  (implies (and (good-to-if-p x)
                (good-to-if-p y)
                (good-to-if-p z)
                (not (eqlablep (nmake-if x y z))))
           (consp (nmake-if x y z))))

(in-theory (disable nmake-if))

(defn to-if-subst (new old term)
  ;; Substitute new for the atom, old, in term.  Note that if old is not an
  ;; atom then this function will return the given good-to-if-p term
  ;; unchanged.
  (declare (xargs :guard (good-to-if-p term)))
  (cond ((atom term)
         (cond ((eq term t) t)
               ((eq term nil) nil)
               ((eql term old) new)
               (t term)))
        (t (hist 'if
                 (to-if-subst new old (cadr term))
                 (to-if-subst new old (caddr term))
                 (to-if-subst new old (cadddr term))))))

(defthm good-to-if-p-to-if-subst
  (implies (and (good-to-if-p new)
                (good-to-if-p term))
           (good-to-if-p (to-if-subst new old term))))

(defthm atom-to-if-implies-eqlablep-to-if-subst
  (implies (and (not (consp (to-if-subst new old term)))
                (good-to-if-p new)
                (good-to-if-p term))
           (eqlablep (to-if-subst new old term))))

(defconst *and-synonyms*   '(and & *))
(defconst *or-synonyms*    '(or \| +))
(defconst *iff-synonyms*   '(iff eq eql equal eqv xnor =
                                 == equiv <-> <=>))
(defconst *if-synonyms*    '(if ite mux))
(defconst *not-synonyms*   '(not ~))
(defconst *xor-synonyms*   '(xor exor))
(defconst *nand-synonyms*  '(nand))
(defconst *nor-synonyms*   '(nor))
(defconst *andc1-synonyms* '(andc1))
(defconst *andc2-synonyms* '(andc2))
(defconst *orc1-synonyms*  '(orc1 implies -> =>))
(defconst *orc2-synonyms*  '(orc2))

(defn to-if (term)
  (declare (xargs :verify-guards nil))

;;; This legacy doc string was replaced Nov. 2014 by the corresponding
;;; auto-generated defxdoc form in the last part of this file.

; ":Doc-section Hons-and-Memoization

;  Recognizer for the TO-IF langauge ~/

;  (TO-IF x) is a recognizer for objects in the TO-IF language, which
;  may be used for writing Boolean expressions.  The TO-IF language is
;  a subset of the TO-IF2 language.

;  If X is in the TO-IF language, then (TO-IF x) returns an equivalent
;  member of the TO-IF language expressed in the limited vocabulary of
;  IF, T, NIL, and variables.  The result returned is not in any
;  particular normal form, but it is in the form expected by the
;  function QNORM1.

;  If X is not in the TO-IF language, then (TO-IF x) returns a CONS
;  whose CAR is a string that may help explain in what sense X is not
;  in the TO-IF language.

;  Though similar to the language of ACL2, the TO-IF language is NOT
;  the same as the ACL2 langauge or the TO-IF2 language, so watch out!

;  (TERM-EVAL (TO-IF term) vars vals) gives the meaning of (TO-IF
;  TERM) with respect to the binding of the variables in VARS to the
;  Booleans in VALS.

;  Informally, in the TO-IF language, T and NIL both are and denote
;  the Boolean constants.  All eqlable ACL2 atoms (i.e., symbols,
;  integers, rational, complex numbers, characters, but not strings)
;  are variables in the TO-IF language.  The variables denote Boolean
;  values, i.e., T and NIL.

;  Merely for emphasis: The integer 2 is a variable in the TO-IF
;  language, odd as that may seem at first.

;  Merelly for emphasis:  The string \"2\" is not a TO-IF variable.

;  (IF x y z) means what Y means if X means T and means what Z means
;  if X means NIL.

;  (TO-IF `(LET ,x ,y ,z)) is the result of simultaneously replacing
;  in (TO-IF z) all the occurrences of the variable x with
;  (TO-IF y).  Note that although in Lisp, one might write:
;  (let ((x y)) z), the TO-IF 'LET' takes exactly three arguments.

;  In a TO-IF expression one may also use the unary operator NOT and
;  the binary operators AND, OR, IFF, IMPLIES, XOR, NAND, NOR, ANDC1,
;  ORC1, and ORC2.

;  TO-IF does not handle quantifiers such as FORALL nor FORSOME, nor
;  does it permit operators to take a variable number of arguments.
;  For such features, see TO-IF2.

;  There are many synonyms for the many familar logical operators.
;  Invoke (SAT-HELP) to see them all.  There is no facility
;  for a user to extend these synonyms.
;   ~/~/"

  (cond ((atom term)
         (cond ((eqlablep term) term)
               (t (hist "Illegal argument to to-if ~a." term))))
        ;; Zero Arguments
        ((to-if-error-p term) term)
        ((not (eqlablep (car term)))
         (hist "Illegal argument to to-if ~a." term))
        ((atom (cdr term))
         (cond ((not (null (cdr term)))
                (hist "Illegal argument to to-if ~a." term))
               ((member (car term) *and-synonyms*) t)
               ((member (car term) *or-synonyms*) nil)
               (t (hist "Illegal argument to to-if ~a." term))))
        ;; One Argument
        ((atom (cddr term))
         (cond ((not (null (cddr term)))
                (hist "Illegal argument to to-if ~a." term))
               (t (let ((arg1 (to-if (cadr term))))
                    (cond ((to-if-error-p arg1)
                           (hist "Illegal argument to to-if ~a."
                                 term))
                          ((member (car term) *not-synonyms*)
                           (nmake-if arg1 nil t))
                          ((or (member (car term) *and-synonyms*)
                               (member (car term) *or-synonyms*))
                           arg1)
                          (t (hist "Illegal arg to to-if ~a."
                                   term)))))))
        ;; Two Arguments
        ((atom (cdddr term))
         (cond ((not (null (cdddr term)))
                (hist "Illegal argument to to-if ~a." term))
               (t (let ((arg1 (to-if (cadr term)))
                        (arg2 (to-if (caddr term))))
                    (cond ((to-if-error-p arg1) arg1)
                          ((to-if-error-p arg2) arg2)
                          ((member (car term) *and-synonyms*)
                           (nmake-if arg1 arg2 nil))
                          ((member (car term) *or-synonyms*)
                           (nmake-if arg1 t arg2))
                          ((member (car term) *iff-synonyms*)
                           (nmake-if arg1 arg2 (nmake-if arg2 nil t)))
                          ((member (car term) *orc1-synonyms*)
                           (nmake-if arg1 arg2 t))
                          ((member (car term) *orc2-synonyms*)
                           (nmake-if arg1 (nmake-if arg2 nil t) t))
                          ((member (car term) *andc1-synonyms*)
                           (nmake-if arg2 (nmake-if arg1 nil t) nil))
                          ((member (car term) *andc2-synonyms*)
                           (nmake-if arg1 (nmake-if arg2 nil t) nil))
                          ((member (car term) *xor-synonyms*)
                           (nmake-if arg1 (nmake-if arg2 nil t) arg2))
                          ((member (car term) *nand-synonyms*)
                           (nmake-if arg1 (nmake-if arg2 nil t) t))
                          ((member (car term) *nor-synonyms*)
                           (nmake-if arg1 nil (nmake-if arg2 nil t)))
                          (t (hist "Illegal arg to to-if ~a."
                                   term)))))))
        ;; LET Expression
        ((and (null (cddddr term)) (eq (car term) 'let))
         (let ((var (cadr term))
               (val (caddr term))
               (body (cadddr term)))
           (cond ((or (not (symbolp var))
                      (eq var t)
                      (eq var nil))
                  (hist "Bad bound variable ~a." var))
                 (t (let ((valt (to-if val))
                          (bodyt (to-if body)))
                      (cond ((to-if-error-p valt) valt)
                            ((to-if-error-p bodyt) bodyt)
                            (t (to-if-subst valt var bodyt))))))))
        ;; IF Expression
        ((and (null (cddddr term)) (member (car term) *if-synonyms*))
         (let ((arg1 (to-if (cadr term)))
               (arg2 (to-if (caddr term)))
               (arg3 (to-if (cadddr term))))
           (cond ((to-if-error-p arg1) arg1)
                 ((to-if-error-p arg2) arg2)
                 ((to-if-error-p arg3) arg3)
                 (t (nmake-if arg1 arg2 arg3)))))
        (t (hist "Illegal argument to to-if ~a." term))))

(defthm good-to-if-p-to-if
  (implies (not (to-if-error-p (to-if term)))
           (good-to-if-p (to-if term))))

(verify-guards to-if)

(defn eql-var-lessp (v1 v2)
  (declare (xargs :guard (and (eqlablep v1)
                              (eqlablep v2))))
  (cond ((characterp v1)
         (if (characterp v2)
             (< (char-code v1)
                (char-code v2))
           t))
        ((symbolp v1)
         (if (characterp v2)
             nil
           (if (symbolp v2)
               (symbol< v1 v2)
             t)))
        (t (if (acl2-numberp v2)
               (if (< (imagpart v1) (imagpart v2))
                   t
                   (if (eql (imagpart v1) (imagpart v2))
                       (< (realpart v1) (realpart v2))
                       nil))
             nil))))

(in-theory (disable eql-var-lessp))

(defn var-lessp (v1 v2 var-order)
  (declare (xargs :guard (and (eqlablep v1)
                              (eqlablep v2)
                              (eqlable-listp var-order))))
  (let ((l1 (member v1 var-order))
        (l2 (member v2 var-order)))
    (if l1
        (if l2
            (and (not (eql v1 v2))
                 (member v2 l1))
          t)
      (if l2
          nil
        (eql-var-lessp v1 v2)))))

(in-theory (disable var-lessp))

(defn nmerge (l1 l2 var-order)
  (declare (xargs :guard (and (eqlable-listp l1)
                              (eqlable-listp l2)
                              (eqlable-listp var-order))
                  :measure (+ (acl2-count l1)
                              (acl2-count l2))))
  (cond ((atom l1) l2)
        ((atom l2) l1)
        ((eql (car l1) (car l2))
         (hons (car l1) (nmerge (cdr l1) (cdr l2) var-order)))
        ((var-lessp (car l1) (car l2) var-order)
         (hons (car l1)
               (nmerge (cdr l1) l2 var-order)))
        (t (hons (car l2)
                 (nmerge l1 (cdr l2) var-order)))))

(defthm eqlable-listp-nmerge
  (implies (and (eqlable-listp l1)
                (eqlable-listp l2)
                (eqlable-listp var-order))
           (eqlable-listp (nmerge l1 l2 var-order))))

(defn vars-help (term var-order)
  (declare (xargs :guard (and (good-to-if-p term)
                              (eqlable-listp var-order))
                  :verify-guards nil))
  (cond ((atom term)
         (cond ((or (eq term t) (eq term nil)) nil)
               (t (hist term))))
        (t (nmerge (vars-help (cadr term) var-order)
                   (nmerge (vars-help (caddr term) var-order)
                           (vars-help (cadddr term) var-order)
                           var-order)
                   var-order))))

(defthm eqlable-listp-vars-help
  (implies (and (good-to-if-p term)
                (eqlable-listp var-order))
           (eqlable-listp (vars-help term var-order))))

(verify-guards vars-help)
(in-theory (disable vars-help))

; VARS was defined to allow the use of CONS for intermediate partially
; sorted lists of symbols, and here we finally then make the list
; unique.

(defn vars (term var-order)
  (declare (xargs :guard (and (good-to-if-p term)
                              (eqlable-listp var-order))))
  (hons-copy (vars-help term var-order)))

(defthm eqlable-listp-vars
  (implies (and (good-to-if-p term)
                (eqlable-listp var-order))
           (eqlable-listp (vars term var-order))))


(defn qnorm1-guard (x)
  ;; Recognizes acceptable terms for QNORM.
  (if (atom x)
      (eqlablep x)
    (let ((fn (car x))
          (args (cdr x)))
      (case fn
        (if (and (consp args)
                 (consp (cdr args))
                 (consp (cddr args))
                 (null (cdddr args))
                 (qnorm1-guard (car args))
                 (qnorm1-guard (cadr args))
                 (qnorm1-guard (caddr args))))
        (quote (and (consp args)
                    (normp (car args))
                    (null (cdr args))))
        (otherwise nil)))))

(defn qnorm1 (term vars)

;;; This legacy doc string was replaced Nov. 2014 by the corresponding
;;; auto-generated defxdoc form in the last part of this file.

; ":Doc-section Hons-and-Memoization

;  Creates ubdds.   ~/

;  (QNORM1 term vars) returns the unique ubdd for TERM, an
;  IF-expression, with respect to the variable ordering VARS. ~/~/"

  (declare (xargs :measure (acl2-count term)
                  :guard (and (qnorm1-guard term)
                              (eqlable-listp vars))))
  (cond ((eq term t) t)
        ((eq term nil) nil)
        ((atom term) (var-to-tree term vars))
        ((eq (car term) 'if)
         (let ((test (qnorm1 (cadr term) vars)))
           (cond ((eq test t)
                  (qnorm1 (caddr term) vars))
                 ((eq test nil)
                  (qnorm1 (cadddr term) vars))
                 (t (q-ite
                     test
                     (qnorm1 (caddr term) vars)
                     (qnorm1 (cadddr term) vars))))))
        ((eq (car term) 'quote) (cadr term))
        (t (list "Bad arg to qnorm1 ~a." term))))

(defn qnorm1-guard-list (l)
  (if (atom l)
      t
    (and (qnorm1-guard (car l))
         (qnorm1-guard-list (cdr l)))))

(defn qnorm1-list (l vars)
  (declare (xargs :guard (and (qnorm1-guard-list l)
                              (eqlable-listp vars))))
  (if (atom l)
      nil
    (cons (qnorm1 (car l) vars)
          (qnorm1-list (cdr l) vars))))


(defthm good-to-if-p-implies-qnorm1-guard
  (implies (good-to-if-p term)
           (qnorm1-guard term)))

(defn qnorm (term)

;;; This legacy doc string was replaced Nov. 2014 by the corresponding
;;; auto-generated defxdoc form in the last part of this file.

; ":Doc-section Hons-and-Memoization

;  Creates ubdds.   ~/

; (QNORM term) returns the unique ubdd for TERM, an expression in
; the TO-IF language, with respect to the variable ordering returned
; by (VARS (TO-IF TERM) NIL).

; If TERM is a tautology, then QNORM returns T.  If term is
; a contradiction, then QNORM returns NIL.  If term is satisfiable,
; then QNORM returns a CONSP ubdd.~/~/"

  (let ((term (to-if term)))
    (cond ((to-if-error-p term) term)
          (t (qnorm1 term (vars term nil))))))

(defn qnorm-list (l vars)
  (declare (xargs :guard (eqlable-listp vars)))
  (cond ((atom l) nil)
        (t (let* ((term (to-if (car l)))
                  (term (if (to-if-error-p term)
                            term
                          (qnorm1 term vars))))
           (hons term
                 (qnorm-list (cdr l) vars))))))

(defn qtaut (term)
  (let ((x (to-if term)))
    (cond ((to-if-error-p x) x)
          (t (let ((vars (vars x nil)))
               (eq 't
                   (qnorm1 x vars)))))))

(defn qsublis (alist term)
  (declare (xargs :guard (and (good-to-if-p term)
                              (eqlable-alistp alist))))
  (cond ((atom term)
         (let ((ans (assoc term alist)))
           (if ans (cdr ans) term)))
        (t (hist 'if
                 (qsublis alist (cadr term))
                 (qsublis alist (caddr term))
                 (qsublis alist (cadddr term))))))

(defn t-nil-tree (x)
  (if (atom x)
      (or (eq x t) (eq x nil))
    (and (t-nil-tree (car x))
         (t-nil-tree (cdr x)))))

(defn q-to-if (term vars)
  (declare (xargs :guard (and (t-nil-tree term)
                              (eqlable-listp vars))))
  (if (atom term)
      term
    (let ((l (q-to-if (car term) (cdr vars)))
          (r (q-to-if (cdr term) (cdr vars))))
      (nmake-if (car vars) l r))))

(defthm good-to-if-p-is-q-to-if
  (implies (and (t-nil-tree term)
                (eqlable-listp vars))
           (good-to-if-p (q-to-if term vars))))

(defn re-order (term oldvars newvars)
  (declare (xargs :guard (and (t-nil-tree term)
                              (eqlable-listp oldvars)
                              (eqlable-listp newvars))))
  (qnorm1 (q-to-if term oldvars) newvars))


; A small set of tests to check our (normalizer-based) tautology
; checker.

(defn common-tautologies ()

  "(COMMON-TAUTOLOGIES) is a list of terms in the TO-IF language each
  of which is a propositional truth, i.e., is a tautology, i.e., has
  value T under all bindings of its variables."

  '((iff a a)
    (implies (and a b) a)
    (implies a (or a b))
    (iff (implies a (implies b c))
         (implies (and a b) c))
    (iff (implies a b) (or (not a) b))
    (iff (iff a b) (and (implies a b) (implies b a)))
    (iff (iff a b) (or (and a b) (and (not a) (not b))))
    (iff (implies a b) (implies (not b) (not a)))
    (iff (not a) (implies a nil))
    (iff (and a t) a)
    (iff (and a nil) nil)
    (iff (not t) nil)
    (iff (not nil) t)
    (iff (or a t) t)
    (iff (or a nil) a)
    (iff (iff a t) a)
    (iff (iff a nil) (not a))
    (iff (and a b) (and b a))
    (iff (or a b) (or b a))
    (iff (or a a) a)
    (iff (not (not a)) a)
    (iff (and a a) a)
    (iff (iff a a) t)
    (iff (xor a a) nil)
    (iff (iff a b) (iff b a))
    (iff (iff a (iff b c)) (iff (iff a b) c))
    (iff (and (or p (or q r))
              (or (not p) q))
         (and (or q r)
              (or (not p) q)))
    (implies (implies (not c) c) c)
    (iff (or a (or b c)) (or (or a b) c))
    (iff (and a (and b c)) (and (and a b) c))
    (iff (and a (or b c)) (or (and a b) (and a c)))
    (iff (or a (and b c)) (and (or a b) (or a c)))
    (iff (not (and a b)) (or (not a) (not b)))
    (iff (not (or a b)) (and (not a) (not b)))
    (iff (xor a b) (not (iff a b)))
    (iff (nor a b) (not (or a b)))
    (iff (nand a b) (not (and a b)))
    (iff (or a (iff b c)) (iff (or a b) (or a c)))
    (iff (and a (xor b c)) (xor (and a b) (and a c)))
    (iff (xor a (xor b c)) (xor (xor a b) c))
    (iff (if a b c) (and (implies a b) (implies (not a) c)))
    (iff (if t b c) b)
    (iff (if nil b c) c)
    (iff (if a b nil) (and a b))
    (iff (if a t b) (or a b))
    (iff (if a b b) b)
    (iff (if a a nil) a)
    (iff (if c b a) (if a (if b t (if c nil t)) (if b c nil)))
    (iff (if b2 a b1) (if a (if b1 t b2) (if b1 (if b2 nil t) nil)))
    (iff (if b1 a b2) (if a (if b1 t b2) (if b1 nil b2)))
    (iff (xor
          k
          (xor
           j
           (xor
            i
            (xor
             h
             (xor g (xor e (xor d (xor c (xor b a)))))))))
         (xor a (xor b (xor
                        c
                        (xor
                         d
                         (xor
                          e
                          (xor g (xor h (xor i (xor j k))))))))))))

(defn common-non-tautologies ()

  "(COMMON-NON-TAUTOLOGIES) is a short list of terms in the TO-IF
  language, each of which is a NOT a tautology."

  '(a
    (xor a b)
    (iff a b)
    (not a)
    (implies a b)
    (implies (or a b) (and a b))
    (iff (implies a b) (implies b a))
    (iff (implies a (implies b c)) (implies (implies a b) c))
    (iff (iff a (or b c)) (or (iff a b) (iff a c)))
    (iff (xor a (and b c)) (and (xor a b) (xor a c)))))

(defn check-q-true (l)
  (if (atom l)
      t
    (let ((term (to-if (car l))))
      (if (to-if-error-p term)
          nil
        (and (eq t (qnorm1 term (vars term nil)))
             (check-q-true (cdr l)))))))

(defn check-q-not-true (l)
  (if (atom l)
      t
    (let ((term (to-if (car l))))
      (if (to-if-error-p term)
          nil
        (and (not (eq t (qnorm1 term (vars term nil))))
             (check-q-not-true (cdr l)))))))

; We disable the executable counterparts so this theorem is checked
; each time this file is loaded.

(in-theory (disable (:executable-counterpart common-tautologies)
                    (:executable-counterpart common-non-tautologies)))

(in-theory (disable common-tautologies common-non-tautologies))

(defn check-q ()
  (and (check-q-true (common-tautologies))
       (check-q-not-true (common-non-tautologies))))

; As a way to i

(defn set-bdd (bdd loc v)
  (cond
   ((atom loc) v)
   ((car loc) (qcons (set-bdd (qcar bdd) (cdr loc) v) (qcdr bdd)))
   (t (qcons (qcar bdd) (set-bdd (qcdr bdd) (cdr loc) v)))))

(defn set-bdd-list (bdds loc vs)
  (if (or (atom vs) (atom bdds))
      nil
    (hons (set-bdd      (car bdds) loc (car vs))
          (set-bdd-list (cdr bdds) loc (cdr vs)))))

(defn set-bdd-pair-list (bdd-pairs loc vs)
  (if (or (atom vs)
          (atom bdd-pairs)
          (atom (car vs))
          (atom (car bdd-pairs)))
      nil
    (hons (hons (set-bdd (caar bdd-pairs) loc (caar vs))
                (set-bdd (cdar bdd-pairs) loc (cdar vs)))
          (set-bdd-pair-list (cdr bdd-pairs) loc (cdr vs)))))

(defconst *2t* t)

(defconst *2f* nil)

(defconst *4x* (hons t t))

(defconst *4u* (hons nil nil))

(defconst *4t* (hons t nil))

(defconst *4f* (hons nil t))

(defn to (x)
  (cond ((or (null x) (eq x 'f))         *4f*)
        ((eq x t)                        *4t*)
        ((or (eq x 'floating) (eq x 'u)) *4u*)
        (t                               *4x*)))

(defn to-list (l)
  (if (atom l) nil
    (cons (to (car l)) (to-list (cdr l)))))

(defn b-fix-eval-bdd (x values)
  (if (eval-bdd x values) t nil))

(defn qv-ite (c a b)
  (if (or (atom a) (atom b))
      nil
    (cons (q-ite c (car a) (car b))
          (qv-ite c (cdr a) (cdr b)))))

(defthm true-listp-qv-ite-if
  (true-listp (qv-ite c a b)))


;!!!  I want to everywhere change Q-IFF-LIST to Q-PAND-IFF-LIST.

(defn q-iff-list (x y)
  (if (or (atom x) (atom y))
      t
    (q-and-ite (q-iff-ite (car x) (car y))
               (q-iff-list (cdr x) (cdr y)))))

(defn or-c2 (x y) (or x (not y)))

(defn and-c1 (x y) (and (not x) y))

(defn and-c2 (x y) (and x (not y)))


; Finds a satisfying assignment for an ubdd.

(defn q-sat (x)
  (if (atom x)
      nil
    (if (eq (cdr x) nil)
        (cons t (q-sat (car x)))
      (cons nil (q-sat (cdr x))))))

; Given a list of ubdds, finds an assignment that satisfies at least
; one of them.

(defn q-sat-any (a)
  (if (atom a)
      nil
    (if (eq (car a) nil)
        (q-sat-any (cdr a))
      (q-sat (car a)))))

; Finds an assignment of ubdd variables which makes the two given ubdd
; vectors unequal.

; (defn find-ctrexample (a b)
;   (let ((xorlst (q-bv-xor a b)))
;    (q-sat-any xorlst)))

(defn q-and-is-nil (x y)
  (cond ((eq x t) (eq y nil))
        ((atom x) t)
        ((eq y t) nil)
        ((atom y) t)
        (t (and (q-and-is-nil (qcar x) (qcar y))
                (q-and-is-nil (qcdr x) (qcdr y))))))

(defn q-and-is-nilc2 (x y)
  (cond ((eq x t) (eq y t))
        ((atom x) t)
        ((eq y t) t)
        ((atom y) nil)
        (t (and (q-and-is-nilc2 (qcar x) (qcar y))
                (q-and-is-nilc2 (qcdr x) (qcdr y))))))

(defn q-not-is-atomic (x)
; returns T, NIL, or NOT-ATOMIC
  (if (atom x)
      (not x)
    'not-atomic))

(defabbrev atom-fix (y)
  (if (atom y) y 'not-atomic))

(defn q-ite-is-atomic (x y z)
  ; returns T, NIL, or NOT-ATOMIC
  (cond
   ((null x) (atom-fix z))
   ((atom x) (atom-fix y))
   (t (let ((y (if (hqual x y) t y))
            (z (if (hqual x z) nil z)))
        (cond ((hqual y z) (atom-fix y))
              ((and (eq y t) (eq z nil)) (atom-fix x))
              ((and (eq y nil) (eq z t)) (q-not-is-atomic x))
              (t (let ((a (q-ite-is-atomic
                           (car x) (qcar y) (qcar z)))
                       (d (q-ite-is-atomic
                           (cdr x) (qcdr y) (qcdr z))))
                   (cond ((or (eq a 'not-atomic)
                              (eq d 'not-atomic))
                          'not-atomic)
                         ((equal a d) a)
                         (t 'not-atomic)))))))))


;; ---------------- end of previous qi.lisp

#+hons
(memoize 'q-ite :condition '(and (consp x) (or (consp y) (consp z))))
#+hons
(memoize 'qnorm1)
#+hons
(memoize 'qvar-n)

(defn lfoo (x) (if (atom x) 0 (+ 1 (lfoo (cdr x)))))

#+hons
(memoize 'lfoo)

(defthm l-thm (equal (lfoo (hons-copy '(a b c))) 3))

(defthm l-thm2 (equal (lfoo (hons-copy '(a b c))) 3))

(defthm quick-sanity-check (check-q))

; The defxdoc forms below were initially generated automatically from
; legacy documentation strings in this file.

(include-book "xdoc/top" :dir :system)

(defxdoc normp
  :parents (hons-and-memoization)
  :short "Recognizer of ubdds."
  :long "<p>
 (NORMP x) returns T or NIL according to whether X is a well-formed ubdd, i.e.,
 a rooted, binary tree, in T and NIL, with no node equal to '(T . T) or '(NIL
 . NIL).</p>

 ")

(defxdoc q-ite
  :parents (hons-and-memoization)
  :short "If-then-else for ubdds."
  :long "<p>
 (Q-ITE x y z) expects three ubdds, which are to be interpreted at the same
 level.  Informally speaking. Q-ITE returns a single ubdd, also at the same
 level, that is 'equivalent' to (IF x y z).  The two theorems Q-ITE-CORRECT and
 NORMP-Q-ITE express formally what Q-ITE returns.</p>

 ")

(defxdoc qnorm
  :parents (hons-and-memoization)
  :short "Creates ubdds."
  :long "<p>
 (QNORM term) returns the unique ubdd for TERM, an expression in the TO-IF
   language, with respect to the variable ordering returned by (VARS (TO-IF
   TERM) NIL).</p>

 <p>If TERM is a tautology, then QNORM returns T.  If term is a contradiction,
   then QNORM returns NIL.  If term is satisfiable, then QNORM returns a CONSP
   ubdd.</p>

 ")

(defxdoc qnorm1
  :parents (hons-and-memoization)
  :short "Creates ubdds."
  :long "<p>
 (QNORM1 term vars) returns the unique ubdd for TERM, an IF-expression, with
 respect to the variable ordering VARS.</p>

 ")

(defxdoc to-if
  :parents (hons-and-memoization)
  :short "Recognizer for the TO-IF langauge"
  :long "<p>
 (TO-IF x) is a recognizer for objects in the TO-IF language, which may be used
 for writing Boolean expressions.  The TO-IF language is a subset of the TO-IF2
 language.</p>

 <p>If X is in the TO-IF language, then (TO-IF x) returns an equivalent member
 of the TO-IF language expressed in the limited vocabulary of IF, T, NIL, and
 variables.  The result returned is not in any particular normal form, but it
 is in the form expected by the function QNORM1.</p>

 <p>If X is not in the TO-IF language, then (TO-IF x) returns a CONS whose CAR
 is a string that may help explain in what sense X is not in the TO-IF
 language.</p>

 <p>Though similar to the language of ACL2, the TO-IF language is NOT the same
 as the ACL2 langauge or the TO-IF2 language, so watch out!</p>

 <p>(TERM-EVAL (TO-IF term) vars vals) gives the meaning of (TO-IF TERM) with
 respect to the binding of the variables in VARS to the Booleans in VALS.</p>

 <p>Informally, in the TO-IF language, T and NIL both are and denote the
 Boolean constants.  All eqlable ACL2 atoms (i.e., symbols, integers, rational,
 complex numbers, characters, but not strings) are variables in the TO-IF
 language.  The variables denote Boolean values, i.e., T and NIL.</p>

 <p>Merely for emphasis: The integer 2 is a variable in the TO-IF language, odd
 as that may seem at first.</p>

 <p>Merelly for emphasis: The string \"2\" is not a TO-IF variable.</p>

 <p>(IF x y z) means what Y means if X means T and means what Z means if X
 means NIL.</p>

 <p>(TO-IF `(LET ,x ,y ,z)) is the result of simultaneously replacing in (TO-IF
 z) all the occurrences of the variable x with (TO-IF y).  Note that although
 in Lisp, one might write: (let ((x y)) z), the TO-IF 'LET' takes exactly three
 arguments.</p>

 <p>In a TO-IF expression one may also use the unary operator NOT and the
 binary operators AND, OR, IFF, IMPLIES, XOR, NAND, NOR, ANDC1, ORC1, and
 ORC2.</p>

 <p>TO-IF does not handle quantifiers such as FORALL nor FORSOME, nor does it
 permit operators to take a variable number of arguments.  For such features,
 see TO-IF2.</p>

 <p>There are many synonyms for the many familar logical operators.  Invoke
 (SAT-HELP) to see them all.  There is no facility for a user to extend these
 synonyms.</p>

 ")
