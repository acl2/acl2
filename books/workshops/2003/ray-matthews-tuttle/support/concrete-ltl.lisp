(in-package "ACL2")

#|

  concrete-ltl.lisp
  ~~~~~~~~~~~~~~~~~

In this book, we define functions to reason about concrete semantics of
LTL. This book is shipped with the certification of our compositional reduction
paper for the purpose of demonstration. We first define a mutually recusrive
clique that defines the semantics of LTL and then we define a single recursive
function to justify that definition. We then go ahead and prove some properties
about the functions. Our goal is to prove the properties that are necessary
about the mutually recursive4 clique as the properties we wish to export about
semantics of LTL. For conjunctive and cone of influence reductions, we need
basically two properties.

(1) That the ltl semantics can be decomposed over conjunction. (Obvious from
definition)

(2) That it is oblivious to paths that are bisimilar.

We have removed the second part of the theorems from this book, primarily
because it was taking a humongous amount of time in v2-6, and I did not have
the guts to see how much time it takes to prove in v2-7. And further, we
contend that if we have defined the semantics of ltl such that the theorem
cannot be proved, then we need to consider redefining the semantics of
LTL. (This book, I hope will provide enough evidence that the semantics can be
defined.) Hence we reasoned completely using a function that is encapsulated
and known to satisfy this property. If the reader feels unsatisfied with this,
we can provide the actual theorems about ltl-periodic-path-emantics, (which are
actually slightly more general than those I exported from the constrained
functions).

|#

(include-book "ltl")

;; Added for compatibility with previous versions of ACL2.

(include-book "../../../../ordinals/e0-ordinal")
(set-well-founded-relation e0-ord-<)

(mutual-recursion

(defun ltl-periodic-path-semantics (f init prefix cycle label)
  (declare (xargs :measure (cons (1+ (acl2-count f)) 0)))
  (cond ((atom f)
         (if (ltl-constantp f)
             (equal f 'true)
           (memberp f (<- label init))))
        ((equal (len f) 3)
         (case (second f)
           (& (and (ltl-periodic-path-semantics (first f) init prefix cycle
                                                label)
                   (ltl-periodic-path-semantics (third f) init prefix cycle
                                                label)))
           (+ (or (ltl-periodic-path-semantics (first f) init prefix cycle
                                               label)
                  (ltl-periodic-path-semantics (third f) init prefix cycle
                                               label)))
           (U (let* ((found-and-index
                      (find-state-satisfying-formula
                       (third f) init prefix cycle label
                       (+ 1 (len prefix) (len cycle))))
                     (found (first found-and-index))
                     (index (second found-and-index)))
                (if (not found)
                    nil
                  (ltl-periodic-path-semantics* (first f) init prefix
                                                cycle label index))))
           (W (let* ((found-and-index
                      (find-state-satisfying-formula
                       (third f) init prefix cycle label
                       (+ 1 (len prefix) (len cycle))))
                     (found (first found-and-index))
                     (index (second found-and-index)))
                (if (not found)
                    (ltl-periodic-path-semantics* (first f) init prefix
                                                  cycle label
                                                  (+ 1 (len prefix) (len cycle)))
                  (ltl-periodic-path-semantics* (first f) init prefix
                                                cycle label index))))
           (t nil)))
        ((equal (len f) 2)
         (case (first f)
           (~ (not (ltl-periodic-path-semantics (second f) init prefix cycle
                                                label)))
           (G  (ltl-periodic-path-semantics* (second f) init prefix
                                             cycle label
                                             (+ 1 (len prefix) (len cycle))))
           (F (let* ((found-and-index
                      (find-state-satisfying-formula
                       (second f) init prefix cycle label
                       (+ 1 (len prefix) (len cycle))))
                     (found (first found-and-index)))
                (if found t nil)))
           (X (ltl-periodic-path-semantics (second f) (first prefix)
                                           (if (endp (rest prefix))
                                               cycle
                                             (rest prefix))
                                           cycle
                                           label))
           (t nil)))
        (t nil)))

(defun ltl-periodic-path-semantics* (f init prefix cycle label dist)
  (declare (xargs :measure (cons (1+ (acl2-count f)) (nfix dist))))
  (if (zp dist) t
    (and (ltl-periodic-path-semantics f init prefix cycle label)
         (ltl-periodic-path-semantics* f (first prefix)
                                       (if (endp (rest prefix))
                                           cycle
                                         (rest prefix))
                                       cycle label (1- dist)))))

(defun find-state-satisfying-formula (f init prefix cycle label dist)
  (declare (xargs :measure (cons (1+ (acl2-count f)) (nfix dist))))
  (cond ((zp dist) (list nil 0))
        ((ltl-periodic-path-semantics f init prefix cycle label)
         (list t 0))
        (t (let* ((found-and-index
                      (find-state-satisfying-formula
                        f (first prefix)
                        (if (endp (rest prefix)) cycle (rest prefix))
                        cycle label (1- dist)))
                  (found (first found-and-index))
                  (ndx (second found-and-index)))
             (list found (1+ ndx))))))

)

;; Now we have ther semantics of LTL that we will call the spec. We now proceed
;; to define a singly recursive version that is equivalent to the spec. Our
;; proofs will be using the singly recursive definition critically in order to
;; get us to what we want.

(defun ltl-semantics-single-recursion (f init prefix cycle label dist index)
  (declare (xargs :measure (cons (1+ (acl2-count f)) (if (equal index 0) 0 (nfix dist)))
                  :otf-flg nil))

  (if (equal index 0)
      (cond ((atom f)
             (if (ltl-constantp f)
                 (equal f 'true)
               (memberp f (<- label init))))
            ((equal (len f) 3)
             (case (second f)
               (& (and (ltl-semantics-single-recursion (first f) init prefix cycle
                                                       label dist 0)
                       (ltl-semantics-single-recursion (third f) init prefix cycle
                                                       label dist 0)))
               (+ (or (ltl-semantics-single-recursion (first f) init prefix cycle
                                                      label dist 0)
                      (ltl-semantics-single-recursion (third f) init prefix cycle
                                                      label dist 0)))
               (U (let* ((found-and-index
                          (ltl-semantics-single-recursion
                           (third f) init prefix cycle label
                           (+ 1 (len prefix) (len cycle))
                           2))
                         (found (first found-and-index))
                         (ndx (second found-and-index)))
                    (if (not found)
                        nil
                      (ltl-semantics-single-recursion (first f) init prefix
                                                        cycle label ndx 1))))
               (W (let* ((found-and-index
                          (ltl-semantics-single-recursion
                           (third f) init prefix cycle label
                           (+ 1 (len prefix) (len cycle))
                           2))
                         (found (first found-and-index))
                         (ndx (second found-and-index)))
                    (if (not found)
                        (ltl-semantics-single-recursion (first f) init prefix
                                                        cycle label
                                                        (+ 1 (len prefix) (len
                                                                           cycle))
                                                        1)
                      (ltl-semantics-single-recursion (first f) init prefix
                                                      cycle label ndx 1))))
               (t nil)))
            ((equal (len f) 2)
             (case (first f)
               (~ (not (ltl-semantics-single-recursion (second f) init prefix cycle
                                                       label dist 0)))
               (G  (ltl-semantics-single-recursion (second f) init prefix
                                                   cycle label
                                                   (+ 1 (len prefix) (len cycle)) 1))
               (F (let* ((found-and-index
                          (ltl-semantics-single-recursion
                           (second f) init prefix  cycle label
                           (+ 1 (len prefix) (len cycle))
                           2))
                         (found (first found-and-index)))
                    (if found T nil)))
               (X (ltl-semantics-single-recursion (second f) (first prefix)
                                                  (if (endp (rest prefix))
                                                      cycle
                                                    (rest prefix))
                                                  cycle
                                                  label dist 0))
               (t nil)))
            (t nil))
    (if (equal index 1)
        (if (zp dist) t
          (and (ltl-semantics-single-recursion f init prefix cycle label dist 0)
               (ltl-semantics-single-recursion f (first prefix)
                                               (if (endp (rest prefix))
                                                   cycle
                                                 (rest prefix))
                                               cycle label (1- dist)
                                               1)))
      (if (equal index 2)
          (cond ((zp dist) (list nil 0))
                ((ltl-semantics-single-recursion f init prefix cycle label dist 0)
                 (list t 0))
                (t (let* ((found-and-index
                           (ltl-semantics-single-recursion
                            f (first prefix)
                            (if (endp (rest prefix)) cycle (rest prefix))
                            cycle label (1- dist) 2))
                          (found (first found-and-index))
                          (ndx (second found-and-index)))
                     (list found (1+ ndx)))))
        nil))))


;; So do we believe that this big hodge-podge is same as the mutually recursive
;; code? Well, let us prove it.

(local
 ;; [Jared] added this because the following proof broke when I built it into ACL2.
 (in-theory (disable FOLD-CONSTS-IN-+)))

(defthm single-and-mutually-recursive-code-same
  (equal  (ltl-semantics-single-recursion f init prefix cycle label dist index)
          (if (equal index 0)
              (ltl-periodic-path-semantics f init prefix cycle label)
            (if (equal index 1)
                (ltl-periodic-path-semantics* f init prefix cycle label dist)
              (if (equal index 2)
                  (find-state-satisfying-formula f init prefix cycle
                                                 label dist)
                nil))))
  :rule-classes nil)

(defthm ltl-semantics-is-boolean
  (if (not (equal i 2))
      (booleanp (ltl-semantics-single-recursion f init prefix cycle label
                                                dist i))
    (and (booleanp (first (ltl-semantics-single-recursion f init prefix
                                                          cycle label dist
                                                          i)))
         (integerp (second (ltl-semantics-single-recursion f init prefix
                                                       cycle label dist
                                                       i)))))
  :rule-classes nil)

(defthm ltl-semantics-0-is-boolean
  (booleanp (ltl-semantics-single-recursion f init prefix cycle label dist 0))
  :hints (("Goal"
           :use ((:instance single-and-mutually-recursive-code-same
                            (index 0)))))
  :rule-classes :type-prescription)

(defthm ltl-semantics-1-boolean
  (booleanp (ltl-semantics-single-recursion f init prefix cycle label dist 1))
   :hints (("Goal"
           :use ((:instance single-and-mutually-recursive-code-same
                            (index 1)))))
  :rule-classes :type-prescription)

(defthm ltl-semantics->2-boolean
  (implies (and (not (equal i 0))
                (not (equal i 1))
                (not (equal i 2)))
           (not (ltl-semantics-single-recursion f init prefix cycle label
                                                     dist i)))
  :rule-classes :type-prescription)

(defthm ltl-semantics-2-boolean
  (booleanp (first (ltl-semantics-single-recursion f init prefix cycle label
                                                   dist 2)))
  :hints (("Goal"
           :use ((:instance ltl-semantics-is-boolean
                            (i 2)))))
  :rule-classes :type-prescription)

(defthm ltl-semantics-2-integer
   (integerp (second (ltl-semantics-single-recursion f init prefix cycle label
                                                   dist 2)))
  :hints (("Goal"
           :use ((:instance ltl-semantics-is-boolean
                            (i 2)))))
  :rule-classes :type-prescription)

(defthm ltl-periodic-path-semantics-decomposed-for-conjunction
  (implies (and ;; (ltl-formulap f)
                (equal (len f) 3)
                (equal (second f) '&))
           (equal (ltl-periodic-path-semantics f init prefix cycle label)
                  (and (ltl-periodic-path-semantics (first f) init prefix cycle
                                                    label)
                       (ltl-periodic-path-semantics (third f) init prefix cycle
                                                    label))))
  :rule-classes nil)
