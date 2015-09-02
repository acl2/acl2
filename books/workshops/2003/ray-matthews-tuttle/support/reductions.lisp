(in-package "ACL2")

#|

  reductions.lisp
  ~~~~~~~~~~~~~~~

In this book, we use the conjunctive reduction and cone of influence reduction
compositionally to provide reduction algorithms for circuits.

|#

(local
(include-book "conjunction")
)

(include-book "cone-of-influence")


(defun ltl-semantics-for-circuit (C f)
  (ltl-semantics f (create-kripke C)))

(defun ltl-semantics-for-circuits* (list)
  (if (endp list) T
    (and (ltl-semantics-for-circuit (second (first list))
                                    (first (first list)))
         (ltl-semantics-for-circuits* (rest list)))))


(defun reduce-problem-conjunction (f C)
  (if (and (equal (len f) 3)
           (equal (second f) '&))
      (append (reduce-problem-conjunction (first f) C)
              (reduce-problem-conjunction (third f) C))
    (list (list f C))))

(defun reduce-problem-cone (f C)
  (let ((vars (create-restricted-var-set f)))
    (cone-of-influence-reduction C vars)))

(defun reduce-problem-cone* (list)
  (if (endp list) nil
    (cons (list (first (first list))
                (reduce-problem-cone (first (first list)) (second (first list))))
            (reduce-problem-cone* (rest list)))))


(defun compositional-reduction (C f)
  (let ((list (reduce-problem-conjunction f C)))
    (reduce-problem-cone* list)))

;; OK, so let us dispatch the obligations for conjunction first.

(local
(in-theory (disable ltl-semantics create-kripke ltl-formulap))
)

(local
(defthm ltl-semantics*-append-reduction
  (equal (ltl-semantics-for-circuits* (append x y))
         (and (ltl-semantics-for-circuits* x)
              (ltl-semantics-for-circuits* y))))
)

(local
(defthm conjunction-produces-correct-list
  (implies (ltl-formulap f)
           (equal (ltl-semantics-for-circuits*
                   (reduce-problem-conjunction f C))
                  (ltl-semantics-for-circuit C f)))
  :otf-flg t
  :hints (("Goal"
           :induct (reduce-problem-conjunction f C)
           :do-not-induct t
           :in-theory (enable ltl-formulap)
           :do-not '(eliminate-destructors generalize))))
)

;; To work with reduce-problems-cone, we need to assume that the variables in f
;; are subsets of the variables in cone of influence reduction. We show that
;; assuming that the variables are subsets of variables of the circuit. We need
;; to show though that the variables of cone will be a superset of vars if we
;; start with a collection of vars that are subset of the variables of the
;; circuit.

(local
(encapsulate
 ()
 (defthm not-memberp-union-reduction
   (implies (and (not (memberp e x))
                 (not (memberp e y)))
            (not (memberp e (set-union x y))))
   :hints (("Goal"
            :in-theory (enable set-union))))

 (local
 (defthm uniquep-set-union-reduction
   (implies (and (uniquep x)
                 (uniquep y))
            (uniquep (set-union x y)))
   :hints (("Goal"
            :in-theory (enable set-union))))
 )

 (local
 (in-theory (disable consistent-equation-record-p))
 )

 (local
 (defthm consistent-equation-record-p-expanded
   (implies (and (consistent-equation-record-p vars equations)
                 (uniquep vars)
                 (memberp v vars)
                 (memberp equation (<- equations v)))
            (subset (find-variables equation)
                    vars))
   :hints (("Goal"
            :use consistent-equation-record-p-necc)))
 )

 (local
 (in-theory (disable consistent-equation-record-p-necc))
 )

 (local
 (defthm set-union-subset-reduction
   (implies (and (subset x z)
                 (subset y z))
            (subset (set-union x y) z))
   :hints (("Goal"
            :in-theory (enable set-union))))
 )

 (local
 (defthm find-variables*-subset-of-variables
   (implies (and (consistent-equation-record-p variables equations)
                 (uniquep variables)
                 (memberp v variables)
                 (subset equation-list (<- equations v)))
            (subset (find-variables* equation-list)
                    variables))
   :hints (("Goal"
            :in-theory (disable find-variables)
            :induct (find-variables* equation-list)
            :do-not '(eliminate-destructors generalize)
            :do-not-induct t)))
 )

 (local
 (defthm find-variables*-is-subset-concretized
   (implies (and (consistent-equation-record-p variables equations)
                 (memberp v variables)
                 (uniquep variables))
            (subset (find-variables* (<- equations v)) variables)))
 )

 (local
 (in-theory (disable find-variables*-subset-of-variables))
 )

 (local
 (defthm find-variables-1-pass-is-subset
   (implies (and (consistent-equation-record-p variables equations)
                 (subset vars variables)
                 (uniquep variables))
            (subset (find-all-variables-1-pass vars equations)
                    variables)))
 )

 (local
 (defthm memberp-union-reduction-1
   (implies (memberp e x)
            (memberp e (set-union y x)))
   :hints (("Goal"
            :in-theory (enable set-union))))
 )

 (local
 (defthm memberp-find-all-variables-reduction
   (implies (and (consistent-equation-record-p variables equations)
                 (subset vars variables)
                 (memberp v vars))
            (memberp v (find-all-variables vars variables equations)))
   :otf-flg t
   :hints (("Goal"
            :induct (find-all-variables vars variables equations)
            :do-not '(eliminate-destructors generalize)
            :do-not-induct t)))
 )

 (local
 (defthm find-all-variables-produces-subset
   (implies (and (consistent-equation-record-p variables equations)
                 (subset vars variables)
                 (subset vars-prime vars))
            (subset vars-prime (find-all-variables vars variables equations))))
 )

 (local
 (defthm set-intersect-is-subset
   (implies (and (subset vars variables)
                 (subset vars vars-prime))
            (subset vars (set-intersect vars-prime variables))))
 )

 (local
 (defthm memberp-remove-reduction
   (equal (memberp e (remove-duplicate-occurrences variables))
          (memberp e variables)))
 )

 (local
 (defthm remove-duplicates-is-subset
   (implies (subset vars variables)
            (subset vars (remove-duplicate-occurrences variables))))
 )

 (local
 (defthm cone-variables-are-subset
   (implies (and (consistent-equation-record-p variables equations)
                 (subset vars variables))
            (subset vars (find-all-variables
                          (set-intersect
                           (remove-duplicate-occurrences vars)
                           variables)
                          variables equations)))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (disable find-all-variables-produces-subset)
            :use ((:instance find-all-variables-produces-subset
                             (vars-prime vars)
                             (vars (set-intersect
                                    (remove-duplicate-occurrences vars)
                                    variables)))))))
 )

 (local
 (defthm circuitp-to-cone-variables
   (implies (and (circuitp C)
                 (subset vars (variables C)))
            (subset vars (cone-variables vars C))))
 )

 (local
 (in-theory (disable circuitp cone-variables cone-of-influence-reduction))
 )

 (defthm cone-of-influence-reduction-for-specific
   (implies (and (circuitp C)
                 (ltl-formulap f)
                 (subset (create-restricted-var-set f)
                         (variables C)))
            (equal (ltl-semantics-for-circuit  (cone-of-influence-reduction
                                                C (create-restricted-var-set
                                                   f))
                                               f)
                   (ltl-semantics-for-circuit C f)))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (disable cone-of-influence-reduction-is-sound-generalized)
            :use ((:instance cone-of-influence-reduction-is-sound-generalized
                             (interesting-vars (create-restricted-var-set f))
                             (vars (create-restricted-var-set f)))))))

 )
)

(local
(in-theory (disable ltl-semantics-for-circuit create-restricted-var-set
                    cone-of-influence-reduction
                    circuitp ltl-formulap))
)

(local
(defthm reduce-problem-cone-reduction
  (implies (and (circuitp C)
                (ltl-formulap f)
                (subset (create-restricted-var-set f) (variables C)))
           (equal (ltl-semantics-for-circuit (reduce-problem-cone f C)
                                             f)
                  (ltl-semantics-for-circuit C f))))
)

(local
(in-theory (disable reduce-problem-cone))
)

(local
(defun well-formed-problems-p (list)
  (if (endp list) T
    (and (ltl-formulap (first (first list)))
         (circuitp (second (first list)))
         (subset (create-restricted-var-set (first (first list)))
                 (variables (second (first list))))
         (well-formed-problems-p (rest list)))))
)

(local
(defthm reduce-problem-cone*-reduction
  (implies (well-formed-problems-p list)
           (equal (ltl-semantics-for-circuits* (reduce-problem-cone* list))
                  (ltl-semantics-for-circuits* list)))
  :otf-flg t
  :hints (("Goal"
           :in-theory (enable reduce-problem-cone*)
           :do-not '(eliminate-destructors generalize))))
)

(local
(defthm subset-member-reduction
  (implies (and (subset (set-union x y) z)
                (memberp e x))
           (memberp e z))
  :hints (("Goal"
           :in-theory (enable set-union))))
)

(local
(defthm subset-member-reduction-2
  (implies (and (subset (set-union x y) z)
                (memberp e y))
           (memberp e z))
  :hints (("Goal"
           :in-theory (enable set-union))))
)

(local
(defthm set-union-subset-reduction
  (implies (subset (set-union x y) z)
           (subset x z))
  :hints (("Goal"
           :in-theory (enable set-union))))
)

(local
(defthm set-union-subset-reduction-2
  (implies (subset (set-union x y) z)
           (subset y z))
  :hints (("Goal"
           :in-theory (enable set-union))))
)

(local
(defthm conjunction-has-variables-subset-1
  (implies (and (ltl-formulap f)
                (equal (len f) 3)
                (subset (create-restricted-var-set f) vars))
           (subset (create-restricted-var-set (first f)) vars))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t
           :in-theory (enable create-restricted-var-set ltl-formulap)
           :expand (create-restricted-var-set f))))
)
(local
(defthm conjunction-has-variables-subset-2
   (implies (and (ltl-formulap f)
                (equal (len f) 3)
                (subset (create-restricted-var-set f) vars))
           (subset (create-restricted-var-set (third f)) vars))
  :hints (("Goal"
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t
           :in-theory (enable create-restricted-var-set ltl-formulap)
           :expand (create-restricted-var-set f))))
)

(local
(defthm well-formed-append-reduction
  (implies (and (force (well-formed-problems-p first))
                (force (well-formed-problems-p second)))
           (well-formed-problems-p (append first second))))
)

(local
(defthm conjunction-produces-well-formed-problems
  (implies (and (circuitp C)
                (ltl-formulap f)
                (subset (create-restricted-var-set f) (variables C)))
           (well-formed-problems-p (reduce-problem-conjunction f C)))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(eliminate-destructors generalize)
           :induct (reduce-problem-conjunction f C))))
)

(DEFTHM compositional-reduction-is-sound
  (implies (and (circuitp C)
                (ltl-formulap f)
                (subset (create-restricted-var-set f) (variables C)))
           (equal (ltl-semantics-for-circuits* (compositional-reduction C f))
                  (ltl-semantics-for-circuit C f))))
