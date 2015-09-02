(in-package "ACL2")

#|

  impl-hack.lisp
  ~~~~~~~~~~~~~~

This book is an implementation hack. The whole state of affairs is extremely
stupid here. What I want to do is the following. When we are asked whether a
(constant) formula is true of a (constant) circuit or not, we will apply the
compositional reduction (by evaluating that function) and then do
a series of model-checking on the reduced circuit. Since we are willing to rely
on an external model-checker, we want a hack function to be evaluated in common
lisp, where it will be redefined as an external system call. In order for that
to occur, we define the function with a guard of T and then set it up so that
the rewriter just makes multiple calls to this function for the model-checking
purpose.

|#

(include-book "reductions")

;; The following function is the hack. It does not matter what it returns,
;;since we will disable it, and use the defining axiom for our work. But it is
;;important to have the function defined with a guard of T so that ACL2 dares
;; to look into the common lisp for its implementation.

(defun ltl-semantics-hack (C f)
  (declare (xargs :guard t
                  :verify-guards t))
  (list C f))

(defun ltl-semantics-hack* (list)
  (if (endp list) T
    (and (ltl-semantics-hack (second (first list))
                             (first (first list)))
         (ltl-semantics-hack* (rest list)))))

(in-theory (disable ltl-semantics-hack (:definition ltl-semantics-hack)))

(defaxiom ltl-semantics-hack-revealed
  (equal (ltl-semantics-for-circuit C f)
         (ltl-semantics-hack C f)))

(local
(defthm ltl-semantocs-hack*-revealed
  (equal (ltl-semantics-hack* list)
         (ltl-semantics-for-circuits* list))
  :hints (("Goal"
           :induct (ltl-semantics-for-circuits* list))))
)

;; The following theorem rewrites the ltl-semantics-for-circuit into this hack*
;; function.

(DEFTHM ltl-semantics-hack-*-from-ltl-semantics-*
  (implies (syntaxp (and (quotep C)
                         (quotep f)))
           (implies (and (circuitp C)
                         (ltl-formulap f)
                         (subset (create-restricted-var-set f) (variables C)))
                    (equal (ltl-semantics-for-circuit C f)
                           (ltl-semantics-hack* (compositional-reduction C
                                                                         f)))))
  :hints (("Goal"
           :in-theory (disable circuitp ltl-semantics-for-circuit
                               compositional-reduction))))

;; Which then is opened up for a series of evaluations of the hack function.

(DEFTHM ltl-semantics-hack-revealed-for-rewriting
  (implies (syntaxp (quotep list))
           (equal (ltl-semantics-hack* list)
                  (if (endp list) T
                    (and (ltl-semantics-hack (second (first list))
                                             (first (first list)))
                         (ltl-semantics-hack* (rest list)))))))

(in-theory (disable ltl-semantics-hack* (:definition ltl-semantics-hack*)
                    (:type-prescription ltl-semantics-hack*)))

