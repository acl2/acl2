;; null-fail-hints.lisp
;; by Sol Swords

;; This file introduces two hint keywords, used as follows:
;;
;; :null nil - an identity hint; useful in :or hints for an alternative in
;;             which nothing is done
;;
;; :fail nil - a hint which causes failure; useful when you want a proof to
;;             automatically fail at a certain point.
;;

(in-package "ACL2")


(include-book "join-thms")

(defun identity-clause-processor (clause)
  (list clause))

(defevaluator null-fail-hint-ev null-fail-hint-evl ((if a b c)))

(def-join-thms null-fail-hint-ev)

(defthm identity-clause-processor-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (null-fail-hint-ev (conjoin-clauses (identity-clause-processor clause))
                         a))
           (null-fail-hint-ev (disjoin clause) a))
  :rule-classes :clause-processor)


(add-custom-keyword-hint
 :null (value (splice-keyword-alist
               :null '(:clause-processor identity-clause-processor)
               keyword-alist))
 :checker (if (eq val nil)
              (value t)
            (er soft 'null-hint "Use value NIL with the :NULL keyword hint.")))


(defun fail-clause-processor (clause)
  (declare (ignore clause))
  (list (list ''nil)))

(defthm fail-clause-processor-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (null-fail-hint-ev (conjoin-clauses (fail-clause-processor clause))
                         a))
           (null-fail-hint-ev (disjoin clause) a))
  :rule-classes :clause-processor)






(add-custom-keyword-hint
 :fail (value (splice-keyword-alist
               :fail '(:clause-processor
                       fail-clause-processor
                       :do-not '(:preprocess simplify))
               keyword-alist))
 :checker (if (eq val nil)
              (value t)
            (er soft 'fail-hint "Use value NIL with the :FAIL keyword hint.")))
