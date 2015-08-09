(in-package "MODEL-CHECK")

(include-book "relations")

; Exercise 17, part 1
(defun modelp (m)
  (declare (xargs :guard t))
  (and (true-listp m)
       (equal (len m) 7)
       (true-listp (first m))
       (relationp (second m))
       (true-listp (third m))
       (relationp (fourth m))
       (relationp (fifth m))
       (relationp (sixth m))
       (integerp (seventh m))
       (<= 0 (seventh m))))

; The components of a model

; Exercise 17, part 2
(defun states (m)
"The states of model m."
  (declare (xargs :guard (modelp m)))
  (first m))

; Exercise 17, part 3
(defun relation (m)
"The relation of model m."
  (declare (xargs :guard (modelp m)))
  (second m))

; Exercise 17, part 4
(defun atomic-props (m)
"The atomic props of model m."
  (declare (xargs :guard (modelp m)))
  (third m))

; Exercise 17, part 5
(defun s-labeling (m)
"The list of props true at states list of model m."
  (declare (xargs :guard (modelp m)))
  (fourth m))

; Exercise 17, part 6
(defun inverse-relation (m)
"The converse relation of model m."
  (declare (xargs :guard (modelp m)))
  (fifth m))

; Exercise 17, part 7
(defun a-labeling (m)
"The list of states for which props hold of model m."
  (declare (xargs :guard (modelp m)))
  (sixth m))

; Exercise 17, part 8
(defun size (m)
"The cardinality of the states of m."
  (declare (xargs :guard (modelp m)))
  (seventh m))

(defthm back-chain-modelp
  (implies (and (true-listp m)
		(equal (len m) 7)
		(true-listp (first m))
		(relationp (second m))
		(true-listp (third m))
		(relationp (fourth m))
		(relationp (fifth m))
		(relationp (sixth m))
		(integerp (seventh m))
		(<= 0 (seventh m)))
	   (modelp m)))

(defthm forward-chain-modelp
  (implies (modelp m)
	   (and (true-listp m)
		(equal (len m) 7)
		(true-listp (first m))
		(relationp (second m))
		(true-listp (third m))
		(relationp (fourth m))
		(relationp (fifth m))
		(relationp (sixth m))
		(integerp (seventh m))
		(<= 0 (seventh m))))
  :rule-classes :forward-chaining)

(in-theory (disable modelp))

(defung make-model (s r ap sl)
"Make a model given s, a list of states, r the transition relation of
the form ((s0 si sj ...) ... (sn sl sk)) (indicating that there is an
arc from s0 to si, sj, etc.), sl is the state labeling of the form
 ((s0 p q ...)  ...  (sn r ...)) where p,q,r are in the list of atomic
propositions ap. The model includes the inverse transition relation
 (useful for EX A forumulas), the inverse labeling relation ((p si
sj ...) ... (s sk sm ...))  indicating at which states atomic
propositions are true, and the size of the model."
  (declare (xargs :guard (and (true-listp s) (relationp r)
			      (true-listp ap) (relationp sl))))
  ((implies (and (true-listp s) (relationp r) (true-listp ap) (relationp sl))
	    (modelp (make-model s r ap sl))) :rule-classes nil)
  (list s r ap sl (inverse r) (inverse sl) (cardinality s)))
