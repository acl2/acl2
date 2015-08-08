(in-package "MODEL-CHECK")
(include-book "relations")
(include-book "fixpoints")

(defun modelp (m)
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
(defun states (m)
  (first m))

(defun relation (m)
  (second m))

(defun atomic-props (m)
  (third m))

(defun s-labeling (m)
  (fourth m))

(defun inverse-relation (m)
  (fifth m))

(defun a-labeling (m)
  (sixth m))

(defun size (m)
  (seventh m))

(defun make-model (s r ap sl)
"Make a model given s, a list of states, r the transition relation of
the form ((s0 si sj ...) ... (sn sl sk)) (indicating that there is an
arc from s0 to si, sj, etc.), sl is the state labeling of the form
 ((s0 p q ...)  ...  (sn r ...)) where p,q,r are in the list of atomic
propositions ap. The model includes the inverse transition relation
 (useful for EX A forumulas) and the inverse labeling relation ((p si
sj ...) ... (s sk sm ...))  indicating at which states atomic
propositions are true."
  (list s r ap sl (inverse r) (inverse sl) (cardinality s)))
