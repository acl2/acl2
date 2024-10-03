(in-package "DJVM")
(include-book "consistent-state")
(include-book "consistent-state-obj-init")


(acl2::set-verify-guards-eagerness 2)






(defun consistent-state-strong (s)
  (and (consistent-state s)
       (consistent-state-obj-init s)))



;;;
;;; experiment, shall we leave it enabled!! 
;;; 
;;; Fri Aug  5 14:00:23 2005
;;;


(in-theory (disable consistent-state-strong 
                    consistent-state 
                    consistent-state-obj-init))

(defthm consistent-state-strong-implies-consistent-state-f
  (implies (consistent-state-strong s)
           (consistent-state s))
  :hints (("Goal" :in-theory (enable consistent-state-strong)))
  :rule-classes :forward-chaining)



(defthm consistent-state-strong-implies-consistent-state-obj-init-f
  (implies (consistent-state-strong s)
           (consistent-state-obj-init s))
  :hints (("Goal" :in-theory (enable consistent-state-strong)))
  :rule-classes :forward-chaining)



(defthm consistent-state-strong-implies-consistent-state-b
  (implies (and (syntaxp (symbolp s))
                (consistent-state-strong s))
           (consistent-state s))
  :hints (("Goal" :in-theory (enable consistent-state-strong))))


(defthm consistent-state-strong-implies-consistent-state-obj-init-b
  (implies (and (syntaxp (symbolp s))
                (consistent-state-strong s))
           (consistent-state-obj-init s))
  :hints (("Goal" :in-theory (enable consistent-state-strong))))


(defthm consistent-state-strong-implied-by-b
  (implies (and (syntaxp (not (symbolp s)))
                (consistent-state s)
                (consistent-state-obj-init s))
           (consistent-state-strong s))
  :hints (("Goal" :in-theory (enable consistent-state-strong))))

