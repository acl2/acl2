(in-package "ACL2")

(defthm integer-listp-update-nth--thm
(implies
  (and (integer-listp n)
       (>= x 0)
       (integerp y)
       (< x (len n)))
  (integer-listp (update-nth x y n)))
  :rule-classes ((:forward-chaining :trigger-terms ((update-nth x y n))) :rewrite)
)

(defthm integer-listp-update-nth-len--thm
(implies
  (and (integer-listp n) (<= 0 x) (< x (len n)))
  (= (len (update-nth x y n)) (len n))))


(defthm int-list--thm
(implies
  (and (integer-listp n)
       (>= x 0)
       (< x (len n)))
  (integerp (nth x n)))
  :rule-classes ((:forward-chaining :trigger-terms ((nth x n))) :rewrite)
)
