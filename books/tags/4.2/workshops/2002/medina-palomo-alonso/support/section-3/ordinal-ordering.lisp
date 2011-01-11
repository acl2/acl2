;;; ----------------
;;; Ordinal ordering
;;; ----------------

(in-package "ACL2")

;;; The ordinal ordering is a partial strict order.

(defthm |~(a o< a)|
  (not (o< a a)))

(defthm |a o< b & b o< c => a o< c|
  (implies (and (o< a b) (o< b c)) (o< a c)))

;;; Antisymmetry of the ordinal ordering.

(defthm |a o< b => ~(b o< a)|
  (implies (o< a b)
           (not (o< b a)))
  :hints (("Goal"
	   :in-theory (disable |a o< b & b o< c => a o< c|)
	   :use (:instance |a o< b & b o< c => a o< c| (c a)))))
