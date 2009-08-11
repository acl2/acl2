(in-package "ACL2")

(include-book "in-conclusion")

(defund imp (a x)
  (if x t (and a t)))

(defcong iff equal (imp a x) 1
  :hints (("Goal" :in-theory (enable imp))))

(defthm open-imp-in-conclusion
  (implies
   (in-conclusion-check (imp a x) :top :any)
   (equal (imp a x) (if x t (and a t))))
  :hints (("Goal" :in-theory (enable imp))))

(defthm implies-imp
  (implies a (imp a x))
  :hints (("Goal" :in-theory (enable imp))))

;; The idea here is to rewrite a boolean term into an expression that
;; implies that term.
;;
;; For example: (=> (acl2-numberp x) (integerp x))
;;
;; Note that this can very easily render a provable goal unprovable.
;;
;; Note that we will usually only want to do this to terms we find in
;; our conclusion.

(defmacro => (x a)
  `(iff ,x (imp ,a (hide ,x))))

