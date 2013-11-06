

(in-package "ACL2")



(defund suffixp (x y)
  (declare (xargs :guard t))
  (or (equal x y)
      (and (consp y)
           (suffixp x (cdr y)))))

(defthm suffixp-cons
  (equal (suffixp a (cons c b))
         (or (equal a (cons c b))
             (suffixp a b)))
  :hints(("Goal" :in-theory (enable suffixp))))



(defthm not-suffixp-cons
  (implies (not (suffixp a b))
           (not (suffixp (cons c a) b)))
  :hints(("Goal" :in-theory (enable suffixp))))



(defthm suffixp-self
  (suffixp x x)
  :hints(("Goal" :in-theory (enable suffixp))))



(defthm suffixp-trans1
  (implies (and (suffixp b c)
                (suffixp a b))
           (suffixp a c))
  :hints(("Goal" :in-theory (enable suffixp))))
