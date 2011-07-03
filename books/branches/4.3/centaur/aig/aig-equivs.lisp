
(in-package "ACL2")

(include-book "base")
(include-book "centaur/misc/witness-cp" :dir :system)
(include-book "centaur/misc/universal-equiv" :dir :system)

(def-universal-equiv aig-equiv
  :qvars env
  :equiv-terms ((equal (aig-eval x env)))
  :defquant t
  :witness-dcls ((declare (xargs :guard t
                                 :verify-guards nil))))

(verify-guards aig-equiv)

(def-universal-equiv aig-alist-equiv
  :qvars k
  :equiv-terms ((iff (hons-assoc-equal k x))
                (aig-equiv (cdr (hons-assoc-equal k x))))
  :defquant t
  :witness-dcls ((declare (xargs :guard t
                                 :verify-guards nil))))

(verify-guards aig-alist-equiv)

(def-universal-equiv faig-equiv
  :qvars env
  :equiv-terms ((equal (faig-eval x env)))
  :defquant t
  :witness-dcls ((declare (xargs :guard t
                                 :verify-guards nil))))

(verify-guards faig-equiv)

(def-universal-equiv faig-alist-equiv
  :qvars k
  :equiv-terms ((iff (hons-assoc-equal k x))
                (faig-equiv (cdr (hons-assoc-equal k x))))
  :defquant t
  :witness-dcls ((declare (xargs :guard t
                                 :verify-guards nil))))

(verify-guards faig-alist-equiv)

(def-universal-equiv aig-env-equiv
  :qvars key
  :equiv-terms ((iff (aig-env-lookup key x)))
  :defquant t
  :witness-dcls ((declare (xargs :guard t
                                 :verify-guards nil))))

(verify-guards aig-env-equiv)


