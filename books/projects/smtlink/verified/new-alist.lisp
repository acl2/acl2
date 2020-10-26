(in-package "ACL2")
(include-book "std/util/define" :dir :system) ;; for define
(include-book "centaur/fty/basetypes" :dir :system) ;; for any-p

(encapsulate ;; model of an array
 (((key-p *) => *)
  ((val-p *) => *)
  ((array-p *) => *)
  ((make-up-a-value *) => *)
  ((array-init) => *)
  ((array-store * * *) => *)
  ((array-select * *) => *))

 ;; local implementations of functions -- implement an array with an alist
 ;; type-recognizers
 (local (define key-p (x)
          :returns (ok any-p)
          :ignore-ok t
          :irrelevant-formals-ok t
          t))

 (local (define val-p (x)
          :returns (ok any-p)
          :ignore-ok t
          :irrelevant-formals-ok t
          t))

 (local (define array-p (x)
          :returns (ok any-p)
          (alistp x)))

 (local (define make-up-a-value (key)
          :returns (v any-p)
          :ignore-ok t
          :irrelevant-formals-ok t
          nil))

 (local (define array-init ()
          :returns (ar0 any-p)
          nil))

 (local (define array-store (key val ar)
          :returns (ar2 any-p)
          (if (alistp ar)
              (acons key val ar)
            (array-init))))

 (local (define array-select (key ar)
          :returns (v any-p)
          (if (alistp ar)
              (cdr (assoc-equal key ar))
            (make-up-a-value key))))

 ;; return type theorems
 (defthm boolean-of-key-p (booleanp (key-p x)))
 (defthm boolean-of-val-p (booleanp (val-p x)))
 (defthm boolean-of-array-p (booleanp (array-p x)))
 (defthm val-p-of-make-up-a-value (val-p (make-up-a-value k)))
 (defthm array-p-of-array-init (array-p (array-init)))
 (defthm array-p-of-array-store
  (implies (and (key-p k) (val-p v) (array-p ar))
           (array-p (array-store k v ar)))
  :hints (("Goal"
           :in-theory (enable array-p array-store))))
 (defthm val-p-of-array-select
  (implies (and (key-p k) (array-p ar))
           (let ((v (array-select k ar)))
             (or (val-p v) (null v)))))
 )
