; (certify-book "term-ordered-perms")

(in-package "ACL2")

(include-book "sorting/perm" :dir :system)

(defun term-orderedp (x)
       (if (endp x)
           t
         (if (endp (cdr x))
             t
           (and (term-order (car x) (car (cdr x)))
                (term-orderedp (cdr x))))))

(encapsulate nil
  (local (defthm term-orderedp-rm
           (implies (term-orderedp a)
                    (term-orderedp (rm e a)))))

  (local (defthm term-orderedp-memb
           (implies (and (term-orderedp a)
                         (not (equal e (car a)))
                         (term-order e (car a)))
                    (not (memb e a)))))

  (local (defthm equal-cons
           (equal (equal (cons a b) x)
                  (and (consp x)
                       (equal a (car x))
                       (equal b (cdr x))))))

  (local (defthm car-rm
           (equal (car (rm e a))
                  (if (consp a)
                      (if (equal e (car a))
                          (cadr a)
                          (car a))
                      nil))))

  (local (defthm true-listp-rm
           (implies (true-listp a)
                    (true-listp (rm e a)))))

  (defthm term-ordered-perms
    (implies (and (true-listp a)
                  (true-listp b)
                  (term-orderedp a)
                  (term-orderedp b))
             (equal (equal a b)
                    (perm a b)))
    :rule-classes nil))

