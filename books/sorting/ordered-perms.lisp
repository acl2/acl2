; (certify-book "ordered-perms")

(in-package "ACL2")

(include-book "perm")

(include-book "orderedp")

(encapsulate nil
             (local (defthm orderedp-rm
                      (implies (orderedp a)
                               (orderedp (rm e a)))))

             (local (defthm orderedp-memb
                      (implies (and (orderedp a)
                                    (not (equal e (car a)))
                                    (lexorder e (car a)))
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

             (defthm ordered-perms
               (implies (and (true-listp a)
                             (true-listp b)
                             (orderedp a)
                             (orderedp b))
                        (equal (equal a b)
                               (perm a b)))
               :rule-classes nil))
