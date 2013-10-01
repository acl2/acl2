#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

(local (defun card (x)
         (if (endp x)
           0
           (if (member-equal (car x) (cdr x))
             (card (cdr x))
             (nfix (1+ (card (cdr x))))))))
(local (defun setp (x)
         (if (endp x)
           t
           (and (not (member-equal (car x) (cdr x)))
                (setp (cdr x))))))
(local (defun set-recursion-scheme (x y)
         (if (endp x) y
           (set-recursion-scheme (remove (car x) x)
                                 (remove (car x) y)))))



(local (defthm member-remove-nonmember
         (implies (not (member-equal a x))
                  (not (member-equal a (remove b x))))))
(local (defthm setp-remove
         (implies (setp x)
                  (setp (remove a x)))
         :rule-classes :type-prescription))
(local (defthm member-remove-diff-member
         (implies (and (not (equal a b))
                       (member-equal a x))
                  (member-equal a (remove b x)))))
(local (defthm subsetp-remove
         (implies (subsetp x y)
                  (subsetp (remove a x)
                           (remove a y)))
         :hints (("Subgoal *1/5" :use (:instance member-remove-diff-member (a (car x)) (b a) (x y))))))
(local (defthm card-remove-nonmember
         (implies (not (member-equal a x))
                  (equal (card (remove a x))
                         (card x)))))
(local (defthm card-remove-member
         (implies (member-equal a x)
                  (equal (card (remove a x))
                         (1- (card x))))))
(local (defthmd subsetp-implies-member
         (implies (and (consp x)
                       (subsetp x y))
                  (member-equal (car x) y))))
(local (defthm equal-cards-imply-same-members
         (implies (and (equal (card x) (card y))
                       (setp x) (setp y)
                       (subsetp x y)
                       (member-equal a y))
                  (member-equal a x))
         :hints (("Goal" :induct (set-recursion-scheme x y))
                 ("Subgoal *1/2" :use (:instance subsetp-implies-member)))))
(local (defthm card-subset
         (implies (and (setp x) (setp y)
                       (subsetp x y))
                  (<= (card x) (card y)))
         :hints (("Subgoal *1/4" :use (:instance equal-cards-imply-same-members
                                       (a (car x)) (x (cdr x)))))))
(local (defthm nodups-len=card
         (implies (no-duplicatesp-equal x)
                  (equal (len x) (card x)))))
(local (defthm nodups-list=set
         (implies (no-duplicatesp-equal x)
                  (setp x))
         :rule-classes :type-prescription))
(defthm len-nodup-subset
  (implies (and (no-duplicatesp-equal x)
                (no-duplicatesp-equal y)
                (subsetp x y))
           (<= (len x) (len y))))
