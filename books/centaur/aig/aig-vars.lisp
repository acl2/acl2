

(in-package "ACL2")

(include-book "base")
(include-book "centaur/misc/equal-sets" :dir :system)
(include-book "centaur/misc/alist-equiv" :dir :system)

(local (in-theory (disable sets::double-containment)))

;; Important for reasoning about AIG-VARS.
(defthm hons-set-equiv-hons-alphorder-merge-append
  (set-equivp (hons-alphorder-merge a b)
              (append a b))
  :hints ((set-reasoning)))


(defthm member-aig-vars-alist-vals
  (implies (not (member-equal v (aig-vars (alist-vals al))))
           (not (member-equal v (aig-vars (cdr (hons-assoc-equal x al)))))))


(defthm member-aig-vars-aig-and
  (implies (and (not (member-equal v (aig-vars x)))
                (not (member-equal v (aig-vars y))))
           (not (member-equal v (aig-vars (aig-and x y)))))
  :hints(("Goal" :in-theory (enable aig-and))))

(defthm aig-vars-aig-not
  (equal (aig-vars (aig-not x))
         (aig-vars x))
  :hints(("Goal" :in-theory (enable aig-not))))

(defthm member-aig-vars-aig-restrict
  (implies (and (not (and (member-equal v (aig-vars x))
                          (not (member-equal v (alist-keys al)))))
                (not (member-equal v (aig-vars (alist-vals al)))))
           (not (member-equal v (aig-vars (aig-restrict x al)))))
  :hints(("Goal" :in-theory (enable aig-restrict))))

(defthm aig-vars-cons
  (set-equivp (aig-vars (cons x y))
              (append (aig-vars x)
                      (aig-vars y))))

(defun strict-alphorder-sortedp (x)
  (if (or (atom x) (atom (cdr x)))
      t
    (and (alphorder (car x) (cadr x))
         (not (equal (car x) (cadr x)))
         (strict-alphorder-sortedp (cdr x)))))



(defthm strict-alphorder-sortedp-hons-alphorder-merge
  (implies (and (strict-alphorder-sortedp a)
                (strict-alphorder-sortedp b)
                (atom-listp a) (atom-listp b))
           (strict-alphorder-sortedp (hons-alphorder-merge a b)))
  :hints(("Goal" :in-theory
          (disable (:type-prescription alphorder)
                   (:type-prescription strict-alphorder-sortedp)
                   (:type-prescription hons-alphorder-merge)
                   (:type-prescription atom-listp)
                   default-car default-cdr
                   alphorder-transitive)
          :induct (hons-alphorder-merge a b))))
      
(defthm aig-vars-alphordered
  (strict-alphorder-sortedp (aig-vars x)))

(local (defthm nonmember-when-strict-alphorder-sorted
         (implies (and (strict-alphorder-sortedp x)
                       (atom-listp x)
                       (alphorder k (car x))
                       (not (equal k (car x)))
                       (atom k))
                  (not (member-equal k x)))))

(local (defun cdr-two-ind (a b)
         (if (atom a)
             b
           (and (consp b)
                (cdr-two-ind (cdr a) (cdr b))))))

(local (defexample set-equivp-silly-example1
         :pattern (set-equivp a b)
         :templates ((car a))
         :instance-rulename set-equivp-instancing))

(local (defexample set-equivp-silly-example2
         :pattern (set-equivp a b)
         :templates ((car b))
         :instance-rulename set-equivp-instancing))

(local (defthm not-consp-car-atom-listp
         (implies (atom-listp x)
                  (not (consp (Car x))))))

(local (defthm not-crossing-members-when-strict-alphorder-sorted
         (implies (and (atom-listp a)
                       (atom-listp b)
                       (strict-alphorder-sortedp a)
                       (strict-alphorder-sortedp b)
                       (member-equal (car a) (cdr b)))
                  (not (member-equal (car b) (cdr a))))
         :hints (("goal" :use ((:instance
                                nonmember-when-strict-alphorder-sorted
                                (k (car a)) (x (cdr b)))
                               (:instance
                                nonmember-when-strict-alphorder-sorted
                                (k (car b)) (x (cdr a))))
                  :in-theory (disable nonmember-when-strict-alphorder-sorted)
                  :do-not-induct t))))



(defthm equal-when-set-equiv-and-strict-alphorder-sorted
  (implies (and (set-equivp a b)
                (atom-listp a)
                (atom-listp b)
                (strict-alphorder-sortedp a)
                (strict-alphorder-sortedp b))
           (equal a b))
  :hints (("goal" :induct (cdr-two-ind a b)
           :in-theory (disable strict-alphorder-sortedp
                               default-cdr)
           :expand ((strict-alphorder-sortedp a)
                    (strict-alphorder-sortedp b))
           :do-not-induct t)
          (witness :ruleset (set-equivp-silly-example1
                             set-equivp-silly-example2
                             set-equivp-witnessing
                             set-equivp-member-template)))
  :rule-classes nil
  :otf-flg t)
