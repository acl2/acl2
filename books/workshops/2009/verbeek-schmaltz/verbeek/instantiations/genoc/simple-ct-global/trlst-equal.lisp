#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book "ordinals/lexicographic-ordering" :dir :system)
(include-book "../../../generic-modules/GeNoC-misc")

;; We define two lists of messages to be equal
;; if they have the same ids. Order doesn't matter.
;; Since a proof obligation states that the ids are
;; unique, only lists with the same number of messages
;; are unique.
(defun trlst-equal (x y)
  (and (subsetp (v-ids x) (v-ids y))
       (subsetp (v-ids y) (v-ids x))))
(defun member-v (v x)
  (member-equal (IdV v) (V-Ids x)))#|ACL2s-ToDo-Line|#




;; We'll proof trlst-equal is an equivalence relation
;; and proof some congruences concerning append and cons.
(defthm v-ids-append
  (equal (v-ids (append a b))
         (append (v-ids a) (v-ids b))))
(in-theory (disable v-ids-append))
(defthm append-v-ids-v-ids-append
  (equal (append (v-ids trlst1) (v-ids trlst2))
         (v-ids (append trlst1 trlst2))))
(defthm member-ids-append1
  (implies (member-equal id (V-Ids x))
           (member-equal id (V-Ids (append x y)))))
(defthm member-ids-append2
  (implies (member-equal id (V-Ids y))
           (member-equal id (V-Ids (append x y)))))
(defthm subsetp-v-ids-append1
  (implies (subsetp (v-ids x1) (v-ids x2))
           (subsetp (v-ids (append x1 y))
                    (v-ids (append x2 y)))))
(defthm subsetp-v-ids-append2
  (implies (subsetp (v-ids y1) (v-ids y2))
           (subsetp (v-ids (append x y1))
                    (v-ids (append x y2)))))
(defthm subsetp-implies-member-v
  (implies (and (subsetp (v-ids x) (v-ids y))
                (member-equal id (V-ids x)))
           (member-equal id (V-Ids y))))
(defthm member-equal-idv-v-ids
  (implies (member-equal v trlst)
           (member-equal (IdV v) (V-Ids trlst))))

(defequiv trlst-equal)
(defcong trlst-equal trlst-equal (cons v trlst) 2)
(defcong trlst-equal trlst-equal (append x y) 1)
(defcong trlst-equal trlst-equal (append x y) 2)
(defcong trlst-equal iff (member-v v x) 2)




(defthm commutativity-of-append2
  (trlst-equal (append x y) (append y x))
  :rule-classes :rewrite
  :otf-flg t)
(defthmd append3=append2+1
  (trlst-equal (append x y z) (append (append x y) z)))
(defthm commutativity-of-append3
  (trlst-equal (append x y z)
               (append y x z))
  :hints (("Goal" :in-theory (disable trlst-equal associativity-of-append)
                  :use ((:instance append3=append2+1)
                        (:instance append3=append2+1 (x y) (y x)))))
  :rule-classes :rewrite)

(defthm trlst-equal-totmissives
  (trlst-equal (totmissives trlst) trlst))
