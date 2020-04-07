(in-package "ACL2")

(include-book "std/lists/repeat" :dir :system)
(include-book "std/lists/sets" :dir :system)

(defthmd
  what-it-means-when-remove-yields-nil
  (iff (consp (remove-equal x l))
       (not (equal (true-list-fix l)
                   (make-list (len l)
                              :initial-element x))))
  :hints (("goal" :in-theory (enable true-list-fix repeat)
           :induct t)))

(thm
  ;; what-that-thing-with-remove-means
  (implies
   (and
    (true-listp l)
    (equal (append (remove-equal x l) y) l))
   (equal y (make-list (- (len l) (len (remove-equal x l)))
                       :initial-element x)))
  :hints
  (("Subgoal *1/2.2'" :expand
    (APPEND (REMOVE-EQUAL (CAR L) (CDR L))
            Y))
   ("Subgoal *1/2.2.2'" :in-theory (disable
                                    (:REWRITE MEMBER-OF-REMOVE))
    :use (:instance
          (:REWRITE MEMBER-OF-REMOVE)
          (X (CDR L)) (B (CAR L)) (A (CAR L))))
   ("Subgoal *1/2.2.1'" :in-theory (enable repeat what-it-means-when-remove-yields-nil))
   ("Subgoal *1/2.1'" :expand
    ((append (remove-equal (car l) (cdr l))
             (repeat (+ (len (cdr l))
                        (- (len (remove-equal (car l) (cdr l)))))
                     (car l)))
     (REPEAT (+ 1 (LEN (CDR L))) (CAR L))))
   ("Subgoal *1/2.1.2'" :in-theory (disable
                                    (:REWRITE MEMBER-OF-REMOVE))
    :use (:instance
          (:REWRITE MEMBER-OF-REMOVE)
          (X (CDR L)) (B (CAR L)) (A (CAR L))))
   ("Subgoal *1/2.1.1'"
    :in-theory (disable
                (:REWRITE LEN-OF-REPEAT))
    :use (:instance
          (:REWRITE LEN-OF-REPEAT)
          (X (CAR L)) (N (LEN (CDR L)))))))
