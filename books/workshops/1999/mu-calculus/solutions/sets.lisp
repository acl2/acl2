(in-package "SETS")
(include-book "defung")
(include-book "meta")
(include-book "perm")

(defun in (a X)
  "Checks for set containment, i.e., is a in X?"
  (declare (xargs :guard (true-listp X)))
  (cond ((endp X) nil)
        ((equal a (car X)) t)
        (t (in a (cdr X)))))

(defun =< (X Y)
  "Subset, i.e., X =< Y"
  (declare (xargs :guard (and (true-listp X) (true-listp Y))))
  (cond ((endp X) t)
        (t (and (in (car X) Y)
                (=< (cdr X) Y)))))

(defun == (X Y)
  "Set equality, i.e., X == Y"
  (declare (xargs :guard (and (true-listp X) (true-listp Y))))
  (and (=< X Y)
       (=< Y X)))

(defung set-union (X Y)
"set union, i.e., X U Y"
  (declare (xargs :guard (true-listp X)))
  ((implies (true-listp Y) (true-listp (set-union X Y)))
   :rule-classes :type-prescription)
  (if (endp X)
      Y
    (cons (car X) (set-union (cdr X) Y))))

(defun intersect (X Y)
"Set intersection, i.e., X & Y"
  (declare (xargs :guard (and (true-listp X) (true-listp Y))))
  (cond ((endp X) nil)
        ((in (car X) Y)
         (cons (car X) (intersect (cdr X) Y)))
        (t (intersect (cdr X) Y))))

(defun minus (X Y)
"Set minus, i.e.,  X - Y"
  (declare (xargs :guard (and (true-listp X) (true-listp Y))))
  (cond ((endp X) nil)
        ((in (car X) Y)
         (minus (cdr X) Y))
        (t (cons (car X) (minus (cdr X) Y)))))

(defun set-complement (X U)
"complement set X, i.e., U - X"
  (declare (xargs :guard (and (true-listp X) (true-listp U))))
  (minus U X))

(defun remove-dups (X)
"Remove duplicates in X"
  (declare (xargs :guard (true-listp X)))
  (cond ((endp X) nil)
        ((in (car X) (cdr X))
         (remove-dups (cdr X)))
        (t (cons (car X)
                 (remove-dups (cdr X))))))

(defun cardinality (X)
"Cardinality of X, i.e., |X|"
  (declare (xargs :guard (true-listp X)))
  (len (remove-dups X)))

(defthm |X =< Y  =>  X =< ({a} U Y)|
  (implies (=< X Y)
           (=< X (cons a Y))))

(defthm |X =< X|
  (=< X X))

(defthm |X =< Y & Y =< Z  =>  X =< Z|
  (implies (and (=< X Y)
                (=< Y Z))
           (=< X Z))
  :rule-classes ((:rewrite)
                 (:forward-chaining :trigger-terms ((=< X Y) (=< Y Z)))))

; Exercise 1
(defequiv ==)

(defthm |X == Y  =>  X =< Y /\ Y =< X|
  (implies (== X Y)
           (and (=< X Y)
                (=< Y X)))
  :rule-classes :forward-chaining)

(defthm |a in X  =>  {a}uX == X|
  (implies (in a X)
           (== (cons a X) X)))

(defthm |{a}u({b} u X)  ==  {b}u({a} u X)|
  (== (cons a (cons b X))
      (cons b (cons a X))))

(defthm atom-==
  (implies (and (atom a)
                (atom b))
           (== a b))
  :rule-classes ((:forward-chaining :trigger-terms ((atom a) (atom b) (== a b)))))

(defthm |X == Y /\ ~(Y == Z)  =>  ~(X == Z)|
  (implies (and (== X Y)
                (not (== Y Z)))
           (not (== X Z)))
  :rule-classes ((:forward-chaining :trigger-terms ((== X Y) (== Y Z)))))

(defthm atom-consp-==
  (implies (and (atom a)
                (consp X))
           (not (== a X)))
  :rule-classes ((:forward-chaining :trigger-terms ((atom a) (consp X) (== a X)))))

(defthm |X =< Y  =>  a in X => a in Y|
  (implies (and (in a X)
                (not (in a Y)))
           (not (=< X Y)))
  :rule-classes ((:forward-chaining :trigger-terms ((in a X) (in a Y) (=< X Y)))))

; Exercise 2, part 1
(defcong == equal (in a X) 2
  :hints (("Goal"
           :use ((:instance |X =< Y  =>  a in X => a in Y|
                            (X x-equiv) (Y X))
                 (:instance |X =< Y  =>  a in X => a in Y|
                            (y x-equiv)))
           :in-theory (disable |X =< Y  =>  a in X => a in Y|))))

(defthm |X == X-equiv  iff  X =< Y /\ X-equiv =< Y|
  (implies (== X X-equiv)
           (iff (=< X Y)
                (=< X-equiv Y)))
  :rule-classes nil)

; Exercise 2, part 2
(defcong == equal (=< X Y) 1
  :hints (("goal"
           :use (:instance |X == X-equiv  iff  X =< Y /\ X-equiv =< Y|))))

; Exercise 2, part 3
(defcong == equal (=< X Y) 2)

; Exercise 2, part 4
(defcong == == (cons a Y) 2)

; Exercise 3, part 1
(defthm |a in X u Y  =  a in X \/ a in Y|
  (equal (in a (set-union X Y))
         (or (in a X)
             (in a Y))))

(defthm |X u {} == X|
  (== (set-union X nil) X))

(defthm |a in (X u {a} u Y)|
  (in a (set-union X (cons a Y))))

; Exercise 3, part 2
(defthm |X  =<  Y u X|
  (=< X (set-union Y X)))

(defthm |X  =<  X u Y|
  (=< X (set-union X Y)))

(defthm |X u Y  =<  X u {a} u Y|
  (=< (set-union X Y)
      (set-union X (cons a Y))))

(defthm |X u atom == X|
  (implies (atom a)
           (== (set-union X a) X)))

(defthm |X u ({a} u Y) ==  {a} u (X u Y)|
  (== (set-union X (cons a Y))
      (cons a (set-union X Y))))

(in-theory (disable ==))

; Exercise 3, part 3
(defthm |X u Y  == Y u X|
  (== (set-union X Y)
      (set-union Y X)))

(defthm |X =< Y  ==>  X u Y == Y|
  (implies (=< X Y)
           (== (set-union X Y) Y)))

; Exercise 3, part 4
(defthm |X u Y == Y  =  X =< Y|
  (equal (== (set-union X Y) Y)
         (=< X Y)))

(defcong == == (set-union X Y) 2)

; Exercise 3, part 5
(defcong == == (set-union X Y) 1
  :hints (("goal"
           :use ((:instance |X u Y  == Y u X|)
                 (:instance |X u Y  == Y u X| (x x-equiv))))))

; Exercise 3, part 6
(defthm |Y u Z =< X  =  Y =< X /\ Z =< X|
  (equal (=< (set-union Y Z) X)
         (and (=< Y X)
              (=< Z X))))

(defthm |X =< Y \/ X =< Z  ==>  X =< Y u Z|
  (implies (or (=< X Y)
               (=< X Z))
           (=< X (set-union Y Z))))

; Exercise 4, part 1
(defthm |a in X&Y  =  a in X  /\  a in Y|
  (equal (in a (intersect X Y))
         (and (in a X)
              (in a Y))))

(defthm |X & atom = {}|
  (implies (atom a)
           (equal (intersect X a) nil)))

(defthm |X & Y  =<  X & ({a} u Y)|
  (=< (intersect X Y)
      (intersect X (cons a Y))))

(defthm |X & Y =< Y & X|
  (=< (intersect X Y)
      (intersect Y X)))

; Exercise 4, part 2
(defthm |X & Y == Y & X|
  (== (intersect X Y)
      (intersect Y X))
  :hints (("goal" :in-theory (enable ==))))

; Exercise 4, part 3
(defthm |X =< Y  ==>  X & Y == X|
  (implies (=< X Y)
           (== (intersect X Y) X)))

; Exercise 4, part 4
(defthm |Y =< X \/ Z =< X  ==>  Y&Z =< X|
  (implies (or (=< Y X)
               (=< Z X))
           (=< (intersect Y Z) X)))

; Exercise 5, part 1
(defthm |X =< Y  ==>  X-Y == {}|
  (implies (=< X Y)
           (equal (minus X Y) nil)))

; Exercise 5, part 2
(defthm |X =< Y  ==>  X-Z =< Y|
  (implies (=< X Y)
           (=< (minus X Z) Y)))

(defun set-remove (a X)
"Removes a from X, i.e., X \ {a}"
  (declare (xargs :guard (true-listp X)))
  (cond ((endp X) nil)
        ((equal a (car X)) (set-remove a (cdr X)))
        (t (cons (car X) (set-remove a (cdr X))))))

(defthm set-remove-in
  (== (cons a (set-remove a X))
      (cons a X))
  :hints (("Goal" :in-theory (enable ==))))

(defun rem-dups (X)
  (declare (xargs :guard (true-listp X)))
  (if (consp X)
      (cons (car X)
            (rem-dups (set-remove (car X) (cdr X))))
    nil))

(defthm rem-dups-same-set
  (== (rem-dups X) X))

(defun rev (X)
  (declare (xargs :guard t))
  (if (consp X)
      (append (rev (cdr X)) (list (car X)))
    nil))

(defthm append-==-set-union
  (== (append X Y)
      (set-union X Y)))

(defthm |(rev X) == X|
  (== (rev X) X))

(defthm set-remove-from-end
  (equal (set-remove a (append X (list a)))
         (set-remove a X)))

(defthm set-remove-from-end2
  (implies (not (equal a b))
           (equal (set-remove a (append X (list b)))
                  (append (set-remove a X) (list b)))))

(defthm set-remove-car
  (implies (and (in a X)
                (not (in a (set-remove (car X) (cdr X)))))
           (equal (car X) a))
  :rule-classes nil)

(defthm in-rem-dups
  (implies (in a X)
           (equal (rem-dups (append X (list a)))
                  (rem-dups X)))
  :hints (("Subgoal *1/2.1"
           :expand (rem-dups (cons (car X)
                                   (append (cdr X) (list a)))))
          ("Subgoal *1/2.1'"
           :cases ((equal a (car X))))
          ("Subgoal *1/1.1"
           :expand (REM-DUPS (CONS (CAR X)
                                   (APPEND (CDR X) (LIST a)))))
          ("Subgoal *1/1.1'"
           :cases ((equal a (car X))))
          ("Subgoal *1/1.1.2'"
           :use ((:instance set-remove-car)))))

(defthm set-remove-in2
  (implies (not (in a X))
           (not (in a (set-remove b X)))))

(defthm not-in-rem-dups
  (implies (not (in a X))
           (equal (rem-dups (append X (list a)))
                  (append (rem-dups X) (list a)))))

(defthm rev-app
  (equal (rev (append X (list a)))
         (cons a (rev X))))

(defthm rev-remove-dups
  (equal (remove-dups X)
         (rev (rem-dups (rev X))))
  :hints (("Subgoal *1/1.2"
           :in-theory (disable in-rem-dups)
           :use ((:instance in-rem-dups (a (car X)) (X (rev (cdr X))))))
          ("Subgoal *1/1.1"
           :in-theory (disable not-in-rem-dups)
           :use ((:instance not-in-rem-dups (a (car X)) (X (rev (cdr X))))))))

(defthm =<-remove-el
 (=< (remove-el a X) X))

(encapsulate
 ()
 (local
  (defun ind-perm (X Y)
    (cond ((atom X) (cons X Y))
          (t (ind-perm (cdr X) (remove-el (car X) Y))))))

 (defthm perm-=<
   (implies (perm X Y)
            (=< X Y))
   :hints (("Goal"
            :induct (ind-perm x y)))
  :rule-classes :forward-chaining))

(defthm perm-is-symmetric
  (implies (perm X Y)
           (perm Y X))
  :rule-classes :forward-chaining)

; Exercise 6, part 2
(defrefinement perm ==
  :hints (("Goal"
           :in-theory (enable ==))))

(defthm rem-dups-open
  (equal (rem-dups (cons a X))
         (cons a (rem-dups (set-remove a X)))))

(defthm set-remove-swap
  (equal (set-remove b (set-remove a X))
         (set-remove a (set-remove b X))))

(defthm rem-dups-set-remove-in
  (not (in a (rem-dups (set-remove a X)))))

(defthm rem-dups-remove-el
  (equal (rem-dups (set-remove a X))
         (remove-el a (rem-dups X))))

(defthm in-set-remove
  (implies (and (in a X)
                (not (equal a b)))
           (in a (set-remove b X))))

(defthm set-remove-=<-
 (implies (=< X Y)
          (=< (set-remove a X)
              (set-remove a Y))))

(defcong == == (set-remove a X) 2
  :hints (("Goal" :in-theory (enable ==))))

; Since this function is used only to prove theorems, there is no
; point in verifying guards.
(defun ind-perm2 (X Y)
   (cond ((atom X) (cons X Y))
         (t (ind-perm2 (set-remove (car X) X) (set-remove (car X) Y)))))

(defcong == perm (rem-dups X) 1
  :hints (("Goal" :induct (ind-perm2 x x-equiv))
          ("Subgoal *1/2''"
           :expand ((REM-DUPS X) (rem-dups x-equiv)))
          ("Subgoal *1/2.4'" :in-theory (enable ==))
          ("Subgoal *1/1''" :in-theory (enable ==))))

(defthm perm-append
  (perm (append X nil) X))

(defthm perm-rev
 (perm (rev X) X))

(defthm perm-rem-dups-remove-dups
 (perm (remove-dups X) (rem-dups X)))

(defcong perm equal (len X) 1)

(defun =<-perm (X Y)
  (declare (xargs :guard (and (true-listp X) (true-listp Y))))
  (cond ((endp X) t)
        (t (and (in (car X) Y)
                (=<-perm (cdr X) (remove-el (car X) Y))))))

(defthm =<-perm-reflexive
  (=<-perm X X))

(defthm in-not-in-remove-el
  (implies (not (in a X))
           (not (in a (remove-el b X)))))

(defthm =<-perm-remove-el
  (implies (=<-perm X (remove-el a Y))
           (=<-perm X Y)))

(defthm =<-perm-=<
  (implies (=<-perm X Y) (=< X Y))
  :rule-classes :forward-chaining)

(defthm remove-el-not-in
  (implies (and (true-listp X)
                (not (in a X)))
           (equal (remove-el a X)
                  X)))

(defthm =<-perm-not-in
 (implies (and (in a X)
               (not (in a Y)))
          (not (=<-perm X Y))))

(defthm =<-perm-remove
  (implies (=<-perm X Y)
           (=<-perm (remove-el a X)
                    (remove-el a Y)))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((remove-el a X) (remove-el a Y)))))

(defthm =<-perm-transitive
  (implies (and (=<-perm X Y)
                (=<-perm Y Z))
           (=<-perm X Z)))

(defun no-dups (X)
  (declare (xargs :guard (true-listp X)))
  (cond ((endp X) t)
        (t (and (not (in (car X) (cdr X)))
                (no-dups (cdr X))))))

(defthm no-dups-rem-dups
  (no-dups (rem-dups X)))

(defthm =<-=<-perm-rem-dups
  (implies (=< X Y)
           (=<-perm (rem-dups X) (rem-dups Y)))
  :hints (("Goal" :induct (ind-perm2 x y))))

(defthm remove-el-len
  (implies (in a X)
           (equal (len (remove-el a X))
                  (- (len X) 1)))
  :rule-classes ((:linear) (:rewrite)))

(defthm =<-perm-len
  (implies (=<-perm X Y)
           (<= (len X) (len Y))))

(defthm =<-len-rem-dups
  (implies (=< X Y)
           (<= (len (rem-dups X)) (len (rem-dups Y))))
  :rule-classes ((:forward-chaining)
                 (:linear)))

(defthm perm-dups-==
  (implies (perm (rem-dups X) (rem-dups Y))
           (== X Y))
  :hints (("Goal"
           :use ((:instance rem-dups-same-set)
                 (:instance rem-dups-same-set (x y)))
           :in-theory (disable rem-dups-same-set)))
  :rule-classes :forward-chaining)

(defthm remove-el-set-remove2
  (implies (no-dups X)
           (perm (remove-el a X)
                 (set-remove a X))))

(defthm set-remove-thm
  (implies (no-dups X)
           (== (set-remove (car X) (cdr X))
               (cdr X)))
  :hints (("Goal"
           :use ((:instance remove-el-set-remove2 (a (car X))))
           :in-theory (disable remove-el-set-remove2))))

(defthm remove-el-no-dups
  (implies (no-dups X)
           (no-dups (remove-el Y X))))

(defthm no-dups-perm
  (implies (and (no-dups X)
                (no-dups Y)
                (== X Y))
           (perm X Y))
  :rule-classes nil)

(defthm =<-perm-len-perm2
  (implies (and (=<-perm X Y)
                (equal (len X)
                       (len Y)))
           (perm X Y))
  :rule-classes :forward-chaining)

(defun s< (X Y)
  (declare (xargs :guard (and (true-listp X) (true-listp Y))))
  (and (=< X Y) (not (=< Y X))))

(defthm s<-implies-<-len
  (implies (s< X Y)
           (< (len (rem-dups X))
              (len (rem-dups Y))))
  :hints (("goal'''"
           :use ((:instance =<-=<-perm-rem-dups))
           :in-theory (disable  =<-=<-perm-rem-dups)))
  :rule-classes ((:linear) (:forward-chaining :trigger-terms ((=< X Y) (== X Y)))))

; Exercise 7
(defthm s<-implies-<-len2
  (implies (s< X Y)
           (< (len (remove-dups X))
              (len (remove-dups Y))))
  :hints (("goal"
	   :use (:instance s<-implies-<-len)))
  :rule-classes nil)

(defthm subset-lens
  (implies (and (=< X Y)
		(equal (len (rem-dups X))
		       (len (rem-dups Y))))
	   (=< Y X))
  :hints (("goal"
	   :in-theory (disable s<-implies-<-len)
	   :use ((:instance s<-implies-<-len))))
  :rule-classes :forward-chaining)
