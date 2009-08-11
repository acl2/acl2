; Exercise 11.5

(in-package "ACL2")

; Start definitions from Chapter 10.

(defun in (a b)
  (cond ((atom b) nil)
        ((equal a (car b)) t)
        (t (in a (cdr b)))))

(defun del (a x)
  (cond ((atom x) nil)
        ((equal a (car x)) (cdr x))
        (t (cons (car x) (del a (cdr x))))))

(defun perm (x y)
  (cond ((atom x) (atom y))
        (t (and (in (car x) y)
                (perm (cdr x) (del (car x) y))))))

; End definitions from Chapter 10.

(local (defthm perm-reflexive
         (perm x x)))

(local
 (encapsulate
  ()

  ;; We can imagine that the following rule would loop with perm-symmetric, so
  ;; we make it local to this encapsulate.

  (local
   (defthm perm-del
     (implies (in a y)
              (equal (perm (del a y) x)
                     (perm y (cons a x))))
     ;; A hint is necessary.
     :hints (("Goal" :induct (perm y x)))))

  (defthm perm-symmetric
    (implies (perm x y) (perm y x)))))

; The following arises from an attempt to prove perm-implies-same-in, below.
(local (defthm in-del-implies-in
         (implies (in x (del a y))
                  (in x y))))

; The following is suggested by our first attempt to prove perm-transitive:
#|
Subgoal *1/5'4'
(IMPLIES (AND (NOT (IN X1 Z))
              (IN X1 Y)
              (PERM X2 (DEL X1 Y)))
         (NOT (PERM Y Z)))
|#
; We however state this in a form that omits the unnecessary perm hypothesis.
(local (defthm perm-implies-same-in
         (implies (and (not (in x1 z))
                       (in x1 y))
                  (not (perm y z)))))

; With the lemmas above, the attempt to prove perm-transitive leads to this
; simplification checkpoint.
#|
Subgoal *1/3'4'
(IMPLIES (AND (IN X1 Z)
              (NOT (PERM (DEL X1 Y) (DEL X1 Z)))
              (IN X1 Y)
              (PERM X2 (DEL X1 Y))
              (PERM Y Z))
         (PERM X2 (DEL X1 Z)))
|#
; The above goal suggests the lemma perm-del-del below.  But an attempt to
; prove perm-del-del leads to the following simplification checkpoint.

#|
Subgoal *1/4.1.2'
(IMPLIES (AND (CONSP Y)
              (EQUAL (PERM (CDR Y) (DEL (CAR Y) Z))
                     (PERM (DEL A (CDR Y))
                           (DEL A (DEL (CAR Y) Z))))
              (IN A (CDR Y))
              (IN A Z)
              (NOT (EQUAL A (CAR Y)))
              (IN (CAR Y) (DEL A Z)))
         (EQUAL (PERM (CDR Y) (DEL (CAR Y) Z))
                (PERM (DEL A (CDR Y))
                      (DEL (CAR Y) (DEL A Z)))))
|#

; So before proviing perm-del-del we prove the following, so that the equality
; hypothesis above will match the conclusion.

(local (defthm del-del
         (equal (del a (del b x))
                (del b (del a x)))))

; Now our attempt to prove perm-del-del leads to the following simplification
; checkpoint.

#|
Subgoal *1/4.1''
(IMPLIES (AND (CONSP Y)
              (IN (CAR Y) Z)
              (PERM (DEL A (CDR Y))
                    (DEL A (DEL (CAR Y) Z)))
              (IN A (CDR Y))
              (IN A Z)
              (NOT (EQUAL A (CAR Y)))
              (NOT (IN (CAR Y) (DEL A Z))))
         (NOT (PERM (CDR Y) (DEL (CAR Y) Z))))
|#

; Hence, we need the following relative of lemma in-del-implies-in above.

(local (defthm in-del
         (implies (not (equal a b))
                  (equal (in a (del b y))
                         (in a y)))))

(local (defthm perm-del-del
         (implies (and (in a y)
                       (in a z))
                  (equal (perm y z)
                         (perm (del a y) (del a z))))))

(local (defthm perm-transitive
         (implies (and (perm x y) (perm y z)) (perm x z))))

#| Use trans1 to print out the translation of (defequiv perm).
ACL2 !>:trans1 (defequiv perm)
 (DEFTHM PERM-IS-AN-EQUIVALENCE
         (AND (BOOLEANP (PERM X Y))
              (PERM X X)
              (IMPLIES (PERM X Y) (PERM Y X))
              (IMPLIES (AND (PERM X Y) (PERM Y Z))
                       (PERM X Z)))
         :RULE-CLASSES (:EQUIVALENCE))
ACL2 !>
|#

(defequiv perm)

