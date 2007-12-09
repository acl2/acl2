(in-package "ACL2")

(include-book "perm")

; ---------------------------------------------------------------------------
; Exercise 11.6

#|
ACL2 !>:trans1 (defcong perm perm (append x y) 1)
 (DEFTHM PERM-IMPLIES-PERM-APPEND-1
         (IMPLIES (PERM X X-EQUIV)
                  (PERM (APPEND X Y) (APPEND X-EQUIV Y)))
         :RULE-CLASSES (:CONGRUENCE))
ACL2 !>
|#

; ---------------------------------------------------------------------------
; Exercise 11.7

; An attempt to prove (defcong perm perm (append x y) 1) leads to the following
; simplification checkpoint, which leads us to lemma in-append below.

#|
Subgoal *1/3.2
(IMPLIES (AND (CONSP X)
              (PERM (APPEND (CDR X) Y)
                    (APPEND (DEL (CAR X) X-EQUIV) Y))
              (IN (CAR X) X-EQUIV)
              (PERM (CDR X) (DEL (CAR X) X-EQUIV)))
         (IN (CAR X) (APPEND X-EQUIV Y)))
|#

(defthm in-append
  (equal (in a (append x y))
         (or (in a x) (in a y))))

; The attempt to prove (defcong perm perm (append x y) 1) still fails, this
; time with the following simplification checkpoint.

#|
Subgoal *1/3''
(IMPLIES (AND (CONSP X)
              (PERM (APPEND (CDR X) Y)
                    (APPEND (DEL (CAR X) X-EQUIV) Y))
              (IN (CAR X) X-EQUIV)
              (PERM (CDR X) (DEL (CAR X) X-EQUIV)))
         (PERM (APPEND (CDR X) Y)
               (DEL (CAR X) (APPEND X-EQUIV Y))))
|#

; The following rewrite rule will allow the second hypothesis and the
; conclusion to match up.

(defthm del-append
  (equal (del a (append x y))
         (if (in a x)
             (append (del a x) y)
           (append x (del a y)))))

(defcong perm perm (append x y) 1)

(defcong perm perm (append x y) 2)
