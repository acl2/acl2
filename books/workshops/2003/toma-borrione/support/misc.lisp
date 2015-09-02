;------------------------------------------
;
; Author:  Diana Toma
; TIMA-VDS, Grenoble, France
; March 2003
; ACL2 formalization of SHAs
; Some definitions on lists needed for the modelization of SHA
;------------------------------------------


(in-package "ACL2")

(include-book "../../../../arithmetic/equalities")
(include-book "../../../../arithmetic/inequalities")
(include-book "../../../../arithmetic-2/floor-mod/floor-mod")
(include-book "../../../../data-structures/list-defuns")
(include-book "../../../../data-structures/list-defthms")

; help for recursion in  theorem demonstration
(defun rec-by-sub1 (k)
(if (and (integerp k) (<= 1 k))  (rec-by-sub1 (- k 1)) t))

(defun rec-by-subn (n l)
 (if (and (integerp n) (< 0 n) (true-listp l) (not (endp l)))
    (rec-by-subn n (nthcdr n l)) t))

;gives the list of elements of l from the i-th position to  the j-th possition
(defun segment (i j l)
 (if (and (integerp i)
            (<= 0 i)(integerp j)
            (<= 0 j)
            (true-listp l))
  (firstn (- j i) (nthcdr i l))
  nil))

;ACL2 !>(segment  2 5 '( 0 1 2 3 4 5 6 7 8 9))
;(2 3 4)

;replace the nth element of l with x

(defun repl ( n x l)
     (if (and (integerp n)
            (<= 0 n)
            (true-listp l))
       (cond ((endp l) nil)
             ((zp n) (cons x (cdr l) ))
             (t  (cons (car l) (repl (- n 1) x (cdr l) ))))

        nil))

;ACL2 !>(repl 2 10 '( 0 1 2 3 4 5 6 7 8 9))
;(0 1 10 3 4 5 6 7 8 9)


;verifies if all elements of l are the same length

(defun el-of-eq-len (l)
 (if (true-listp l)
     (if (or (endp l) (endp (cdr l))) t
         (and (equal (len (car l)) (len  (cadr l)))
              (el-of-eq-len (cdr l))))
     nil))

;ACL2 !>( el-of-eq-len '((1 2) 0 ))
;NIL
;ACL2 !>( el-of-eq-len '((1 2) (0 3) ))
;T

; theorems for make-list

(DEFTHM BINARY-APPEND-make-list-ac
   (implies (consp b)
                      (EQUAL (BINARY-APPEND (make-list-ac i k B) C)
                             (make-list-ac i k (BINARY-APPEND B C)))))
(defthm append-make-list
(IMPLIES (AND (INTEGERP I) (<= 0 I))
         (EQUAL
                (make-list-ac I k (LIST K))
                (APPEND (make-list-ac I k NIL) (LIST K)))))

(defthm inverse-make-list
(implies (and (INTEGERP N) (<= 0 N))
 (equal (cons k (make-list n :initial-element k ))
        (append (make-list n :initial-element k ) (list k)))))

(local
(defthm n+1-make-list
(implies (and (INTEGERP N) (<= 1 N))
 (equal  (make-list n :initial-element k )
        (append (make-list (- n 1) :initial-element k ) (list k))))))

(defthm append-make-list-i-j
(IMPLIES (AND (INTEGERP i) (<= 0 i)(INTEGERP j) (<= 0 j))
         (EQUAL  (APPEND (MAKE-LIST i :initial-element k)
                         (make-list j :initial-element k))
                 (make-list (+ i j) :initial-element k ))))

(defthm revappend-make-list
(implies (and  (integerp n) (<= 0 n))
         (equal (REVAPPEND (MAKE-LIST n :initial-element k) nil)
                (make-list n :initial-element k )))
:hints ((  "goal" :induct (rec-by-sub1 n))
("Subgoal *1/1'" :use (:instance append-make-list-i-j (i (1- n)) (j 1)))))

(defthm len-app-make
(IMPLIES
     (AND (true-listP X)
          (true-listP Y)
          (<= (LEN Y) (LEN X)))
 (equal (len  (APPEND (MAKE-LIST-AC (+ (LEN X) (- (LEN Y)))  0 NIL) Y))
         (len x) )))


;theorems for segment
(defthm segment-append
  (implies (and (integerp k) (<= 0 k)(integerp j) (<= 0 j) (<= k j)
                (true-listp l1)  (true-listp l2) (<= (len l1) k) )
           (equal (segment k j (append l1 l2))
                  (segment  (- k (len l1))  (- j (len l1)) l2))))

(defthm segment-cons
 (implies (and (integerp j) (<= 0 j) (true-listp l2))
           (equal (segment 1 j (cons l1 l2)) (segment 0 (- j 1) l2))))


(defthm segment-0
 (implies (and (integerp j) (<= 0 j) (true-listp l))
           (equal (segment 0 j l) (firstn j l))))

;modified  SIMPLIFY-MOD-+-MOD from floor-mod book
 (DEFTHM SIMPLIFY-MOD-+-MOD1
                      (IMPLIES (AND
                                    (INTEGERP  (/ Y Z))
                                    (FM-GUARD (W X) (Y Z)))
                               (AND (EQUAL (MOD (+ W (MOD X Y)) Z)
                                           (MOD (+ W X) Z))
                                    (EQUAL (MOD (+ (MOD X Y) W) Z)
                                           (MOD (+ W X) Z))
                                    (EQUAL (MOD (+ W (- (MOD X Y))) Z)
                                           (MOD (+ W (- X)) Z))
                                    (EQUAL (MOD (+ (MOD X Y) (- W)) Z)
                                           (MOD (+ X (- W)) Z)))))
