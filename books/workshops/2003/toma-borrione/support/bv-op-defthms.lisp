;------------------------------------------
;
; Author:  Diana Toma
; TIMA-VDS, Grenoble, France
; March 2003
; ACL2 formalization of bit-vectors as lists
; Theorems of bit-vectors operations
;------------------------------------------


(in-package "ACL2")


(include-book "bv-op-defuns")

; theorems on bvp

(defthm bvp-true-listp
  (implies  (bvp l) (true-listp l)))

(defthm bvp-append
  (implies (and  (bvp l) (bvp l1))
           (bvp (append l l1))))

(defthm revappend-is-bvp
 (implies (and (bvp i)(bvp j))
          (bvp (revappend i j))))

(defthm reverse-is-bvp
 (implies (bvp i) (bvp (reverse i))))

(defthm bvp-make-list-0
     (bvp (make-list n :initial-element 0 )))

(defthm bvp-make-list-ac-0
     (bvp (make-list-ac n  0 nil )))

(defthm bvp-make-list-ac-1
     (bvp (make-list-ac n  1 nil )))

(defthm bvp-firstn
(implies (bvp l) (bvp (firstn n l))))

(defthm bvp-nthcdr
(implies (bvp l) (bvp (nthcdr n l))))

; theorems on wvp

(defthm wvp-append
(implies (and (wvp m w) (wordp l w))
   (wvp (append m (list l)) w))
:hints (("goal" :induct (wvp m w) )))


;(SET-MATCH-FREE-ERROR NIL)

(defthm nth-wvp
   (implies  (and  (integerp j) (<= 0 j)   (wvp m i))
             (bvp (nth j  m )) ))

(defthm len-nth-wvp
   (implies  (and  (integerp j) (<= 0 j)
                   (wvp m i) (< j (len m) ))
            (equal  (len (nth j  m )) i)))


(defthm len-car-wvp
   (implies (and  (wvp m i) (not (endp m)))
            (equal  (len ( car  m )) i)))

;(SET-MATCH-FREE-ERROR t)

(defthm wordp-nth
  (implies  (and  (integerp j) (<= 0 j)
                  (< j (len m) ) (wvp m i))
            (wordp (nth j m) i)))


;theorems on bit-vector <-> integer conversions

(defthm integerp-bv-int-little-endian
  (implies (bvp v)
       (and (integerp (bv-int-little-endian v))
            (<= 0 (bv-int-little-endian v)))))


(defthm integerp-bv-int-big-endian
  (implies (bvp v)
       (and (integerp (bv-int-big-endian v))
            (<= 0 (bv-int-big-endian v)))))


(defthm int-bv-little-endian-is-bvp
 (implies (and (integerp i)(<= 0 i))
          (bvp (int-bv-little-endian i))))


(defthm len-bv-int-little-endian
  (implies (and (bvp m))
      (<= (bv-int-little-endian m)
          (- (expt 2 (len m)) 1))))


(local
(defthm len-bv-int-little-endian-reverse
  (implies (and (bvp m))
      (<= (bv-int-little-endian (reverse m))
          (- (expt 2 (len (reverse m))) 1)))
 :hints (("Goal" :in-theory (disable  len-reverse reverse  )))))


(defthm len-int-bv-little-endian-max
  (implies (and (integerp i)(<= 0 i) )
           (< i (expt 2 (len (int-bv-little-endian  i))))))


(defthm len-int-bv-little-endian-min
  (implies (and (integerp i)(< 1 i) )
           (<= (expt 2 ( - (len (int-bv-little-endian  i)) 1)) i)))


(defthm len-int-bv-little-endian-2y-1
  (implies (and  (integerp y)(< 0 y) )
           (equal (len (int-bv-little-endian  (- (expt 2 y) 1) )) y )))


(local
(defthm len-int-bv-little-endian-1-aux
(IMPLIES (AND  (INTEGERP l) (< 0 l))
         (<= (LEN (INT-BV-little-endian l ))
             (LEN (INT-BV-little-endian (+ 1 l)))))))

(local
(defthm len-int-bv-little-endian-1
(IMPLIES (AND  (INTEGERP l) (<= 0 l))
         (<= (LEN (INT-BV-little-endian l ))
             (LEN (INT-BV-little-endian (+ 1 l)))))
:hints
((  "goal"
  :do-not-induct t
  :use (len-int-bv-little-endian-1-aux)
  :in-theory (disable  int-bv-little-endian )))))



(local
(defthm len-int-bv-little-endian-k+1
(IMPLIES (AND (INTEGERP K) (INTEGERP I)
              (<= K I)  (<= 1 K))
         (<= (LEN (INT-BV-little-endian (+  I (- K))))
             (LEN (INT-BV-little-endian (+ 1 I (- K))))))))


(local
(defthm interm
(IMPLIES (AND  (<= (LEN (INT-BV-little-endian (+ 1 I (- K))))
               (LEN (INT-BV-little-endian I)))
               (<= (LEN (INT-BV-little-endian (+  I (- K))))
               (LEN (INT-BV-little-endian (+ 1 I (- K))))))
 (<= (LEN (INT-BV-little-endian (+ I (- K))))
     (LEN (INT-BV-little-endian I))))))


(defthm len-int-bv-little-endian-k
(IMPLIES (AND  (INTEGERP I) (INTEGERP k)
              (<= k I) (<= 0 k))
         (<= (LEN (INT-BV-little-endian (- I k)))
             (LEN (INT-BV-little-endian  i))))
:hints
(("goal"
  :do-not '(generalize)
  :induct (rec-by-sub1 k)
  :in-theory (disable int-bv-little-endian ))))


(defthm len-int-bv-little-endian-i<=j
  (implies (and  (integerp i)(<= 0 i) (integerp j)(<= 0 j) (<= i j) )
       (<= (len (int-bv-little-endian i))
           (len (int-bv-little-endian j))  ))
:hints
(("goal"
  :use (:instance len-int-bv-little-endian-k ( i j) (k (- j i)))
  :in-theory (disable int-bv-little-endian  ))))


(defthm len-int-bv-little-endian-i<=2y-1
  (implies (and (integerp i)(<= 0 i) (<= i (- (expt 2 y) 1))
                (integerp y)(< 0 y) )
          (<= (len (int-bv-little-endian  i)) y ))
:hints
(("goal"
  :use ((:instance  len-int-bv-little-endian-i<=j (i i) (j (- (expt 2 y) 1)))
        len-int-bv-little-endian-2y-1)
  :do-not-induct t
  :in-theory (disable int-bv-little-endian))))


(defthm int-bv-big-endian-is-bvp
 (implies (and (integerp i)(<= 0 i))
          (bvp (int-bv-big-endian i))))


(defthm len-bv-int-big-endian
  (implies  (bvp m)
      (<= (bv-int-big-endian m) (- (expt 2 (len m)) 1)))
:hints
(("goal'"
  :do-not-induct t
  :use (len-bv-int-little-endian-reverse )
  :in-theory (disable  reverse ))))


(defthm len-int-bv-big-endian-max
  (implies (and (integerp i)(<= 0 i) )
      (< i (expt 2  (len (int-bv-big-endian  i))))))


(defthm len-int-bv-big-endian-min
  (implies (and (integerp i)(< 1 i) )
           (<= (expt 2 (- (len (int-bv-big-endian i)) 1)) i)))


(defthm len-int-bv-big-endian-2y-1
  (implies (and  (integerp y)(< 0 y) )
           (equal (len (int-bv-big-endian  (- (expt 2 y) 1) )) y )))


(defthm len-int-bv-big-endian-i<=j
  (implies (and  (integerp i)(<= 0 i) (integerp j)(<= 0 j) (<= i j) )
       (<= (len (int-bv-big-endian i)) (len (int-bv-big-endian j))  ))
:hints
(("goal"
  :in-theory (disable int-bv-little-endian  ))))


(defthm len-int-bv-big-endian-i<=2y-1
  (implies (and (integerp i)(<= 0 i) (<= i  (- (expt 2 y) 1))
               (integerp y)(< 0 y) )
          (<= (len (int-bv-big-endian  i)) y ))
:hints
(("goal"
  :do-not-induct t
  :in-theory (disable int-bv-little-endian ))))


(defthm bv-int-int-bv-i=i-little-endian
  (IMPLIES (AND  (INTEGERP I)  (<= 0 I))
         (EQUAL (BV-INT-LITTLE-ENDIAN  (INT-BV-LITTLE-ENDIAN I)) i)))


(defthm bv-int-int-bv-i=i-big-endian
  (IMPLIES (AND  (INTEGERP I) (<= 0 I))
         (EQUAL (BV-INT-big-ENDIAN  (INT-BV-big-ENDIAN I)) i)))


(local
(defthm bv-int-app-little-endian-base
(IMPLIES (AND  (INTEGERP I) (<= 0 I))
         (EQUAL (BV-INT-LITTLE-ENDIAN (APPEND (INT-BV-LITTLE-ENDIAN I)
                                              (list 0)))
                (BV-INT-LITTLE-ENDIAN (INT-BV-LITTLE-ENDIAN I))))))


(local
(defthm bv-int-app-little-endian
(IMPLIES  (bvp m)
         (EQUAL (BV-INT-LITTLE-ENDIAN (APPEND m   (list 0)))
                (BV-INT-LITTLE-ENDIAN  m )))))


(local
(defthm aux-append-m1-m2
(IMPLIES (AND (TRUE-LISTP MLAC)
              (TRUE-LISTP IBLEN))
         (EQUAL (BV-INT-LITTLE-ENDIAN (APPEND IBLEN MLAC '(0)))
                (BV-INT-LITTLE-ENDIAN (APPEND IBLEN MLAC))))))


(local
(defthm n+1-make-list
(implies (and (INTEGERP N) (<= 1 N))
 (equal  (make-list n :initial-element k )
        (append (make-list (- n 1) :initial-element k ) (list k))))))


(local
(defthm bv-int-app-int-bv-little-endian-simplif1
(IMPLIES (AND (integerp i) (<= 0 i) (integerp n) (<= 0 n))
 (EQUAL (BV-INT-LITTLE-ENDIAN (APPEND (INT-BV-LITTLE-ENDIAN  i)
                                      (MAKE-LIST n :initial-element 0)))
        (BV-INT-LITTLE-ENDIAN (INT-BV-LITTLE-ENDIAN i))))
:hints ((  "goal" :induct (rec-by-sub1 n)))))


(defthm  bv-int-app-int-bv-little-endian
  (IMPLIES (AND (integerp i) (<= 0 i) (integerp n) (<= 0 n))
           (EQUAL (BV-INT-little-ENDIAN (APPEND (INT-BV-little-ENDIAN i)
                                          (MAKE-LIST n  :initial-element 0)))
           i)))


(defthm  bv-int-app-int-bv-big-endian
  (IMPLIES (AND (integerp i) (<= 0 i) (integerp n) (<= 0 n))
           (EQUAL (BV-INT-BIG-ENDIAN (APPEND (MAKE-LIST n  :initial-element 0)
                                       (INT-BV-BIG-ENDIAN i)))
           i)))

;theorems on bv-to-n

(defthm bvp-bv-to-n
   (implies (and (bvp v) (integerp n) (<= 0 n))
            (bvp (bv-to-n v n))))

(defthm len-bv-to-n
   (implies (and (bvp v) (integerp n) (<= 0 n))
            (equal (len (bv-to-n v n)) n)))

(defthm wordp-bv-to-n
   (implies (and (bvp v) (integerp n) (<= 0 n))
            (wordp (bv-to-n v n) n))
:hints
(("goal"
  :use (bvp-bv-to-n len-bv-to-n) )))

;theorems on bv-and

(defthm comutativity-of-bv-a
  (equal (bv-a x y) (bv-a y x)))


(defthm bv-a-is-bvp
  (bvp (bv-a x y)))


(defthm len-bv-a
 (implies (and (bvp x) (bvp y)  (EQUAL (LEN X) (len y)))
      (and   (equal (len (bv-a x y)) (len x) )
             (equal (len (bv-a x y)) (len y)))))


(defthm wordp-bv-a
 (implies (and (bvp x) (bvp y)(EQUAL (LEN X) (len y) ))
         (and (wordp (bv-a x y) (len y))
              (wordp (bv-a x y) (len x))))
:hints (("goal" :use (len-bv-a bv-a-is-bvp))))


(defthm wordp-binary-bv-and-word
 (implies (and (wordp x w) (wordp y w)
               (integerp w) (<= 0 w))
   (wordp (binary-bv-and x y) w)))


(defthm comutativity-of-bv-and
  (equal (bv-and x y) (bv-and y x)))


(defthm bv-and-is-bvp
  (bvp (bv-and x y)))


(defthm len-bv-and
   (implies (and (bvp x) (bvp y))
            (equal (len (bv-and x y))
                   (if (<= (len x) (len y))
                       (len y)
                       (len x))))
:hints (("goal" :in-theory (disable  N+1-MAKE-LIST))))


(defthm wordp-bv-and
 (implies (and (bvp x) (bvp y))
          (wordp (bv-and x y) (if (<= (len x) (len y))
                                 (len y)
                                 (len x))))
:hints (("goal" :use (len-bv-and bv-and-is-bvp))))


;theorems on bv-or

(defthm comutativity-of-bv-o
  (equal (bv-o x y) (bv-o y x)))


(defthm bv-o-is-bvp
  (bvp (bv-o x y)))


(defthm len-bv-o
 (implies (and (bvp x) (bvp y)  (EQUAL (LEN X) (len y)))
      (and   (equal (len (bv-o x y)) (len x) )
              (equal (len (bv-o x y)) (len y)))))


(defthm wordp-bv-o
 (implies (and (bvp x) (bvp y)(EQUAL (LEN X) (len y) ))
         (and (wordp (bv-o x y) (len y))
              (wordp (bv-o x y) (len x))))
:hints (("goal" :use (len-bv-o bv-o-is-bvp))))


(defthm wordp-binary-bv-or-word
 (implies (and (wordp x w) (wordp y w)
                (integerp w) (<= 0 w))
   (wordp (binary-bv-or x y) w)))


(defthm comutativity-of-bv-or
  (equal (bv-or x y) (bv-or y x)))


(defthm bv-or-is-bvp
  (bvp (bv-or x y)))


(defthm len-bv-or
   (implies (and (bvp x) (bvp y))
            (equal (len (bv-or x y))
                   (if (<= (len x) (len y))
                       (len y)
                       (len x))))
:hints (("goal" :in-theory (disable  N+1-MAKE-LIST))))


(defthm wordp-bv-or
 (implies (and (bvp x) (bvp y))
          (wordp (bv-or x y) (if (<= (len x) (len y))
                                 (len y)
                                 (len x))))
:hints (("goal" :use (len-bv-or bv-or-is-bvp))))


;theorems on bv-xor

(defthm comutativity-of-bv-xo
  (equal (bv-xo x y) (bv-xo y x)))


(defthm bv-xo-is-bvp
  (bvp (bv-xo x y)))


(defthm len-bv-xo
 (implies (and (bvp x) (bvp y)  (EQUAL (LEN X) (len y)))
      (and   (equal (len (bv-xo x y)) (len x) )
              (equal (len (bv-xo x y)) (len y)))))


(defthm wordp-bv-xo
 (implies (and (bvp x) (bvp y)(EQUAL (LEN X) (len y) ))
         (and (wordp (bv-xo x y) (len y))
              (wordp (bv-xo x y) (len x))))
:hints (("goal" :use (len-bv-xo bv-xo-is-bvp))))


(defthm wordp-binary-bv-xor-word
 (implies (and (wordp x w) (wordp y w)
                (integerp w) (<= 0 w))
   (wordp (binary-bv-xor x y) w)))


(defthm comutativity-of-bv-xor
  (equal (bv-xor x y) (bv-xor y x)))


(defthm bv-xor-is-bvp
  (bvp (bv-xor x y)))


(defthm len-bv-xor
   (implies (and (bvp x) (bvp y))
            (equal (len (bv-xor x y))
                   (if (<= (len x) (len y))
                       (len y)
                       (len x))))
:hints (("goal" :in-theory (disable  N+1-MAKE-LIST ))))


(defthm wordp-bv-xor
 (implies (and (bvp x) (bvp y))
          (wordp (bv-xor x y) (if (<= (len x) (len y))
                                 (len y)
                                 (len x))))
:hints (("goal" :use (len-bv-xor bv-xor-is-bvp))))


;theorems on bv-not

(defthm bv-not-is-bvp
  (bvp (bv-not x)))


(defthm len-bv-not
   (implies (bvp x)
            (equal (len (bv-not x)) (len x))))


(defthm wordp-bv-not
 (implies  (bvp x)
          (wordp (bv-not x)  (len x))))


;theorems on plus

(local
(defthm aux
(implies (and (integerp i)(integerp j) (integerp z) (<= 0 i) (<= 0 j) (< 0 z))
         (and (<= 0 (mod (+ i j) z))  (integerp (mod (+ i j) z))))))


(local
(defthm aux1
(implies (and (bvp x) (<= 0 (bv-int-big-endian x))
           (<=  (bv-int-big-endian x) (expt 2 i))
           (bvp y) (<= 0 (bv-int-big-endian y))
           (<=  (bv-int-big-endian y) (expt 2 i))
           (integerp i) (<= 0 i))
(BVP (INT-BV-BIG-ENDIAN (MOD (+ (BV-INT-BIG-ENDIAN X)
                                                   (BV-INT-BIG-ENDIAN Y))
                                                (EXPT 2 I)))))
:hints
(("goal"
  :in-theory (disable int-bv-big-endian bv-int-big-endian)
  :use ((:instance integerp-BV-INT-BIG-ENDIAN (v x))
       (:instance integerp-BV-INT-BIG-ENDIAN (v y))
       (:instance int-bv-big-endian-is-bvp
                 (i (MOD (+ (BV-INT-BIG-ENDIAN X) (BV-INT-BIG-ENDIAN Y))
                             (EXPT 2 I))))) ))))


(defthm bvp-binary-plus
 (implies (and (bvp x) (<= 0 (bv-int-big-endian x))
               (<=  (bv-int-big-endian x) (expt 2 i))
               (bvp y) (<= 0 (bv-int-big-endian y))
               (<=  (bv-int-big-endian y) (expt 2 i))
               (integerp i) (<= 0 i))
          (bvp (binary-plus i x y)))
:hints (
("goal"
  :use (:instance bvp-bv-to-n
             (v (INT-BV-BIG-ENDIAN (MOD (+ (BV-INT-BIG-ENDIAN X)
                   (BV-INT-BIG-ENDIAN Y)) (EXPT 2 I)))) (n i))
  :in-theory (disable int-bv-big-endian bv-int-big-endian))))


(defthm len-binary-plus
 (implies (and (bvp x) (<= 0 (bv-int-big-endian x))
               (<=  (bv-int-big-endian x) (expt 2 i))
               (bvp y) (<= 0 (bv-int-big-endian y))
               (<=  (bv-int-big-endian y) (expt 2 i))
               (integerp i) (<= 0 i))
          (equal (len (binary-plus i x y)) i))
:hints
(("goal"
  :in-theory (disable int-bv-big-endian bv-int-big-endian))))


(defthm wordp-binary-plus
 (implies (and (bvp x) (<= 0 (bv-int-big-endian x))
               (<=  (bv-int-big-endian x) (expt 2 i))
               (bvp y) (<= 0 (bv-int-big-endian y))
               (<=  (bv-int-big-endian y) (expt 2 i))
               (integerp i) (<= 0 i))
          (wordp (binary-plus i x y) i))
:hints
(("goal"
  :in-theory (disable binary-plus int-bv-big-endian bv-int-big-endian))))


(defthm wordp-binary-plus-word
 (implies (and (wordp x w) (wordp y w)
                (integerp w) (<= 0 w))
          (wordp (binary-plus w x y) w))
:hints
(("goal"
   :use ((:instance  len-bv-int-big-endian (m x))
        (:instance  len-bv-int-big-endian (m y)))
   :in-theory (disable binary-plus ))))


;theorems on shift functions

(defthm bvp-<<
 (implies (and (wordp x w )
           (integerp n)
           (<= 0 n) (integerp w)
           (<= 0 w)
           (<= n w)) (bvp (<< x n w))))


(defthm len-<<
 (implies (and (wordp x w )
           (integerp n)
           (<= 0 n) (integerp w)
           (<= 0 w)
           (<= n w)) (equal (len (<< x n w)) w )))


(defthm wordp-<<
 (implies (and (wordp x w )
           (integerp n)
           (<= 0 n) (integerp w)
           (<= 0 w)
           (<= n w)) (wordp (<< x n w) w))
:hints (("goal" :use (bvp-<< len-<<))))


(defthm bvp->>
 (implies (and (wordp x w )
           (integerp n)
           (<= 0 n) (integerp w)
           (<= 0 w)
           (<= n w)) (bvp (>> x n w) )))


(defthm len->>
 (implies (and (wordp x w )
           (integerp n)
           (<= 0 n) (integerp w)
           (<= 0 w)
           (<= n w)) (equal (len (>> x n w)) w )))


(defthm wordp->>
 (implies (and (wordp x w )
           (integerp n)
           (<= 0 n) (integerp w)
           (<= 0 w)
           (<= n w)) (wordp (>> x n w) w))
:hints (("goal" :use (bvp->> len->>))))

(defthm wordp-shr
 (implies (and (wordp x w )
           (integerp n)
           (<= 0 n) (integerp w)
           (<= 0 w)
           (<= n w)) (wordp (shr n x w) w))
:hints (("goal" :in-theory (disable >> wordp))))

(defthm bvp-rotr
 (implies (and (wordp x w )
           (integerp n)
           (<= 0 n) (integerp w)
           (<= 0 w)
           (<= n w)) (bvp (rotr n x w) ))
:hints (("goal"
:in-theory (disable >> <<  binary-bv-or )
)))

(defthm len-rotr
 (implies (and (wordp x w )
           (integerp n)
           (<= 0 n) (integerp w)
           (<= 0 w)
           (<= n w)) (equal (len (rotr n x w) ) w))
:hints (("goal"
:in-theory (disable >> <<  binary-bv-or len wordp )
)))

(defthm wordp-rotr
 (implies (and (wordp x w )
           (integerp n)
           (<= 0 n) (integerp w)
           (<= 0 w)
           (<= n w)) (wordp (rotr n x w) w))
:hints (("goal"
:in-theory (disable  rotr len )
)))

(defthm bvp-rotl
 (implies (and (wordp x w )
           (integerp n)
           (<= 0 n) (integerp w)
           (<= 0 w)
           (<= n w)) (bvp (rotl n x w) ))
:hints (("goal"
:in-theory (disable >> <<  binary-bv-or )
)))

(defthm len-rotl
 (implies (and (wordp x w )
           (integerp n)
           (<= 0 n) (integerp w)
           (<= 0 w)
           (<= n w)) (equal (len (rotl n x w) ) w))
:hints (("goal"
:in-theory (disable >> <<  binary-bv-or len wordp )
)))

(defthm wordp-rotl
 (implies (and (wordp x w )
           (integerp n)
           (<= 0 n) (integerp w)
           (<= 0 w)
           (<= n w)) (wordp (rotl n x w) w))
:hints (("goal"
:in-theory (disable  rotl len )
)))


(defthm rotl->rotr
 (implies (and (wordp x w)
           (integerp n)
           (< 0 n)(integerp w)
           (<= 0 w)
           (<= n w))
         (equal (rotl n x w) (rotr (- w n) x w)))
)


(defthm rotr->rotl
 (implies (and (wordp x w)
           (integerp n)
           (<= 0 n)(integerp w)
           (<= 0 w)
           (<= n w))
         (equal (rotr n x w) (rotl (- w n) x w))))
