;------------------------------------------
;
; Author:  Diana Toma
; TIMA-VDS, Grenoble, France
; March 2003
; ACL2 formalization of SHAs
; General parsing and its application to SHAs
;------------------------------------------



(IN-PACKAGE "ACL2")

(include-book "padding-1-256")
(include-book "padding-384-512")

;---parsing

; parses the message m into blocks of n elements


(local
(defthm 2n<i
  (implies (and (integerp n) (< 0 n) (integerp i)
                (<  n i) (integerp (* i (/ n))) )
           (<= 2 (* i (/ n) )))))


(local
(defthm n<=i
  (implies (and (integerp n) (< 0 n) (integerp i)
                (equal (mod  i n) 0) (< 0 i) )
           (<= n i) )))


(defun parsing (m n)
 (if (and (integerp n)
            (<= 0 n)
            (true-listp m))
     (cond ((endp m) nil)
           ((zp n) nil)
           (t (cons (firstn n m) (parsing (nthcdr n m) n))))
     nil))

;ACL2 !>(parsing '(0 1 2 3 4 5 6 7) 3)
;((0 1 2) (3 4 5) (6 7))


(defthm true-listp-car-parsing
 (implies (and (true-listp l) (integerp n) (<= 0 n))
     (true-listp (car (parsing l n)) )))



(defthm bvp-car-parsing
 (implies (and (bvp l) (integerp n) (<= 0 n))
     (bvp (car (parsing l n)) )))


(local
(defthm len-consp-nthcdr
  (implies (and (integerp n) (< 0 n) (true-listp l)(consp (nthcdr n l)))
           (< n (len  l)))))


(defthm car-parsing
 (implies (and (true-listp l) (integerp n) (<= 0 n))
     (equal (car (parsing l n)) (firstn n l))))


(defthm parsing-right-len
   (implies (and (true-listp l) (integerp n) (< 0 n)
            (equal (mod (len l) n) 0))
            (el-of-eq-len (parsing l n)))
:hints
(("goal"
  :do-not '(generalize)
  :induct (rec-by-subn n l ))
("subgoal *1/1.4''"
  :use (len-consp-nthcdr (:instance 2n<i (n n) (i (len l)))))))


(defthm len-car-parsing
 (implies (and (true-listp l) (integerp n) (< 0 n)
            (<= n (len l)))
            (equal (len (car (parsing  l n)))  n)))


(defthm wordp-car-parsing
  (implies (and (bvp l) (integerp n) (< 0 n) (<= n (len l) ))
         (wordp (car (parsing l n) ) n)))


(defthm wvp-parsing
  (implies (and (bvp m) (equal (mod (len m) n) 0) (integerp n) (< 0 n))
          (wvp (parsing  m n) n))
:hints (("subgoal *1/5" :use (:instance n<=i (i (len m) )))))


(defthm len-parsing
  (implies (and (true-listp m) (equal (mod (len m) n) 0)
                (integerp n) (< 0 n))
          (equal (len (parsing  m n)) (/ (len m) n)))
:hints (("subgoal *1/5" :use (:instance n<=i (i (len m) )))))


(defthm parsing-512-is-good
(implies (and (bvp m)
              (< (len m) (expt 2 64)))
       (and (el-of-eq-len (parsing (padding-1-256 m) 512))
             (equal (len (car (parsing (padding-1-256 m) 512))) 512)))
:hints
(("goal"
  :use ((:instance parsing-right-len (l (padding-1-256 m)) (n 512)  )
        len-padding-1-256-mod-512=0)
  :in-theory (disable el-of-eq-len parsing padding-1-256 ))
("subgoal 1" :use len-padding-1-256 )))


(defthm wvp-parsing-512
  (implies (and (bvp m)
              (< (len m) (expt 2 64)))
           (wvp (parsing (padding-1-256 m) 512) 512))
:hints
(("goal"
  :use ( len-padding-1-256-mod-512=0)
  :in-theory (disable mod  parsing padding-1-256 ))))


(defthm len-parsing-512
  (implies (and (bvp m)
              (< (len m) (expt 2 64)))
          (<= 1 (len (parsing (padding-1-256 m) 512))))
:hints
(("goal"
  :use ( len-padding-1-256-mod-512=0
       (:instance len-parsing (m (padding-1-256 m)) (n 512))
        len-padding-1-256 )
  :in-theory (disable  parsing padding-1-256 len ))))



(defthm parsing-1024-is-good
(implies (and (bvp m)
              (< (len m) (expt 2 128)))
      (and   (el-of-eq-len (parsing (padding-512 m) 1024))
        (equal (len (car (parsing (padding-512 m) 1024))) 1024 )))
:hints
(("goal"
  :use ((:instance parsing-right-len (l (padding-512 m)) (n 1024)  )
        len-padding-512-mod-1024=0)
  :in-theory (disable el-of-eq-len parsing padding-512 ))
("subgoal 1" :use len-padding-512 )))


(defthm wvp-parsing-1024
  (implies (and (bvp m)
              (< (len m) (expt 2 128)))
           (wvp (parsing (padding-512 m) 1024) 1024))
:hints
(("goal"
  :use ( len-padding-512-mod-1024=0)
  :in-theory (disable mod  parsing padding-512 ))))

