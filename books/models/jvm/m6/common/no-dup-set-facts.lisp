;;  ----- Basic Set Theory Stuff ----
#|
(certify-book "no-dup-set-facts" 0)
|#
;; Sun Dec 21 22:06:19 2003
;; 
;; This books contains set of lemmas about set-differences. 
;; 


(in-package "ACL2")

(defconst *no-dup-set-facts-basic-functions* 
  '(mem notMem subset del app set-diff set-equal nodup-set))

;; This set of functions are defined in ACL2 package. 
;; some function are used in typechecker.lisp

;----------------------------------------------------------

;----------------------------------------------------
(acl2::set-verify-guards-eagerness 2)


(defun mem (c cl)
  (if (not (consp cl))
      nil
    (or (equal (car cl) c)
        (mem c (cdr cl)))))

(defun notMem (c cl)
  (not (mem c cl)))

(defun subset (s1 s2)
  (if (not (consp s1))
      t
    (and (mem (car s1) s2)
         (subset (cdr s1) s2))))

(defun del (a y)
  (if (not (consp y))
      nil
    (if (equal (car y) a)
        (cdr y)
      (cons (car y) (del a (cdr y))))))

(defun app (a b)
  (if (not (consp a))
      b
    (cons (car a) (app (cdr a) b))))

;------------------------------------------------------

(acl2::set-verify-guards-eagerness 1)

(defun set-diff (total seen) ;; *14* 
  (declare (xargs :guard (and (true-listp total)
                              (true-listp seen))))
  (if (endp total)
      nil
    (if (mem (car total) seen)
        (set-diff (cdr total) seen)
      (cons (car total) (set-diff (cdr total) (cons (car total) seen))))))

;; *14* Note: 
;;       Set-Diff returns a non-duplicated list that represent
;;       the set

;; some work  Set Theory stuff
;; mainly about set-diff, nodup-set, the size of the nodup-set
;;
;; this is used for proving termination of class superclass resolution

;; Originally. I did somework with permuation. 
;; Later found out Set-equal + Non-Dup suffice.



(defun set-equal (a b)
  (declare (xargs :guard (and (true-listp a)
                              (true-listp b))))
  (and (subset a b)
       (subset b a)))



;(set-match-free-error nil)


(defthm subset-cons 
  (implies (subset a b)
           (subset a (cons x b))))

(defthm subset-reflexive 
  (subset x x))


(defthm mem-subset
   (implies (and (mem x a)
                 (subset a b))
            (mem x b)))

(defthm subset-transitive 
  (implies (and (subset a b)
                (subset b c))
           (subset a c)))


(defthm set-equal-transitive
  (implies (and (set-equal a b)
                (set-equal b c))
           (set-equal a c)))

(defequiv set-equal)

(defcong set-equal equal (mem x s) 2
  :hints (("Subgoal *1/4" :cases ((mem x (cdr s))))
          ("Subgoal *1/4.2" 
           :use (:instance mem-subset  (a acl2::s-equiv) (b s))
           :in-theory (disable mem-subset))))

(defthm set-equal-cons
  (implies (set-equal a b)
           (set-equal (cons x a) (cons x b))))


(defthm set-equal-mem-cons-2
  (implies (mem x l)
           (set-equal (cons x l) l)))
                                             
(in-theory (disable set-equal))


(defun set-diff-cong-induct (s s-equiv total)
  (if (endp total)
      (cons s s-equiv)
    (if (mem (car total) s)
          (set-diff-cong-induct s s-equiv (cdr total))
      (set-diff-cong-induct (cons (car total) s) (cons (car total) s-equiv) (cdr total)))))


(defthm set-equal-cons-f
  (implies (not (set-equal (cons x a) (cons x b)))
           (not (set-equal a b)))
  :hints (("Goal" :in-theory (enable set-equal)))
  :rule-classes :forward-chaining)

(defcong set-equal equal (set-diff total acl2::seen) 2
  :hints (("Goal" :in-theory (disable set-equal-cons)
           :induct (set-diff-cong-induct acl2::seen acl2::seen-equiv total))))


(defun subset-set-diff-induct (total a b)
  (if (endp total)
      (cons a b)
    (subset-set-diff-induct (cdr total) (cons (car total) a) (cons (car total) b)))) 
  

(defthm subset-set-diff
  (implies (subset a b) 
           (subset (set-diff total b) (set-diff total a)))
  :hints (("Goal" :induct (subset-set-diff-induct total a b))))


;;-------------------------------------------------------------------- 

; ---- nodup-set ----- 

(defun nodup-set (s)
  (declare (xargs :guard (true-listp s)))
  (if (endp s)
      t
    (and (not (mem (car s) (cdr s)))
         (nodup-set (cdr s)))))


(defthm mem-set-diff
  (implies (mem a seen)
           (not (mem a (set-diff total seen)))))


(defthm set-diff-is-a-nodup-set
  (nodup-set (set-diff total seen))
  :rule-classes :type-prescription)


(defun subset-nodup-set-size-induct (s1 s2)
  (if (endp s1)
      s2
    (subset-nodup-set-size-induct (cdr s1) (del (car s1) s2))))

(defthm del-set-len
  (implies (mem x s)
           (equal (len s)  (+ 1 (len (del x s))))))     

(defthm mem-del 
  (implies (not (equal a b))
           (equal (mem a (del b x))
                  (mem a x))))
           
(defthm del-nodups
  (implies (nodup-set s)
           (nodup-set (del x s))))


(defthm del-nodup-set-subset
  (implies (and (subset (cons x s1) s2)
                (nodup-set (cons x s1)))
           (subset s1 (del x s2))))

; --- to talk about termination, we talk about the number of unseen
; --- classes decrease.


(defthm subset-nodup-set-size
  (implies (and (subset s1 s2)
                (nodup-set s1)
                (nodup-set s2))
           (<= (len s1) (len s2)))
  :hints (("Goal" :induct (subset-nodup-set-size-induct s1 s2)))
  :rule-classes :linear)


(defun len-set-equal-nodup-set-x-induct (s1 s2)
  (if (endp s1)
      s2
    (len-set-equal-nodup-set-x-induct (cdr s1) (del (car s1) s2))))

(defthm  len-set-equal-nodup-set-x
  (implies (and (mem a s2)
                (not (mem a s1))
                (subset s1 s2)
                (nodup-set s1)
                (nodup-set s2))
           (< (len s1) (len s2)))
  :hints (("Goal" :induct (len-set-equal-nodup-set-x-induct s1 s2))))


(defthm mem-set-diff-x
  (implies (and (mem a total)
                (not (mem a seen)))
           (mem a (set-diff total seen))))

(defthm len-set-diff-mem
  (implies (and (not (mem a seen)) 
                (mem a total))
           (< (len (set-diff total (cons a seen)))
              (len (set-diff total seen))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance len-set-equal-nodup-set-x
                            (s1 (set-diff total (cons a seen)))
                            (s2 (set-diff total seen))))))
  :rule-classes :linear)
           
;; ----------- Above enough rules about set-diff -----------







