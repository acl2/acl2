#|$ACL2s-Preamble$;
;;Author - Harsh Raju Chamarthi (harshrc)
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2S")

(include-book "defdata/top" :ttags :all)
(include-book "std/lists/top" :dir :system)
(include-book "std/alists/top" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

; I (Pete) went through the built-in functions and added
; signature rules where appropriate. This list is not complete
; for two reasons. First, there are some cases in which we fail
; due to the algorithm not being as general as it can be. See the
; acl2s-issues file. Second, I made one pass through the
; documentation of ACL2-built-ins. I should check again and I
; should check functions defined in the books we load 

(sig append ((listof :a) (listof :a)) => (listof :a))
(sig acl2::rev ((listof :a)) => (listof :a))
(sig nth (nat (listof :a)) => :a 
     :satisfies (< x1 (len x2)))
; PETE: I added and removed the sig below because it caused the
; theorem prover to get super slow.
;(sig car ((listof :a)) => :a :satisfies (consp x1)) ;new: check
(sig cons (:a (listof :a)) => (listof :a))
(sig acl2::fix-true-list ((listof :a)) => (listof :a))
(sig last ((listof :a)) => (listof :a))
(sig acl2::repeat (nat :a) => (listof :a)) ;renamed from replicate-fn
(sig make-list-ac (nat :a (listof :a)) => (listof :a))
(sig nthcdr (nat (listof :a)) => (listof :a))
(sig remove (all (listof :a)) => (listof :a))
(sig remove1-equal (all (listof :a)) => (listof :a))
(sig remove-duplicates ((listof :a)) => (listof :a))
(sig cdr ((listof :a)) => (listof :a))
(sig revappend ((listof :a) (listof :a)) => (listof :a))
(sig reverse ((listof :a)) => (listof :a))
(sig set-difference$ ((listof :a) (listof :a)) => (listof :a))
(sig first-n-ac (nat (listof :a) (listof :a)) => (listof :a)
     :satisfies (< x1 (len x2)))
(sig take (nat (listof :a)) => (listof :a)
     :satisfies (<= x1 (len x2))
     :hints (("Goal" :cases ((equal x1 (len x2))))))
(sig subseq-list ((listof :a) nat nat) => (listof :a)
     :satisfies (and (<= x3 (len x1)) (<= x2 x3)))
(sig subseq ((listof :a) nat nat) => (listof :a)
     :satisfies (and (<= x3 (len x1)) (<= x2 x3)))

(sig put-assoc-equal (:a :b (alistof :a :b)) => (alistof :a :b))
(sig pairlis$ ((listof :a) (listof :b)) => (alistof :a :b)
     :satisfies (= (len x1) (len x2)))
(sig update-nth (nat :a (listof :a)) => (listof :a) ;new: check
     :satisfies (<= x1 (len x3)))

(include-book "arithmetic-5/top" :dir :system)

(defthm natp-implies-acl2-numberp
  (implies (natp x)
           (acl2-numberp x))
  :rule-classes ((:rewrite)))

(defthm posp-implies-acl2-numberp
  (implies (posp x)
           (acl2-numberp x))
  :rule-classes ((:rewrite)))

(defthm integerp-implies-acl2-numberp
  (implies (integerp x)
           (acl2-numberp x))
  :rule-classes ((:rewrite)))

(defthm rationalp-implies-acl2-numberp2
  (implies (rationalp x)
           (acl2-numberp x))
  :rule-classes ((:rewrite)))

(defthm natp-implies-rationalp
  (implies (natp x)
           (rationalp x))
  :rule-classes ((:rewrite)))

(defthm posp-implies-rationalp
  (implies (posp x)
           (rationalp x))
  :rule-classes ((:rewrite)))

(defthm integerp-implies-rationalp
  (implies (integerp x)
           (rationalp x))
  :rule-classes ((:rewrite)))

(defthm numerator-1-decreases
  (implies (rationalp n) 
           (< (numerator (- n 1))
              (numerator n)))
  :hints (("goal" 
           :use ((:instance ACL2::|(* r (denominator r))| 
                  (acl2::r n))
                 (:instance ACL2::|(* r (denominator r))| 
                  (acl2::r (- n 1)))
                 )
           :in-theory (disable ACL2::|(* r (denominator r))|)))
  :rule-classes ((:linear) (:rewrite)))

(defun posp-ind (n)
  (if (or (zp n) (equal n 1))
    n
    (posp-ind (- n 1))))

(defthm numerator-n-decreases
  (implies (and (rationalp r)
                (<= n r)
                (integerp n)
                (< 0 n))
           (< (numerator (+ (- n) r))
                    (numerator r)))
  :hints (("goal" :induct (posp-ind n))
          ("subgoal *1/2.2" 
           :use ((:instance numerator-1-decreases 
                            (n (+ r (- n) 1))))))
  :rule-classes ((:linear) (:rewrite)))



