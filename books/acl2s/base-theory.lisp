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

; Pete 9/14/2018: Useful for must-fail
(include-book "misc/eval" :dir :system)

; Pete 9/16/2018: Better range support
(include-book "tau/bounders/elementary-bounders" :dir :system)

; Pete 9/27/2018: Include utilities book
(include-book "utilities")

; Pete 9/14/2018: I am enabling some of the functions that
; std/lists/top disables, since this causes problems where simple
; theorems do not getting proved.

(in-theory (enable
            true-listp
            len
            append
            rev
            revappend
            no-duplicatesp-equal
            make-character-list
            nthcdr
            subseq-list
            resize-list
            last
            butlast
            remove
            member
            subsetp
            intersectp
            union-equal
            set-difference-equal
            intersection-equal))

; I (Pete) went through the built-in functions and added signature
; rules where appropriate. This list is not complete for two
; reasons. First, there are some cases in which we fail due to the
; algorithm not being as general as it can be. See the acl2s-issues
; file. Second, I made one pass through the documentation of
; ACL2-built-ins. I should check again and I should check functions
; defined in the books we load.

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

#|
PETE: adding something like this might be useful.
Decided to leave out for now because

1. Building the books takes long
2. The use of rtl sometimes slows down proofs

(include-book
  "rtl/rel11/lib/top" :dir :system)
(in-theory
 (disable
  acl2::|(mod (+ x y) z) where (<= 0 z)| acl2::|(mod (+ x (- (mod a b))) y)| 
  acl2::|(mod (mod x y) z)| acl2::|(mod (+ x (mod a b)) y)| acl2::cancel-mod-+
  acl2::mod-cancel-*-const acl2::simplify-products-gather-exponents-equal 
  acl2::simplify-products-gather-exponents-<
  acl2::cancel-mod-+ acl2::reduce-additive-constant-< acl2::|(floor x 2)|
  acl2::|(equal x (if a b c))| acl2::|(equal (if a b c) x)|))
|#

#| 

PETE: See if there is a way to get rid of these rules.

|#

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

(defthm replace-o<-with-<
  (implies (and (natp x)
                (natp y))
           (equal (o< x y)
                  (< x y)))
  :hints (("goal" :in-theory (enable o<))))

(defmacro tlp (x)
  `(true-listp ,x))

(add-macro-fn tlp true-listp)

(defmacro tl-fix (x)
  `(acl2::true-list-fix ,x))

(add-macro-fn tl-fix acl2::true-list-fix)

(defmacro app (&rest rst)
  `(append ,@rst))

(add-macro-fn app binary-append)
