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
(include-book "definec" :ttags :all)
(include-book "properties")

(include-book "std/strings/top" :dir :system)
(include-book "system/doc/developers-guide" :dir :system)

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

#|

Experimenting with arithmetic.
Here is what we had before experimentation.

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

|#

#|

New versions using only fc rules and disabling natp, posp definitions.
The idea is to construct a partial order of the types and only include
forward-chaining rules that state a type is a subtype of the types
immediately above it.

The types are:

neg: non-pos-integer, neg-rational
pos: nat, pos-rational
non-neg-integer (rewrites to nat)
nat: integer
non-pos-integer: integer
odd:     (not recognizer)
even:    (not recognizer)
z:       (not recognizer)
integer: rational
neg-ratio: non-pos-ratio, non-pos-rational
pos-ratio: non-neg-ratio, non-neg-rational
non-neg-ratio: ratio
non-pos-ratio: ratio
ratio: rational
neg-rational: non-pos-rational
pos-rational: non-neg-rational
non-neg-rational: rational
non-pos-rational: rational
rational: acl2-number
complex-rational: acl2-number
acl2-number

We also want disjoint theorems

neg: nat,
pos: non-pos-integer
odd: even (don't need as it follows from definition of odd)
integer: ratio
neg-ratio: non-neg-rational (probably don't need)
pos-ratio: non-pos-rational (probably don't need)
neg-rational: non-neg-rational
pos-rational: non-pos-rational
rational: complex-rational

I updated defdata so that it generates forward-chaining rules with
subtype and disjoint forms, so see base.lisp in defdata.


|#

#|

These rules cause problems. Better to
use the rules below.

(defthm negp-expand-+
  (implies (and (integerp x)
                (integerp y))
           (equal (negp (+ x y))
                  (< x (- y)))))

(defthm posp-expand-+
  (implies (and (integerp x)
                (integerp y))
           (equal (posp (+ x y))
                  (< (- y) x))))

(defthm natp-expand-+
  (implies (and (integerp x)
                (integerp y))
           (equal (natp (+ x y))
                  (<= (- y) x))))

(defthm non-pos-integerp-expand-+
  (implies (and (integerp x)
                (integerp y))
           (equal (non-pos-integerp (+ x y))
                  (<= x (- y)))))

(defthm non-neg-rational-expand-+
  (implies (and (rationalp x)
                (rationalp y))
           (equal (non-neg-rationalp (+ x y))
                  (<= (- y) x))))

(defthm non-pos-rational-expand-+
  (implies (and (rationalp x)
                (rationalp y))
           (equal (non-pos-rationalp (+ x y))
                  (<= x (- y)))))
|#

#|

Rules like this will probably blow up
if I want to get something complete,
so instead I use computed hints.

(defthm negp-closed-under-+x
  (implies (and (negp x)
                (non-pos-integerp y))
           (negp (+ x y))))

(defthm negp-closed-under-+y
  (implies (and (negp y)
                (non-pos-integerp x))
           (negp (+ x y))))

(defthm posp-closed-under-+x
  (implies (and (posp x)
                (natp y))
           (posp (+ x y))))

(defthm posp-closed-under-+y
  (implies (and (posp y)
                (natp x))
           (posp (+ x y))))

(defthm natp-closed-under-+
  (implies (and (natp x)
                (natp y))
           (natp (+ x y))))

(defthm non-pos-integerp-closed-under-+
  (implies (and (non-pos-integerp x)
                (non-pos-integerp y))
           (non-pos-integerp (+ x y))))

(defthm neg-rational-closed-under-+x
  (implies (and (neg-rationalp x)
                (non-pos-rationalp y))
           (neg-rationalp (+ x y))))

(defthm neg-rational-closed-under-+y
  (implies (and (neg-rationalp y)
                (non-pos-rationalp x))
           (neg-rationalp (+ x y))))

(defthm pos-rational-closed-under-+x
  (implies (and (pos-rationalp x)
                (non-neg-rationalp y))
           (pos-rationalp (+ x y))))

(defthm pos-rational-closed-under-+y
  (implies (and (pos-rationalp y)
                (non-neg-rationalp x))
           (pos-rationalp (+ x y))))

(defthm non-neg-rational-closed-under-+
  (implies (and (non-neg-rationalp x)
                (non-neg-rationalp y))
           (non-neg-rationalp (+ x y))))

(defthm non-pos-rational-closed-under-+
  (implies (and (non-pos-rationalp x)
                (non-pos-rationalp y))
           (non-pos-rationalp (+ x y))))
|#

(in-theory
 (disable negp posp natp non-pos-integerp
          neg-ratiop pos-ratiop non-neg-ratiop non-pos-ratiop ratiop
          neg-rationalp pos-rationalp non-neg-rationalp
          non-pos-rationalp))

(mutual-recursion
 (defun find-first-call (fn term)
 ; Find the first call of fn in term.
  (cond ((acl2::variablep term) nil)
        ((acl2::fquotep term) nil)
        ((equal (acl2::ffn-symb term) fn)
         term)
        (t (find-first-call-lst fn (acl2::fargs term)))))
 (defun find-first-call-lst (fn lst)
 ; Find the first call of fn in a list of terms.
  (cond ((endp lst) nil)
        (t (or (find-first-call fn (car lst))
               (find-first-call-lst fn (cdr lst)))))))

(defun stage1 (fn max clause flg)
; If the clause is stable under simplification and there is a call of
; fn in it, expand it.  But don't do it more than max times.
 (let ((temp (and flg
                  (find-first-call-lst fn clause))))
   (if temp
       (if (zp max)
           (cw "~%~%HINT PROBLEM:  The maximum repetition count of ~
                your STAGE hint been reached without eliminating ~
                all of the calls of ~x0.  You could supply a larger ~
                count with the optional second argument to STAGE ~
                (which defaults to 100).  But think about what is ~
                happening! Is each stage permanently eliminating a ~
                call of ~x0?~%~%"
               fn)
         `(:computed-hint-replacement
            ((stage1 ',fn ,(- max 1)
                     clause
                     stable-under-simplificationp))
           :expand (,temp)))
     nil)))

(defmacro stage (fn &optional (max '100))
 `(stage1 ',fn ,max clause stable-under-simplificationp))

; see custom.lisp where the stage hints have been added.

#|

End of new version.

|#


#|

From rtl/rel11/lib/top.lisp, where various arithmetic-5
theorems are disabled.

I commented out some disabled theorems that seem fine to me.

|#

(in-theory
 #!acl2(disable |(mod (+ x y) z) where (<= 0 z)|
                |(mod (+ x (- (mod a b))) y)|
                |(mod (mod x y) z)|
                |(mod (+ x (mod a b)) y)|
                mod-cancel-*-const
                cancel-mod-+
                reduce-additive-constant-<
                ash-to-floor
                |(floor x 2)|
                |(equal x (if a b c))|
                |(equal (if a b c) x)|
                |(logior 1 x)|
;;                mod-theorem-one-b
                |(mod (- x) y)|
;;                acl2::mod-sums-cancel-1
;;                acl2::|(equal (mod a n) (mod b n))|
                ))

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

(add-macro-fn tlp true-listp)

(defmacro tl-fix (x)
  `(acl2::true-list-fix ,x))

(add-macro-fn tl-fix acl2::true-list-fix)

(defmacro app (&rest rst)
  `(append ,@rst))

(add-macro-fn app binary-append)

; shorthand for equal
(defmacro == (x y)
  `(equal ,x ,y))

(defmacro =/= (x y)
  `(not (equal ,x ,y)))

(defmacro != (x y)
  `(not (equal ,x ,y)))

(definec in (a :all X :tl) :bool
  (and (consp X)
       (or (== a (car X))
           (in a (cdr X)))))
