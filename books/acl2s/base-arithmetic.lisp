#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2S")

(include-book "defdata/top" :ttags :all)

; Pete 9/16/2018: Better range support
(include-book "tau/bounders/elementary-bounders" :dir :system)

; Pete 9/27/2018: Include utilities book
(include-book "definec" :ttags :all)

(include-book "acl2s/ccg/ccg" :dir :system 
  :uncertified-okp nil :ttags ((:ccg))
  :load-compiled-file nil)

(set-termination-method :ccg)

; An attempt to control the order of arithmetic rules.
(include-book
  "arithmetic-5/lib/basic-ops/simple-equalities-and-inequalities"
  :dir :system)
(include-book "arithmetic-5/lib/basic-ops/simplify" :dir :system)
(include-book "arithmetic-5/lib/basic-ops/building-blocks" :dir :system)
(include-book "arithmetic-5/lib/floor-mod/floor-mod" :dir :system)
(local (include-book "arithmetic-5/top" :dir :system))
(local (set-defunc-timeout 1000))

#|
PETE: adding something like this might be useful.
Decided to leave out for now because

1. Building the books takes long
2. The use of rtl sometimes slows down proofs

(include-book
  "rtl/rel11/lib/top" :dir :system)
(in-theory
 (disable
  acl2::|(mod (+ x y) z) where (<= 0 z)| 
  acl2::|(mod (+ x (- (mod a b))) y)|
  acl2::|(mod (mod x y) z)| 
  acl2::|(mod (+ x (mod a b)) y)| 
  acl2::cancel-mod-+
  acl2::mod-cancel-*-const 
  acl2::simplify-products-gather-exponents-equal
  acl2::simplify-products-gather-exponents-<
  acl2::cancel-mod-+ 
  acl2::reduce-additive-constant-< 
  acl2::|(floor x 2)|
  acl2::|(equal x (if a b c))| 
  acl2::|(equal (if a b c) x)|))
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

neg: non-pos-integer, non-0-integer, neg-rational
pos: nat, non-0-integer, pos-rational

non-pos-integer: integer
non-0-integer: integer
nat: integer

odd:     (not recognizer)
even:    (not recognizer)
z:       (not recognizer)

integer: rational

neg-ratio: non-pos-rational
pos-ratio: non-neg-rational

ratio: rational

neg-rational: non-pos-rational, non-0-rational
pos-rational: non-neg-rational, non-0-rational

non-neg-rational: rational
non-pos-rational: rational
non-0-rational: rational

rational: acl2-number
complex-rational: acl2-number
acl2-number: atom

We also want disjoint theorems

neg: nat
pos: non-pos-integer

integer: ratio

neg-ratio: non-neg-rational (probably don't need)
pos-ratio: non-pos-rational (probably don't need)

neg-rational: non-neg-rational
pos-rational: non-pos-rational
rational: complex-rational

odd: even (don't need as it follows from definition of odd)

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
          neg-ratiop pos-ratiop ratiop
          neg-rationalp pos-rationalp non-neg-rationalp
          non-pos-rationalp))

#|

End of new version.

|#


#|

From rtl/rel11/lib/top.lisp, where various arithmetic-5
theorems are disabled.

I commented out some disabled theorems that seem fine to me.

|#

(local
(in-theory
 #!acl2(disable
        ;; |(mod (+ x y) z) where (<= 0 z)|
        ;; |(mod (+ x (- (mod a b))) y)|
        ;; |(mod (mod x y) z)|
        ;; |(mod (+ x (mod a b)) y)|
        ;; mod-cancel-*-const
        cancel-floor-+
        cancel-mod-+
        prefer-positive-addends-<
        prefer-positive-addends-equal
        reduce-additive-constant-< 
        reduce-additive-constant-equal
        default-mod-ratio
        ash-to-floor
        |(floor x 2)|
        |(equal x (if a b c))|
        |(equal (if a b c) x)|
        |(logior 1 x)|
        |(mod (+ 1 x) y)|
        ;; mod-theorem-one-b x
        ;; default-plus-2 x
        ;; default-minus
        ;;  |(mod (- x) y)|
        ;;  mod-sums-cancel-1
        ;;  |(equal (mod a n) (mod b n))|
        )))

(defthm acl2s-default-mod-ratio
  (implies (and (not (complex-rationalp x))
                (syntaxp (not (acl2::proveably-real/rational
                                     'y
                                     (cons (cons 'y y) 'nil)
                                     mfc state))))
           (equal (mod x y)
                  (if (real/rationalp y)
                      (mod x y)
                    (fix x))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

#!acl2
(defthm acl2s::acl2s-cancel-floor-+
  (implies
   (and (real/rationalp (/ x y))
        (syntaxp (in-term-order-+ x mfc state))
        (bind-free
         (find-cancelling-addends x y mfc state)
         (addend))
        (equal i (/ addend y))
        (integerp i))
   (equal (floor x y)
          (+ (- i)
             (floor (+ addend x)
                    y))))
  :hints (("goal" :by acl2::cancel-floor-+))
  :rule-classes ((:rewrite :backchain-limit-lst 2)))

#!acl2
(defthm acl2s::acl2s-cancel-mod-+
  (implies
   (and (acl2-numberp y)
        (not (equal y 0))
        (syntaxp (not (equal x ''0)))
        (real/rationalp (/ x y))
        (syntaxp (in-term-order-+ x mfc state))
        (bind-free
         (find-cancelling-addends x y mfc state)
         (addend))
        (equal i (/ addend y))
        (integerp i))
   (equal (mod x y)
          (mod (+ addend x) y)))
  :hints (("goal" :use ((:instance acl2::cancel-mod-+))
           :in-theory (disable acl2::cancel-mod-+ acl2::cancel-floor-+)))
  :otf-flg t
  :rule-classes ((:rewrite :backchain-limit-lst 2)))

#|

 This was leading to infinite rewrite loops, which should be
 investigated.

#!acl2
(defthm acl2s::acl2s-prefer-positive-addends-<
  (implies
   (and (syntaxp (in-term-order-+ lhs mfc state))
        (syntaxp (in-term-order-+ rhs mfc state))
        (syntaxp (or (equal (fn-symb lhs)
                            'binary-+)
                     (equal (fn-symb rhs)
                            'binary-+)))
        (bind-free
         (find-negative-addend lhs rhs mfc state)
         (x)))
   (equal (< lhs rhs)
          (< (+ x lhs)
             (+ x rhs))))
  :rule-classes ((:rewrite :backchain-limit-lst 2)))
|#

#!acl2
(defthm acl2s::acl2s-prefer-positive-addends-<1
  (implies
   (and (syntaxp (in-term-order-+ lhs mfc state))
        (syntaxp (in-term-order-+ rhs mfc state))
        (syntaxp (or (equal (fn-symb lhs)
                            'binary-+)
                     (equal (fn-symb rhs)
                            'binary-+)))
        (bind-free
         (find-negative-addend lhs rhs mfc state)
         (x))
        (equal yyy (- x)))
   (equal (< lhs (+ yyy rhs))
          (< (+ (- yyy) lhs) rhs)))
  :rule-classes ((:rewrite :backchain-limit-lst 2)))

#!acl2
(defthm acl2s::acl2s-prefer-positive-addends-<2
  (implies
   (and (syntaxp (in-term-order-+ lhs mfc state))
        (syntaxp (in-term-order-+ rhs mfc state))
        (syntaxp (or (equal (fn-symb lhs)
                            'binary-+)
                     (equal (fn-symb rhs)
                            'binary-+)))
        (bind-free
         (find-negative-addend lhs rhs mfc state)
         (x))
        (equal yyy (- x)))
   (equal (< (+ yyy lhs) rhs)
          (< lhs (+ (- yyy) rhs))))
  :rule-classes ((:rewrite :backchain-limit-lst 2)))

#!acl2
(defthm acl2s::acl2s-prefer-positive-addends-equal
  (implies (and (acl2-numberp lhs)
                (acl2-numberp rhs)
                (syntaxp (in-term-order-+ lhs mfc state))
                (syntaxp (in-term-order-+ rhs mfc state))
                (syntaxp (or (equal (fn-symb lhs)
                                    'binary-+)
                             (equal (fn-symb rhs)
                                    'binary-+)))
                (bind-free
                 (find-negative-addend lhs rhs mfc state)
                 (x)))
           (equal (equal lhs rhs)
                  (equal (+ x lhs)
                         (+ x rhs))))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

#!acl2
(defthm acl2s::acl2s-reduce-additive-constant-<
  (implies
   (and (syntaxp (in-term-order-+ lhs mfc state))
        (syntaxp (in-term-order-+ rhs mfc state))
        (bind-free (find-constant-addend lhs rhs)
                   (c))
        (not (equal c 0))
        (syntaxp
         (simplify-ok-p
          (cons '< (cons lhs (cons rhs 'nil)))
          '(< (binary-+ c lhs)
              (binary-+ c rhs))
          (cons (cons 'lhs lhs)
                (cons (cons 'rhs rhs)
                      (cons (cons 'c c) 'nil)))
          mfc state))
        (acl2-numberp lhs)
        (acl2-numberp rhs)
        (acl2-numberp c))
   (equal (< lhs rhs)
          (< (+ c lhs)
             (+ c rhs))))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

#!acl2
(defthm acl2s::acl2s-reduce-additive-constant-equal
  (implies
   (and (syntaxp (in-term-order-+ lhs mfc state))
        (syntaxp (in-term-order-+ rhs mfc state))
        (bind-free (find-constant-addend lhs rhs)
                   (c))
        (not (equal c 0))
        (syntaxp
         (simplify-ok-p
          (cons 'equal
                (cons lhs (cons rhs 'nil)))
          '(equal (binary-+ c lhs)
                  (binary-+ c rhs))
          (cons (cons 'lhs lhs)
                (cons (cons 'rhs rhs)
                      (cons (cons 'c c) 'nil)))
          mfc state))
        (acl2-numberp lhs)
        (acl2-numberp rhs)
        (acl2-numberp c))
   (equal (equal lhs rhs)
          (equal (+ c lhs)
                 (+ c rhs))))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

;;; When things have stabilized under simplification, enable non-linear
;;; arithmetic for one round (goal being simplified) only.

#!ACL2
(defun my-nonlinearp-default-hint (stable-under-simplificationp hist pspv)
  ;; (declare (xargs :guard (and (consp pspv)
  ;;                 (consp (car pspv))
  ;;                 (consp (caar pspv))
  ;;                 (consp (cdaar pspv))
  ;;                 (consp (cddaar pspv))
  ;;                 (consp (cdr (cddaar pspv)))
  ;;                 (consp (cddr (cddaar pspv)))
  ;;                 (consp (cdddr (cddaar pspv)))
  ;;                 (consp (cddddr (cddaar pspv))))))
  (cond (stable-under-simplificationp
         (if (not (access rewrite-constant
                   (access prove-spec-var pspv :rewrite-constant)
                   :nonlinearp))
       (prog2$
        nil ;;harshrc 14Jan2012- The following gives a nasty error when run inside of ld
        ;; (observation-cw 'my-nonlinearp-default-hint 
        ;;                 "~%~%[Note: We now enable non-linear arithmetic.]~%~%")
        '(:computed-hint-replacement t
                     :nonlinearp t))
           nil))
        ((access rewrite-constant
              (access prove-spec-var pspv :rewrite-constant)
              :nonlinearp)
         (if (and (consp hist)
          (consp (car hist))
          ;; Without this, we would loop forever.  But
          ;; whenever I try to write an explanation, I get
          ;; confused about why it works.  I stumbled across
          ;; this by trial and error and observing the output
          ;; of tracing.  Some day I should figure out what I
          ;; am doing.
          (not (equal (caar hist) 'SETTLED-DOWN-CLAUSE)))
         (prog2$
          nil ;;The following gives a nasty error when run inside of ld
          ;; (observation-cw 'my-nonlinearp-default-hint 
          ;;                 "~%~%[Note: We now disable non-linear arithmetic.]~%~%")
           '(:computed-hint-replacement t
                        :nonlinearp nil))
           nil))
        (t
         nil)))

#!acl2
(local
 (set-default-hints
  '((my-nonlinearp-default-hint stable-under-simplificationp hist pspv)
    (acl2s::stage acl2s::negp)
    (acl2s::stage acl2s::posp)
    (acl2s::stage acl2s::natp)
    (acl2s::stage acl2s::non-pos-integerp)
    (acl2s::stage acl2s::neg-ratiop)
    (acl2s::stage acl2s::pos-ratiop)
    (acl2s::stage acl2s::non-neg-ratiop)
    (acl2s::stage acl2s::non-pos-ratiop)
    (acl2s::stage acl2s::ratiop)
    (acl2s::stage acl2s::neg-rationalp)
    (acl2s::stage acl2s::pos-rationalp)
    (acl2s::stage acl2s::non-neg-rationalp)
    (acl2s::stage acl2s::non-pos-rationalp))))

(include-book "arithmetic-5/top" :dir :system)

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

(definec nat-ind (n :nat) :nat
  (if (zp n)
      n
    (nat-ind (- n 1))))

(definec pos-ind (n :pos) :pos
  (if (= n 1)
      n
    (pos-ind (- n 1))))

(definec int-ind (x :int) :nat
  (cond ((zip x) x)
        ((< x 0) (int-ind (1+ x)))
        (t (int-ind (1- x)))))

(defthm nat-induction-scheme
  t
  :rule-classes
  ((:induction :pattern (integerp x)
               :condition (and (integerp x) (>= x 0))
               :scheme (nat-ind x))))

(defthm pos-induction-scheme
  t
  :rule-classes
  ((:induction :pattern (integerp x)
               :condition (and (integerp x) (>= x 1))
               :scheme (pos-ind x))))

(defthm int-induction-scheme
  t
  :rule-classes
  ((:induction :pattern (integerp x)
               :condition (integerp x)
               :scheme (int-ind x))))

; The above induction schemes maybe useful in certain cases, but they
; also tend to cause ACL2 to pick the "wrong" induction schemes, so
; they are off by default.
(in-theory (disable nat-induction-scheme pos-induction-scheme int-induction-scheme))

(defthm cancel-<-+-1
  (equal (< (+ a b) a)
         (< b 0)))

(defthm cancel-<-+-2
  (equal (< a (+ a b))
         (< 0 b)))

(defthm cancel-<-*-1
  (implies (and (acl2-numberp a)
                (< 0 a)
                (rationalp b))
           (equal (< (* a b) a)
                  (< b 1)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm cancel-<-*-2
  (implies (and (acl2-numberp a)
                (< 0 a)
                (rationalp b))
           (equal (< a (* a b))
                  (< 1 b)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))
     
(defthm numerator-n-decreases
  (implies (and (rationalp r)
                (<= n r)
                (integerp n)
                (< 0 n))
           (< (numerator (+ (- n) r))
              (numerator r)))
  :hints (("goal" :induct (pos-ind n))
          ("subgoal *1/2.2"
           :use ((:instance numerator-1-decreases
                            (n (+ r (- n) 1))))))
  :rule-classes ((:linear) (:rewrite)))

(defthm replace-o<-with-<
  (implies (and (natp x)
                (natp y))
           (equal (o< x y)
                  (< x y)))
  :hints (("goal" :in-theory (enable o<)))
  :rule-classes ((:rewrite :backchain-limit-lst 2)))


#|

 Useful theorems about mod.

|#

(local
 (in-theory
  #!acl2(enable
         ;; |(mod (+ x y) z) where (<= 0 z)|
         ;; |(mod (+ x (- (mod a b))) y)|
         ;; |(mod (mod x y) z)|
         ;; |(mod (+ x (mod a b)) y)|
         ;; mod-cancel-*-const
         cancel-floor-+
         cancel-mod-+
         prefer-positive-addends-<
         prefer-positive-addends-equal
         reduce-additive-constant-< 
         reduce-additive-constant-equal
         default-mod-ratio
         ash-to-floor
         |(floor x 2)|
         |(equal x (if a b c))|
         |(equal (if a b c) x)|
         |(logior 1 x)|
         |(mod (+ 1 x) y)|
         ;; mod-theorem-one-b x
         ;; default-plus-2 x
         ;; default-minus
         ;;  |(mod (- x) y)|
         ;;  mod-sums-cancel-1
         ;;  |(equal (mod a n) (mod b n))|
         )))

(defthm mod-plus-simplify-a<n-+b
  (implies (and (non-neg-rationalp a)
                (< a n))
           (equal (equal (+ a (mod b n)) b)
                  (and (equal a 0)
                       (equal (mod b n) b))))
  :hints (("goal" :cases ((rationalp n)))))

(defthm mod-plus-simplify-b<n-+b
  (implies (and (acl2-numberp a)
                (non-neg-rationalp b)
                (< b n))
           (equal (equal (+ a (mod b n)) b)
                  (equal a 0))))

(defthm mod-plus-simplify-a<n-+b+n
  (implies (and (non-neg-rationalp a)
                (< a n))
           (equal (equal (+ a (mod b n))
                         (+ n b))
                  (and (equal a 0)
                       (< b 0)
                       (equal (mod b n) (+ b n))))))

(defthm mod-plus-simplify-b<n-+b+n
  (implies (and (non-neg-rationalp b)
                (< b n))
           (equal (equal (+ a (mod b n))
                         (+ n b))
                  (or (and (equal a 0)
                           (< b 0)
                           (equal (mod b n) (+ b n)))
                      (and (equal a n)
                           (<= 0 b)
                           (equal (mod b n) b))))))

(defthm |(x*y mod m)/y = x|
  (implies (and (acl2-numberp y)
                (/= y 0)
                (acl2-numberp x)
                (acl2-numberp m))
           (equal (equal (* (/ y) (mod (* x y) m)) x)
                  (equal (mod (* x y) m) (* x y)))))


(in-theory
 #!acl2(disable
        ;; |(mod (+ x y) z) where (<= 0 z)|
        ;; |(mod (+ x (- (mod a b))) y)|
        ;; |(mod (mod x y) z)|
        ;; |(mod (+ x (mod a b)) y)|
        ;; mod-cancel-*-const
        cancel-floor-+
        cancel-mod-+
        prefer-positive-addends-<
        prefer-positive-addends-equal
        reduce-additive-constant-< 
        reduce-additive-constant-equal
        default-mod-ratio
        ash-to-floor
        |(floor x 2)|
        |(equal x (if a b c))|
        |(equal (if a b c) x)|
        |(logior 1 x)|
        |(mod (+ 1 x) y)|
        ;; mod-theorem-one-b x
        ;; default-plus-2 x
        ;; default-minus
        ;;  |(mod (- x) y)|
        ;;  mod-sums-cancel-1
        ;;  |(equal (mod a n) (mod b n))|
        ))
