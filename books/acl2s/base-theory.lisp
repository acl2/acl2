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
(include-book "misc/meta-lemmas" :dir :system)

; Pete 9/14/2018: Useful for must-fail
(include-book "std/testing/eval" :dir :system)

; Pete 9/16/2018: Better range support
(include-book "tau/bounders/elementary-bounders" :dir :system)

; Pete 9/27/2018: Include utilities book
(include-book "utilities")
(include-book "definec" :ttags :all)
(include-book "cons-size")
(include-book "properties")
(include-book "check-equal")

(include-book "std/strings/top" :dir :system)
(include-book "system/doc/developers-guide" :dir :system)

(include-book "acl2s/acl2s-size" :dir :system)
(include-book "acl2s/ccg/ccg" :dir :system 
  :uncertified-okp nil :ttags ((:ccg))
  :load-compiled-file nil)

(set-termination-method :ccg)

; inhibit all ccg output.
; comment out to debug termination failures in the book.
(make-event
 (er-progn
  (set-ccg-inhibit-output-lst acl2::*ccg-valid-output-names*)
  (value '(value-triple :invisible))))

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


; An attempt to control the order of arithmetic rules.
(include-book
  "arithmetic-5/lib/basic-ops/simple-equalities-and-inequalities"
  :dir :system)
(include-book "arithmetic-5/lib/basic-ops/simplify" :dir :system)
(include-book "arithmetic-5/lib/basic-ops/building-blocks" :dir :system)
(include-book "arithmetic-5/lib/floor-mod/floor-mod" :dir :system)
(local (include-book "arithmetic-5/top" :dir :system))

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

(defun pair-tl (x y)
  (if (or (endp x) (endp y))
      nil
    (cons (list (car x) (car y)) (pair-tl (cdr x) (cdr y)))))

(defun stage-rule1 (fn def-rule vars max clause flg)
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
            ((stage-rule1 ',fn
                          ',def-rule
                          ',vars
                          ,(- max 1)
                          clause
                          stable-under-simplificationp))
            :expand (:with ,def-rule ,temp)))
      nil)))

(defmacro stage-rule (fn def-rule &optional (max '100) vars)
  `(stage-rule1 ',fn
                ',def-rule
                (or ,vars (formals ',fn (w state)))
                ,max
                clause
                stable-under-simplificationp))

#|
 Here is an example of how this is used

 (add-default-hints!
  '((stage-rule cfix cfix-definition-rule))
  :at-end t)

|#

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

(add-macro-fn tlp true-listp)

(defmacro tl-fix (x)
  `(acl2::true-list-fix ,x))

(add-macro-fn tl-fix acl2::true-list-fix)

(definec bin-app (x :tl y :tl) :tl
  (append x y))

(make-n-ary-macro app bin-app nil t)

(add-macro-fn app binary-append)
(add-macro-fn app bin-app)

; shorthand for equal
(defmacro == (x y)
  `(equal ,x ,y))

; shorthand for not equal
(defmacro =/= (x y)
  `(not (equal ,x ,y)))

; shorthand for not equal
(defmacro != (x y)
  `(not (equal ,x ,y)))

; shorthand for implies
(defmacro => (x y)
  `(implies ,x ,y))

; shorthand for not
(defmacro ! (x)
  `(not ,x))

; shorthand for and 
(defmacro ^ (&rest args)
  (and-macro args))

; shorthand for or
(defmacro v (&rest args)
  (or-macro args))

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

#|

Useful for testing defunc/definec errors

:trans1
(definec in (a :all X :tl) :bool
  (and (consp X)
       (or (== a (car X))
           (in a (cdr X)))))

:trans1
(DEFINEC-CORE IN NIL (A :ALL X :TL)
  :BOOL (AND (CONSP X)
             (OR (== A (CAR X)) (IN A (CDR X)))))

(redef+)
(redef-)

|#

(definec in (a :all X :tl) :bool
  (and (consp X)
       (or (== a (car X))
           (in a (cdr X)))))

(defdata non-empty-true-list (cons all true-list))

(defdata-alias ne-tl non-empty-true-list)

(add-macro-fn ne-tlp non-empty-true-listp)

; left and right are strict versions of car and cdr, i.e., they can
; only be applied to conses.
(definec left (x :cons) :all 
  (car x))

(definec right (x :cons) :all
  (cdr x))

; head and tail are versions of car and cdr that are applied to only
; true-lists and they are also strict, so the true-lists have to be
; conses.
(definec head (x :ne-tl) :all
  (car x))

(definec tail (x :ne-tl) :tl 
  (cdr x))

(definec lcons (x :all y :tl) :ne-tl 
  (cons x y))

; a strict version of nth requiring that the list have at least n+1
; elements (since we use 0 indexing)
(definec lnth (n :nat l :tl) :all
  :pre (< n (len l))
  (nth n l))

(check= (lnth 2 '(0 1 2 3)) 2)

; a strict version of nthcdr, requiring that we have at least n
; elements ((nthcdr 0 l) is the identity)
(definec lnthcdr (n :nat l :tl) :tl
  :pre (<= n (len l))
  (nthcdr n l))

(check= (lnthcdr 2 '(0 1 2 3)) '(2 3))

; The definitions below are used to define gen-car-cdr-macros.
(defdata str-all (list string all))
(defdata l-str-all (listof str-all))

(definec-no-test gen-car-cdr-aux-1
  (car :var cdr :var carstr :string cdrstr :string res :l-str-all) :l-str-all
  (if (endp res)
      res
    (b* ((e (first res))
         (str (first e))
         (exp (second e)))
      (list* `(,(str::cat carstr str)
               `(,',car ,,exp))
             `(,(str::cat cdrstr str)
               `(,',cdr ,,exp))
             (gen-car-cdr-aux-1 car cdr carstr cdrstr (cdr res))))))

(check= (gen-car-cdr-aux-1 'head 'tail "h" "t" '(("" x)))
        `(("h" `(head ,x))
          ("t" `(tail ,x))))

; The termination hint isn't need, but it saves 10 seconds and I
; certify this file enough that it is worth annotating.
(definec-no-test gen-car-cdr-aux
  (car :var cdr :var carstr :string cdrstr :string
       depth :nat res :l-str-all) :l-str-all
  (declare (xargs :consider-only-ccms (depth)))
  (cond ((endp res) (gen-car-cdr-aux
                     car
                     cdr
                     carstr
                     cdrstr
                     depth
                     `(("" x))))
        ((== depth 0) res)
        (t (app (if (consp (cdr res)) res nil)
                (gen-car-cdr-aux
                 car
                 cdr
                 carstr
                 cdrstr
                 (1- depth)
                 (gen-car-cdr-aux-1 car cdr carstr cdrstr res))))))

(check= (gen-car-cdr-aux 'head 'tail "h" "t" 1 nil)
        `(("h" `(head ,x))
          ("t" `(tail ,x))))

(check= (gen-car-cdr-aux 'head 'tail "h" "t" 2 nil)
        `(("h" `(head ,x))
          ("t" `(tail ,x))
          ("hh" `(head (head ,x)))
          ("th" `(tail (head ,x)))
          ("ht" `(head (tail ,x)))
          ("tt" `(tail (tail ,x)))))

(definec gen-car-cdr-defs-fn
  (l :l-str-all prefix :string suffix :string pkg :string) :all
  :pre (!= pkg "")
  (if (endp l)
      l
    (b* ((mname (defdata::s+ (str::cat prefix (caar l) suffix) :pkg pkg))
         (x (fix-intern$ "X" pkg)))
      (cons 
       `(defmacro ,mname (,x)
          ,(cadar l))
       (gen-car-cdr-defs-fn (cdr l) prefix suffix pkg)))))

(definec gen-car-cdr-macros-fn
  (car :var cdr :var carstr :string cdrstr :string prefix :string
       suffix :string depth :nat pkg :string) :all
  :pre (!= pkg "")
  :skip-tests t
  (let ((l (gen-car-cdr-aux car cdr carstr cdrstr depth nil)))
    `(encapsulate
      ()
      ,@(gen-car-cdr-defs-fn l prefix suffix pkg))))

(check=
 (gen-car-cdr-macros-fn 'head 'tail "A" "D" "LC" "R" 2 "ACL2S")
 `(encapsulate
   nil
   (defmacro lcar (x) `(head ,x))
   (defmacro lcdr (x) `(tail ,x))
   (defmacro lcaar (x) `(head (head ,x)))
   (defmacro lcdar (x) `(tail (head ,x)))
   (defmacro lcadr (x) `(head (tail ,x)))
   (defmacro lcddr (x) `(tail (tail ,x)))))

(defmacro gen-car-cdr-macros
  (car cdr carstr cdrstr prefix suffix depth)
  `(make-event
    (gen-car-cdr-macros-fn
     ',car ',cdr ,carstr ,cdrstr ,prefix ,suffix ,depth
     (current-package state))))

(gen-car-cdr-macros head tail "A" "D" "LC" "R" 4)

; Generates the following redundant events, where "s" means "strict":


(defmacro lcar (x) `(head ,x))
(defmacro lcdr (x) `(tail ,x))

(defmacro lcaar (x) `(head (head ,x)))
(defmacro lcadr (x) `(head (tail ,x)))
(defmacro lcdar (x) `(tail (head ,x)))
(defmacro lcddr (x) `(tail (tail ,x)))

(defmacro lcaaar (x) `(head (head (head ,x))))
(defmacro lcaadr (x) `(head (head (tail ,x))))
(defmacro lcadar (x) `(head (tail (head ,x))))
(defmacro lcaddr (x) `(head (tail (tail ,x))))
(defmacro lcdaar (x) `(tail (head (head ,x))))
(defmacro lcdadr (x) `(tail (head (tail ,x))))
(defmacro lcddar (x) `(tail (tail (head ,x))))
(defmacro lcdddr (x) `(tail (tail (tail ,x))))

(defmacro lcaaaar (x) `(head (head (head (head ,x)))))
(defmacro lcaaadr (x) `(head (head (head (tail ,x)))))
(defmacro lcaadar (x) `(head (head (tail (head ,x)))))
(defmacro lcaaddr (x) `(head (head (tail (tail ,x)))))
(defmacro lcadaar (x) `(head (tail (head (head ,x)))))
(defmacro lcadadr (x) `(head (tail (head (tail ,x)))))
(defmacro lcaddar (x) `(head (tail (tail (head ,x)))))
(defmacro lcadddr (x) `(head (tail (tail (tail ,x)))))
(defmacro lcdaaar (x) `(tail (head (head (head ,x)))))
(defmacro lcdaadr (x) `(tail (head (head (tail ,x)))))
(defmacro lcdadar (x) `(tail (head (tail (head ,x)))))
(defmacro lcdaddr (x) `(tail (head (tail (tail ,x)))))
(defmacro lcddaar (x) `(tail (tail (head (head ,x)))))
(defmacro lcddadr (x) `(tail (tail (head (tail ,x)))))
(defmacro lcdddar (x) `(tail (tail (tail (head ,x)))))
(defmacro lcddddr (x) `(tail (tail (tail (tail ,x)))))

(gen-car-cdr-macros head tail "A" "D" "LC" "R" 4)

#|

 Generates the following macros, where "l" means true-list :

 lcar:  (head x)
 lcdr:  (tail x)
 lcaar: (head (head x))
 lcadr: (head (tail x))

 ...

 lcddddr: (tail (tail (tail (tail x))))

|#

; strict versions of first, ..., tenth: we require that x is a tl
; with enough elements
(defmacro lfirst   (x) `(lcar ,x))
(defmacro lsecond  (x) `(lcadr ,x))
(defmacro lthird   (x) `(lcaddr ,x))
(defmacro lfourth  (x) `(lcadddr ,x))
(defmacro lfifth   (x) `(lcar (lcddddr ,x)))
(defmacro lsixth   (x) `(lcadr (lcddddr ,x)))
(defmacro lseventh (x) `(lcaddr (lcddddr ,x)))
(defmacro leighth  (x) `(lcadddr (lcddddr ,x)))
(defmacro lninth   (x) `(lcar (lcddddr (lcddddr ,x))))
(defmacro ltenth   (x) `(lcadr (lcddddr (lcddddr ,x))))

; A forward-chaining rule to deal with the relationship
; between len and cdr.

(defthm expand-len-with-trigger-cdr
  (implies (and (<= c (len x))
                (posp c))
           (<= (1- c) (len (cdr x))))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((< (len x) c) (cdr x)))))

(defthm len-non-nil-with-trigger-cdr
  (implies (and (<= c (len x))
                (posp c))
           x)
  :rule-classes ((:forward-chaining :trigger-terms ((< (len x) c)))))

#|

 This may be useful. I started with this, but used the above rule
 instead.

 (defthm exp-len1
   (implies (and (syntaxp (quotep c))
                 (syntaxp (< (second c) 100))
 		 (posp c)
 		 (<= c (len x)))
            (<= (1- c) (len (cdr x))))
   :rule-classes ((:forward-chaining :trigger-terms ((< (len x) c)))))

 (defthm exp-len2
   (implies (and (syntaxp (quotep c))
                 (syntaxp (< (second c) 100))
 		 (posp c)
 		 (<= c (len x)))
	    x)
   :rule-classes ((:forward-chaining :trigger-terms ((< (len x) c)))))

|#

#|

 A collection of forward-chaining rules that help with reasoning about
 conses with car, cdr, head, tail, left, right.

|#

(defthm cddr-implies-cdr-trigger-cddr
  (implies (cddr x)
	   (cdr x))
  :rule-classes ((:forward-chaining :trigger-terms ((cddr x)))))

(defthm tlp-implies-tlpcdr-trigger-cdr
  (implies (true-listp x)
	   (true-listp (cdr x)))
  :rule-classes ((:forward-chaining :trigger-terms ((cdr x)))))

(defthm tlp-consp-cdr-implies-tail-trigger-tail
  (implies (and (true-listp x)
		(consp (cdr x)))
	   (tail x))
  :rule-classes ((:forward-chaining :trigger-terms ((tail x)))))

(defthm tlp-consp-implies-tlp-tail-trigger-tail
  (implies (and (true-listp x) x)
	   (true-listp (tail x)))
  :rule-classes ((:forward-chaining :trigger-terms ((tail x)))))

(defthm consp-cdr-implies-right-trigger-right
  (implies (consp (cdr x))
	   (right x))
  :rule-classes ((:forward-chaining :trigger-terms ((right x)))))

(defthm tlp-consp-implies-tlp-right-trigger-right
  (implies (and (true-listp x) x)
	   (true-listp (right x)))
  :rule-classes ((:forward-chaining :trigger-terms ((right x)))))

; Basic left-right theorems
(defthm left-cons
  (equal (left (cons x y))
         x))

(defthm right-cons
  (equal (right (cons x y))
         y))

(defthm left-consp
  (implies (force (consp x))
           (equal (left x) (car x))))

(defthm right-consp
  (implies (force (consp x))
           (equal (right x) (cdr x))))

; Basic head-tail theorems
(defthm head-cons
  (implies (force (tlp y))
           (equal (head (cons x y))
                  x)))

(defthm tail-cons
  (implies (force (tlp y))
           (equal (tail (cons x y))
                  y)))

(defthm head-consp
  (implies (and (force (tlp x)) (force x))
           (equal (head x) (car x))))

(defthm tail-consp
  (implies (and (force (tlp x)) (force x))
           (equal (tail x) (cdr x))))

; Disable tail, head, left, right so that it is easier to debug
; proofs
(in-theory (disable tail tail-definition-rule
                    head head-definition-rule
                    left left-definition-rule
                    right right-definition-rule))

#||

 Suppose I want to define a datatype corresponding to a non-empty list of
 integers that ends with a natural number. Here's one way to do that.

 (defdata loin (oneof (list nat)
                      (cons integer loin)))

 By defining the snoc constructor, we can instead 

 (defdata loi (listof int))
 (defdata loins (snoc loi nat))

 (defdata-equal-strict loin loins)

||#

(definec snoc (l :tl e :all) :ne-tl
  (append l (list e)))

(defmacro lsnoc (l e)
  `(snoc ,l ,e))

(definec snocl (l :ne-tl) :tl
  (butlast l 1))

(definec snocr (l :ne-tl) :all
  (car (last l)))

(register-data-constructor
 (ne-tlp snoc)
 ((tlp snocl) (allp snocr))
 :rule-classes nil
 :proper nil)

(definec lendp (x :tl) :bool
  (atom x))

(definec llen (x :tl) :nat
  (len x))

(definec lrev (x :tl) :tl
  (rev x))

; Added this since even on very simple examples defconst
; seems to go on forever.
(defmacro def-const (name form &optional doc)
  `(with-output
    :off :all :gag-mode nil :stack :push
    (make-event
     (let ((form ,form))
       `(with-output
         :stack :pop 
         (defconst ,',name ',form ,@(and ,doc '(,doc))))))))

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
