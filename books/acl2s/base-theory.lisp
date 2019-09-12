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
(include-book "check-equal")

(include-book "std/strings/top" :dir :system)
(include-book "system/doc/developers-guide" :dir :system)

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
neg-ratio: non-pos-rational
pos-ratio: non-neg-rational
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

#|
Useful for testing defunc/definec errors

:trans1
(definec in (a :all X :tl) :bool
  (and (consp X)
       (or (== a (car X))
           (in a (cdr X)))))

:trans1
(DEFUNC IN (A X)
  :INPUT-CONTRACT (TRUE-LISTP X)
  :OUTPUT-CONTRACT (BOOLEANP (IN A X))
  (AND (CONSP X)
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

; a strict version of nth requiring that the list have at least n+1
; elements (since we use 0 indexing)
(defunc snth (n l)
  :pre  (and (natp n) (tlp l) (< (len l) n))
  :post t
  (nth n l))

; a strict version of nthcdr, requiring that we have at least n
; elements ((nthcdr 0 l) is the identity)
(defunc snthcdr (n l)
  :pre (and (natp n) (tlp l) (<= (len l) n))
  :post :tl
  (nthcdr n l))

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
  (declare (xargs :consider-only-ccms ( depth )))
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

(defunc gen-car-cdr-defs-fn (l prefix suffix pkg)
  :pre (and (l-str-allp l) (stringp prefix) (stringp suffix)
            (stringp pkg) (!= pkg ""))
  :post :all
  (if (endp l)
      l
    (b* ((mname (defdata::s+ (str::cat prefix (caar l) suffix) :pkg pkg))
         (x (fix-intern$ "X" pkg)))
      (cons 
       `(defmacro ,mname (,x)
          ,(cadar l))
       (gen-car-cdr-defs-fn (cdr l) prefix suffix pkg)))))

(defunc gen-car-cdr-macros-fn
  (car cdr carstr cdrstr prefix suffix depth pkg)
  :pre (and (varp car) (varp cdr) (stringp carstr)
            (stringp cdrstr) (stringp prefix) (stringp suffix)
            (natp depth) (stringp pkg) (!= pkg ""))
  :post :all
  :skip-tests t
  (let ((l (gen-car-cdr-aux car cdr carstr cdrstr depth nil)))
    `(encapsulate
      ()
      ,@(gen-car-cdr-defs-fn l prefix suffix pkg))))

(check=
 (gen-car-cdr-macros-fn 'head 'tail "A" "D" "SC" "R" 2 "ACL2S")
 `(encapsulate
   nil
   (defmacro scar (x) `(head ,x))
   (defmacro scdr (x) `(tail ,x))
   (defmacro scaar (x) `(head (head ,x)))
   (defmacro scdar (x) `(tail (head ,x)))
   (defmacro scadr (x) `(head (tail ,x)))
   (defmacro scddr (x) `(tail (tail ,x)))))

(defmacro gen-car-cdr-macros
  (car cdr carstr cdrstr prefix suffix depth)
  `(make-event
    (gen-car-cdr-macros-fn
     ',car ',cdr ,carstr ,cdrstr ,prefix ,suffix ,depth
     (current-package state))))

(gen-car-cdr-macros left right "A" "D" "SC" "R" 4)

; Generates the following redundant events, where "s" means "strict":


(defmacro scar (x) `(left ,x))
(defmacro scdr (x) `(right ,x))

(defmacro scaar (x) `(left (left ,x)))
(defmacro scadr (x) `(left (right ,x)))
(defmacro scdar (x) `(right (left ,x)))
(defmacro scddr (x) `(right (right ,x)))

(defmacro scaaar (x) `(left (left (left ,x))))
(defmacro scaadr (x) `(left (left (right ,x))))
(defmacro scadar (x) `(left (right (left ,x))))
(defmacro scaddr (x) `(left (right (right ,x))))
(defmacro scdaar (x) `(right (left (left ,x))))
(defmacro scdadr (x) `(right (left (right ,x))))
(defmacro scddar (x) `(right (right (left ,x))))
(defmacro scdddr (x) `(right (right (right ,x))))

(defmacro scaaaar (x) `(left (left (left (left ,x)))))
(defmacro scaaadr (x) `(left (left (left (right ,x)))))
(defmacro scaadar (x) `(left (left (right (left ,x)))))
(defmacro scaaddr (x) `(left (left (right (right ,x)))))
(defmacro scadaar (x) `(left (right (left (left ,x)))))
(defmacro scadadr (x) `(left (right (left (right ,x)))))
(defmacro scaddar (x) `(left (right (right (left ,x)))))
(defmacro scadddr (x) `(left (right (right (right ,x)))))
(defmacro scdaaar (x) `(right (left (left (left ,x)))))
(defmacro scdaadr (x) `(right (left (left (right ,x)))))
(defmacro scdadar (x) `(right (left (right (left ,x)))))
(defmacro scdaddr (x) `(right (left (right (right ,x)))))
(defmacro scddaar (x) `(right (right (left (left ,x)))))
(defmacro scddadr (x) `(right (right (left (right ,x)))))
(defmacro scdddar (x) `(right (right (right (left ,x)))))
(defmacro scddddr (x) `(right (right (right (right ,x)))))

(gen-car-cdr-macros head tail "A" "D" "SLC" "R" 4)

#|

 Generates the following macros, where "sl" means strict list:

 slcar:  (head x)
 slcdr:  (tail x)
 slcaar: (head (head x))
 slcadr: (head (tail x))

 ...

 slcddddr: (tail (tail (tail (tail x))))

|#

; strict versions of first, ..., tenth: we require that x is a tl
; with enough elements
(defmacro sfirst   (x) `(slcar ,x))
(defmacro ssecond  (x) `(slcadr ,x))
(defmacro sthird   (x) `(slcaddr ,x))
(defmacro sfourth  (x) `(slcadddr ,x))
(defmacro sfifth   (x) `(slcar (slcddddr ,x)))
(defmacro ssixth   (x) `(slcadr (slcddddr ,x)))
(defmacro sseventh (x) `(slcaddr (slcddddr ,x)))
(defmacro seighth  (x) `(slcadddr (slcddddr ,x)))
(defmacro sninth   (x) `(slcar (slcddddr (slcddddr ,x))))
(defmacro stenth   (x) `(slcadr (slcddddr (slcddddr ,x))))

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

(definec snocl (l :ne-tl) :tl
  (butlast l 1))

(definec snocr (l :ne-tl) :all
  (car (last l)))

(register-data-constructor
 (ne-tlp snoc)
 ((tlp snocl) (allp snocr))
 :rule-classes nil
 :proper nil)


