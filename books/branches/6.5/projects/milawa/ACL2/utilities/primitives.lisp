; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "../acl2-hacks/top")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)


(in-theory (disable ACL2::booleanp
                    (:type-prescription ACL2::not)
                    (:type-prescription ACL2::iff)
                    (:type-prescription ACL2::booleanp)
                    (:executable-counterpart ACL2::tau-system)
                    ACL2::iff-implies-equal-not
                    ACL2::iff-implies-equal-implies-1
                    ACL2::iff-implies-equal-implies-2
                    ACL2::booleanp-compound-recognizer))

;; After ACL2 4.3, I started seeing these crop up in rare proofs involving
;; constants, e.g., if the goal involved a term like (equal '(nil) (foo x))
;; then somehow ACL2 would start using its own rules about car/cdr/cons.  So,
;; now I just disable these, too.
(in-theory (disable acl2::car-cons
                    acl2::cdr-cons
                    acl2::cons-equal
                    acl2::default-car
                    acl2::default-cdr))

(local (in-theory (enable acl2::car-cons
                          acl2::cdr-cons
                          acl2::cons-equal
                          acl2::default-car
                          acl2::default-cdr)))


;; Base functions.
;;
;; We now define our base functions like car, cons, natp, and +.  We also
;; introduce some non-base functions like natp and <= which can be defined
;; in terms of the other base functions.

(definlined car (x)
  (declare (xargs :guard t :export nil))
  (if (consp x)
      (COMMON-LISP::car x)
    nil))

(definlined cdr (x)
  (declare (xargs :guard t :export nil))
  (if (consp x)
      (COMMON-LISP::cdr x)
    nil))

(defmacro first (x)
  (list 'car x))

(defmacro second (x)
  (list 'first (list 'cdr x)))

(defmacro third (x)
  (list 'second (list 'cdr x)))

(defmacro fourth (x)
  (list 'third (list 'cdr x)))

(defmacro fifth (x)
  (list 'fourth (list 'cdr x)))


;; Symbolp is a tricky case.  We want to have our ACL2 model match with the
;; logical story of Milawa, and we can accomplish this using the definition
;; shown below involving intern-in-package-of-symbol.

(defund symbolp (x)
  (declare (xargs :guard t :export nil))
  (and (COMMON-LISP::symbolp x)
       (equal x (ACL2::intern-in-package-of-symbol (COMMON-LISP::symbol-name x) 'MILAWA::foo))))

;; Unfortunately, intern-in-package-of-symbol is horribly slow.  To see just
;; how bad it is, we ran the following loops on lhug-3.  Using ACL2::symbolp,
;; the loop completes in .27 seconds.  But using the logical definition of
;; MILAWA::symbolp, the loop takes 61.17 seconds.  In other words, the damn
;; intern-in-package-of-symbol is making Milawa's symbolp run 226 times slower
;; than slower than the regular symbolp from Lisp.
;;
;; (in-package "ACL2")
;; (defparameter *foo* 'MILAWA::foo)
;; (time$ (loop for i fixnum from 1 to 100000000 do (ACL2::symbolp *foo*)))
;; (time$ (loop for i fixnum from 1 to 100000000 do (MILAWA::symbolp *foo*)))
;;
;; Is this a problem?  Well, yes and no.  For one, note that in our standalone
;; proof-checking system (Sources/milawa.lisp), that we can use Lisp's symbolp
;; directly because of the acceptable object invariant.  Hence, the slowness of
;; our ACL2 symbolp will cause the performance of our ACL2 model to differ from
;; that of our Milawa model.
;;
;; The real question, then, is how often symbolp is called.  After all, the
;; loop above was done for 100 million calls of symbolp.  But symbolp isn't
;; really used in any particularly intense way throughout most of the system,
;; and so we tolerated this performance until we were far into the
;; bootstrapping process.
;;
;; When we decided we wanted to speed up validity checking for worlds, we found
;; that symbolp's performance was actually meaningful.  In particular, this is
;; because the symbol-< function must "symbol-fix" its arguments, so for each
;; symbol-< comparison we must pay the price of interning twice.  This is quite
;; bad for the performance of mergesorting, search-tree lookups, and the like.
;;
;; Since ACL2 is being used only as a tool to sketch out the soundness proof,
;; we feel justified in unsoundly increasing the performance of symbolp, via
;; the following ttag.  Its logical definition is still the same as presented
;; above, but we could easily exploit this ttag to prove nil via the executable
;; counterpart of symbolp.

(ACL2::defttag unsound-but-faster-symbolp)
(ACL2::progn!
 (ACL2::set-raw-mode t)
 (ACL2::declaim (ACL2::inline MILAWA::symbolp))
 (ACL2::defun MILAWA::symbolp (x)
              (ACL2::symbolp x)))

(definlined symbol-< (x y)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable symbolp)))
                  :export nil))
  (let ((x-fix (if (symbolp x) x nil))
        (y-fix (if (symbolp y) y nil)))
    (if (COMMON-LISP::string< (COMMON-LISP::symbol-name x-fix)
                              (COMMON-LISP::symbol-name y-fix))
        t
      nil)))

(definlined natp (x)
  (declare (xargs :guard t :export nil))
  (and (COMMON-LISP::integerp x)
       (COMMON-LISP::<= 0 x)))

(definlined nfix (x)
  (declare (xargs :guard t))
  (if (natp x)
      x
    0))

(definlined < (a b)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable natp nfix)))
                  :export nil))
  (COMMON-LISP::< (nfix a) (nfix b)))

(definline <= (a b)
  ;; Note: we leave <= enabled
  (declare (xargs :guard t))
  (not (< b a)))

(definlined zp (x)
  (declare (xargs :guard t))
  (if (natp x)
      (equal x 0)
    t))

; Originally I defined + with no bounds checking.  But for Magnus Myreen's
; verifie Lisp, we wanted to ensure that no sums would overflow 30-bit
; integers.

(definlined + (a b)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable natp nfix)))
                  :export nil))
  (let ((ret (COMMON-LISP::+ (nfix a) (nfix b))))
    (if (< ret 1073741824)
        ret
      (ACL2::prog2$
       (ACL2::er ACL2::hard? '+ "Sum exceeds 30 bits.")
       ret))))

; The only overflows we ran into dealt with the RANK function, which we
; memoized and used to compute proof sizes.  But all of this is just dealing
; with proof debugging.  So, we make an unbounded version of RANK that we can
; use in debugging messages.

(acl2::defun unbounded-rank (x)
  (declare (xargs :guard t
                  :measure (acl2::acl2-count x)
                  :hints(("Goal" :in-theory (enable car cdr)))
                  :guard-hints(("Goal" :in-theory (enable car cdr)))))
  (if (consp x)
      (common-lisp::+ 1
                      (unbounded-rank (car x))
                      (unbounded-rank (cdr x)))
    0))

(definlined - (a b)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable natp nfix)))
                  :export nil))
  (nfix (COMMON-LISP::- (nfix a) (nfix b))))




(encapsulate
 ()
 (local (defthm natp-same-as-in-acl2
          ;; Just an observation; we never install this as a rule.
          (equal (natp x) (ACL2::natp x))
          :rule-classes nil
          :hints(("Goal" :in-theory (enable natp)))))

 (local (defthm nfix-same-as-in-acl2
          ;; Just an observation; we never install this as a rule.
          (equal (nfix x) (ACL2::nfix x))
          :rule-classes nil
          :hints(("Goal" :in-theory (enable natp nfix)))))

 (local (defthm zp-same-as-in-acl2
          ;; Just an observation; we never install this as a rule.
          (equal (zp x) (ACL2::zp x))
          :rule-classes nil
          :hints(("Goal" :in-theory (enable natp zp))))))




(defund booleanp (x)
  (declare (xargs :guard t))
  (if (equal x t)
      t
    (equal x nil)))

(defthm equal-of-booleans-rewrite
  ;; This is an important rule which takes care of a lot of cases which would
  ;; ordinarily require type reasoning.  The basic idea is that we can replace
  ;; equalities with iff equivalence as long as the arguments are both boolean.
  ;;
  ;; When I was at Rockwell, we had this rule with a backchain limit of zero,
  ;; which effectively means only type reasoning and forward chaining would be
  ;; used to determine if x and y are booleans.  For Milawa, I use a limit of
  ;; one instead of zero.  This is important since I disable all of the type
  ;; prescription rules and don't use forward chaining rules.  Instead, I tend
  ;; to prove simple rewrite rules of the form (equal (booleanp (fn x)) t).
  ;; With no hypotheses, these rules will always succeed as long as they are
  ;; given a chance to fire, but with a backchain limit of 0 they will not get
  ;; this chance.  Using a backchain limit of 1 fixes this.
  (implies (and (booleanp x)
                (booleanp y))
           (equal (equal x y)
                  (iff x y)))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable booleanp))))

(defthm booleanp-of-booleanp
  (equal (booleanp (booleanp x))
         t)
  :hints(("Goal" :in-theory (enable booleanp))))

(defthm booleanp-of-equal
  (equal (booleanp (equal x y))
         t)
  :hints(("Goal" :in-theory (enable booleanp))))

(defthm booleanp-of-not
  (equal (booleanp (not x))
         t))

(defthm booleanp-of-iff
  (equal (booleanp (iff x y))
         t))

(defthm booleanp-of-zp
  (equal (booleanp (zp x))
         t)
  :hints(("Goal" :in-theory (enable zp))))



;; Cons, Car, and Cdr.

(defthm booleanp-of-consp                                             ;; Axiom
  (equal (booleanp (consp x))
         t)
  :hints(("Goal" :in-theory (enable booleanp))))

(defthm car-when-not-consp                                            ;; Axiom
  (implies (not (consp x))
           (equal (car x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable car))))

(defthm cdr-when-not-consp                                            ;; Axiom
  (implies (not (consp x))
           (equal (cdr x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable cdr))))

(defthm car-of-cons                                                   ;; Axiom
  (equal (car (cons x y))
         x)
  :hints(("Goal" :in-theory (enable car))))

(defthm cdr-of-cons                                                   ;; Axiom
  (equal (cdr (cons x y))
         y)
  :hints(("Goal" :in-theory (enable cdr))))

(defthm car-cdr-elim                                                  ;; Axiom
  (implies (consp x)
           (equal (cons (car x) (cdr x))
                  x))
  :rule-classes :elim
  :hints(("Goal" :in-theory (enable car cdr))))

(defthm cons-of-car-and-cdr
  (implies (consp x)
           (equal (cons (car x) (cdr x))
                  x)))

(defthm equal-of-cons-rewrite
  ;; The syntaxp hypothesis prevents us from splitting up constants such as
  ;; ''NIL.  This wasn't really a problem as far as proofs succeeding, but it
  ;; made the proof output difficult to read.
  (implies (syntaxp (and (not (ACL2::quotep x))
                         (or (not (ACL2::quotep a))
                             (not (ACL2::quotep b)))))
           (equal (equal x (cons a b))
                  (and (consp x)
                       (equal (car x) a)
                       (equal (cdr x) b)))))

(defthmd equal-of-cons-rewrite-constants
  ;; Porting to ACL2 6.2, I found that lemma-6-for-ordered-map-submapp-property
  ;; in mergesort.lisp no longer proved, and was stuck on this goal:
  ;;
  ;; (IMPLIES (AND (NOT (CONSP CE))
  ;;               (EQUAL (CONS NIL CE3) '(NIL))
  ;;               CE3)
  ;;          (NOT (SUBMAPP (CONS '(NIL) CE2)
  ;;                        (CONS CE CE0)))).
  ;;
  ;; This should be taken care of by equal-of-cons-rewrite, but somehow it was
  ;; not, I guess because the unifier wasn't matching the constant against
  ;; Milawa's cons?  At any rate, add a rule that uses acl2::cons instead, to
  ;; try to help the unifier pick up constants.
  (equal (equal x (cons a b))
         (and (consp x)
              (equal (car x) a)
              (equal (cdr x) b))))


;; Symbolp and Symbol-<.

(defthm booleanp-of-symbolp                                           ;; Axiom
  (equal (booleanp (symbolp x))
         t)
  :hints(("Goal" :in-theory (enable booleanp symbolp))))

(defthm booleanp-of-symbol-<                                          ;; Axiom
  (equal (booleanp (symbol-< x y))
         t)
  :hints(("Goal" :in-theory (enable symbol-<))))

(defthm irreflexivity-of-symbol-<                                     ;; Axiom
  (equal (symbol-< x x)
         nil)
  :hints(("Goal" :in-theory (enable symbol-<))))

(defthm antisymmetry-of-symbol-<                                      ;; Axiom
  (implies (symbol-< x y)
           (equal (symbol-< y x)
                  nil))
  :hints(("Goal"
          :in-theory (e/d (symbol-< symbolp COMMON-LISP::string<)
                          (ACL2::string<-l
                           str::coerce-to-list-removal)))))

(defthm transitivity-of-symbol-<                                      ;; Axiom
  (implies (and (symbol-< x y)
                (symbol-< y z))
           (equal (symbol-< x z)
                  t))
  :hints(("Goal" :in-theory (e/d (symbol-< symbolp COMMON-LISP::string<)
                                 (ACL2::string<-l
                                  str::coerce-to-list-removal)))))

(encapsulate
 ()
 (local (defthm lemma
          (implies (and (ACL2::stringp x)
                        (ACL2::stringp y))
                   (equal (equal (ACL2::coerce x 'list)
                                 (ACL2::coerce y 'list))
                          (equal x y)))
          :hints(("Goal"
                  :in-theory (disable ACL2::coerce-inverse-2)
                  :use ((:instance ACL2::coerce-inverse-2 (ACL2::x x))
                        (:instance ACL2::coerce-inverse-2 (ACL2::x y)))))))

 (local (defthm lemma2
          (implies (and (ACL2::symbolp x)
                        (ACL2::symbolp y)
                        (equal (ACL2::symbol-package-name x)
                               (ACL2::symbol-package-name y)))
                   (equal (equal x y)
                          (equal (ACL2::symbol-name x)
                                 (ACL2::symbol-name y))))
          :hints(("Goal" :use ((:instance ACL2::symbol-equality
                                          (ACL2::s1 x)
                                          (ACL2::s2 y)))))))

 (defthm trichotomy-of-symbol-<                                       ;; Axiom
   (implies (and (symbolp x)
                 (symbolp y)
                 (not (symbol-< x y)))
            (equal (symbol-< y x)
                   (not (equal x y))))
   :hints(("Goal" :in-theory (e/d (symbol-< symbolp COMMON-LISP::string<)
                                  (ACL2::string<-l
                                   ACL2::member-symbol-name))))))

(defthm symbol-<-completion-left                                      ;; Axiom
  (implies (not (symbolp x))
           (equal (symbol-< x y)
                  (symbol-< nil y)))
  :hints(("Goal" :in-theory (enable symbol-<))))

(defthm symbol-<-completion-right                                     ;; Axiom
  (implies (not (symbolp y))
           (equal (symbol-< x y)
                  (symbol-< x nil)))
  :hints(("Goal" :in-theory (enable symbol-<))))




;; Reasoning about Types.

(defthm booleanp-of-natp                                              ;; Axiom
  (equal (booleanp (natp x))
         t)
  :hints(("Goal" :in-theory (enable natp))))

(defthm symbolp-when-natp-cheap                                       ;; Axiom
  (implies (natp x)
           (equal (symbolp x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable natp symbolp))))

(defthm symbolp-when-consp-cheap                                      ;; Axiom
  (implies (consp x)
           (equal (symbolp x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable symbolp))))

(defthm consp-when-natp-cheap                                         ;; Axiom
  (implies (natp x)
           (equal (consp x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable natp))))

(defthm booleanp-when-natp-cheap
  (implies (natp x)
           (equal (booleanp x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable booleanp))))

(defthm booleanp-when-consp-cheap
  (implies (consp x)
           (equal (booleanp x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable booleanp))))

(defthm symbolp-when-booleanp-cheap
  (implies (booleanp x)
           (equal (symbolp x)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable booleanp))))



;; Nfix and Zp.

(defthm natp-of-nfix
  (equal (natp (nfix a))
         t)
  :hints(("Goal" :in-theory (enable nfix))))

(defthm nfix-when-natp-cheap
  (implies (natp x)
           (equal (nfix x)
                  x))
  :hints(("Goal" :in-theory (enable nfix)))
  :rule-classes ((:rewrite :backchain-limit-lst 2)))

(defthm nfix-when-not-natp-cheap
  (implies (not (natp x))
           (equal (nfix x)
                  0))
  :hints(("Goal" :in-theory (enable nfix)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm equal-of-nfix-of-self
  ;; No symmetric rule because of term order
  (equal (equal x (nfix x))
         (natp x)))

(defthm equal-of-zero-and-nfix
  ;; No symmetric rule because of term order
  (equal (equal 0 (nfix x))
         (zp x))
  :hints(("Goal" :in-theory (enable nfix zp))))

(defthm zp-when-natp-cheap
  (implies (natp x)
           (equal (zp x)
                  (equal x 0)))
  :hints(("Goal" :in-theory (enable zp)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm zp-when-not-natp-cheap
  (implies (not (natp x))
           (equal (zp x)
                  t))
  :hints(("Goal" :in-theory (enable zp)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm zp-of-nfix
  (equal (zp (nfix x))
         (zp x))
  :hints(("Goal" :in-theory (enable nfix))))

(defthm nfix-of-nfix
  ;; I once wrote a note to myself to get rid of this rule, since we have
  ;; nfix-when-natp now.  But in retrospect I don't like that idea.  This rule
  ;; can still be applied by urewrite, etc.
  (equal (nfix (nfix a))
         (nfix a)))

(defthm natp-when-not-zp-cheap
  (implies (not (zp a))
           (equal (natp a)
                  t))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm natp-when-zp-cheap
  (implies (zp a)
           (equal (natp a)
                  (equal a 0)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm nfix-when-zp-cheap
  (implies (zp a)
           (equal (nfix a)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm equal-of-nfix-with-positive-constant
  (implies (and (syntaxp (ACL2::quotep c))
                (not (zp c)))
           (equal (equal c (nfix a))
                  (equal c a))))




;; Addition.

(defthm natp-of-plus                                                  ;; Axiom
  (equal (natp (+ a b))
         t)
  :hints(("Goal" :in-theory (enable + natp nfix))))

(defthm plus-under-iff
  (iff (+ a b)
       t)
  :hints(("Goal" :use ((:instance booleanp-when-natp-cheap (x (+ a b)))))))

(defthm commutativity-of-+                                            ;; Axiom
  (equal (+ a b)
         (+ b a))
  :hints(("Goal" :in-theory (enable +))))

(defthm associativity-of-+                                            ;; Axiom
  (equal (+ (+ a b) c)
         (+ a (+ b c)))
  :hints(("Goal" :in-theory (enable + natp nfix))))

(defthm commutativity-of-+-two
  (equal (+ a (+ b c))
         (+ b (+ a c)))
  :hints(("Goal" :use ((:instance commutativity-of-+ (a a) (b (+ b c)))))))

(defthm gather-constants-from-plus-of-plus
  (implies (and (syntaxp (ACL2::quotep x))
                (syntaxp (ACL2::quotep y)))
           (equal (+ x (+ y z))
                  (+ (+ x y) z))))



(encapsulate
 ()
 (local (defthmd plus-when-not-natp-left                              ;; Axiom
          (implies (not (natp a))
                   (equal (+ a b)
                          (+ 0 b)))
          :hints(("Goal" :in-theory (enable + natp nfix)))))

 (local (defthmd plus-of-zero-when-natural                            ;; Axiom
          (implies (natp a)
                   (equal (+ a 0)
                          a))
          :hints(("Goal" :in-theory (enable + natp nfix)))))

 (defthmd plus-completion-left
   (implies (not (natp a))
            (equal (+ a b)
                   (nfix b)))
   :hints(("Goal"
           :use ((:instance plus-when-not-natp-left)
                 (:instance plus-of-zero-when-natural (a b))
                 (:instance plus-when-not-natp-left (a b) (b 0))))))

 (defthmd plus-completion-right
   (implies (not (natp b))
            (equal (+ a b)
                   (nfix a)))
   :rule-classes ((:rewrite :backchain-limit-lst 1))
   :hints(("Goal" :use ((:instance plus-completion-left (a b) (b a))))))

 (defthm plus-of-zero-right
   (equal (+ a 0)
          (nfix a))
   :hints(("Goal"
           :in-theory (enable plus-completion-right)
           :use ((:instance plus-of-zero-when-natural)))))

 (defthm plus-of-zero-left
   (equal (+ 0 a)
          (nfix a))
   :hints(("Goal" :use ((:instance commutativity-of-+ (a 0) (b a))))))

 (defthm plus-when-zp-left-cheap
   (implies (zp a)
            (equal (+ a b)
                   (nfix b)))
   :hints(("Goal" :use ((:instance plus-completion-left))))
   :rule-classes ((:rewrite :backchain-limit-lst 1)))

 (defthm plus-when-zp-right-cheap
   (implies (zp b)
            (equal (+ a b)
                   (nfix a)))
   :hints(("Goal" :use ((:instance plus-completion-right))))
   :rule-classes ((:rewrite :backchain-limit-lst 1))))

(defthm plus-of-nfix-left
  (equal (+ (nfix a) b)
         (+ a b))
  :hints(("Goal" :in-theory (enable nfix))))

(defthm plus-of-nfix-right
  (equal (+ a (nfix b))
         (+ a b))
  :hints(("Goal" :in-theory (enable nfix))))




;; Less-Than Relation.

(local (defthm booleanp-of-acl2-<
         (equal (booleanp (ACL2::< x y))
                t)
         :hints(("Goal" :in-theory (enable booleanp)))))

(defthm booleanp-of-<                                                 ;; Axiom
  (equal (booleanp (< x y))
         t)
  :hints(("Goal" :in-theory (enable <))))

(defthm irreflexivity-of-<                                            ;; Axiom
  (equal (< a a)
         nil)
  :hints(("Goal" :in-theory (enable <))))

(defthm less-of-zero-right                                            ;; Axiom
  (equal (< a 0)
         nil)
  :hints(("Goal" :in-theory (enable < natp nfix))))

(encapsulate
 ()
 (defthmd less-completion-right                                         ;; Axiom
   (implies (not (natp b))
            (equal (< a b)
                   nil))
   :rule-classes ((:rewrite :backchain-limit-lst 1))
   :hints(("Goal" :in-theory (enable natp < nfix))))

 (defthm less-when-zp-right-cheap
   (implies (zp b)
            (equal (< a b)
                   nil))
   :hints(("Goal" :use ((:instance less-completion-right))))
   :rule-classes ((:rewrite :backchain-limit-lst 1))))


(encapsulate
 ()
 (local (defthm less-of-zero-left-when-natp                           ;; Axiom
          (implies (natp a)
                   (equal (< 0 a)
                          (not (equal a 0))))
          :hints(("Goal" :in-theory (enable natp < nfix)))))

 (defthm less-of-zero-left
   (equal (< 0 a)
          (not (zp a)))))


(encapsulate
 ()
 (defthmd less-completion-left                                        ;; Axiom
   (implies (not (natp a))
            (equal (< a b)
                   (< 0 b)))
   :rule-classes ((:rewrite :backchain-limit-lst 1))
   :hints(("Goal" :in-theory (enable <))))

 (defthm less-when-zp-left-cheap
   (implies (zp a)
            (equal (< a b)
                   (not (zp b))))
   :hints(("Goal" :use ((:instance less-completion-left))))))

(defthm less-of-nfix-left
  (equal (< (nfix a) b)
         (< a b))
  :hints(("Goal" :in-theory (enable nfix))))

(defthm less-of-nfix-right
  (equal (< a (nfix b))
         (< a b))
  :hints(("Goal" :in-theory (enable nfix))))

(defthm transitivity-of-<                                             ;; Axiom
  (implies (and (< a b)
                (< b c))
           (equal (< a c)
                  t))
  :hints(("Goal" :in-theory (enable <))))

(defthm antisymmetry-of-<
  (implies (< a b)
           (equal (< b a)
                  nil))
  :hints(("Goal" :use ((:instance transitivity-of-< (a a) (b b) (c a)))))
  :rule-classes ((:rewrite :backchain-limit-lst 3)))

(encapsulate
 ()
 (local (defthm trichotomy-of-<-when-natp                             ;; Axiom
          (implies (and (natp a)
                        (natp b)
                        (not (< a b))
                        (not (equal a b)))
                   (equal (< b a)
                          t))
          :hints(("Goal" :in-theory (enable < natp nfix)))))

  (defthm trichotomy-of-<
    ;; The order of these hyps reduces backchaining
    (implies (and (not (equal (nfix a) (nfix b)))
                  (not (< a b)))
             (equal (< b a)
                    t))
    :hints(("Goal" :in-theory (enable nfix)))))

(defthm one-plus-trick                                                ;; Axiom
  (implies (< a b)
           (equal (< b (+ 1 a))
                  nil))
  :hints(("Goal" :in-theory (enable < + natp nfix))))

(encapsulate
 ()
 (defthm natural-less-than-one-is-zero                                ;; Axiom
   (implies (and (natp a)
                 (< a 1))
            (equal a 0))
   :rule-classes nil
   :hints(("Goal" :in-theory (enable < + natp nfix))))

 (defthm less-of-one-right
   (equal (< a 1)
          (zp a))
   :hints(("Goal" :use ((:instance natural-less-than-one-is-zero))))))

(defthm less-of-one-left
  (equal (< 1 a)
         (and (not (zp a))
              (not (equal a 1))))
  :hints(("Goal" :in-theory (enable zp))))

(defthm transitivity-of-<-two
  (implies (and (< a b)
                (not (< c b)))
           (equal (< a c)
                  t))
  :hints(("Goal"
          :in-theory (e/d (nfix)
                          (trichotomy-of-<))
          :use ((:instance trichotomy-of-< (a b) (b c))))))

(defthm transitivity-of-<-three
  (implies (and (not (< b a))
                (< b c))
           (equal (< a c)
                  t)))

(defthm transitivity-of-<-four
  (implies (and (not (< b a))
                (not (< c b)))
           (equal (< c a)
                  nil)))



;; Less-Than and Addition.

(defthm |(< (+ a b) (+ a c))|                                         ;; Axiom
  (equal (< (+ a b) (+ a c))
         (< b c))
  :hints(("Goal" :in-theory (enable < + natp nfix))))

(defthm |(< a (+ a b))|
  (equal (< a (+ a b))
         (< 0 b))
  :hints(("Goal" :use ((:instance |(< (+ a b) (+ a c))| (b 0) (c b))))))

(defthm |(< a (+ b a))|
  (equal (< a (+ b a))
         (< 0 b)))

(defthm |(< (+ a b) a)|
  (equal (< (+ a b) a)
         nil)
  :hints(("Goal" :use ((:instance |(< (+ a b) (+ a c))| (c 0))))))

(defthm |(< (+ b a) a)|
  (equal (< (+ b a) a)
         nil))

(defthm |(< a (+ b c a))|
  (equal (< a (+ b (+ c a)))
         (< 0 (+ b c))))

(defthm |(< a (+ b a c))|
  (equal (< a (+ b (+ a c)))
         (< 0 (+ b c))))

(defthm |(< a (+ b c d a))|
  (equal (< a (+ b (+ c (+ d a))))
         (< 0 (+ b (+ c d)))))

(defthm |(< a (+ b c a d))|
  (equal (< a (+ b (+ c (+ a d))))
         (< 0 (+ b (+ c d)))))

(defthm |(< a (+ b c d e a))|
  (equal (< a (+ b (+ c (+ d (+ e a)))))
         (< 0 (+ b (+ c (+ d e))))))

(defthm |(< a (+ b c d a e))|
  (equal (< a (+ b (+ c (+ d (+ a e)))))
         (< 0 (+ b (+ c (+ d e))))))

(defthm |(< a (+ b c d e f a))|
  (equal (< a (+ b (+ c (+ d (+ e (+ f a))))))
         (< 0 (+ b (+ c (+ d (+ e f)))))))

(defthm |(< a (+ b c d e a f))|
  (equal (< a (+ b (+ c (+ d (+ e (+ a f))))))
         (< 0 (+ b (+ c (+ d (+ e f)))))))

(defthm |(< (+ a b) (+ c a))|
  (equal (< (+ a b) (+ c a))
         (< b c)))

(defthm |(< (+ b a) (+ c a))|
  (equal (< (+ b a) (+ c a))
         (< b c)))

(defthm |(< (+ b a) (+ a c))|
  (equal (< (+ b a) (+ a c))
         (< b c)))

(defthm |(< (+ a b) (+ c a d))|
  (equal (< (+ a b) (+ c (+ a d)))
         (< b (+ c d))))

(defthm |(< (+ b a c) (+ d a))|
  (equal (< (+ b (+ a c)) (+ d a))
         (< (+ b c) d)))

(defthm |a <= b, c != 0 --> a < b+c|
  (implies (and (not (< b a))
                (not (zp c)))
           (equal (< a (+ b c))
                  t))
  :hints(("Goal" :in-theory (enable zp))))

(defthm |a <= b, c != 0 --> a < c+b|
  (implies (and (not (< b a))
                (not (zp c)))
           (equal (< a (+ c b))
                  t)))

(defthm |a <= b, c != 0 --> a < c+b+d|
  (implies (and (not (< b a))
                (not (zp c)))
           (equal (< a (+ c (+ b d)))
                  t)))

(defthm |a <= b, c != 0 --> a < c+d+b|
  (implies (and (not (< b a))
                (not (zp c)))
           (equal (< a (+ c (+ d b)))
                  t)))

(defthm |c < a, d <= b --> c+d < a+b|
  (implies (and (< c a)
                (not (< b d)))
           (equal (< (+ c d) (+ a b))
                  t))
  :hints(("Goal" :use ((:instance transitivity-of-<-three
                                  (a (+ c d))
                                  (b (+ c b))
                                  (c (+ a b)))))))

(defthm |c < a, d <= b --> c+d < b+a|
  (implies (and (< c a)
                (not (< b d)))
           (equal (< (+ c d) (+ b a))
                  t)))

(defthm |c <= a, d < b --> c+d < a+b|
  (implies (and (not (< a c))
                (< d b))
           (equal (< (+ c d) (+ a b))
                  t))
  :hints(("Goal" :use ((:instance |c < a, d <= b --> c+d < a+b|
                                  (c d) (a b) (d c) (b a))))))

(defthm |c <= a, d < b --> c+d < b+a|
  (implies (and (not (< a c))
                (< d b))
           (equal (< (+ c d) (+ b a))
                  t)))

(defthm |c <= a, d <= b --> c+d <= a+b|
  (implies (and (not (< a c))
                (not (< b d)))
           (equal (< (+ a b) (+ c d))
                  nil))
  :hints(("Goal" :use ((:instance transitivity-of-<-four
                                  (a (+ c d))
                                  (b (+ c b))
                                  (c (+ a b)))))))

(defthm |c <= a, d <= b --> c+d <= b+a|
  (implies (and (not (< a c))
                (not (< b d)))
           (equal (< (+ b a) (+ c d))
                  nil)))




;; Equalities with Sums.

(defthm |(= a (+ a b))|
  (equal (equal a (+ a b))
         (and (natp a)
              (zp b)))
  :hints(("Goal"
          :in-theory (disable |(< a (+ a b))|)
          :use ((:instance |(< a (+ a b))|)))))

(defthm |(= a (+ b a))|
  (equal (equal a (+ b a))
         (and (natp a)
              (zp b))))

(encapsulate
 ()
 (defthm |lemma for (= (+ a b) (+ a c))|
   (implies (and (natp b)
                 (natp c)
                 (equal (+ a b) (+ a c)))
            (equal b c))
   :rule-classes nil
   :hints(("Goal"
           :in-theory (disable |(< (+ a b) (+ a c))|)
           :use ((:instance |(< (+ a b) (+ a c))| (a a) (b b) (c c))
                 (:instance |(< (+ a b) (+ a c))| (a a) (b c) (c b))))))

 (defthm |(= (+ a b) (+ a c))|
   (equal (equal (+ a b) (+ a c))
          (equal (nfix b) (nfix c)))
   :hints(("Goal"
           :in-theory (enable nfix)
           :use ((:instance |lemma for (= (+ a b) (+ a c))|
                            (a a)
                            (b (nfix b))
                            (c (nfix c))))))))

(defthm |(= (+ a b) (+ c a))|
  (equal (equal (+ a b) (+ c a))
         (equal (nfix b) (nfix c))))

(defthm |(= (+ b a) (+ c a))|
  (equal (equal (+ b a) (+ c a))
         (equal (nfix b) (nfix c))))

(defthm |(= (+ b a) (+ a c))|
  (equal (equal (+ b a) (+ a c))
         (equal (nfix b) (nfix c))))

(encapsulate
 ()
 (local (defthm lemma
          ;; Milawa can prove it without this lemma
          (implies (and (not (zp a))
                        (not (zp b)))
                   (equal (equal 0 (+ a b))
                          nil))
          :hints (("Goal"
                   :in-theory (disable |(< (+ a b) (+ a c))|
                                       |(< (+ b a) (+ c a))|
                                       |(< a (+ a b))|)
                   :use ((:instance |(< (+ a b) (+ a c))| (a b) (b 0) (c a)))))))

 (defthm |(= 0 (+ a b))|
   (equal (equal 0 (+ a b))
          (and (zp a)
               (zp b)))
   :hints(("Goal" :use ((:instance lemma))))))

(encapsulate
 ()
 (defthmd |lemma for (= (+ a x b) (+ c x d))|
   ;; hackery with names to make it commute them nicely
   (equal (equal (+ e (+ b c))
                 (+ d (+ b f)))
          (equal (+ e c)
                 (+ d f))))

 (defthm |(= (+ a x b) (+ c x d))|
   (equal (equal (+ a (+ x b))
                 (+ c (+ x d)))
          (equal (+ a b)
                 (+ c d)))
   :hints(("Goal" :in-theory (enable |lemma for (= (+ a x b) (+ c x d))|)))))



;; Squeeze laws.

(defthm squeeze-law-one
  (implies (not (< b a))
           (equal (< (+ 1 a) b)
                  (and (not (equal (nfix a) (nfix b)))
                       (not (equal (+ 1 a) (nfix b))))))
  :hints(("Goal" :in-theory (enable nfix))))

(defthm squeeze-law-two
  (implies (not (< b a))
           (equal (< b (+ 1 a))
                  (equal (nfix b) (nfix a))))
  :hints(("Goal" :in-theory (enable nfix))))

(defthm squeeze-law-three
  (implies (< a b)
           (equal (< (+ 1 a) b)
                  (not (equal (nfix b) (+ 1 a)))))
  :hints(("Goal" :in-theory (enable nfix))))



;; Subtraction.

(defthm natp-of-minus                                                 ;; Axiom
  (equal (natp (- a b))
         t)
  :hints(("Goal" :in-theory (enable -))))

(defthm minus-under-iff
  (iff (- a b)
       t)
  :hints(("Goal" :use ((:instance booleanp-when-natp-cheap
                                  (x (- a b)))))))

(defthm minus-when-not-less                                           ;; Axiom
  (implies (not (< b a))
           (equal (- a b)
                  0))
  :hints(("Goal" :in-theory (enable - < natp nfix zp))))

(defthm minus-of-self
  (equal (- a a)
         0))

(defthm minus-of-zero-left
  (equal (- 0 a)
         0))

(defthm minus-cancels-summand-right                                   ;; Axiom
  (equal (- (+ a b) b)
         (nfix a))
  :hints(("Goal" :in-theory (enable - + < natp nfix))))

(defthm minus-of-zero-right
  (equal (- a 0)
         (nfix a))
  :hints(("Goal"
          :in-theory (e/d (nfix) (minus-cancels-summand-right))
          :use ((:instance minus-cancels-summand-right (a a) (b 0))))))

(encapsulate
 ()
 (local (ACL2::allow-fertilize t))
 (defthm minus-cancels-summand-left
   (equal (- (+ a b) a)
          (nfix b))
   :hints(("Goal"
           :in-theory (disable commutativity-of-+
                               |(= (+ b a) (+ a c))|
                               |(= (+ a b) (+ c a))|)
           :use ((:instance commutativity-of-+))))))



(encapsulate
 ()
 (local (defthm less-of-minus-less                                    ;; Axiom
          (implies (< b a)
                   (equal (< (- a b) c)
                          (< a (+ b c))))
          :hints(("Goal" :in-theory (enable < + - natp nfix)))))

 (defthm |(< (- a b) c)|
   (equal (< (- a b) c)
          (if (< a b)
              (< 0 c)
            (< a (+ b c))))
   :hints(("Goal" :cases ((< b a))))))

(defthm |(< a (- b c))|                                               ;; Axiom
  (equal (< a (- b c))
         (< (+ a c) b))
  :hints(("Goal" :in-theory (enable < + - natp nfix))))



(encapsulate
 ()
 (local (defthm plus-of-minus-right                                   ;; Axiom
          (implies (< c b)
                   (equal (+ a (- b c))
                          (- (+ a b) c)))
          :hints(("Goal" :in-theory (enable + - < natp nfix)))))

 (defthm |(+ a (- b c))|
   (equal (+ a (- b c))
          (if (< c b)
              (- (+ a b) c)
            (nfix a)))))

(defthm |(+ (- a b) c)|
  (equal (+ (- a b) c)
         (if (< b a)
             (- (+ a c) b)
           (nfix c))))



(encapsulate
 ()
 (local (defthm minus-of-minus-right                                  ;; Axiom
          (implies (< c b)
                   (equal (- a (- b c))
                          (- (+ a c) b)))
          :hints(("Goal" :in-theory (enable + - < natp nfix)))))

 (defthm |(- a (- b c))|
   (equal (- a (- b c))
          (if (< c b)
              (- (+ a c) b)
            (nfix a)))))

(defthm |(- (- a b) c)|                                               ;; Axiom
  (equal (- (- a b) c)
         (- a (+ b c)))
  :hints(("Goal" :in-theory (enable + - < natp nfix zp))))



(encapsulate
 ()
 (local (defthm equal-of-minus-property                               ;; Axiom
          (implies (< b a)
                   (equal (equal (- a b) c)
                          (equal a (+ b c))))
          :hints(("Goal" :in-theory (enable + < - natp nfix)))))

 (defthm |(= (- a b) c)|
   (equal (equal (- a b) c)
          (if (< b a)
              (equal a (+ b c))
            (equal c 0)))))

(defthm |(= c (- a b))|
  (equal (equal c (- a b))
         (if (< b a)
             (equal a (+ b c))
           (equal c 0))))



(defthm |(- (+ a b) (+ a c))|
  (equal (- (+ a b) (+ a c))
         (- b c)))

(defthm |(- (+ a b) (+ c a))|
  (equal (- (+ a b) (+ c a))
         (- b c)))

(defthm |(- (+ b a) (+ c a))|
  (equal (- (+ b a) (+ c a))
         (- b c)))

(defthm |(- (+ b a) (+ a c))|
  (equal (- (+ b a) (+ a c))
         (- b c)))

(defthm |(- (+ a b) (+ c d a))|
  (equal (- (+ a b) (+ c (+ d a)))
         (- b (+ c d))))

(defthm |a < b --> a <= b-1|
  (implies (< a b)
           (equal (< (- b 1) a)
                  nil)))


(defthm minus-when-zp-left-cheap
  (implies (zp a)
           (equal (- a b)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm minus-when-zp-right-cheap
  (implies (zp b)
           (equal (- a b)
                  (nfix a)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm minus-of-nfix-left
  (equal (- (nfix a) b)
         (- a b)))

(defthm minus-of-nfix-right
  (equal (- a (nfix b))
         (- a b)))








;; Constant Gathering.  We break our normal forms when we can put two constants
;; next to one another, since they can then be evaluated away to make progress.

(defthm gather-constants-from-less-of-plus
  (implies (and (syntaxp (ACL2::quotep const))
                (syntaxp (ACL2::quotep const2)))
           (equal (< (+ const x) const2)
                  (and (< const const2)
                       (< x (- const2 const))))))

(defthm gather-constants-from-less-of-plus-two
  (implies (and (syntaxp (ACL2::quotep const))
                (syntaxp (ACL2::quotep const2)))
           (equal (< const (+ const2 x))
                  (or (< const const2)
                      (< (- const const2) x)))))

(defthm gather-constants-from-less-of-plus-and-plus
  (implies (and (syntaxp (ACL2::quotep a))
                (syntaxp (ACL2::quotep b)))
           (equal (< (+ a x) (+ b y))
                  (if (< a b)
                      (< x (+ (- b a) y))
                    (< (+ (- a b) x) y)))))

(encapsulate
 ()
 (defthm lemma-for-gather-constants-from-equal-of-plus-and-plus
   (implies (< c1 c2)
            (equal (equal (+ c1 x) (+ c2 y))
                   (equal (nfix x) (+ (- c2 c1) y))))
   :rule-classes nil)

 (defthm lemma2-for-gather-constants-from-equal-of-plus-and-plus
   (implies (and (not (< c1 c2)))
            (equal (equal (+ c1 x) (+ c2 y))
                   (equal (+ (- c1 c2) x) (nfix y))))
   :rule-classes nil
   :hints(("Goal"
           :in-theory (e/d (nfix) (trichotomy-of-<))
           :use ((:instance trichotomy-of-< (a c1) (b c2))))))

 (defthm gather-constants-from-equal-of-plus-and-plus
   (implies (and (syntaxp (ACL2::quotep c1))
                 (syntaxp (ACL2::quotep c2)))
            (equal (equal (+ c1 x) (+ c2 y))
                   (if (< c1 c2)
                       (equal (nfix x) (+ (- c2 c1) y))
                     (equal (+ (- c1 c2) x) (nfix y)))))
   :hints(("Goal" :use ((:instance lemma-for-gather-constants-from-equal-of-plus-and-plus)
                        (:instance lemma2-for-gather-constants-from-equal-of-plus-and-plus))))))

(defthm gather-constants-from-equal-of-plus
  (implies (and (syntaxp (ACL2::quotep const))
                (syntaxp (ACL2::quotep const2)))
           (equal (equal (+ const x) const2)
                  (and (not (< const2 const))
                       (natp const2)
                       (equal (nfix x)
                              (- const2 const))))))

(defthm gather-constants-from-minus-of-plus
  (implies (and (syntaxp (ACL2::quotep const))
                (syntaxp (ACL2::quotep const2)))
           (equal (- (+ const x) const2)
                  (if (< const2 const)
                      (+ (- const const2) x)
                    (- x (- const2 const))))))

(defthm gather-constants-from-minus-of-plus-two
  (implies (and (syntaxp (ACL2::quotep const))
                (syntaxp (ACL2::quotep const2)))
           (equal (- const (+ const2 x))
                  (if (< const2 const)
                      (- (- const const2) x)
                    0))))

(defthm gather-constants-from-minus-of-plus-and-plus
  (implies (and (syntaxp (ACL2::quotep const))
                (syntaxp (ACL2::quotep const2)))
           (equal (- (+ const a) (+ const2 b))
                  (if (< const const2)
                      (- a (+ (- const2 const) b))
                    (- (+ (- const const2) a) b)))))





(defthm not-equal-when-less
  (implies (< x y)
           (equal (equal x y)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm not-equal-when-less-two
  (implies (< y x)
           (equal (equal x y)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))



(defthm |a <= d, b+c <= e --> b+a+c <= d+e|
  (implies (and (not (< d a))
                (not (< e (+ b c))))
           (equal (< (+ d e) (+ b (+ a c)))
                  nil)))

(defthm |(< (+ a b) (+ c b d))|
  (equal (< (+ a b) (+ c (+ b d)))
         (< a (+ c d))))

(defthm |(< (+ a b c)) (+ d c))|
  (equal (< (+ a (+ b c)) (+ d c))
         (< (+ a b) d))
  :hints(("Goal"
          :in-theory (disable |(< (+ b a c) (+ d a))|)
          :use ((:instance |(< (+ b a c) (+ d a))|
                           (a c) (b a) (c b) (d d))))))

(defthm |a <= b, b <= c --> a < 1+c|
  (implies (and (not (< b a))
                (not (< c b)))
           (equal (< a (+ 1 c))
                  t)))

(defthm |b <= c, a <= b --> a < 1+c|
  (implies (and (not (< c b))
                (not (< b a)))
           (equal (< a (+ 1 c))
                  t)))



(definline max (a b)                        ;; note: we leave max enabled
  (declare (xargs :guard t))
  (if (< a b)
      (nfix b)
    (nfix a)))

(defthm natp-of-max
  (equal (natp (max a b))
         t)
  :hints(("Goal" :in-theory (enable max))))

(defthm equal-of-max-and-zero
  (equal (equal (max a b) 0)
         (and (zp a)
              (zp b)))
  :hints(("Goal" :in-theory (enable max))))

(defthm max-of-zero-left
  (equal (max 0 a)
         (nfix a)))

(defthm max-of-zero-right
  (equal (max a 0)
         (nfix a)))



(definline min (a b)                        ;; note: we leave min enabled
  (declare (xargs :guard t))
  (if (< a b)
      (nfix a)
    (nfix b)))

(defthm natp-of-min
  (equal (natp (min a b))
         t)
  :hints(("Goal" :in-theory (enable min))))

(defthm equal-of-min-and-zero
  (equal (equal (min a b) 0)
         (or (zp a)
             (zp b)))
  :hints(("Goal" :in-theory (enable min))))

(defthm min-of-zero-left
  (equal (min 0 a)
         0))

(defthm min-of-zero-right
  (equal (min a 0)
         0))


(definline max3 (a b c)                     ;; note: we leave max3 enabled
  (declare (xargs :guard t))
  (max a (max b c)))








;; We now introduce ordinals and our rank function.

(defund ord< (x y)
  (declare (xargs :guard t))
  (cond ((not (consp x))
         (if (consp y)
             t
           (< x y)))
        ((not (consp y))
         nil)
        ((not (equal (car (car x))
                     (car (car y))))
         (ord< (car (car x))
               (car (car y))))
        ((not (equal (cdr (car x))
                     (cdr (car y))))
         (< (cdr (car x))
            (cdr (car y))))
        (t
          (ord< (cdr x) (cdr y)))))

(defthm booleanp-of-ord<
  (equal (booleanp (ord< x y))
         t)
  :hints(("Goal" :in-theory (enable ord<))))

(defthm ord<-when-naturals
  (implies (and (natp x)
                (natp y))
           (equal (ord< x y)
                  (< x y)))
  :hints(("Goal" :in-theory (enable ord<))))



(defund ordp (x)
  (declare (xargs :guard t))
  (if (not (consp x))
      (natp x)
    (and (consp (car x))
         (ordp (car (car x)))
         (not (equal (car (car x)) 0))
         (< 0 (cdr (car x)))
         (ordp (cdr x))
         (if (consp (cdr x))
             (ord< (car (car (cdr x)))
                   (car (car x)))
          t))))

(defthm booleanp-of-ordp
  (equal (booleanp (ordp x))
         t)
  :hints(("Goal" :in-theory (enable ordp))))


(defthm ordp-when-natp
  (implies (natp x)
           (equal (ordp x)
                  t))
  :hints(("Goal" :in-theory (enable ordp))))




(defund rank (x)
  (declare (xargs :guard t))
  (if (consp x)
      (+ 1
         (+ (rank (car x))
            (rank (cdr x))))
    0))

(defthm natp-of-rank
  (equal (natp (rank x))
         t)
  :hints(("Goal" :in-theory (enable rank))))

(defthm rank-when-not-consp
  (implies (not (consp x))
           (equal (rank x)
                  0))
  :hints(("Goal" :in-theory (enable rank))))

(defthm rank-of-cons
  (equal (rank (cons x y))
         (+ 1
            (+ (rank x)
               (rank y))))
  :hints(("Goal" :in-theory (enable rank))))

(defthm |(< 0 (rank x))|
  (equal (< 0 (rank x))
         (consp x))
  :hints(("Goal" :in-theory (enable rank))))

(defthm ordp-of-rank
  (equal (ordp (rank x))
         t)
  :hints(("Goal" :in-theory (enable ordp))))

(defthm rank-of-car
  (equal (< (rank (car x)) (rank x))
         (consp x))
  :hints(("Goal" :in-theory (enable rank))))

(defthm rank-of-car-weak
  (equal (< (rank x) (rank (car x)))
         nil)
  :hints(("Goal" :in-theory (enable rank))))

(defthm rank-of-cdr
  (equal (< (rank (cdr x)) (rank x))
         (consp x))
  :hints(("Goal" :in-theory (enable rank))))

(defthm rank-of-cdr-weak
  (equal (< (rank x) (rank (cdr x)))
         nil)
  :hints(("Goal" :in-theory (enable rank))))

(defthm rank-of-second
  (equal (< (rank (second x)) (rank x))
         (consp x))
  :hints(("Goal"
          :in-theory (disable transitivity-of-<-four)
          :use ((:instance transitivity-of-<-three
                           (a (rank (car (cdr x))))
                           (b (rank (cdr x)))
                           (c (rank x)))))))

(defthm rank-of-second-weak
  (equal (< (rank x) (rank (second x)))
         nil)
  :hints(("Goal"
          :use ((:instance transitivity-of-<-four
                           (a (rank (second x)))
                           (b (rank (cdr x)))
                           (c (rank x)))))))

(defthm rank-of-third
  (equal (< (rank (third x)) (rank x))
         (consp x))
  :hints(("Goal"
          :in-theory (disable transitivity-of-<-four)
          :use ((:instance transitivity-of-<-three
                           (a (rank (third x)))
                           (b (rank (cdr x)))
                           (c (rank x)))))))

(defthm rank-of-third-weak
  (equal (< (rank x) (rank (third x)))
         nil)
  :hints(("Goal"
          :use ((:instance transitivity-of-<-four
                           (a (rank (third x)))
                           (b (rank (cdr x)))
                           (c (rank x)))))))

(defthm rank-of-fourth
  (equal (< (rank (fourth x)) (rank x))
         (consp x))
  :hints(("Goal"
          :in-theory (disable transitivity-of-<-two)
          :use ((:instance transitivity-of-<-two
                           (a (rank (fourth x)))
                           (b (rank (cdr x)))
                           (c (rank x)))))))

(defthm rank-of-fourth-weak
  (equal (< (rank x) (rank (fourth x)))
         nil)
  :hints(("Goal"
          :use ((:instance transitivity-of-<-four
                           (a (rank (fourth x)))
                           (b (rank (cdr x)))
                           (c (rank x)))))))




(encapsulate
 ()
 ;; We now instruct ACL2 to use our ord< function as its well founded relation.

 (local (in-theory (enable car cdr)))

 (local (defthm lemma
          (implies (and (ordp x)
                        (ordp y))
                   (equal (ord< x y)
                          (acl2::o< x y)))
          :hints(("Goal" :in-theory (enable ordp ord< < natp nfix zp)))))

 (local (defthm lemma2
          (equal (ordp x)
                 (ACL2::o-p x))
          :hints(("Goal" :in-theory (enable ordp ord< < natp nfix zp)))))

 (defthm ord<-is-well-founded
   (and (implies (ordp x)
                 (ACL2::o-p (ACL2::identity x)))
        (implies (and (ordp x)
                      (ordp y)
                      (ord< x y))
                 (ACL2::o< (ACL2::identity x)
                           (ACL2::identity y))))
   :rule-classes :well-founded-relation))

(set-well-founded-relation ord<)
(set-measure-function rank)




(defund two-nats-measure (a b)
  ;; We create the ordinal w*(1+a) + b.  When ord< is applied to such ordinals,
  ;; the lexiographic ordering of <a, b> is induced.  So, the two-nats-measure
  ;; function can be used to admit new functions whose termination relies on
  ;; two natural-valued expressions together.
  (declare (xargs :guard t))
  (cons (cons 1 (+ 1 (nfix a)))
        (nfix b)))

(defthm ordp-of-two-nats-measure
  (equal (ordp (two-nats-measure a b))
         t)
  :hints(("Goal" :in-theory (enable two-nats-measure ordp))))

(defthm ord<-of-two-nats-measure
  (equal (ord< (two-nats-measure a1 b1)
               (two-nats-measure a2 b2))
         (or (< a1 a2)
             (and (equal (nfix a1) (nfix a2))
                  (< b1 b2))))
  :hints(("Goal" :in-theory (enable two-nats-measure ord<))))




(defund three-nats-measure (a b c)
  ;; We create the ordinal w^2(1+a) + w*(1+b) + c.  When ord< is applied to
  ;; such ordinals, the lexiographic ordering of <a, b, c> is induced.
  (declare (xargs :guard t))
  (cons (cons 2 (+ 1 (nfix a)))
        (cons (cons 1 (+ 1 (nfix b)))
              (nfix c))))

(defthm ordp-of-three-nats-measure
  (equal (ordp (three-nats-measure a b c))
         t)
  :hints(("Goal" :in-theory (enable three-nats-measure ordp))))

(defthm ord<-of-three-nats-measure
  (equal (ord< (three-nats-measure a1 b1 c1)
               (three-nats-measure a2 b2 c2))
         (or (< a1 a2)
             (and (equal (nfix a1) (nfix a2))
                  (or (< b1 b2)
                      (and (equal (nfix b1) (nfix b2))
                           (< c1 c2))))))
  :hints(("Goal" :in-theory (enable three-nats-measure ord<))))





;; We provide several commonly useful induction scheme.

(defun cdr-induction (x)
  (declare (xargs :guard t))
  (if (consp x)
      (cdr-induction (cdr x))
    nil))

(defun cdr-cdr-induction (a b)
  (declare (xargs :guard t))
  (if (and (consp a)
           (consp b))
      (cdr-cdr-induction (cdr a) (cdr b))
    nil))

(defun cdr-cdr-cdr-induction (x y z)
  (declare (xargs :guard t))
  (if (and (consp x)
           (consp y)
           (consp z))
      (cdr-cdr-cdr-induction (cdr x) (cdr y) (cdr z))
    nil))

(defun four-cdrs-induction (a b c d)
  (declare (xargs :guard t))
  (if (and (consp a)
           (consp b)
           (consp c)
           (consp d))
      (four-cdrs-induction (cdr a) (cdr b) (cdr c) (cdr d))
    nil))

(defun dec-induction (a)
  (declare (xargs :guard t :measure (nfix a)))
  (if (zp a)
      nil
    (dec-induction (- a 1))))

(defun dec-dec-induction (a b)
  (declare (xargs :guard t :measure (nfix a)))
  (if (or (zp a)
          (zp b))
      nil
    (dec-dec-induction (- a 1) (- b 1))))

(defun sub-induction (a b)
  (declare (xargs :guard t :measure (nfix a)))
  (cond ((zp b) nil)
        ((< a b) nil)
        (t (sub-induction (- a b) b))))

(defun car-cdr-induction (x)
  (declare (xargs :guard t))
  (if (consp x)
      (list (car-cdr-induction (car x))
            (car-cdr-induction (cdr x)))
    t))





