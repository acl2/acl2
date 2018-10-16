; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
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

;; basic.lisp
;; Basic Lists Reasoning

(in-package "LIST")
(include-book "std/lists/list-defuns" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(include-book "../util/debug")
(include-book "acl2-count")

;; bzo (ews and jcd) We would like to disable true-listp as well, but we're
;; afraid it may break a lot of stuff, so we haven't tried it yet.

(in-theory (disable nthcdr append))


;; Standard Rules
;;
;; The following are "standard" rules that we typically want to have in every
;; proof effort that we have engaged in.  We feel that this is a nice place
;; for these rules, because we very often want to reason about lists.

;; bzo (jcd) - Do we have this rule in many other places?  Would it be good
;; to "standardize" and use this one location (or put these someplace else)?

(local (include-book "../util/iff"))

;; Note (jcd and ews): At one point, we tried strengthened this rule by moving
;; the consp hypothesis into the conclusion.  The modified rule was:
;;
;; (defthm equal-cons-cases
;;   (equal (equal (cons a b) c)
;;          (and (consp c)
;;               (equal a (car c))
;;               (equal b (cdr c)))))
;;
;; This rule turned out to be too strong.  It caused some proofs to fail, but
;; worse was the way that it slowed down proofs.  For example, bags/meta.lisp
;; originally took about 170 seconds, but using the new rule the time ballooned
;; to 1,200 seconds.  We have concluded that the original rule is what we
;; wanted, and so we have not changed the following:
; Hmmm.  Maybe the problem was that ACL2 unifies constant lists with cons?  Maybe a syntaxp test would help?  -ews

(defthm equal-cons-cases
  (implies (consp c)
           (equal (equal (cons a b) c)
                  (and (equal a (car c))
                       (equal b (cdr c))))))



;; As expected, ACL2 now has CONS-CAR-CDR, so we comment out all this stuff. -ews
;;
;; ;; bzo (ews and jcd) - This rule is inspired by the built in axiom
;; ;; car-cdr-elim.  We think that the case splitting version is better.  We have
;; ;; asked Matt Kaufmann to change ACL2 to provide the new rule instead, and
;; ;; he may change car-cdr-elim at some point in the future.
;; ;;
;; ;; So, when version 2.9.3 comes out, someone should check to see if this rule
;; ;; is now built in, and if so, remove this!

;; (defthm car-cdr-elim-better
;;   (equal (cons (car x) (cdr x))
;;          (if (consp x)
;;              x
;;            (cons nil nil))))

;; ;; Note that we leave the :elim rule enabled -- we only want to replace the
;; ;; rewrite rule because we don't really know how the elim rule works.

;; (in-theory (disable (:rewrite car-cdr-elim)))



;; (jcd) - Originally there was a backchaining limit here of 0.  I have taken
;; this out.  I think that trying to establish (not (consp x)) should be
;; fairly cheap usually, even if some backchaining is allowed to occur.  And,
;; unless things are dramatically slower, I think that removing the limit is
;; justified on the grounds that this is clearly a strong "progress making"
;; rule, and we will want to have it fire whenever possible.

(defthm true-listp-of-non-consp
  (implies (not (consp x))
           (equal (true-listp x)
                  (equal nil x))))


;; Note (jcd): We proved the following rule (trivially) and found that some
;; later proofs that use lists were *much* slower.  By *much*, what we mean
;; is, a jump from .46 seconds to 95 seconds.  We thought these looked like
;; nice rules, so we started tracing type-set to figure out what was going on.
;; It turns out, that there is a function called type-set-cons, that
;; automatically "knows" these rules at a really deep level.  So, there is
;; really no need to prove them at all.  Hence, we have removed them.  Don't
;; uncomment them unless you know what you are doing.

;;
;; (defthm true-listp-of-cons-type-prescription
;;   (implies (true-listp y)
;;            (true-listp (cons a y)))
;;   :rule-classes :type-prescription)
;;
;; (defthm not-true-listp-of-cons-type-prescription
;;   (implies (not (true-listp y))
;;            (not (true-listp (cons a y))))
;;   :rule-classes :type-prescription)


;; Note (jcd): Why would we prove this rule?  Isn't this built into ACL2 as
;; well?  It turns out that it isn't.  Here is an example script to convince
;; yourself of it.  The example goes through with our rule, but not without.
;; (Another way to prove it without our rule is to use cases for (true-listp
;; y), but our rule will prove it with no hints.)
;;
;; (defstub foo (x) t)
;;
;; (in-theory (disable true-listp))
;;
;; (thm (equal (foo (true-listp (cons x y)))
;;             (foo (true-listp y))))

(defthm true-listp-of-cons
  (equal (true-listp (cons a y))
         (true-listp y))
  :hints(("Goal" :in-theory (enable true-listp))))

(defthm cdr-does-nothing-rewrite
  (equal (equal x (cdr x))
         (equal x nil)))

;bzo (ews and jcd) -  consider disabling this.
(defthm equal-car-differential
  (implies (and (not (equal a b))
                (equal (cdr a) (cdr b))
                (consp a)
                (consp b))
           (equal (equal (car a) (car b))
                  nil)))





;; Extended Macros for Repeated Car/Cdr'ing
;;
;; bzo (jcd) - I sure hope we don't want these macros.  Can we get rid of them
;; easily?  Hopefully they shouldn't occur in many places.  Note that they are
;; in the exports list if we want to kill them.  I think these are awful.

;; used in bags/meta once
;; used in gacc/gacc-exports.lisp once
;; used in gacc/gacc.lisp once
(defmacro cdddddr (x)
  `(cdr (cddddr ,x)))

;; used in gacc/gacc.lisp once
(defmacro cddddddr (x)
  `(cddr (cddddr ,x)))

;; never used
(defmacro caddddddr (x)
  `(car (cddddddr ,x)))

;; used in gacc/gacc-exports.lisp once
;; used in gacc/gacc.lisp several times
(defmacro cadddddr (x)
  `(car (cdddddr ,x)))

;; used in bags/meta.lisp once
;; used in gacc/gacc-exports.lisp once
;; used in gacc/ram.lisp once
;; used in gacc/gacc.lisp several times
(defmacro caddddr (x)
  `(car (cddddr ,x)))



;; Len-len-induction
;;
;; This is a useful induction scheme for cdr'ing down two lists at the same
;; time.  It is particularly helpful when you are trying to prove congruence
;; rules and need to recur down two lists x and x-equiv at the same time.

;; bzo (jcd) This should this be called cdr-cdr-induction, since it doesn't
;; mention len.  This is a really common induction scheme and it's used in many
;; books.  Renaming it will be some work.

(defun len-len-induction (x y)
  (if (and (consp x)
           (consp y))
      (len-len-induction (cdr x) (cdr y))
    nil))



;; finalcdr Function
;;
;; finalcdr keeps taking cdrs of X until we hit an atom, and returns that
;; atom.  For a true-listp, that atom will be nil, otherwise it will be
;; whatever is in the cdr-most position of the non true-list.

(defund finalcdr (x)
  (declare (type t x))
  (if (consp x)
      (finalcdr (cdr x))
    x))

(local
 (encapsulate
  ()

  ;; This is a test to make sure finalcdr's :type-prescription rule is
  ;; as strong as we think.  Don't remove this just because its has no
  ;; effect on the world!

  (local
   (defthm finalcdr-type-prescription-test
     (not (consp (finalcdr x)))
     :rule-classes nil
     :hints (("Goal"
              :in-theory (union-theories '(booleanp
                                           (:type-prescription finalcdr))
                                         (theory 'minimal-theory))))))))


(defthm finalcdr-when-true-listp
  (implies (true-listp x)
           (equal (finalcdr x)
                  nil))
  :hints (("Goal" :in-theory (enable finalcdr))))

(defthm finalcdr-when-non-consp
  (implies (not (consp x))
           (equal (finalcdr x)
                  x))
  :hints (("Goal" :in-theory (enable finalcdr))))

;bzo trying without this
;; (defthm finalcdr-when-cdr-not-consp
;;   (implies (and (consp x)
;;                 (not (consp (cdr x))))
;;            (equal (finalcdr x)
;;                   (cdr x)))
;;  :hints (("Goal" :in-theory (enable finalcdr))))

(defthm finalcdr-of-cdr
  (equal (finalcdr (cdr y))
         (if (consp y)
             (finalcdr y)
           nil))
  :hints (("Goal" :in-theory (enable finalcdr))))

(defthm acl2-count-of-finalcdr-linear
  (implies (consp y)
           (< (acl2-count (finalcdr y))
              (acl2-count y)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable finalcdr))))

(defthm acl2-count-finalcdr-less-than-acl2-count
  (equal (< (acl2-count (finalcdr y))
            (acl2-count y))
         (consp y)))

(defthm finalcdr-of-cons
  (equal (finalcdr (cons a x))
         (finalcdr x))
  :hints (("Goal" :in-theory (enable finalcdr))))

(defthm finalcdr-does-nothing-rewrite
  (equal (equal (finalcdr x) x)
         (not (consp x))))

(defthm finalcdr-append
  (equal (finalcdr (append a b))
         (finalcdr b))
  :hints (("Goal" :in-theory (enable append))))



;; fix Function
;;
;; fix changes the final cdr of X to be nil.  Many functions which operate
;; on lists (like the bags functions?) don't access those final cdrs and so are
;; unaffected if we call fix on their arguments.

; [Jared] unifying this with std/lists/list-fix
; [Mihir] unifying this with true-list-fix (built-in)

;; (defund fix (x)
;;   (declare (type t x))
;;   (if (consp x)
;;       (cons (car x)
;;             (fix (cdr x)))
;;     nil))

(defmacro fix (x) `(acl2::true-list-fix ,x))
(add-macro-alias fix acl2::true-list-fix)


(defthm fix-iff-consp
  (iff (fix x)
       (consp x))
  :hints (("Goal" :in-theory (enable fix))))

(defthm fix-of-non-consp
  (implies (not (consp x))
           (equal (fix x)
                  nil)))

(defthm fix-of-cons
  (equal (fix (cons a y))
         (cons a (fix y)))
  :hints (("Goal" :in-theory (enable fix))))

(defthm true-listp-fix
  (implies (true-listp x)
           (equal (fix x)
                  x))
  :hints (("Goal" :in-theory (enable fix))))

(defthm fix-does-nothing-rewrite
  (equal (equal x (fix x))
         (true-listp x)))

(defthm acl2-count-of-fix
  (equal (acl2-count (fix x))
         (- (acl2-count x)
            (acl2-count (finalcdr x))))
  :hints (("Goal" :in-theory (enable fix finalcdr))))



;; equiv Relation
;;
;; equiv: We say that two lists are congruent (i.e., equivalent) if their
;; fix's are the same, i.e., if they differ only in their final cdrs.  jcd
;; thinks this should be renamed to equiv, but maybe it's too much work now.

;; [Jared] unifying this with std/acl2::list-equiv
;;
;; (defund equiv (x y)
;;   (declare (type t x y))
;;   (equal (fix x)
;;          (fix y)))

(defmacro equiv (x y) `(acl2::list-equiv ,x ,y))
(add-macro-alias equiv acl2::list-equiv)

;; [Jared] this is now already known
;; (defequiv equiv
;;   :hints (("Goal" :in-theory (enable equiv))))

(local
 (defthmd open-equal-on-consp
   (implies
    (consp x)
    (equal (equal x y)
	   (and (consp y)
		(equal (car x) (car y))
		(equal (cdr x) (cdr y)))))))

;; This rule might be handy if you are trying to prove things like
;; (defcong list::equiv equal (foo x) 1)

(defthmd equal-to-equiv-equal-finalcdr
  (equal (equal x y)
	 (and (equal (finalcdr x) (finalcdr y))
	      (equiv x y)))
  :hints (("Goal" :in-theory (enable open-equal-on-consp equiv fix)
	   :induct (len-len-induction x y))))

(defthm equal-of-fixes
  (equal (equal (fix x)
                (fix y))
         (equiv x y))
  :hints (("Goal" :in-theory (enable equiv))))

(theory-invariant (incompatible (:rewrite equal-of-fixes)
                                (:definition equiv)))

(local (in-theory (disable (:rewrite equal-of-fixes))))

(defthm fix-equiv
  (equiv (fix x)
             x)
  :hints(("Goal" :in-theory (enable equiv))))

(defthm finalcdr-equiv
  (equiv (finalcdr x)
             nil)
  :hints(("Goal" :in-theory (enable equiv))))

(defcong equiv equal (consp x) 1
  :hints(("Goal" :in-theory (enable equiv)
         :induct (len-len-induction x x-equiv))))

(defcong equiv equal (car x) 1
  :hints(("Goal" :in-theory (enable equiv))))

(defcong equiv equiv (cdr x) 1
  :hints(("Goal" :in-theory (enable equiv))))

(defcong equiv equiv (cons x y) 2
  :hints(("Goal" :in-theory (enable equiv))))

(defcong equiv equal (fix x) 1
  :hints(("Goal" :in-theory (enable equiv))))

(defthm equiv-of-non-consp-two
  (implies (not (consp y))
           (equal (equiv x y)
                  (not (consp x))))
  :hints (("Goal" :in-theory (enable equiv))))

(defthm equiv-of-non-consp-one
  (implies (not (consp x))
           (equal (equiv x y)
                  (not (consp y))))
  :hints (("Goal" :in-theory (enable equiv))))

(defthm equiv-cons-cases
  (equal (equiv x (cons y z))
         (and (consp x)
              (equal y (car x))
              (equiv z (cdr x))))
  :hints (("Goal" :in-theory (enable equiv))))

(defthm equiv-of-two-true-listps
  (implies (and (true-listp x)
                (true-listp y))
           (equal (equiv x y)
                  (equal x y)))
  :hints (("Goal" :in-theory (enable equiv))))

;This looks like it could be expensive if k is large.
(defthm equiv-of-constant
  (implies (and (syntaxp (quotep k))
                (consp k))
           (equal (equiv k x)
                  (and (consp x)
                       (equal (car x) (car k))
                       (equiv (cdr x) (cdr k)))))
  :hints (("Goal" :in-theory (enable equiv fix))))

;bzo consider a recursive-flavored :definition rule instead?
;bzo consider disabling this?
(defthm open-equiv
  (implies (and (consp x)
                (consp y))
           (equal (equiv x y)
                  (and (equal (car x) (car y))
                       (equiv (cdr x) (cdr y)))))
  :hints (("Goal" :in-theory (enable equiv fix))))

(defthmd open-equiv-1
  (and
   (implies
    (consp x)
    (equal (equiv x y)
           (and (consp y)
                (equal (car x) (car y))
                (equiv (cdr x) (cdr y)))))
   (implies
    (consp y)
    (equal (equiv x y)
           (and (consp x)
                (equal (car x) (car y))
                (equiv (cdr x) (cdr y))))))
  :hints (("Goal" :in-theory (enable equiv fix))))

;; Len Theorems
;;
;; Despite being built into the system, ACL2 has few useful rules for reasoning
;; about len out of the box.  We add quite a few rules here.  We typically want
;; len to be disabled, but realizing that this is not the default, we have not
;; forced our will upon the user.  Note that if you disable len, you may wish
;; to also enable the :rewrite rule len-of-cdr.

;; bzo (ews and jcd) - We'd like to disable len at the top of the file but we
;; tried it and it seemed to break a lot in other libraries that use lists.
;; Revisit this later.

(local (in-theory (disable len)))

(encapsulate
 ()

 (local (defthmd len-of-fix
          (equal (len (fix x))
                 (len x))
          :hints (("Goal" :in-theory (enable len fix)))))

 (defcong equiv equal (len x) 1
   :hints (("Goal" :in-theory (enable equiv)
            :use ((:instance len-of-fix (x x))
                  (:instance len-of-fix (x x-equiv)))))))

(defthm len-non-negative-linear
  (<= 0 (len x))
  :rule-classes :linear)

(defthm len-non-negative
  (equal (< (len x) 0)
         nil))

(defthm len-when-consp-linear
  (implies (consp x)
           (< 0 (len x)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable len))))

(defthm len-pos-rewrite
  (equal (< 0 (len x))
         (consp x))
  :hints (("Goal" :in-theory (enable len))))

(defthm len-of-non-consp
  (implies (not (consp x))
           (equal (len x)
                  0))
  :hints (("Goal" :in-theory (enable len))))

(defthm len-equal-0-rewrite
  (equal (equal 0 (len x))
         (not (consp x)))
  :hints (("Goal" :in-theory (enable len))))


;; Note (jcd and ews): The rule below, consp-when-len-is-known-and-positive,
;; looks strange.  With it, we can prove the following:
;;
;; (defstub foo (x) t)
;;
;; (thm
;;  (implies (equal 2 (len x))
;;           (equal (foo (consp x))
;;                  (foo t))))
;;
;; Why have the free variable here?  Without it, the rule would only be
;; triggered by: (< 0 (len x)), but we want it to fire any time we know that
;; (len x) is equal to some term FOO (see whether FOO is known to be positive
;; and, if so, throw (consp x) into the type-alist).
;;
;; Why make this a :forward-chaining rule instead of a :rewrite rule?  Well, we
;; think that a :rewrite rule hung on (consp x) which all of a sudden starts
;; reasoning about len would be too expensive, although we guess we could make
;; this a :rewrite rule with a backchain-limit on the second hyp.  We haven't
;; looked into that yet.

(defthm consp-when-len-is-known-and-positive
  (implies (and (equal (len x) foo) ;foo is a free variable
                (< 0 foo))
           (consp x))
  :rule-classes :forward-chaining)

(defthm len-cons
  (equal (len (cons a x))
         (+ 1 (len x)))
  :hints (("Goal" :in-theory (enable len))))


;; Note (jcd): I thought for some time about combining the following rules,
;; since they are the same but have different rule classes.  In the end I
;; decided to leave them separate.  I think combining them would be okay in the
;; sense that you can always disable only the :linear or :rewrite portion of
;; the rule if you needed to.  However, generally people will just disable
;; "len-of-cdr" without specifying if the :linear or :rewrite portion is to be
;; used, and that would leave them without even the non-problematic and
;; potentially useful :linear version.  The split approach ensures that this
;; won't happen.

(defthm len-of-cdr-linear
  (implies (consp x)
           (equal (len (cdr x))
                  (+ -1 (len x))))
  :rule-classes :linear)

(defthmd len-of-cdr
  (implies (consp x)
           (equal (len (cdr X))
                  (+ -1 (len x)))))

;bzo replace the other one?
;should this be enabled?
(defthmd len-of-cdr-better
  (equal (len (cdr x))
         (if (consp x)
             (+ -1 (len x))
           0)))


(theory-invariant (incompatible (:rewrite len-of-cdr)
                                (:definition len)))

(theory-invariant (incompatible (:rewrite len-of-cdr-better)
                                (:definition len)))

(local (in-theory (enable len-of-cdr-better)))


(defthm len-of-cdr-bound-weak-linear
  (<= (len (cdr x))
      (len x))
  :rule-classes :linear)

(defthm len-of-cdr-bound-weak
  (equal (< (len x) (len (cdr x)))
         nil))

(defthm len-of-cdr-bound-tight-linear
  (implies (consp x)
           (< (len (cdr x))
              (len x)))
  :rule-classes :linear)

(defthm len-of-cdr-bound-tight
  (equal (< (len (cdr x)) (len x))
         (consp x)))





(defthm len-equal-1-rewrite
  (equal (equal (len y) 1)
         (equal (fix y) (list (car y))))
  :hints(("Goal" :in-theory (enable fix))))



;; Append Theorems
;;
;; As with len, few useful rules are built in for reasoning about append.  Here
;; we introduce a useful suite of such rules.  Also as with len, even though we
;; prefer to work with append disabled, we leave it enabled here since that is
;; the "default" behavior of ACL2.  Users are encouraged to disable append on
;; their own after including this book.

(defthm consp-append
  (equal (consp (append x y))
         (or (consp x)
             (consp y)))
  :hints (("Goal" :in-theory (enable append))))

(defthm append-consp-type-one
  (implies (consp x)
           (consp (append x y)))
    :rule-classes ((:type-prescription)))

(defthm append-consp-type-two
  (implies (consp y)
           (consp (append x y)))
    :rule-classes ((:type-prescription)))

;; bzo (jcd): There was a comment that arithmetic/top-with-meta had a rule
;; named append-true-listp-type-prescription, and so the following rule was
;; named append-true-listp-type-prescription-better.  (Actually that rule comes
;; from meta/term-defuns.lisp, which is included by arithmetic/top-with-meta.)
;; The rule is inferior -- it has an additional hypothesis that (true-listp x).
;;
;; I've reported the problem to Matt Kaufmann, and I think he has fixed it in
;; the development version of 2.9.3.  Once 2.9.3 is released, we should see if
;; the theorem is fixed in those books.  Then, we might consider moving this
;; theorem to the ACL2:: package so that it will have the same name.
;; Otherwise, users might have to disable it in both packages (although it's
;; weird to want to disable a type prescription rule).

(defthm append-true-listp-type-prescription
  (implies (true-listp y)
           (true-listp (append x y)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable append))))

(defthm true-listp-of-append
  (equal (true-listp (append x y))
         (true-listp y))
  :hints (("Goal" :in-theory (enable append))))

(defthmd car-append
  (equal (car (append x y))
         (if (consp x)
             (car x)
           (car y)))
  :hints (("Goal" :in-theory (enable append))))

(defthm car-append-not-consp
  (implies
   (not (consp x))
   (equal (car (append x y))
          (car y)))
  :hints (("goal" :in-theory (enable append))))

(defthm car-append-consp
  (implies
   (consp x)
   (equal (car (append x y))
          (car x)))
  :hints (("goal" :in-theory (enable append))))

(defthmd cdr-append
  (equal (cdr (append x y))
         (if (consp x)
             (append (cdr x) y)
           (cdr y)))
  :hints (("Goal" :in-theory (enable append))))

(defthm cdr-append-not-consp
  (implies
   (not (consp x))
   (equal (cdr (append x y))
          (cdr y)))
  :hints (("goal" :in-theory (enable append))))

(defthm cdr-append-consp
  (implies
   (consp x)
   (equal (cdr (append x y))
          (append (cdr x) y)))
  :hints (("goal" :in-theory (enable append))))

(defthm len-append
  (equal (len (append x y))
         (+ (len x)
            (len y)))
  :hints (("Goal" :in-theory (enable append))))


(defthm equal-len-append
  (implies (and (true-listp x)
                (true-listp y)
                (equal (len x) (len y)))
           (equal (equal (append x p) (append y q))
                  (and (equal x y)
                       (equal p q))))
  :hints (("Goal"
           :in-theory (enable append)
           :induct (len-len-induction x y))))

;; TEMP (jcd) - removed this theorem because it is subsumed by
;; append-of-non-consp-one below.
;;
;; (defthm append-of-nil-one
;;   (equal (append nil x)
;;          x)
;;   :hints (("Goal" :in-theory (enable append))))

;; (jcd ) the -two version of this rule isn't easy to
;; state (if we append x onto a non-consp y, we change the final cdr of x to be
;; y)...  bzo make it anyway
(defthm append-of-non-consp-one
  (implies (not (consp x))
           (equal (append x y) y))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints (("Goal" :in-theory (enable append))))

(defthm append-iff
  (iff (append x y)
       (or (consp x) y))
  :hints (("Goal" :in-theory (enable append))))

(defthm append-of-cons
  (equal (append (cons a x) y)
         (cons a (append x y)))
  :hints (("Goal" :in-theory (enable car-append cdr-append))))

(defthm equal-append-x-append-x
  (equal (equal (append x y)
                (append x z))
         (equal y z))
  :hints (("Goal" :in-theory (enable append))))

(defthm append-associative
  (equal (append (append x y) z)
         (append x (append y z)))
  :hints (("Goal" :in-theory (enable append))))

;; TEMP (jcd) - A comment indicated that we don't need this rule if the
;; associativity of append is enabled, and I agree.  I have removed it.
;;
;; (defthm append-equality-cancel
;;   (equal (equal (append x y)
;;                 (append (append x z) w))
;;          (equal y (append z w))))

(defthm fix-of-append
  (equal (fix (append x y))
         (append x (fix y)))
  :hints (("Goal" :in-theory (enable fix append))))

(defthm append-of-nil-two
  (equal (append x nil)
         (fix x))
  :hints (("Goal" :in-theory (enable car-append fix))))

(encapsulate
 ()

 (local (defthm acl2-count-of-append-when-consp
          (implies (consp y)
                   (equal (acl2-count (append y x))
                          (+ (- (acl2-count (finalcdr y)))
                             (acl2-count x)
                             (acl2-count y))))
          :hints (("Goal" :do-not '(generalize eliminate-destructors)
                   :in-theory (enable append finalcdr)))))

 (local (defthm acl2-count-of-append-when-not-consp
          (implies (not (consp y))
                   (equal (acl2-count (append y x))
                          (acl2-count x)))
          :hints (("Goal" :do-not '(generalize eliminate-destructors)
                   :in-theory (enable)))))

 (defthm acl2-count-of-append
   ;; or we could replace the first 2 summands with acl2-count of (fix y)
   ;; bzo lemma about that?
   (equal (acl2-count (append y x))
          (if (consp y)
              (+ (- (acl2-count (finalcdr y)))
                 (acl2-count y)
                 (acl2-count x)
                 )
            (acl2-count x)))
   :hints (("Goal" :do-not '(generalize eliminate-destructors)
            :in-theory (enable))))
 )

(defthm acl2-count-of-append-increases
  (implies (consp y)
           (< (acl2-count x)
              (acl2-count (append y x))))
  :hints (("Goal" :in-theory (disable acl2-count))))

(defthm append-equal-self-one
  (equal (equal x (append x y))
         (equal y (finalcdr x)))
  :hints (("Goal" :in-theory (enable append))))

;; TEMP (jcd) - removed this.  this is nothing more than an instance of the
;; equality axiom schema for functions, and it seems stupid to prove it.  It
;; was being used in the proof of append-equal-self-two below, but I've
;; replaced that with an explicit hint for how to do the proof.  At the least,
;; this should become a local event to the proof of append-equal-self-two.
;;
;; (defthm acl2-count-diff-means-not-equal
;;   (implies (< (acl2-count x) (acl2-count y))
;;            (not (equal x y))))

(defthm append-equal-self-two
   (equal (equal x (append y x))
          (not (consp y)))
   :hints(("Goal"
           :in-theory (disable acl2-count-of-append)
           :use (:instance acl2-count-of-append))))

(defthm appends-equal
  (equal (equal (append x1 y)
                (append x2 y))
         (equal (fix x1)
                (fix x2)))
  :hints (("Goal" :induct (len-len-induction x1 x2)
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable append fix))))

(defthm append-equal-fix-rewrite
  (equal (equal (append x y) (fix x))
         (equal nil y))
  :hints (("Goal" :in-theory (enable append fix))))

(defcong equiv equal (append x y) 1
  :hints (("Goal" :in-theory (enable equiv append))))

(defcong equiv equiv (append x y) 2
  :hints (("Goal" :in-theory (enable equiv append))))

;; TEMP (jcd) - originally we had the following rule, with a note asking if it
;; could be made more general:
;;
;; (defthm equiv-of-append-onto-finalcdr
;;   (equiv (append x (finalcdr y))
;;              x)
;;   :hints (("Goal" :in-theory (enable equiv))))
;;
;; I have removed it, since we already have the rule below, which is more
;; general and trivially implies equiv-of-append-onto-finalcdr with the
;; type prescription of finalcdr.

(defthm append-of-non-consp-2
  (implies (not (consp y))
           (equiv (append x y) x))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints(("Goal" :in-theory (enable equiv fix))))

;; TEMP (jcd) -- I've replaced (equiv nil y) in the following rules with
;; (not (consp y)).  These are identical concepts, but (not (consp y)) seems
;; more primitive to me, and therefore seems to make "more" progress.

(defthm equiv-of-append-self-one
 (equal (equiv (append x y) x)
        (not (consp y)))
 :hints (("Goal" :in-theory (enable equiv fix))))

(defthm equiv-of-append-self-two
  (equal (equiv x (append x y))
         (not (consp y)))
  :hints (("Goal" :in-theory (enable equiv fix))))

(defthm equiv-of-append-self-three
  (equal (equiv (append y x) x)
         (not (consp y)))
  :hints (("Goal" :in-theory (enable equiv fix))))

(defthm equiv-of-append-self-four
  (equal (equiv x (append y x))
         (not (consp y)))
  :hints (("Goal" :in-theory (enable equiv fix))))

;make more like this?
(defthm equiv-of-two-append-same
  (equal (equiv (append x y)
                (append x z))
         (equiv y z))
  :hints (("Goal" :in-theory (enable equiv))))




;; Firstn Function
;;
;; Firstn is peculiar in that there are other libraries which use and define
;; it.  So, we have gone to some lengths to ensure that firstn is defined
;; entirely within the ACL2 package.

(defund firstn (ACL2::n ACL2::l)
  "The sublist of L consisting of its first N elements."
  (declare (xargs :guard (and (true-listp ACL2::l)
                              (integerp ACL2::n)
                              (<= 0 ACL2::n))))
  (cond ((endp ACL2::l) nil)
        ((zp ACL2::n) nil)
        (t (cons (car ACL2::l)
                 (firstn (1- ACL2::n) (cdr ACL2::l))))))

;; TEMP (jcd) added another test for the type prescription of firstn.

(local
 (encapsulate
  ()

  ;; This is a test to make sure firstn's :type-prescription rule is
  ;; as strong as we think.  Don't remove this just because its has no
  ;; effect on the world!

  (local
   (defthm test-for-type-prescription-of-firstn
     (true-listp (firstn n l))
     :rule-classes nil
     :hints (("Goal" :in-theory (union-theories '(booleanp
                                                  (:type-prescription firstn))
                                                (theory 'minimal-theory))))))
  ))

;; TEMP (jcd) - we had this, but I've replaced it with the congruence rule
;; below.
;;
;; (defthm firstn-of-fix
;;   (equal (firstn n (fix l))
;;          (firstn n l)))

;; TEMP (jcd) - added this rule
(defcong equiv equal (firstn n l) 2
  :hints(("Goal" :in-theory (e/d (firstn equiv)
                                 (equal-of-fixes)))))

;; TEMP (jcd) - originally we had this rule (in nth-and-update-nth, maybe?),
;; but I've removed it because it is subsumed by firstn-of-zp
;;
;; (defthm firstn-0
;;   (equal (firstn 0 l)
;;          nil)
;;   :hints (("goal" :in-theory (enable firstn))))

(defthm firstn-of-zp
  (implies (zp n)
           (equal (firstn n x) nil))
  :hints (("Goal" :in-theory (enable firstn))))

;; TEMP (jcd) - this is a new rule, inspired by the list-defthms book.  Their
;; version applies to first-n-ac, but ours will apply to our firstn function.

(defthm consp-firstn
  (equal (consp (firstn n x))
         (and (not (zp n))
              (consp x)))
  :hints(("Goal" :in-theory (enable firstn))))

;; TEMP (jcd) - this is a new rule, inspired by the list-defthms book.  Their
;; version applies to first-n-ac, but ours will apply to our firstn function.

(defthm consp-firstn-type-prescription
  (implies (and (integerp n)
                (< 0 n)
                (consp x))
           (consp (firstn n x)))
  :rule-classes :type-prescription)


(defthm car-of-firstn
  (equal (car (firstn n y))
         (if (zp n)
             nil
           (car y)))
  :hints (("Goal" :in-theory (enable firstn))))

;; TEMP (jcd) - I found this rule buried in nth-and-update-nth.lisp, but
;; it seems like it belongs here.  (Probably has to do with the ACL2::firstn
;; versus LIST::firstn mess that we used to have).

(defthm firstn-cons
  (equal (firstn n (cons a b))
         (if (zp n)
             nil
           (cons a (firstn (1- n) b))))
  :hints (("Goal" :in-theory (enable firstn))))

(defthm firstn-iff
  (iff (firstn n x)
       (and (not (zp n))
            (consp x)))
  :hints (("Goal" :in-theory (enable firstn))))

(defthm len-of-firstn
  (equal (len (firstn n x))
         (min (nfix n) (len x)))
  :hints (("Goal" :in-theory (enable firstn))))

;; TEMP (jcd) - I am removing this rule in favor of firstn-does-nothing below,
;; which I believe should trivially subsume this.  (I rescued
;; firstn-does-nothing out of nth-and-update-nth.lisp)
;;
;; (defthm firstn-of-len-same
;;   (equal (firstn (len x) x)
;;          (fix x))
;;   :hints (("Goal" :in-theory (enable firstn len))))

(defthm firstn-does-nothing
  (implies (<= (len x) (nfix n))
           (equal (firstn n x)
                  (fix x)))
  :hints(("Goal" :in-theory (enable firstn))))

(defthm firstn-of-append
  (equal (firstn n (append x y))
         (append (firstn n x)
                 (firstn (+ n (- (len x))) y)))
  :hints (("Goal"
           :in-theory (enable firstn append fix))))

;; TEMP (jcd) - removed this rule on the grounds that firstn-of-append subsumes
;; it and, that, if (len x) is actually n above, then the rule will rewrite it
;; to (append (firstn (len x) x) nil) (with help from firstn-of-zp), which
;; append-of-nil-two will then rewrite to exactly (fix x), and we will
;; have achieved the same effect.  (In fact, I think this rule originally was
;; listed above firstn-of-append, so it wasn't getting the chance to fire)
;;
;; (defthm firstn-of-len-and-append-same
;;   (equal (firstn (len x) (append x y))
;;          (fix x))
;;   :hints (("Goal" :in-theory (enable firstn append))))

;; TEMP (jcd) - Removed this for now, seems like it's an obvious consequence of
;; the equality axiom schema for functions or whatever its called
;;
;; (defthmd not-equal-from-len-not-equal
;;   (implies (not (equal (len x) (len y)))
;;            (not (equal x y))))

;; TEMP (jcd) - Removed this appalling rule which doesn't seem to be necessary
;; anywhere for anything.
;;
;; (defthm equal-of-if-hack
;;   (implies (and (not (equal x y))
;;                 (not (equal x z)))
;;            (equal (equal x (if test y z))
;;                   nil)))

(encapsulate
 ()

 ;; TEMP (jcd) - this seems quite ugly so I've at least made it local, since
 ;; it is subsumed by the theorem it helps and since it is rule-classes nil
 ;; anyways.  I've also put this into an encapsulate.

 (local (defthm equal-of-firstn-and-firstn-same-two-helper
          (implies (and (not (equal n1 n2))
                        (integerp n1)
                        (integerp n2)
                        (<= 0 n1)
                        (<= 0 n2))
                   (equal (equal (firstn n1 x)
                                 (firstn n2 x))
                          (and (equal (firstn (min n1 n2) x)
                                      (firstn (min n1 n2) x))
                               (<= (len x) (min n1 n2)))))
          :rule-classes nil
          :hints (("Goal"
                   :in-theory (enable firstn)))))

 ;; bzo (jcd) - Do we want this crazy rule?

 (defthm equal-of-firstn-and-firstn-same-two
   (implies (not (equal n1 n2))
            (equal (equal (firstn n1 x)
                          (firstn n2 x))
                   (if (zp n1)
                       (or (zp n2) (not (consp x)))
                     (if (zp n2)
                         (or (zp n1) (not (consp x)))
                       (and (equal (firstn (min n1 n2) x)
                                   (firstn (min n1 n2) x))
                            (<= (len x) (min n1 n2)))))))
   :hints (("Goal" :use (:instance
                         equal-of-firstn-and-firstn-same-two-helper))))
 )

;; TEMP (jcd) - rescued the following encapsulate from nth-and-update-nth.lisp
;;
;; bzo (jcd) - the equivalent rule in list-defthms.lisp does not mention the
;; nfixes in the concluding firstn's.  Should we take them out?
(encapsulate
 ()

 (local (defthm firstn-of-firstn-one
          (implies (< (nfix n1) (nfix n2))
                   (equal (firstn n1 (firstn n2 l))
                          (firstn (nfix n1) l)))
          :hints(("Goal" :in-theory (enable firstn)))))

 (local (defthm firstn-of-firstn-two
          (implies (<= (nfix n2) (nfix n1))
                   (equal (firstn n1 (firstn n2 l))
                          (firstn (nfix n2) l)))
          :hints(("Goal" :in-theory (enable firstn)))))

 (defthm firstn-of-firstn
   (equal (firstn n1 (firstn n2 l))
          (if  (<= (nfix n2) (nfix n1))
              (firstn (nfix n2) l)
            (firstn (nfix n1) l))))
 )

;Do we want to do something similar for (first 2 x)?  Probably not?  -ews
(defthm firstn-1-rewrite
  (implies (consp x)
           (equal (firstn 1 x)
                  (list (car x))))
  :hints (("Goal" :in-theory (enable firstn))))

(defthm list::firstn-1-rewrite-strong
  (equal (firstn 1 x)
         (if (consp x)
             (list (car x))
           nil))
  :hints (("Goal" :in-theory (enable firstn))))

(defthmd firstn-of-cdr
  (implies (natp n)
           (equal (firstn n (cdr lst))
                  (cdr (firstn (+ 1 n) lst)))))

(defthm cdr-of-firstn
  (implies (natp n)
           (equal (cdr (firstn n lst))
                  (firstn (+ -1 n) (cdr lst)))))

(theory-invariant (incompatible (:rewrite firstn-of-cdr) (:rewrite cdr-of-firstn)))

;; Nthcdr Function
;;
;; Like len and append, we prefer to keep nthcdr disabled, but we will only
;; locally disable it so that we do not force our will upon the user.

(local (in-theory (disable nthcdr)))


;; TEMP (jcd) -- made this rule more general.  it used to be the following:
;;
;; (defthm nthcdr-of-0
;;   (equal (nthcdr 0 x)
;;          x)
;;   :hints (("Goal" :in-theory (enable nthcdr))))

(defthm nthcdr-of-zp
  (implies (zp n)
           (equal (nthcdr n x)
                  x))
  :hints(("Goal" :in-theory (enable nthcdr))))

;; TEMP (jcd) -- rescued this rule from nth-and-update-nth.lisp

(defthm nthcdr-iff
  (implies (true-listp l)
           (iff (nthcdr n l)
                (< (nfix n) (len l))))
  :hints (("Goal" :in-theory (enable nthcdr))))

;; TEMP (jcd) -- added this type prescription rule.  previously it was a
;; rewrite rule.  also see true-listp-of-nthcdr directly below.

(defthm true-listp-of-nthcdr-type-prescription
  (implies (true-listp l)
           (true-listp (nthcdr n l)))
  :hints(("Goal" :in-theory (enable nthcdr)))
  :rule-classes :type-prescription)

;; TEMP (jcd) -- added this rewrite rule, which is new.  Previously we only
;; have the above type prescription rule, but as a :rewrite rule, and this
;; seems like it will be more effective because it has no hyps.

(defthm true-listp-of-nthcdr
  (equal (true-listp (nthcdr n l))
         (or (< (len l) (nfix n))
             (true-listp l)))
  :hints(("Goal" :in-theory (enable nthcdr))))


;; TEMP (jcd) - the rules car-nthcdr and cdr-nthcdr have been inspired by the
;; standard list-defthms book, but improved to remove hypotheses.

;; bzo (jcd) - do we really want car-nthcd?  It rewrites a term to
;; nth, but we haven't included the nth/update-nth book in this basic core!
;; For now I am going to say that this is ok, and hopefully if someone uses
;; this rule they will include the nth-and-update-nth.lisp book.  But, maybe
;; the answer is to extend the core with the basic theorems about nth which
;; do not mention update-nth.

(defthm car-nthcdr
  (equal (car (nthcdr n x))
         (nth n x))
  :hints(("Goal" :in-theory (enable nthcdr))))

(defthm cdr-nthcdr
  (equal (cdr (nthcdr n x))
         (nthcdr (1+ (nfix n)) x))
  :hints(("Goal" :in-theory (enable nthcdr))))


;; TEMP (jcd) -- Enabled this rule.  A comment asked if this rule was too
;; strong, but I think it is a good rule and unless it breaks things, I think
;; we will want to have it enabled.

(defthm nthcdr-of-cons
  (equal (nthcdr n (cons a x))
         (if (and (integerp n)
                  (< 0 n))
             (nthcdr (+ -1 n) x)
           (cons a x)))
  :hints(("Goal" :in-theory (enable nthcdr))))

;; TEMP (jcd) -- Removed these rules since I am enabling nthcdr-of-cons and
;; these are just special cases of it.  (These were disabled anyway)
;;
;; (defthmd nthcdr-of-cons-special-one
;;   (implies (syntaxp (quotep n))
;;            (equal (nthcdr n (cons a x))
;;                   (if (and (integerp n)
;;                            (< 0 n))
;;                       (nthcdr (+ -1 n) x)
;;                     (cons a x))))
;;   :hints(("Goal" :in-theory (enable nthcdr))))
;;
;; (defthmd nthcdr-of-cons-special-two
;;   (implies (syntaxp (quotep m))
;;            (equal (nthcdr (+ m n) (cons a x))
;;                   (if (and (integerp (+ m n))
;;                            (< 0 (+ m n)))
;;                       (nthcdr (+ (+ -1 m) n) x)
;;                     (cons a x))))
;;   :hints(("Goal" :in-theory (enable nthcdr))))


;; TEMP (jcd) - made this rule stronger.  originally it was the following:
;;
;; (defthm nthcdr-of-len
;;   (equal (nthcdr (len x) x)
;;          (finalcdr x))
;;   :hints (("Goal" :in-theory (enable nthcdr len))))

(defthm nthcdr-of-len-or-more
  (implies (<= (len path) (nfix n))
           (equal (nthcdr n path)
                  (if (equal (len path) (nfix n))
                      (finalcdr path)
                    nil)))
  :hints(("Goal" :in-theory (enable nthcdr))))


;; jcd - This rule originally asked "yuck?"  But I think it is actually a
;; nice rule.

(defthm nthcdr-of-non-consp
  (implies (not (consp x))
           (equal (nthcdr n x)
                  (if (zp n)
                      x
                    nil)))
  :hints (("Goal" :in-theory (enable nthcdr))))

;; (TEMP) jcd - Removed this rule because it is subsumed by nthcdr-append
;; below.  There was a comment here asking if we could generalize this.

;; (defthm nthcdr-of-len-and-append
;;   (equal (nthcdr (len p) (append p list))
;;          list)
;;   :hints (("Goal" :in-theory (enable nthcdr append))))

;; jcd - The following rule was essentially copied from the list-defthms
;; book.  It's a good rule.

(defthm nthcdr-of-append
  (equal (nthcdr n (append a b))
         (if (<= (nfix n) (len a))
             (append (nthcdr n a) b)
           (nthcdr (- n (len a)) b)))
  :hints(("Goal" :in-theory (enable nthcdr))))

;; jcd - Here's another nice rule from the list-defthms book that we didn't
;; have before.

(defthm nthcdr-of-firstn
  (equal (nthcdr i (firstn j x))
         (if (<= (nfix j) (nfix i))
             nil
           (firstn (- (nfix j) (nfix i)) (nthcdr i x))))
  :hints(("Goal" :in-theory (enable firstn nthcdr))))

(defthmd firstn-of-nthcdr
  (implies (and (natp m)
                (natp n))
           (equal (firstn m (nthcdr n s))
                  (nthcdr n (firstn (+ m n) s)))))

;which way do we want to go?  maybe we should use subrange?
(theory-invariant (incompatible (:rewrite list::nthcdr-of-firstn)
                                (:rewrite firstn-of-nthcdr)))



(defthm list::nthcdr-of-firstn-goes-to-nil
  (implies (<= (nfix j) (nfix i))
           (equal (nthcdr i (firstn j x))
                  nil))
  :hints (("Goal" :in-theory (enable firstn nthcdr))))


(defthm len-of-nthcdr
  (equal (len (nthcdr n l))
         (if (natp n) ; change to use nfix around n?
             (max 0 (- (len l) n))
           (len l)))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm consp-of-nthcdr
  (equal (consp (nthcdr n l))
         (< (nfix n) (len l)))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defcong equiv equiv (nthcdr n l) 2
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm fix-of-nthcdr
  (equal (fix (nthcdr n l))
         (nthcdr n (fix l)))
  :hints (("Goal" :in-theory (enable nthcdr fix))))

(defthm nthcdrs-agree-when-shorter-nthcdrs-agree
  (implies (and (equal (nthcdr m x) (nthcdr m y))
                (<= m n)
                (natp m)
                (natp n)
                )
           (equal (equal (nthcdr n y) (nthcdr n x))
                  t))
  :hints (("Goal" :in-theory (enable nthcdr))))


;; ======================================================
;;
;; list-fix-equiv: an equivalence for lists of lists
;; (most useful in the "path" library)
;;
;; ======================================================

; [Jared] BOZO this is NOT the same as acl2::list-fix defined
; in the std library--it applies list::fix to a list of lists.
; We should really rename this.

(defun list::list-fix (list)
  (declare (type t list))
  (if (consp list)
      (cons (list::fix (car list)) (list::list-fix (cdr list)))
    nil))

(defthm true-list-listp-list-fix
  (true-list-listp (list::list-fix list)))

(defthm true-list-listp-implies-list-fix-identity
  (implies
   (true-list-listp list)
   (equal (list::list-fix list)
          list)))

(defcong list::equiv list::equiv (list::list-fix list) 1
  :hints (("goal"
           :in-theory (enable car-append cdr-append)
           :induct (len-len-induction list list-equiv))))

(defthm open-list-fix
  (implies (consp list)
           (equal (list::list-fix list)
                  (cons (list::fix (car list)) (list::list-fix (cdr list))))))

(defthm iff-list-fix
  (iff (list::list-fix x)
       (consp x)))

(defthm consp-list-fix
  (equal (consp (list::list-fix x))
         (consp x)))

(defun list::list-equiv (x y)
  (equal
   (list::list-fix x)
   (list::list-fix y)))

(defthm open-list-equiv-nonconsp-1
  (implies
   (not (consp x))
   (equal
    (list::list-equiv x y)
    (not (consp y)))))

(defthm open-list-equiv-nonconsp-2
  (implies
   (not (consp y))
   (equal
    (list::list-equiv x y)
    (not (consp x)))))

(defthm open-list-equiv-consp-1
  (implies
   (consp x)
   (equal
    (list::list-equiv x y)
    (and
     (consp y)
     (equal
      (list::fix (car x))
      (list::fix (car y)))
     (list::list-equiv (cdr x) (cdr y))))))

(defthm open-list-equiv-consp-2
  (implies
   (consp x)
   (equal
    (list::list-equiv y x)
    (and
     (consp y)
     (equal
      (list::fix (car x))
      (list::fix (car y)))
     (list::list-equiv (cdr y) (cdr x))))))

(defequiv list::list-equiv)

(defthm list-equiv-list-fix-reduction
  (list::list-equiv (list::list-fix list) list))

(in-theory (disable list::list-equiv))

(defrefinement list::equiv list::list-equiv
  :hints (("goal" :induct (len-len-induction x y))))

(defcong list::list-equiv list::list-equiv (cons a x) 2)

(defcong list::equiv list::list-equiv (cons a x) 1)

(defcong list::list-equiv list::list-equiv (append x y) 1
  :hints (("goal" :induct (len-len-induction x x-equiv))))

(defcong list::list-equiv list::list-equiv (append x y) 2
  :hints (("goal" :in-theory (enable append)
           :induct (append x y))))

;; TEMP (jcd) - there was some question as to which way to go (push fix into
;; nthcdr, or pull it out?) but I think we want to use the rule above, since
;; the congruence for (nthcdr n l) will get us pretty far if all we care about
;; is list-equivalence.  I've commented out the already-disabled nthcdr-of-fix
;; below in the name of simplification.
;;
;; (defthmd nthcdr-of-fix
;;   (equal (nthcdr n (fix p))
;;          (fix (nthcdr n p))))

(defthm nthcdr-of-nthcdr
  (equal (nthcdr n1 (nthcdr n2 l))
         (nthcdr (+ (nfix n1) (nfix n2)) l))
  :hints (("Goal" :in-theory (enable nthcdr))))

(defthm nthcdr-when-<=
  (implies (and (<= (len l) (nfix n))
                (true-listp l)
                )
           (equal (nthcdr n l)
                  nil))
  :hints (("Goal" :in-theory (enable nthcdr))))

;; TEMP (jcd) - rescued this theorem from nth-and-update-nth.lisp and also
;; changed it into rule-classes :linear instead of :rewrite.

(defthm acl2-count-of-nthcdr
  (implies (and (integerp n)
                (> n 0)
                (consp l))
           (< (acl2-count (nthcdr n l))
              (acl2-count l)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable nthcdr))))

;; TEMP (jcd) - added this rule which was inspired by list-defthms.lisp.  Our
;; rule uses equiv instead of equal, but we don't have a true-listp
;; hypothesis.

(defthm append-firstn-nthcdr
  (equal (append (firstn n l) (nthcdr n l))
         (if (<= (nfix n) (len l))
             l
           (fix l)))
  :hints(("Goal" :in-theory (enable firstn nthcdr))))



(defthmd equal-append-reduction!
  (equal (equal (append x y) z)
         (and (equiv x (firstn (len x) z))
              (equal y (nthcdr (len x) z))))
  :hints (("Goal"
           :induct (len-len-induction x z)
           :in-theory (enable firstn nthcdr append))))

;; TEMP (jcd) - rescued this rule from nth-and-update-nth.lisp

(defthm equal-append-append-simple
  (implies (equal (len a) (len b))
           (equal (equal (append a c)
                         (append b d))
                  (and (equal (fix a)
                              (fix b))
                       (equal c d))))
  :hints(("Goal" :in-theory (enable equiv
                                    equal-append-reduction!))))


;; TEMP (jcd) - removed this because now I haven't done anything to the local
;; theory and len-of-cdr is already set to be disabled when it is exported.
;;
;; (in-theory
;;  (e/d
;;   (len nthcdr firstn)
;;   (len-of-cdr)
;;   ))




;; Appendx.  The build in binary-append function has a guard which requires x
;; to be a true list.  This is sometimes irritating, so we provide the
;; following function which is provably equal to append logically, but which
;; removes the guard.  We use MBE so that the definition of appendx can just be
;; an "abbreviation rule" that expands to append.
;;
;; NOTE 1: You should NEVER try to write theorems about appendx; write your
;; theorems about "append" instead.
;;
;; NOTE 2: Using "appendx" will be much slower than "append", since surely Lisp
;; implementations will have a built in "native" append function, e.g., written
;; in C when using GCL, so if execution speed matters, you may prefer to use
;; "append" instead.

(defun binary-appendx (x y)
  (declare (type t x y))
  (mbe :logic (append x y)
       :exec (if (consp x)
                 (cons (car x) (binary-appendx (cdr x) y))
               y)))

(defmacro appendx (x y &rest rst)
  (xxxjoin 'binary-appendx (cons x (cons y rst))))

(add-binop appendx binary-appendx)





;could phrase RHS in terms of len?
(defthm list-hack
  (equal (equal (list::fix x) (list (car x)))
         (and (consp x)
              (not (consp (cdr x))))))

(defthm list-equiv-hack
  (equal (equal (list::fix x) y)
         (and (true-listp y)
              (list::equiv x y))))

(theory-invariant (incompatible (:rewrite list::equiv) (:rewrite LIST::LIST-EQUIV-HACK)))

;make cheap version?
(defthm len-when-at-most-1
  (implies (not (consp (cdr x)))
           (equal (len x)
                  (if (consp x)
                      1
                    0))))

;;; need to sort these:

;generalize to subrange?
(defthm nthcdr-firstn-one-more
  (implies (and (natp n)
                (< n (len s))
                )
           (equal (nthcdr n (firstn (+ 1 n) s))
                  (list (nth n s))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (list::nthcdr-of-firstn ;nthcdr firstn (:definition nth)
                            )
                           (firstn-of-nthcdr)))))

;bzo might be expensive?
(defthm cars-match-from-firstn-fact
  (implies (and (equal x (firstn n y))
                (integerp n)
                (<= 0 n))
           (equal (equal (car x) (car y))
                  (if (consp x)
                      t
                    (equal nil (car y))))))

;bzo might be expensive?
(defthm cars-match-from-firstn-fact-2
  (implies (and (equal x (firstn n y))
                (integerp n)
                (<= 0 n))
           (equal (equal (car y) (car x))
                  (if (consp x)
                      t
                    (equal nil (car y))))))

;may be too strong for general use...
(defthmd list::equal-cons-cases-strong
  (equal (equal (cons a b) c)
         (and (consp c)
              (equal a (car c))
              (equal b (cdr c)))))

(defthmd len-cdr-equal-len-cdr-rewrite
  (equal (equal (len (cdr x)) (len (cdr y)))
         (if (consp x)
             (if (consp y)
                 (equal (len x) (len y))
               (equal 1 (len x))
               )
           (if (consp y)
               (equal 1 (len y))
             t)))
  :hints (("Goal" :in-theory (enable))))

(theory-invariant (incompatible (:rewrite len-cdr-equal-len-cdr-rewrite) (:definition len)))

(include-book "../adviser/adviser")

(encapsulate
 ()

 (encapsulate
  (((equiv-hyps) => *)
   ((equiv-lhs) => *)
   ((equiv-rhs) => *)
   )

  (local (defun equiv-hyps () nil))
  (local (defun equiv-lhs () nil))
  (local (defun equiv-rhs () nil))

  (defthm equiv-multiplicity-constraint
    (implies
     (equiv-hyps)
     (and
      (equal (len (equiv-lhs)) (len (equiv-rhs)))
      (equal (nth arbitrary-element (equiv-lhs))
	     (nth arbitrary-element (equiv-rhs)))))
    :rule-classes nil)
  )

 (local (defun badguy (x y)
	  (declare (xargs :measure (len x)))
          (cond ((atom x) 0)
                ((not (equal (car x) (car y)))
                 0)
                (t (1+ (badguy (cdr x) (cdr y)))))))

 (local (defthm badguy-witness
          (equal (acl2::list-equiv x y)
		 (and (equal (len x) (len y))
		      (equal (nth (badguy x y) x)
			     (nth (badguy x y) y))))
	  :hints (("Goal" :in-theory (enable open-equiv-1)))))

 (defthm equiv-by-multiplicity-driver
   (implies (equiv-hyps)
            (acl2::list-equiv (equiv-lhs) (equiv-rhs)))
   :rule-classes nil
   :hints(("Goal"
           :use ((:instance
                  equiv-multiplicity-constraint
                  (arbitrary-element (badguy (equiv-lhs) (equiv-rhs))))))))

 (ADVISER::defadvice equiv-by-multiplicity
   (implies (equiv-hyps)
            (acl2::list-equiv (equiv-lhs) (equiv-rhs)))
   :rule-classes (:pick-a-point :driver equiv-by-multiplicity-driver))

 )

(in-theory (disable EQUIV-BY-MULTIPLICITY))

;; ===================================================================
;;
;; carx/cdrx/car?/cdr?/car!/cdr!
;;
;; ===================================================================

(defund cdrx (x)
  (declare (type t x))
  (if (consp x) (cdr x) nil))

(defund carx (x)
  (declare (type t x))
  (if (consp x) (car x) nil))

(local (in-theory (enable carx cdrx)))

(defthm cdrx-to-cdr
  (equal (cdrx x) (cdr x)))

(defthm carx-to-car
  (equal (carx x) (car x)))

(defund cdr? (x)
  (declare (type t x))
  (if (consp x) (cdr x) nil))

(defund car? (x default)
  (declare (type t x))
  (if (consp x) (car x) default))

(defund cdr! (x)
  (declare (type t x))
  (if (consp x) (cdr x)
    (coi-debug::fail :value nil
		 :message "In function cdr!: argument ~x0 is not a consp"
		 :parameters (x))))

(defund car! (x default)
  (declare (type t x))
  (if (consp x) (car x)
    (coi-debug::fail :value default
		 :message "In function car!: argument ~x0 is not a consp"
		 :parameters (x))))

(local (in-theory (enable cdr? car? cdr! car!)))

(defcong list::equiv list::equiv (cdr? x) 1)
(defcong list::equiv list::equiv (cdr! x) 1)
(defcong list::equiv equal (car? x default) 1)
(defcong list::equiv equal (car! x default) 1)

(defthm equal-car?-nil-reduction
  (equal (car? x nil) (car x)))

(defthm equal-car!-nil-reduction
  (equal (car! x nil) (car x)))

(defthm cdr?-consp-reduction
  (implies
   (consp x)
   (equal (cdr? x) (cdr x)))
  :rule-classes ((:rewrite
		  :backchain-limit-lst 0)))

(defthm cdr!-consp-reduction
  (implies
   (consp x)
   (equal (cdr! x) (cdr x)))
  :rule-classes ((:rewrite
		  :backchain-limit-lst 0)))

(defthm cdr?-not-consp-reduction
  (implies
   (not (consp x))
   (equal (cdr? x) nil))
  :rule-classes ((:rewrite
		  :backchain-limit-lst 0)))

(defthm cdr!-not-consp-reduction
  (implies
   (not (consp x))
   (equal (cdr! x) nil))
  :rule-classes ((:rewrite
		  :backchain-limit-lst 0)))

(defthm car?-consp-reduction
  (implies
   (consp x)
   (equal (car? x d) (car x)))
  :rule-classes ((:rewrite
		  :backchain-limit-lst 0)))

(defthm car!-consp-reduction
  (implies
   (consp x)
   (equal (car! x d) (car x)))
  :rule-classes ((:rewrite
		  :backchain-limit-lst 0)))

(defthm car?-not-consp-reduction
  (implies
   (not (consp x))
   (equal (car? x d) d))
  :rule-classes ((:rewrite
		  :backchain-limit-lst 0)))

(defthm car!-not-consp-reduction
  (implies
   (not (consp x))
   (equal (car! x d) d))
  :rule-classes ((:rewrite
		  :backchain-limit-lst 0)))

;;
;; Locations: computes the locations of a particular item in a list
;;

(defun locations (n key args)
  (declare (type (integer 0 *) n))
  (if (consp args)
      (if (equal key (car args))
	  (cons (nfix n) (locations (1+ n) key (cdr args)))
	(locations (1+ n) key (cdr args)))
    nil))

(defcong equiv equal (locations n key args) 3)

(defthm true-listp-location
  (true-listp (locations n key args)))
