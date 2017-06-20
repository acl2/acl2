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

(in-package "BAG")

(include-book "bind-free-rules") ;remove this?
(local (include-book "../util/iff"))

(in-theory (disable mfc-clause))
(in-theory (disable acl2::mfc-type-alist))
(in-theory (disable acl2::unsigned-byte-p))
(in-theory (disable pseudo-termp pseudo-term-listp))

(local (in-theory (disable acl2-count)))
(local (in-theory (enable member-to-memberp)))

(defthm ACL2-COUNT-NTH
  (implies
   (AND
    (consp list)
    (NOT (ZP I)))
   (< (ACL2-COUNT (SYN::NTH I LIST))
      (ACL2-COUNT LIST)))
  :HINTS (("goal" :IN-THEORY (enable syn::nth))))

;bzo some of the comments in this book may be out of date

;This book contains Eric's :meta rules for bags.  The rules in this book can
;replace most of the rules in bind-free-rules.lisp.  The :meta rules in this
;book "extended" in that they access the meta-function context (or mfc).  Each
;rules rewrites a term based on information in the type-alist and generates a
;hypothesis containing exactly the information that the rule relied upon.

;; This books contains :meta rules to establish the following:
;; (subbagp x y)
;; (unique x)
;; (disjoint x y)
;; (memberp a x)
;; (not (memberp a x))
;; (not (equal a b))

;;Each of the six rules in this file is very similar. See the comments for the
;;first rule (about subbagp) for more information.


;This doesn't do much consing (bzo what about the call to syntax-subbagp?),
;but hyp-for-syntax-subbagp-from-facts does.  Try to show that X is a subbagp
;of y, given the facts in CLAUSE (currently, we pay attention to only the
;subbagp facts in CLAUSE).  CLAUSE is a clause, and so facts that come from
;hypotheses are negated in CLAUSE.  The flag PERFORM-SYNTAX-SUBBAGP-TEST
;indicates whether we should test whether (syntax-subbagp x y).  Note that we
;need not do this on each recursive call, only on calls where x or y has
;changed.  The flag perform-syntax-subbagp-test should always be t for
;top-level calls. bzo better type guard on the flag (it's a boolean) So for
;the usual case (we're just walking down the clause, skipping literals that
;aren't subbagp calls), we don't keep redoing the syntax-subbagp test.
;perform-syntax-subbagp-test is a single 0 or 1 (so we can declare it to have
;type "bit"); maybe this is silly and we should just use t or nil...

;the parameter N represents the number of additional facts we are allowed to
;use and is used mostly for termination.  (I guess if there are cycles among
;the subbagp facts in the clause, then we might actually hit the case where we
;test for N.  prevents loops and is okay because, given a clause with n
;literals, we'll never need to use more than n facts to make a subbagp chain I
;wanted to move the test of N right before the recrusive call, so that we
;don't have to bother checking N in the usual case (namely, when entry is not
;a subbagp claim), but that didn't work because ACL2 only uses the top-level
;IF structure to determine termination. :-(

;We currently don't make use of the polarity of the term being rewritten to
;decide what to do for it.  We could, for example, try to rewrite hypotheses
;to false and conclusions to true. It's probably okay to not refrain from
;trying a rewrite due to polarity, since doing so can help get rid of
;redundant information; if, say, a hyp is implied by the other hyps, maybe we
;do want to get rid of it (by rewriting it to t) since it might just distract
;the user.  We also don't know a quick and easy way to tell the polarity of a
;term.

;;
;; Lemmas about allvars1 (this closely follows the material in :doc MUTUAL-RECURSION-PROOF-EXAMPLE)
;;

(defun symbol-listp-all-vars1-induction (flg x ans)
    ; Flg is non-nil (or t) if we are ``thinking'' of a single term.
  (if (atom x)
      (list x ans)
    (if flg
        (symbol-listp-all-vars1-induction nil (cdr x) ans)
      (list (symbol-listp-all-vars1-induction t (car x) ans)
            (symbol-listp-all-vars1-induction nil (cdr x) (all-vars1 (car x) ans))))))

(defthm symbol-listp-all-vars1-flg
  (if flg
      (implies (and (pseudo-termp x)
                    (symbol-listp ans))
               (symbol-listp (all-vars1 x ans)))
    (implies (and (pseudo-term-listp x)
                  (symbol-listp ans))
             (symbol-listp (all-vars1-lst x ans))))
  :hints (("Goal" :in-theory (enable pseudo-termp)
           :induct (symbol-listp-all-vars1-induction flg x ans)))
  :rule-classes nil)

(defthm symbol-listp-all-vars1
  (implies (and (pseudo-termp x)
                (symbol-listp ans))
           (symbol-listp (all-vars1 x ans)))
  :hints (("Goal" :by (:instance symbol-listp-all-vars1-flg
                                 (flg t)))))

(defthm symbol-listp-all-vars1-lst
  (implies (and (pseudo-term-listp x)
                (symbol-listp ans))
           (symbol-listp (all-vars1-lst x ans)))
  :hints (("Goal" :by (:instance symbol-listp-all-vars1-flg (flg nil)))))

(defun true-listp-all-vars1-induction (flg x ans)
    ; Flg is non-nil (or t) if we are ``thinking'' of a single term.
  (if (atom x)
      (list x ans)
    (if flg
        (true-listp-all-vars1-induction nil (cdr x) ans)
      (list (true-listp-all-vars1-induction t (car x) ans)
            (true-listp-all-vars1-induction nil (cdr x) (all-vars1 (car x) ans))))))

(defthm true-listp-all-vars1-flg
  (if flg
      (implies (and (pseudo-termp x)
                    (true-listp ans))
               (true-listp (all-vars1 x ans)))
    (implies (and (pseudo-term-listp x)
                  (true-listp ans))
             (true-listp (all-vars1-lst x ans))))
  :hints
  (("Goal" :induct (true-listp-all-vars1-induction flg x ans)))
  :rule-classes nil)

(defthm true-listp-all-vars1
  (implies (and (pseudo-termp x)
                (true-listp ans))
           (true-listp (all-vars1 x ans)))
  :hints (("Goal" :by (:instance true-listp-all-vars1-flg
                                 (flg t)))))

(defthm true-listp-all-vars1-lst
  (implies (and (pseudo-term-listp x)
                (true-listp ans))
           (true-listp (all-vars1-lst x ans)))
  :hints (("Goal" :by (:instance true-listp-all-vars1-flg (flg nil)))))

(in-theory (disable all-vars1 all-vars1-lst))


;;
;; lemmas about type-alistp
;;


(in-theory (disable acl2::type-alistp acl2::type-alist-entryp))

(defthm type-alistp-forward-to-true-listp
  (implies (acl2::type-alistp x)
           (true-listp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable acl2::type-alistp))))

(defthm type-alistp-forward-to-pseudo-termp-of-caar
  (implies (and (acl2::type-alistp x)
                x)
           (pseudo-termp (caar x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable acl2::type-alistp
                                     acl2::type-alist-entryp))))
(defthm type-alistp-of-cdr
  (implies (acl2::type-alistp type-alist)
           (acl2::type-alistp (cdr type-alist)))
  :hints (("Goal" :in-theory (enable acl2::type-alistp))))

(defthm type-alistp-fw-to-bound-1
  (implies (acl2::type-alistp type-alist)
           (<= (cadar type-alist) acl2::*max-type-set*))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable acl2::type-alist-entryp ACL2::TYPE-ALISTP))))

(defthm type-alistp-fw-to-bound-2
  (implies (acl2::type-alistp type-alist)
           (<= acl2::*min-type-set* (CADAR TYPE-ALIST)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable acl2::type-alist-entryp ACL2::TYPE-ALISTP))))

(defthm type-alistp-fw-to-integerp-of-cadar
  (implies (and (acl2::type-alistp type-alist)
                type-alist)
           (integerp (cadar type-alist)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable acl2::type-alist-entryp ACL2::TYPE-ALISTP))))




;;
;;
;; stuff about types
;;
;;

;needed for the guards to the ts- functions (perhaps prove the needed lemmas in a separate book?) (e.g., loganding the cadar of a type-alistp does such and such)
; (Matt K., 10/2013: Changed rel8 to rel9.)
(local (include-book "rtl/rel9/support/support/logand" :dir :system))

;Checks that TS represents a non-nil type.
;was a macro...
(defund ts-non-nil (ts)
  (declare (xargs :guard (and (INTEGERP ts)
                              (<= acl2::*min-type-set* ts)
                              (<= ts acl2::*max-type-set*))))
  (not (acl2::ts-intersectp ts acl2::*ts-nil*)))

;Checks that TS represents the type nil.
;was a macro...
(defund ts-nil (ts)
  (declare (xargs :guard (and (INTEGERP ts)
                              (<= acl2::*min-type-set* ts)
                              (<= ts acl2::*max-type-set*))))
  (acl2::ts= ts acl2::*ts-nil*))




;;
;; stuff about unsigned-byte-p
;;


;move this to a book about unsigned-byte-p?
;this broke something in push-gacc. why?  so i disabled it.
(defthmd unsigned-byte-p-from-bounds
  (implies (and (syntaxp (quotep bits))
                (< x (expt 2 bits))
                (integerp x)
                (<= 0 x)
                (integerp bits)
                (<= 0 bits))
           (acl2::unsigned-byte-p bits x))
  :hints (("Goal" :in-theory (enable acl2::unsigned-byte-p))))

(local (in-theory (enable unsigned-byte-p-from-bounds)))

(defthm unsigned-byte-p-of-one-less
  (implies (and (acl2::unsigned-byte-p 16 n)
                (< 0 n)
                (integerp n)
                )
           (acl2::unsigned-byte-p 16 (+ -1 n)))
  :hints (("Goal" :in-theory (enable acl2::unsigned-byte-p))))

;Making this local, since we have the same rule in super-ihs, and we don't need both.
;If you need rules about unsigned-byte-p, get them from super-ihs...
(local
 (defthm usb-linear-rewrite
   (implies (and (acl2::unsigned-byte-p n x)
                 (<= (expt 2 n) v))
            (< x v))
   :rule-classes (:rewrite)
   :hints (("goal" :in-theory (enable acl2::unsigned-byte-p)))))

(defund usb16-fix (x)
  (declare (type t x))
  (if (and (integerp x)
           (<= 0 x)
           (< x 65536))
      x
    65535))

(defthm usb16-usb16-fix
  (acl2::unsigned-byte-p 16 (usb16-fix x))
  :hints (("goal" :in-theory (enable usb16-fix))))

(defthm usb16-implies-usb16-fix-identity
  (implies
   (acl2::unsigned-byte-p 16 x)
   (equal (usb16-fix x) x))
  :hints (("goal" :in-theory (enable usb16-fix)
           :cases ((equal x 65535)))))

;;
;;
;; make-conjunction, etc.
;;
;;

;Returns a term representing the conjunctionof TERM1 and TERM2.
(defund make-conjunction (term1 term2)
  (declare (type t term1 term2))
  (if (equal term1 ''t)
      term2 ;conjoining something with "true" has no effect
    (if (equal term2 ''t)
        term1 ;conjoining something with "true" has no effect
      `(if ,term1 ,term2 'nil))))

(defthm make-conjunction-of-t-two
  (equal (make-conjunction x ''t)
         x)
  :hints (("Goal" :in-theory (enable make-conjunction))))

(defthm make-conjunction-of-t-one
  (equal (make-conjunction ''t x)
         x)
  :hints (("Goal" :in-theory (enable make-conjunction))))

(defthm make-conjunction-equal--quote-t-rewrite
  (equal (equal ''t (make-conjunction term1 term2))
         (and (equal ''t term1)
              (equal ''t term2)))
  :hints (("Goal" :in-theory (enable make-conjunction))))

(defthm syntax-ev-of-make-conjunction
  (iff (syntax-ev (make-conjunction term1 term2) alist)
       (and (syntax-ev term1 alist)
                (syntax-ev term2 alist)))
  :hints (("Goal" :in-theory (enable make-conjunction))))

(defthm pseudo-termp-of-make-conjunction
  (equal (pseudo-termp (make-conjunction term1 term2))
         (and (pseudo-termp term1)
                  (pseudo-termp term2)))
  :hints (("Goal" :in-theory (enable make-conjunction pseudo-termp))))

;could check whether term1 is ''t, but I think that'll never happen (we only negate stuff we find typed to nil in the type-alist).
;we don't need to check whether term2 is 't, because we'd still generate essentially `(if ,term1 'nil ,term2)
(defund make-conjunction-with-arg1-negated (term1 term2)
  (declare (type t term1 term2))
  `(if ,term1 'nil ,term2))

(defthm syntax-ev-of-make-conjunction-with-arg1-negated
  (iff (syntax-ev (make-conjunction-with-arg1-negated term1 term2) alist)
       (and (not (syntax-ev term1 alist))
            (syntax-ev term2 alist)))
  :hints (("Goal" :in-theory (enable make-conjunction-with-arg1-negated))))

(defthm pseudo-termp-of-make-conjunction-with-arg1-negated
  (equal  (pseudo-termp (make-conjunction-with-arg1-negated term1 term2))
          (and (pseudo-termp term1)
               (pseudo-termp term2)))
  :hints (("Goal" :in-theory (enable make-conjunction-with-arg1-negated))))

;(We could pass in a name to prepend to the variable used in the let?)
;Tests whether hyp is nil.  If so, returns nil.  If not, conjoins it with fact.
;We don't bother to check whether fact is nil (since it comes from the type-alist in situations when we call this macro).
(defmacro conjoin-fact-and-hyp (fact hyp)
  `(let ((hyp--dont-use-this-name-elsewhere ,hyp))
     (if hyp--dont-use-this-name-elsewhere
         (make-conjunction ,fact hyp--dont-use-this-name-elsewhere)
       nil)))

;(We could pass in a name to prepend to the variable used in the let?)
;We don't bother to check whether fact is nil (since it usually comes from the type-alist).
(defmacro conjoin-fact-and-two-hyps (fact hyp1 hyp2)
  `(let ((hyp1--dont-use-this-name-elsewhere ,hyp1))
     (if hyp1--dont-use-this-name-elsewhere
         (let ((hyp2--dont-use-this-name-elsewhere ,hyp2))
           (if hyp2--dont-use-this-name-elsewhere
               (make-conjunction ,fact (make-conjunction hyp1--dont-use-this-name-elsewhere hyp2--dont-use-this-name-elsewhere))
             nil))
       nil)))

(defmacro conjoin-negated-fact-and-hyp (fact hyp)
  `(let ((hyp--dont-use-this-name-elsewhere ,hyp))
     (if hyp--dont-use-this-name-elsewhere
         (make-conjunction-with-arg1-negated ,fact hyp--dont-use-this-name-elsewhere)
       nil)))

;;
;;
;; stuff to support binding all the vars in our hyps to themselves
;;
;;

;; Essay on hypothesis metafunctions and changes recently made to ACL2.
;;
;; If a hypothesis metafunction generates a hypothesis which mentions variables not in the term being rewritten,
;; those variables are considered free when ACL2 relieves the generated hypothesis.  This was a big surprise to us!
;; Furthermore, :meta rules behave as if they have :match-free :once. We had a small example in which a :meta rule
;; failed because a spurious match was found, preventing the right match from being found.  That was annoying, since
;; we know exactly what we want the variables in our hyp to be bound to (namely, themselves!)  Recall that everything
;; in our generated hyps comes straight from the type-alist.  We solve the free variables problem by binding to
;; itself each variable from the hyp which is not also in the term being rewritten.  (A recent change to ACL2 allows
;; this. Previously, the hyps generated by hypothesis metafunctions could not include calls to SYNP (which is what
;; BIND-FREE expands into.)  We also add a backchain limit of 0 to our :meta rules, because nothing more than type
;; reasoning should be needed to relieve the hyps, since they can straight from the type-alist.  Having a backchain
;; limit also ensures that the rule won't loop by finding in the generated hypothesis the very term bring rewritten.
;; (A change to ACL2 allowed the use of backchain limits with :meta rules.)


;; This generates what is essentially a call to bind-free that binds each var in VARS to themselves.  (Actually,
;; bind-free is a macro, and we must generate a term, so we generate a call to SYNP, which is what the call to
;; bind-free would expans into.)
;; NOTE! If VARS is nil, you probably don't want to call this function, since it will
;; return what is essentially a call to bind-free with a nil, and returning nil is how a bind-free function signals
;; failure.
;;  bzo add a guard that  vars is not nil?

;This partly follows a defun from Matt Kaufmann.
(defund bind-vars-to-selves (vars)
  (declare (xargs :guard t))
; The following can be figured out by running
; :trans1 (bind-free (pairlis$ '(a b c) '(a b c)) (a b c))
  `(SYNP ',vars
         '(BIND-FREE (PAIRLIS$ ',vars ',vars)
                     ,vars)
         '(PAIRLIS$ ',vars ',vars)))

(defun bind-extra-vars-in-hyp (hyp term)
  (declare (xargs :guard (and (pseudo-termp term)
                              (pseudo-termp hyp)
                              )))
  (if hyp ;bzo do we even need to check this?
      (let* ((hyp-vars (all-vars hyp))
             (lhs-vars (all-vars term))
             (extra-vars (acl2::set-difference-eq hyp-vars lhs-vars)))
        (if extra-vars ;if there are no extra vars, we can't just have "bind-free" return an empty alist, since that's how bind-free indicates failure.
            (make-conjunction (bind-vars-to-selves extra-vars) hyp)
          hyp))
    ''nil))

(set-state-ok t) ;we will pass state to our metafunctions





;; jcd - speed hack !!
;;
;; these rules seem to slow down the proofs in this book after this point, and
;; don't seem to be needed.  so, I am locally disabling them.
(local (in-theory (disable default-car default-cdr)))




;;
;;
;; :meta rule for subbagp (other rules are similar to this one; this one is well-documented)
;;
;;

;; Ways to show (subbagp x y):
;;   Easy Case: Discover that (syntax-subbagp x y).
;;   Find (subbagp BLAH1 BLAH2) where (syntax-subbagp x BLAH1), and then show (subbagp BLAH2 y).

;; (We say we are searching for a "subbagp chain" from X to Y.)
;; (We start at X and move toward Y.  Would it be more efficient to start from Y?)
;; (Note that we don't start to build the subbagp chain by looking for facts of the form (subbagp x BLAH).
;;   Rather, we are more general and look for facts of the form (subbagp BLAH1 BLAH2) where x is a syntactic subbagp
;;   of BLAH1.)

;; This function returns t or nil depending on whether we can show BLAH using information in the type-alist.  It is
;; written to be fast in the common case (when processing type-alist entries which are irrelevant to the task at
;; hand) and to avoid doing consing whenever possible.

;; X and Y are the terms for which we are trying to show (subbagp x y)

;; The counter N is the number of additional facts we may use before we stop.  We expect to rarely hit this limit,
;; but N helps us prove termination.  We require that N be an unsigned-byte-p of size 16.  We hope this makes the
;; operations involving it fast (that is, that they use fixnums instead of bignums.)  I can't imagine ever needing
;; this function to use more that 65535 facts in its attempt to rewrite some term.

;; TYPE-ALIST is the part of the type-alist which we are walking down looking for a potentially helpful fact.

;; WHOLE-TYPE-ALIST is the whole type-alist, including the part we have already walked down.  We need to keep the
;; whole thing around because, once we find a fact that might help us, we go back and reconsider the whole
;; TYPE-ALIST, looking for another fact which might connect with (here, might extend the subbagp chain from) the fact
;; we just found.

;; PERFORM-SYNTAX-TEST is a bit (0 or 1). If it is 1, we call syntax-subbagp on x and y to see whether we can tell
;; (subbag x y) just by looking at X and Y.  Note that we need not perform this test again on recursive calls for
;; which both X and Y are unchanged. So we pass 0 for the perform-syntax-test parameter on such calls.

;; This function is very structurally similar to hyp-for-show-subbagp-from-type-alist.  Any changes should be made to both.

(defignored show-subbagp-from-type-alist a (x y n type-alist whole-type-alist perform-syntax-test)
  (declare (type t x y type-alist whole-type-alist)
           (type (unsigned-byte 16) n)
           (type bit perform-syntax-test)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp x)
                              (pseudo-termp y)
                              )
                  :measure `((1 . ,(+ 1 (nfix n))) . ,(len type-alist))
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))
                  :guard-hints  (("Goal" :do-not '(preprocess)))
                  ))
  (if (and (equal 1 perform-syntax-test)
           (syntax-subbagp x y) ;we can tell just by looking at x and y that x is a subbagp of y
           )
      t
    (if (zp n) ;prevents loops.
        nil
      (if (endp type-alist)
          nil
        (let* ((entry (car type-alist))
               (fact (car entry)))
          (or (and (consp fact)
                   (equal (car fact) 'subbagp)
                   (ts-non-nil (cadr entry)) ;check that the type is either t or non-nil
                   (syntax-subbagp x (cadr fact))
                   (show-subbagp-from-type-alist (caddr fact) y (+ -1 n) whole-type-alist whole-type-alist 1)
                   (equal nil (cdddr fact))
                   )
              (show-subbagp-from-type-alist x y n (cdr type-alist) whole-type-alist 0)))))))

(defirrelevant show-subbagp-from-type-alist 1 a (x y n type-alist whole-type-alist perform-syntax-test)
  :hints (("goal" :in-theory (enable syntax-subbagp-irrelevant
                                     show-subbagp-from-type-alist-fn))))

;This either returns nil, indicating failure to show (subbagp x y), or it returns a term which is basically a
;conjunction (actually an equivalent nest of IFs) of the facts from the type-alist that we used to show (subbagp x y).

;This function is very structurally similar to show-subbagp-from-type-alist.  Any changes should be made to both.

(defignored hyp-for-show-subbagp-from-type-alist a (x y n type-alist whole-type-alist perform-syntax-test)
  (declare (type t x y type-alist whole-type-alist)
           (type (unsigned-byte 16) n) ;           (type (integer 0 *) n)
           (type bit perform-syntax-test)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp x)
                              (pseudo-termp y))
                  :guard-hints  (("Goal" :do-not '(preprocess)))
                  :measure `((1 . ,(+ 1 (nfix n))) . ,(len type-alist))
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))))

  (if (and (equal 1 perform-syntax-test) (syntax-subbagp x y)) ;we can tell just by looking at x and y that x is a subbagp of y
      ''t ;nothing from TYPE-ALIST was needed, so the hyp we return is just ''t
    (if (zp n)
        nil ;we failed (this probably won't happen in practice
      (if (endp type-alist)
          nil
        (let* ((entry (car type-alist))
               (fact (car entry)))
          (or (and (consp fact)
                   (equal (car fact) 'subbagp)
                   (ts-non-nil (cadr entry))
                   (syntax-subbagp x (cadr fact))
                   (equal nil (cdddr fact))
                   (conjoin-fact-and-hyp
                    fact  (hyp-for-show-subbagp-from-type-alist
                           (caddr fact) y (+ -1 n) whole-type-alist whole-type-alist 1)))
              (hyp-for-show-subbagp-from-type-alist x y n (cdr type-alist) whole-type-alist 0)))))))

(defirrelevant hyp-for-show-subbagp-from-type-alist 1 a (x y n type-alist whole-type-alist perform-syntax-test)
  :hints (("goal" :in-theory (enable
                              syntax-subbagp-irrelevant
                              hyp-for-show-subbagp-from-type-alist-fn))))

(defthm show-subbagp-from-type-alist-iff-hyp-for-show-subbagp-from-type-alist
  (iff (show-subbagp-from-type-alist x y n type-alist whole-type-alist flg)
       (hyp-for-show-subbagp-from-type-alist x y n type-alist whole-type-alist flg))
  :hints (("Goal" :in-theory (enable show-subbagp-from-type-alist-fn
                                     hyp-for-show-subbagp-from-type-alist-fn))))


(defthm show-subbagp-from-type-alist-works-right
  (implies (and (hyp-for-show-subbagp-from-type-alist x y n type-alist whole-type-alist flg)
                (syntax-ev (hyp-for-show-subbagp-from-type-alist x y n type-alist whole-type-alist flg) a))
           (subbagp (syntax-ev x a)
                    (syntax-ev y a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (hyp-for-show-subbagp-from-type-alist-fn
                            )
                           ())))
  :rule-classes (:rewrite :forward-chaining))

;; ;do we need this?
;; ;use this more?
;; (defthm show-subbagp-from-type-alist-works-right-2
;;   (implies (equal (hyp-for-show-subbagp-from-type-alist x y n type-alist whole-type-alist flg)
;;                   ''t)
;;            (subbagp (syntax-ev x alist)
;;                     (syntax-ev y alist)))
;;   :hints (("Goal" :in-theory (disable show-subbagp-from-type-alist-works-right)
;;            :use (:instance show-subbagp-from-type-alist-works-right))))

(defthm hyp-for-show-subbagp-from-type-alist-equal-t-rewrite
  (equal (equal (hyp-for-show-subbagp-from-type-alist x y n type-alist whole-type-alist flg)
                ''t)
         (and (equal 1 flg) (syntax-subbagp x y)))
  :hints (("Goal" :expand ((HYP-FOR-SHOW-SUBBAGP-FROM-TYPE-ALIST-fn a X Y N TYPE-ALIST WHOLE-TYPE-ALIST FLG))
           :in-theory (enable hyp-for-show-subbagp-from-type-alist-fn))))


(defthm pseudo-termp-of-hyp-for-show-subbagp-from-type-alist
  (implies (and (acl2::type-alistp type-alist)
                (acl2::type-alistp whole-type-alist)
                )
           (pseudo-termp (hyp-for-show-subbagp-from-type-alist x y n type-alist whole-type-alist perform-syntax-test)))
  :hints (("Goal" :in-theory (enable HYP-FOR-SHOW-SUBBAGP-FROM-TYPE-ALIST-FN))))

;This is the metafunction.

;(We could count the number of subbagp facts and use that value for len.  This
;might be a good idea if we think cycles might exist among our subbagp facts.)
;(Or We could consider using the length of the clause, not the type-alist for
;len.)

(defun show-subbagp-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (and (consp term) ;well-formedness checks, should always succeed
           (equal (car term) 'subbagp) ;needed for the guard stuff..
           (let* ((type-alist (acl2::mfc-type-alist mfc))
                  (len (usb16-fix (len type-alist))))
             (show-subbagp-from-type-alist-fn nil (cadr term) (caddr term) len type-alist type-alist 1)))
      ''t
    term))

;This is the hypothesis metafunction

;This partly follows something from Matt Kaufmann.
(defun hyp-for-show-subbagp-from-mfc (term mfc state)
  (declare (type t term mfc state)
           (ignore state)
           (xargs :guard (pseudo-termp term)))
  (if (and (consp term)
           (equal (car term) 'subbagp) ;needed for the guard stuff..
           )
      (let* ((type-alist (acl2::mfc-type-alist mfc))
             (len (usb16-fix (len type-alist))))
        (bind-extra-vars-in-hyp
         (hyp-for-show-subbagp-from-type-alist-fn nil (cadr term) (caddr term) len type-alist type-alist 1) term))
    ''nil))


;; This is the :meta rule for (subbagp x y).

(defthm meta-rule-to-show-subbagp
  (implies (syntax-ev (hyp-for-show-subbagp-from-mfc term mfc state) a)
           (equal (syntax-ev term a)
                  (syntax-ev (show-subbagp-from-mfc term mfc state) a)))
  :otf-flg t
  :rule-classes ((:meta :trigger-fns (subbagp)
                        :backchain-limit-lst 0 ;just in case...
                        ))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable HYP-FOR-SHOW-SUBBAGP-FROM-TYPE-ALIST-irrelevant)
           :do-not '(generalize eliminate-destructors))))


;;
;; tests of meta-rule-to-show-subbagp
;;

;bzo why does the t-p rule get used here?
(encapsulate

 ()
 (local (defthmd tester0
          (implies (bag::subbagp x y)
                   (bag::subbagp x (cons nil y)))
          :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-subbagp)
                                                     (theory 'minimal-theory))))))

 (local (defthmd tester
          (implies (and (subbagp x y)
                        (subbagp y z)
                        (subbagp z q))
                   (subbagp x q))
          :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-subbagp)
                                                     (theory 'minimal-theory)))))))

(encapsulate
 ()
 (local (defthmd tester1
          (implies (and (subbagp x y)
                        (subbagp (append y b) z))
                   (subbagp x z))
          :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-subbagp)
                                                     (theory 'minimal-theory)))))))

;make more tests where the second arg of the target subbagp has structure (i.e., isn't just a variable)?
(encapsulate
 ()
 (local (defthmd tester2
          (implies (subbagp a x)
                   (subbagp a (append x y)))
          :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-subbagp)
                                                     (theory 'minimal-theory)))))))

(encapsulate
 ()
 (local (defthmd tester-huge
          (implies (and (subbagp x y)
                        (subbagp y z)
                        (subbagp z w)
                        (subbagp (append w aa) cc)
                        (subbagp cc q))
                   (subbagp x q))
          :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-subbagp)
                                                     (theory 'minimal-theory)))))))

(encapsulate
 ()
 (local (defthmd tester-huge2
          (implies (and (subbagp x y)
                        (subbagp y z)
                        (subbagp z w)
                        (subbagp (cons aa w) cc)
                        (subbagp cc q))
                   (subbagp x q))
          :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-subbagp)
                                                     (theory 'minimal-theory)))))))


(in-theory (disable subbagp-computation)) ;we will use my rule instead
;(in-theory (disable meta-rule-to-show-subbagp))


;;
;;
;; Eric's rule for UNIQUE (very similar to the rule for SUBBAGP; see the documentation for that)
;;
;;

;; Ways to show (unique x):
;;   Find (unique BLAH), and then show (subbagp x BLAH).
;; (We could stop if X is syntactically not unique,  e.g., if X is (cons a (cons a y)).

(defignored show-unique-from-type-alist a (x n type-alist whole-type-alist)
  (declare (type t x type-alist whole-type-alist)
           (type (unsigned-byte 16) n)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp x)
                              )
                  :guard-hints  (("Goal" :do-not '(preprocess)))))
  (if (endp type-alist)
      nil
    (let* ((entry (car type-alist))
           (fact (car entry)))
      (or (and (consp fact)
               (equal (car fact) 'unique)
               (ts-non-nil (cadr entry))
               (show-subbagp-from-type-alist x (cadr fact) n whole-type-alist whole-type-alist 1)
               (equal nil (cddr fact)))
          (show-unique-from-type-alist x n (cdr type-alist) whole-type-alist)))))

(defirrelevant show-unique-from-type-alist 1 a (x n type-alist whole-type-alist)
  :hints (("goal" :in-theory (enable HYP-FOR-SHOW-SUBBAGP-FROM-TYPE-ALIST-irrelevant
                                     show-subbagp-from-type-alist-irrelevant
                                     show-unique-from-type-alist-fn))))

(defignored hyp-for-show-unique-from-type-alist a (x n type-alist whole-type-alist)
  (declare (type t x type-alist whole-type-alist)
           (type (unsigned-byte 16) n)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp x))
                  :guard-hints  (("Goal" :do-not '(preprocess)))))
  (if (endp type-alist)
      nil
    (let* ((entry (car type-alist))
           (fact (car entry)))
      (or (and (consp fact)
               (equal (car fact) 'unique)
               (ts-non-nil (cadr entry))
               (equal nil (cddr fact))
               (conjoin-fact-and-hyp fact
                                     (hyp-for-show-subbagp-from-type-alist x (cadr fact) n whole-type-alist whole-type-alist 1)))
          (hyp-for-show-unique-from-type-alist x n (cdr type-alist) whole-type-alist)))))

(defirrelevant hyp-for-show-unique-from-type-alist 1 a (x n type-alist whole-type-alist)
  :hints (("goal" :in-theory (enable hyp-for-show-subbagp-from-type-alist-irrelevant
                                     hyp-for-show-unique-from-type-alist-fn))))

(defthm show-unique-from-type-alist-iff-hyp-for-show-unique-from-type-alist
  (iff (show-unique-from-type-alist x n type-alist whole-type-alist)
       (hyp-for-show-unique-from-type-alist x n type-alist whole-type-alist))
  :hints (("Goal" :in-theory (enable show-unique-from-type-alist-fn
                                     hyp-for-show-unique-from-type-alist-fn))))

(defthm show-unique-from-type-alist-works-right
  (implies (and (syntax-ev (hyp-for-show-unique-from-type-alist x n type-alist whole-type-alist ) a)
                (hyp-for-show-unique-from-type-alist x n type-alist whole-type-alist ))
           (unique (syntax-ev x a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (hyp-for-show-unique-from-type-alist-fn)
                           ())))
  :rule-classes (:rewrite :forward-chaining))

(defthm pseudo-termp-of-hyp-for-show-unique-from-type-alist
  (implies (and (acl2::type-alistp type-alist)
                (acl2::type-alistp whole-type-alist)
                )
           (pseudo-termp (hyp-for-show-unique-from-type-alist x n type-alist whole-type-alist)))
  :hints (("Goal" :in-theory (enable hyp-for-show-unique-from-type-alist-fn))))


;;
;; Non-membership sidecase
;;

(defignore syntax-show-common-members a (list)
  (declare (type (satisfies pseudo-termp) list)
           (xargs :guard-hints (("goal" :in-theory (enable pseudo-termp)))))
  (cond
   ((syn::consp list)
    (let ((v    (syn::car list))
          (list (syn::cdr list)))
      (or (syntax-memberp v list)
          (syntax-show-common-members list))))
   ((syn::appendp list)
    (syntax-show-common-members (syn::arg 2 list)))
   ((syn::quotep list)
    (not (unique (syn::dequote list))))))

(defirrelevant syntax-show-common-members 1 a (list)
  :hints (("goal" :in-theory (enable
                              syntax-memberp-irrelevant
                              ))))

(defthm syntax-show-common-members-implies-not-unique
  (implies
   (syntax-show-common-members list)
   (not (unique (syntax-ev list a))))
  :hints (("goal" :in-theory (enable SYN::NTH unique)))
  :rule-classes (:rewrite :forward-chaining))


(defun show-unique-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (and (consp term) ;should always succeed
           (equal 'unique (car term)))
      (if (let* ((type-alist (acl2::mfc-type-alist mfc))
                 (len (usb16-fix (len type-alist))))
            (show-unique-from-type-alist-fn nil (cadr term) len type-alist type-alist))
          (syn::true)
        (if (syntax-show-common-members-fn nil (cadr term))
            (syn::nil)
          term))
    term))

(defun hyp-for-show-unique-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (and (consp term) ;should always succeed
           (equal 'unique (car term)) ;should always succeed, included for guard proof
           )
      (let* ((type-alist (acl2::mfc-type-alist mfc))
             (len (usb16-fix (len type-alist))))
        (let ((hyp (hyp-for-show-unique-from-type-alist-fn nil (cadr term) len type-alist type-alist)))
          (or (and hyp
                   (bind-extra-vars-in-hyp hyp term))
              (if (syntax-show-common-members-fn nil (cadr term))
                  (syn::true)
                (syn::nil)))))
    (syn::nil)))

(defthm meta-rule-to-show-unique
  (implies (syntax-ev (hyp-for-show-unique-from-mfc term mfc state) a)
           (equal (syntax-ev term a)
                  (syntax-ev (show-unique-from-mfc term mfc state) a)))
  :rule-classes ((:meta :trigger-fns (unique)
                        :backchain-limit-lst 0 ;just in case...
                        ))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable
                       hyp-for-show-unique-from-type-alist-irrelevant
                       syntax-show-common-members-irrelevant
                       )
           :do-not '(generalize eliminate-destructors))))

(in-theory (disable unique-computation))

;;
;; tests for meta-rule-to-show-unique
;

(encapsulate
 ()
 (local
  (defthmd unique-test
    (implies (and (subbagp x y)
                  (subbagp y z)
                  (subbagp z w)
                  (unique w))
             (unique x))
    :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-unique)
                                               (theory 'minimal-theory)))))))

(encapsulate
 ()
 (local
  (defthmd unique-test1
    (implies (and (subbagp x y)
                  (subbagp (append y p) z)
                  (subbagp z w)
                  (unique w))
             (unique x))
    :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-unique)
                                               (theory 'minimal-theory)))))))

(encapsulate
 ()
 (local
  (defthmd unique-test2
    (implies (unique (append x y))
             (unique x))
    :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-unique)
                                               (theory 'minimal-theory)))))))

(encapsulate
 ()
 (local
  (defthmd unique-test3
    (implies (and (subbagp x a)
                  (unique (append a y)))
             (unique x))
    :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-unique)
                                               (theory 'minimal-theory)))))))

(encapsulate
 ()
 (local
  (defthmd unique-test4
    (implies (and (subbagp x a)
                  (subbagp a y)
                  (subbagp y z)
                  (unique y))
             (unique x))
    :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-unique)
                                               (theory 'minimal-theory)))))))




;;
;;
;; ways to show unique-subbagps  -- we never use this directly.  rather, we use it to show disjointness...
;;
;;

(defignored show-unique-subbagps-from-type-alist a (x y bag n type-alist whole-type-alist perform-syntax-test)
  (declare (type t x y bag type-alist whole-type-alist)
           (type (unsigned-byte 16) n)
           (type bit perform-syntax-test)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp x)
                              (pseudo-termp y)
                              (pseudo-termp bag))
                  :guard-hints  (("Goal"
                                  :do-not '(preprocess)))
                  :measure `((1 . ,(+ 1 (nfix n))) . ,(len type-alist))
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))))
  (if (and (equal 1 perform-syntax-test)
           (syntax-unique-subbagps x y bag)
           )
      t
    (if (zp n)
        nil
      (if (endp type-alist)
          nil
        (let* ((entry (car type-alist))
               (fact (car entry)))
          (or (and (consp fact)
                   (equal (car fact) 'subbagp)
                   (ts-non-nil (cadr entry))
                   (or (and (syntax-subbagp x (cadr fact))
                            (show-unique-subbagps-from-type-alist
                             (caddr fact) y bag (+ -1 n) whole-type-alist whole-type-alist 1))
                       (and (syntax-subbagp y (cadr fact))
                            (show-unique-subbagps-from-type-alist
                             (caddr fact) x bag (+ -1 n) whole-type-alist whole-type-alist 1))
                       (and (syntax-subbagp (caddr fact) bag)
                            (show-unique-subbagps-from-type-alist
                             x y (cadr fact) (+ -1 n) whole-type-alist whole-type-alist 0)))
                   (equal nil (cdddr fact)))
              (show-unique-subbagps-from-type-alist x y bag n (cdr type-alist) whole-type-alist 0)))))))

(defirrelevant show-unique-subbagps-from-type-alist 1 a (x y bag n type-alist whole-type-alist perform-syntax-test)
  :hints (("goal" :in-theory (enable
                              show-unique-subbagps-from-type-alist-fn
                              syntax-subbagp-irrelevant
                              syntax-unique-subbagps-irrelevant
                              ))))

(defignored hyp-for-show-unique-subbagps-from-type-alist a (x y bag n type-alist whole-type-alist perform-syntax-test)
  (declare (type t x y bag type-alist whole-type-alist)
           (type (unsigned-byte 16) n)
           (type bit perform-syntax-test)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp x)
                              (pseudo-termp y)
                              (pseudo-termp bag))
                  :guard-hints  (("Goal"
                                  :do-not '(preprocess)))
                  :measure `((1 . ,(+ 1 (nfix n))) . ,(len type-alist))
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))))
  (if (and (equal 1 perform-syntax-test)
           (syntax-unique-subbagps x y bag)
           )
      ''t
    (if (zp n)
        nil
      (if (endp type-alist)
          nil
        (let* ((entry (car type-alist))
               (fact (car entry)))
          (or (and (consp fact)
                   (equal (car fact) 'subbagp)
                   (ts-non-nil (cadr entry))
                   (equal nil (cdddr fact))
                   (or (and (syntax-subbagp x (cadr fact))
                            (conjoin-fact-and-hyp
                             fact (hyp-for-show-unique-subbagps-from-type-alist
                                   (caddr fact) y bag (+ -1 n) whole-type-alist whole-type-alist 1)))
                       (and (syntax-subbagp y (cadr fact))
                            (conjoin-fact-and-hyp
                             fact (hyp-for-show-unique-subbagps-from-type-alist
                                   (caddr fact) x bag (+ -1 n) whole-type-alist whole-type-alist 1)))
                       (and (syntax-subbagp (caddr fact) bag)
                            (conjoin-fact-and-hyp
                             fact (hyp-for-show-unique-subbagps-from-type-alist
                                   x y (cadr fact) (+ -1 n) whole-type-alist whole-type-alist 0)))
                       ))
              (hyp-for-show-unique-subbagps-from-type-alist
               x y bag n (cdr type-alist) whole-type-alist 0)))))))

(defirrelevant hyp-for-show-unique-subbagps-from-type-alist 1 a
  (x y bag n type-alist whole-type-alist perform-syntax-test)
  :hints (("goal" :in-theory (enable
                              hyp-for-show-unique-subbagps-from-type-alist-fn
                              syntax-unique-subbagps-irrelevant
                              syntax-subbagp-irrelevant
                              ))))

(defthm show-unique-subbagps-from-type-alist-iff-hyp-for-show-unique-from-type-alist
  (iff (show-unique-subbagps-from-type-alist x y bag n type-alist whole-type-alist flg)
       (hyp-for-show-unique-subbagps-from-type-alist x y bag n type-alist whole-type-alist flg))
  :hints (("Goal" :in-theory (enable show-unique-subbagps-from-type-alist-fn
                                     hyp-for-show-unique-subbagps-from-type-alist-fn
                                     ))))

;bzo make a meta rule to conclude unique-subbagps
;get rid of some hints?
;really slow proof!

; jcd - i looked at speeding this up by disabling rules from accumulated
; persistence, but I didn't get very far at all.  it uses the definition
; hyp-for-show-unique-subbagps-from-type-alist-fn a lot but you can't just
; disable it, or the proof fails.  so, i didn't change anything, since i didn't
; have anything to show for it.

(defthm show-unique-subbagps-from-type-alist-works-right
  (implies (and (syntax-ev (hyp-for-show-unique-subbagps-from-type-alist x y bag n type-alist whole-type-alist flg) a)
                (hyp-for-show-unique-subbagps-from-type-alist x y bag n type-alist whole-type-alist flg)
                (equal v (syntax-ev x a))
                (equal w (syntax-ev y a))
                )
           (unique-subbagps v w (syntax-ev bag a)))
  :hints (("Goal"
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable hyp-for-show-unique-subbagps-from-type-alist-fn)))
  :rule-classes (:rewrite :forward-chaining))

(defthmd show-unique-subbagps-from-type-alist-works-right-2
  (implies
   (and (hyp-for-show-unique-subbagps-from-type-alist x y bag n type-alist whole-type-alist flg)
        (equal (hyp-for-show-unique-subbagps-from-type-alist x y bag n type-alist whole-type-alist flg) ''t))
   (unique-subbagps (syntax-ev x a)
                    (syntax-ev y a)
                    (syntax-ev bag a)))
  :hints (("Goal" :use (:instance  show-unique-subbagps-from-type-alist-works-right
                                   (v (syntax-ev x a))
                                   (w (syntax-ev y a)))
           :in-theory (disable  show-unique-subbagps-from-type-alist-works-right)))
  :rule-classes (:rewrite :forward-chaining))

;bzo any tests for this? go ahead and make the :meta rule?
(defthm pseudo-termp-of-hyp-for-show-unique-subbagps-from-type-alist
  (implies (and (acl2::type-alistp type-alist)
                (acl2::type-alistp whole-type-alist)
                )
           (pseudo-termp (hyp-for-show-unique-subbagps-from-type-alist x y bag n type-alist whole-type-alist flg)))
  :hints (("Goal" :in-theory (enable HYP-FOR-SHOW-UNIQUE-SUBBAGPS-FROM-TYPE-ALIST-fn))))

;;
;;
;; disjoint
;;
;;


;old stuff
(in-theory (disable unique-subbagps-from-unique-subbagps-and-subbagp))


(defignored show-disjoint-from-type-alist a (x y n type-alist whole-type-alist )
  (declare (type t x y type-alist whole-type-alist)
           (type (unsigned-byte 16) n)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp x)
                              (pseudo-termp y))
                  :guard-hints  (("Goal" :do-not '(preprocess)))
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))))
  (if (endp type-alist)
      nil
    (let* ((entry (car type-alist))
           (fact (car entry)))
      (or (and (consp fact)
               (or (and (equal (car fact) 'disjoint)
                        (ts-non-nil (cadr entry))
                        (or (and (show-subbagp-from-type-alist x (cadr fact) n whole-type-alist whole-type-alist 1)
                                 (show-subbagp-from-type-alist y (caddr fact) n whole-type-alist whole-type-alist 1))
                            (and (show-subbagp-from-type-alist y (cadr fact) n whole-type-alist whole-type-alist 1)
                                 (show-subbagp-from-type-alist x (caddr fact) n whole-type-alist whole-type-alist 1)))
                        (equal nil (cdddr fact))
                        )
                   (and (equal (car fact) 'unique)
                        (ts-non-nil (cadr entry))
                        (show-unique-subbagps-from-type-alist x y (cadr fact) n whole-type-alist whole-type-alist 1)
                        (equal nil (cddr fact)))))
          (show-disjoint-from-type-alist x y n (cdr type-alist) whole-type-alist)))))

(defirrelevant show-disjoint-from-type-alist 1 a (x y n type-alist whole-type-alist )
  :hints (("goal" :in-theory (enable
                              show-disjoint-from-type-alist-fn
                              show-subbagp-from-type-alist-irrelevant
                              HYP-FOR-SHOW-UNIQUE-SUBBAGPS-FROM-TYPE-ALIST-irrelevant
                              HYP-FOR-SHOW-SUBBAGP-FROM-TYPE-ALIST-irrelevant
                              ))))

(defignored hyp-for-show-disjoint-from-type-alist a (x y n type-alist whole-type-alist)
  (declare (type t x y type-alist whole-type-alist)
           (type (unsigned-byte 16) n)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp x)
                              (pseudo-termp y))
                  :guard-hints  (("Goal" :do-not '(preprocess)))
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))))
  (if (endp type-alist)
      nil
    (let* ((entry (car type-alist))
           (fact (car entry)))
      (or (and (consp fact)
               (or (and (equal (car fact) 'disjoint)
                        (ts-non-nil (cadr entry))
                        (equal nil (cdddr fact))
                        (or (conjoin-fact-and-two-hyps fact
                              (hyp-for-show-subbagp-from-type-alist
                               x (cadr fact) n whole-type-alist whole-type-alist 1)
                              (hyp-for-show-subbagp-from-type-alist
                               y (caddr fact) n whole-type-alist whole-type-alist 1))
                            (conjoin-fact-and-two-hyps fact
                              (hyp-for-show-subbagp-from-type-alist
                               y (cadr fact) n whole-type-alist whole-type-alist 1)
                              (hyp-for-show-subbagp-from-type-alist
                               x (caddr fact) n whole-type-alist whole-type-alist 1))))
                   (and (equal (car fact) 'unique)
                        (ts-non-nil (cadr entry))
                        (equal nil (cddr fact))
                        (conjoin-fact-and-hyp fact
                          (hyp-for-show-unique-subbagps-from-type-alist
                           x y (cadr fact) n whole-type-alist whole-type-alist 1)))))
          (hyp-for-show-disjoint-from-type-alist x y n (cdr type-alist) whole-type-alist)))))

(defirrelevant hyp-for-show-disjoint-from-type-alist 1 a (x y n type-alist whole-type-alist)
  :hints (("goal" :in-theory (enable
                              hyp-for-show-disjoint-from-type-alist-fn
                              hyp-for-show-subbagp-from-type-alist-irrelevant
                              hyp-for-show-unique-subbagps-from-type-alist-irrelevant
                              ))))

(defthm show-disjoint-from-type-alist-iff-hyp-for-show-disjoint-from-type-alist
  (iff (show-disjoint-from-type-alist x y n type-alist whole-type-alist)
       (hyp-for-show-disjoint-from-type-alist x y n type-alist whole-type-alist))
  :hints (("Goal" :in-theory (enable show-disjoint-from-type-alist-fn
                                     hyp-for-show-disjoint-from-type-alist-fn
                                     ))))

(defthm show-disjoint-from-type-alist-works-right
  (implies (and (syntax-ev (hyp-for-show-disjoint-from-type-alist x y n type-alist whole-type-alist) a)
                (hyp-for-show-disjoint-from-type-alist x y n type-alist whole-type-alist))
           (disjoint (syntax-ev x a)
                     (syntax-ev y a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (hyp-for-show-disjoint-from-type-alist-fn
                            *TRIGGER*-UNIQUE-SUBBAGPS-IMPLIES-DISJOINTNESS
                            show-unique-subbagps-from-type-alist-works-right
;                            show-subbagp-from-type-alist-works-right-2
                            )
                           ())))
  :rule-classes (:rewrite :forward-chaining))

(defthm pseudo-termp-of-hyp-for-show-disjoint-from-type-alist
  (implies (and (acl2::type-alistp type-alist)
                (acl2::type-alistp whole-type-alist)
                )
           (pseudo-termp (hyp-for-show-disjoint-from-type-alist x y n type-alist whole-type-alist)))
  :hints (("Goal" :in-theory (enable HYP-FOR-SHOW-DISJOINT-FROM-TYPE-ALIST-fn))))

(defun show-disjoint-from-mfc (term mfc state)
  (declare (type t term mfc state)
           (ignore state)
           (xargs :guard (pseudo-termp term)
                  ))
  (if (and (consp term)    ;well-formedness checks, should always succeed
           (equal (car term) 'disjoint)
           )
      (let* ((type-alist (acl2::mfc-type-alist mfc))
             (len (usb16-fix (len type-alist))))
        (if (show-disjoint-from-type-alist-fn nil (cadr term) (caddr term) len type-alist type-alist)
            ''t
          term))
    term))

(defun hyp-for-show-disjoint-from-mfc (term mfc state)
  (declare (type t term mfc state)
           (xargs :guard (pseudo-termp term))
           (ignore state))
  (if (and (consp term) ;well-formedness checks, should always succeed
           (equal (car term) 'disjoint)
           )
      (let* ((type-alist (acl2::mfc-type-alist mfc))
             (len (usb16-fix (len type-alist))))
        (bind-extra-vars-in-hyp (hyp-for-show-disjoint-from-type-alist-fn
                                 nil (cadr term) (caddr term) len type-alist type-alist) term))
    ''nil))

(defthm meta-rule-to-show-disjoint
  (implies (syntax-ev (hyp-for-show-disjoint-from-mfc term mfc state) a)
           (equal (syntax-ev term a)
                  (syntax-ev (show-disjoint-from-mfc term mfc state) a)))
  :hints (("goal" :in-theory (enable
                              hyp-for-show-disjoint-from-type-alist-irrelevant
                              )))
  :rule-classes ((:meta :trigger-fns (disjoint)
                        :backchain-limit-lst 0 ;just in case...
                        )))

(in-theory (disable disjoint-computation))
(in-theory (disable subbagp-disjoint))
;(in-theory (disable meta-rule-to-show-disjoint))



(encapsulate
 ()

 (local
  (defthmd disjoint-test
    (implies (and (subbagp x (append x0 x1))
                  (subbagp (append x0 x1) x2)
                  (subbagp y y1)
                  (subbagp y1 y2)
                  (disjoint x2 y2))
;(disjoint x1 y1))
             (disjoint x y))
       :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-disjoint
                                                    hide-disjoint-forward hide-unique-forward
                                                    HIDE-SUBBAGP-FORWARD)
                                                  (theory 'minimal-theory))))))

 (local
  (defthmd disjoint-test1
    (implies (and (subbagp x x1)
                  (subbagp x1 (append x2 x3))
                  (subbagp y y1)
                  (subbagp y1 y2)
                  (disjoint x1 y2))
             (disjoint x y))
           :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-disjoint
                                                    hide-disjoint-forward hide-unique-forward
                                                    HIDE-SUBBAGP-FORWARD)
                                                  (theory 'minimal-theory))))))

 (local
  (defthmd disjoint-test2
    (implies (and (subbagp x x0)
                  (subbagp y y0)
                  (unique (append x0 y0)))
             (disjoint x y))
           :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-disjoint
                                                    hide-disjoint-forward hide-unique-forward
                                                    HIDE-SUBBAGP-FORWARD)
                                                  (theory 'minimal-theory))))))

 (local
  (defthmd disjoint-test3
    (implies (and (subbagp x (append x1 x2))
                  (subbagp (append x1 x2) x3)
                  (subbagp y y1)
                  (disjoint y1 x3))
             (disjoint x y))
           :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-disjoint
                                                    hide-disjoint-forward hide-unique-forward
                                                    HIDE-SUBBAGP-FORWARD)
                                                  (theory 'minimal-theory))))))

 (local
  (defthmd disjoint-test4
    (implies (and (subbagp x x0)
                  (subbagp y y0)
                  (subbagp (append x0 y0) z)
                  (subbagp z z0)
                  (subbagp z0 z1)
                  (unique z1)
                  ;(unique z0)
                  )
             (disjoint x y))
           :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-disjoint
                                                    ;hide-disjoint-forward hide-unique-forward
                                                    ;HIDE-SUBBAGP-FORWARD
                                                    )
                                                  (theory 'minimal-theory))))))

 (local
  (defthmd disjoint-test5
    (implies (and (subbagp y v)
                  (subbagp w u)
                  (memberp x w)
                  (disjoint u v)
                  (memberp x y)
                  )
             (disjoint w y))
           :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-disjoint
                                                    hide-disjoint-forward hide-unique-forward
                                                    HIDE-SUBBAGP-FORWARD)
                                                  (theory 'minimal-theory)))))))






;;
;;
;; rule to show memberp
;;
;;

(defignored show-memberp-from-type-alist a (v x n type-alist whole-type-alist perform-syntax-test)
  (declare (type t v x type-alist whole-type-alist)
           (type (unsigned-byte 16) n)
           (type bit perform-syntax-test)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp v)
                              (pseudo-termp x))
                  :guard-hints  (("Goal" :do-not '(preprocess)))
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))))
  (if (and (equal 1 perform-syntax-test)
           (syntax-memberp v x) ;we can tell just by looking at v and x that a is a memberp of x
           )
      t
    (if (endp type-alist)
        nil
      (let* ((entry (car type-alist))
             (fact (car entry)))
        (or (and (consp fact)
                 (or (and (equal (car fact) 'subbagp)
                          (ts-non-nil (cadr entry))
                          (syntax-memberp v (cadr fact))
                          (show-subbagp-from-type-alist (caddr fact) x n whole-type-alist whole-type-alist 1)
                          (equal nil (cdddr fact))
                          )
                     (and (or (equal (car fact) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                              (equal (car fact) 'acl2::member-equal))
                          (ts-non-nil (cadr entry))
                          (equal (cadr fact) v)
                          (show-subbagp-from-type-alist (caddr fact) x n whole-type-alist whole-type-alist 1)
                          (equal nil (cdddr fact))
                          )))
            (show-memberp-from-type-alist v x n (cdr type-alist) whole-type-alist 0))))))

(defirrelevant show-memberp-from-type-alist 1 a (v x n type-alist whole-type-alist perform-syntax-test)
  :hints (("goal" :in-theory (enable
                              show-memberp-from-type-alist-fn
                              syntax-memberp-irrelevant
                              show-subbagp-from-type-alist-irrelevant
                              HYP-FOR-SHOW-SUBBAGP-FROM-TYPE-ALIST-irrelevant
                              ))))

(defignored hyp-for-show-memberp-from-type-alist a (v x n type-alist whole-type-alist perform-syntax-test)
  (declare (type t v x type-alist whole-type-alist)
           (type (unsigned-byte 16) n)
           (type bit perform-syntax-test)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp v)
                              (pseudo-termp x))
                  :guard-hints  (("Goal" :do-not '(preprocess)))
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))))
  (if (and (equal 1 perform-syntax-test)
           (syntax-memberp v x) ;we can tell just by looking at v and x that a is a memberp of x
           )
      ''t
    (if (endp type-alist)
        nil
      (let* ((entry (car type-alist))
             (fact (car entry)))
        (or (and (consp fact)
                 (or (and (equal (car fact) 'subbagp)
                          (ts-non-nil (cadr entry))
                          (syntax-memberp v (cadr fact))
                          (equal nil (cdddr fact))
                          (conjoin-fact-and-hyp fact
                            (hyp-for-show-subbagp-from-type-alist
                             (caddr fact) x n whole-type-alist whole-type-alist 1)))
                     (and (or (equal (car fact) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                              (equal (car fact) 'acl2::member-equal))
                          (ts-non-nil (cadr entry))
                          (equal (cadr fact) v)
                          (equal nil (cdddr fact))
                          (conjoin-fact-and-hyp fact
                            (hyp-for-show-subbagp-from-type-alist
                             (caddr fact) x n whole-type-alist whole-type-alist 1))
                          )))
            (hyp-for-show-memberp-from-type-alist v x n (cdr type-alist) whole-type-alist 0))))))

(defirrelevant hyp-for-show-memberp-from-type-alist 1 a (v x n type-alist whole-type-alist perform-syntax-test)
  :hints (("goal" :in-theory (enable
                              hyp-for-show-memberp-from-type-alist-fn
                              syntax-memberp-irrelevant
                              hyp-for-show-subbagp-from-type-alist-irrelevant
                              ))))

(defthm show-memberp-from-type-alist-iff-hyp-for-show-memberp-from-type-alist
  (iff (show-memberp-from-type-alist x y n type-alist whole-type-alist flg)
       (hyp-for-show-memberp-from-type-alist x y n type-alist whole-type-alist flg))
  :hints (("Goal" :in-theory (enable show-memberp-from-type-alist-fn
                                     hyp-for-show-memberp-from-type-alist-fn
                                     ))))

(defthm pseudo-termp-of-hyp-for-show-memberp-from-type-alist
  (implies (and (acl2::type-alistp type-alist)
                (acl2::type-alistp whole-type-alist)
                )
           (pseudo-termp (hyp-for-show-memberp-from-type-alist x y n type-alist whole-type-alist flg)))
  :hints (("Goal" :in-theory (enable HYP-FOR-SHOW-MEMBERP-FROM-TYPE-ALIST-fn))))

(defthm show-memberp-from-type-alist-works-right
  (implies (and (syntax-ev (hyp-for-show-memberp-from-type-alist x y n type-alist whole-type-alist flg) a)
                (hyp-for-show-memberp-from-type-alist x y n type-alist whole-type-alist flg)
                )
           (memberp (syntax-ev x a)
                    (syntax-ev y a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (
          ("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (hyp-for-show-memberp-from-type-alist-fn
                            )
                           ()))))

(defthm hyp-for-show-memberp-from-type-alist-equal-t-rewrite
  (equal (equal (hyp-for-show-memberp-from-type-alist x y n type-alist whole-type-alist flg)
                ''t)
         (and (equal 1 flg) (syntax-memberp x y)))
  :hints (("Goal" :in-theory (enable hyp-for-show-memberp-from-type-alist-fn))))

(defun show-memberp-from-mfc (term mfc state)
  (declare (ignore state)
           (type t term mfc state)
           (xargs :guard (pseudo-termp term)))
  (if (and (consp term)
           (or (equal (car term) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
               (equal (car term) 'acl2::member-equal))
           )
      (let* ((type-alist (acl2::mfc-type-alist mfc))
             (len (usb16-fix (len type-alist))))
        (if (show-memberp-from-type-alist-fn nil (cadr term) (caddr term) len type-alist type-alist 1)
            ''t
          term))
    term))

(defun hyp-for-show-memberp-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (and (consp term)
           (or (equal (car term) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
               (equal (car term) 'acl2::member-equal))
           )
      (let* ((type-alist (acl2::mfc-type-alist mfc))
             (len (usb16-fix (len type-alist))))
        (bind-extra-vars-in-hyp (hyp-for-show-memberp-from-type-alist-fn
                                 nil (cadr term) (caddr term) len type-alist type-alist 1) term))
    ''nil))

(defthm meta-rule-to-show-memberp
  (implies (syntax-ev (hyp-for-show-memberp-from-mfc term mfc state) a)
           (iff (syntax-ev term a)
                (syntax-ev (show-memberp-from-mfc term mfc state) a)))
  :rule-classes ((:meta :trigger-fns (acl2::member list::memberp)
                        :backchain-limit-lst 0 ;just in case...
                        ))
  :hints (("Goal" :in-theory (enable
                              hyp-for-show-memberp-from-type-alist-irrelevant
                              )
           :do-not-induct t :do-not '(generalize eliminate-destructors))))

(in-theory (disable memberp-computation))

(encapsulate
 ()

 (local
  (defthmd memberp-test
    (implies (and (memberp x z)
                  (subbagp z w)
                  (subbagp w y)
                  (subbagp y u))
             (memberp x (append u v)))
    :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-memberp)
                                               (theory 'minimal-theory))))))

 (local
  (defthmd memberp-test1
    (implies (and (memberp x z)
                  (subbagp z w)
                  (subbagp w y))
             (memberp x y))
        :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-memberp)
                                                   (theory 'minimal-theory))))))



 (local
  (defthmd memberp-test2
    (implies (and (memberp x (append u v))
                  (subbagp (append u v) w)
                  (subbagp w y))
             (memberp x y))
        :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-memberp)
                                               (theory 'minimal-theory))))))

 )

;;
;;
;; rule to show non-memberp
;;
;;



(local
 (defthm cons-iff
   (iff (cons x y)
        t)))

(defignored show-non-memberp-from-type-alist a (v x n type-alist whole-type-alist)
  (declare (type t v x type-alist whole-type-alist)
           (type (unsigned-byte 16) n)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp v)
                              (pseudo-termp x))
                  :guard-hints  (("Goal" :do-not '(preprocess)))
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))))
  (if (endp type-alist)
      nil
    (let* ((entry (car type-alist))
           (fact (car entry)))
      (or (and (consp fact)
               (or (and (equal (car fact) 'unique)
                        (ts-non-nil (cadr entry))
                        (show-unique-subbagps-from-type-alist
                         `(cons ,v 'nil) x (cadr fact) n whole-type-alist whole-type-alist 1)
                        (equal nil (cddr fact))
                        )
                   (and (equal (car fact) 'disjoint)
                        (ts-non-nil (cadr entry))
                        (or (and (show-memberp-from-type-alist
                                  v (cadr fact) n whole-type-alist whole-type-alist 1)
                                 (show-subbagp-from-type-alist
                                  x (caddr fact) n whole-type-alist whole-type-alist 1))
                            (and (show-memberp-from-type-alist
                                  v (caddr fact) n whole-type-alist whole-type-alist 1)
                                 (show-subbagp-from-type-alist
                                  x (cadr fact) n whole-type-alist whole-type-alist 1)))
                        (equal nil (cdddr fact)))))
          (show-non-memberp-from-type-alist v x n (cdr type-alist) whole-type-alist)))))


(defirrelevant show-non-memberp-from-type-alist 1 a (v x n type-alist whole-type-alist)
  :hints (("goal" :in-theory (enable
                              show-non-memberp-from-type-alist-fn
                              show-memberp-from-type-alist-irrelevant
                              show-subbagp-from-type-alist-irrelevant
                              show-unique-subbagps-from-type-alist-irrelevant
                              HYP-FOR-SHOW-SUBBAGP-FROM-TYPE-ALIST-irrelevant
                              HYP-FOR-SHOW-MEMBERP-FROM-TYPE-ALIST-irrelevant
                              hyp-for-show-unique-subbagps-from-type-alist-irrelevant
                              ))))

(defignored hyp-for-show-non-memberp-from-type-alist a (v x n type-alist whole-type-alist)
  (declare (type t v x type-alist whole-type-alist)
           (type (unsigned-byte 16) n)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp v)
                              (pseudo-termp x))
                  :guard-hints  (("Goal" :do-not '(preprocess)))
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))))
  (if (endp type-alist)
      nil
    (let* ((entry (car type-alist))
           (fact (car entry)))
      (or (and (consp fact)
               (or (and (equal (car fact) 'unique)
                        (ts-non-nil (cadr entry))
                          (equal nil (cddr fact))
                          (conjoin-fact-and-hyp fact
                            (hyp-for-show-unique-subbagps-from-type-alist
                             `(cons ,v 'nil) x (cadr fact) n whole-type-alist whole-type-alist 1)))
                   (and (equal (car fact) 'disjoint)
                        (ts-non-nil (cadr entry))
                        (equal nil (cdddr fact))
                        (or (conjoin-fact-and-two-hyps fact
                              (hyp-for-show-memberp-from-type-alist
                               v (cadr fact) n whole-type-alist whole-type-alist 1)
                              (hyp-for-show-subbagp-from-type-alist
                               x (caddr fact) n whole-type-alist whole-type-alist 1))
                            (conjoin-fact-and-two-hyps fact
                              (hyp-for-show-memberp-from-type-alist
                               v (caddr fact) n whole-type-alist whole-type-alist 1)
                              (hyp-for-show-subbagp-from-type-alist
                               x (cadr fact) n whole-type-alist whole-type-alist 1))))))
          (hyp-for-show-non-memberp-from-type-alist v x n (cdr type-alist) whole-type-alist)))))

(defirrelevant hyp-for-show-non-memberp-from-type-alist 1 a (v x n type-alist whole-type-alist)
  :hints (("goal" :in-theory (enable
                              hyp-for-show-non-memberp-from-type-alist-fn
                              hyp-for-show-unique-subbagps-from-type-alist-irrelevant
                              hyp-for-show-memberp-from-type-alist-irrelevant
                              hyp-for-show-subbagp-from-type-alist-irrelevant
                              ))))

(defthm show-non-memberp-from-type-alist-iff-hyp-for-show-non-memberp-from-type-alist
  (iff (show-non-memberp-from-type-alist v x n type-alist whole-type-alist)
       (hyp-for-show-non-memberp-from-type-alist v x n type-alist whole-type-alist))
  :hints (("Goal" :in-theory (enable show-non-memberp-from-type-alist-fn
                                     hyp-for-show-non-memberp-from-type-alist-fn
                                     ))))


(local (in-theory (enable not-memberp-from-disjointness-two
                          not-memberp-from-disjointness-one
                          not-memberp-from-unique-subbagps-of-something-unique-alt
                          not-memberp-from-unique-subbagps-of-something-unique)))

(defthm show-non-memberp-from-type-alist-works-right
  (implies (and (syntax-ev (hyp-for-show-non-memberp-from-type-alist v x n type-alist whole-type-alist) a)
                (hyp-for-show-non-memberp-from-type-alist v x n type-alist whole-type-alist)
                )
           (not (memberp (syntax-ev v a)
                         (syntax-ev x a))))
  :rule-classes (:rewrite :forward-chaining)
  :hints (
          ("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (hyp-for-show-non-memberp-from-type-alist-fn
                            )
                           ()))))

#+joe
(and acl2::stable-under-simplificationp
               `(:in-theory (e/d (hyp-for-show-non-memberp-from-type-alist
                                  )
                                 (show-unique-subbagps-from-type-alist-works-right))
                            :expand ((HYP-FOR-SHOW-NON-MEMBERP-FROM-TYPE-ALIST A X N TYPE-ALIST WHOLE-TYPE-ALIST))
                            :use (:instance show-unique-subbagps-from-type-alist-works-right
                                            (alist alist)
                                            (x (LIST* 'CONS A '('NIL)))
                                            (y X)
                                            (bag  (CADAR (CAR TYPE-ALIST)))
                                            (n n)
                                            (type-alist whole-type-alist)
                                            (flg 1))))

#+joe
(defthm show-non-memberp-from-type-alist-works-right-2
  (implies (equal (hyp-for-show-non-memberp-from-type-alist a x n type-alist whole-type-alist)
                 ''t)
           (not (memberp (syntax-ev a alist)
                         (syntax-ev x alist))))
  :hints (("Goal" :in-theory (disable show-non-memberp-from-type-alist-works-right)
           :use (:instance show-non-memberp-from-type-alist-works-right))))

(defthm pseudo-termp-of-hyp-for-show-non-memberp-from-type-alist
  (implies (and (acl2::type-alistp type-alist)
                (acl2::type-alistp whole-type-alist)
                )
           (pseudo-termp (hyp-for-show-non-memberp-from-type-alist v x n type-alist whole-type-alist)))
  :hints (("Goal" :in-theory (enable HYP-FOR-SHOW-NON-MEMBERP-FROM-TYPE-ALIST))))

(defun show-non-memberp-from-mfc (term mfc state)
  (declare (ignore state)
           (type t term mfc state)
           (xargs :guard (pseudo-termp term)))
  (if (and (consp term)
           (or (equal (car term) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
               (equal (car term) 'acl2::member-equal))
           )
      (let* ((type-alist (acl2::mfc-type-alist mfc))
            (len  (usb16-fix (len type-alist))))
        (if (show-non-memberp-from-type-alist-fn nil (cadr term) (caddr term) len type-alist type-alist)
            ''nil ;we're rewriting a call to memberp to nil
          term))
    term))

(defun hyp-for-show-non-memberp-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (and (consp term)
           (or (equal (car term) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
               (equal (car term) 'acl2::member-equal))
           )
      (let* ((type-alist (acl2::mfc-type-alist mfc))
            (len  (usb16-fix (len type-alist))))
        (bind-extra-vars-in-hyp (hyp-for-show-non-memberp-from-type-alist-fn
                                 nil (cadr term) (caddr term) len type-alist type-alist) term))
    ''nil))

(defthm meta-rule-to-show-non-memberp
  (implies (syntax-ev (hyp-for-show-non-memberp-from-mfc term mfc state) a)
           (iff (syntax-ev term a)
                (syntax-ev (show-non-memberp-from-mfc term mfc state) a)))
  :rule-classes ((:meta :trigger-fns (list::memberp acl2::member)
                        :backchain-limit-lst 0 ;just in case...
                        ))
  :hints (("Goal" :in-theory (enable
                              hyp-for-show-non-memberp-from-type-alist-irrelevant
                              )
           :do-not-induct t :do-not '(generalize eliminate-destructors))))


(in-theory (disable non-memberp-computation))


(encapsulate
 ()

 (local
  (defthmd non-memberp-test
    (implies (and (subbagp y v)
                  (subbagp w u)
                  (memberp x w)
                  (disjoint u v))
             (not (memberp x y)))
    :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-non-memberp)
                                               (theory 'minimal-theory))))))
 )



;This failed before Matt Kaufmann changed ACL2 to allow me to insert
;calls to SYNP in the generated hypotheses for my :meta rules.  It
;failed because variables in the generated hyp which do not appear in
;the LHS are treated as free when the hyp is relieved, and only one
;match is tried (!).  In this example, when relieving the hyp, ACL2
;found a spurious match and missed the real one.  Binding the
;variables to themselves using SYNP fixes that.

(encapsulate
 ()
 (local
  (defthmd non-memberp-test1
    (implies (and (not (disjoint q w))
                  (not (subbagp g h))
                  (subbagp p q)
                  (subbagp q (append r s))
                  (subbagp (append r s) v)
                  (memberp a j)
                  (subbagp j (append k l))
                  (subbagp (append k l) m)
                  (disjoint m v)
                  (disjoint i o)
                  )
             (not (memberp a p)))
    :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-non-memberp)
                                               (theory 'minimal-theory)))))))


(in-theory (disable hide-subbagp-forward
                    hide-subbagp-z-z
                    hide-unique-forward
                    hide-disjoint-forward
                    subbagp-pair-x-x-y-y
                    hide-memberp-forward
                    *trigger*-syntax-ev-syntax-subbagp
                    syntactic-membership-meta-rule
                    ;run-remove-1-helper2
                    ))




;;
;;
;;
;;
;;


;move this stuff to meta.lisp?

(defignored syntax-unique-memberps a (v b bag)
  (declare (type t v b bag)
           (xargs :guard (and (pseudo-termp v)
                              (pseudo-termp b)
                              (pseudo-termp bag))))
  (met ((hit1 new-bag)
        (syntax-remove-1 v bag))
       (and hit1
            (met ((hit2 newer-bag)
                  (syntax-remove-1 b new-bag))
                 (declare (ignore newer-bag))
                 hit2))))

(defirrelevant syntax-unique-memberps 1 a (v b bag)
  :hints (("goal" :in-theory (enable
                              syntax-unique-memberps-fn
                              syntax-remove-1-irrelevant
                              syntax-memberp-irrelevant
                              ))))

(defthm syntax-unique-memberps-implies-unique-memberps
  (implies (syntax-unique-memberps v b bag)
           (unique-memberps (syntax-ev v a)
                            (syntax-ev b a)
                            (syntax-ev bag a)))
  :hints (("Goal" :in-theory (enable unique-memberps
                                     syntax-unique-memberps-fn
                                     )))
  :rule-classes (:rewrite :forward-chaining))


(defignored syntax-unique-memberp-and-subbagp a (v x bag)
  (declare (type t v x bag)
           (xargs :guard (and (pseudo-termp v)
                              (pseudo-termp x)
                              (pseudo-termp bag))))
  (met ((hit1 new-bag)
        (syntax-remove-1 v bag))
       (and hit1
            (met ((hit2 new-x newer-bag)
                  (syntax-remove-bag x new-bag))
                 (declare (ignore newer-bag))
                 (and hit2
                      (equal ''nil ;bzo what about other final cdrs (also an issue elsewhere?)
                             new-x))))))

(defirrelevant syntax-unique-memberp-and-subbagp 1 a (v x bag)
  :hints (("goal" :in-theory (enable
                              syntax-unique-memberp-and-subbagp-fn
                              syntax-remove-1-irrelevant
                              syntax-remove-bag-irrelevant
                              SYNTAX-MEMBERP-irrelevant
                              ))))

;move
(defthm subbagp-from-syntax-remove-bag
  (implies (and (val 0 (syntax-remove-bag x z))               ;z is a free var
                (equal ''nil (val 1 (syntax-remove-bag x z)))
                (subbagp (syntax-ev z a) y))
           (subbagp (syntax-ev x a)
                    y))
  :hints (("Goal" :use (:instance subbagp-chaining (x (syntax-ev x a)) (y y) (z (syntax-ev z a)))))
  :rule-classes (:rewrite :forward-chaining))

(defthm syntax-unique-memberp-and-subbagp-implies-unique-memberp-and-subbagp
  (implies (syntax-unique-memberp-and-subbagp v x bag)
           (unique-memberp-and-subbagp (syntax-ev v a)
                                       (syntax-ev x a)
                                       (syntax-ev bag a)))
  :hints (("Goal" :in-theory (enable unique-memberp-and-subbagp
                                     syntax-unique-memberp-and-subbagp)))
  :rule-classes (:rewrite :forward-chaining))

(defun show-unique-memberp-and-subbagp-from-type-alist-memberp-case (a v x bag entry fact type-alist w whole-type-alist)
  (declare (ignore type-alist type-alist)
           (xargs :guard  (and (acl2::type-alistp type-alist)
                               (acl2::type-alistp whole-type-alist)
                               (not (endp type-alist))
                               (consp fact)
                               (equal entry (car type-alist))
                               (equal fact (car entry))
                               (or (equal (car fact) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                                   (equal (car fact) 'acl2::member-equal))
                               (pseudo-termp v)
                               (pseudo-termp x)
                               (pseudo-termp bag)
                               (equal w (usb16-fix (len whole-type-alist))))
                  :guard-hints  (("Goal" :do-not '(preprocess)))))
  (and (equal v (cadr fact))
       (ts-non-nil (cadr entry))
       (show-unique-subbagps-from-type-alist
        x (caddr fact) bag w whole-type-alist whole-type-alist 1)
       (equal nil (cdddr fact))))

(defignored show-unique-memberp-and-subbagp-from-type-alist
  a (v x bag n type-alist w whole-type-alist perform-syntax-test)
  (declare (type t v x bag type-alist whole-type-alist)
           (type (unsigned-byte 16) n w)
           (type bit perform-syntax-test)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp v)
                              (pseudo-termp x)
                              (pseudo-termp bag)
                              (equal w (usb16-fix (len whole-type-alist)))
                              )
                  :measure `((1 . ,(+ 1 (nfix n))) . ,(len type-alist))
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))
                  :guard-hints (("Goal" :in-theory (disable show-unique-memberp-and-subbagp-from-type-alist-memberp-case)
                                 :do-not '(preprocess))) ))
  (if (and (equal 1 perform-syntax-test)
           (syntax-unique-memberp-and-subbagp v x bag)
           )
      t
    (if (zp n)
        nil
      (if (endp type-alist)
          nil
        (let* ((entry (car type-alist))
               (fact (car entry)))
          (or (and (consp fact)
                   (or (and (equal (car fact) 'subbagp)
                            (ts-non-nil (cadr entry))
                            (or (and (syntax-memberp v (cadr fact))
                                     (show-unique-subbagps-from-type-alist
                                      x (caddr fact) bag w whole-type-alist whole-type-alist 1))
                                (and (syntax-subbagp x (cadr fact))
                                     (show-unique-memberp-and-subbagp-from-type-alist
                                      v (caddr fact) bag (1- n) whole-type-alist w whole-type-alist 1))
                                (and (syntax-subbagp (caddr fact) bag) ;how did we verify these guards? <-- huh?
                                     (show-unique-memberp-and-subbagp-from-type-alist
                                      v x (cadr fact) (1- n) whole-type-alist w whole-type-alist 0)))
                            (equal nil (cdddr fact)))
                       (and (or (equal (car fact) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                                (equal (car fact) 'acl2::member-equal))
                            (show-unique-memberp-and-subbagp-from-type-alist-memberp-case a v x bag entry fact type-alist w whole-type-alist)
                            )))
              (show-unique-memberp-and-subbagp-from-type-alist
               v x bag n (cdr type-alist) w whole-type-alist 0)))))))



(defirrelevant show-unique-memberp-and-subbagp-from-type-alist
  1 a (v x bag n type-alist w whole-type-alist perform-syntax-test)
  :hints (("goal" :in-theory
           (enable
            show-unique-memberp-and-subbagp-from-type-alist
            syntax-memberp-irrelevant
            show-unique-subbagps-from-type-alist-irrelevant
            SYNTAX-SUBBAGP-irrelevant
            HYP-FOR-SHOW-UNIQUE-SUBBAGPS-FROM-TYPE-ALIST-irrelevant
            SYNTAX-UNIQUE-MEMBERP-AND-SUBBAGP-irrelevant
            ))))

(defun hyp-for-show-unique-memberp-and-subbagp-from-type-alist-subbagp-case-1 (a v x bag entry fact type-alist w whole-type-alist)
  (declare (ignore type-alist entry)
           (xargs :guard  (and (acl2::type-alistp type-alist)
                               (acl2::type-alistp whole-type-alist)
                               (not (endp type-alist))
                               (consp fact)
                               (equal entry (car type-alist))
                               (equal fact (car entry))
                               (equal (car fact) 'subbagp)

                               (pseudo-termp v)
                               (pseudo-termp x)
                               (pseudo-termp bag)
                               (equal w (usb16-fix (len whole-type-alist))))
                  :guard-hints  (("Goal" :do-not '(preprocess)))))
  (and (syntax-memberp v (cadr fact))
       (conjoin-fact-and-hyp
        fact (hyp-for-show-unique-subbagps-from-type-alist
              x (caddr fact) bag w whole-type-alist whole-type-alist 1))))

(defun hyp-for-show-unique-memberp-and-subbagp-from-type-alist-memberp-case (a v x bag entry fact type-alist w whole-type-alist)
  (declare (ignore type-alist type-alist)
           (xargs :guard  (and (acl2::type-alistp type-alist)
                               (acl2::type-alistp whole-type-alist)
                               (not (endp type-alist))
                               (consp fact)
                               (equal entry (car type-alist))
                               (equal fact (car entry))
                               (or (equal (car fact) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                                   (equal (car fact) 'acl2::member-equal))
                               (pseudo-termp v)
                               (pseudo-termp x)
                               (pseudo-termp bag)
                               (equal w (usb16-fix (len whole-type-alist))))
                  :guard-hints  (("Goal" :do-not '(preprocess)))))
  (and (equal v (cadr fact))
       (ts-non-nil (cadr entry))
       (equal nil (cdddr fact))
       (conjoin-fact-and-hyp
        fact (hyp-for-show-unique-subbagps-from-type-alist
              x (caddr fact) bag w whole-type-alist whole-type-alist 1))))


(defthm show-unique-memberp-and-subbagp-from-type-alist-memberp-case-iff
  (implies
   (force fact) ; added with soundness bug fix for v3-6-1
   (iff (show-unique-memberp-and-subbagp-from-type-alist-memberp-case a v x bag entry fact type-alist w whole-type-alist)
        (hyp-for-show-unique-memberp-and-subbagp-from-type-alist-memberp-case a v x bag entry fact type-alist w whole-type-alist))))

;(in-theory (disable show-unique-memberp-and-subbagp-from-type-alist-memberp-case
;                    hyp-for-show-unique-memberp-and-subbagp-from-type-alist-memberp-case))


(defignored hyp-for-show-unique-memberp-and-subbagp-from-type-alist
  a (v x bag n type-alist w whole-type-alist perform-syntax-test)
  (declare (type t v x bag type-alist whole-type-alist)
           (type (unsigned-byte 16) n w)
           (type bit perform-syntax-test)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp v)
                              (pseudo-termp x)
                              (pseudo-termp bag)
                              (equal w (usb16-fix (len whole-type-alist))))
                  :measure `((1 . ,(+ 1 (nfix n))) . ,(len type-alist))
                  :guard-hints  (("Goal" :do-not '(preprocess)
                                  :in-theory (disable hyp-for-show-unique-memberp-and-subbagp-from-type-alist-subbagp-case-1
                                                      hyp-for-show-unique-memberp-and-subbagp-from-type-alist-memberp-case)
                                  ))
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)
                           :in-theory (disable hyp-for-show-unique-memberp-and-subbagp-from-type-alist-subbagp-case-1
                                               hyp-for-show-unique-memberp-and-subbagp-from-type-alist-memberp-case)))))
  (if (and (equal 1 perform-syntax-test)
           (syntax-unique-memberp-and-subbagp v x bag))
      ''t
    (if (zp n)
        nil
      (if (endp type-alist)
          nil
        (let* ((entry (car type-alist))
               (fact (car entry)))
          (or (and (consp fact)
                   (or (and (equal (car fact) 'subbagp)
                            (ts-non-nil (cadr entry))
                            (equal nil (cdddr fact))
                            (or (hyp-for-show-unique-memberp-and-subbagp-from-type-alist-subbagp-case-1 a v x bag entry fact type-alist w whole-type-alist)
                                (and (syntax-subbagp x (cadr fact))
                                     (conjoin-fact-and-hyp
                                      fact (hyp-for-show-unique-memberp-and-subbagp-from-type-alist
                                            v (caddr fact) bag (1- n) whole-type-alist w whole-type-alist 1)))
                                (and (syntax-subbagp (caddr fact) bag)
                                     (conjoin-fact-and-hyp
                                      fact (hyp-for-show-unique-memberp-and-subbagp-from-type-alist
                                            v x (cadr fact) (1- n) whole-type-alist w whole-type-alist 0)))))
                       (and (or (equal (car fact) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                                (equal (car fact) 'acl2::member-equal))
                            (hyp-for-show-unique-memberp-and-subbagp-from-type-alist-memberp-case a v x bag entry fact type-alist w whole-type-alist)
                            )))
              (hyp-for-show-unique-memberp-and-subbagp-from-type-alist
               v x bag n (cdr type-alist) w whole-type-alist 0)))))))

(defirrelevant hyp-for-show-unique-memberp-and-subbagp-from-type-alist
  1 a (v x bag n type-alist w whole-type-alist perform-syntax-test)
  :hints (("goal" :in-theory (enable
                              hyp-for-show-unique-memberp-and-subbagp-from-type-alist
                              hyp-for-show-unique-subbagps-from-type-alist-irrelevant
                              syntax-unique-memberp-and-subbagp-irrelevant
                              syntax-memberp-irrelevant
                              SYNTAX-SUBBAGP-irrelevant))))

(defthm show-unique-memberp-and-subbagp-from-type-alist-iff-hyp-for-show-unique-from-type-alist
  (iff (show-unique-memberp-and-subbagp-from-type-alist v x bag n type-alist w whole-type-alist flg)
       (hyp-for-show-unique-memberp-and-subbagp-from-type-alist v x bag n type-alist w whole-type-alist flg))
  :hints (("Goal" :in-theory (enable show-unique-memberp-and-subbagp-from-type-alist
                                     hyp-for-show-unique-memberp-and-subbagp-from-type-alist
                                     ))))

(defthm UNIQUE-MEMBERP-AND-SUBBAGP-WHEN-UNIQUE-SUBBAGPS-AND-MEMBERP-ALT-trigger
  (IMPLIES
   (AND
    (MEMBERP A X)
    (UNIQUE-SUBBAGPS Y X BAG))
   (UNIQUE-MEMBERP-AND-SUBBAGP A Y BAG)))

(defthmd unique-memberp-and-subbagp-subbagp-trigger
  (implies
   (and
    (subbagp b1 b2)
    (memberp v b1)
    (unique-subbagps x b2 bag))
   (unique-memberp-and-subbagp v x bag)))

(defthm show-unique-memberp-and-subbagp-from-type-alist-works-right
  (implies (and (syntax-ev (hyp-for-show-unique-memberp-and-subbagp-from-type-alist
                            v x bag n type-alist w whole-type-alist flg) a)
                (hyp-for-show-unique-memberp-and-subbagp-from-type-alist
                 v x bag n type-alist w whole-type-alist flg))
           (unique-memberp-and-subbagp (syntax-ev v a)
                                       (syntax-ev x a)
                                       (syntax-ev bag a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors preprocess
                                       )
           :in-theory (e/d (hyp-for-show-unique-memberp-and-subbagp-from-type-alist
                            unique-memberp-and-subbagp-subbagp-trigger)
                           ())))
  :rule-classes (:rewrite :forward-chaining))


#+joe
(defthm show-unique-memberp-and-subbagp-from-type-alist-works-right-2
  (implies
   (and (equal ''t (hyp-for-show-unique-memberp-and-subbagp-from-type-alist a x bag n type-alist w whole-type-alist flg))
        (hyp-for-show-unique-memberp-and-subbagp-from-type-alist a x bag n type-alist w whole-type-alist flg))
   (unique-memberp-and-subbagp (syntax-ev a alist)
                               (syntax-ev x alist)
                               (syntax-ev bag alist)))
  :hints (("Goal" :use (:instance show-unique-memberp-and-subbagp-from-type-alist-works-right)
           :in-theory (disable  show-unique-memberp-and-subbagp-from-type-alist-works-right))))

;bzo any tests for this? go ahead and make the :meta rule?

(defthm pseudo-termp-of-hyp-for-show-unique-memberp-and-subbagp-from-type-alist
  (implies (and (acl2::type-alistp type-alist)
                (acl2::type-alistp whole-type-alist)
                )
           (pseudo-termp (hyp-for-show-unique-memberp-and-subbagp-from-type-alist x y bag n type-alist w whole-type-alist flg)))
  :hints (("Goal" :in-theory (enable HYP-FOR-SHOW-UNIQUE-MEMBERP-AND-SUBBAGP-FROM-TYPE-ALIST))))


;;meta rule goes here

;;tests go here...















;; Ways to show (unique-memberps a b bag)
;;   Easy case: Discover that (syntax-unique-memberps a b bag).
;;   Find (subbagp BLAH1 BLAH2) where (syntax-memberp a BLAH1), and then show (unique-memberp-and-subbagp b BLAH2 bag).
;;   Find (subbagp BLAH1 BLAH2) where (syntax-memberp b BLAH1), and then show (unique-memberp-and-subbagp a BLAH2 bag).
;;   Find (subbagp BLAH1 BLAH2) where (syntax-subbagp BLAH2 bag), and then show (unique-memberps a b BLAH1).
;;   Find (memberp a BLAH), and then show (unique-memberp-and-subbagp b BLAH bag).
;;   Find (memberp b BLAH), and then show (unique-memberp-and-subbagp a BLAH bag).

(defun show-unique-memberps-from-type-alist-memberp-case (a v b bag entry fact type-alist w whole-type-alist)
  (declare (ignore type-alist)
           (type (unsigned-byte 16) w)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (not (endp type-alist))
                              (equal entry (car type-alist))
                              (consp fact)
                              (equal fact (car entry))
                              (or (equal (car fact) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                                  (equal (car fact) 'acl2::member-equal))
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp v)
                              (pseudo-termp b)
                              (pseudo-termp bag)
                              (equal w (usb16-fix (len whole-type-alist))))
                  :guard-hints  (("Goal" :do-not '(preprocess)))))
  (and(ts-non-nil (cadr entry))
      (or (and (equal v (cadr fact))
               (show-unique-memberp-and-subbagp-from-type-alist
                b (caddr fact) bag w whole-type-alist w whole-type-alist 1))
          (and (equal b (cadr fact))
               (show-unique-memberp-and-subbagp-from-type-alist
                v (caddr fact) bag w whole-type-alist w whole-type-alist 1)))
      (equal nil (cdddr fact))))



(defignored show-unique-memberps-from-type-alist a (v b bag n type-alist w whole-type-alist perform-syntax-test)
  (declare (type t v b bag type-alist whole-type-alist)
           (type (unsigned-byte 16) n w)
           (type bit perform-syntax-test)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp v)
                              (pseudo-termp b)
                              (pseudo-termp bag)
                              (equal w (usb16-fix (len whole-type-alist))))
                  :guard-hints  (("Goal" :in-theory (disable show-unique-memberps-from-type-alist-memberp-case)
                                  :do-not '(preprocess)))
                  :measure `((1 . ,(+ 1 (nfix n))) . ,(len type-alist))
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))))
  (if (and (equal 1 perform-syntax-test)
           (syntax-unique-memberps v b bag))
      t
    (if (or (zp n) (endp type-alist))
        nil
      (let* ((entry (car type-alist))
             (fact (car entry)))
        (or (and (consp fact)
                 (or (and (equal (car fact) 'subbagp)
                          (ts-non-nil (cadr entry))
                          (or (and (syntax-memberp v (cadr fact))
                                   (show-unique-memberp-and-subbagp-from-type-alist
                                    b (caddr fact) bag w whole-type-alist w whole-type-alist 1))
                              (and (syntax-memberp b (cadr fact))
                                   (show-unique-memberp-and-subbagp-from-type-alist
                                    v (caddr fact) bag w whole-type-alist w whole-type-alist 1))
                              (and (syntax-subbagp (caddr fact) bag)
                                   (show-unique-memberps-from-type-alist
                                    v b (cadr fact) (1- n) whole-type-alist w whole-type-alist 0)))
                          (equal nil (cdddr fact)))
                     (and (or (equal (car fact) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                              (equal (car fact) 'acl2::member-equal))
                          (show-unique-memberps-from-type-alist-memberp-case a v b bag entry fact type-alist w whole-type-alist)
                          )))
            (show-unique-memberps-from-type-alist v b bag n (cdr type-alist) w whole-type-alist 0))))))


(defirrelevant show-unique-memberps-from-type-alist 1 a
  (v b bag n type-alist w whole-type-alist perform-syntax-test)
  :hints (("goal" :in-theory (enable
                              show-unique-memberps-from-type-alist
                              syntax-unique-memberps-irrelevant
                              syntax-memberp-irrelevant
                              SYNTAX-SUBBAGP-irrelevant
                              show-unique-memberp-and-subbagp-from-type-alist-irrelevant
                              hyp-for-show-unique-memberp-and-subbagp-from-type-alist-irrelevant
                              ))))

(defun hyp-for-show-unique-memberps-from-type-alist-memberp-case (a v b bag entry fact type-alist w whole-type-alist)
  (declare (ignore type-alist)
           (type (unsigned-byte 16) w)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (not (endp type-alist))
                              (equal entry (car type-alist))
                              (consp fact)
                              (equal fact (car entry))
                              (or (equal (car fact) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                                  (equal (car fact) 'acl2::member-equal))
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp v)
                              (pseudo-termp b)
                              (pseudo-termp bag)
                              (equal w (usb16-fix (len whole-type-alist))))
                  :guard-hints  (("Goal" :do-not '(preprocess)))))
  (and (ts-non-nil (cadr entry))
       (equal nil (cdddr fact))
       (or (and (equal v (cadr fact))
                (conjoin-fact-and-hyp fact
                                      (hyp-for-show-unique-memberp-and-subbagp-from-type-alist
                                       b (caddr fact) bag w whole-type-alist w whole-type-alist 1)))
           (and (equal b (cadr fact))
                (conjoin-fact-and-hyp fact
                                      (hyp-for-show-unique-memberp-and-subbagp-from-type-alist
                                       v (caddr fact) bag w whole-type-alist w whole-type-alist 1))))))


(defthm hyp-for-show-unique-memberps-from-type-alist-memberp-case-iff
  (implies
   (force fact) ; added with soundness bug fix for v3-6-1
   (iff (hyp-for-show-unique-memberps-from-type-alist-memberp-case a v b bag entry fact type-alist w whole-type-alist)
        (show-unique-memberps-from-type-alist-memberp-case a v b bag entry fact type-alist w whole-type-alist))))

(defun hyp-for-show-unique-memberps-from-type-alist-subbagp-case-1 (a v b bag entry fact type-alist w whole-type-alist)
  (declare (ignore type-alist entry)
           (type (unsigned-byte 16) w)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (not (endp type-alist))
                              (equal entry (car type-alist))
                              (consp fact)
                              (equal fact (car entry))
                              (equal (car fact) 'subbagp)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp v)
                              (pseudo-termp b)
                              (pseudo-termp bag)
                              (equal w (usb16-fix (len whole-type-alist))))
                  :guard-hints  (("Goal" :do-not '(preprocess)))))
  (or (and (syntax-memberp v (cadr fact))
           (conjoin-fact-and-hyp fact
                                 (hyp-for-show-unique-memberp-and-subbagp-from-type-alist
                                  b (caddr fact) bag w whole-type-alist w whole-type-alist 1)))
      (and (syntax-memberp b (cadr fact))
           (conjoin-fact-and-hyp fact
                                 (hyp-for-show-unique-memberp-and-subbagp-from-type-alist
                                  v (caddr fact) bag w whole-type-alist w whole-type-alist 1)))
      ))

(defignored hyp-for-show-unique-memberps-from-type-alist a (v b bag n type-alist w whole-type-alist perform-syntax-test)
  (declare (type t v b bag type-alist whole-type-alist)
           (type (unsigned-byte 16) n w)
           (type bit perform-syntax-test)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp v)
                              (pseudo-termp b)
                              (pseudo-termp bag)
                              (equal w (usb16-fix (len whole-type-alist))))
                  :guard-hints  (("Goal" :do-not '(preprocess)
                                  :in-theory (disable hyp-for-show-unique-memberps-from-type-alist-memberp-case
                                                      hyp-for-show-unique-memberps-from-type-alist-subbagp-case-1)
                                  ))
                  :measure `((1 . ,(+ 1 (nfix n))) . ,(len type-alist))
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)
                           :in-theory (disable hyp-for-show-unique-memberps-from-type-alist-subbagp-case-1
                                               hyp-for-show-unique-memberps-from-type-alist-memberp-case)
                           ))))
  (if (and (equal 1 perform-syntax-test)
           (syntax-unique-memberps v b bag)
           )
      ''t
    (if (or (zp n) (endp type-alist))
        nil
      (let* ((entry (car type-alist))
             (fact (car entry)))
        (or (and (consp fact)
                 (or (and (equal (car fact) 'subbagp)
                          (ts-non-nil (cadr entry))
                          (equal nil (cdddr fact))
                          (or (hyp-for-show-unique-memberps-from-type-alist-subbagp-case-1 a v b bag entry fact type-alist w whole-type-alist)
                              (and (syntax-subbagp (caddr fact) bag)
                                   (conjoin-fact-and-hyp fact
                                                         (hyp-for-show-unique-memberps-from-type-alist
                                                          v b (cadr fact) (1- n) whole-type-alist w whole-type-alist 0))))
                          )
                     (and (or (equal (car fact) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                              (equal (car fact) 'acl2::member-equal))
                          (hyp-for-show-unique-memberps-from-type-alist-memberp-case a v b bag entry fact type-alist w whole-type-alist)

                          )))
            (hyp-for-show-unique-memberps-from-type-alist v b bag n (cdr type-alist) w whole-type-alist 0))))))

(defirrelevant hyp-for-show-unique-memberps-from-type-alist 1 a
  (v b bag n type-alist w whole-type-alist perform-syntax-test)
  :hints (("goal" :in-theory (enable
                              hyp-for-show-unique-memberps-from-type-alist
                              syntax-unique-memberps-irrelevant
                              syntax-memberp-irrelevant
                              SYNTAX-SUBBAGP-irrelevant
                              hyp-for-show-unique-memberp-and-subbagp-from-type-alist-irrelevant
                              ))))

(defthm pseudo-termp-of-hyp-for-show-unique-memberps-from-type-alist
  (implies (and (acl2::type-alistp type-alist)
                (acl2::type-alistp whole-type-alist)
                )
           (pseudo-termp (hyp-for-show-unique-memberps-from-type-alist v b bag n type-alist w whole-type-alist flg)))
  :hints (("Goal" :in-theory (enable hyp-for-show-unique-memberps-from-type-alist))))


;;
(defthm show-unique-memberps-from-type-alist-iff-hyp-for-show-unique-from-type-alist
  (iff (show-unique-memberps-from-type-alist x y bag n type-alist w whole-type-alist flg)
       (hyp-for-show-unique-memberps-from-type-alist x y bag n type-alist w whole-type-alist flg))
  :hints (("Goal" :in-theory (e/d (show-unique-memberps-from-type-alist
                                     hyp-for-show-unique-memberps-from-type-alist
                                     ) (;HYP-FOR-SHOW-UNIQUE-MEMBERPS-FROM-TYPE-ALIST-MEMBERP-CASE
                                        )))))

;drop some hints?
(defthm show-unique-memberps-from-type-alist-works-right
  (implies (and (syntax-ev (hyp-for-show-unique-memberps-from-type-alist v b bag n type-alist w whole-type-alist flg) a)
                (hyp-for-show-unique-memberps-from-type-alist v b bag n type-alist w whole-type-alist flg)
                )
           (unique-memberps (syntax-ev v a)
                            (syntax-ev b a)
                            (syntax-ev bag a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (hyp-for-show-unique-memberps-from-type-alist
                            default-car default-cdr
                            )
                           (;for efficiency:

                            DEFAULT-CAR
                            ;;LIST::EQUAL-OF-BOOLEANS-REWRITE
                            acl2::iff-reduction
                            ))))
  :rule-classes (:rewrite :forward-chaining))

(defun show-unique-memberps-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (and (consp term)
           (equal (car term) 'unique-memberps)
           (consp (cdr term))
           (consp (cddr term))
           (consp (cdddr term))
           (null  (cddddr term))
           (let* ((type-alist (acl2::mfc-type-alist mfc))
                  (len (usb16-fix (len type-alist)))
                  )
             (show-unique-memberps-from-type-alist-fn
              nil (cadr term) (caddr term) (cadddr term) len type-alist len type-alist 1)))
      ''t
    term))

(defun hyp-for-show-unique-memberps-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (and (consp term)
           (equal (car term) 'unique-memberps)
           (consp (cdr term))
           (consp (cddr term))
           (consp (cdddr term))
           (null  (cddddr term)))
      (let* ((type-alist (acl2::mfc-type-alist mfc))
             (len (usb16-fix (len type-alist)))
             )
        (bind-extra-vars-in-hyp
         (hyp-for-show-unique-memberps-from-type-alist-fn
          nil (cadr term) (caddr term) (cadddr term) len type-alist len type-alist 1) term))
    ''nil))

(defthm meta-rule-to-show-unique-memberps
  (implies (syntax-ev (hyp-for-show-unique-memberps-from-mfc term mfc state) a)
           (equal (syntax-ev term a)
                  (syntax-ev (show-unique-memberps-from-mfc term mfc state) a)))
  :otf-flg t
  :rule-classes ((:meta :trigger-fns (unique-memberps)
                        :backchain-limit-lst 0 ;just in case...
                        ))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable
                       hyp-for-show-unique-memberps-from-type-alist-irrelevant
                       ))))

;;
;;
;; Eric's rule for not equal
;;
;;

;Ways to show (not (equal x y)):
; Find (not (memberp x BLAH)) and show (memberp y BLAH), or vice-versa.
; Find (memberp x BLAH) and show (not (memberp y BLAH)), or vice-versa.
; Find (disjoint BLAH1 BLAH2) and show that a is a memberp of BLAH1 and b is a memberp of BLAH2, or vice versa.  (perhaps subset chains will intervene...)

; Find (unique BLAH) and show a and b are unique-memberps of BLAH. or that (list a) and (list b) are unique-subbagps of BLAH?? no? won't catch memberp facts?

;skip these for now?
; Find (subbagp BLAH1 BLAH2) where BLAH1 syntactically contains a, and show that b is not a memberp of BLAH2. - bzo do the memberp rules cover this case?
; Find (subbagp BLAH1 BLAH2) where BLAH1 syntactically contains b, and show that a is not a memberp of BLAH2.


;note that we actually look for something of the form (memberp b BLAH) which types to nil?

;bzo if they're constants, just call equal?  do we need to do that?  can other metafunctions call this one?
;unused?
;; (defun make-negation (term)
;;   (declare (type t term))
;;   `(if ,term 'nil 't))

;newly pulled out (doing so speed the guard conjecture for
;show-not-equal-from-type-alist-fn up by a ton (at the expense of perhaps
;slightly slower metafunction execution, but i bet that effect is minimal, and
;I'm sick of waiting for eric-meta to certify)
(defun show-not-equal-from-type-alist-member-case (a x y n entry fact type-alist whole-type-alist)
  (declare (ignore  type-alist)
           (xargs :guard (and (acl2::type-alistp whole-type-alist)
                              (acl2::type-alistp type-alist)
                              (not (endp type-alist))
                              (pseudo-termp x)
                              (pseudo-termp y)
                              (consp fact)
                              (equal entry (car type-alist))
;                              (memberp entry whole-type-alist)
                              (equal fact (car entry))
                              (acl2::unsigned-byte-p 16 n)
                              (equal n (usb16-fix (len whole-type-alist)))
                              (or (equal (car fact) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                                  (equal (car fact) 'acl2::member-equal)))
                  :guard-hints (("Goal"

                                 :do-not '(generalize eliminate-destructors)))))
  (or (and (ts-nil (cadr entry))
           (or (and (equal x (cadr fact))
                    (show-memberp-from-type-alist
                     y (caddr fact) n whole-type-alist whole-type-alist 1)
                    (equal nil (cdddr fact)))
               (and (equal y (cadr fact))
                    (show-memberp-from-type-alist
                     x (caddr fact) n whole-type-alist whole-type-alist 1)
                    (equal nil (cdddr fact)))))
      (and (ts-non-nil (cadr entry))
           (or (and (equal x (cadr fact))
                    (show-non-memberp-from-type-alist
                     y (caddr fact) n whole-type-alist whole-type-alist)
                    (equal nil (cdddr fact)))
               (and (equal y (cadr fact))
                    (show-non-memberp-from-type-alist
                     x (caddr fact) n whole-type-alist whole-type-alist)
                    (equal nil (cdddr fact)))))))

(defignored show-not-equal-from-type-alist a (x y n type-alist whole-type-alist)
  (declare (type t x y type-alist whole-type-alist)
           (type (unsigned-byte 16) n)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp x)
                              (pseudo-termp y)
                              (equal n (usb16-fix (len whole-type-alist))))
                  :guard-hints
                  (("Goal"
                    ;; jcd speed hacks that don't really help much
                    :in-theory (disable (:type-prescription show-memberp-from-type-alist-fn)
                                        (:type-prescription ts-non-nil)
                                        (:type-prescription show-non-memberp-from-type-alist-fn)
                                        (:type-prescription hyp-for-show-memberp-from-type-alist-fn)
                                        (:type-prescription ts-nil)
                                        ;(:rewrite LIST::equal-of-booleans-rewrite)
                                        (:rewrite acl2::equal-booleans-reducton)
                                        (:type-prescription booleanp)
                                        (:type-prescription ACL2::type-alistp)
                                        (:type-prescription
                                         show-unique-memberps-from-type-alist-fn)
                                        (:type-prescription pseudo-termp)
                                        show-not-equal-from-type-alist-member-case
                                        )
                    :do-not '(preprocess)))
                  :hints (("Goal" :do-not '(generalize eliminate-destructors)))))
  (if (endp type-alist)
      nil
    (let* ((entry (car type-alist))
           (fact (car entry)))
      (or (and (consp fact)
               (or (and (or (equal (car fact) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                            (equal (car fact) 'acl2::member-equal)) ;fact = (memberp ...)
                        (show-not-equal-from-type-alist-member-case a x y n entry fact type-alist whole-type-alist)
                        )
                   (and (equal 'disjoint (car fact))
                        (ts-non-nil (cadr entry))
                        (or (and (show-memberp-from-type-alist
                                  x (cadr fact) n whole-type-alist whole-type-alist 1)
                                 (show-memberp-from-type-alist
                                  y (caddr fact) n whole-type-alist whole-type-alist 1)
                                 (equal nil (cdddr fact)))
                            (and (show-memberp-from-type-alist
                                  x (caddr fact) n whole-type-alist whole-type-alist 1)
                                 (show-memberp-from-type-alist
                                  y (cadr fact) n whole-type-alist whole-type-alist 1)
                                 (equal nil (cdddr fact)))))
                   (and (equal 'unique (car fact))
                        (ts-non-nil (cadr entry))
                        (show-unique-memberps-from-type-alist
                         x y (cadr fact) n whole-type-alist n whole-type-alist 1)
                        (equal nil (cdddr fact)))))
          (show-not-equal-from-type-alist x y n (cdr type-alist) whole-type-alist)))))

(defirrelevant show-not-equal-from-type-alist 1 a (x y n type-alist whole-type-alist)
  :hints (("goal" :in-theory (enable
                              show-not-equal-from-type-alist
                              hyp-for-show-memberp-from-type-alist-irrelevant
                              hyp-for-show-non-memberp-from-type-alist-irrelevant
                              hyp-for-show-unique-memberps-from-type-alist-irrelevant
                              ))))

;pulling this stuff out into a separate function
;  one more function call would be done when member or memberp facts are found in the type-alist
;  but now the guard conjecture for hyp-for-show-not-equal-from-type-alist takes 3 seconds instead of 145.
;  also, isn't the hyp fun only called when the metafunction succeeds?
;bzo - it's kind of gross to
;pass in the ignored type-alist, but it made the guard conjecture very close
;to what it was before this stuff was pulled out into a function
(defun hyp-for-show-not-equal-from-type-alist-member-case (a x y n entry fact type-alist whole-type-alist)
  (declare (ignore  type-alist)
           (xargs :guard (and (acl2::type-alistp whole-type-alist)
                              (acl2::type-alistp type-alist)
                              (not (endp type-alist))
                              (pseudo-termp x)
                              (pseudo-termp y)
                              (consp fact)
                              (equal entry (car type-alist))
;                              (memberp entry whole-type-alist)
                              (equal fact (car entry))
                              (acl2::unsigned-byte-p 16 n)
                              (equal n (usb16-fix (len whole-type-alist)))
                              (or (equal (car fact) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                                  (equal (car fact) 'acl2::member-equal)))
                  :guard-hints (("Goal"

                                 :do-not '(generalize eliminate-destructors)))))
  (or (and (ts-nil (cadr entry))
           (equal nil (cdddr fact))
           (or (and (equal x (cadr fact))
                    (conjoin-negated-fact-and-hyp
                     fact
                     (hyp-for-show-memberp-from-type-alist y (caddr fact) n whole-type-alist whole-type-alist 1)))
               (and (equal y (cadr fact))
                    (conjoin-negated-fact-and-hyp
                     fact
                     (hyp-for-show-memberp-from-type-alist x (caddr fact) n whole-type-alist whole-type-alist 1)))))
      (and (ts-non-nil (cadr entry))
           (equal nil (cdddr fact))
           (or (and (equal x (cadr fact))
                    (conjoin-fact-and-hyp
                     fact (hyp-for-show-non-memberp-from-type-alist
                           y (caddr fact) n whole-type-alist whole-type-alist)))
               (and (equal y (cadr fact))
                    (conjoin-fact-and-hyp
                     fact (hyp-for-show-non-memberp-from-type-alist
                           x (caddr fact) n whole-type-alist whole-type-alist)))))))


(defignored hyp-for-show-not-equal-from-type-alist a (x y n type-alist whole-type-alist)
  (declare (type t x y type-alist whole-type-alist)
           (type (unsigned-byte 16) n)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp x)
                              (pseudo-termp y)
                              (equal n (usb16-fix (len whole-type-alist))))
                  :guard-hints (("Goal" :in-theory (disable hyp-for-show-not-equal-from-type-alist-member-case)
                                 :do-not '(preprocess)))
                  :hints (("Goal" :do-not '(preprocess generalize eliminate-destructors)))))
  (if (endp type-alist)
      nil
    (let* ((entry (car type-alist))
           (fact (car entry)))
      (or (and (consp fact)
               (or (and (or (equal (car fact) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                            (equal (car fact) 'acl2::member-equal))
                        ;pulled this stuff out into a function call (otherwise, the guard conjecture for this event takes forever)
                        (hyp-for-show-not-equal-from-type-alist-member-case a x y n entry fact type-alist whole-type-alist)
                        )
                   (and (equal 'disjoint (car fact))
                        (ts-non-nil (cadr entry))
                        (equal nil (cdddr fact))
                        (or (conjoin-fact-and-two-hyps
                             fact (hyp-for-show-memberp-from-type-alist
                                   x (cadr fact) n whole-type-alist whole-type-alist 1)
                             (hyp-for-show-memberp-from-type-alist
                              y (caddr fact) n whole-type-alist whole-type-alist 1)
                             )
                            (conjoin-fact-and-two-hyps
                             fact (hyp-for-show-memberp-from-type-alist
                                   x (caddr fact) n whole-type-alist whole-type-alist 1)
                             (hyp-for-show-memberp-from-type-alist
                              y (cadr fact) n whole-type-alist whole-type-alist 1))))
                   (and (equal 'unique (car fact))
                        (ts-non-nil (cadr entry))
                        (equal nil (cdddr fact))
                        (conjoin-fact-and-hyp
                         fact (hyp-for-show-unique-memberps-from-type-alist
                               x y (cadr fact) n whole-type-alist n whole-type-alist 1))
                        )))
          (hyp-for-show-not-equal-from-type-alist x y n (cdr type-alist) whole-type-alist)))))

(defirrelevant hyp-for-show-not-equal-from-type-alist 1 a (x y n type-alist whole-type-alist)
  :hints (("goal" :in-theory (enable
                              hyp-for-show-not-equal-from-type-alist
                              hyp-for-show-memberp-from-type-alist-irrelevant
                              hyp-for-show-non-memberp-from-type-alist-irrelevant
                              hyp-for-show-unique-memberps-from-type-alist-irrelevant
                              ))))


(defthm show-not-equal-from-type-alist-iff-hyp-for-show-not-equal-from-type-alist
  (iff (show-not-equal-from-type-alist x y n type-alist whole-type-alist)
       (hyp-for-show-not-equal-from-type-alist x y n type-alist whole-type-alist))
  :hints (("Goal" :in-theory (enable show-not-equal-from-type-alist
                                     hyp-for-show-not-equal-from-type-alist
                                     ))))

(defthm show-not-equal-from-type-alist-works-right
  (implies (and (syntax-ev (hyp-for-show-not-equal-from-type-alist x y n type-alist whole-type-alist) a)
                (hyp-for-show-not-equal-from-type-alist x y n type-alist whole-type-alist)
                )
           (not (equal (syntax-ev x a)
                       (syntax-ev y a))))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d ( not-equal-when-unique-and-unique-memberps
                             hyp-for-show-not-equal-from-type-alist
                             not-equal-from-member-of-disjoint-facts
                             not-equal-from-member-of-disjoint-facts-alt
                             )
                           ()))))

(defthm pseudo-termp-of-hyp-for-show-not-equal-from-type-alist
  (implies (and (acl2::type-alistp type-alist)
                (acl2::type-alistp whole-type-alist)
                )
           (pseudo-termp (hyp-for-show-not-equal-from-type-alist x y n type-alist whole-type-alist)))
  :hints (("Goal" :in-theory (enable HYP-FOR-SHOW-NOT-EQUAL-FROM-TYPE-ALIST))))

(defun show-not-equal-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (and (consp term) ;should always succeed
           (equal (car term) 'equal) ;should always succeed
           (let* ((type-alist (acl2::mfc-type-alist mfc))
                  (len (usb16-fix (len type-alist)))
                  )
             (show-not-equal-from-type-alist-fn nil (cadr term) (caddr term) len type-alist type-alist))
           (equal (cdddr term) nil))
      ''nil
    term))

(defun hyp-for-show-not-equal-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (and (consp term)
           (equal (car term) 'equal)
           (equal (cdddr term) nil))
      (let* ((type-alist (acl2::mfc-type-alist mfc))
             (len (usb16-fix (len type-alist)))
             )
        (bind-extra-vars-in-hyp (hyp-for-show-not-equal-from-type-alist-fn nil (cadr term) (caddr term) len type-alist type-alist) term))
    ''nil))


;This rule is hung on equal; is it expensive?  I've tried to write my
;metafunctions efficiently.  If this rule proves too expensive, we
;could introduce a new function, neq, for inequality.  But that seems
;unfortunate...

(defthm meta-rule-to-show-not-equal
  (implies (syntax-ev (hyp-for-show-not-equal-from-mfc term mfc state) a)
           (equal (syntax-ev term a)
                  (syntax-ev (show-not-equal-from-mfc term mfc state) a)))
  :otf-flg t
  :rule-classes ((:meta :trigger-fns (equal)
                        :backchain-limit-lst 0 ;just in case...
                        ))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable
                       hyp-for-show-not-equal-from-type-alist-irrelevant
                       ))))

;wrapping this around the equal calls I want to rewrite keeps acl2
;from using substitution, etc. to prove the goal, thus making for a
;better test of my :meta rules.

(local (defstub foo-eric (x) t))


(encapsulate
 ()
 (local (defthm neq-test-1
          (implies (not (memberp a (list b c d e f)))
                   (equal (foo-eric (equal a d))
                          (foo-eric nil)))
          :rule-classes nil
          :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-not-equal)
                                                     (theory 'minimal-theory)))))))

(encapsulate
 ()
 (local (defthm neq-test-2
          (implies (not (memberp a (cons b (cons c (append (cons d (cons e nil)) f)))))
                   (equal (foo-eric (equal a d))
                          (foo-eric nil)))
          :rule-classes nil
          :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-not-equal)
                                                     (theory 'minimal-theory)))))))

(encapsulate
 ()
 (local (defthm neq-test-2-alt
          (implies (not (memberp a (cons b (cons c (append f (cons d (cons e nil)))))))
                   (equal (foo-eric (equal a d))
                          (foo-eric nil)))
          :rule-classes nil
          :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-not-equal)
                                                     (theory 'minimal-theory)))))))

(encapsulate
 ()
 (local (defthm neq-test-2-alt-back
          (implies (not (memberp a (cons b (cons c (append f (cons d (cons e nil)))))))
                   (equal (foo-eric (equal d a))
                          (foo-eric nil)))
          :rule-classes nil
          :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-not-equal)
                                                     (theory 'minimal-theory)))))))

(encapsulate
 ()
 (local (defthm neq-test-greve
          (implies
           (and (memberp a x)
                (not (memberp b x)))
           (equal (foo-eric (equal a b))
                  (foo-eric nil)))
          :rule-classes nil
          :hints (("Goal" :in-theory (union-theories '(meta-rule-to-show-not-equal)
                                                     (theory 'minimal-theory)))))))

;bzo add more tests!



;;  Bbzo this is incomplete

;; ;bzo new stuff. remove skip--proofs.  replace unique-subbagps?

;; ;this all is written in an out-of-date style;compare it to the other stuff in this file

;; (defund show-subbagp2-from-type-alist (x y n type-alist whole-type-alist
;;                                          perform-syntax-test)
;;   (declare (type t x y type-alist whole-type-alist)
;;            (type (unsigned-byte 16) n)
;;            (type bit perform-syntax-test)
;;            (xargs :measure `((1 . ,(+ 1 (nfix n))) . ,(len type-alist))
;;                   :hints (("Goal" :do-not '(generalize eliminate-destructors)))))
;;   (if (and (equal 1 perform-syntax-test)
;;            (syntax-subbagp x y) ;we can tell just by looking at x and y that x is a subbagp of y
;;            )
;;       t
;;     (if (zp n) ;prevents loops and is okay because, given a type-alist with n things in it, we'll never need to use more than n facts to make a subbagp chain ; bzo should n be the len of the clause of type-alist?
;;         nil
;;       (if (consp type-alist)
;;           (let ((entry (car type-alist)))
;;             (if (consp entry)
;;                 (let ((fact (car entry)))
;;                   (or (and (consp fact)
;;                            (equal (car fact) 'subbagp)
;; ;                           (consp (cdr entry))
;;                            (ts-non-nil (cadr entry)) ;check that the type is either t or non-nil
;;  ;                          (consp (cdr fact))
;;   ;                         (consp (cddr fact))

;;                            (syntax-subbagp (cadr fact) x)
;;                            (syntax-subbagp (caddr fact) y)

;;                            (met ((hit smaller-cadr smaller-x) (syntax-remove-bag (cadr fact) x))
;;                                 (declare (ignore hit smaller-cadr))
;;                                 (met ((hit2 smaller-caddr smaller-y) (syntax-remove-bag (caddr fact) y))
;;                                      (declare (ignore hit2 smaller-caddr))
;;                                      (show-subbagp2-from-type-alist smaller-x
;;                                                                     smaller-y
;;                                                                     (+ -1 n) whole-type-alist whole-type-alist
;;                                                                     1)))
;;                                         ;we've found success; now we just need to check the arities of some stuff:
;;                            (equal nil (cdddr fact))
;;                            )
;;                       (show-subbagp2-from-type-alist x y n (cdr type-alist) whole-type-alist
;;                                                     0)))
;;               (show-subbagp2-from-type-alist x y n (cdr type-alist) whole-type-alist
;;                                             0)))
;;         nil))))

;;   bzo fix up make conjunction, etc.
;; (defund hyp-for-show-subbagp2-from-type-alist (x y n type-alist whole-type-alist
;;                                                  perform-syntax-test)
;;   (declare (type t x y type-alist whole-type-alist)
;;            (type (unsigned-byte 16) n)
;;            (type bit perform-syntax-test)
;;            (xargs :measure `((1 . ,(+ 1 (nfix n))) . ,(len type-alist))
;;                   :hints (("Goal" :do-not '(generalize eliminate-destructors)))))
;;   (if (and (equal 1 perform-syntax-test)
;;            (syntax-subbagp x y) ;we can tell just by looking at x and y that x is a subbagp of y
;;            )
;;       ''t
;;     (if (zp n) ;prevents loops and is okay because, given a type-alist with n things in it, we'll never need to use more than n facts to make a subbagp chain ; bzo should n be the len of the clause of type-alist?
;;         nil
;;       (if (consp type-alist)
;;           (let ((entry (car type-alist)))
;;             (if (consp entry)
;;                 (let ((fact (car entry)))
;;                   (or (and (consp fact)
;;                            (equal (car fact) 'subbagp)
;;    ;                        (consp (cdr entry))
;;                            (ts-non-nil (cadr entry)) ;check that the type is either t or non-nil
;;     ;                       (consp (cdr fact))
;;      ;                      (consp (cddr fact))

;;                            (syntax-subbagp (cadr fact) x)
;;                            (syntax-subbagp (caddr fact) y)

;;                            (met ((hit smaller-cadr smaller-x) (syntax-remove-bag (cadr fact) x))
;;                                 (declare (ignore hit smaller-cadr))
;;                                 (met ((hit2 smaller-caddr smaller-y) (syntax-remove-bag (caddr fact) y))
;;                                      (declare (ignore hit2 smaller-caddr))
;;                                      (let ((hyp (hyp-for-show-subbagp2-from-type-alist
;;                                                  smaller-x
;;                                                  smaller-y
;;                                                  (+ -1 n) whole-type-alist whole-type-alist
;;                                                  1)))
;;                                        (if (and hyp
;;                                                 (equal nil (cdddr fact)))
;;                                            (make-conjunction fact hyp)
;;                                          nil))))

;;                            )
;;                       (hyp-for-show-subbagp2-from-type-alist x y n (cdr type-alist) whole-type-alist
;;                                                              0)))
;;               (hyp-for-show-subbagp2-from-type-alist x y n (cdr type-alist) whole-type-alist
;;                                                      0)))
;;         nil))))


;; (defthm show-subbagp2-from-type-alist-iff-hyp-for-show-subbagp2-from-type-alist
;;   (iff (show-subbagp2-from-type-alist x y n type-alist whole-type-alist flg)
;;        (hyp-for-show-subbagp2-from-type-alist x y n type-alist whole-type-alist flg))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable show-subbagp2-from-type-alist
;; ;                                     MAKE-CONJUNCTION
;;                                      hyp-for-show-subbagp2-from-type-alist
;;                                      ))))



;; (defevaluator syntax-ev2 syntax-ev2-list
;;   (
;; ;   (hide-claim x)
;;    (type-reasoning-only x)
;;    (hide x)
;;    (hide-unique list)
;;    (hide-subbagp x y) ;added by eric
;;    (hide-disjoint x y) ;added by eric
;;    (hide-memberp a x) ;added by eric
;;    (perm x y)
;;    (unique list)
;; ;   (implies-if a term)
;;    (if a b c)
;;    (consp x)
;;    (true-listp x)
;;    (binary-append x y)
;;    (cons a b)
;;    (meta-subbagp list1 list2)
;;    (remove-bag x list)
;;    (meta-remove-bag x list)
;;    (remove-1 x list)
;; ;   (meta-remove-1 x list)
;;    (unique-subbagps x y list)
;;    (subbagp-pair x1 x2 list1 list2)
;;    (meta-memberp x list)
;;    (any-subbagp x list) ;remove this?
;;    (finalcdr x)
;;    (list::fix x)
;;    (subbagp x y) ;added by eric
;;    (memberp a x) ;added by eric
;;    (disjoint x y) ;added by eric
;; ;   (synp vars form term) ;added by eric
;;    (val n x) ;bzo we didn't need this! go back to syntax-ev

;;    ))


;; ;; ;hmmm. what lemma do we want here?
;; ;; (thm
;; ;;  (implies (and (SYNTAX-SUBBAGP x y)
;; ;;                (SYNTAX-EV2 (VAL 2
;; ;;                                       (SYNTAX-REMOVE-BAG (CADAAR TYPE-ALIST)
;; ;;                                                          X))
;; ;;                            A)

;; ;; (defthm syntax-remove-bag-1-yields-a-subbagp
;; ;;   (subbagp (syntax-ev2 (val 1 (syntax-remove-bag-1 x y))
;; ;;                        a)
;; ;;            (syntax-ev2 y a))
;; ;;   :hints (("Goal" :in-theory (enable syntax-remove-bag-1))))

;; ;; (defthm syntax-remove-1-yields-a-subbagp
;; ;;   (subbagp (SYNTAX-EV2 (VAL 1 (SYNTAX-REMOVE-1 b Y)) A)
;; ;;            (syntax-ev2 y a))
;; ;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;; ;;            :in-theory (enable syntax-remove-1))))

;; ;; (defthm syntax-remove-bag-yields-a-subbagp
;; ;;   (subbagp (syntax-ev2 (val 2 (syntax-remove-bag x y)) a)
;; ;;            (syntax-ev2 y a))
;; ;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;; ;;            :in-theory (enable syntax-remove-bag syntax-remove-bag-1))))

;; ;; z z

;; ;; (thm
;; ;;  (implies (and (subbagp (syntax-ev2 (val 2 (syntax-remove-bag small x)) a)
;; ;;                         (syntax-ev2 (val 2 (syntax-remove-bag big y)) a))
;; ;;                (subbagp (syntax-ev2 small a)
;; ;;                         (syntax-ev2 big a)))
;; ;;           (subbagp (syntax-ev2 x a)
;; ;;                    (syntax-ev2 y a)))
;; ;;  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;; ;;           :in-theory (enable syntax-remove-bag syntax-remove-bag-1))))


;; ;; (defthm show-subbagp2-from-type-alist-works-right
;; ;;   (implies
;; ;;    (and (syntax-ev2 (hyp-for-show-subbagp2-from-type-alist x y n type-alist whole-type-alist flg) a)
;; ;;         (hyp-for-show-subbagp2-from-type-alist x y n type-alist whole-type-alist flg)
;; ;;         )
;; ;;    (subbagp (syntax-ev2 x a)
;; ;;             (syntax-ev2 y a)))
;; ;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;; ;;            :in-theory (e/d (hyp-for-show-subbagp2-from-type-alist
;; ;;                             )
;; ;;                            ()))
;; ;; ))



;; (set-state-ok t)

;; (defun hyp-for-show-subbagp2-from-mfc (term mfc state)
;;   (declare (ignore state)
;;            (type t term mfc state)
;;            (xargs :guard (pseudo-termp term)))

;;   (if (and (consp term)
;;            (equal (car term) 'subbagp)
;;            (consp (cdr term))
;;            (consp (cddr term)))
;;       (let* ((type-alist (acl2::mfc-type-alist mfc))
;;              (len (usb16-fix (len type-alist)))
;;              )
;;         (bind-extra-vars-in-hyp (hyp-for-show-subbagp2-from-type-alist (cadr term) (caddr term) len type-alist type-alist 1) term))
;;     ''nil))


;; ;We could count the number of subbagp facts and use that count instead of (len clause).  This might be a good idea if we think cycles might exist among our subbagp facts.
;; ;We don't let LEN be more than 65535, so that it can be a fix-num in show-subbagp2-from-clause.
;; ;I can't imagine needing to make a chain of more than 65535 subbagp facts!
;; ;bzo what if we're rewriting a subbagp claim that's not the atom of a top-level literal?  then we're okay because or rules won't use that fact?
;; ;it would be nice to know that mfc-ts returns a valid type.
;; (defun show-subbagp2-from-mfc (term mfc state)
;;   (declare (ignore state)
;;            (xargs :guard (pseudo-termp term))
;;            (type t term mfc state))
;;   (if (and (consp term)  ;well-formedness checks, should always succeed
;; ;           (consp (cdr term))
;;  ;          (consp (cddr term))
;;            )
;;       (let* ((type-alist (acl2::mfc-type-alist mfc))
;;              (len (usb16-fix (len type-alist)))
;;              )
;;         (if (and (show-subbagp2-from-type-alist (cadr term) (caddr term) len type-alist type-alist 1)
;;                  (equal (car term) 'subbagp) ;well-formedness check, should always succeed)
;;                  )
;;             term ;''t Bbzo put this back
;;           term))
;;     term))




;; ;I never got around to proving this
;; ;add the SYNP treatment to this!  see the other rules in this file
;; (defthm meta-rule-to-show-subbagp2
;;    (implies (syntax-ev (hyp-for-show-subbagp2-from-mfc term mfc state) alist)
;;             (equal (syntax-ev term alist)
;;                    (syntax-ev (show-subbagp2-from-mfc term mfc state) alist)))
;;    :otf-flg t
;;    :rule-classes ((:meta :trigger-fns (subbagp)
;;                          :backchain-limit-lst 0 ;just in case...
;;                          ))
;;    :hints (("Goal" :do-not-induct t
;;             :in-theory (enable TYPE-REASONING-ONLY)
;;             :expand ((:free (x) (hide x)))
;;             :do-not '(generalize eliminate-destructors))))





;; (thm
;;  (implies (and (subbagp (list a) z)
;;                (subbagp (list b) y))
;;           (subbagp (list a b) (append z y)))
;;  :hints (("Goal" :in-theory '( meta-rule-to-show-subbagp2))))

;; (thm
;;  (implies (and (subbagp (list a e d) z)
;;                (subbagp (list b ff) y))
;;           (subbagp (list a b e d ff) (append z y)))
;;  :hints (("Goal" :in-theory '( meta-rule-to-show-subbagp2))))




;; ;If hyp is non-nil and check is also non-nil, then make a conjunction of fact and hyp.
;; (defun conjoin-fact-to-hyp-given-check (fact hyp check)
;;   (if (and hyp check)
;;       (make-conjunction fact hyp)))

;; ;check is entirely pro-forma, so don't perform it unless hyp is non-nil
;; (defmacro conjoin-fact-to-hyp-given-check (fact hyp check)
;;   `(let ((hyp ,hyp))
;;      (if (and hyp ,check)
;;          (make-conjunction ,fact hyp))))

;; ;; (thm
;; ;;    (NOT (SYNTAX-SUBBAGP X NIL))
;; ;;    :hints (("Goal" :in-theory (enable SYNTAX-SUBBAGP SYNTAX-SUBBAGP-HELPER))))
