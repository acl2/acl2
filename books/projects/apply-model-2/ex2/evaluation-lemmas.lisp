; Copyright (C) 2019, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Lemmas Needed to Prove that the Warrants of user-defs.lisp are Valid

; The book basically just proves, for every function fn that has a doppelganger
; fn!, that fn!=fn, in the evaluation theory of
; (defattach badge-userfn badge-userfn!)
; (defattach apply$-userfn apply$-userfn!).
; (defattach untame-apply$ untame-apply$!)

; That evaluation theory is realized as a current theory by ``re-certifying''
; ../apply.lisp and user-defs.lisp with the portculis defined in
; evaluation-apply.acl2, which contains:

; (defun modapp::badge-userfn (fn)
;   (declare (xargs :guard t))
;   (modapp::badge-userfn! fn))

; (defun modapp::apply$-userfn (fn args)
;   (declare (xargs :guard (true-listp args)))
;   (modapp::apply$-userfn! fn args))

; (defun modapp::untame-apply$ (fn args)
;   (declare (xargs :guard (true-listp args)))
;   (modapp::untame-apply$! fn args))

; To certify ../apply.lisp and user-defs.lisp with a different portculis we
; first copy them ex1/evaluation-apply.lisp and evaluation-user-defs.lisp.

(in-package "MODAPP")

(include-book "evaluation-user-defs")

(include-book "tools/flag" :dir :system)

(defthm badge-is-badge!
  (equal (badge fn) (badge! fn))
  :hints (("Goal" :in-theory (enable badge badge!))))

(make-flag boom tamep)
(defthm-boom
  (defthm tamep-is-tamep!
    (equal (tamep x) (tamep! x))
    :flag tamep)
  (defthm tamep-functionp-is-tamep-functionp!
    (equal (tamep-functionp fn) (tamep-functionp! fn))
    :flag tamep-functionp)
  (defthm suitably-tamep-listp-is-suitably-tamep-listp!
    (equal (suitably-tamep-listp n flags args) (suitably-tamep-listp! n flags args))
    :flag suitably-tamep-listp))

(make-flag bang apply$!
           :hints (("Goal" :in-theory (enable badge apply$))))

; Prove that the doppelgangers of all Group 1 functions are equal to their counterparts.

(defthm ok-fnp!-is-ok-fnp
  (equal (ok-fnp! lst)
         (ok-fnp lst)))

; Do I need these?
(defthm len-collect
  (equal (len (collect lst fn))
         (len lst)))

(defthm len-prow
  (implies (not (endp (cdr lst)))
           (< (len (prow lst fn))(len lst)))
  :rule-classes :linear)

(defthm-bang
  (defthm apply$!-is-apply$
    (equal (apply$! fn args) (apply$ fn args))
    :flag apply$!)

; BTW: The proofs of these theorems illustrate why we need the tamep in ev$ (a
; question we were once uncertain about).  When evaluating a call of a
; user-defined mapper, ev$! just cadrs the functional arg but ev$ evaluates it.
; But that means that apply$!  is apply$ on lambda applications only if the
; body is tame!

  (defthm ev$!-is-ev$
    (equal (ev$! x a) (ev$ x a))
    :flag ev$!)
  (defthm ev$!-list-is-ev$-list
    (equal (ev$!-list x a) (ev$-list x a))
    :flag ev$!-list)
  (defthm collect!-is-collect
    (equal (collect! lst fn)
           (collect lst fn))
    :flag collect!)
  (defthm sumlist!-is-sumlist
    (equal (sumlist! lst fn)
           (sumlist lst fn))
    :flag sumlist!)
  (defthm sumlist-with-params!-is-sumlist
    (equal (sumlist-with-params! lst fn params)
           (sumlist-with-params lst fn params))
    :flag sumlist-with-params!)
  (defthm filter!-is-filter
    (equal (filter! lst fn)
           (filter lst fn))
    :flag filter!)
  (defthm all!-is-all
    (equal (all! lst fn)
           (all lst fn))
    :flag all!)
  (defthm xists!-is-xists
    (equal (xists! lst fn)
           (xists lst fn))
    :flag xists!)
  (defthm maxlist!-is-maxlist
    (equal (maxlist! lst fn)
           (maxlist lst fn))
    :flag maxlist!)
  (defthm collect-on!-is-collect-on
    (equal (collect-on! lst fn)
           (collect-on lst fn))
    :flag collect-on!)
  (defthm collect-tips!-is-collect-tips
    (equal (collect-tips! x fn)
           (collect-tips x fn))
    :flag collect-tips!)
  (defthm apply$2!-is-apply$2
    (equal (apply$2! fn x y)
           (apply$2 fn x y))
    :flag apply$2!)
  (defthm apply$2x!-is-apply$2x
    (equal (apply$2x! fn x y)
           (apply$2x fn x y))
    :flag apply$2x!)
  (defthm apply$2xx!-is-apply$2xx
    (equal (apply$2xx! fn x y)
           (apply$2xx fn x y))
    :flag apply$2xx!)
  (defthm russell!-is-russell
    (equal (russell! fn x)
           (russell fn x))
    :flag russell!)
  (defthm foldr!-is-foldr
    (equal (foldr! lst fn init)
           (foldr lst fn init))
    :flag foldr!)
  (defthm foldl!-is-foldl
    (equal (foldl! lst fn ans)
           (foldl lst fn ans))
    :flag foldl!)
  (defthm collect-from-to!-is-collect-from-to
    (equal (collect-from-to! i max fn)
           (collect-from-to i max fn))
    :flag collect-from-to!)
  (defthm collect*!-is-collect
    (equal (collect*! lst fn)
           (collect* lst fn))
    :flag collect*!)
  (defthm collect2!-is-collect
    (equal (collect2! lst fn1 fn2)
           (collect2 lst fn1 fn2))
    :flag collect2!)
  (defthm recur-by-collect!-is-recur-by-collect
    (equal (recur-by-collect! lst fn)
           (recur-by-collect lst fn))
    :flag recur-by-collect!)
  (defthm prow!-is-prow
    (equal (prow! lst fn)
           (prow lst fn))
    :flag prow!)
  (defthm prow*!-is-prow*
    (equal (prow*! lst fn)
           (prow* lst fn))
    :flag prow*!)
  (defthm fn-2-and-fn-3!-is-fn-2-and-fn-3
    (equal (fn-2-and-fn-3! fn x)
           (fn-2-and-fn-3 fn x))
    :flag fn-2-and-fn-3!)
  (defthm fn-5!-is-fn-5
    (equal (fn-5! fn x)
           (fn-5 fn x))
    :flag fn-5!)
  (defthm map-fn-5!-is-fn-5
    (equal (map-fn-5! lst fn)
           (map-fn-5 lst fn))
    :flag map-fn-5!)
  (defthm sumlist-expr!-is-sumlist-expr
    (equal (sumlist-expr! lst expr alist)
           (sumlist-expr lst expr alist))
    :flag sumlist-expr!)
  (defthm twofer!-is-twofer
    (equal (twofer! lst fn xpr alist)
           (twofer lst fn xpr alist))
    :flag twofer!)
  (defthm collect-a!-is-collect-a
    (equal (collect-a! lst fn)
           (collect-a lst fn))
    :flag collect-a!)
  (defthm collect-b!-is-collect-b
    (equal (collect-b! lst fn)
           (collect-b lst fn))
    :flag collect-b!)
  (defthm collect-c!-is-collect-c
    (equal (collect-c! lst fn1 fn2)
           (collect-c lst fn1 fn2))
    :flag collect-c!)
  (defthm collect-d!-is-collect-d
    (equal (collect-d! lst fn1 fn2)
           (collect-d lst fn1 fn2))
    :flag collect-d!)
  (defthm collect-e!-is-collect-e
    (equal (collect-e! lst fn)
           (collect-e lst fn))
    :flag collect-e!)
  (defthm my-apply-2!-is-my-apply-2
    (equal (my-apply-2! fn1 fn2 x)
           (my-apply-2 fn1 fn2 x))
    :flag my-apply-2!)
  (defthm my-apply-2-1!-is-my-apply-2-1
    (equal (my-apply-2-1! fn x)
           (my-apply-2-1 fn x))
    :flag my-apply-2-1!)
  (defthm collect-my-rev!-is-collect-my-rev
    (equal (collect-my-rev! lst)
           (collect-my-rev lst))
    :flag collect-my-rev!)
  (defthm my-append2!-is-my-append2
    (equal (my-append2! x y)
           (my-append2 x y))
    :flag my-append2!)
  (defthm sqnats!-is-sqnats
    (equal (sqnats! x)
           (sqnats x))
    :flag sqnats!)
  (defthm sum-of-products!-is-sum-of-products
    (equal (sum-of-products! lst)
           (sum-of-products lst))
    :flag sum-of-products!)
  (defthm collect-composition!-is-collect-composition
    (equal (collect-composition! lst fn gn)
           (collect-composition lst fn gn))
    :flag collect-composition!)
  (defthm collect-x1000!-is-collect-x1000
    (equal (collect-x1000! lst fn)
           (collect-x1000 lst fn))
    :flag collect-x1000!)
  (defthm collect-x1000-caller!-is-collect-x1000-caller
    (equal (collect-x1000-caller! lst fn)
           (collect-x1000-caller lst fn))
    :flag collect-x1000-caller!)
  (defthm guarded-collect!-is-guarded-collect
    (equal (guarded-collect! lst fn)
           (guarded-collect lst fn))
    :flag guarded-collect!)
  (defthm ack$!-is-ack$
        (equal (ack$! fn k n m)
               (ack$  fn k n m))
    :flag ack$!)
  (defthm silly$!-is-silly$
        (equal (silly$! fn k n m)
               (silly$  fn k n m))
    :flag silly$!)

; Given that apply$-userfn is DEFINED to be apply$-userfn!, their equality is
; trivial and doesn't belong in this conjunction.  But since apply$-userfn1 is
; one of the fns in the clique, we need a theorem with this :flag.  Note the
; :rule-classes; as a rewrite rule this loops.

  (defthm apply$-userfn1!-is-apply$-userfn
    (equal (apply$-userfn1! fn args)
           (apply$-userfn fn args))
    :rule-classes nil
    :flag apply$-userfn1!)

  :hints
  (("Goal"
    :in-theory (e/d (badge apply$ ev$ apply$-lambda)
                    ((:executable-counterpart force)))
    :expand (
             (ev$! x a)
             (ev$ x a)
             (:free (n ilk ilks x) (suitably-tamep-listp! n (cons ilk ilks) x))
             (COLLECT-FROM-TO! I MAX FN)
             (COLLECT-FROM-TO I MAX FN)
             ))
   ))

(defthm apply$-lambda!-is-apply$-lambda
  (equal (apply$-lambda! fn args) (apply$-lambda fn args)))

