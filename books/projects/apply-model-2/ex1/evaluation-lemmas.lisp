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
  (defthm sumlist!-is-sumlist
    (equal (sumlist! lst fn)
           (sumlist lst fn))
    :flag sumlist!)
  (defthm foldr!-is-foldr
    (equal (foldr! lst fn init)
           (foldr lst fn init))
    :flag foldr!)
  (defthm prow!-is-prow
    (equal (prow! lst fn)
           (prow lst fn))
    :flag prow!)
  (defthm prow*!-is-prow*
    (equal (prow*! lst fn)
           (prow* lst fn))
    :flag prow*!)
  (defthm collect-a!-is-collect-a
    (equal (collect-a! lst fn)
           (collect-a lst fn))
    :flag collect-a!)
  (defthm sum-of-products!-is-sum-of-products
    (equal (sum-of-products! lst)
           (sum-of-products lst))
    :flag sum-of-products!)
  (defthm ack$!-is-ack$
        (equal (ack$! fn k n m)
               (ack$  fn k n m))
    :flag ack$!)
  (defthm silly$!-is-silly$
        (equal (silly$! fn k n m)
               (silly$  fn k n m))
    :flag silly$!)


; Given that apply$-userfn is DEFINED to be apply$-userfn! in the portcullis of
; this book, their equality is trivial and doesn't belong in this conjunction.
; But since apply$-userfn1 is one of the fns in the clique, we need a theorem
; with this :flag.  Note the :rule-classes; as a rewrite rule this loops.

  (defthm apply$-userfn1!-is-apply$-userfn
    (equal (apply$-userfn1! fn args)
           (apply$-userfn fn args))
    :rule-classes nil
    :flag apply$-userfn1!)

  :hints
  (("Goal"
    :in-theory (e/d (badge apply$ ev$ apply$-lambda o<)
                    ((:executable-counterpart force)))
    :expand (
             (ev$! x a)
             (ev$ x a)
             (:free (n ilk ilks x) (suitably-tamep-listp! n (cons ilk ilks) x))
             ))
   ))

(defthm apply$-lambda!-is-apply$-lambda
  (equal (apply$-lambda! fn args) (apply$-lambda fn args)))

