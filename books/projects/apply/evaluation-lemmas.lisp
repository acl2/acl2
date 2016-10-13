; Copyright (C) 2016, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Portcullis:
; (include-book "evaluation-user-book")

; Lemmas Needed to Prove that the Warrants of User-Book are Valid

; The book basically just proves, for every function fn that has a doppelganger
; fn!, that fn!=fn, in the evaluation theory of
; (defattach badge-userfn badge-userfn!)
; (defattach apply$-userfn apply$-userfn!)
; after defining all the doppelgangers of user-book.lisp.

; That evaluation theory is realized as a current theory by
; (defun badge-userfn (fn) (badge-userfn! fn))
; (defun apply$-userfn (fn args) (apply$-userfn! fn args))
; and then re-certifying apply.lisp and user-book.lisp.  That's
; how evaluation-user-book.lisp, in the portcullis above, was built.

(in-package "ACL2")

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

; The following represents a lemma we may need to prove that
; recur-by-collect is equal to its doppleganger.

(defthm len-collect
  (equal (len (collect lst fn))
         (len lst))
  :hints
  (("Goal" :in-theory (disable collect-is-a-foldr))))

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
  :hints
  (("Goal"
    :in-theory (enable badge apply$ ev$ apply$-lambda)
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

; =================================================================
; 13. prove that the dopplegangers of the ordinary functions and tame
;     instances are equal to their correspondents.

(defthm ap!-is-ap
  (equal (ap! x y)
         (ap x y)))

(defthm rev!-is-rev
  (equal (rev! x)
         (rev x)))

(defthm palindromify-list!-is-palindromify-list
  (equal (palindromify-list! lst)
         (palindromify-list lst)))

(defthm list-of-true-listsp!-is-list-of-true-listsp
  (equal (list-of-true-listsp! lst)
         (list-of-true-listsp lst)))

(defthm list-of-list-of-true-listsp!-is-list-of-list-of-true-listsp
  (equal (list-of-list-of-true-listsp! lst)
         (list-of-list-of-true-listsp lst)))

(defthm expt-2-and-expt-3!-is-expt-2-and-expt-3
  (equal (expt-2-and-expt-3! x)
         (expt-2-and-expt-3 x)))

(defthm expt-5!-is-expt-5
  (equal (expt-5! x)
         (expt-5 x)))

(defthm ok-fnp!-is-ok-fnp
  (equal (ok-fnp! lst)
         (ok-fnp lst)))

(defthm collect-rev!-is-collect-rev
  (equal (collect-rev! x)
         (collect-rev x))
  :hints (("Goal" :in-theory (e/d (APPLY$) (APPLY$-REV)))))

(defthm sum-of-products!-is-sum-of-products
  (equal (sum-of-products! x)
         (sum-of-products x))
  :hints (("Goal" :in-theory (e/d (APPLY$) (APPLY$-REV)))))

; =================================================================
; The End


