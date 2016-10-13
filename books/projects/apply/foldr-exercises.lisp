; Copyright (C) 2016, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Portcullis:
; (include-book "apply")

; FOLDR Exercises

; Summary

; In this book we define the classic function FOLDR and prove that various
; familiar functions and ideas can be expressed with it.  In particular, we
; show how FOLDR can ``be'' APPEND, REV, COLLECT, ALLWAYS, SUMLIST, FILTER, and
; (sort of) MAXLIST.

; Some implications of this work are:

; (1) We might consider providing FOLDR as a primitive and then not allowing
; the user to define any mappers (i.e., prevent the user from using APPLY$ etc
; in defuns) and just rely on FOLDR to provide a lot of power and convenience.
; This would simplify the soundness story considerably because then we would
; not have to contemplate finding a measure (in the model construction as
; illustrated by modeled-portculis.lisp) for arbitrary mapping functions.  We'd
; support just APPLY$, EV$, EV$-LIST, and FOLDR.  Instead, we find a measure to
; explain APPLY$, EV$, EV$-LIST, and FOLDR and that measure and clique is fixed
; for all instances of the story.  (Personally, Moore isn't persuaded that we
; want to prohibit the definition of other mappers.)

; (2) However, maybe there is a way to use FOLDR to create a simpler soundness
; story while still allowing the user to define COLLECT, etc.  For example, in
; the soundness story we could keep the concrete clique fixed as in (2) and
; model COLLECT and the all the other user-defined mappers as calls of FOLDR,
; which removes them from the clique and allows us to skip the creation of the
; messy measure.  Of course, to rely on this version of the story we'd want to
; check that every user-defined mapper was really some instance of FOLDR, a not
; unreasonable restriction.

; (3) At one point below (see maxlist-non-nil and maxlist-is-sort-of-a-foldr)
; we have to express the idea that fn returns an integer on every element of a
; given list and we do this with ALLWAYS and COLLECT.  It is very natural in
; the sense that it was easy to write, the normal machinery handled its
; participation in the proofs, and it avoids the definition of yet another
; special-purpose recursive function.  Thus, these exercises can be thought of
; as a little supporting evidence for the utility of apply and mapping
; functions.

; (ld "~/work/apply/book1/consistency/foldr-exercises.lisp")
; (certify-book "foldr-exercises")

(in-package "ACL2")

; (include-book "apply")

(defun$ foldr (lst fn init)
  (if (endp lst)
      init
      (apply$ fn
              (list (car lst)
                    (foldr (cdr lst) fn init)))))
(defun$ ap (x y)
  (if (consp x)
      (cons (car x) (ap (cdr x) y))
      y))

(defun$ rev (x)
  (if (consp x)
      (ap (rev (cdr x)) (cons (car x) nil))
      nil))

(defthm foldr-is-ap
  (equal (foldr x 'cons y) (ap x y)))

(defthm foldr-is-rev
  (implies (apply$-warrant-foldr)
           (equal (foldr x
                         '(lambda (x y)
                                  (foldr y 'cons (cons x 'nil)))
                         nil)
                  (rev x))))

; Now I define various mappers and show that foldr can be made to
; do all those jobs.

(defun$ collect (lst fn)
  (cond ((endp lst) nil)
        (t (cons (apply$ fn (list (car lst)))
                 (collect (cdr lst) fn)))))

(defun$ allways (lst fn)
  (cond ((endp lst) t)
        (t (and (apply$ fn (list (car lst)))
                (allways (cdr lst) fn)))))

(defun$ sumlist (lst fn)
  (cond ((endp lst) 0)
        (t (+ (apply$ fn (list (car lst)))
              (sumlist (cdr lst) fn)))))

(defun$ max$ (x y)

; I have to define max$ rather than use the built-in MAX because the current
; APPLY$ does not consider MAX built-in!  Remember, the current APPLY$ only
; recognizes the primitives in *apply$-primitives*.

  (if (< x y) y x))

(defun$ maxlist (lst fn)
  (cond ((endp lst) nil)
        ((endp (cdr lst)) (apply$ fn (list (car lst))))
        (t (max$ (apply$ fn (list (car lst)))
                 (maxlist (cdr lst) fn)))))

(defun$ filter (lst fn)
  (cond ((endp lst) nil)
        ((apply$ fn (list (car lst)))
         (cons (car lst) (filter (cdr lst) fn)))
        (t (filter (cdr lst) fn))))

; The theorem below, which is not being stored as a rule, illustrates the most
; general fact we can think of relating COLLECT and FOLDR:

(defthm general-collect-is-a-foldr
  (implies (and (not (equal fn 'QUOTE))
                (not (equal fn 'IF))
                (symbolp x)
                (symbolp y)
                (not (eq x y))
                (tamep `(,fn ,x)))
           (equal (collect lst fn)
                  (foldr lst
                         `(lambda (,x ,y)
                            (cons (,fn ,x) ,y))
                         nil)))
  :rule-classes nil)

; But this rule is not useful as a rewrite rule because x and y are free
; variables.  Furthermore, if the goal is to rewrite COLLECTs into FOLDRs, it's
; not necessary to be so general.  We can just choose the x and y we want to
; use.  We use a convenient abbreviation for the hypotheses we'll see over and
; over here.

(defun$ ok-fnp (fn)
  (and (not (equal fn 'QUOTE))
       (not (equal fn 'IF))
       (tamep `(,fn X))))

(defthm collect-is-a-foldr
  (implies (force (ok-fnp fn))
           (equal (collect lst fn)
                  (foldr lst
                         `(LAMBDA (X Y)
                                  (CONS (,fn X) Y))
                         nil))))

(defthm allways-is-a-foldr
  (implies (force (ok-fnp fn))
           (equal (allways lst fn)
                  (foldr lst
                         `(LAMBDA (X Y)
                                  (IF (,fn X) Y 'NIL))
                         t))))

(defthm sumlist-is-a-foldr
  (implies (force (ok-fnp fn))
           (equal (sumlist lst fn)
                  (foldr lst
                         `(LAMBDA (X Y)
                                  (BINARY-+ (,fn X) Y))
                         0))))

; Clearly we could on and on with these sorts of mappers!

; Before dealing with maxlist we deal with filter...

(defthm filter-is-a-foldr
  (implies (force (ok-fnp fn))
           (equal (filter lst fn)
                  (foldr lst `(lambda (x y)
                                (if (,fn x)
                                    (cons x y)
                                    y))
                         nil))))

; Maxlist cannot be expressed as a foldr without some additional hypotheses or
; special cases.  The problem is that maxlist never calls itself recursively on
; the empty list while foldr does.  That means maxlist never compares its
; ``initial value'' (i.e., its value on the empty list) to any of the values
; returned by fn.  But foldr does compare those two.  One can try to avoid that
; by special-casing the singleton list sort of like maxlist does, but in fact
; that idea doesn't work.  (Note the NOT in the conclusion; the theorem below
; provides a counterexample to the claimed equivalence.)

(defthm maxlist-is-not-this-foldr!
  (let ((lst '(4 1))
        (fn '(lambda (x) (binary-* '-5 x))))
    (implies (and (force (ok-fnp fn))
                  (apply$-warrant-MAX$)
                  )
             (NOT (equal (maxlist lst fn)
                         (if (endp lst)
                             nil
                             (if (endp (cdr lst))
                                 (apply$ fn (list (car lst)))
                                 (foldr lst
                                        `(LAMBDA (X Y)
                                                 (MAX$ (,fn X) Y))
                                        nil)))))))
  :hints (("Goal" :expand ((:free (x) (HIDE x)))))
  :rule-classes nil)

; The maxlist above returns -5 but the foldr returns nil (which is bigger than
; all the negatives).

; So if foldr always compares its value on the empty list to the values of fn
; on elements of its input list, we must have a way to tell whether the value
; being compared is the special one returned for the empty list.  But without
; some kind of restriction on what fn returns, we cannot designate a
; ``special'' value.

; If we posit that fn always returns a number (at least, over the elements in
; lst), then we can tell the difference between the initial value and any call
; of fn, and then we get a reasonable relationship.

(defthm maxlist-non-nil
  (implies (and (force (ok-fnp fn))
                (allways (collect lst fn) 'acl2-numberp))
           (iff (maxlist lst fn)
                (consp lst))))

(defthm maxlist-is-sort-of-a-foldr
  (implies (and (force (ok-fnp fn))
                (apply$-warrant-MAX$)
                (allways (collect lst fn) 'acl2-numberp))
           (equal (maxlist lst fn)
                  (foldr lst `(lambda (x y)
                                (if (equal y 'nil) 
                                    (,fn x)
                                    (max$ (,fn x) y)))
                         nil))))

; This concludes our foldr exercises.



