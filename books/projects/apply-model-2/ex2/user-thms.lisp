; Copyright (C) 2019, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "MODAPP")
(include-book "user-defs")

; -----------------------------------------------------------------
; Some Sample Theorems about Mapping Functions

; Theorems just showing some evaluations:

(defthm collect-example
  (equal (collect '(1 2 3) '(LAMBDA (X) (CONS 'A X)))
         '((A . 1) (A . 2) (A . 3)))
  :rule-classes nil)

(defthm collect-collect-example
  (implies (warrant collect)
           (equal (collect '((1 2 3) (4 5 6))
                           '(LAMBDA (X)
                                    (COLLECT X '(LAMBDA (X) (CONS 'A X)))))
                  '(((A . 1) (A . 2) (A . 3))
                    ((A . 4) (A . 5) (A . 6)))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (x) (hide x))))))

(defthm recur-by-collect-example
  (equal (recur-by-collect '(1 1 1)
                           '(LAMBDA (X) (BINARY-+ '1 X)))
         '(1 2 3))
  :rule-classes nil)

; A theorem showing that functions can be data, i.e., we can apply mapping functions
; to mapping functions, as long as the data functions are tame.

(defthm collect*-collect-example
  (implies (warrant square collect)
           (equal (collect* '(((1 2 3) (LAMBDA (X) (CONS 'A X)))
                              ((4 5 6 7) SQUARE)
                              (((20 21 22)
                                (30 31 32)
                                (40 41 42))
                               (LAMBDA (Y)
                                       (COLLECT Y '(LAMBDA (Z) (CONS 'C Z)))))
                              )
                            'COLLECT)
                  '(((A . 1)(A . 2)(A . 3))
                    (16 25 36 49)
                    (((C . 20) (C . 21) (C . 22))
                     ((C . 30) (C . 31) (C . 32))
                     ((C . 40) (C . 41) (C . 42)))
                    )))
  :rule-classes nil
  :hints
  (("Goal"
    :in-theory
    (disable (:executable-counterpart collect)
             (:executable-counterpart collect*)))))

; Theorems about general relationships

(defthm collect-my-append1
  (equal (collect (my-append1 a b) fn)
         (my-append1 (collect a fn)
                     (collect b fn))))

(defthm sumlist-my-append1
  (equal (sumlist (my-append1 a b) u)
         (+ (sumlist a u)
            (sumlist b u))))

(defthm all-my-append1
  (equal (all (my-append1 a b) fn)
         (and (all a fn) (all b fn))))

(defthm xists-my-append1
  (equal (xists (my-append1 a b) fn)
         (if (xists a fn)
             t
             (xists b fn))))

(defthm len-filter
  (<= (len (filter lst fn)) (len lst))
  :rule-classes :linear)

(defthm filter-v-all
  (implies (true-listp lst)
           (iff (equal (filter lst fn) lst)
                (all lst fn)))
  :hints (("Subgoal *1/3.2'" :in-theory (disable len-filter)
           :use ((:instance len-filter (lst (cdr lst)) (fn fn))))))

(defthm filter-v-xists
  (iff (filter lst fn)
       (xists lst fn))
  :rule-classes nil)

; We show some theorems about FOLDR further below.

; Theorems about concrete uses of mapping functions.

(encapsulate nil
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm sumlist-nats
    (implies (and (warrant square)
                  (natp n))
             (equal (sumlist (nats n) 'SQUARE)
                    (/ (* n (+ n 1) (+ (* 2 n) 1))
                       6)))
    :hints (("Goal" :expand ((:free (x) (HIDE x)))))))

; If lst is a true-list and every element of lst is also, then reversing each element twice
; leaves lst unchanged:

(defthm rev-rev-version-1
  (implies (and (warrant my-rev)
                (true-listp lst)
                (all lst 'true-listp))
           (equal (collect (collect lst 'my-rev) 'my-rev) lst)))

; We can actually accomplish an append and a reverse via FOLDRs.  So after we
; establish that, we repeat the above theorem but this time without referring
; to my-rev.

(defthm foldr-as-my-append1
  (equal (foldr x 'CONS y)
         (my-append1 x y)))

(defthm foldr-as-my-rev
  (implies (warrant foldr)
           (equal (foldr x
                         '(LAMBDA (X Y)
                            (FOLDR Y 'CONS (CONS X 'NIL)))
                         nil)
                  (my-rev x))))

(defthm rev-rev-version-2
  (implies (and (warrant foldr)
                (true-listp lst)
                (all lst 'true-listp))
           (equal (collect (collect lst
                                    '(lambda (x)
                                       (foldr x
                                              '(LAMBDA (X Y)
                                                       (FOLDR Y 'CONS (CONS X 'NIL)))
                                              nil)))
                           '(lambda (x)
                              (foldr x
                                     '(LAMBDA (X Y)
                                              (FOLDR Y 'CONS (CONS X 'NIL)))
                                     nil)))
                  lst)))

; And ALL and COLLECT are also FOLDRs, so we can make this an all FOLDR show:

(defthm rev-rev-version-3
  (implies (and (warrant foldr)
                (true-listp lst)
                (foldr lst
                       '(LAMBDA (X Y)
                                (IF (TRUE-LISTP X) Y 'NIL))
                       t))
           (equal (foldr
                   (foldr lst
                          '(LAMBDA (X Y)
                                   (CONS (foldr x
                                                '(LAMBDA (X Y)
                                                         (FOLDR Y 'CONS (CONS X 'NIL)))
                                                nil)
                                         Y))
                          nil)
                   '(LAMBDA (X Y)
                            (CONS (foldr x
                                         '(LAMBDA (X Y)
                                                  (FOLDR Y 'CONS (CONS X 'NIL)))
                                         nil)
                                  Y))
                   nil)
                  lst)))

; A few theorems manipulating mapping functions and the functions they
; apply.

; Here is a way to move a constant factor out of a sumlist regardless of the
; names of the variables.

(defthm sumlist-binary-*-constant
  (implies (tamep body)
           (equal (sumlist lst (lamb (list v) (list 'binary-* (list 'quote const) body)))
                  (* const (sumlist lst (lamb (list v) body))))))

(defthm lamb-x-x-is-identity
  (implies (symbolp x)
           (fn-equal (lamb (list x) x) 'identity))
  :hints (("Goal" :in-theory (enable fn-equal))))

; The hint below is only provided to show that the theorem is proved by
; rewriting, not induction.

(defthm example-of-loop$-rewriting
  (equal (sumlist (my-append1 aaa bbb) (lamb '(x) '(binary-* '2 x)))
         (+ (* 2 (sumlist aaa 'identity))
            (* 2 (sumlist bbb 'identity))))
  :hints (("Goal" :do-not-induct t))
  :rule-classes nil)

; A couple of nice foldr theorems.  The first two are redundant; they were
; critical as rewrite rules in our rev-rev versions above.  We repeat them here
; just to summarize the relations with foldr. The rest These are really just
; designed to illustrate the relationships, not to be used as rewrites.

(defthm foldr-as-my-append1
  (equal (foldr x 'CONS y)
         (my-append1 x y)))

(defthm foldr-as-my-rev
  (implies (warrant foldr)
           (equal (foldr x
                         '(LAMBDA (X Y)
                            (FOLDR Y 'CONS (CONS X 'NIL)))
                         nil)
                  (my-rev x))))

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
; not necessary to be so general: we could just choose the x and y we want to
; use.  But we're not interested in rewriting in either direction here so we
; make this (and subsequent theorems) :rule-classes nil.

; We use a convenient abbreviation for the hypotheses we'll see over and over
; here.

(defthm foldr-as-collect
  (implies (force (ok-fnp fn))
           (equal (foldr lst
                         `(LAMBDA (X Y)
                                  (CONS (,fn X) Y))
                         nil)
                  (collect lst fn)))
  :rule-classes nil)

(defthm foldr-as-sumlist
  (implies (ok-fnp fn)
           (equal (foldr lst
                         `(LAMBDA (X Y)
                                  (BINARY-+ (,fn X) Y))
                         0)
                  (sumlist lst fn)))
  :rule-classes nil)

(defthm foldr-as-filter
  (implies (ok-fnp fn)
           (equal (foldr lst
                         `(LAMBDA (X Y)
                            (IF (,fn X) (CONS X Y) Y))
                         nil)
                  (filter lst fn)))
  :rule-classes nil)

(defthm foldr-as-all
  (implies (ok-fnp fn)
           (equal (foldr lst
                         `(LAMBDA (X Y)
                                  (IF (,fn X) Y 'NIL))
                         t)
                  (all lst fn)))
  :rule-classes nil)

(defthm foldr-as-xists
  (implies (ok-fnp fn)
           (equal (foldr lst
                         `(LAMBDA (X Y)
                                  (IF (,fn X) 'T Y))
                         nil)
                  (xists lst fn)))
  :rule-classes nil)

(defthm maxlist-non-nil
  (implies (and (ok-fnp fn)
                (all (collect lst fn) 'ACL2-NUMBERP))
           (iff (maxlist lst fn)
                (consp lst)))
  :rule-classes nil)

(defthm foldr-as-maxlist
  (implies (and (ok-fnp fn)
                (all (collect lst fn) 'ACL2-NUMBERP))
           (equal (foldr lst `(LAMBDA (X Y)
                                (IF (EQUAL Y 'NIL)
                                    (,fn X)
                                    (MAX (,fn X) Y)))
                         nil)
                  (maxlist lst fn)))
  :rule-classes nil)

