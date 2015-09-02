(in-package "BAG")

;BOZO decide whether to hang the rules on equal (is that too expensive?) or on the special function NEQ.

(include-book "bind-free-rules")

(defun neq (x y)
  (not (equal x y)))

(local (defstub foo (x) t))

;how does append play into all of this?

(set-state-ok t)


#|
Eric,

  Following are some example problems:

  The ones for which you would have to write new meta code:
|#


;Look through the clause for a (non-negated) literal of the form
;(memberp a BLAH) where BLAH syntactically contains b.
;or a (non-negated) literal of the form:
;(memberp b BLAH) where BLAH syntactically contains a.
;If such a literal is found, return it.  The (non-negated) presence of that literal in the clause
;essentially means that we have a hypotheses which is the negation of that literal, e.g., (not (memberp a BLAH)).
;where BLAH syntactically contains b. In this case, a and b can't be equal.
;If not such literal is found, return nil.

(defignored find-memberp-literal-that-shows-a-and-b-differ a (v b clause)
  (declare (type t v b clause)
           (xargs :guard (and (pseudo-termp v)
                              (pseudo-termp b)
                              (pseudo-term-listp clause))
                  ))
  (if (not (consp clause))
      nil
    (let ((lit (car clause)))
      (if (and (consp lit)
               (equal 'memberp (car lit)) ;the fact (memberp v x) appears un-negated in the clause
               (consp (cdr lit)))
          (if (or (and (equal v (cadr lit))
                       (consp (cddr lit))
                       (syntax-memberp b (caddr lit)))
                  (and (equal b (cadr lit))
                       (consp (cddr lit))
                       (syntax-memberp v (caddr lit))))
              lit
            (find-memberp-literal-that-shows-a-and-b-differ v b (cdr clause)))
        (find-memberp-literal-that-shows-a-and-b-differ v b (cdr clause))))))

(defirrelevant find-memberp-literal-that-shows-a-and-b-differ 1 a (v b clause)
  :hints (("goal" :in-theory (enable
			      find-memberp-literal-that-shows-a-and-b-differ
			      syntax-memberp-irrelevant
			      ))))

;TERM has the form (equal a b)
(defun metafunction-to-rewrite-equal-to-nil (term mfc state)
  (declare (ignore state)
           (type t term mfc state)
           (xargs :guard (pseudo-termp term)
                  ))
  (if (and (consp term)
           (equal (car term) 'equal)
           (consp (cdr term))
           (consp (cddr term))
           (find-memberp-literal-that-shows-a-and-b-differ-fn
	    nil (cadr term) (caddr term) (mfc-clause mfc))
           (null (cdddr term))
           )
      ''nil
    term))

(defun hyp-for-metafunction-to-rewrite-equal-to-nil (term mfc state)
  (declare (ignore state)
           (type t term mfc state)
           (xargs :guard (pseudo-termp term)
                  ))
  (if (and (consp term)
           (equal (car term) 'equal)
           (consp (cdr term))
           (consp (cddr term))
           (null (cdddr term))
           )
      `(not ,(find-memberp-literal-that-shows-a-and-b-differ-fn
	      nil (cadr term) (caddr term) (mfc-clause mfc)))
    ''nil))

(defevaluator ev3 ev3-list
  ((memberp x l)
   (binary-append x y)
   (cons x y)
   (not x)
   (if x y z)
   (equal x y)
   ))


(local
 (defthm syntactic-membership-meta-rule-helper
   (implies (syntax-memberp x y)
	    (memberp (ev3 x a)
		     (ev3 y a)))
   :rule-classes (:forward-chaining)
   :hints (("Goal" :in-theory (enable memberp
				      syntax-memberp
				      )))))

(local
 (defthm helper-bozo
   (implies (and (find-memberp-literal-that-shows-a-and-b-differ x y clause)
                 (not (ev3 (find-memberp-literal-that-shows-a-and-b-differ x y clause)
                           a)))
            (not (equal (ev3 x a) (ev3 y a))))
   :hints (("Goal" :in-theory (enable
			       find-memberp-literal-that-shows-a-and-b-differ
			       )
	    :do-not '(generalize eliminate-destructors)))))

;Rewrite (equal a b) to nil when either the clause contains (not
;(memberp a BLAH)) and BLAH syntactically contains b.  or the clause
;contains (not (memberp b BLAH)) and BLAH syntactically contains a.

(defthm meta-rule-to-rewrite-equal-to-nil
  (implies (ev3 (hyp-for-metafunction-to-rewrite-equal-to-nil term mfc state) a)
           (equal (ev3 term a)
                  (ev3 (metafunction-to-rewrite-equal-to-nil term mfc state) a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
	   :in-theory (enable
		       find-memberp-literal-that-shows-a-and-b-differ-irrelevant
		       )))
  :rule-classes ((:meta :trigger-fns (equal))))

(encapsulate
 ()
 (local (defthm neq-test-1
          (implies (not (memberp a (list b c d e f)))
                   (equal (foo (equal a d))
                          (foo nil)))
          :rule-classes nil
          :hints (("Goal" :in-theory (union-theories '(meta-rule-to-rewrite-equal-to-nil)
                                                     (theory 'minimal-theory)))))))

(encapsulate
 ()
 (local (defthm neq-test-2
          (implies (not (memberp a (cons b (cons c (append (cons d (cons e nil)) f)))))
                   (equal (foo (equal a d))
                          (foo nil)))
          :rule-classes nil
          :hints (("Goal" :in-theory (union-theories '(meta-rule-to-rewrite-equal-to-nil)
                                                     (theory 'minimal-theory)))))))

(encapsulate
 ()
 (local (defthm neq-test-2-alt
          (implies (not (memberp a (cons b (cons c (append f (cons d (cons e nil)))))))
                   (equal (foo (equal a d))
                          (foo nil)))
          :rule-classes nil
          :hints (("Goal" :in-theory (union-theories '(meta-rule-to-rewrite-equal-to-nil)
                                                     (theory 'minimal-theory)))))))

;;
;;
;;
;;
;;

;Looks for a negated literal (roughly, a hypothesis) of the form  (memberp a x))
;Returns the literal if it finds one.  Else, returns nil.
(defun find-negated-memberp-literal-in-clause (a x clause)
  (declare (type t a x clause))
  (if (consp clause)
      (let ((lit (car clause)))  ;testing whether lit is (not (memberp a x))
        (if (and (consp lit)
                 (equal 'not (car lit))
                 (consp (cdr lit)))
            (let ((inner-lit (cadr lit)))
              (if (and (consp inner-lit)
                       (equal 'memberp (car inner-lit))
                       (consp (cdr inner-lit))
                       (equal a (cadr inner-lit))
                       (consp (cddr inner-lit))
                       (equal x (caddr inner-lit))
;check arities?
                       )
                  inner-lit
                (find-negated-memberp-literal-in-clause a x (cdr clause))))
          (find-negated-memberp-literal-in-clause a x (cdr clause))))
    nil))

;Look through the clause for literals of the form:
;(memberp a BLAH)
;and
;(not (memberp b BLAH))
;or vice versa
;This function looks for the (memberp a BLAH) literal and then calls a helper function to find the
;(not (memberp b BLAH)) literal.
;This function returns a term representing the conjunction of the literals, or else nil.
;We choose to have the outer loop (this function, rather than the one it calls) look for literals of the form (memberp a BLAH) or (memberp b BLAH)
;instead of literals of the form (not (memberp b BLAH)) or (not (memberp a BLAH)) for two reasons:
;1. In the cases where this rule won't hit, it's cheaper to not strip off the enclosiing NOTs from the literals
;2. We expect memberp to appear less often in the clause than not-memberp, since not-memberp appears less often as a hyp .. do we??  BOZO ask greve!
;what if a equals b?
(defun find-two-memberp-literals-that-tell-you-that-a-and-b-differ (a b clause whole-clause)
  (declare (type t a b clause whole-clause))
  (if (consp clause)
      (let ((lit (car clause)))
        (if (and (consp lit)
                 (equal 'memberp (car lit)) ;the fact (not (memberp a x)) appears un-negated in the clause
                 (consp (cdr lit)))
            (if (and (equal a (cadr lit))
                     (consp (cddr lit)) ;necessary?
                     )
                (let ((result (find-negated-memberp-literal-in-clause b (caddr lit) whole-clause)))
                  (if result
                      `(if (not ,lit) ; `(and (not ,lit) ,result)
                           ,result
                         'nil)
                    (find-two-memberp-literals-that-tell-you-that-a-and-b-differ a b (cdr clause) whole-clause)))
              (if (and (equal b (cadr lit))
                       (consp (cddr lit)) ;necessary?
                       )
                  (let ((result (find-negated-memberp-literal-in-clause a (caddr lit) whole-clause)))
                    (if result
                        `(if (not ,lit); `(and (not ,lit) ,result)
                             ,result
                           'nil)
                      (find-two-memberp-literals-that-tell-you-that-a-and-b-differ a b (cdr clause) whole-clause)))
                (find-two-memberp-literals-that-tell-you-that-a-and-b-differ a b (cdr clause) whole-clause)))
          (find-two-memberp-literals-that-tell-you-that-a-and-b-differ a b (cdr clause) whole-clause)))
    nil))

;TERM has the form (equal a b)
(defun metafunction-for-two-memberp-literals-blah (term mfc state)
  (declare (ignore state) (type t term mfc state))
  (if (and (consp term)
           (equal (car term) 'equal)
           (consp (cdr term))
           (consp (cddr term))
           (null (cdddr term))
           (find-two-memberp-literals-that-tell-you-that-a-and-b-differ (cadr term) (caddr term) (mfc-clause mfc) (mfc-clause mfc))
           )
      ''nil
    term))

(defun hyp-metafunction-for-two-memberp-literals-blah (term mfc state)
  (declare (ignore state) (type t term mfc state))
  (if (and (consp term)
           (equal (car term) 'equal)
           (consp (cdr term))
           (consp (cddr term))
           (null (cdddr term))
           )
      (let ((hyp (find-two-memberp-literals-that-tell-you-that-a-and-b-differ (cadr term) (caddr term) (mfc-clause mfc) (mfc-clause mfc))))
        (if hyp
            hyp
          ''nil))
    ''nil))

(local
 (defthm cons-iff
   (iff (cons a b) t)))

(local (defthm helper3
 (implies (and (ev3 (find-negated-memberp-literal-in-clause x list clause) a)
               (find-negated-memberp-literal-in-clause x list clause))
          (memberp (ev3 x a) (ev3 list a )))))


(local
 (defthm syntactic-membership-meta-rule-helper-2
   (implies (and (find-two-memberp-literals-that-tell-you-that-a-and-b-differ x y clause clause2)
                 (ev3 (find-two-memberp-literals-that-tell-you-that-a-and-b-differ x y clause clause2)
                      a))
            (not (equal (ev3 x a)
                        (ev3 y a))))
   :hints (("Goal" :do-not '(generalize eliminate-destructors)
            :in-theory (e/d (memberp) (;FIND-NEGATED-MEMBERP-LITERAL-IN-CLAUSE
                                              ))))))

; ; Greve almost considers this a special case.
(defthm meta-rule-for-two-memberp-literals
  (implies (ev3 (hyp-metafunction-for-two-memberp-literals-blah term mfc state) a)
           (equal (ev3 term a)
                  (ev3 (metafunction-for-two-memberp-literals-blah term mfc state) a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)))
  :rule-classes ((:meta :trigger-fns (equal))))



;BOZO extend to case when x isn't quite the same in both places!
;or see greve's suggestion below
(encapsulate
 ()
 (local (defthm test-meta-rule-for-two-memberp-literals
          (implies (and (memberp a x)
                        (not (memberp b x)))
                   (equal (foo (equal a b))
                          (foo nil)))
          :rule-classes nil
          :hints (("Goal" :in-theory (union-theories '(meta-rule-for-two-memberp-literals)
                                                     (theory 'minimal-theory)))))))








#|
;too expensive?!
(defthm disjoint-singletons-means-not-equal
  (implies (disjoint (list a) (list b))
           (not (equal a b))))


;  Ones that could (at least in part) hijack the disjoint code:

;why does this work but not the disj version?
(defthm neq-test-3-foo
  (implies (unique (list a b c d e f))
           (equal (foo (equal b e))
                  (foo nil)))
  :hints (("Goal" :in-theory (disable UNIQUE-OF-CONS)))
;  :hints (("Goal" :in-theory (enable unique-of-cons)))
  )


;could this be failing because the disjoint claims gets rewritten when we are neither backchaining nor rewriting a top-level literal in the clause
(defthm neq-test-3-foo-disj
  (implies (unique (list a b c d e f))
           (equal (foo (disjoint (list b) (list e)))
                  (foo t)))
  :hints (("Goal" :in-theory (disable UNIQUE-OF-CONS
                                      DISJOINT-OF-CONS-TWO
                                      DISJOINT-OF-CONS-ONE
                                      DISJOINT-OF-SINGLETON-ONE
                                      DISJOINT-OF-SINGLETON-TWO)))
;  :hints (("Goal" :in-theory (enable unique-of-cons)))
  )


(defthm neq-test-3-foo-disj2
  (implies (unique (list a b c d e f))
           (equal (disjoint (list b) (list e))
                  t))
  :hints (("Goal" :in-theory (disable UNIQUE-OF-CONS
                                      DISJOINT-OF-CONS-TWO
                                      DISJOINT-OF-CONS-ONE
                                      DISJOINT-OF-SINGLETON-ONE
                                      DISJOINT-OF-SINGLETON-TWO)))
;  :hints (("Goal" :in-theory (enable unique-of-cons)))
  )

(defthm neq-test-4-foo
  (implies (disjoint (list a b c) (list d e f))
           (equal (foo (equal b e)) (foo nil))))

;BOZO why can't we get this!? now we can!
;on the one hand, we'd like to tie the neq rules to the disjointness rules. on the other hands, disjointness claims about singletons really should be simplified away.
;maybe i need to figure out all the ways we can conclude disjoint and write similar rules for neq (or for (note equal)).
(defthm neq-test-5-foo-aux
  (implies (and (disjoint x (list b c d))
                (memberp a x))
           (equal (foo (disjoint (list a) (list b)))
                  (foo t)))
  :hints (("Goal" :in-theory (disable DISJOINT-OF-CONS-TWO
                                      DISJOINT-OF-SINGLETON-TWO
                                      DISJOINT-OF-SINGLETON-one))))


(defthm neq-test-5-foo
  (implies (and (disjoint x (list b c d))
                (memberp a x))
           (equal (foo (equal a b))
                  (foo nil)))
  :hints (("Goal" :in-theory (disable DISJOINT-OF-CONS-TWO

                                      DISJOINT-OF-SINGLETON-TWO
                                      DISJOINT-OF-SINGLETON-ONE))))




(defthm blah
  (implies (

  (not (equal a b))


(thm
 (implies (and (disjoint x (list b c d))
               (memberp a x))
          (equal (foo (disjoint (list a) (list b)))
                 (foo t))))

;why doesn't hijacking the disjoint rule work for this?
(defthm neq-test-5-foo
  (implies (and (disjoint x (list b c d))
                (memberp a x))
           (equal (foo (equal a b)) (foo nil))))

(defthm neq-test-6
 (implies
  (and
    (unique (append x (list c d e f)))
    (memberp a x))
  (neq a d)))

(defthm neq-test-6-foo
  (implies (and (unique (append x (list c d e f)))
                (memberp a x))
           (equal (foo (neq a d)) (foo t))))

(defthm neq-test-7
  (implies
   (and
    (disjoint x y)
    (memberp a x)
    (memberp b y))
   (neq a b)))

(defthm neq-test-7-foo
  (implies (and (disjoint x y)
                (memberp a x)
                (memberp b y))
           (equal (foo (neq a b)) (foo t))))




In general:

  I would suggest: if neither a nor b appear as
an argument to member in the hypothesis,
wrap them in a list and pass them to the
disjoint computation.

  If one does appear as an argument to a member
in the hypothesis (memberp a x), try to establish the
disjointness of the other from the list argument of
member.
|#
